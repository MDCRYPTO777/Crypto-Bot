#!/usr/bin/env node
/* Paper Trading Desk, script version.
   Run:   node desk.js          (needs Node 18 or newer, no installs)
   View:  http://localhost:3000  (set PORT to change)
   Trades are simulated with fake money. State is saved in desk-state.json next to this file. */
'use strict';
const http=require('http'),fs=require('fs'),path=require('path'),os=require('os');
if(typeof fetch!=='function'){console.error('This needs Node 18 or newer. You have '+process.version+'.');process.exit(1)}
const PORT=Number(process.env.PORT)||3000;
const FILE=path.join(__dirname,'desk-state.json');

/* Engine: no DOM. createDesk(env) -> desk. env = {fetchJson(url), now(), load(), save(obj)} */
function createDesk(env){
  const DEF={stack:500,slip:2,ageMinM:30,ageMaxH:72,liqMin:40000,mcMin:100000,mcMax:5000000,volMin:50000,
    ranMax:100,minScore:75,sizeMin:3,sizeMax:8,maxPos:3,reserve:20,stop:20,tp:100,trail:35,timeH:6,
    liqDrop:30,dayLoss:15,requireAudit:true};
  const DEX='https://api.dexscreener.com', RUG='https://api.rugcheck.xyz/v1/tokens/';
  const GT='https://api.geckoterminal.com/api/v2/networks/solana/';
  const DEX_LISTS=['/token-profiles/latest/v1','/token-boosts/latest/v1','/token-boosts/top/v1','/community-takeovers/latest/v1'];
  const GT_PAGES=[];
  for(let i=1;i<=5;i++)GT_PAGES.push('new_pools?page='+i);
  for(let i=1;i<=3;i++)GT_PAGES.push('trending_pools?page='+i);
  for(let i=1;i<=4;i++)GT_PAGES.push('pools?sort=h24_tx_count_desc&page='+i);
  const MINT=/^[1-9A-HJ-NP-Za-km-z]{32,44}$/;
  const MAX_UNIVERSE=900, BATCHES_PER_SCAN=8;
  const num=x=>{const n=Number(x);return isFinite(n)?n:0};
  const clamp=(x,a,b)=>Math.max(a,Math.min(b,x));
  const sym=p=>String((p.baseToken&&p.baseToken.symbol)||'?').slice(0,14);
  const fresh=cfg=>({cfg,cash:cfg.stack,start:cfg.stack,positions:[],closed:[],activity:[],equity:[],
    day:null,stopsInRow:0,scanPausedUntil:0,halted:false,haltReason:'',running:true,cooldown:{},
    seenReject:{},errors:{dex:0,rug:0},watch:[],funnel:{tracked:0,pass:0,scored:0,safe:0},lastScan:0,
    agents:{scanner:{line:'Waiting for first scan',met:''},analyst:{line:'Idle',met:''},auditor:{line:'Idle',met:''},
      executor:{line:'Waiting for a coin to pass',met:''},risk:{line:'No open positions',met:''}}});
  let S=fresh({...DEF});
  const saved=env.load();
  if(saved&&saved.cfg&&Array.isArray(saved.positions)){
    const f=fresh({...DEF,...saved.cfg});
    S={...f,...saved,cfg:f.cfg,agents:{...f.agents,...(saved.agents||{})},funnel:{...f.funnel,...(saved.funnel||{})}};
  }
  const auditCache={};          // mint -> {t,r}
  const universe=new Map();     // mint -> last time a source listed it
  const info=new Map();         // mint -> {p: pair, t: fetched}
  let gtCursor=0, queue=[];
  const persist=()=>env.save(S);

  function log(kind,title,sub,amt,pct){
    S.activity.unshift({t:env.now(),kind,title,sub,amt,pct});
    if(S.activity.length>200)S.activity.length=200;
  }
  function reject(mint,s,who,reason){
    const k=mint+'|'+who,t=env.now();
    if(S.seenReject[k]&&t-S.seenReject[k]<30*60e3)return;
    S.seenReject[k]=t;
    log('reject','Rejected '+s,who+' · '+reason);
    const keys=Object.keys(S.seenReject);
    if(keys.length>600)for(const x of keys)if(t-S.seenReject[x]>30*60e3)delete S.seenReject[x];
  }
  function value(){return S.cash+S.positions.reduce((a,p)=>a+p.qty*p.last,0)}
  function mark(){
    const t=env.now(),v=value();
    S.equity.push({t,v});
    if(S.equity.length>1500)S.equity=S.equity.filter((_,i)=>i%2===0||i>S.equity.length-300);
    const d=new Date(t).toDateString();
    if(!S.day||S.day.d!==d)S.day={d,v};
  }
  function bestPairs(list){
    const by={};
    for(const p of Array.isArray(list)?list:[]){
      const m=p&&p.baseToken&&p.baseToken.address;
      if(!m||!MINT.test(m)||p.chainId!=='solana'||!num(p.priceUsd))continue;
      if(!by[m]||num(p.liquidity&&p.liquidity.usd)>num(by[m].liquidity&&by[m].liquidity.usd))by[m]=p;
    }
    return by;
  }
  async function pairsFor(mints){
    const jobs=[];
    for(let i=0;i<mints.length;i+=30)jobs.push(env.fetchJson(DEX+'/tokens/v1/solana/'+mints.slice(i,i+30).join(',')));
    const res=await Promise.allSettled(jobs),out={};
    if(jobs.length&&res.every(r=>r.status==='rejected'))throw res[0].reason;
    for(const r of res)if(r.status==='fulfilled')Object.assign(out,bestPairs(r.value));
    return out;
  }
  function score(p){
    const h1=(p.txns&&p.txns.h1)||{},b=num(h1.buys),s=num(h1.sells);
    const m5v=num(p.volume&&p.volume.m5),h1v=num(p.volume&&p.volume.h1),liq=num(p.liquidity&&p.liquidity.usd);
    const c1=num(p.priceChange&&p.priceChange.h1),c5=num(p.priceChange&&p.priceChange.m5);
    let sc=0;
    sc+=clamp(((b+s?b/(b+s):0)-0.5)/0.2,0,1)*25;           // buyers outnumber sellers
    sc+=h1v?clamp((m5v*12/h1v-0.5)/1.5,0,1)*25:0;          // volume speeding up
    sc+=liq?clamp(h1v/liq,0,1)*20:0;                        // volume vs pool size
    sc+=c1>=5&&c1<=60?20:c1>0&&c1<5?10:c1>60?8:0;           // rising, not vertical
    sc+=c5>0?10:0;
    return Math.round(sc);
  }
  async function audit(mint){
    const c=auditCache[mint];
    if(c&&env.now()-c.t<10*60e3)return c.r;
    let r;
    try{
      const d=await env.fetchJson(RUG+mint+'/report/summary');
      const bad=(Array.isArray(d.risks)?d.risks:[]).filter(x=>x&&x.level==='danger').map(x=>String(x.name||'risk').slice(0,40));
      r=d.rugged?{ok:false,why:'flagged as rugged'}:bad.length?{ok:false,why:bad[0]}:{ok:true};
      S.errors.rug=0;auditCache[mint]={t:env.now(),r};
    }catch(e){S.errors.rug++;r={ok:!S.cfg.requireAudit,why:'safety check unavailable'}}
    return r;
  }
  function sell(pos,frac,reason,price){
    const c=S.cfg,q=pos.qty*frac,proceeds=q*price*(1-c.slip/100),cost=pos.cost*frac,pnl=proceeds-cost;
    S.cash+=proceeds;pos.qty-=q;pos.cost-=cost;pos.realized=(pos.realized||0)+pnl;
    log('sell','Sold '+pos.sym+(frac<1?' '+Math.round(frac*100)+'%':''),'Risk · '+reason,pnl,cost?pnl/cost*100:0);
    if(pos.qty*price<0.01||frac>=1){
      S.positions=S.positions.filter(x=>x!==pos);
      S.closed.unshift({sym:pos.sym,pnl:pos.realized,t:env.now()});
      if(S.closed.length>300)S.closed.length=300;
      S.cooldown[pos.mint]=env.now();
      S.stopsInRow=pos.realized<0?S.stopsInRow+1:0;
      if(S.stopsInRow>=3){S.stopsInRow=0;S.scanPausedUntil=env.now()+2*3600e3;log('info','Scanner paused 2 hours','3 losing trades in a row')}
    }
  }

  /* Find coins: every DexScreener list each scan, plus two GeckoTerminal pages in rotation. */
  async function discover(){
    const t=env.now(),urls=DEX_LISTS.map(u=>DEX+u);
    for(let i=0;i<2;i++){urls.push(GT+GT_PAGES[gtCursor%GT_PAGES.length]);gtCursor++}
    const res=await Promise.allSettled(urls.map(u=>env.fetchJson(u)));
    let ok=0;
    res.forEach((r,i)=>{
      if(r.status!=='fulfilled')return;
      const add=m=>{if(MINT.test(m||'')){if(!universe.has(m))queue.push(m);universe.set(m,t)}};
      if(i<DEX_LISTS.length){ok++;if(Array.isArray(r.value))for(const x of r.value)if(x&&x.chainId==='solana')add(x.tokenAddress)}
      else for(const x of (r.value&&Array.isArray(r.value.data)?r.value.data:[])){
        const id=x&&x.relationships&&x.relationships.base_token&&x.relationships.base_token.data&&x.relationships.base_token.data.id;
        if(typeof id==='string'&&id.indexOf('solana_')===0)add(id.slice(7));
      }
    });
    if(universe.size>MAX_UNIVERSE){
      const old=[...universe.entries()].sort((a,b)=>a[1]-b[1]).slice(0,universe.size-MAX_UNIVERSE);
      for(const [m] of old){universe.delete(m);info.delete(m)}
    }
    return ok;
  }
  /* Refresh prices: new coins first, then the ones not checked for the longest. */
  async function refresh(){
    const t=env.now(),limit=BATCHES_PER_SCAN*30;
    const first=queue.filter(m=>universe.has(m)).slice(0,limit);queue=queue.slice(first.length);
    const set=new Set(first);
    if(set.size<limit){
      const rest=[...universe.keys()].filter(m=>!set.has(m)).sort((a,b)=>((info.get(a)||{}).t||0)-((info.get(b)||{}).t||0));
      for(const m of rest){if(set.size>=limit)break;set.add(m)}
    }
    const list=[...set];
    if(!list.length)return;
    const pairs=await pairsFor(list);
    for(const m of list){if(pairs[m])info.set(m,{p:pairs[m],t});else{const o=info.get(m);info.set(m,{p:o&&o.p&&t-o.t<120e3?o.p:null,t})}}
  }

  async function scan(){
    if(!S.running||S.halted)return;
    const c=S.cfg,t=env.now(),A=S.agents;
    if(t<S.scanPausedUntil){A.scanner.line='Paused after 3 losses in a row';A.scanner.met='';return persist()}
    try{
      const ok=await discover();
      if(!ok&&!universe.size)throw new Error('no sources');
      await refresh();
      S.errors.dex=0;
    }catch(e){S.errors.dex++;A.scanner.line='Cannot reach DexScreener, retrying';A.scanner.met='';return persist()}

    const pass=[];let tracked=0;
    for(const [,x] of info){
      const p=x.p;if(!p)continue;tracked++;
      const ageM=(t-num(p.pairCreatedAt))/60e3,liq=num(p.liquidity&&p.liquidity.usd),mc=num(p.marketCap||p.fdv),v=num(p.volume&&p.volume.h1);
      if(ageM>=c.ageMinM&&ageM<=c.ageMaxH*60&&liq>=c.liqMin&&mc>=c.mcMin&&mc<=c.mcMax&&v>=c.volMin)pass.push({p,sc:score(p)});
    }
    pass.sort((a,b)=>b.sc-a.sc);
    A.scanner.line=pass.length?pass.length+' pass the filters, best: '+sym(pass[0].p):'No coin passes the filters right now';
    A.scanner.met=universe.size+' coins';

    const W=[];let scored=0,safe=0,audits=0,rej=0;
    for(const {p,sc} of pass){
      const m=p.baseToken.address,s=sym(p),c1=num(p.priceChange&&p.priceChange.h1);
      const w={mint:m,sym:s,mc:num(p.marketCap||p.fdv),c1,score:sc,state:'low',note:'score '+sc+', needs '+c.minScore};
      const show=W.length<14;if(show)W.push(w);
      if(S.positions.some(x=>x.mint===m)){w.state='ok';w.note='holding';continue}
      if(S.cooldown[m]&&t-S.cooldown[m]<6*3600e3){w.note='traded in the last 6h';continue}
      if(c1>c.ranMax){w.state='no';w.note='already ran '+Math.round(c1)+'% this hour';if(sc>=c.minScore)reject(m,s,'Analyst',w.note);continue}
      if(sc<c.minScore)continue;
      scored++;
      const h1=(p.txns&&p.txns.h1)||{};
      if(!num(h1.sells)){w.state='no';w.note='no sells going through';rej++;reject(m,s,'Auditor',w.note);continue}
      if(!auditCache[m]&&audits>=4){w.note='waiting for safety check';continue}
      if(!auditCache[m])audits++;
      const a=await audit(m);
      if(!a.ok){w.state='no';w.note=a.why;rej++;reject(m,s,'Auditor',a.why);continue}
      safe++;w.state='ok';w.note='passed every check';
      // Executor
      const v=value();
      if(S.positions.length>=c.maxPos){w.note='passed, but '+c.maxPos+' positions already open';continue}
      const pct=c.sizeMin+(c.sizeMax-c.sizeMin)*clamp((sc-c.minScore)/Math.max(1,95-c.minScore),0,1);
      const size=v*pct/100;
      if(S.cash-size<v*c.reserve/100){w.note='passed, but would break the cash reserve';continue}
      let now=p;
      try{const f=await pairsFor([m]);if(f[m])now=f[m]}catch(e){}
      const price=num(now.priceUsd);
      if(price>num(p.priceUsd)*1.15){w.state='no';w.note='price jumped before the buy';reject(m,s,'Executor',w.note);continue}
      const entry=price*(1+c.slip/100);
      S.cash-=size;
      S.positions.push({mint:m,sym:s,pair:p.pairAddress,entry,qty:size/entry,cost:size,opened:t,high:price,last:price,
        tp1:false,liqPeak:num(now.liquidity&&now.liquidity.usd),misses:0,realized:0,score:sc});
      log('buy','Bought '+s,'Executor · score '+sc+' · '+pct.toFixed(1)+'% of stack',-size);
      A.executor.line='Bought '+s;w.note='bought';
    }
    S.watch=W;S.funnel={tracked,pass:pass.length,scored,safe};S.lastScan=t;
    A.analyst.line=pass.length?'Top score '+pass[0].sc+' ('+sym(pass[0].p)+')':'Nothing to score';
    A.analyst.met=scored+' at '+c.minScore+'+';
    A.auditor.line=scored?safe+' safe, '+rej+' rejected':'No coin reached the safety check';
    A.auditor.met=S.errors.rug?'offline':safe+' safe';
    A.executor.met=S.positions.length+'/'+c.maxPos+' open';
    mark();persist();
  }

  async function risk(){
    if(!S.running)return;
    const c=S.cfg,t=env.now(),A=S.agents;
    if(S.positions.length){
      let pairs;
      try{pairs=await pairsFor(S.positions.map(p=>p.mint))}catch(e){A.risk.line='Cannot reach prices, retrying';return}
      for(const pos of [...S.positions]){
        const p=pairs[pos.mint];
        if(!p){
          if(++pos.misses>=12){pos.last=0;sell(pos,1,'coin disappeared from listings, counted as total loss',0)}
          continue;
        }
        pos.misses=0;
        const price=num(p.priceUsd),liq=num(p.liquidity&&p.liquidity.usd);
        pos.last=price;pos.high=Math.max(pos.high,price);pos.liqPeak=Math.max(pos.liqPeak,liq);
        const chg=(price/pos.entry-1)*100,ageH=(t-pos.opened)/3600e3;
        if(liq<pos.liqPeak*(1-c.liqDrop/100))sell(pos,1,'liquidity dropped '+c.liqDrop+'%',price);
        else if(!pos.tp1&&chg<=-c.stop)sell(pos,1,'stop -'+c.stop+'%',price);
        else if(!pos.tp1&&chg>=c.tp){pos.tp1=true;sell(pos,0.5,'take profit +'+c.tp+'%',price)}
        else if(pos.tp1&&price<=pos.high*(1-c.trail/100))sell(pos,1,'trail '+c.trail+'% from high',price);
        else if(!pos.tp1&&ageH>=c.timeH&&chg>-10&&chg<20)sell(pos,1,'time stop '+c.timeH+'h',price);
      }
    }
    mark();
    if(S.day&&!S.halted&&value()<=S.day.v*(1-c.dayLoss/100)){
      for(const pos of [...S.positions])sell(pos,1,'daily loss limit',pos.last);
      S.halted=true;S.haltReason='Daily loss limit of '+c.dayLoss+'% hit. Everything was sold.';
      log('info','Desk halted',S.haltReason);
    }
    A.risk.line=S.positions.length?'Guarding '+S.positions.map(p=>p.sym).join(', '):'No open positions';
    A.risk.met=S.positions.length+' open';
    A.executor.met=S.positions.length+'/'+c.maxPos+' open';
    persist();
  }
  return {
    get state(){return S},value,scan,risk,score,
    setRunning(on){S.running=on;if(on&&S.halted){S.halted=false;S.haltReason='';S.day={d:new Date(env.now()).toDateString(),v:value()}}persist()},
    setCfg(k,v){if(k in DEF){S.cfg[k]=v;persist()}},
    reset(){S=fresh({...S.cfg});persist()},
    DEF
  };
}

const desk=createDesk({
  now:()=>Date.now(),
  load(){try{return JSON.parse(fs.readFileSync(FILE,'utf8'))}catch(e){return null}},
  save(o){try{fs.writeFileSync(FILE+'.tmp',JSON.stringify(o));fs.renameSync(FILE+'.tmp',FILE)}catch(e){console.error('Could not save state: '+e.message)}},
  async fetchJson(url){
    const r=await fetch(url,{signal:AbortSignal.timeout(9000),headers:{accept:'application/json','user-agent':'paper-desk/1.0'}});
    if(!r.ok)throw new Error('HTTP '+r.status);
    return r.json();
  }
});

/* Print each new buy, sell and halt to the terminal. */
let printed=desk.state.activity.length?desk.state.activity[0].t:0;
function report(){
  const fresh=desk.state.activity.filter(a=>a.t>printed&&a.kind!=='reject').reverse();
  for(const a of fresh)console.log(new Date(a.t).toLocaleTimeString()+'  '+a.title+'  |  '+a.sub+(a.kind==='sell'?'  |  '+(a.amt>=0?'+':'-')+'$'+Math.abs(a.amt).toFixed(2):'')+'  |  stack $'+desk.value().toFixed(2));
  if(desk.state.activity.length)printed=Math.max(printed,desk.state.activity[0].t);
}
let busyScan=false,busyRisk=false;
async function doScan(){if(busyScan)return;busyScan=true;try{await desk.scan()}catch(e){console.error('scan error: '+e.message)}busyScan=false;report()}
async function doRisk(){if(busyRisk)return;busyRisk=true;try{await desk.risk()}catch(e){console.error('risk error: '+e.message)}busyRisk=false;report()}
process.on('unhandledRejection',e=>console.error('error: '+(e&&e.message||e)));
process.on('uncaughtException',e=>console.error('error: '+(e&&e.message||e)));

const PAGE="<!DOCTYPE html>\n<html lang=\"en\">\n<head>\n<meta charset=\"utf-8\">\n<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n<title>Paper Trading Desk</title>\n<link rel=\"preconnect\" href=\"https://fonts.googleapis.com\">\n<link href=\"https://fonts.googleapis.com/css2?family=Manrope:wght@500;600;700;800&display=swap\" rel=\"stylesheet\">\n<style>\n:root{\n  /* layout: one phone-width column on black — big stack number, chart, live watchlist, bots, activity */\n  color-scheme: dark;\n  --bg:#000; --panel:#141416; --line:#232326;\n  --text:#fff; --muted:#8e8e93;\n  --up:#30d158; --down:#ff453a; --warn:#ffd60a;\n  --sans:\"Manrope\",system-ui,-apple-system,\"Segoe UI\",sans-serif;\n}\n*{box-sizing:border-box}\nhtml,body{margin:0}\nbody{background:var(--bg);color:var(--text);font-family:var(--sans);font-size:15px;line-height:1.35;font-variant-numeric:tabular-nums}\nmain{max-width:520px;margin:0 auto;padding:16px 16px 40px;display:flex;flex-direction:column;gap:22px}\nh1{font-size:17px;font-weight:700;margin:0}\nh2{font-size:20px;font-weight:800;margin:0}\n.muted{color:var(--muted)} .up{color:var(--up)} .down{color:var(--down)}\nheader{display:flex;align-items:center;justify-content:space-between;gap:10px}\n.brand{display:flex;align-items:center;gap:10px}\n.logo{width:28px;height:28px;border-radius:50%;background:#fff;color:#000;display:grid;place-items:center;font-weight:800;font-size:14px}\n.pill{font-size:12px;font-weight:700;padding:4px 10px;border-radius:999px;background:#1c1c1e;color:var(--muted);white-space:nowrap}\n.pill.live{background:rgba(48,209,88,.16);color:var(--up)}\n.pill.live::before{content:\"\";display:inline-block;width:6px;height:6px;border-radius:50%;background:var(--up);margin-right:6px;vertical-align:1px}\n.pill.stop{background:rgba(255,69,58,.16);color:var(--down)}\n.pill.paper{background:rgba(255,214,10,.14);color:var(--warn)}\n.sub{font-size:12px;color:var(--muted);display:flex;justify-content:space-between;gap:8px;margin-top:6px}\n.big{font-size:52px;font-weight:800;letter-spacing:-.02em;line-height:1.05;margin-top:8px;overflow-wrap:anywhere}\n.pnl{display:flex;align-items:center;gap:8px;flex-wrap:wrap;font-size:15px;font-weight:700;margin-top:6px}\n.mult{background:var(--up);color:#000;border-radius:999px;padding:2px 9px;font-size:13px;font-weight:800}\n.mult.neg{background:var(--down);color:#fff}\ncanvas{width:100%;height:130px;display:block;margin-top:10px}\n.tabs{display:flex;justify-content:space-between;gap:4px;margin-top:8px}\n.tabs button{flex:1;background:none;border:0;color:var(--muted);font:inherit;font-size:12px;font-weight:700;padding:6px 0;border-radius:999px;cursor:pointer}\n.tabs button[aria-pressed=true]{background:var(--up);color:#000}\n.kpis{display:grid;grid-template-columns:repeat(4,1fr);gap:8px;margin-top:12px}\n.kpi{background:var(--panel);border-radius:12px;padding:9px 10px;min-width:0}\n.kpi span{display:block;font-size:11px;color:var(--muted)}\n.kpi b{font-size:14px;overflow-wrap:anywhere}\n.actions{display:flex;gap:8px;margin-top:12px;flex-wrap:wrap}\nbutton.btn{font:inherit;font-weight:700;font-size:14px;color:var(--text);background:#1c1c1e;border:0;border-radius:999px;padding:10px 16px;cursor:pointer}\nbutton.btn.go{background:var(--up);color:#000}\nbutton.btn.danger{color:var(--down)}\nbutton:focus-visible,input:focus-visible,summary:focus-visible,a:focus-visible{outline:2px solid var(--up);outline-offset:2px}\n.head{display:flex;justify-content:space-between;align-items:baseline;gap:10px;margin-bottom:10px}\n.head small{color:var(--up);font-size:12px;font-weight:700;text-align:right}\n.box{background:var(--panel);border-radius:16px;padding:4px 12px}\n.funnel{display:grid;grid-template-columns:repeat(4,1fr);gap:6px;margin-bottom:10px}\n.funnel div{background:var(--panel);border-radius:12px;padding:8px 6px;text-align:center}\n.funnel b{display:block;font-size:17px}\n.funnel span{font-size:10.5px;color:var(--muted)}\n.row{display:flex;align-items:center;gap:10px;padding:10px 0;border-top:1px solid var(--line)}\n.row:first-child{border-top:0}\n.ico{flex:0 0 32px;height:32px;border-radius:50%;display:grid;place-items:center;font-weight:800;font-size:13px;color:#000;background:var(--c,#3a3a3c)}\n.l{flex:1;min-width:0}\n.t{font-weight:700;overflow-wrap:anywhere}\n.t a{color:inherit;text-decoration:none}\n.s{font-size:12px;color:var(--muted);overflow-wrap:anywhere}\n.r{text-align:right;white-space:nowrap;font-weight:700;font-size:14px}\n.r small{display:block;font-size:12px;font-weight:600}\n.bar{height:4px;border-radius:2px;background:#2c2c2e;margin-top:5px;overflow:hidden}\n.bar i{display:block;height:100%;background:var(--up);border-radius:2px}\n.bar i.low{background:#636366}\n.chip{font-size:11px;font-weight:700;border-radius:999px;padding:2px 8px;background:#2c2c2e;color:var(--muted)}\n.chip.ok{background:rgba(48,209,88,.16);color:var(--up)}\n.chip.no{background:rgba(255,69,58,.16);color:var(--down)}\n.empty{color:var(--muted);font-size:13px;padding:14px 0}\n.banner{border-radius:12px;padding:10px 12px;font-size:13px;font-weight:600;background:rgba(255,69,58,.14);color:var(--down)}\n.banner.note{background:rgba(255,214,10,.12);color:var(--warn)}\n#banners{display:flex;flex-direction:column;gap:8px}\n#banners:empty{display:none}\n#toast{position:fixed;left:50%;top:10px;transform:translate(-50%,-140%);width:min(488px,calc(100% - 24px));background:rgba(44,44,46,.96);border-radius:18px;padding:12px 14px;display:flex;gap:10px;align-items:center;transition:transform .35s;z-index:5}\n#toast.on{transform:translate(-50%,0)}\n@media (prefers-reduced-motion:reduce){#toast{transition:none}}\ndetails summary{cursor:pointer;font-size:20px;font-weight:800}\n.grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(140px,1fr));gap:10px;margin-top:12px}\nlabel{display:flex;flex-direction:column;gap:4px;font-size:12px;color:var(--muted)}\nlabel.check{flex-direction:row;align-items:center;gap:8px;color:var(--text);font-size:13px;grid-column:1/-1}\ninput[type=number]{font:inherit;font-weight:700;color:var(--text);background:var(--panel);border:1px solid var(--line);border-radius:10px;padding:8px 10px;width:100%}\n.foot{font-size:12px;color:var(--muted)}\n#confirm{display:none;gap:8px;align-items:center;flex-wrap:wrap;margin-top:10px}\n#confirm.on{display:flex}\n</style>\n</head>\n<body>\n<div id=\"toast\" role=\"status\" aria-live=\"polite\"></div>\n<main>\n  <section aria-label=\"Stack\">\n    <header>\n      <div class=\"brand\"><span class=\"logo\">P</span><h1>Paper Desk</h1></div>\n      <div style=\"display:flex;gap:6px\">\n        <span class=\"pill paper\">Fake money</span>\n        <span class=\"pill\" id=\"status\">Starting</span>\n      </div>\n    </header>\n    <div class=\"sub\"><span id=\"open\">0 open</span><span id=\"clock\"></span></div>\n    <div class=\"big\" id=\"value\">$500.00</div>\n    <div class=\"pnl\" id=\"pnl\"></div>\n    <canvas id=\"chart\" height=\"130\" aria-label=\"Stack value over time\"></canvas>\n    <div class=\"tabs\" id=\"tabs\"></div>\n    <div class=\"kpis\">\n      <div class=\"kpi\"><span>Cash</span><b id=\"cash\">$500.00</b></div>\n      <div class=\"kpi\"><span>Closed</span><b id=\"ntrades\">0</b></div>\n      <div class=\"kpi\"><span>Win rate</span><b id=\"win\">n/a</b></div>\n      <div class=\"kpi\"><span>Today</span><b id=\"today\">0.00%</b></div>\n    </div>\n    <div class=\"actions\">\n      <button class=\"btn go\" id=\"toggle\" type=\"button\">Pause desk</button>\n      <button class=\"btn danger\" id=\"reset\" type=\"button\">Reset</button>\n    </div>\n    <div id=\"confirm\">\n      <span class=\"muted\" style=\"font-size:13px\">Erase all paper trades and start over?</span>\n      <button class=\"btn danger\" id=\"yes\" type=\"button\">Yes, reset</button>\n      <button class=\"btn\" id=\"no\" type=\"button\">Cancel</button>\n    </div>\n  </section>\n\n  <div id=\"banners\"></div>\n\n  <section>\n    <div class=\"head\"><h2>Looking at now</h2><small id=\"scanline\">Waiting for first scan</small></div>\n    <div class=\"funnel\" id=\"funnel\"></div>\n    <div class=\"box\" id=\"watch\"></div>\n  </section>\n\n  <section>\n    <div class=\"head\"><h2>Bots</h2><small>5 running</small></div>\n    <div class=\"box\" id=\"agents\"></div>\n  </section>\n\n  <section>\n    <div class=\"head\"><h2>Positions</h2><small id=\"poscount\"></small></div>\n    <div class=\"box\" id=\"positions\"></div>\n  </section>\n\n  <section>\n    <div class=\"head\"><h2>Activity</h2></div>\n    <div class=\"box\" id=\"activity\"></div>\n  </section>\n\n  <section>\n    <details>\n      <summary>Rules</summary>\n      <div class=\"grid\" id=\"settings\"></div>\n      <p class=\"foot\">Changes apply from the next scan. Starting stack applies after a reset.</p>\n    </details>\n  </section>\n\n  <p class=\"foot\">Simulated trades at live prices from DexScreener, with extra coin discovery from GeckoTerminal. Nothing here touches a wallet or real money. The desk runs inside desk.js on your computer or server, whether or not this page is open. Real fills on small coins are worse than simulated ones.</p>\n</main>\n\n<script>\n(function(){\n    const $=id=>document.getElementById(id);\n  const esc=s=>String(s==null?'':s).replace(/[&<>\"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','\"':'&quot;',\"'\":'&#39;'}[c]));\n  const usd=n=>(n<0?'-':'')+'$'+Math.abs(n).toLocaleString('en-US',{minimumFractionDigits:2,maximumFractionDigits:2});\n  const sgn=n=>(n>0?'+':'')+usd(n);\n  const pct=n=>(n>0?'+':'')+n.toFixed(2)+'%';\n  const cls=n=>n>0?'up':n<0?'down':'muted';\n  const time=t=>new Date(t).toLocaleTimeString([], {hour:'numeric',minute:'2-digit'});\n  const short=n=>n>=1e6?'$'+(n/1e6).toFixed(1)+'M':n>=1e3?'$'+Math.round(n/1e3)+'K':'$'+Math.round(n);\n\n  let offline=false,built=false;\n  const desk={state:null,value(){return this.state.value},\n    async post(p,b){try{const r=await fetch(p,{method:'POST',headers:{'content-type':'application/json'},body:JSON.stringify(b||{})});if(!r.ok)throw 0;this.state=await r.json();offline=false}catch(e){offline=true}render()},\n    setRunning(on){this.state.running=on;return this.post('/api/running',{on})},\n    setCfg(k,v){this.state.cfg[k]=v;return this.post('/api/cfg',{k,v})},\n    reset(){return this.post('/api/reset')}};\n\n  const AGENTS=[['scanner','Scanner','#64d2ff','S'],['analyst','Analyst','#ff9f0a','A'],['auditor','Auditor','#bf5af2','U'],\n                ['executor','Executor','#30d158','E'],['risk','Risk','#ff453a','R']];\n  const FIELDS=[['stack','Starting stack $'],['minScore','Minimum score'],['maxPos','Max open positions'],\n    ['sizeMin','Smallest trade % of stack'],['sizeMax','Largest trade % of stack'],['reserve','Cash reserve %'],\n    ['stop','Stop loss %'],['tp','Take profit %'],['trail','Trailing stop %'],['timeH','Time stop hours'],\n    ['slip','Slippage and fees %'],['dayLoss','Daily loss limit %'],['liqMin','Min liquidity $'],\n    ['mcMin','Min market cap $'],['mcMax','Max market cap $'],['volMin','Min 1h volume $'],\n    ['ageMinM','Min age minutes'],['ageMaxH','Max age hours'],['ranMax','Skip if up % this hour']];\n  const RANGES=[['LIVE',15*60e3],['1H',3600e3],['4H',4*3600e3],['1D',24*3600e3],['ALL',0]];\n  let range=4,lastSeen=null,toastTimer=0;\n\n  $('tabs').innerHTML=RANGES.map((r,i)=>'<button type=\"button\" data-i=\"'+i+'\" aria-pressed=\"'+(i===range)+'\">'+r[0]+'</button>').join('');\n  $('tabs').addEventListener('click',e=>{const b=e.target.closest('button');if(!b)return;range=Number(b.dataset.i);\n    [...$('tabs').children].forEach((x,i)=>x.setAttribute('aria-pressed',i===range));chart()});\n\n  function buildSettings(){\n    const c=desk.state.cfg;\n    $('settings').innerHTML=FIELDS.map(([k,l])=>'<label for=\"f-'+k+'\">'+esc(l)+'<input type=\"number\" id=\"f-'+k+'\" min=\"0\" step=\"any\" value=\"'+esc(c[k])+'\"></label>').join('')+\n      '<label class=\"check\" for=\"f-requireAudit\"><input type=\"checkbox\" id=\"f-requireAudit\"'+(c.requireAudit?' checked':'')+'> Require the RugCheck safety check before buying</label>';\n    FIELDS.forEach(([k])=>$('f-'+k).addEventListener('change',e=>{const v=Number(e.target.value);if(isFinite(v)&&v>=0)desk.setCfg(k,v);else e.target.value=desk.state.cfg[k]}));\n    $('f-requireAudit').addEventListener('change',e=>{desk.setCfg('requireAudit',e.target.checked);render()});\n  }\n\n  function chart(){\n    const cv=$('chart'),S=desk.state,dpr=window.devicePixelRatio||1,w=cv.clientWidth,h=130,span=RANGES[range][1];\n    cv.width=w*dpr;cv.height=h*dpr;const g=cv.getContext('2d');g.scale(dpr,dpr);g.clearRect(0,0,w,h);\n    let pts=span?S.equity.filter(p=>p.t>=Date.now()-span):S.equity;\n    const base=pts.length?pts[0].v:S.start,vals=pts.length?pts.map(p=>p.v):[S.start];\n    const lo=Math.min(base,...vals),hi=Math.max(base,...vals),pad=(hi-lo||1)*0.18;\n    const y=v=>h-8-(v-(lo-pad))/((hi+pad)-(lo-pad))*(h-16),x=i=>vals.length>1?i/(vals.length-1)*(w-10)+2:w-8;\n    const col=vals[vals.length-1]>=base?'#30d158':'#ff453a';\n    g.strokeStyle='#2c2c2e';g.setLineDash([2,5]);g.beginPath();g.moveTo(0,y(base));g.lineTo(w,y(base));g.stroke();g.setLineDash([]);\n    g.beginPath();\n    if(vals.length>1)vals.forEach((v,i)=>i?g.lineTo(x(i),y(v)):g.moveTo(x(i),y(v)));else{g.moveTo(0,y(base));g.lineTo(x(0),y(vals[0]))}\n    g.strokeStyle=col;g.lineWidth=2;g.lineJoin='round';g.stroke();\n    g.lineTo(x(vals.length-1),h);g.lineTo(vals.length>1?x(0):0,h);g.closePath();\n    const grad=g.createLinearGradient(0,0,0,h);grad.addColorStop(0,col+'55');grad.addColorStop(1,col+'00');g.fillStyle=grad;g.fill();\n    g.beginPath();g.arc(x(vals.length-1),y(vals[vals.length-1]),4,0,7);g.fillStyle=col;g.fill();\n  }\n\n  function toast(a){\n    const el=$('toast'),sell=a.kind==='sell';\n    el.innerHTML='<span class=\"ico\" style=\"--c:'+(sell?(a.amt>=0?'#30d158':'#ff453a'):'#64d2ff')+'\">'+(sell?'$':'+')+'</span><div class=\"l\"><div class=\"t\">'+esc(a.title)+(sell?'':' · '+usd(-a.amt))+'</div><div class=\"s\">'+esc(a.sub)+(sell?' · <span class=\"'+cls(a.amt)+'\">'+sgn(a.amt)+' ('+pct(a.pct||0)+')</span>':'')+'</div></div>';\n    el.classList.add('on');clearTimeout(toastTimer);toastTimer=setTimeout(()=>el.classList.remove('on'),4500);\n  }\n\n  function render(){\n    const S=desk.state,v=desk.value(),d=v-S.start,x=S.start?v/S.start:1;\n    $('value').textContent=usd(v);$('value').className='big '+(d>0?'up':d<0?'down':'');\n    $('pnl').innerHTML='<span class=\"'+cls(d)+'\">'+(d>=0?'▲':'▼')+' '+usd(Math.abs(d))+' ('+pct(S.start?d/S.start*100:0)+')</span><span class=\"mult'+(d<0?' neg':'')+'\">'+x.toFixed(2)+'x</span>';\n    $('open').textContent=S.positions.length+' open';$('clock').textContent=time(Date.now());\n    $('cash').textContent=usd(S.cash);\n    $('ntrades').textContent=S.closed.length;\n    $('win').textContent=S.closed.length?Math.round(S.closed.filter(c=>c.pnl>0).length/S.closed.length*100)+'%':'n/a';\n    const td=S.day?(v/S.day.v-1)*100:0;$('today').textContent=pct(td);$('today').className=cls(td);\n    const st=$('status');\n    if(S.halted){st.textContent='Halted';st.className='pill stop'}\n    else if(!S.running){st.textContent='Paused';st.className='pill'}\n    else{st.textContent='Live';st.className='pill live'}\n    $('toggle').textContent=S.halted?'Restart desk':S.running?'Pause desk':'Resume desk';\n\n    const b=[];if(offline)b.push(DOWN);\n    if(S.halted)b.push('<div class=\"banner\">'+esc(S.haltReason)+' Press Restart desk to continue.</div>');\n    if(S.errors.dex>=3)b.push('<div class=\"banner\">Price data from DexScreener is not loading. Check your connection. The desk keeps retrying.</div>');\n    if(S.errors.rug>=2)b.push('<div class=\"banner note\">The RugCheck safety check is not reachable'+(S.cfg.requireAudit?', so no coin can pass the Auditor. To keep paper trading without it, open Rules and untick the safety check.':'. Coins are being bought without it.')+'</div>');\n    $('banners').innerHTML=b.join('');\n\n    const F=S.funnel;\n    $('scanline').textContent=S.lastScan?'Last scan '+new Date(S.lastScan).toLocaleTimeString([], {hour:'numeric',minute:'2-digit',second:'2-digit'}):'Waiting for first scan';\n    $('funnel').innerHTML=[[F.tracked,'coins priced'],[F.pass,'pass filters'],[F.scored,'score '+S.cfg.minScore+'+'],[F.safe,'safe to buy']]\n      .map(([n,l])=>'<div><b>'+n+'</b><span>'+esc(l)+'</span></div>').join('');\n    $('watch').innerHTML=S.watch.length?S.watch.map(w=>\n      '<div class=\"row\"><div class=\"l\"><div class=\"t\"><a href=\"https://dexscreener.com/solana/'+esc(w.mint)+'\" target=\"_blank\" rel=\"noopener\">'+esc(w.sym)+'</a> <span class=\"muted\" style=\"font-weight:600;font-size:12px\">'+short(w.mc)+' · <span class=\"'+cls(w.c1)+'\">'+pct(w.c1)+' 1h</span></span></div>'+\n      '<div class=\"bar\"><i class=\"'+(w.score>=S.cfg.minScore?'':'low')+'\" style=\"width:'+Math.max(2,Math.min(100,w.score))+'%\"></i></div><div class=\"s\" style=\"margin-top:4px\">'+esc(w.note)+'</div></div>'+\n      '<div class=\"r\">'+w.score+'<small><span class=\"chip '+(w.state==='ok'?'ok':w.state==='no'?'no':'')+'\">'+(w.state==='ok'?'pass':w.state==='no'?'rejected':'watching')+'</span></small></div></div>').join('')\n      :'<div class=\"empty\">'+(S.lastScan?'No coin passes the filters right now. The desk keeps scanning.':'The coins being checked show up here after the first scan.')+'</div>';\n\n    $('agents').innerHTML=AGENTS.map(([k,n,c,i])=>'<div class=\"row\"><span class=\"ico\" style=\"--c:'+c+'\">'+i+'</span><div class=\"l\"><div class=\"t\">'+n+'</div><div class=\"s\">'+esc(S.agents[k].line)+'</div></div><div class=\"r muted\" style=\"font-size:12px\">'+esc(S.agents[k].met)+'</div></div>').join('');\n\n    $('poscount').textContent=S.positions.length+' of '+S.cfg.maxPos;\n    $('positions').innerHTML=S.positions.length?S.positions.map(p=>{\n      const val=p.qty*p.last,ch=(p.last/p.entry-1)*100;\n      return '<div class=\"row\"><span class=\"ico\">'+esc(p.sym.slice(0,1).toUpperCase())+'</span><div class=\"l\"><div class=\"t\"><a href=\"https://dexscreener.com/solana/'+esc(p.mint)+'\" target=\"_blank\" rel=\"noopener\">'+esc(p.sym)+'</a></div><div class=\"s\">in since '+time(p.opened)+' · score '+esc(p.score)+(p.tp1?' · half sold, trailing':'')+'</div></div><div class=\"r\">'+usd(val)+'<small class=\"'+cls(ch)+'\">'+pct(ch)+'</small></div></div>'}).join('')\n      :'<div class=\"empty\">None yet. The desk buys only when a coin passes every bot.</div>';\n\n    $('activity').innerHTML=S.activity.length?S.activity.slice(0,60).map(a=>{\n      const r=a.kind==='reject'?'<span class=\"muted\">Skipped</span>':a.kind==='sell'?'<span class=\"'+cls(a.amt)+'\">'+sgn(a.amt)+'<small>'+pct(a.pct||0)+'</small></span>':a.kind==='buy'?usd(-a.amt):'';\n      const c=a.kind==='buy'?'#64d2ff':a.kind==='sell'?(a.amt>=0?'#30d158':'#ff453a'):'#3a3a3c',i=a.kind==='buy'?'+':a.kind==='sell'?'$':a.kind==='reject'?'×':'i';\n      return '<div class=\"row\"><span class=\"ico\" style=\"--c:'+c+'\">'+i+'</span><div class=\"l\"><div class=\"t\">'+esc(a.title)+'</div><div class=\"s\">'+esc(a.sub)+' · '+time(a.t)+'</div></div><div class=\"r\">'+r+'</div></div>'}).join('')\n      :'<div class=\"empty\">Buys, sells and rejections show up here with the reason for each.</div>';\n\n    const top=S.activity.find(a=>a.kind==='buy'||a.kind==='sell');\n    if(top&&lastSeen!==null&&top.t>lastSeen)toast(top);\n    lastSeen=top?top.t:0;\n    chart();\n  }\n\n  const DOWN='<div class=\"banner\">Cannot reach the desk script. Check that desk.js is still running on your computer or server.</div>';\n  async function pull(){\n    try{const r=await fetch('/api/state',{cache:'no-store'});if(!r.ok)throw 0;desk.state=await r.json();offline=false}catch(e){offline=true}\n    if(!desk.state){$('banners').innerHTML=DOWN;return}\n    if(!built){buildSettings();built=true}\n    render();\n  }\n  $('toggle').addEventListener('click',()=>{const S=desk.state;if(S)desk.setRunning(S.halted?true:!S.running)});\n  $('reset').addEventListener('click',()=>$('confirm').classList.add('on'));\n  $('no').addEventListener('click',()=>$('confirm').classList.remove('on'));\n  $('yes').addEventListener('click',async()=>{$('confirm').classList.remove('on');if(!desk.state)return;await desk.reset();buildSettings()});\n  window.addEventListener('resize',()=>{if(desk.state)chart()});\n  document.addEventListener('visibilitychange',()=>{if(!document.hidden)pull()});\n  pull();setInterval(pull,3000);\n})();\n</script>\n</body>\n</html>\n";
const view=()=>JSON.stringify({...desk.state,value:desk.value()});
function body(req){return new Promise(res=>{let s='';req.on('data',c=>{s+=c;if(s.length>10000)req.destroy()});req.on('end',()=>{try{res(JSON.parse(s||'{}'))}catch(e){res({})}})})}
http.createServer(async(req,res)=>{
  const url=req.url.split('?')[0],json=()=>{res.writeHead(200,{'content-type':'application/json','cache-control':'no-store'});res.end(view())};
  try{
    if(req.method==='GET'&&url==='/'){res.writeHead(200,{'content-type':'text/html; charset=utf-8','cache-control':'no-store'});return res.end(PAGE)}
    if(req.method==='GET'&&url==='/api/state')return json();
    if(req.method==='POST'&&url==='/api/running'){const b=await body(req);desk.setRunning(!!b.on);if(b.on)doScan();return json()}
    if(req.method==='POST'&&url==='/api/cfg'){
      const b=await body(req);
      if(b.k==='requireAudit')desk.setCfg('requireAudit',!!b.v);
      else if(typeof b.k==='string'&&b.k in desk.DEF&&typeof b.v==='number'&&isFinite(b.v)&&b.v>=0)desk.setCfg(b.k,b.v);
      return json();
    }
    if(req.method==='POST'&&url==='/api/reset'){await body(req);desk.reset();printed=0;doScan();return json()}
    res.writeHead(404,{'content-type':'text/plain'});res.end('Not found');
  }catch(e){res.writeHead(500,{'content-type':'text/plain'});res.end('Error')}
}).listen(PORT,'0.0.0.0',()=>{
  console.log('Paper desk is running with fake money. Stack: $'+desk.value().toFixed(2));
  console.log('Dashboard on this computer:  http://localhost:'+PORT);
  for(const list of Object.values(os.networkInterfaces()))for(const n of list||[])
    if(n.family==='IPv4'&&!n.internal)console.log('Dashboard on the same Wi-Fi:  http://'+n.address+':'+PORT);
  console.log('Leave this window open. Press Ctrl+C to stop.');
  doRisk().then(doScan);
  setInterval(doScan,10000);
  setInterval(doRisk,5000);
});
