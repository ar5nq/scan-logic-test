#!/usr/bin/env node
// ICT confluence scanner — GitHub Actions edition.
//
// Runs on a schedule independent of any device being awake, computes the same
// SCAN read as the terminal.html artifact (logic below is ported verbatim,
// not reimplemented — if you change SCAN in the terminal, ask for this file
// to be resynced so they don't drift), and pushes a phone notification via
// ntfy.sh the moment a watchlist instrument crosses into STRONG.
//
// Needs Node 18+ (built-in fetch). No npm dependencies.

const fs = require('fs');
const path = require('path');
const webpush = require('web-push');

const STATE_PATH = path.join(__dirname, 'state.json');
const NTFY_TOPIC = process.env.NTFY_TOPIC || ''; // optional fallback, see README
const PUSH_SUBSCRIPTION = process.env.PUSH_SUBSCRIPTION || ''; // JSON, pasted from the app's ALERT panel
const VAPID_PUBLIC_KEY = process.env.VAPID_PUBLIC_KEY || '';
const VAPID_PRIVATE_KEY = process.env.VAPID_PRIVATE_KEY || '';
const VAPID_SUBJECT = process.env.VAPID_SUBJECT || 'mailto:example@example.com';

// Every tracked instrument now alerts — no silent subset. Safe to widen
// because the tightened STRONG bar (score>=70 AND 4+ factors, see
// scoreSetup) makes STRONG rare enough on its own that this doesn't turn
// into alert spam. Kept as a derived list so it can never drift from
// INSTRUMENTS.
const INSTRUMENTS = {
  EURUSD: { id:'EURUSD', digits:4, yTickers:['EURUSD=X'] },
  GBPUSD: { id:'GBPUSD', digits:4, yTickers:['GBPUSD=X'] },
  XAUUSD: { id:'XAUUSD', digits:2, yTickers:['XAUUSD=X', 'GC=F'] },   // GC=F = gold futures, reliable fallback
  XAGUSD: { id:'XAGUSD', digits:3, yTickers:['XAGUSD=X', 'SI=F'] },   // SI=F = silver futures, reliable fallback
  NAS100: { id:'NAS100', digits:1, yTickers:['^NDX', 'NQ=F'] },       // NQ=F = Nasdaq futures fallback
  SP500:  { id:'SP500',  digits:1, yTickers:['^GSPC', 'ES=F'] },      // ES=F = S&P futures fallback
  AUDUSD: { id:'AUDUSD', digits:4, yTickers:['AUDUSD=X'] },
  NZDUSD: { id:'NZDUSD', digits:4, yTickers:['NZDUSD=X'] },
  USDJPY: { id:'USDJPY', digits:3, yTickers:['USDJPY=X'] },
  USDCAD: { id:'USDCAD', digits:4, yTickers:['USDCAD=X'] },
  EURGBP: { id:'EURGBP', digits:4, yTickers:['EURGBP=X'] },
  EURJPY: { id:'EURJPY', digits:3, yTickers:['EURJPY=X'] },
  GER40:  { id:'GER40',  digits:1, yTickers:['^GDAXI'] },
  UK100:  { id:'UK100',  digits:1, yTickers:['^FTSE'] },
  US30:   { id:'US30',   digits:1, yTickers:['^DJI', 'YM=F'] },       // YM=F = Dow futures fallback
};

// LIVE/PAID SCOPE: only these 4 passed the R-multiple backtest with a real
// positive edge (NAS100 +0.08R, GER40 +0.04R, UK100 +0.07R, AUDUSD +0.04R
// across 296-1164 trades each). Everything else in the full 15-instrument
// set showed flat-to-negative avg R and is NOT included in alerts until
// the scoring is re-tuned and re-backtested for them specifically.
const WATCHLIST = ['NAS100', 'GER40', 'UK100', 'AUDUSD'];

const SMT_PARTNER = {
  NAS100:'SP500', SP500:'NAS100',
  EURUSD:'GBPUSD', GBPUSD:'EURUSD',
  XAUUSD:'XAGUSD', XAGUSD:'XAUUSD',
  AUDUSD:'NZDUSD', NZDUSD:'AUDUSD',
  USDJPY:'USDCAD', USDCAD:'USDJPY',
  GER40:'UK100',   UK100:'GER40',
  US30:'SP500',
  // EURGBP, EURJPY: no clean correlated partner in this set — confluence-only.
};

function aggregateCandles(bars, factor){
  const out = [];
  for(let i=0;i<bars.length;i+=factor){
    const chunk = bars.slice(i, i+factor);
    if(chunk.length===0) continue;
    out.push({
      t: chunk[0].t,
      o: chunk[0].o,
      c: chunk[chunk.length-1].c,
      h: Math.max(...chunk.map(b=>b.h)),
      l: Math.min(...chunk.map(b=>b.l)),
      v: chunk.reduce((s,b)=> s+(b.v||0), 0),
    });
  }
  return out;
}

function findPivots(bars, lookback=2){
  const highs = [], lows = [];
  for(let i=lookback; i<bars.length-lookback; i++){
    const win = bars.slice(i-lookback, i+lookback+1);
    if(bars[i].h === Math.max(...win.map(b=>b.h))) highs.push({ i, price:bars[i].h, t:bars[i].t });
    if(bars[i].l === Math.min(...win.map(b=>b.l))) lows.push({ i, price:bars[i].l, t:bars[i].t });
  }
  return { highs, lows };
}

function structureTrend(bars, lookback=2){
  const { highs, lows } = findPivots(bars, lookback);
  if(highs.length<2 || lows.length<2) return { bias:'NEUTRAL', reason:'not enough swing structure yet' };
  const h = highs.slice(-2), l = lows.slice(-2);
  const higherHigh = h[1].price > h[0].price;
  const higherLow  = l[1].price > l[0].price;
  if(higherHigh && higherLow) return { bias:'BULLISH', reason:'higher high + higher low' };
  if(!higherHigh && !higherLow) return { bias:'BEARISH', reason:'lower high + lower low' };
  return { bias:'NEUTRAL', reason:'mixed — no clean HH/HL or LH/LL yet' };
}

function lastBreak(bars, refTrend, lookback=2){
  const { highs, lows } = findPivots(bars, lookback);
  if(!highs.length || !lows.length) return null;
  const lastHigh = highs[highs.length-1], lastLow = lows[lows.length-1];
  const brokeHigh = bars.slice(lastHigh.i+1).some(b=> b.c > lastHigh.price);
  const brokeLow  = bars.slice(lastLow.i+1).some(b=> b.c < lastLow.price);
  if(brokeHigh && (!brokeLow || lastHigh.i >= lastLow.i)){
    return { dir:'BULLISH', kind: refTrend==='BEARISH' ? 'MSS' : 'BOS', level:lastHigh.price };
  }
  if(brokeLow && (!brokeHigh || lastLow.i >= lastHigh.i)){
    return { dir:'BEARISH', kind: refTrend==='BULLISH' ? 'MSS' : 'BOS', level:lastLow.price };
  }
  return null;
}

function findFVGs(bars, maxCount=6){
  const out = [];
  for(let i=2;i<bars.length;i++){
    const a=bars[i-2], c=bars[i];
    if(a.h < c.l) out.push({ i, dir:'BULLISH', top:c.l, bottom:a.h });
    else if(a.l > c.h) out.push({ i, dir:'BEARISH', top:a.l, bottom:c.h });
  }
  out.forEach(g=>{
    const after = bars.slice(g.i+1);
    if(g.dir==='BULLISH'){
      g.filled   = after.some(b=> b.l <= g.bottom);
      g.inversed = after.some(b=> b.c <  g.bottom);
    }else{
      g.filled   = after.some(b=> b.h >= g.top);
      g.inversed = after.some(b=> b.c >  g.top);
    }
  });
  return out.slice(-maxCount);
}

function findOrderBlocks(bars, pivots){
  const { highs, lows } = pivots;
  const obs = [];
  highs.forEach(h=>{
    const breakIdx = bars.findIndex((b,idx)=> idx>h.i && b.c>h.price);
    if(breakIdx<0) return;
    for(let j=breakIdx-1; j>=Math.max(0,breakIdx-5); j--){
      if(bars[j].c < bars[j].o){ obs.push({ i:j, type:'BULLISH OB', top:bars[j].h, bottom:bars[j].l }); break; }
    }
  });
  lows.forEach(l=>{
    const breakIdx = bars.findIndex((b,idx)=> idx>l.i && b.c<l.price);
    if(breakIdx<0) return;
    for(let j=breakIdx-1; j>=Math.max(0,breakIdx-5); j--){
      if(bars[j].c > bars[j].o){ obs.push({ i:j, type:'BEARISH OB', top:bars[j].h, bottom:bars[j].l }); break; }
    }
  });
  return obs.sort((a,b)=>a.i-b.i);
}

function computeOTE(pivots){
  const { highs, lows } = pivots;
  if(!highs.length || !lows.length) return null;
  const lastHigh = highs[highs.length-1], lastLow = lows[lows.length-1];
  const range = lastHigh.price - lastLow.price;
  if(range<=0) return null;
  if(lastHigh.i > lastLow.i){ // most recent leg ran low -> high
    return { dir:'BULLISH', top: lastHigh.price - range*0.618, bottom: lastHigh.price - range*0.79 };
  }
  return { dir:'BEARISH', top: lastLow.price + range*0.79, bottom: lastLow.price + range*0.618 };
}

function classifyRange(bars4h, bars1h){
  if(bars4h.length<2 || bars1h.length<2) return null;
  const ref4h = bars4h[bars4h.length-2]; // last fully-closed 4H bar
  const t0 = ref4h.t, t1 = bars4h[bars4h.length-1].t;
  const within = bars1h.filter(b=> b.t!=null && b.t>=t0 && b.t<t1);
  const use1h = within.length ? within : bars1h.slice(-4);
  const h4=ref4h.h, l4=ref4h.l;
  const h1=Math.max(...use1h.map(b=>b.h)), l1=Math.min(...use1h.map(b=>b.l));
  const tol = (h4-l4)*0.03 || h4*0.0005;

  const hCmp = Math.abs(h1-h4)<=tol ? 0 : (h1>h4 ? 1 : -1); // 1H high vs 4H high
  const lCmp = Math.abs(l1-l4)<=tol ? 0 : (l1>l4 ? 1 : -1); // 1H low vs 4H low

  let type, note;
  if(hCmp>0 && lCmp<0){
    type='EXPANDED';
    note="1H has pushed beyond the 4H box on BOTH sides — no clean box left at all. Lowest-quality read of the six; if you trade it anyway, retest-rejection is doing all the work, not the box.";
  }else if(hCmp>0){ // hCmp=1, lCmp is 0 or 1
    type='SHIFTED-UP';
    note="1H has already broken above the 4H high while its low still sits above (or at) the 4H low — the 4H box is running stale to the upside. Lower-quality read; if you trade it, use the 1H high and 4H low as your two extremes, trend-dependent, and retest-rejection matters more here, not less.";
  }else if(lCmp<0){ // hCmp is -1 or 0, lCmp=-1
    type='SHIFTED-DOWN';
    note="1H has already broken below the 4H low while its high still sits below (or at) the 4H high — the 4H box is running stale to the downside. Vice versa of the shifted-up case: use the 1H low and 4H high as your two extremes, trend-dependent, retest-rejection still matters more here.";
  }else if(hCmp===0 && lCmp>0){
    type='ALIGNED-UP';
    note='4H and 1H are trending up together — the highs are riding close to the same level. Break the near 1H high first, then look for continuation through the 4H high, staying with the trend.';
  }else if(hCmp<0 && lCmp===0){
    type='ALIGNED-DOWN';
    note='4H and 1H are trending down together — the lows are riding close to the same level. Break the near 1H low first, then look for continuation through the 4H low, staying with the trend.';
  }else{
    type='NESTED';
    note='1H range sits inside the 4H box. Wait for a break of either 1H extreme, then a retest + rejection of that level, before targeting the opposite 4H extreme.';
  }
  return { type, note, h4, l4, h1, l1 };
}

function readDivergence(pivotsA, pivotsB, idA, idB, kind){
  if(pivotsA.length<2 || pivotsB.length<2) return { text:'Not enough swing points yet', flag:false };
  const a1=pivotsA[pivotsA.length-2], a2=pivotsA[pivotsA.length-1];
  const b1=pivotsB[pivotsB.length-2], b2=pivotsB[pivotsB.length-1];
  const aUp = a2.price > a1.price, bUp = b2.price > b1.price;
  if(aUp !== bUp) return { text: `${idA} printed a ${aUp?'higher':'lower'} ${kind}, ${idB} printed a ${bUp?'higher':'lower'} ${kind} \u2014 that's a divergence`, flag:true, aUp, bUp };
  return { text: `Both printed a ${aUp?'higher':'lower'} ${kind} \u2014 no divergence here`, flag:false, aUp, bUp };
}

// factorCount = how many INDEPENDENT confluence factors fire in the bias
// direction (trend, range, OTE, FVG, OB, SMT — max 6, or 5 for EURGBP/
// EURJPY which have no SMT partner). Score alone rewards magnitude — a
// setup could hit 70+ off just trend+range+FVG with nothing else agreeing.
// factorCount rewards actual agreement across independent signals. STRONG
// now requires both, kept identical to terminal.html's scoring so the two
// never drift on what counts as a real signal.
function scoreSetup({ trend4h, break1h, range, ote, fvgs, obs, smt, price, instId }){
  const bias = break1h ? break1h.dir : (trend4h.bias!=='NEUTRAL' ? trend4h.bias : null);
  if(!bias) return { score:0, bias:null, label:'NO READ', notes:['Not enough clean structure yet on either timeframe.'], withTrend:false, factorCount:0 };
  let score = 0; const notes = []; let factorCount = 0;
  const withTrend = trend4h.bias!=='NEUTRAL' && trend4h.bias===bias;
  if(withTrend){ score+=25; factorCount++; notes.push('With the 4H trend (+25)'); }
  else if(trend4h.bias!=='NEUTRAL'){ score-=20; notes.push('Countertrend vs 4H — this is your ~3W/7L bucket (\u221220)'); }
  if(range){
    if(range.type==='NESTED'){ score+=20; factorCount++; notes.push('Nested 1H-in-4H range — clean breakout+retest structure (+20)'); }
    else if(range.type==='ALIGNED-UP' || range.type==='ALIGNED-DOWN'){ score+=15; factorCount++; notes.push(`Aligned/trending range (${range.type}) (+15)`); }
    else if(range.type==='SHIFTED-UP' || range.type==='SHIFTED-DOWN'){ score-=10; notes.push(`Shifted range (${range.type}) — 4H box running stale on one side, avoid-leaning (\u221210)`); }
    else{ score-=15; notes.push('Expanded range on both sides — no clean box left, avoid-leaning (\u221215)'); }
  }
  let oteHit = false;
  if(ote && ote.dir===bias){
    const inZone = price<=Math.max(ote.top,ote.bottom) && price>=Math.min(ote.top,ote.bottom);
    if(inZone){ score+=15; factorCount++; oteHit = true; notes.push('Price is inside the OTE 61.8\u201379% zone (+15)'); }
  }
  const dirFVGs = (fvgs||[]).filter(g=> g.dir===bias && !g.filled);
  if(dirFVGs.length){ score+=10; factorCount++; notes.push(`${dirFVGs.length} unfilled ${bias.toLowerCase()} FVG in your direction (+10)`); }
  const invFVGs = (fvgs||[]).filter(g=> g.inversed);
  if(invFVGs.length){ score+=10; notes.push(`${invFVGs.length} inversed FVG (IFVG) on the chart — reversal marker (+10)`); }
  if((obs||[]).length){ score+=10; factorCount++; notes.push(`${obs.length} order block(s) mapped on this leg (+10)`); }
  let smtHit = false;
  if(smt){
    const smtRead = (divSet) => {
      if(!divSet) return null;
      if(divSet.lowDiv && divSet.lowDiv.flag && divSet.lowDiv.aUp===false && divSet.lowDiv.bUp===true) return 'bullish';
      if(divSet.highDiv && divSet.highDiv.flag && divSet.highDiv.aUp===true && divSet.highDiv.bUp===false) return 'bearish';
      return null;
    };
    const read1h = smtRead(smt.smt1h);
    const read4h = smtRead(smt.smt4h);

    if(read4h==='bullish' && bias==='BULLISH'){ score+=15; smtHit=true; notes.push(`4H SMT divergence vs ${smt.partnerId} on the low — ${instId} weaker there, bullish tell, HTF (+15)`); }
    else if(read4h==='bearish' && bias==='BEARISH'){ score+=15; smtHit=true; notes.push(`4H SMT divergence vs ${smt.partnerId} on the high — ${instId} stronger there, bearish tell, HTF (+15)`); }

    if(read1h==='bullish' && bias==='BULLISH'){ score+=10; smtHit=true; notes.push(`1H SMT divergence vs ${smt.partnerId} on the low — ${instId} weaker there, bullish tell (+10)`); }
    else if(read1h==='bearish' && bias==='BEARISH'){ score+=10; smtHit=true; notes.push(`1H SMT divergence vs ${smt.partnerId} on the high — ${instId} stronger there, bearish tell (+10)`); }

    if(smtHit) factorCount++; // count once regardless of whether both TFs fired

    if(read1h && read4h && read1h!==read4h){
      notes.push(`Heads up: 1H SMT reads ${read1h}, 4H SMT reads ${read4h} — they disagree, weight the 4H read more`);
    }
  }
  score = Math.max(0, Math.min(100, score));
  const label = (score>=70 && factorCount>=4) ? 'STRONG' : score>=45?'MODERATE':score>=20?'WEAK':'AVOID';
  if(score>=70 && factorCount<4) notes.push(`Score cleared 70 but only ${factorCount} independent factor(s) agreed — held to MODERATE (needs 4+)`);
  return { score, bias, label, notes, withTrend, factorCount };
}

function computeScan(inst, bars4, bars1, partnerBars1, partnerBars4){
  const pivots1  = findPivots(bars1, 2);
  const pivots4  = findPivots(bars4, 2);
  const trend4h  = structureTrend(bars4, 2);
  const break1h  = lastBreak(bars1, trend4h.bias, 2);
  const range    = classifyRange(bars4, bars1);
  const ote      = computeOTE(pivots1);
  const fvgs     = findFVGs(bars1, 6);
  const obs      = findOrderBlocks(bars1, pivots1);
  const partnerId = SMT_PARTNER[inst.id];
  let smt = null;
  if(partnerId && partnerBars1 && partnerBars1.length>=6){
    const pivotsP1 = findPivots(partnerBars1, 2);
    const smt1h = {
      highDiv: readDivergence(pivots1.highs, pivotsP1.highs, inst.id, partnerId, '1H high'),
      lowDiv:  readDivergence(pivots1.lows,  pivotsP1.lows,  inst.id, partnerId, '1H low'),
    };
    let smt4h = null;
    if(partnerBars4 && partnerBars4.length>=6){
      const pivotsP4 = findPivots(partnerBars4, 2);
      smt4h = {
        highDiv: readDivergence(pivots4.highs, pivotsP4.highs, inst.id, partnerId, '4H high'),
        lowDiv:  readDivergence(pivots4.lows,  pivotsP4.lows,  inst.id, partnerId, '4H low'),
      };
    }
    smt = { partnerId, smt1h, smt4h };
  }
  const result   = scoreSetup({ trend4h, break1h, range, ote, fvgs, obs, smt, price: inst.price, instId: inst.id });
  return { trend4h, break1h, range, ote, fvgs, obs, smt, result };
}

async function fetchYahooBarsFrom(host, yTicker, interval, range){
  const url = `https://${host}/v8/finance/chart/${encodeURIComponent(yTicker)}?interval=${interval}&range=${range}`;
  const res = await fetch(url, {
    headers: {
      'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0 Safari/537.36',
      'Accept': 'application/json',
    },
  });
  if(!res.ok) throw new Error(`bad status ${res.status} for ${yTicker} via ${host}`);
  const json = await res.json();
  const result = json?.chart?.result?.[0];
  if(!result) throw new Error(`no chart result for ${yTicker} via ${host}`);
  const times = result.timestamp || [];
  const q = result.indicators?.quote?.[0] || {};
  const bars = [];
  times.forEach((tm,i)=>{
    const o=q.open?.[i], h=q.high?.[i], l=q.low?.[i], c=q.close?.[i];
    if(o!=null && h!=null && l!=null && c!=null) bars.push({ t:tm, o, h, l, c });
  });
  if(bars.length<2) throw new Error(`empty series for ${yTicker} via ${host}`);
  return bars;
}

// query1 occasionally 404s specific symbols (seen on XAUUSD=X/XAGUSD=X from a
// non-browser context) even though the same symbol works fine elsewhere —
// query2 is the same API on a different host and often succeeds when query1
// doesn't. Try both before giving up on an instrument for this run.
async function fetchYahooBars(yTicker, interval, range){
  try{
    return await fetchYahooBarsFrom('query1.finance.yahoo.com', yTicker, interval, range);
  }catch(err1){
    try{
      return await fetchYahooBarsFrom('query2.finance.yahoo.com', yTicker, interval, range);
    }catch(err2){
      throw new Error(`${err1.message} | fallback also failed: ${err2.message}`);
    }
  }
}

// Same trick the browser uses: Yahoo has no native 4H interval, so pull 1H
// bars and bundle every 4 into a 4H candle.
// Some instruments have more than one candidate Yahoo symbol (e.g. gold's
// spot symbol occasionally 404s server-side even though it's fine from a
// browser — GC=F futures is the reliable fallback). Try each in order.
async function get4hAnd1h(yTickers){
  let lastErr;
  for(const yTicker of yTickers){
    try{
      const raw1h = await fetchYahooBars(yTicker, '60m', '5d');
      const bars4 = aggregateCandles(raw1h, 4);
      return { bars4, bars1: raw1h, usedTicker: yTicker };
    }catch(err){
      lastErr = err;
    }
  }
  throw lastErr;
}

// ---- Economic calendar: high-impact release alerts ----------------------
// Source: Forex Factory's own published weekly JSON export (not a scrape —
// this is the file FF itself publishes for third-party tools). Free, no
// key, but rate-limited by FF to ~2 requests/5min per IP — fine here since
// this only runs once per scheduled scan (every ~15min).
const CALENDAR_URL = 'https://nfs.faireconomy.media/ff_calendar_thisweek.json';
// Alert on a high-impact release for any currency actually in our
// instrument set, derived automatically so this can't drift from
// INSTRUMENTS. Indices/metals are USD-sensitive by default.
const RELEVANT_CURRENCIES = new Set(['USD']); // NAS100 & AUDUSD are USD-driven
Object.keys(INSTRUMENTS).forEach(id=>{
  if(!WATCHLIST.includes(id)) return; // scoped to the live 4 only, not the full 15
  if(/^[A-Z]{6}$/.test(id)){ RELEVANT_CURRENCIES.add(id.slice(0,3)); RELEVANT_CURRENCIES.add(id.slice(3,6)); }
});
RELEVANT_CURRENCIES.add('EUR'); // GER40
RELEVANT_CURRENCIES.add('GBP'); // UK100
const ALERT_WINDOW_MIN = 45; // push once an event is this close, not sooner

async function fetchEconCalendar(){
  try{
    const res = await fetch(CALENDAR_URL, { headers:{ 'User-Agent':'Mozilla/5.0' } });
    if(!res.ok) throw new Error(`bad status ${res.status}`);
    return await res.json();
  }catch(err){
    console.error('econ calendar fetch failed:', err.message);
    return [];
  }
}

async function checkEconCalendar(state){
  const events = await fetchEconCalendar();
  if(!events.length) return;
  const now = Date.now();
  state.econAlerted = state.econAlerted || [];
  const alertedSet = new Set(state.econAlerted);

  for(const ev of events){
    const impact = (ev.impact || '').toLowerCase();
    if(impact !== 'high') continue;
    if(!RELEVANT_CURRENCIES.has(ev.country)) continue;
    const evTime = Date.parse(ev.date);
    if(!evTime) continue;
    const minsAway = (evTime - now) / 60000;
    if(minsAway < 0 || minsAway > ALERT_WINDOW_MIN) continue; // too late or too far out

    const key = `${ev.country}|${ev.title}|${ev.date}`;
    if(alertedSet.has(key)) continue;

    const body = [
      `${ev.country} \u00b7 in ${Math.round(minsAway)} min`,
      ev.forecast ? `Forecast: ${ev.forecast}${ev.previous ? ` (prev ${ev.previous})` : ''}` : (ev.previous ? `Previous: ${ev.previous}` : ''),
    ].filter(Boolean).join('\n');
    await pushNotify(`\u26a0\ufe0f HIGH IMPACT: ${ev.title}`, body, 'high');
    console.log(`  -> pushed econ calendar alert: ${ev.title} (${ev.country}, ${Math.round(minsAway)}min)`);
    alertedSet.add(key);
  }

  // prune anything more than ~6h old so this list doesn't grow forever
  state.econAlerted = [...alertedSet].filter(k=>{
    const parts = k.split('|'); const t = Date.parse(parts[parts.length-1]);
    return !t || (now - t) < 6*60*60*1000;
  });
}

async function pushNotify(title, message, priority){
  let sentSomewhere = false;

  // Primary: real Web Push straight to the installed app (via its service
  // worker) — this is what makes the alert land on the home-screen app icon.
  if(PUSH_SUBSCRIPTION && VAPID_PUBLIC_KEY && VAPID_PRIVATE_KEY){
    try{
      webpush.setVapidDetails(VAPID_SUBJECT, VAPID_PUBLIC_KEY, VAPID_PRIVATE_KEY);
      const subscription = JSON.parse(PUSH_SUBSCRIPTION);
      await webpush.sendNotification(subscription, JSON.stringify({ title, body: message }));
      console.log('  web push sent');
      sentSomewhere = true;
    }catch(err){
      console.error('web push failed:', err.message);
    }
  }

  // Optional secondary channel: ntfy.sh, only if you've set NTFY_TOPIC too.
  if(NTFY_TOPIC){
    try{
      const res = await fetch(`https://ntfy.sh/${encodeURIComponent(NTFY_TOPIC)}`, {
        method: 'POST',
        body: message,
        headers: { 'Title': title, 'Priority': priority || 'default', 'Tags': 'chart_with_upwards_trend' },
      });
      if(!res.ok) console.error('ntfy push failed:', res.status, await res.text());
      else sentSomewhere = true;
    }catch(err){
      console.error('ntfy push error:', err.message);
    }
  }

  if(!sentSomewhere){
    console.log('No push channel configured (PUSH_SUBSCRIPTION+VAPID keys, or NTFY_TOPIC) — would have sent:');
    console.log(title, '\n', message);
  }
}

function loadState(){
  try{ return JSON.parse(fs.readFileSync(STATE_PATH, 'utf8')); }
  catch(err){ return {}; }
}
function saveState(state){
  fs.writeFileSync(STATE_PATH, JSON.stringify(state, null, 2) + '\n');
}

async function main(){
  // Manual test mode: fires a push immediately regardless of any instrument's
  // actual state, so you can confirm delivery without waiting for a real
  // STRONG crossover. Triggered by the "Send test push" workflow input.
  if(process.env.TEST_PUSH === 'true'){
    console.log('TEST_PUSH mode — sending a test notification, skipping the actual scan.');
    await pushNotify('\u26a1 SCAN test push', `If you're reading this on your phone, push is wired up correctly. Sent at ${new Date().toISOString()}.`, 'high');
    return;
  }

  const state = loadState();
  const cache = {};

  // High-impact econ releases (CPI, NFP, FOMC, etc.) coming up in the next
  // ~45min for any currency we actually trade — separate from the SCAN
  // confluence alerts below.
  await checkEconCalendar(state);

  // fetch every tracked instrument once (watchlist + their SMT partners)
  const needed = new Set(WATCHLIST);
  WATCHLIST.forEach(id=> { if(SMT_PARTNER[id]) needed.add(SMT_PARTNER[id]); });

  for(const id of needed){
    const inst = INSTRUMENTS[id];
    if(!inst) continue;
    try{
      cache[id] = await get4hAnd1h(inst.yTickers);
      console.log(`fetched ${id}: ${cache[id].bars4.length} x 4H, ${cache[id].bars1.length} x 1H (via ${cache[id].usedTicker})`);
    }catch(err){
      console.error(`fetch failed for ${id}:`, err.message);
    }
  }

  for(const id of WATCHLIST){
    const inst = INSTRUMENTS[id];
    const own = cache[id];
    if(!own || own.bars4.length<6 || own.bars1.length<6){
      console.log(`${id}: not enough bars, skipping this run`);
      continue;
    }
    const partnerId = SMT_PARTNER[id];
    const partnerBars1 = cache[partnerId] ? cache[partnerId].bars1 : null;
    const partnerBars4 = cache[partnerId] ? cache[partnerId].bars4 : null;
    const price = own.bars1[own.bars1.length-1].c;

    const bundle = computeScan({ id, price }, own.bars4, own.bars1, partnerBars1, partnerBars4);
    const prevLabel = state[id];
    console.log(`${id}: ${bundle.result.bias || 'NO READ'} · ${bundle.result.label} (${bundle.result.score}/100), was ${prevLabel || 'unknown'}`);

    if(bundle.result.label==='STRONG' && prevLabel!=='STRONG'){
      const body = [
        `${bundle.result.score}/100 · ${bundle.range ? bundle.range.type : ''}`,
        ...bundle.result.notes,
      ].join('\n');
      await pushNotify(`⚡ SCAN: ${id} STRONG ${bundle.result.bias}`, body, 'high');
      console.log(`  -> pushed STRONG alert for ${id}`);
    }
    state[id] = bundle.result.label;
  }

  saveState(state);
}

main().catch(err=>{ console.error(err); process.exit(1); });
