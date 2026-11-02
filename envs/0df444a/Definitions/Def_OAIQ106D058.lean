-- Prove2me | Definitions.Def_OAIQ106D058
-- name    : OAIQ106D058
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T12:26:54.815787+00:00
-- url     : https://prove2.me/theorems/9c6fb480-fd30-476f-8e49-c0c533c6ad24
-- title:
--   Definitions bundle OAIQ106D058 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1739 declarations of OpenAI's Lean: 1739 definitions. The definitions and types are `OAI.MUB6.Certificate.PairSemantics.raw3001`, `OAI.MUB6.Certificate.PairSemantics.raw3001step0`, `OAI.MUB6.Certificate.PairSemantics.raw3001step1`, `OAI.MUB6.Certificate.PairSemantics.raw3001step2`, `OAI.MUB6.Certificate.PairSemantics.raw3002`, `OAI.MUB6.Certificate.PairSemantics.raw3003`, `OAI.MUB6.Certificate.PairSemantics.raw3003step0`, `OAI.MUB6.Certificate.PairSemantics.raw3003step1`, `OAI.MUB6.Certificate.PairSemantics.raw3004`, `OAI.MUB6.Certificate.PairSemantics.raw3004step0`, `OAI.MUB6.Certificate.PairSemantics.raw3004step1`, `OAI.MUB6.Certificate.PairSemantics.raw3005`, `OAI.MUB6.Certificate.PairSemantics.raw3005step0`, `OAI.MUB6.Certificate.PairSemantics.raw3005step1`, `OAI.MUB6.Certificate.PairSemantics.raw3006`, `OAI.MUB6.Certificate.PairSemantics.raw3006step0`, `OAI.MUB6.Certificate.PairSemantics.raw3006step1`, `OAI.MUB6.Certificate.PairSemantics.raw3007`, `OAI.MUB6.Certificate.PairSemantics.raw3007step0`, `OAI.MUB6.Certificate.PairSemantics.raw3008`, `OAI.MUB6.Certificate.PairSemantics.raw3008step0`, `OAI.MUB6.Certificate.PairSemantics.raw3008step1`, `OAI.MUB6.Certificate.PairSemantics.raw3009`, `OAI.MUB6.Certificate.PairSemantics.raw3009step0`, `OAI.MUB6.Certificate.PairSemantics.raw3009step1`, `OAI.MUB6.Certificate.PairSemantics.raw300step0`, `OAI.MUB6.Certificate.PairSemantics.raw301`, `OAI.MUB6.Certificate.PairSemantics.raw3010`, `OAI.MUB6.Certificate.PairSemantics.raw3010step0`, `OAI.MUB6.Certificate.PairSemantics.raw3011`, `OAI.MUB6.Certificate.PairSemantics.raw3011step0`, `OAI.MUB6.Certificate.PairSemantics.raw3011step1`, `OAI.MUB6.Certificate.PairSemantics.raw3012`, `OAI.MUB6.Certificate.PairSemantics.raw3012step0`, `OAI.MUB6.Certificate.PairSemantics.raw3012step1`, `OAI.MUB6.Certificate.PairSemantics.raw3013`, `OAI.MUB6.Certificate.PairSemantics.raw3013step0`, `OAI.MUB6.Certificate.PairSemantics.raw3013step1`, `OAI.MUB6.Certificate.PairSemantics.raw3014`, `OAI.MUB6.Certificate.PairSemantics.raw3014step0` and 1699 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_PairSemantics_Canonical0`, `MutuallyUnbiased_PairSemantics_Canonical1`, `MutuallyUnbiased_PairSemantics_Canonical10`, `MutuallyUnbiased_PairSemantics_Canonical100`, `MutuallyUnbiased_PairSemantics_Canonical101`, `MutuallyUnbiased_PairSemantics_Canonical102`, `MutuallyUnbiased_PairSemantics_Canonical103`, `MutuallyUnbiased_PairSemantics_Canonical104`, `MutuallyUnbiased_PairSemantics_Canonical105`, `MutuallyUnbiased_PairSemantics_Canonical106`, `MutuallyUnbiased_PairSemantics_Canonical107`, `MutuallyUnbiased_PairSemantics_Canonical108`, `MutuallyUnbiased_PairSemantics_Canonical109`, `MutuallyUnbiased_PairSemantics_Canonical11`, `MutuallyUnbiased_PairSemantics_Canonical110`, `MutuallyUnbiased_PairSemantics_Canonical111`, `MutuallyUnbiased_PairSemantics_Canonical112`, `MutuallyUnbiased_PairSemantics_Canonical113`, `MutuallyUnbiased_PairSemantics_Canonical9`, `MutuallyUnbiased_PairSemantics_Canonical93`, `MutuallyUnbiased_PairSemantics_Canonical94`, `MutuallyUnbiased_PairSemantics_Canonical95`, `MutuallyUnbiased_PairSemantics_Canonical96`, `MutuallyUnbiased_PairSemantics_Canonical97`, `MutuallyUnbiased_PairSemantics_Canonical98`, `MutuallyUnbiased_PairSemantics_Canonical99`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1161`, `OAI.MUB6.Certificate.MixedSemantics.sound1162`, `OAI.MUB6.Certificate.MixedSemantics.sound1163`, `OAI.MUB6.Certificate.MixedSemantics.sound1164`, `OAI.MUB6.Certificate.MixedSemantics.sound1165`, `OAI.MUB6.Certificate.MixedSemantics.sound1168`, `OAI.MUB6.Certificate.MixedSemantics.sound1170`, `OAI.MUB6.Certificate.MixedSemantics.sound1173`, `OAI.MUB6.Certificate.MixedSemantics.sound1339`, `OAI.MUB6.Certificate.MixedSemantics.sound1340`, `OAI.MUB6.Certificate.MixedSemantics.sound1341`, `OAI.MUB6.Certificate.MixedSemantics.sound1342`, `OAI.MUB6.Certificate.MixedSemantics.sound1346`, `OAI.MUB6.Certificate.MixedSemantics.sound206`, `OAI.MUB6.Certificate.MixedSemantics.sound207`, `OAI.MUB6.Certificate.MixedSemantics.sound294`, `OAI.MUB6.Certificate.MixedSemantics.sound644`, `OAI.MUB6.Certificate.MixedSemantics.sound645`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound137`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound139`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound150`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound151`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1013`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1170`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1318`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1484`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1517`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2191`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2198`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2199`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2200`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2201`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2202`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2205`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2206`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2211`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2214`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2216`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2217`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2226`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2227`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2231`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2240`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2241`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2242`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2248`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2252`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2255`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2257`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2261`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2263`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2267`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2268`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2269`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2271`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2272`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2273`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2274`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2275`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2279`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2280`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2282`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2288`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2291`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2292`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2293`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2294`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2297`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2298`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2299`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2300`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2301`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2302`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2303`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2304`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2308`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2309`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2313`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2317`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2318`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2320`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2321`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2322`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2323`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2324`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2326`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2327`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2329`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2330`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2332`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2333`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2335`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2336`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2337`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2338`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2340`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2345`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2346`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2350`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2351`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2352`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2354`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2355`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2356`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2357`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2360`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2363`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2364`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2365`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2366`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2368`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2371`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2375`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2378`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2379`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2381`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2384`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2389`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2391`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2396`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2397`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2398`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2403`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2404`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2406`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2411`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2413`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2414`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2415`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2418`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2419`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2420`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2424`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval117`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval12`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval134`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval141`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval145`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval147`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval149`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval155`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval159`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval165`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval18`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval182`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval202`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval21`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval215`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval218`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval224`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval225`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval37`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval39`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval41`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval46`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval476`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval52`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval54`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval56`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval6`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval63`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval69`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval73`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval74`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval77`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval79`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval8`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval83`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval86`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval91`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval99`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval113`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval150`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval21`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval215`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval216`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval220`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval222`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval44`, `OAI.MUB6.Certificate.PairSemantics.boundarySound165`, `OAI.MUB6.Certificate.PairSemantics.boundarySound243`, `OAI.MUB6.Certificate.PairSemantics.boundarySound248`, `OAI.MUB6.Certificate.PairSemantics.boundarySound252`, `OAI.MUB6.Certificate.PairSemantics.boundarySound261`, `OAI.MUB6.Certificate.PairSemantics.boundarySound264`, `OAI.MUB6.Certificate.PairSemantics.boundarySound445`, `OAI.MUB6.Certificate.PairSemantics.boundarySound454`, `OAI.MUB6.Certificate.PairSemantics.boundarySound49`, `OAI.MUB6.Certificate.PairSemantics.boundarySound51`, `OAI.MUB6.Certificate.PairSemantics.boundarySound75`, `OAI.MUB6.Certificate.PairSemantics.boundarySound83`, `OAI.MUB6.Certificate.PairSemantics.boundarySound97`, `OAI.MUB6.Certificate.PairSemantics.sound1381`, `OAI.MUB6.Certificate.PairSemantics.sound1383`, `OAI.MUB6.Certificate.PairSemantics.sound1384`, `OAI.MUB6.Certificate.PairSemantics.sound1387`, `OAI.MUB6.Certificate.PairSemantics.sound1390`, `OAI.MUB6.Certificate.PairSemantics.sound1391`, `OAI.MUB6.Certificate.PairSemantics.sound1395`, `OAI.MUB6.Certificate.PairSemantics.sound1399`, `OAI.MUB6.Certificate.PairSemantics.sound1414`, `OAI.MUB6.Certificate.PairSemantics.sound1424`, `OAI.MUB6.Certificate.PairSemantics.sound1437`, `OAI.MUB6.Certificate.PairSemantics.sound1443`, `OAI.MUB6.Certificate.PairSemantics.sound1512`, `OAI.MUB6.Certificate.PairSemantics.sound1518`, `OAI.MUB6.Certificate.PairSemantics.sound1520`, `OAI.MUB6.Certificate.PairSemantics.sound1523`, `OAI.MUB6.Certificate.PairSemantics.sound1533`, `OAI.MUB6.Certificate.PairSemantics.sound1540`, `OAI.MUB6.Certificate.PairSemantics.sound1614`, `OAI.MUB6.Certificate.PairSemantics.sound1617`, `OAI.MUB6.Certificate.PairSemantics.sound1638`, `OAI.MUB6.Certificate.PairSemantics.sound1646`, `OAI.MUB6.Certificate.PairSemantics.sound1648`, `OAI.MUB6.Certificate.PairSemantics.sound1652`, `OAI.MUB6.Certificate.PairSemantics.sound1707`, `OAI.MUB6.Certificate.PairSemantics.sound1716`, `OAI.MUB6.Certificate.PairSemantics.sound1718`, `OAI.MUB6.Certificate.PairSemantics.sound1769`, `OAI.MUB6.Certificate.PairSemantics.sound1826`, `OAI.MUB6.Certificate.PairSemantics.sound1828`, `OAI.MUB6.Certificate.PairSemantics.sound1865`, `OAI.MUB6.Certificate.PairSemantics.sound1867`, `OAI.MUB6.Certificate.PairSemantics.sound1869`, `OAI.MUB6.Certificate.PairSemantics.sound1870`, `OAI.MUB6.Certificate.PairSemantics.sound1872`, `OAI.MUB6.Certificate.PairSemantics.sound1873`, `OAI.MUB6.Certificate.PairSemantics.sound1879`, `OAI.MUB6.Certificate.PairSemantics.sound1938`, `OAI.MUB6.Certificate.PairSemantics.sound1968`, `OAI.MUB6.Certificate.PairSemantics.sound1977`, `OAI.MUB6.Certificate.PairSemantics.sound1978`, `OAI.MUB6.Certificate.PairSemantics.sound1980`, `OAI.MUB6.Certificate.PairSemantics.sound1986`, `OAI.MUB6.Certificate.PairSemantics.sound1987`, `OAI.MUB6.Certificate.PairSemantics.sound2041`, `OAI.MUB6.Certificate.PairSemantics.sound2106`, `OAI.MUB6.Certificate.PairSemantics.sound2108`, `OAI.MUB6.Certificate.PairSemantics.sound2113`, `OAI.MUB6.Certificate.PairSemantics.sound2117`, `OAI.MUB6.Certificate.PairSemantics.sound2123`, `OAI.MUB6.Certificate.PairSemantics.sound2152`, `OAI.MUB6.Certificate.PairSemantics.sound2204`, `OAI.MUB6.Certificate.PairSemantics.sound2286`, `OAI.MUB6.Certificate.PairSemantics.sound2294`, `OAI.MUB6.Certificate.PairSemantics.sound2307`, `OAI.MUB6.Certificate.PairSemantics.sound2375`, `OAI.MUB6.Certificate.PairSemantics.sound2389`, `OAI.MUB6.Certificate.PairSemantics.sound2413`, `OAI.MUB6.Certificate.PairSemantics.sound2414`, `OAI.MUB6.Certificate.PairSemantics.sound2417`, `OAI.MUB6.Certificate.PairSemantics.sound2456`, `OAI.MUB6.Certificate.PairSemantics.sound2457`, `OAI.MUB6.Certificate.PairSemantics.sound2473`, `OAI.MUB6.Certificate.PairSemantics.sound2477`, `OAI.MUB6.Certificate.PairSemantics.sound2489`, `OAI.MUB6.Certificate.PairSemantics.sound2520`, `OAI.MUB6.Certificate.PairSemantics.sound2525`, `OAI.MUB6.Certificate.PairSemantics.sound2670`, `OAI.MUB6.Certificate.PairSemantics.sound2852`, `OAI.MUB6.Certificate.PairSemantics.sound2854`, `OAI.MUB6.Certificate.PairSemantics.sound2863`, `OAI.MUB6.Certificate.PairSemantics.sound2864`, `OAI.MUB6.Certificate.PairSemantics.sound2865`, `OAI.MUB6.Certificate.PairSemantics.sound2866`, `OAI.MUB6.Certificate.PairSemantics.sound2867`, `OAI.MUB6.Certificate.PairSemantics.sound2868`, `OAI.MUB6.Certificate.PairSemantics.sound2872`, `OAI.MUB6.Certificate.PairSemantics.sound2873`, `OAI.MUB6.Certificate.PairSemantics.sound2875`, `OAI.MUB6.Certificate.PairSemantics.sound2880`, `OAI.MUB6.Certificate.PairSemantics.sound2881`, `OAI.MUB6.Certificate.PairSemantics.sound2883`, `OAI.MUB6.Certificate.PairSemantics.sound2884`, `OAI.MUB6.Certificate.PairSemantics.sound2887`, `OAI.MUB6.Certificate.PairSemantics.sound2888`, `OAI.MUB6.Certificate.PairSemantics.sound2890`, `OAI.MUB6.Certificate.PairSemantics.sound2891`, `OAI.MUB6.Certificate.PairSemantics.sound2892`, `OAI.MUB6.Certificate.PairSemantics.sound2894`, `OAI.MUB6.Certificate.PairSemantics.sound2895`, `OAI.MUB6.Certificate.PairSemantics.sound2896`, `OAI.MUB6.Certificate.PairSemantics.sound2897`, `OAI.MUB6.Certificate.PairSemantics.sound2898`, `OAI.MUB6.Certificate.PairSemantics.sound2899`, `OAI.MUB6.Certificate.PairSemantics.sound2901`, `OAI.MUB6.Certificate.PairSemantics.sound2902`, `OAI.MUB6.Certificate.PairSemantics.sound2903`, `OAI.MUB6.Certificate.PairSemantics.sound2906`, `OAI.MUB6.Certificate.PairSemantics.sound2909`, `OAI.MUB6.Certificate.PairSemantics.sound2912`, `OAI.MUB6.Certificate.PairSemantics.sound2913`, `OAI.MUB6.Certificate.PairSemantics.sound2914`, `OAI.MUB6.Certificate.PairSemantics.sound2915`, `OAI.MUB6.Certificate.PairSemantics.sound2916`, `OAI.MUB6.Certificate.PairSemantics.sound2917`, `OAI.MUB6.Certificate.PairSemantics.sound2918`, `OAI.MUB6.Certificate.PairSemantics.sound2922`, `OAI.MUB6.Certificate.PairSemantics.sound2924`, `OAI.MUB6.Certificate.PairSemantics.sound2929`, `OAI.MUB6.Certificate.PairSemantics.sound2930`, `OAI.MUB6.Certificate.PairSemantics.sound2931`, `OAI.MUB6.Certificate.PairSemantics.sound2933`, `OAI.MUB6.Certificate.PairSemantics.sound2936`, `OAI.MUB6.Certificate.PairSemantics.sound2939`, `OAI.MUB6.Certificate.PairSemantics.sound2940`, `OAI.MUB6.Certificate.PairSemantics.sound2941`, `OAI.MUB6.Certificate.PairSemantics.sound2944`, `OAI.MUB6.Certificate.PairSemantics.sound2947`, `OAI.MUB6.Certificate.PairSemantics.sound2948`, `OAI.MUB6.Certificate.PairSemantics.sound2949`, `OAI.MUB6.Certificate.PairSemantics.sound2950`, `OAI.MUB6.Certificate.PairSemantics.sound2953`, `OAI.MUB6.Certificate.PairSemantics.sound2955`, `OAI.MUB6.Certificate.PairSemantics.sound2956`, `OAI.MUB6.Certificate.PairSemantics.sound2958`, `OAI.MUB6.Certificate.PairSemantics.sound2960`, `OAI.MUB6.Certificate.PairSemantics.sound2962`, `OAI.MUB6.Certificate.PairSemantics.sound2964`, `OAI.MUB6.Certificate.PairSemantics.sound2965`, `OAI.MUB6.Certificate.PairSemantics.sound2966`, `OAI.MUB6.Certificate.PairSemantics.sound2968`, `OAI.MUB6.Certificate.PairSemantics.sound2970`, `OAI.MUB6.Certificate.PairSemantics.sound2973`, `OAI.MUB6.Certificate.PairSemantics.sound2975`, `OAI.MUB6.Certificate.PairSemantics.sound2976`, `OAI.MUB6.Certificate.PairSemantics.sound2977`, `OAI.MUB6.Certificate.PairSemantics.sound2979`, `OAI.MUB6.Certificate.PairSemantics.sound2980`, `OAI.MUB6.Certificate.PairSemantics.sound2982`, `OAI.MUB6.Certificate.PairSemantics.sound2986`, `OAI.MUB6.Certificate.PairSemantics.sound2988`, `OAI.MUB6.Certificate.PairSemantics.sound2989`, `OAI.MUB6.Certificate.PairSemantics.sound2990`, `OAI.MUB6.Certificate.PairSemantics.sound2991`, `OAI.MUB6.Certificate.PairSemantics.sound2993`, `OAI.MUB6.Certificate.PairSemantics.sound2994`, `OAI.MUB6.Certificate.PairSemantics.sound2996`, `OAI.MUB6.Certificate.PairSemantics.sound2997`, `OAI.MUB6.Certificate.PairSemantics.sound2998`, `OAI.MUB6.Certificate.PairSemantics.sound2999`, `OAI.MUB6.Certificate.PairSemantics.sound3000`, `OAI.MUB6.Certificate.PairSemantics.sound3001`, `OAI.MUB6.Certificate.PairSemantics.sound3006`, `OAI.MUB6.Certificate.PairSemantics.sound3009`, `OAI.MUB6.Certificate.PairSemantics.sound3010`, `OAI.MUB6.Certificate.PairSemantics.sound3011`, `OAI.MUB6.Certificate.PairSemantics.sound3012`, `OAI.MUB6.Certificate.PairSemantics.sound3013`, `OAI.MUB6.Certificate.PairSemantics.sound3014`, `OAI.MUB6.Certificate.PairSemantics.sound3015`, `OAI.MUB6.Certificate.PairSemantics.sound3016`, `OAI.MUB6.Certificate.PairSemantics.sound3017`, `OAI.MUB6.Certificate.PairSemantics.sound3018`, `OAI.MUB6.Certificate.PairSemantics.sound3019`, `OAI.MUB6.Certificate.PairSemantics.sound3020`, `OAI.MUB6.Certificate.PairSemantics.sound3021`, `OAI.MUB6.Certificate.PairSemantics.sound3022`, `OAI.MUB6.Certificate.PairSemantics.sound3023`, `OAI.MUB6.Certificate.PairSemantics.sound3027`, `OAI.MUB6.Certificate.PairSemantics.sound3029`, `OAI.MUB6.Certificate.PairSemantics.sound3030`, `OAI.MUB6.Certificate.PairSemantics.sound3033`, `OAI.MUB6.Certificate.PairSemantics.sound3034`, `OAI.MUB6.Certificate.PairSemantics.sound3035`, `OAI.MUB6.Certificate.PairSemantics.sound3039`, `OAI.MUB6.Certificate.PairSemantics.sound3040`, `OAI.MUB6.Certificate.PairSemantics.sound3043`, `OAI.MUB6.Certificate.PairSemantics.sound3044`, `OAI.MUB6.Certificate.PairSemantics.sound3047`, `OAI.MUB6.Certificate.PairSemantics.sound3049`, `OAI.MUB6.Certificate.PairSemantics.sound3051`, `OAI.MUB6.Certificate.PairSemantics.sound3056`, `OAI.MUB6.Certificate.PairSemantics.sound3058`, `OAI.MUB6.Certificate.PairSemantics.sound3061`, `OAI.MUB6.Certificate.PairSemantics.sound3063`, `OAI.MUB6.Certificate.PairSemantics.sound3072`, `OAI.MUB6.Certificate.PairSemantics.sound3073`, `OAI.MUB6.Certificate.PairSemantics.sound3074`, `OAI.MUB6.Certificate.PairSemantics.sound3076`, `OAI.MUB6.Certificate.PairSemantics.sound3078`, `OAI.MUB6.Certificate.PairSemantics.sound3080`, `OAI.MUB6.Certificate.PairSemantics.sound3081`, `OAI.MUB6.Certificate.PairSemantics.sound3082`, `OAI.MUB6.Certificate.PairSemantics.sound3083`, `OAI.MUB6.Certificate.PairSemantics.sound3084`, `OAI.MUB6.Certificate.PairSemantics.sound3085`, `OAI.MUB6.Certificate.PairSemantics.sound3092`, `OAI.MUB6.Certificate.PairSemantics.sound3093`, `OAI.MUB6.Certificate.PairSemantics.sound3094`, `OAI.MUB6.Certificate.PairSemantics.sound3097`, `OAI.MUB6.Certificate.PairSemantics.sound3100`, `OAI.MUB6.Certificate.PairSemantics.sound3101`, `OAI.MUB6.Certificate.PairSemantics.sound3102`, `OAI.MUB6.Certificate.PairSemantics.sound3106`, `OAI.MUB6.Certificate.PairSemantics.sound3107`, `OAI.MUB6.Certificate.PairSemantics.sound3108`, `OAI.MUB6.Certificate.PairSemantics.sound3109`, `OAI.MUB6.Certificate.PairSemantics.sound3110`, `OAI.MUB6.Certificate.PairSemantics.sound3111`, `OAI.MUB6.Certificate.PairSemantics.sound3112`, `OAI.MUB6.Certificate.PairSemantics.sound3113`, `OAI.MUB6.Certificate.PairSemantics.sound3114`, `OAI.MUB6.Certificate.PairSemantics.sound3115`, `OAI.MUB6.Certificate.PairSemantics.sound3116`, `OAI.MUB6.Certificate.PairSemantics.sound3118`, `OAI.MUB6.Certificate.PairSemantics.sound3119`, `OAI.MUB6.Certificate.PairSemantics.sound3120`, `OAI.MUB6.Certificate.PairSemantics.sound3121`, `OAI.MUB6.Certificate.PairSemantics.sound3122`, `OAI.MUB6.Certificate.PairSemantics.sound3123`, `OAI.MUB6.Certificate.PairSemantics.sound3124`, `OAI.MUB6.Certificate.PairSemantics.sound3125`, `OAI.MUB6.Certificate.PairSemantics.sound3128`, `OAI.MUB6.Certificate.PairSemantics.sound3129`, `OAI.MUB6.Certificate.PairSemantics.sound3130`, `OAI.MUB6.Certificate.PairSemantics.sound3131`, `OAI.MUB6.Certificate.PairSemantics.sound3133`, `OAI.MUB6.Certificate.PairSemantics.sound3135`, `OAI.MUB6.Certificate.PairSemantics.sound3136`, `OAI.MUB6.Certificate.PairSemantics.sound3138`, `OAI.MUB6.Certificate.PairSemantics.sound3139`, `OAI.MUB6.Certificate.PairSemantics.sound3140`, `OAI.MUB6.Certificate.PairSemantics.sound3141`, `OAI.MUB6.Certificate.PairSemantics.sound3142`, `OAI.MUB6.Certificate.PairSemantics.sound3144`, `OAI.MUB6.Certificate.PairSemantics.sound3145`, `OAI.MUB6.Certificate.PairSemantics.sound3146`, `OAI.MUB6.Certificate.PairSemantics.sound3150`, `OAI.MUB6.Certificate.PairSemantics.sound3151`, `OAI.MUB6.Certificate.PairSemantics.sound3152`, `OAI.MUB6.Certificate.PairSemantics.sound3153`, `OAI.MUB6.Certificate.PairSemantics.sound3155`, `OAI.MUB6.Certificate.PairSemantics.sound3158`, `OAI.MUB6.Certificate.PairSemantics.sound3159`, `OAI.MUB6.Certificate.PairSemantics.sound3160`, `OAI.MUB6.Certificate.PairSemantics.sound3161`, `OAI.MUB6.Certificate.PairSemantics.sound3162`, `OAI.MUB6.Certificate.PairSemantics.sound3163`, `OAI.MUB6.Certificate.PairSemantics.sound3164`, `OAI.MUB6.Certificate.PairSemantics.sound3166`, `OAI.MUB6.Certificate.PairSemantics.sound3167`, `OAI.MUB6.Certificate.PairSemantics.sound3168`, `OAI.MUB6.Certificate.PairSemantics.sound3169`, `OAI.MUB6.Certificate.PairSemantics.sound3170`, `OAI.MUB6.Certificate.PairSemantics.sound3171`, `OAI.MUB6.Certificate.PairSemantics.sound3172`, `OAI.MUB6.Certificate.PairSemantics.sound3173`, `OAI.MUB6.Certificate.PairSemantics.sound3174`, `OAI.MUB6.Certificate.PairSemantics.sound3176`, `OAI.MUB6.Certificate.PairSemantics.sound3178`, `OAI.MUB6.Certificate.PairSemantics.sound3179`, `OAI.MUB6.Certificate.PairSemantics.sound3180`, `OAI.MUB6.Certificate.PairSemantics.sound3181`, `OAI.MUB6.Certificate.PairSemantics.sound3183`, `OAI.MUB6.Certificate.PairSemantics.sound3184`, `OAI.MUB6.Certificate.PairSemantics.sound3185`, `OAI.MUB6.Certificate.PairSemantics.sound3186`, `OAI.MUB6.Certificate.PairSemantics.sound3187`, `OAI.MUB6.Certificate.PairSemantics.sound3188`, `OAI.MUB6.Certificate.PairSemantics.sound3189`, `OAI.MUB6.Certificate.PairSemantics.sound3191`, `OAI.MUB6.Certificate.PairSemantics.sound3192`, `OAI.MUB6.Certificate.PairSemantics.sound3193`, `OAI.MUB6.Certificate.PairSemantics.sound3194`, `OAI.MUB6.Certificate.PairSemantics.sound3195`, `OAI.MUB6.Certificate.PairSemantics.sound3196`, `OAI.MUB6.Certificate.PairSemantics.sound3197`, `OAI.MUB6.Certificate.PairSemantics.sound3201`, `OAI.MUB6.Certificate.PairSemantics.sound3202`, `OAI.MUB6.Certificate.PairSemantics.sound3206`, `OAI.MUB6.Certificate.PairSemantics.sound3208`, `OAI.MUB6.Certificate.PairSemantics.sound3213`, `OAI.MUB6.Certificate.PairSemantics.sound3214`, `OAI.MUB6.Certificate.PairSemantics.sound3215`, `OAI.MUB6.Certificate.PairSemantics.sound3216`, `OAI.MUB6.Certificate.PairSemantics.sound3217`, `OAI.MUB6.Certificate.PairSemantics.sound3218`, `OAI.MUB6.Certificate.PairSemantics.sound3219`, `OAI.MUB6.Certificate.PairSemantics.sound3221`, `OAI.MUB6.Certificate.PairSemantics.sound3223`, `OAI.MUB6.Certificate.PairSemantics.sound3224`, `OAI.MUB6.Certificate.PairSemantics.sound3226`, `OAI.MUB6.Certificate.PairSemantics.sound3227`, `OAI.MUB6.Certificate.PairSemantics.sound3228`, `OAI.MUB6.Certificate.PairSemantics.sound3230`, `OAI.MUB6.Certificate.PairSemantics.sound3237`, `OAI.MUB6.Certificate.PairSemantics.sound3238`, `OAI.MUB6.Certificate.PairSemantics.sound3239`, `OAI.MUB6.Certificate.PairSemantics.sound3240`, `OAI.MUB6.Certificate.PairSemantics.sound3241`, `OAI.MUB6.Certificate.PairSemantics.sound3244`, `OAI.MUB6.Certificate.PairSemantics.sound3246`, `OAI.MUB6.Certificate.PairSemantics.sound3247`, `OAI.MUB6.Certificate.PairSemantics.sound3248`, `OAI.MUB6.Certificate.PairSemantics.sound3250`, `OAI.MUB6.Certificate.PairSemantics.sound3254`, `OAI.MUB6.Certificate.PairSemantics.sound3256`, `OAI.MUB6.Certificate.PairSemantics.sound3258`, `OAI.MUB6.Certificate.PairSemantics.sound3263`, `OAI.MUB6.Certificate.PairSemantics.sound3267`, `OAI.MUB6.Certificate.PairSemantics.sound3268`, `OAI.MUB6.Certificate.PairSemantics.sound3269`, `OAI.MUB6.Certificate.PairSemantics.sound3270`, `OAI.MUB6.Certificate.PairSemantics.sound3271`, `OAI.MUB6.Certificate.PairSemantics.sound3273`, `OAI.MUB6.Certificate.PairSemantics.sound3275`, `OAI.MUB6.Certificate.PairSemantics.sound3276`, `OAI.MUB6.Certificate.PairSemantics.sound3277`, `OAI.MUB6.Certificate.PairSemantics.sound3279`, `OAI.MUB6.Certificate.PairSemantics.sound3282`, `OAI.MUB6.Certificate.PairSemantics.sound3284`, `OAI.MUB6.Certificate.PairSemantics.sound3288`, `OAI.MUB6.Certificate.PairSemantics.sound3289`, `OAI.MUB6.Certificate.PairSemantics.sound3290`, `OAI.MUB6.Certificate.PairSemantics.sound3292`, `OAI.MUB6.Certificate.PairSemantics.sound3293`, `OAI.MUB6.Certificate.PairSemantics.sound3294`, `OAI.MUB6.Certificate.PairSemantics.sound3296`, `OAI.MUB6.Certificate.PairSemantics.sound3297`, `OAI.MUB6.Certificate.PairSemantics.sound3299`, `OAI.MUB6.Certificate.PairSemantics.sound3301`, `OAI.MUB6.Certificate.PairSemantics.sound3307`, `OAI.MUB6.Certificate.PairSemantics.sound3310`, `OAI.MUB6.Certificate.PairSemantics.sound3312`, `OAI.MUB6.Certificate.PairSemantics.sound3313`, `OAI.MUB6.Certificate.PairSemantics.sound3314`, `OAI.MUB6.Certificate.PairSemantics.sound3315`, `OAI.MUB6.Certificate.PairSemantics.sound3316`, `OAI.MUB6.Certificate.PairSemantics.sound3317`, `OAI.MUB6.Certificate.PairSemantics.sound3322`, `OAI.MUB6.Certificate.PairSemantics.sound3323`, `OAI.MUB6.Certificate.PairSemantics.sound3324`, `OAI.MUB6.Certificate.PairSemantics.sound3325`, `OAI.MUB6.Certificate.PairSemantics.sound3327`, `OAI.MUB6.Certificate.PairSemantics.sound3328`, `OAI.MUB6.Certificate.PairSemantics.sound3332`, `OAI.MUB6.Certificate.PairSemantics.sound3333`, `OAI.MUB6.Certificate.PairSemantics.sound3335`, `OAI.MUB6.Certificate.PairSemantics.sound3336`, `OAI.MUB6.Certificate.PairSemantics.sound3357`, `OAI.MUB6.Certificate.PairSemantics.sound3360`, `OAI.MUB6.Certificate.PairSemantics.sound3361`, `OAI.MUB6.Certificate.PairSemantics.sound3362`, `OAI.MUB6.Certificate.PairSemantics.sound3366`, `OAI.MUB6.Certificate.PairSemantics.sound3367`, `OAI.MUB6.Certificate.PairSemantics.sound3369`, `OAI.MUB6.Certificate.PairSemantics.sound3381`, `OAI.MUB6.Certificate.PairSemantics.sound3382`, `OAI.MUB6.Certificate.PairSemantics.sound3383`, `OAI.MUB6.Certificate.PairSemantics.sound3384`, `OAI.MUB6.Certificate.PairSemantics.sound3385`, `OAI.MUB6.Certificate.PairSemantics.sound3408`, `OAI.MUB6.Certificate.PairSemantics.sound3411`, `OAI.MUB6.Certificate.PairSemantics.sound3412`, `OAI.MUB6.Certificate.PairSemantics.sound3418`, `OAI.MUB6.Certificate.PairSemantics.sound3421`, `OAI.MUB6.Certificate.PairSemantics.sound3454`, `OAI.MUB6.Certificate.PairSemantics.sound3456`, `OAI.MUB6.Certificate.PairSemantics.sound3459`, `OAI.MUB6.Certificate.PairSemantics.sound3460`, `OAI.MUB6.Certificate.PairSemantics.sound3461`, `OAI.MUB6.Certificate.PairSemantics.sound3463`, `OAI.MUB6.Certificate.PairSemantics.sound3468`, `OAI.MUB6.Certificate.PairSourceBridge.allRowsSound`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound100`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound101`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound103`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound104`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound105`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound106`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound107`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound111`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound112`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound113`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound115`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound121`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound124`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound125`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound126`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound127`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound130`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound131`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound132`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound133`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound134`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound135`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound136`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound137`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound141`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound142`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound146`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound15`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound150`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound151`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound153`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound154`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound155`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound156`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound159`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound160`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound162`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound163`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound165`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound166`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound167`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound168`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound170`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound175`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound176`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound180`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound181`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound182`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound184`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound185`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound186`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound187`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound190`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound193`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound194`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound195`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound196`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound198`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound201`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound205`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound208`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound209`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound211`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound214`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound219`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound221`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound226`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound227`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound228`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound233`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound234`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound236`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound241`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound242`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound243`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound244`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound245`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound246`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound248`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound249`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound250`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound254`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound26`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound30`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound31`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound34`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound35`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound36`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound40`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound41`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound46`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound49`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound51`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound52`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound61`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound62`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound65`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound72`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound74`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound80`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound84`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound87`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound89`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound93`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound95`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound99` and `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm26`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw30step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![-2, 2, 0], ![-3, 0, 3]]

def raw30step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 3, -3], ![2, 0, -2]]

def raw31 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -1, -1], ![3, -1, -2]]

def raw31step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![-2, 1, 1], ![-3, 1, 2]]

def raw31step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![1, 1, -2], ![1, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw32 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 0, -2], ![3, -2, -1]]

def raw32step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![-2, 0, 2], ![-3, 2, 1]]

def raw32step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![2, 1, -3]]

def raw33 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 1, -3], ![3, -3, 0]]

def raw33step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![-2, -1, 3], ![-3, 3, 0]]

def raw33step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![3, -1, -2]]

def raw34 : Matrix (Fin 2) (Fin 3) ℤ := ![![-5, 2, 3], ![5, -2, -3]]

def raw34step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![2, -2], ![3, -3]]

def raw35 : Matrix (Fin 2) (Fin 3) ℤ := ![![-5, 3, 2], ![5, -3, -2]]

def raw35step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![3, -3], ![2, -2]]

def raw35step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![2, -2], ![3, -3]]

def raw36 : Matrix (Fin 6) (Fin 2) ℤ := ![![-5, 5], ![0, 0], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]

def raw41step0 : Matrix (Fin 2) (Fin 2) ℤ := ![![-5, 5], ![5, -5]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw320 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![3, -2, -1]]

def raw321 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 0, -1], ![1, 3, -4]]

def raw321step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 2, -1], ![-1, 0, 1], ![-1, -3, 4]]

def raw321step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]

def raw322 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]

def raw323 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 2, -3], ![1, 1, -2]]

def raw323step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]

def raw324 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![2, 3, -5]]

def raw324step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -2, 3], ![4, 1, -5]]

def raw324step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -3, 2], ![1, 4, -5]]

def raw325 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]

def raw326 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

def raw326step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]

def raw326step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def raw327 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]

def raw327step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2]]

def raw328 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![2, 2, -4]]

def raw328step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![4, 0, -4]]

def raw328step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-4, 0, 4]]

def raw328step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 4, -4], ![1, -2, 1]]

def raw329 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 0, -1], ![1, -1, 0], ![1, 2, -3]]

def raw329step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-1, 1, 0], ![-1, -2, 3]]

def raw329step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def raw330 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 1, -2], ![1, -1, 0], ![1, 1, -2]]

def raw330step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2]]

def raw331 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 2, -3], ![1, -2, 1], ![1, 1, -2]]

def raw331step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]

def raw332 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 2, -3], ![1, -1, 0], ![1, 0, -1]]

def raw332step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, -2, 3], ![-1, 1, 0], ![-1, 0, 1]]

def raw332step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def raw333 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 2, -3], ![2, -1, -1]]

def raw333step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, -2, 3], ![-2, 1, 1]]

def raw333step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -2, 1], ![1, 3, -4]]

def raw334 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 3, -4], ![1, -2, 1], ![1, 0, -1]]

def raw334step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, -3, 4], ![-1, 2, -1], ![-1, 0, 1]]

def raw334step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]

def raw335 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 3, -4], ![2, -2, 0]]

def raw335step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![4, -4, 0]]

def raw335step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 4, -4], ![2, -3, 1]]

def raw336 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![2, -2, 0], ![1, 3, -4]]

def raw336step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![4, 0, -4]]

def raw336step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 4, -4], ![2, -3, 1]]

def raw337 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 0, 3], ![0, -2, 2, 0], ![3, 2, -2, -3]]

def raw337step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![3, 0, -3]]

def raw337step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 3, -3], ![2, 0, -2]]

def raw338 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 0, 3], ![1, -2, 2, -1], ![2, 2, -2, -2]]

def raw338step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]

def raw339 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 1, 2], ![-2, 2, 1, -1], ![5, -2, -2, -1]]

def raw339step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

def raw340 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 1, 2], ![-1, 2, -2, 1], ![4, -2, 1, -3]]

def raw340step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]

def raw341 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 1, 2], ![-1, 2, 1, -2], ![4, -2, -2, 0]]

def raw341step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

def raw342 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 1, 2], ![-1, 3, -2, 0], ![4, -3, 1, -2]]

def raw342step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]

def raw343 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 1, 2], ![0, -2, 1, 1], ![3, 2, -2, -3]]

def raw343step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 1, -2], ![2, 1, -3]]

def raw343step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 1, -2], ![1, 2, -3]]

def raw344 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 1, 2], ![0, -2, 2, 0], ![3, 2, -3, -2]]

def raw344step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]

def raw344step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, -2, 3], ![-2, 0, 2]]

def raw344step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![2, 0, -2]]

def raw345 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 1, 2], ![0, -2, 3, -1], ![3, 2, -4, -1]]

def raw345step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 3, -4], ![2, -1, -1]]

def raw345step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, -3, 4], ![-2, 1, 1]]

def raw345step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]

def raw346 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 1, 2], ![0, 2, -2, 0], ![3, -2, 1, -2]]

def raw346step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]

def raw346step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]

def raw346step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

def raw347 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 1, 2], ![0, 3, -2, -1], ![3, -3, 1, -1]]

def raw347step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]

def raw348 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 1, 2], ![0, 4, -2, -2], ![3, -4, 1, 0]]

def raw348step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 4, -4], ![1, -2, 1], ![2, -2, 0]]

def raw349 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 1, 2], ![1, -2, 1, 0], ![2, 2, -2, -2]]

def raw349step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]

def raw349step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

def raw350 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 1, 2], ![1, -2, 2, -1], ![2, 2, -3, -1]]

def raw350step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]

def raw351 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 1, 2], ![1, -2, 3, -2], ![2, 2, -4, 0]]

def raw351step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 3, -4], ![2, -2, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical100
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3200 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw3200step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![-1, -1, 0, 2], ![3, 0, -1, -2]]

def raw3200step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![1, 1, 0, -2], ![-3, 0, 1, 2]]

def raw3200step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -3, 2], ![1, 0, 1, -2]]

def raw3201 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 0, 0, -1]]

def raw3201step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw3202 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def raw3203 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, -1, 2, -2]]

def raw3204 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -2, 1, -1]]

def raw3204step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![-1, -1, 1, 1], ![3, 0, -2, -1]]

def raw3204step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![1, 1, -1, -1], ![-3, 0, 2, 1]]

def raw3204step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -3, 1], ![1, -1, 1, -1]]

def raw3205 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def raw3206 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, -1, 1, -1]]

def raw3207 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw3207step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw3208 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, -2, 0, 0]]

def raw3208step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![-1, -1, 2, 0], ![3, 0, -3, 0]]

def raw3208step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -2, 0, 1]]

def raw3209 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def raw3210 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw3211 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, -1, 1]]

def raw3211step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw3212 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![2, -2, -1, 1]]

def raw3212step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![-1, -1, 3, -1], ![3, 0, -4, 1]]

def raw3212step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -2, 2, 0], ![0, 3, 1, -4], ![1, 0, -2, 1]]

def raw3213 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 1, 2, -4]]

def raw3213step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![-1, -1, 0, 2], ![3, 0, 1, -4]]

def raw3213step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw3214 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 1, 1, -3]]

def raw3214step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![-1, -1, 1, 1], ![3, 0, 0, -3]]

def raw3214step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -2, 0, 1]]

def raw3215 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 1, 0, -2]]

def raw3215step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![-1, -1, 2, 0], ![3, 0, -1, -2]]

def raw3215step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 2, -1], ![1, 1, -2, 0], ![-3, 0, 1, 2]]

def raw3215step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -3, 1], ![1, 0, 1, -2]]

def raw3216 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![1, -2, 3, -2], ![1, 1, -1, -1]]

def raw3216step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![-1, -1, 3, -1], ![3, 0, -2, -1]]

def raw3216step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def raw3217 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 3, -4]]

def raw3217step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![-1, -1, -1, 3], ![3, 0, 1, -4]]

def raw3217step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw3218 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw3218step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![-1, -1, 0, 2], ![3, 0, 0, -3]]

def raw3218step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -1, 0, 0]]

def raw3219 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw3219step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, -1, 1, 0], ![-1, 1, -1, 1], ![-1, 0, -1, 2]]

def raw3219step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -1, 2], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw3220 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def raw3220step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![-1, -1, 2, 0], ![3, 0, -2, -1]]

def raw3220step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw3221 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw3221step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![-1, -1, 3, -1], ![3, 0, -3, 0]]

def raw3221step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw3222 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, -1, 3, -3]]

def raw3222step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 0, -1], ![-1, -1, -1, 3], ![3, 0, 0, -3]]

def raw3222step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw3223 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, -1, 2, -2]]

def raw3223step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 0, -1], ![-1, -1, 0, 2], ![3, 0, -1, -2]]

def raw3223step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw3224 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 0, 1, -2]]

def raw3224step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def raw3225 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw3225step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -2, -1]]

def raw3226 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw3226step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, -1, -2]]

def raw3227 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 0, -1], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def raw3227step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![-1, 0, -1, 2], ![3, -1, 0, -2]]

def raw3227step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![1, 0, 1, -2], ![-3, 1, 0, 2]]

def raw3227step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -3, 2], ![1, 0, 1, -2]]

def raw3228 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def raw3228step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 2, -2, -1]]

def raw3229 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 2, -2]]

def raw3229step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 2, -1, -2]]

def raw3230 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def raw3230step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw3231 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw3231step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, -1, 0, 1], ![0, -1, -2, 3], ![-1, 1, 1, -1], ![-1, 1, 0, 0]]

def raw3231step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, 2, -3], ![1, 1, -1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical101
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3232 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 1, -1, -1]]

def raw3232step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![-1, 0, 2, -1], ![3, -1, -1, -1]]

def raw3232step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw3233 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 1, -2, 0]]

def raw3233step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![-1, 0, 3, -2], ![3, -1, -2, 0]]

def raw3233step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 2, -1], ![1, 0, -3, 2], ![-3, 1, 2, 0]]

def raw3233step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, 0, -3, 2]]

def raw3234 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 2, -3]]

def raw3234step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw3235 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw3235step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![-1, 0, 2, -1], ![3, -1, -2, 0]]

def raw3235step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw3236 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 0, -1], ![1, -1, 3, -3], ![1, 0, -2, 1]]

def raw3236step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, -1, 0, 1], ![-1, 1, -3, 3], ![-1, 0, 2, -1]]

def raw3236step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, -1, -3, 3]]

def raw3237 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, -1, 3, -3]]

def raw3237step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, -1, 0, 1], ![-1, 0, 2, -1], ![-1, 1, -3, 3]]

def raw3237step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, -1, -3, 3]]

def raw3238 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 1, -2], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 0, 0, -1]]

def raw3238step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw3239 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 1, -2], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def raw3239step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![-1, 1, -1, 1], ![3, -2, 0, -1]]

def raw3239step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![1, -1, 1, -1], ![-3, 2, 0, 1]]

def raw3239step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -3, 1], ![1, -1, 1, -1]]

def raw3240 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 1, -2], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def raw3240step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw3241 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 1, -1, -1]]

def raw3241step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw3242 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 1, -2, 0]]

def raw3243 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def raw3243step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, -1, -1, 2], ![-1, 1, 1, -1], ![-1, 0, -1, 2]]

def raw3243step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, 1, -1, -1]]

def raw3244 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw3244step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, -1, -1, 2], ![-1, 1, -1, 1], ![-1, 0, 1, 0]]

def raw3244step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1]]

def raw3245 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 1, -2], ![1, 0, -2, 1], ![1, -1, 2, -2]]

def raw3245step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, -1, -1, 2], ![-1, 0, 2, -1], ![-1, 1, -2, 2]]

def raw3245step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, -1, -2, 2]]

def raw3246 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 2, -3], ![0, 1, -2, 1], ![2, -2, 1, -1]]

def raw3246step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![2, -2, 1, -1]]

def raw3247 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 2, -3], ![0, 1, -1, 0], ![2, -2, 0, 0]]

def raw3247step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![-1, 2, -1, 0], ![3, -3, 0, 0]]

def raw3247step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -2, 0, 1]]

def raw3248 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 2, -3], ![1, -2, 1, 0], ![1, 1, -2, 0]]

def raw3249 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw3249step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, -1, -2, 3], ![-1, 1, 1, -1], ![-1, 0, 0, 1]]

def raw3249step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 1, -1, -1]]

def raw3250 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw3250step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![-1, 2, 0, -1], ![3, -3, 0, 0]]

def raw3250step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 1, 0], ![1, -2, 0, 1], ![-3, 3, 0, 0]]

def raw3250step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, -1, 0]]

def raw3251 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 0, -2, 1]]

def raw3251step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, -1, -2, 3], ![-1, 1, -1, 1], ![-1, 0, 2, -1]]

def raw3251step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw3252 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 2, -3], ![1, 0, -2, 1], ![1, -1, 1, -1]]

def raw3252step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, -1, -2, 3], ![-1, 0, 2, -1], ![-1, 1, -1, 1]]

def raw3252step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw3253 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 3, -4], ![1, -2, 0, 1], ![1, 1, -2, 0]]

def raw3254 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw3254step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![-1, 3, -1, -1], ![3, -4, 1, 0]]

def raw3254step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 0, 1], ![0, 1, 3, -4], ![1, 1, -2, 0]]

def raw3255 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw3255step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![-1, 3, 0, -2], ![3, -4, 0, 1]]

def raw3255step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 1, 0], ![1, -3, 0, 2], ![-3, 4, 0, -1]]

def raw3255step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -3, 4], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw3256 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 3, -4], ![1, 0, -2, 1], ![1, -1, 0, 0]]

def raw3256step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 0, -1], ![-1, 3, -2, 0], ![3, -4, 1, 0]]

def raw3256step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 0, 1], ![1, -3, 2, 0], ![-3, 4, -1, 0]]

def raw3256step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -3, 4], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw3257 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def raw3257step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![-1, -2, 0, 3], ![3, 0, 1, -4]]

def raw3257step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 3, -4], ![2, -2, 0, 0]]

def raw3258 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -2, 1, 0], ![1, 0, 2, -3]]

def raw3259 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -2, 2, -1], ![1, 0, 1, -2]]

def raw3260 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw3260step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![-1, -2, 3, 0], ![3, 0, -2, -1]]

def raw3260step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -2, 2, 0], ![1, 2, -3, 0], ![-3, 0, 2, 1]]

def raw3260step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 2, 1, -3], ![1, 0, -3, 2]]

def raw3261 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw3261step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![-1, -2, 0, 3], ![3, 0, 0, -3]]

def raw3261step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -2, 1, 1], ![1, 2, 0, -3], ![-3, 0, 0, 3]]

def raw3261step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -3, 3], ![0, 2, 1, -3], ![1, -2, 0, 1]]

def raw3262 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def raw3263 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -1, 2, -2], ![1, -1, 1, -1]]

def raw3263step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, -1, 2, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical102
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3264 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -1, -1], ![1, -2, 1, 0], ![1, 0, 1, -2]]

def raw3264step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def raw3265 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -1, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw3265step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![-1, -1, 2, 0], ![3, -1, -1, -1]]

def raw3265step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def raw3266 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -1, -1], ![1, -2, 3, -2], ![1, 0, -1, 0]]

def raw3266step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![-1, -1, 3, -1], ![3, -1, -2, 0]]

def raw3266step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw3267 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, -1, 3, -3]]

def raw3268 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw3268step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![-1, -1, 0, 2], ![3, -1, 0, -2]]

def raw3268step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -2, 1, 1], ![1, 1, 0, -2], ![-3, 1, 0, 2]]

def raw3268step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw3269 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def raw3269step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def raw3270 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, 0, -2], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def raw3270step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![-1, 0, 2, -1], ![3, -2, -1, 0]]

def raw3270step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -2, 2, 0], ![1, 0, -2, 1], ![-3, 2, 1, 0]]

def raw3270step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 2, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw3271 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, -1, 2, -2]]

def raw3271step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 2, -1, -2]]

def raw3272 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, 1, -3], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def raw3272step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![-1, 1, 1, -1], ![3, -3, 0, 0]]

def raw3272step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -2, 2, 0], ![1, -1, -1, 1], ![-3, 3, 0, 0]]

def raw3272step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, -1, 1]]

def raw3273 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, 1, -3], ![1, -1, -1, 1], ![1, -1, 1, -1]]

def raw3273step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def raw3274 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, 2, -4], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def raw3274step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![-1, 2, 0, -1], ![3, -4, 1, 0]]

def raw3274step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -2, 2, 0], ![1, -2, 0, 1], ![-3, 4, -1, 0]]

def raw3274step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw3275 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, 2, -4], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw3275step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![-1, 2, -1, 0], ![3, -4, 1, 0]]

def raw3275step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, 1, -2, 0]]

def raw3276 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![1, -2, 2, -1], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def raw3276step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -2, 2, -1], ![1, 0, 1, -2]]

def raw3277 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![1, -2, 3, -2], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def raw3277step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![1, -2, 3, -2], ![1, 1, 0, -2]]

def raw3278 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![1, -2, 3, -2], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw3278step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 2, 0], ![-1, 3, -2, 0], ![3, -2, 0, -1]]

def raw3278step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 2, -2, 0], ![1, -3, 2, 0], ![-3, 2, 0, 1]]

def raw3278step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 2, 1, -3], ![1, 0, -3, 2]]

def raw3279 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![1, -2, 3, -2], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw3279step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 2, 0], ![-1, 3, -1, -1], ![3, -2, -1, 0]]

def raw3279step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw3280 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![1, -1, 2, -2], ![0, 2, -2, 0], ![1, -1, 1, -1]]

def raw3280step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def raw3281 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![1, -1, 3, -3], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw3281step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 2, -1], ![-1, 3, -2, 0], ![3, -3, 0, 0]]

def raw3281step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 1, -2, 1], ![1, -3, 2, 0], ![-3, 3, 0, 0]]

def raw3281step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -3, 3], ![0, 2, 1, -3], ![1, -2, 0, 1]]

def raw3282 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![1, -1, 3, -3], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw3282step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, -1, 3, -3]]

def raw3283 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![1, 0, -2, 1], ![0, 1, 1, -2], ![1, -1, 2, -2]]

def raw3283step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![-1, 0, 2, -1], ![0, -1, -1, 2], ![-1, 1, -2, 2]]

def raw3283step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, -1, -2, 2]]

def raw3284 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![1, 0, -2, 1], ![0, 1, 2, -3], ![1, -1, 1, -1]]

def raw3284step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![-1, 0, 2, -1], ![0, -1, -2, 3], ![-1, 1, -1, 1]]

def raw3284step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw3285 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![1, 0, -2, 1], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw3285step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![-1, -2, 3, 0], ![3, 1, -4, 0]]

def raw3285step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, -1, 1], ![1, 2, -3, 0], ![-3, -1, 4, 0]]

def raw3285step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -3, 4], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw3286 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![1, 0, 1, -2], ![0, 2, -1, -1], ![1, -2, 1, 0]]

def raw3286step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def raw3287 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![1, 0, 2, -3], ![0, 2, -2, 0], ![1, -2, 1, 0]]

def raw3287step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -2, 1, 0], ![1, 0, 2, -3]]

def raw3288 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 2, 2, -2], ![4, -2, -2, 0]]

def raw3288step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 2, -2], ![2, -2, 0]]

def raw3289 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, -2, 2, 1], ![3, 2, -2, -3]]

def raw3289step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![2, 1, -3]]

def raw3290 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, -2, 3, 0], ![3, 2, -3, -2]]

def raw3290step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![2, 0, -2]]

def raw3291 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, -2, 4, -1], ![3, 2, -4, -1]]

def raw3291step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 4, -4], ![2, -1, -1]]

def raw3292 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -3, 3, 0], ![2, 3, -3, -2]]

def raw3292step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 3, -3], ![2, 0, -2]]

def raw3293 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -3, 4, -1], ![2, 3, -4, -1]]

def raw3293step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 4, -4], ![2, -1, -1]]

def raw3294 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 0, 2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw3294step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, 0, -2], ![0, -1, 1, 0], ![-1, 0, 1, 0], ![-1, -1, -2, 4]]

def raw3294step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw3295 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 0, 2], ![0, 1, -1, 0], ![1, 1, -2, 0], ![1, 0, 3, -4]]

def raw3295step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 0, 2], ![0, 1, -1, 0], ![1, 0, 3, -4], ![1, 1, -2, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical103
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3296 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 0, 2], ![0, 1, 3, -4], ![2, 1, -3, 0]]

def raw3296step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 0, 3, -3], ![2, 2, -4, 0]]

def raw3296step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, -1, -1], ![0, 0, -3, 3], ![-2, -2, 4, 0]]

def raw3296step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 3, -3], ![0, 2, -2, 0], ![2, 0, -1, -1]]

def raw3297 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 0, 2], ![0, 2, -2, 0], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def raw3297step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![2, 0, -2, 0]]

def raw3298 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 0, 2], ![0, 2, 2, -4], ![2, 0, -2, 0]]

def raw3298step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, 0, -2], ![0, -2, -2, 4], ![-2, 0, 2, 0]]

def raw3298step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![2, 0, 0, -2]]

def raw3299 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 0, 2], ![1, 0, 3, -4], ![1, 2, -3, 0]]

def raw3299step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 0, 2], ![0, 0, 3, -3], ![2, 2, -4, 0]]

def raw3299step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 2, 0, -2], ![0, 0, -3, 3], ![-2, -2, 4, 0]]

def raw3299step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 3, -3], ![0, 2, -2, 0], ![2, 0, -1, -1]]

def raw3300 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 0, 2], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def raw3300step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, 0, -2], ![-1, -1, 1, 1], ![-1, -1, -1, 3]]

def raw3300step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw3301 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 0, 2], ![1, 1, 2, -4], ![1, 1, -2, 0]]

def raw3301step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 0, 2, -2], ![2, 2, -4, 0]]

def raw3301step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 2, -1, -1], ![0, 0, -2, 2], ![-2, -2, 4, 0]]

def raw3301step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw3302 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, -2, 1], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw3303 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, -2, 1], ![2, 1, 1, -4]]

def raw3303step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, -1, -1], ![0, -1, 2, -1], ![-2, -1, -1, 4]]

def raw3303step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def raw3304 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 0, -2, 1], ![1, 1, 2, -4]]

def raw3305 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw3306 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw3306step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, 0, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -2, 1]]

def raw3307 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw3308 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw3308step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, -1, -1], ![0, -1, 0, 1], ![-1, 0, 0, 1], ![-1, -1, 1, 1]]

def raw3308step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw3309 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -2, 0]]

def raw3310 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw3311 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, 1, -2], ![2, 1, -2, -1]]

def raw3311step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, -1, -1], ![0, -1, -1, 2], ![-2, -1, 2, 1]]

def raw3311step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def raw3312 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw3313 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 2, -2, 0], ![1, 0, 1, -2], ![1, 0, 0, -1]]

def raw3313step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw3314 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 2, -2, 0], ![2, 0, 1, -3]]

def raw3314step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, -1, -1], ![0, -2, 2, 0], ![-2, 0, -1, 3]]

def raw3314step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![2, 0, 0, -2]]

def raw3315 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw3315step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1]]

def raw3316 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![1, 0, -2, 1], ![1, 2, 1, -4]]

def raw3316step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, -1, -1], ![-1, 0, 2, -1], ![-1, -2, -1, 4]]

def raw3316step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw3317 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![1, 0, -1, 0], ![1, 2, 0, -3]]

def raw3317step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -2, 0, 1]]

def raw3318 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![1, 0, 1, -2], ![1, 2, -2, -1]]

def raw3318step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, -1, -1], ![-1, 0, -1, 2], ![-1, -2, 2, 1]]

def raw3318step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw3319 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![1, 1, -3, 1], ![1, 1, 2, -4]]

def raw3319step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 1, -3, 2], ![2, 1, 1, -4]]

def raw3319step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 2, -1, -1], ![0, -1, 3, -2], ![-2, -1, -1, 4]]

def raw3319step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 3, -2], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw3320 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![1, 1, -2, 0], ![1, 1, 1, -3]]

def raw3320step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 1, -2, 1], ![2, 1, 0, -3]]

def raw3320step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 2, -1, -1], ![0, -1, 2, -1], ![-2, -1, 0, 3]]

def raw3320step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw3321 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def raw3321step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, -1, -1], ![-1, -1, 1, 1], ![-1, -1, 0, 2]]

def raw3321step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw3322 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![1, 1, 0, -2], ![1, 1, -1, -1]]

def raw3322step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, -1, -1], ![-1, -1, 0, 2], ![-1, -1, 1, 1]]

def raw3322step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw3323 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![1, 1, 1, -3], ![1, 1, -2, 0]]

def raw3323step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 1, 1, -2], ![2, 1, -3, 0]]

def raw3323step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 2, -1, -1], ![0, -1, -1, 2], ![-2, -1, 3, 0]]

def raw3323step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw3324 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![1, 2, -2, -1], ![1, 0, 1, -2]]

def raw3324step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, -1, -1], ![-1, -2, 2, 1], ![-1, 0, -1, 2]]

def raw3324step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw3325 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw3326 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw3327 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical104
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3328 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, -1, 0], ![1, 1, -1, -1], ![1, 0, 0, -1]]

def raw3328step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw3329 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, -1, 0], ![2, 1, -1, -2]]

def raw3329step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def raw3329step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw3330 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw3331 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 1, 0, -2]]

def raw3332 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw3333 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw3333step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, -2, 0], ![0, -1, 0, 1], ![-1, 0, 0, 1], ![-1, -1, 2, 0]]

def raw3333step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw3334 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![1, 1, -2, 0], ![1, 0, 0, -1]]

def raw3334step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, -2, 0], ![0, -1, 0, 1], ![-1, -1, 2, 0], ![-1, 0, 0, 1]]

def raw3334step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw3335 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![1, 1, -1, -1], ![1, 0, -1, 0]]

def raw3335step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw3336 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def raw3336step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw3336step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -2, 0, 1]]

def raw3337 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw3337step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw3338 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 2, -2, 0], ![2, 0, 0, -2]]

def raw3339 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw3340 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 2, 0, -2], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def raw3341 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw3341step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw3342 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 2, 0, -2], ![2, 0, -2, 0]]

def raw3343 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![1, 0, -2, 1], ![1, 2, 0, -3]]

def raw3343step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, -2, 0], ![-1, 0, 2, -1], ![-1, -2, 0, 3]]

def raw3343step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -2, 0]]

def raw3344 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![1, 0, -1, 0], ![1, 2, -1, -2]]

def raw3344step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 0, 2], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def raw3344step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -2, 0, 1]]

def raw3345 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![1, 0, 0, -1], ![1, 2, -2, -1]]

def raw3345step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 0, 2], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw3345step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw3346 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def raw3346step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, -2, 0], ![-1, -1, 2, 0], ![-1, -1, 0, 2]]

def raw3346step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw3347 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def raw3348 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![1, 2, 0, -3], ![1, 0, -2, 1]]

def raw3348step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, -2, 0], ![-1, -2, 0, 3], ![-1, 0, 2, -1]]

def raw3348step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -2, 0]]

def raw3349 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![2, 2, -2, -2]]

def raw3349step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![2, 0, -2]]

def raw3350 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 3, -1], ![2, 2, -3, -1]]

def raw3350step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

def raw3351 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 4, -2], ![2, 2, -4, 0]]

def raw3351step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 4, -4], ![2, -2, 0]]

def raw3352 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 0, 0, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw3352step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 1, -2], ![0, 0, 0, 0], ![-1, 0, 1, 0], ![-1, -1, -2, 4]]

def raw3352step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 1, -2], ![-1, 0, 1, 0], ![-1, -1, -2, 4]]

def raw3352step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

def raw3353 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw3353step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 1, -2], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, -1, -2, 4]]

def raw3353step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw3354 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def raw3354step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def raw3355 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![2, 0, 2, -4]]

def raw3355step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -1, 0, 0]]

def raw3356 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def raw3356step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def raw3357 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw3358 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw3358step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 1, -2], ![0, -1, -3, 4], ![-1, 0, 1, 0], ![-1, 0, 1, 0]]

def raw3358step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw3359 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![2, 0, -2, 0]]

def raw3359step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 1, -2], ![0, -1, -3, 4], ![-2, 0, 2, 0]]

def raw3359step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -2, 2, 0], ![0, 2, 0, -2], ![1, 0, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical105
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3360 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw3361 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 2, -2, 0], ![2, -1, 3, -4]]

def raw3361step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, -1, -2, 3], ![2, 2, 0, -4]]

def raw3361step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![-2, -2, 0, 4]]

def raw3361step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![0, 1, 2, -3], ![2, 0, 0, -2]]

def raw3362 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw3362step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 1, -2], ![0, -2, -2, 4], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw3362step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw3363 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw3363step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 1, -2], ![-1, 0, 1, 0], ![-1, -1, -2, 4]]

def raw3363step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

def raw3364 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![1, 0, 0, -1], ![1, 1, 1, -3]]

def raw3364step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 1, -2], ![-1, 0, 0, 1], ![-1, -1, -1, 3]]

def raw3364step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def raw3365 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![1, 0, 3, -4], ![1, 1, -2, 0]]

def raw3365step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 1, -2], ![-1, 0, -3, 4], ![-1, -1, 2, 0]]

def raw3365step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw3366 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![1, 1, -2, 0], ![1, 0, 3, -4]]

def raw3366step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 1, -2], ![-1, -1, 2, 0], ![-1, 0, -3, 4]]

def raw3366step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw3367 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw3367step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![0, -1, 1, 0], ![-1, 0, 1, 0], ![-1, -1, -2, 4]]

def raw3367step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw3368 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![2, 1, 1, -4]]

def raw3368step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 0, -1], ![0, 1, -1, 0], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-2, -1, -1, 4]]

def raw3368step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw3369 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 1, -3]]

def raw3369step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 0, -1], ![0, 1, -1, 0], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-2, 0, -1, 3]]

def raw3369step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw3370 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw3371 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 2, 2, -5]]

def raw3371step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, -2, -2, 5]]

def raw3371step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw3372 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw3372step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 0, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, -1, -2, 4]]

def raw3372step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw3373 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, 2, -4]]

def raw3373step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 0, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![0, -2, -2, 4]]

def raw3373step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw3374 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw3374step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 0, -1], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, -2, 3]]

def raw3374step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw3375 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 2, -3]]

def raw3375step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 0, -1], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-2, 1, -2, 3]]

def raw3375step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw3376 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def raw3376step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 0, -1], ![0, -1, 1, 0], ![-1, 1, 1, -1], ![-1, -1, -2, 4]]

def raw3376step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw3377 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 1, 2, -3]]

def raw3377step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 0, -1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![0, -1, -2, 3]]

def raw3377step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw3378 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![1, 0, -2, 1], ![1, 1, 2, -4]]

def raw3378step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 0, -1], ![-1, 0, 2, -1], ![-1, -1, -2, 4]]

def raw3378step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw3379 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw3379step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 0, -1], ![-1, 0, 1, 0], ![-1, -1, -1, 3]]

def raw3379step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw3380 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw3380step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 0, -1], ![-1, 0, -1, 2], ![-1, -1, 1, 1]]

def raw3380step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1]]

def raw3381 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw3381step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, -1, 0], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![-1, -1, -1, 3]]

def raw3381step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw3382 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, 0, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw3382step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw3382step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, -1, 0, 0]]

def raw3383 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, 0, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw3383step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw3383step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw3384 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, 0, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw3384step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![0, -1, 0, 0, 1], ![0, 1, 0, 0, -1], ![2, 0, 0, -1, -1]]

def raw3384step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw3384step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw3385 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw3385step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw3386 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw3386step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, -1, 0], ![0, 0, -1, 1], ![-1, 0, 1, 0], ![-1, -1, 1, 1]]

def raw3386step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw3387 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw3387step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, -1, 0], ![0, 0, -1, 1], ![-1, 0, 0, 1], ![-1, -1, 2, 0]]

def raw3387step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw3388 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 0, 0, 0], ![2, 0, 0, -2]]

def raw3388step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw3388step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, -1, 0, 0]]

def raw3389 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 0, 1, -1], ![2, 0, -1, -1]]

def raw3389step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, -1, 0], ![0, -1, 1, 0], ![0, 0, -1, 1], ![-2, 0, 1, 1]]

def raw3389step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw3390 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def raw3390step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw3391 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def raw3391step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, -1, 0], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-2, 1, 0, 1]]

def raw3391step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical106
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3392 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def raw3393 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw3394 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw3394step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw3395 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw3395step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0]]

def raw3396 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw3396step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, -1, 0, 0]]

def raw3397 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 0, 1, -1], ![2, 0, -2, 0]]

def raw3397step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw3398 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw3398step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw3399 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw3399step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw3400 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw3401 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw3401step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw3402 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, -1, 0]]

def raw3402step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw3403 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw3403step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw3404 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 2, -1, -1], ![2, -1, 0, -1]]

def raw3404step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw3405 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![1, 0, -2, 1], ![1, 1, 1, -3]]

def raw3405step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, -1, 0], ![-1, 0, 2, -1], ![-1, -1, -1, 3]]

def raw3405step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw3406 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw3406step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw3406step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw3407 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![1, 0, 1, -2], ![1, 1, -2, 0]]

def raw3407step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, -1, 0], ![-1, 0, -1, 2], ![-1, -1, 2, 0]]

def raw3407step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw3408 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![1, 1, -2, 0], ![1, 0, 1, -2]]

def raw3408step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, -1, 0], ![-1, -1, 2, 0], ![-1, 0, -1, 2]]

def raw3408step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw3409 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![1, 1, -1, -1], ![1, 0, 0, -1]]

def raw3409step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![2, 0, -1, -1]]

def raw3409step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw3410 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw3410step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1]]

def raw3411 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw3411step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -1, -1, 0]]

def raw3412 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw3413 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def raw3413step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, -2, 1], ![0, -1, 0, 1], ![-1, 0, 2, -1], ![-1, 0, 0, 1]]

def raw3413step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw3414 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw3414step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw3415 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw3415step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw3416 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 1, 1, -2], ![2, 0, -3, 1]]

def raw3416step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 2, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw3417 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 2, -3, 1], ![2, -1, 1, -2]]

def raw3417step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, -2, 1], ![0, -2, 3, -1], ![-2, 1, -1, 2]]

def raw3417step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -2, 2, -1], ![1, 0, 1, -2]]

def raw3418 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, -1, -1, 0]]

def raw3419 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![1, -1, 0, 0], ![1, 2, -2, -1]]

def raw3419step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![2, -1, 0, -1]]

def raw3419step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw3420 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![1, 0, -2, 1], ![1, 1, 0, -2]]

def raw3420step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, -2, 1], ![-1, 0, 2, -1], ![-1, -1, 0, 2]]

def raw3420step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw3421 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw3421step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 2, -1, -1], ![2, -1, 0, -1]]

def raw3421step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 0, -1], ![0, -2, 1, 1], ![-2, 1, 0, 1]]

def raw3421step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw3422 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw3422step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def raw3423 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![1, 0, 1, -2], ![1, 1, -3, 1]]

def raw3423step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, -2, 1], ![-1, 0, -1, 2], ![-1, -1, 3, -1]]

def raw3423step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical107
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3424 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 0, -1, 0]]

def raw3424step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 1, 0], ![0, 2, -1, -1], ![2, -1, -1, 0]]

def raw3424step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, -1, 0], ![0, -2, 1, 1], ![-2, 1, 1, 0]]

def raw3424step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw3425 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 3, -3]]

def raw3426 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -2, 2, -2]]

def raw3427 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![2, -2, 0, 0]]

def raw3428 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def raw3429 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw3429step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 2, -2], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, -3, 4]]

def raw3429step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -3, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw3430 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def raw3430step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 2, -2], ![0, -1, 1, 0], ![-1, 1, -3, 3], ![-1, 0, 0, 1]]

def raw3430step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -3, 3]]

def raw3431 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw3431step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 2, -2], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-2, 2, -2, 2]]

def raw3431step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, 0, -2]]

def raw3432 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 1, -1, -1]]

def raw3433 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def raw3433step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 2, -2], ![0, -1, 0, 1], ![-1, 1, -2, 2], ![-1, 0, 0, 1]]

def raw3433step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw3434 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw3434step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 2, -2], ![0, -1, 0, 1], ![-1, 1, -3, 3], ![-1, 0, 1, 0]]

def raw3434step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -3, 3]]

def raw3435 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![2, -1, 2, -3]]

def raw3435step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 2, -2], ![0, -1, 0, 1], ![-2, 1, -2, 3]]

def raw3435step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -2, -2, 3]]

def raw3436 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, -1, 1, -2]]

def raw3436step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 2, -2], ![0, -1, -1, 2], ![-2, 1, -1, 2]]

def raw3436step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw3437 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw3437step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 2, -2], ![0, -1, -3, 4], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw3437step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw3438 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, 0, -1, 0], ![1, -1, 0, 0]]

def raw3438step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 2, -2], ![0, -1, -3, 4], ![-1, 0, 1, 0], ![-1, 1, 0, 0]]

def raw3438step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw3439 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, 3, -4], ![2, -1, -1, 0]]

def raw3439step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 2, -2], ![0, -1, -3, 4], ![-2, 1, 1, 0]]

def raw3439step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -2, 1, 0]]

def raw3440 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 2, -1, -1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw3441 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 2, -1, -1], ![2, -2, 3, -3]]

def raw3441step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, -2, -1, 3], ![2, 2, -1, -3]]

def raw3441step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![-2, -2, 1, 3]]

def raw3441step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, 0, 1, -3]]

def raw3442 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, -2, 2, -2]]

def raw3442step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 2, -2], ![0, -2, 0, 2], ![-2, 2, -2, 2]]

def raw3442step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, 0, 0, -2]]

def raw3443 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw3443step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 2, -2], ![0, -2, -2, 4], ![-1, 1, 0, 0], ![-1, 1, 0, 0]]

def raw3443step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw3444 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![2, -2, 0, 0]]

def raw3444step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 2, -2], ![0, -2, -2, 4], ![-2, 2, 0, 0]]

def raw3444step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![2, 0, 0, -2]]

def raw3445 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![1, -2, 1, 0], ![1, 2, 1, -4]]

def raw3445step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, -2, 1, 1], ![2, 2, 0, -4]]

def raw3445step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 2, -2], ![0, 2, -1, -1], ![-2, -2, 0, 4]]

def raw3445step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw3446 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![1, -2, 3, -2], ![1, 2, -1, -2]]

def raw3446step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, -2, 3, -1], ![2, 2, -2, -2]]

def raw3446step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 2, -2], ![0, 2, -3, 1], ![-2, -2, 2, 2]]

def raw3446step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 2, -1, -1], ![2, 0, 1, -3]]

def raw3447 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw3447step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 2, -2], ![-1, 1, 0, 0], ![-1, -1, -2, 4]]

def raw3447step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw3448 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![1, -1, 1, -1], ![1, 1, 1, -3]]

def raw3448step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 2, -2], ![-1, 1, -1, 1], ![-1, -1, -1, 3]]

def raw3448step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw3449 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![1, -1, 2, -2], ![1, 1, 0, -2]]

def raw3449step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 2, -2], ![-1, 1, -2, 2], ![-1, -1, 0, 2]]

def raw3449step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw3450 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![1, -1, 3, -3], ![1, 1, -1, -1]]

def raw3450step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 2, -2], ![-1, 1, -3, 3], ![-1, -1, 1, 1]]

def raw3450step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -3, 3]]

def raw3451 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![1, 2, -1, -2], ![1, -2, 3, -2]]

def raw3451step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 2, -2], ![0, -2, -1, 3], ![2, 2, -2, -2]]

def raw3451step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, -2, 2], ![0, 2, 1, -3], ![-2, -2, 2, 2]]

def raw3451step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 2, -1, -1], ![2, 0, 1, -3]]

def raw3452 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![0, 2, 2, -4]]

def raw3452step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![0, -2, -2, 4]]

def raw3452step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw3453 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw3453step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, -1, -2, 4]]

def raw3453step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw3454 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 1, -1], ![1, 1, 1, -3]]

def raw3454step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, -1, 1], ![-1, -1, -1, 3]]

def raw3454step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw3455 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![2, -1, 2, -3]]

def raw3455step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![0, 0, 0, 1, -1], ![0, -1, 0, -1, 2], ![2, 1, 0, 0, -3]]

def raw3455step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, -1, -1, 2], ![2, 1, 0, -3]]

def raw3455step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical108
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3456 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 0, 0, 0], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def raw3456step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![0, 0, 0, -1, 1], ![0, -1, 0, -1, 2], ![2, 1, 0, 1, -4]]

def raw3456step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, -1, -1], ![0, 0, 0, 1, -1], ![0, 1, 0, 1, -2], ![-2, -1, 0, -1, 4]]

def raw3456step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![-2, -1, -1, 4]]

def raw3456step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw3457 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw3457step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, -1, 1], ![-1, -1, 1, 1]]

def raw3457step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw3458 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw3458step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 1, -1], ![0, 0, -2, 2], ![-1, 1, 0, 0], ![-1, -1, 1, 1]]

def raw3458step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw3459 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![0, 1, 3, -4], ![2, -2, 0, 0]]

def raw3460 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def raw3461 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def raw3461step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 1, -1], ![0, -1, 2, -1], ![-1, 1, -3, 3], ![-1, 0, 0, 1]]

def raw3461step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -3, 3]]

def raw3462 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 0, 0, 0], ![2, -1, 2, -3]]

def raw3462step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![0, 0, 1, 0, -1], ![0, -1, -1, 0, 2], ![2, 1, 0, 0, -3]]

def raw3462step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, -1, -1, 2], ![2, 1, 0, -3]]

def raw3462step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def raw3463 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 3, -3]]

def raw3464 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw3464step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 1, -1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-2, 2, -2, 2]]

def raw3464step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw3465 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, -2, 0, 0]]

def raw3465step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 1, -1], ![0, -1, 1, 0], ![0, -1, -2, 3], ![-2, 2, 0, 0]]

def raw3465step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw3466 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![2, -2, -1, 1]]

def raw3467 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 1, 2, -4]]

def raw3467step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-1, 2, 0, -1], ![-1, -1, -2, 4]]

def raw3467step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw3468 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 1, 1, -3]]

def raw3468step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, -1, 1, 0], ![1, 1, -2, 0], ![1, 1, 1, -3]]

def raw3469 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 3, -4]]

def raw3469step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-1, 1, 1, -1], ![-1, 0, -3, 4]]

def raw3469step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw3470 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![0, 1, 2, -3]]

def raw3470step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![0, -1, -2, 3]]

def raw3470step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw3471 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw3471step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-1, 1, -3, 3], ![-1, 0, 1, 0]]

def raw3471step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, -2, 0], ![1, -1, 3, -3]]

def raw3472 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 3, -3], ![1, 0, -2, 1]]

def raw3472step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 1, -3, 3], ![-1, 0, 2, -1]]

def raw3472step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -3, 3]]

def raw3473 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw3473step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 1, -1], ![0, -1, -3, 4], ![-1, 1, 1, -1], ![-1, 0, 1, 0]]

def raw3473step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw3474 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![1, -1, 3, -3], ![1, 1, -2, 0]]

def raw3474step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, -1, 3, -2], ![2, 1, -3, 0]]

def raw3474step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 1, -1], ![0, 1, -3, 2], ![-2, -1, 3, 0]]

def raw3474step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 2, -3]]

def raw3475 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 0, 0], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw3475step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![0, 0, 1, 1, -2], ![0, 0, -2, 0, 2], ![2, 0, 1, -1, -2]]

def raw3475step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, 0, -2], ![0, 0, -1, -1, 2], ![0, 0, 2, 0, -2], ![-2, 0, -1, 1, 2]]

def raw3475step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![0, 2, 0, -2], ![-2, -1, 1, 2]]

def raw3475step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw3476 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 0, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def raw3476step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![0, 0, 1, 1, -2], ![0, 0, -1, -1, 2], ![2, 0, 0, 0, -2]]

def raw3476step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![0, -1, -1, 2], ![2, 0, 0, -2]]

def raw3476step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def raw3477 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 0, 0], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def raw3477step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![2, 0, 1, -3]]

def raw3477step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-2, 0, -1, 3]]

def raw3477step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, -1, 3]]

def raw3477step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw3478 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 0, 0], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw3478step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![2, 0, -1, -1]]

def raw3478step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]

def raw3479 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw3479step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw3479step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def raw3480 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw3480step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, -1, 2, 0]]

def raw3480step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw3481 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 1, -3, 2], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw3482 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def raw3483 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def raw3483step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, -1, 1], ![0, -1, 2, -1], ![0, -1, 0, 1], ![-2, 2, -1, 1]]

def raw3483step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def raw3484 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 0, 1, -1], ![2, -1, -1, 0]]

def raw3484step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw3485 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -2, 1], ![2, -2, 2, -2]]

def raw3485step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def raw3486 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw3486step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw3487 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def raw3487step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, -1, 1], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-2, 2, -1, 1]]

def raw3487step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical109
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3488 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 0, 0]]

def raw3488step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw3489 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 1, -2, 0]]

def raw3489step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, -1, 1], ![0, -1, 0, 1], ![-1, 2, -1, 0], ![-1, -1, 2, 0]]

def raw3489step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw3490 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw3490step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def raw3491 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw3491step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def raw3492 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw3492step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw3493 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -2, 0, 0]]

def raw3493step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw3494 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw3494step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, 1, -2], ![2, -1, -1, 0]]

def raw3494step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw3495 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![1, -1, 2, -2], ![1, 1, -3, 1]]

def raw3495step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, -1, 1], ![-1, 1, -2, 2], ![-1, -1, 3, -1]]

def raw3495step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 2, -2]]

def raw3496 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, 1, -3, 2], ![2, -1, 1, -2]]

def raw3496step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, -2, 2], ![0, -1, 3, -2], ![-2, 1, -1, 2]]

def raw3496step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -2, -1, 2]]

def raw3497 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def raw3498 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, -1, 0, -1]]

def raw3498step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -2, 0, 1]]

def raw3499 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -2, 1], ![2, -2, 1, -1]]

def raw3499step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def raw3500 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 0, 0]]

def raw3500step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw3501 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw3501step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw3502 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw3502step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 1, 0], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw3503 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -1, -2, 1]]

def raw3503step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw3504 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, 2, -3, 1], ![2, -2, 1, -1]]

def raw3504step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, -2, 2], ![0, -2, 3, -1], ![-2, 2, -1, 1]]

def raw3504step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![2, -2, 1, -1]]

def raw3505 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw3505step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw3506 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def raw3506step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw3507 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw3507step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, -2, 2], ![-1, 1, 0, 0], ![-1, -1, 2, 0]]

def raw3507step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw3508 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![1, -1, 1, -1], ![1, 1, -3, 1]]

def raw3508step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, -2, 2], ![-1, 1, -1, 1], ![-1, -1, 3, -1]]

def raw3508step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 1, -1]]

def raw3509 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 3, -3], ![1, -1, 0, 0], ![1, 1, -3, 1]]

def raw3509step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, -3, 3], ![-1, 1, 0, 0], ![-1, -1, 3, -1]]

def raw3509step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw3510 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -3, 2], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw3511 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -3, 2], ![0, 1, 0, -1], ![2, -2, 3, -3]]

def raw3511step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![0, -3, 0, 3], ![2, 2, -1, -3]]

def raw3511step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![0, 3, 0, -3], ![-2, -2, 1, 3]]

def raw3511step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 2, 0, -2], ![1, -2, -2, 3]]

def raw3512 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -3, 2], ![0, 1, 1, -2], ![2, -2, 2, -2]]

def raw3513 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -3, 2], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw3514 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -3, 2], ![0, 1, 3, -4], ![2, -2, 0, 0]]

def raw3514step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![0, -3, 3, 0], ![2, 2, -4, 0]]

def raw3514step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![0, 3, -3, 0], ![-2, -2, 4, 0]]

def raw3514step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 3, -3], ![0, 2, -1, -1], ![2, -2, 0, 0]]

def raw3515 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -3, 2], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def raw3515step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, -3, 1, 2], ![2, 2, 0, -4]]

def raw3515step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 2, -1], ![0, 3, -1, -2], ![-2, -2, 0, 4]]

def raw3515step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 3, -2], ![0, 2, -1, -1], ![2, -1, 0, -1]]

def raw3516 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -3, 2], ![1, -2, 3, -2], ![1, 1, 0, -2]]

def raw3517 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -3, 2], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw3517step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, -3, 0, 3], ![2, 2, 0, -4]]

def raw3517step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -3, 3], ![0, 2, 2, -4], ![1, -2, 0, 1]]

def raw3518 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -3, 2], ![1, -1, 1, -1], ![1, 0, 2, -3]]

def raw3518step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 3, -2], ![-1, 1, -1, 1], ![-1, 0, -2, 3]]

def raw3518step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![0, -1, -2, 3], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw3519 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -3, 2], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def raw3519step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 3, -2], ![-1, 1, -3, 3], ![-1, 0, 0, 1]]

def raw3519step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![0, -1, 0, 1], ![0, 2, 0, -2], ![1, -1, -3, 3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw352 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 1, 2], ![1, 2, -3, 0], ![2, -2, 2, -2]]

def raw352step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]

def raw353 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 1, 2], ![1, 2, -2, -1], ![2, -2, 1, -1]]

def raw353step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

def raw354 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 1, 2], ![2, -2, 1, -1], ![1, 2, -2, -1]]

def raw354step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]

def raw354step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

def raw355 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 2, 1], ![-2, 2, -1, 1], ![5, -2, -1, -2]]

def raw355step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![2, -1, -1], ![1, 1, -2]]

def raw355step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

def raw356 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 2, 1], ![-1, 2, -2, 1], ![4, -2, 0, -2]]

def raw356step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![2, -2, 0], ![1, 1, -2]]

def raw356step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

def raw357 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 2, 1], ![-1, 2, 1, -2], ![4, -2, -3, 1]]

def raw357step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![2, 1, -3], ![1, -2, 1]]

def raw357step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]

def raw358 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 2, 1], ![-1, 3, 0, -2], ![4, -3, -2, 1]]

def raw358step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![2, 0, -2], ![1, -2, 1]]

def raw358step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]

def raw359 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 2, 1], ![0, -2, 0, 2], ![3, 2, -2, -3]]

def raw359step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![2, 0, -2], ![1, 2, -3]]

def raw359step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-2, 0, 2], ![-1, -2, 3]]

def raw359step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![2, 0, -2]]

def raw360 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 2, 1], ![0, -2, 1, 1], ![3, 2, -3, -2]]

def raw360step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![2, 1, -3], ![1, 1, -2]]

def raw360step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 1, -2], ![1, 2, -3]]

def raw361 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 2, 1], ![0, 2, -2, 0], ![3, -2, 0, -1]]

def raw361step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![2, -2, 0], ![1, 0, -1]]

def raw361step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![2, -2, 0]]

def raw362 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 2, 1], ![0, 2, 0, -2], ![3, -2, -2, 1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical110
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3520 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -3, 2], ![1, 0, 3, -4], ![1, -1, 0, 0]]

def raw3520step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 0, -1], ![0, -3, 3, 0], ![2, 2, -4, 0]]

def raw3520step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -3, 3], ![0, 2, 2, -4], ![1, -2, 0, 1]]

def raw3521 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def raw3522 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 1, -2]]

def raw3523 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw3524 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw3525 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -2, 3, -3]]

def raw3525step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![0, -2, -1, 3], ![2, 1, 0, -3]]

def raw3525step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, 1, 0, -2]]

def raw3526 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw3526step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 2, -1], ![0, -1, 0, 1], ![-1, 2, -2, 1], ![-1, 0, 0, 1]]

def raw3526step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw3527 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, -1, 0]]

def raw3528 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw3528step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 2, -1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 1, -2, 2]]

def raw3528step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw3529 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw3529step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![0, -2, 0, 2], ![2, 1, -1, -2]]

def raw3529step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![0, 2, 0, -2], ![-2, -1, 1, 2]]

def raw3529step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw3530 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def raw3531 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -2, 1, -1]]

def raw3531step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 2, -1], ![0, -1, -1, 2], ![-2, 2, -1, 1]]

def raw3531step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def raw3532 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw3532step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 2, -1], ![0, -1, -2, 3], ![-1, 1, 0, 0], ![-1, 1, 0, 0]]

def raw3532step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def raw3533 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![2, -2, 0, 0]]

def raw3533step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![0, -2, 2, 0], ![2, 1, -3, 0]]

def raw3533step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![0, 2, -2, 0], ![-2, -1, 3, 0]]

def raw3533step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -2, 0]]

def raw3534 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def raw3535 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw3536 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, -1, 1]]

def raw3536step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw3537 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![2, -2, -1, 1]]

def raw3537step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![0, -2, 3, -1], ![2, 1, -4, 1]]

def raw3537step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![0, 2, -3, 1], ![-2, -1, 4, -1]]

def raw3537step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, 1, -3], ![2, 0, -2, 0]]

def raw3538 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![1, -2, 0, 1], ![1, 1, 2, -4]]

def raw3538step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 2, -1], ![-1, 2, 0, -1], ![-1, -1, -2, 4]]

def raw3538step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw3539 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![1, -2, 1, 0], ![1, 1, 1, -3]]

def raw3539step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, -2, 1, 1], ![2, 1, 0, -3]]

def raw3539step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 2, -1], ![0, 2, -1, -1], ![-2, -1, 0, 3]]

def raw3539step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw3540 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![1, -2, 2, -1], ![1, 1, 0, -2]]

def raw3540step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 2, -1], ![-1, 2, -2, 1], ![-1, -1, 0, 2]]

def raw3540step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw3541 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![1, -2, 3, -2], ![1, 1, -1, -1]]

def raw3541step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, -2, 3, -1], ![2, 1, -2, -1]]

def raw3541step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 2, -2], ![1, 1, 0, -2]]

def raw3542 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![1, -1, -1, 1], ![1, 0, 3, -4]]

def raw3542step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 2, -1], ![-1, 1, 1, -1], ![-1, 0, -3, 4]]

def raw3542step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw3543 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw3543step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -2, 0, 1]]

def raw3544 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw3544step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 2, -1], ![-1, 1, -1, 1], ![-1, 0, -1, 2]]

def raw3544step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw3545 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def raw3545step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 2, -1], ![-1, 1, -2, 2], ![-1, 0, 0, 1]]

def raw3545step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw3546 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw3546step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, -2, 3, -1], ![2, 1, -3, 0]]

def raw3546step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, -2, 1]]

def raw3547 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![1, 0, -1, 0], ![1, -1, 3, -3]]

def raw3547step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 0, -1], ![0, -2, -1, 3], ![2, 1, 0, -3]]

def raw3547step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, -2, 1]]

def raw3548 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![1, 0, 3, -4], ![1, -1, -1, 1]]

def raw3548step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 2, -1], ![-1, 0, -3, 4], ![-1, 1, 1, -1]]

def raw3548step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw3549 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![1, 1, 0, -2], ![1, -2, 2, -1]]

def raw3549step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 2, -1], ![-1, -1, 0, 2], ![-1, 2, -2, 1]]

def raw3549step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw3550 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![1, 1, 2, -4], ![1, -2, 0, 1]]

def raw3550step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 2, -1], ![-1, -1, -2, 4], ![-1, 2, 0, -1]]

def raw3550step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw3551 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 0, 3, -4]]

def raw3551step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![-1, 0, -3, 4]]

def raw3551step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical111
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3552 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 0, -1, 1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw3552step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![-1, 1, -3, 3], ![-1, 0, 1, 0]]

def raw3552step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, -2, 0], ![1, -1, 3, -3]]

def raw3553 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 0, 3, -3], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw3553step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 1, 0], ![0, 0, -3, 3], ![-1, 1, 1, -1], ![-1, 0, 1, 0]]

def raw3553step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, -1, 1]]

def raw3554 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -2, 1], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def raw3554step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def raw3555 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -2, 1], ![1, -2, 2, -1], ![1, 0, 1, -2]]

def raw3555step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 1, -2]]

def raw3556 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -2, 1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw3556step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw3557 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw3557step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw3558 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -2, 1], ![2, -2, 3, -3]]

def raw3558step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![0, -1, -2, 3], ![2, 0, 1, -3]]

def raw3558step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, 1, 0, -2]]

def raw3559 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, -1, 2], ![1, 0, 3, -4]]

def raw3560 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 2, -3]]

def raw3560step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-1, 2, 0, -1], ![-1, 0, -2, 3]]

def raw3560step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw3561 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 0, 1, -2]]

def raw3561step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-1, 2, -1, 0], ![-1, 0, -1, 2]]

def raw3561step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw3562 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw3562step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw3563 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 3, -2], ![1, 0, -1, 0]]

def raw3563step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw3564 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, -1, 3, -3]]

def raw3565 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw3565step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw3566 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, -1, -1, 1]]

def raw3566step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, -1, 3, -3]]

def raw3567 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def raw3567step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![0, -1, -1, 2], ![2, 0, 0, -2]]

def raw3567step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def raw3568 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def raw3568step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw3569 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, -2, 1]]

def raw3570 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 2, -2]]

def raw3570step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 1, 1, -1], ![-1, 1, -2, 2]]

def raw3570step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw3571 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw3571step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 1, -1, 1]]

def raw3571step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw3572 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def raw3572step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 1, 0], ![0, -1, -1, 2], ![-1, 2, -1, 0], ![-1, 0, 1, 0]]

def raw3572step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -1, -1, 0]]

def raw3573 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 0, -2, 1]]

def raw3574 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw3574step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 1, 0], ![0, -1, -1, 2], ![-1, 1, 0, 0], ![-1, 1, 0, 0]]

def raw3574step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw3575 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def raw3575step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 1, 0], ![0, -1, -2, 3], ![-1, 2, 0, -1], ![-1, 0, 1, 0]]

def raw3575step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw3576 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw3576step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 1, 0], ![0, -1, -2, 3], ![-1, 1, 1, -1], ![-1, 1, 0, 0]]

def raw3576step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw3577 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, -2, -1, 1]]

def raw3577step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![0, -1, 2, -1], ![2, 0, -3, 1]]

def raw3577step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 2, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw3578 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, -1, 2], ![1, 0, -1, 0]]

def raw3579 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, 0, 1], ![1, 0, -2, 1]]

def raw3580 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -2, 2], ![1, -1, 0, 0]]

def raw3581 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, -1, 1]]

def raw3582 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![2, -2, -2, 2]]

def raw3582step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![0, -1, 3, -2], ![2, 0, -4, 2]]

def raw3582step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 2, 0], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw3583 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![1, -2, -1, 2], ![1, 1, 2, -4]]

def raw3583step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, -1, -1, 2], ![2, 0, 2, -4]]

def raw3583step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical112
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3584 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 1, 1, -3]]

def raw3584step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 1, 0], ![-1, 2, 0, -1], ![-1, -1, -1, 3]]

def raw3584step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw3585 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 1, -1, -1]]

def raw3585step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, -1, 2, -1], ![2, 0, -1, -1]]

def raw3585step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def raw3586 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![1, -1, -2, 2], ![1, 0, 3, -4]]

def raw3586step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, -1, -2, 3], ![2, 0, 2, -4]]

def raw3586step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw3587 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 2, -3]]

def raw3587step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, -1, -1, 2], ![2, 0, 1, -3]]

def raw3587step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw3588 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw3588step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, -1, 1, 0], ![2, 0, -1, -1]]

def raw3588step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw3589 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![1, 0, -2, 1], ![1, -1, 3, -3]]

def raw3589step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 0, -1], ![0, -1, -2, 3], ![2, 0, 1, -3]]

def raw3589step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def raw3590 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 1, -1, -1]]

def raw3590step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 0, 1, -1], ![2, -1, 0, -1]]

def raw3590step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw3591 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 1, -2, 0]]

def raw3591step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 0, 2, -2], ![2, -1, -1, 0]]

def raw3591step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 2, -1], ![0, 0, -2, 2], ![-2, 1, 1, 0]]

def raw3591step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw3592 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 1, -3, 1]]

def raw3592step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 0, 3, -3], ![2, -1, -2, 1]]

def raw3592step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 2, -1], ![0, 0, -3, 3], ![-2, 1, 2, -1]]

def raw3592step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 2, -1, -1], ![1, -2, -1, 2]]

def raw3593 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def raw3593step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw3594 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw3594step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 0, 1, -1], ![2, -1, -1, 0]]

def raw3594step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw3595 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -2, 1]]

def raw3595step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 0, 1], ![-1, 1, -2, 2], ![-1, 0, 2, -1]]

def raw3595step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw3596 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![0, 1, -2, 1], ![2, -2, 1, -1]]

def raw3596step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![0, -1, 2, -1], ![-2, 2, -1, 1]]

def raw3596step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def raw3597 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 1, -3, 1]]

def raw3598 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw3598step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![-1, 1, 1, -1], ![-1, 0, 0, 1]]

def raw3598step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, -1, -1]]

def raw3599 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 0, -2, 1]]

def raw3599step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![-1, 1, -1, 1], ![-1, 0, 2, -1]]

def raw3599step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw3600 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 2, -3], ![1, -2, 1, 0], ![1, 1, -3, 1]]

def raw3600step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 2, 1, -3], ![2, -3, 0, 1]]

def raw3600step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 2, -1], ![0, -2, -1, 3], ![-2, 3, 0, -1]]

def raw3600step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 2, -1, -1], ![2, -1, -1, 0]]

def raw3601 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw3601step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -2, 3], ![-1, 1, 1, -1], ![-1, 0, 1, 0]]

def raw3601step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, -1, -1]]

def raw3602 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw3602step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -2, 3], ![-1, 1, 0, 0], ![-1, 0, 2, -1]]

def raw3602step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw3603 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 0, -3, 2]]

def raw3603step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -2, 3], ![-1, 1, -1, 1], ![-1, 0, 3, -2]]

def raw3603step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 3, -2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw3604 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 3, -4], ![1, -2, -1, 2], ![1, 1, -2, 0]]

def raw3604step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 3, -1, -2], ![2, -4, 2, 0]]

def raw3604step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 2, -1], ![0, -3, 1, 2], ![-2, 4, -2, 0]]

def raw3604step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 2, 1, -3], ![2, -1, -1, 0]]

def raw3605 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 3, -4], ![1, -2, 0, 1], ![1, 1, -3, 1]]

def raw3605step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 3, 0, -3], ![2, -4, 1, 1]]

def raw3605step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 2, -1], ![0, -3, 0, 3], ![-2, 4, -1, -1]]

def raw3605step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 3, -3], ![0, 2, -1, -1], ![2, -1, -1, 0]]

def raw3606 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 3, -4], ![1, -1, -2, 2], ![1, 0, -1, 0]]

def raw3606step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -3, 4], ![-1, 1, 2, -2], ![-1, 0, 1, 0]]

def raw3606step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 2, 0, -2], ![1, -1, 2, -2]]

def raw3607 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, 0, -2, 1]]

def raw3607step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -3, 4], ![-1, 1, 1, -1], ![-1, 0, 2, -1]]

def raw3607step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw3608 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -3, 2]]

def raw3608step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -3, 4], ![-1, 1, 0, 0], ![-1, 0, 3, -2]]

def raw3608step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 3, -2], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw3609 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 3, -4], ![1, 0, -3, 2], ![1, -1, 0, 0]]

def raw3609step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -3, 4], ![-1, 0, 3, -2], ![-1, 1, 0, 0]]

def raw3609step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 3, -2], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw3610 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 3, -4], ![1, 0, -2, 1], ![1, -1, -1, 1]]

def raw3610step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -3, 4], ![-1, 0, 2, -1], ![-1, 1, 1, -1]]

def raw3610step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw3611 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, -3, 1], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def raw3611step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![0, -3, 0, 3], ![2, 1, 1, -4]]

def raw3611step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -2, 2, 0], ![0, 3, 0, -3], ![-2, -1, -1, 4]]

def raw3611step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 3, -3], ![0, 2, -2, 0], ![2, -1, 0, -1]]

def raw3612 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, -3, 1], ![1, -2, 1, 0], ![1, 0, 2, -3]]

def raw3612step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -2, 3, -1], ![-1, 2, -1, 0], ![-1, 0, -2, 3]]

def raw3612step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 2, -2, 0], ![2, -1, 0, -1]]

def raw3613 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, -3, 1], ![1, -2, 2, -1], ![1, 0, 1, -2]]

def raw3613step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -2, 3, -1], ![-1, 2, -2, 1], ![-1, 0, -1, 2]]

def raw3613step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![2, -1, 1, -2]]

def raw3614 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, -3, 1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw3614step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![0, -3, 3, 0], ![2, 1, -2, -1]]

def raw3614step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -2, 2, 0], ![0, 3, -3, 0], ![-2, -1, 2, 1]]

def raw3614step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, 0, -1], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, -2, -1, 2]]

def raw3615 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, -3, 1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw3615step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![0, -3, 0, 3], ![2, 1, 0, -3]]

def raw3615step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -3, 3], ![0, 2, 1, -3], ![1, -2, 0, 1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical113
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3616 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, -3, 1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def raw3616step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -2, 3, -1], ![-1, 1, -1, 1], ![-1, 1, -2, 2]]

def raw3616step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def raw3617 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, -2, 0], ![1, -2, -1, 2], ![1, 0, 3, -4]]

def raw3617step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![0, -2, -1, 3], ![2, 0, 2, -4]]

def raw3617step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -2, 2, 0], ![0, 2, 1, -3], ![-2, 0, -2, 4]]

def raw3617step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 2, 1, -3], ![2, 0, -1, -1]]

def raw3618 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, -2, 0], ![1, -2, 3, -2], ![1, 0, -1, 0]]

def raw3618step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![0, -2, 3, -1], ![2, 0, -2, 0]]

def raw3618step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw3619 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, -2, 0], ![1, -1, -1, 1], ![1, -1, 3, -3]]

def raw3619step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![0, -2, -1, 3], ![2, 0, 1, -3]]

def raw3619step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![2, -1, 0, -1]]

def raw3620 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw3620step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![0, -2, 0, 2], ![2, 0, 0, -2]]

def raw3620step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -2, 0, 1]]

def raw3621 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def raw3621step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def raw3622 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, -1, -1], ![1, -2, 3, -2], ![1, 0, -2, 1]]

def raw3622step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![0, -1, 3, -2], ![2, -1, -2, 1]]

def raw3622step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, 0, -2], ![1, -1, 2, -2], ![1, 0, -2, 1]]

def raw3623 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw3623step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![0, -1, 0, 1], ![2, -1, 0, -1]]

def raw3623step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -2, 1, 1], ![0, 1, 0, -1], ![-2, 1, 0, 1]]

def raw3623step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw3624 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, 0, -2], ![1, -2, 2, -1], ![1, 0, -2, 1]]

def raw3624step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -2, 0, 2], ![-1, 2, -2, 1], ![-1, 0, 2, -1]]

def raw3624step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, -1, 0, -1]]

def raw3625 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, 2, -4], ![1, -2, -1, 2], ![1, 0, -1, 0]]

def raw3625step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![0, 2, -1, -1], ![2, -4, 2, 0]]

def raw3625step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -2, 1, 0]]

def raw3626 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, 2, -4], ![1, -2, 0, 1], ![1, 0, -2, 1]]

def raw3626step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -2, -2, 4], ![-1, 2, 0, -1], ![-1, 0, 2, -1]]

def raw3626step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw3627 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, 2, -4], ![1, -1, -2, 2], ![1, -1, 0, 0]]

def raw3627step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![0, 2, -2, 0], ![2, -4, 2, 0]]

def raw3627step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -2, 1, 0]]

def raw3628 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, 2, -4], ![1, -1, -1, 1], ![1, -1, -1, 1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]

def raw301 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]

def raw301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

def raw302 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![3, -2, -1]]

def raw302step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]

def raw303 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

def raw304 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]

def raw305 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

def raw306 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def raw306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]

def raw306step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def raw307 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

def raw307step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]

def raw307step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

def raw308 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]

def raw308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 0, 1], ![-1, 1, 0], ![-1, 0, 1]]

def raw308step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def raw309 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

def raw309step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]

def raw309step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -2, 1], ![1, 3, -4]]

def raw310 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

def raw311 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![2, -2, 0], ![1, 1, -2]]

def raw311step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

def raw312 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![3, -1, -2]]

def raw312step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![4, -2, -2]]

def raw312step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, -1, -1]]

def raw313 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]

def raw314 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]

def raw315 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw316 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]

def raw316step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw317 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]

def raw318 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]

def raw319 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![2, -2, 0], ![1, 0, -1]]

def raw319step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical93
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3001 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, -2, 1, -1]]

def raw3001step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![-2, -1, 2, 1], ![4, 0, -3, -1]]

def raw3001step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![2, 1, -2, -1], ![-4, 0, 3, 1]]

def raw3001step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 0, -2, 2], ![0, 3, 1, -4], ![1, -2, -1, 2]]

def raw3002 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw3003 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, -1, 0], ![0, 1, 3, -4], ![2, -2, 0, 0]]

def raw3003step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![-2, -1, 3, 0], ![4, 0, -4, 0]]

def raw3003step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 4, -4], ![0, 2, -2, 0], ![1, -2, 0, 1]]

def raw3004 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def raw3004step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![-2, -1, 1, 2], ![4, 0, 0, -4]]

def raw3004step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 0, 4, -4], ![0, 1, -2, 1], ![1, -2, 0, 1]]

def raw3005 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw3005step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![-2, -1, 0, 3], ![4, 0, 0, -4]]

def raw3005step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 4, -4], ![0, 1, -2, 1], ![1, -1, 0, 0]]

def raw3006 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 2, -3]]

def raw3006step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, -1, 1, 0], ![-1, 1, -1, 1], ![-1, 0, -2, 3]]

def raw3006step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -2, 3], ![0, 2, 2, -4], ![1, -1, -1, 1]]

def raw3007 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw3007step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, -1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical94
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3008 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw3008step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![-2, 0, 0, 2], ![4, -1, -1, -2]]

def raw3008step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 0, 2, -2], ![1, 1, -2, 0]]

def raw3009 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, -2, 1, -1]]

def raw3009step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![-2, 0, 1, 1], ![4, -1, -2, -1]]

def raw3009step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw3010 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw3010step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 1, -3]]

def raw3011 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 0, -1], ![0, 1, 2, -3], ![2, -2, 0, 0]]

def raw3011step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![-2, 0, 2, 0], ![4, -1, -3, 0]]

def raw3011step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -2, 1, 0]]

def raw3012 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 1, 0, -2]]

def raw3012step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![-2, 0, 2, 0], ![4, -1, -1, -2]]

def raw3012step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw3013 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 1, -1, -1]]

def raw3013step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![-2, 0, 3, -1], ![4, -1, -2, -1]]

def raw3013step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 3, -2], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw3014 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw3014step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![-2, 0, 0, 2], ![4, -1, 0, -3]]

def raw3014step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw3015 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw3015step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![-2, 0, 1, 1], ![4, -1, -1, -2]]

def raw3015step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw3016 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def raw3016step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![-2, 0, 2, 0], ![4, -1, -2, -1]]

def raw3016step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw3017 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, -1, 3, -3]]

def raw3017step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 0, -1], ![-2, 0, -1, 3], ![4, -1, 0, -3]]

def raw3017step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 3, -2], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw3018 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, -1, 2, -2]]

def raw3018step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 0, -1], ![-2, 0, 0, 2], ![4, -1, -1, -2]]

def raw3018step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw3019 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 1, -2], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def raw3019step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![-2, 1, 0, 1], ![4, -2, -1, -1]]

def raw3019step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw3020 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw3020step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2], ![1, 0, 1, -2]]

def raw3021 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![2, -2, 0, 0]]

def raw3021step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![-2, 1, 1, 0], ![4, -2, -2, 0]]

def raw3021step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def raw3022 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 1, 0, -2]]

def raw3022step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 1, -2], ![1, 0, 1, -2], ![1, 1, -2, 0]]

def raw3023 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 1, -1, -1]]

def raw3023step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![-2, 1, 2, -1], ![4, -2, -1, -1]]

def raw3023step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 1, -2], ![1, -1, 2, -2], ![1, 1, -2, 0]]

def raw3024 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw3024step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, -1, -1, 2], ![-1, 1, 0, 0], ![-1, 0, -1, 2]]

def raw3024step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw3025 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 1, -2], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw3025step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, -1, -1, 2], ![-1, 1, -2, 2], ![-1, 0, 1, 0]]

def raw3025step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 2, 2, -4], ![1, -1, -2, 2]]

def raw3026 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, -1, 2, -2]]

def raw3026step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, -1, -1, 2], ![-1, 0, 1, 0], ![-1, 1, -2, 2]]

def raw3026step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 2, 2, -4], ![1, -1, -2, 2]]

def raw3027 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 2, -3], ![1, -2, 1, 0], ![1, 1, -1, -1]]

def raw3028 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw3028step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![-2, 2, 0, 0], ![4, -3, 0, -1]]

def raw3028step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 1, 0], ![2, -2, 0, 0], ![-4, 3, 0, 1]]

def raw3028step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, 0, 3, -4]]

def raw3029 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw3029step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![-2, 2, 1, -1], ![4, -3, -1, 0]]

def raw3029step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 1, 0], ![2, -2, -1, 1], ![-4, 3, 1, 0]]

def raw3029step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -2, 2]]

def raw3030 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 2, -3], ![1, 0, -1, 0], ![1, -1, 1, -1]]

def raw3030step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 0, -1], ![-2, 2, -1, 1], ![4, -3, 0, -1]]

def raw3030step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 0, 1], ![2, -2, 1, -1], ![-4, 3, 0, 1]]

def raw3030step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -2, 2]]

def raw3031 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw3031step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![-2, 3, 0, -1], ![4, -4, 0, 0]]

def raw3031step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 1, 0], ![2, -3, 0, 1], ![-4, 4, 0, 0]]

def raw3031step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 4, -4], ![0, 1, -3, 2], ![1, 0, -1, 0]]

def raw3032 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 3, -4], ![1, 0, -1, 0], ![1, -1, 0, 0]]

def raw3032step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 0, -1], ![-2, 3, -1, 0], ![4, -4, 0, 0]]

def raw3032step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 0, 1], ![2, -3, 1, 0], ![-4, 4, 0, 0]]

def raw3032step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 4, -4], ![0, 1, -3, 2], ![1, 0, -1, 0]]

def raw3033 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -2, 1, 0], ![1, 0, 2, -3]]

def raw3034 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -2, 2, -1], ![1, 0, 1, -2]]

def raw3034step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![-2, -1, 2, 1], ![4, -1, -1, -2]]

def raw3034step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, -2, 0], ![1, -1, 2, -2], ![1, 0, 1, -2]]

def raw3035 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw3035step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![-2, -1, 3, 0], ![4, -1, -2, -1]]

def raw3035step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 3, -2], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def raw3036 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw3036step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![-2, -1, 0, 3], ![4, -1, 0, -3]]

def raw3036step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -2, 1, 1], ![2, 1, 0, -3], ![-4, 1, 0, 3]]

def raw3036step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -3, 2], ![0, 1, 3, -4], ![1, -2, 1, 0]]

def raw3037 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def raw3038 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -1, 2, -2], ![1, -1, 1, -1]]

def raw3038step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def raw3039 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, 0, -2], ![1, -2, 1, 0], ![1, 0, 1, -2]]

def raw3039step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 1, -2, 0], ![1, 1, 0, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical95
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3040 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, 0, -2], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw3040step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![-2, 0, 2, 0], ![4, -2, -1, -1]]

def raw3040step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def raw3041 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, 0, -2], ![1, -2, 3, -2], ![1, 0, -1, 0]]

def raw3041step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![-2, 0, 3, -1], ![4, -2, -2, 0]]

def raw3041step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 4, -2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw3042 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw3042step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![-2, 0, 0, 2], ![4, -2, 0, -2]]

def raw3042step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -2, 1, 1], ![2, 0, 0, -2], ![-4, 2, 0, 2]]

def raw3042step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -2, 1, 0]]

def raw3043 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def raw3043step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def raw3044 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, 0, -2], ![1, -1, 2, -2], ![1, -1, 0, 0]]

def raw3044step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![-2, 0, 2, 0], ![4, -2, -2, 0]]

def raw3044step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -2, 1, 1], ![2, 0, -2, 0], ![-4, 2, 2, 0]]

def raw3044step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -2, 1, 0]]

def raw3045 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, 1, -3], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def raw3045step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![-2, 1, 2, -1], ![4, -3, -1, 0]]

def raw3045step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -2, 2, 0], ![2, -1, -2, 1], ![-4, 3, 1, 0]]

def raw3045step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 3, -4], ![0, 2, -2, 0], ![1, -2, -1, 2]]

def raw3046 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, 1, -3], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw3046step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![-2, 1, 0, 1], ![4, -3, 0, -1]]

def raw3046step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -2, 1, 1], ![2, -1, 0, -1], ![-4, 3, 0, 1]]

def raw3046step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, 1, -2, 0]]

def raw3047 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, 2, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw3047step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![-2, 2, 0, 0], ![4, -4, 0, 0]]

def raw3047step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 4, -4], ![1, 1, -2, 0]]

def raw3048 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![1, -2, 1, 0], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw3048step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def raw3049 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![1, -2, 2, -1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw3049step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 1, 1], ![-2, 2, 1, -1], ![4, -1, -2, -1]]

def raw3049step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 1, -2], ![1, -1, 2, -2], ![1, 1, -2, 0]]

def raw3050 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![1, -2, 2, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw3050step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 2, 0], ![-2, 2, -1, 1], ![4, -1, -1, -2]]

def raw3050step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, -2, 0], ![1, -1, 2, -2], ![1, 0, 1, -2]]

def raw3051 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![1, -2, 3, -2], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw3051step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 2, 0], ![-2, 3, -1, 0], ![4, -2, -1, -1]]

def raw3051step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 3, -2], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def raw3052 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![1, -1, 1, -1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw3052step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def raw3053 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![1, -1, 2, -2], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def raw3053step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def raw3054 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![1, -1, 3, -3], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def raw3054step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 2, -1], ![-2, 3, -1, 0], ![4, -3, -1, 0]]

def raw3054step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 1, -2, 1], ![2, -3, 1, 0], ![-4, 3, 1, 0]]

def raw3054step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -3, 2], ![0, 1, 3, -4], ![1, -2, 1, 0]]

def raw3055 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw3056 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -2, 1, 1], ![1, 0, -1, 0], ![1, 2, 1, -4]]

def raw3056step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 0, 2], ![-1, 1, -1, 1], ![3, 1, 0, -4]]

def raw3056step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 2, 0, -2], ![1, -1, 1, -1], ![-3, -1, 0, 4]]

def raw3056step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw3057 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -2, 1, 1], ![1, 1, -2, 0], ![1, 1, 2, -4]]

def raw3058 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -2, 1, 1], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def raw3058step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 1, 1, -3]]

def raw3059 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -2, 2, 0], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def raw3059step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![2, 0, 0, -2]]

def raw3060 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -2, 2, 0], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw3060step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![-1, 2, 0, -1], ![3, 0, -2, -1]]

def raw3060step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -2, 0]]

def raw3061 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -2, 2, 0], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def raw3061step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![-1, 2, -1, 0], ![3, 0, -1, -2]]

def raw3061step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def raw3062 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, -1, 2], ![0, 0, 2, -2], ![2, 1, 0, -3]]

def raw3062step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, 1, -2], ![0, 0, -2, 2], ![-2, -1, 0, 3]]

def raw3062step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, 0, 1, -2]]

def raw3063 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, -1, 2], ![0, 1, 2, -3], ![2, 0, 0, -2]]

def raw3063step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, 1, -2], ![0, -1, -2, 3], ![-2, 0, 0, 2]]

def raw3063step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, 1, 0, -2]]

def raw3064 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 0, 1], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw3064step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![-1, 0, -1, 2], ![3, 1, 0, -4]]

def raw3064step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![-3, -1, 0, 4]]

def raw3064step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw3065 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 1, 0], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw3065step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, -1, 0], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![-1, -1, -2, 4]]

def raw3065step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw3066 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def raw3067 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 2, -3]]

def raw3067step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 3, -1], ![0, 1, -3, 2], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw3068 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw3068step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw3069 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw3070 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw3070step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 3, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw3071 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw3071step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, -2, 1], ![0, -1, 1, 0], ![-1, 0, 0, 1], ![-1, 0, 0, 1]]

def raw3071step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 2, 1, -3], ![1, 0, -2, 1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical96
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3072 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw3072step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, -2, 1], ![0, -1, 1, 0], ![-2, 0, 0, 2]]

def raw3072step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, 0, 2], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw3073 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw3073step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, -2, 1], ![0, -1, 0, 1], ![-1, 0, 1, 0], ![-1, 0, 0, 1]]

def raw3073step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw3074 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw3074step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![-1, 2, 0, -1], ![3, -1, -1, -1]]

def raw3074step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw3075 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

def raw3075step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, -2, 1], ![0, -1, -1, 2], ![-2, 0, 2, 0]]

def raw3075step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 2, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw3076 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw3077 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw3078 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![2, -1, 1, -2]]

def raw3079 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, -1, 0, -1]]

def raw3079step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw3080 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![1, -1, 1, -1], ![1, 2, -2, -1]]

def raw3080step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![-1, 2, 1, -2], ![3, -1, -1, -1]]

def raw3080step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 1, -2], ![1, -2, -1, 2], ![-3, 1, 1, 1]]

def raw3080step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 2, -1], ![1, 1, -3, 1], ![1, 1, 0, -2]]

def raw3081 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw3081step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, -2, 1], ![-1, 0, 1, 0], ![-1, -1, 0, 2]]

def raw3081step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw3082 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw3082step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![-1, 2, 0, -1], ![3, -1, -1, -1]]

def raw3082step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw3083 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![1, 0, 1, -2], ![1, 1, -2, 0]]

def raw3083step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, -2, 1], ![-1, 0, -1, 2], ![-1, -1, 2, 0]]

def raw3083step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -3, 1], ![1, 0, 1, -2]]

def raw3084 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![1, 1, -2, 0], ![1, 0, 1, -2]]

def raw3084step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, -2, 1], ![-1, -1, 2, 0], ![-1, 0, -1, 2]]

def raw3084step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -3, 1], ![1, 0, 1, -2]]

def raw3085 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![1, 2, -2, -1], ![1, -1, 1, -1]]

def raw3085step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 2, -1], ![-1, 2, -2, 1], ![3, -1, -1, -1]]

def raw3085step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, -2, 1], ![1, -2, 2, -1], ![-3, 1, 1, 1]]

def raw3085step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 2, -1], ![1, 1, -3, 1], ![1, 1, 0, -2]]

def raw3086 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw3087 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw3087step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, -3, 2], ![0, -1, 2, -1], ![-1, 0, 0, 1], ![-1, 0, 0, 1]]

def raw3087step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 2, 1, -3], ![1, 0, -3, 2]]

def raw3088 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, -2, 1], ![2, 0, 0, -2]]

def raw3088step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, -3, 2], ![0, -1, 2, -1], ![-2, 0, 0, 2]]

def raw3088step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 2, 1, -3], ![1, 0, -3, 2]]

def raw3089 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw3090 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw3090step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 3, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw3091 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def raw3092 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw3093 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def raw3093step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, -3, 2], ![0, -1, 0, 1], ![-1, 0, 2, -1], ![-1, 0, 0, 1]]

def raw3093step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, 0, -3, 2]]

def raw3094 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw3094step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 3, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw3095 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw3096 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 2, -2, 0], ![2, -1, 0, -1]]

def raw3097 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw3098 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw3099 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 2, -1, -1], ![2, -1, -1, 0]]

def raw3100 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![1, -1, -1, 1], ![1, 2, -1, -2]]

def raw3100step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, -3, 2], ![-1, 1, 1, -1], ![-1, -2, 1, 2]]

def raw3100step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, 1, -3], ![1, -1, 1, -1], ![1, 0, -3, 2]]

def raw3101 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![1, -1, 0, 0], ![1, 2, -2, -1]]

def raw3101step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![-1, 3, 0, -2], ![3, -2, 0, -1]]

def raw3101step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -2, 3, -1], ![0, 3, -1, -2], ![1, 0, -2, 1]]

def raw3102 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![1, 0, -2, 1], ![1, 1, 0, -2]]

def raw3102step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, -3, 2], ![-1, 0, 2, -1], ![-1, -1, 0, 2]]

def raw3102step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, 0, -3, 2]]

def raw3103 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw3103step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![-1, 3, -1, -1], ![3, -2, 0, -1]]

def raw3103step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, 1, -2, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical97
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3104 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw3104step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, -3, 2], ![-1, 0, 0, 1], ![-1, -1, 2, 0]]

def raw3104step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, -3, 1], ![1, 0, 2, -3]]

def raw3105 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![1, 1, -2, 0], ![1, 0, 0, -1]]

def raw3105step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, -3, 2], ![-1, -1, 2, 0], ![-1, 0, 0, 1]]

def raw3105step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, -3, 1], ![1, 0, 2, -3]]

def raw3106 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![1, 1, -1, -1], ![1, 0, -1, 0]]

def raw3106step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 1, 0], ![-1, 3, -1, -1], ![3, -2, -1, 0]]

def raw3106step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def raw3107 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![1, 2, -1, -2], ![1, -1, -1, 1]]

def raw3107step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, -3, 2], ![-1, -2, 1, 2], ![-1, 1, 1, -1]]

def raw3107step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, 1, -3], ![1, -1, 1, -1], ![1, 0, -3, 2]]

def raw3108 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw3108step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, -1, -1, 3]]

def raw3108step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 0, 1], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw3109 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def raw3109step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, -1, 1], ![-1, -1, 0, 2]]

def raw3109step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw3110 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw3110step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, 1, -1], ![0, 0, -2, 2], ![-1, 1, 0, 0], ![-1, -1, 0, 2]]

def raw3110step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, 0, 0]]

def raw3111 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![2, -2, 0, 0]]

def raw3112 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def raw3113 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def raw3113step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-1, 1, -3, 3], ![-1, 0, 0, 1]]

def raw3113step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -3, 3]]

def raw3114 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw3114step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 1, -3, 3], ![-1, 0, 1, 0]]

def raw3114step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -3, 3]]

def raw3115 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 0, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw3115step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![0, 0, 1, 1, -2], ![-1, 0, -1, 0, 2], ![3, 0, 0, -1, -2]]

def raw3115step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, 0, -2], ![0, 0, -1, -1, 2], ![1, 0, 1, 0, -2], ![-3, 0, 0, 1, 2]]

def raw3115step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![1, 1, 0, -2], ![-3, 0, 1, 2]]

def raw3115step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -3, 2], ![1, 0, 1, -2]]

def raw3116 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 0, 0], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def raw3116step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![-1, 0, -1, 2], ![3, 0, 1, -4]]

def raw3116step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 1, -1], ![1, 0, 1, -2], ![-3, 0, -1, 4]]

def raw3116step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![1, 1, -2], ![-3, -1, 4]]

def raw3116step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2]]

def raw3117 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def raw3117step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -1, 1, 0], ![-2, 1, 0, 1]]

def raw3117step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -2, 0, 1]]

def raw3118 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -2, 0, 0]]

def raw3118step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw3119 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw3119step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, -1, 1, 1]]

def raw3119step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, 0, 0]]

def raw3120 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw3121 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -2, 1, -1]]

def raw3122 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def raw3123 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def raw3123step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def raw3124 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -2, 0, 0]]

def raw3124step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

def raw3125 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw3125step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -2, 3], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw3126 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw3126step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, -1, 1], ![0, -1, 1, 0], ![-1, 1, -1, 1], ![-1, 0, 0, 1]]

def raw3126step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw3127 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw3127step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, -1, 1], ![0, -1, 1, 0], ![-1, 1, -2, 2], ![-1, 0, 1, 0]]

def raw3127step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, -1, 2, -2]]

def raw3128 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def raw3128step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def raw3129 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -2, 1]]

def raw3129step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, -1, 1], ![0, -1, 0, 1], ![-1, 1, -2, 2], ![-1, 0, 2, -1]]

def raw3129step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, -2, 2]]

def raw3130 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw3131 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def raw3132 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw3132step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw3133 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -2, 1, -1]]

def raw3133step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![-1, 1, -1, 1], ![3, -1, -1, -1]]

def raw3133step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 1, -1]]

def raw3134 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw3134step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![-1, 1, 1, -1], ![3, -1, -1, -1]]

def raw3134step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw3135 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -2, 1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical98
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3136 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, -1, 1, -2]]

def raw3136step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, -2, 2], ![0, -1, 2, -1], ![-2, 1, -1, 2]]

def raw3136step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -2, -1, 2]]

def raw3137 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def raw3138 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 0, 0]]

def raw3138step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, 0, -2, 0]]

def raw3139 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 1, -1, -1]]

def raw3140 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw3140step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -2, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw3141 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def raw3141step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, -2, 2], ![0, -1, 1, 0], ![-2, 1, 0, 1]]

def raw3141step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -2, 0, 1]]

def raw3142 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![0, 1, -1, 0], ![2, -2, 0, 0]]

def raw3142step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, 0, -2, 0]]

def raw3143 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 1, -2, 0]]

def raw3144 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw3144step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw3145 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw3145step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, -2, 2], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw3145step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw3146 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw3146step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![-1, 2, 0, -1], ![3, -2, -1, 0]]

def raw3146step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw3147 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -2, 1, 0], ![1, 0, 0, -1]]

def raw3148 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw3149 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, -1, 0, 0]]

def raw3149step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw3150 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![2, -2, 1, -1]]

def raw3151 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def raw3152 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw3152step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw3153 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, -2, 0, 0]]

def raw3153step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -2, 0]]

def raw3154 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![1, -2, 1, 0], ![1, 2, -2, -1]]

def raw3154step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![-1, 2, 1, -2], ![3, -2, 0, -1]]

def raw3154step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 2, -2], ![1, -2, -1, 2], ![-3, 2, 0, 1]]

def raw3154step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -3, 1]]

def raw3155 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def raw3155step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, -2, 2], ![-1, 1, 1, -1], ![-1, -1, 0, 2]]

def raw3155step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -1, 1, -1]]

def raw3156 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw3156step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![-1, 2, 0, -1], ![3, -2, 0, -1]]

def raw3156step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 1, -1], ![1, -2, 0, 1], ![-3, 2, 0, 1]]

def raw3156step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw3157 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw3157step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, -2, 2], ![-1, 1, -1, 1], ![-1, -1, 2, 0]]

def raw3157step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -3, 1], ![1, -1, 1, -1]]

def raw3158 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![1, 1, -2, 0], ![1, -1, 1, -1]]

def raw3158step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, -2, 2], ![-1, -1, 2, 0], ![-1, 1, -1, 1]]

def raw3158step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -3, 1], ![1, -1, 1, -1]]

def raw3159 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![1, 2, -2, -1], ![1, -2, 1, 0]]

def raw3159step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 2, -2], ![-1, 2, -2, 1], ![3, -2, -1, 0]]

def raw3159step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, -2, 2], ![1, -2, 2, -1], ![-3, 2, 1, 0]]

def raw3159step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -3, 1]]

def raw3160 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw3160step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, -3, 3], ![0, -1, 2, -1], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw3160step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 0, -3, 3], ![0, 2, 1, -3], ![1, -1, 0, 0]]

def raw3161 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 3, -3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 0, 0]]

def raw3162 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 3, -3], ![0, 1, -1, 0], ![2, -1, -1, 0]]

def raw3162step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![-1, 3, -1, -1], ![3, -3, 0, 0]]

def raw3162step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw3163 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw3164 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 3, -3], ![0, 2, -2, 0], ![2, -2, 0, 0]]

def raw3165 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 3, -3], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def raw3165step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, -3, 3], ![-1, 1, 1, -1], ![-1, -1, 1, 1]]

def raw3165step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -3, 3], ![0, 2, 1, -3], ![1, -1, 1, -1]]

def raw3166 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 3, -3], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw3166step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, -3, 3], ![-1, 1, 0, 0], ![-1, -1, 2, 0]]

def raw3166step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 2, -3, 1], ![1, -1, 0, 0]]

def raw3167 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 3, -3], ![1, 1, -2, 0], ![1, -1, 0, 0]]

def raw3167step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, -3, 3], ![-1, -1, 2, 0], ![-1, 1, 0, 0]]

def raw3167step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 2, -3, 1], ![1, -1, 0, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical99
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3168 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw3169 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw3170 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def raw3171 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -2, 3, -3]]

def raw3171step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![-1, -2, 0, 3], ![3, 1, -1, -3]]

def raw3171step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![1, 2, 0, -3], ![-3, -1, 1, 3]]

def raw3171step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, 1, -3], ![1, -1, -3, 3]]

def raw3172 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw3173 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -2, 2, -2]]

def raw3174 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw3175 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, -1, 0, 0]]

def raw3175step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw3176 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![2, -2, 1, -1]]

def raw3177 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw3178 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 3, -4], ![2, -2, 0, 0]]

def raw3179 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def raw3180 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![1, -2, 3, -2], ![1, 1, 0, -2]]

def raw3181 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw3181step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, -1, 2, -1], ![-1, 1, 0, 0], ![-1, 0, -3, 4]]

def raw3181step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -3, 4], ![0, 2, 1, -3], ![1, -1, 0, 0]]

def raw3182 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 0, 2, -3]]

def raw3182step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, -1, 2, -1], ![-1, 1, -1, 1], ![-1, 0, -2, 3]]

def raw3182step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -2, 3], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw3183 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def raw3183step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, -1, 2, -1], ![-1, 1, -3, 3], ![-1, 0, 0, 1]]

def raw3183step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 2, 1, -3], ![1, -1, -3, 3]]

def raw3184 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, -1, 3, -3]]

def raw3184step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, -1, 2, -1], ![-1, 0, 0, 1], ![-1, 1, -3, 3]]

def raw3184step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 2, 1, -3], ![1, -1, -3, 3]]

def raw3185 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![1, 0, 1, -2], ![1, -1, 2, -2]]

def raw3185step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, -1, 2, -1], ![-1, 0, -1, 2], ![-1, 1, -2, 2]]

def raw3185step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 1, -3], ![1, -1, -2, 2]]

def raw3186 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![1, 0, 2, -3], ![1, -1, 1, -1]]

def raw3186step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, -1, 2, -1], ![-1, 0, -2, 3], ![-1, 1, -1, 1]]

def raw3186step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -2, 3], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw3187 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![1, 0, 3, -4], ![1, -1, 0, 0]]

def raw3187step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, -1, 2, -1], ![-1, 0, -3, 4], ![-1, 1, 0, 0]]

def raw3187step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -3, 4], ![0, 2, 1, -3], ![1, -1, 0, 0]]

def raw3188 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def raw3189 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 0, 2, -3]]

def raw3190 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 1, -2]]

def raw3191 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw3192 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw3193 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def raw3194 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 3, -3]]

def raw3194step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![-1, -1, -1, 3], ![3, 0, 0, -3]]

def raw3194step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, 1, 0, -2]]

def raw3195 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 0, 1, -2]]

def raw3195step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def raw3196 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw3196step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -2, -1]]

def raw3197 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, -1, 0]]

def raw3198 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 3, -3]]

def raw3199 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw3199step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, -1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end


