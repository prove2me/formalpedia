-- Prove2me | Definitions.Def_OAIQ106D137
-- name    : OAIQ106D137
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T13:28:21.662564+00:00
-- url     : https://prove2.me/theorems/0f3d64d4-efe7-48f8-b3da-d3fb6cd6ae73
-- title:
--   Definitions bundle OAIQ106D137 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 142 declarations of OpenAI's Lean: 142 definitions. The definitions and types are `OAI.MUB6.Certificate.PairData.target1`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow0`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow1`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow10`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow100`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow101`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow102`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow103`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow104`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow105`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow106`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow107`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow108`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow11`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow12`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow128`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow129`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow13`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow130`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow131`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow133`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow134`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow135`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow138`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow139`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow14`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow140`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow144`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow145`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow146`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow147`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow150`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow151`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow152`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow153`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow156`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow157`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow158`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow16`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow161` and 102 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_PairData_Data`, `MutuallyUnbiased_PairSemantics_Boundary0`, `MutuallyUnbiased_PairSemantics_Boundary1`, `MutuallyUnbiased_PairSemantics_Boundary10`, `MutuallyUnbiased_PairSemantics_Boundary11`, `MutuallyUnbiased_PairSemantics_Boundary12`, `MutuallyUnbiased_PairSemantics_Boundary2`, `MutuallyUnbiased_PairSemantics_Boundary5`, `MutuallyUnbiased_PairSemantics_Boundary6`, `MutuallyUnbiased_PairSemantics_Boundary7`, `MutuallyUnbiased_PairSemantics_Boundary8`, `MutuallyUnbiased_PairSemantics_Boundary9`, `MutuallyUnbiased_PairSemantics_Values0`, `MutuallyUnbiased_PairSemantics_Values1`.
--
--   **Imports.** It imports the bundles `OAIQ106D000` and `OAIQ106D002` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.MUB6.Certificate.PairSemantics.boundarySound165`, `OAI.MUB6.Certificate.PairSemantics.boundarySound243`, `OAI.MUB6.Certificate.PairSemantics.boundarySound248`, `OAI.MUB6.Certificate.PairSemantics.boundarySound249`, `OAI.MUB6.Certificate.PairSemantics.boundarySound250`, `OAI.MUB6.Certificate.PairSemantics.boundarySound252`, `OAI.MUB6.Certificate.PairSemantics.boundarySound261`, `OAI.MUB6.Certificate.PairSemantics.boundarySound264`, `OAI.MUB6.Certificate.PairSemantics.boundarySound305` and `OAI.MUB6.Certificate.PairSemantics.boundarySound347`; the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1161`, `OAI.MUB6.Certificate.MixedSemantics.sound1162`, `OAI.MUB6.Certificate.MixedSemantics.sound1163`, `OAI.MUB6.Certificate.MixedSemantics.sound1164`, `OAI.MUB6.Certificate.MixedSemantics.sound1165`, `OAI.MUB6.Certificate.MixedSemantics.sound1168`, `OAI.MUB6.Certificate.MixedSemantics.sound1170`, `OAI.MUB6.Certificate.MixedSemantics.sound1173`, `OAI.MUB6.Certificate.MixedSemantics.sound1339`, `OAI.MUB6.Certificate.MixedSemantics.sound1340`, `OAI.MUB6.Certificate.MixedSemantics.sound1341`, `OAI.MUB6.Certificate.MixedSemantics.sound1342`, `OAI.MUB6.Certificate.MixedSemantics.sound1346`, `OAI.MUB6.Certificate.MixedSemantics.sound644`, `OAI.MUB6.Certificate.MixedSemantics.sound645`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound135`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound136`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound137`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound138`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound141`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound142`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound143`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound144`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound145`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound146`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound147`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1013`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1170`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1484`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1517`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2166`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2168`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2169`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2176`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2177`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2178`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2179`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2180`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2181`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2182`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2183`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2184`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2185`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2187`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2188`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2189`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2190`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2191`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2192`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2194`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2197`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2198`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2199`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2203`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2229`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2259`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2260`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2261`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2263`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2264`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2266`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2267`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2268`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2269`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2270`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2271`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2272`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2273`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2274`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2275`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2276`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2277`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2278`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2279`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2280`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2282`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2283`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2284`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2286`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2287`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2288`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2289`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2291`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2292`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2293`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2294`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2296`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2297`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2298`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2299`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2300`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2301`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2302`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2303`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2304`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2306`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2307`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2308`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2309`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2313`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2315`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2316`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2317`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2318`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2319`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2320`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2321`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2322`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2323`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2324`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2325`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2326`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2327`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2329`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2330`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2331`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2332`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2333`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2334`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2335`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2336`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2337`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2338`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2340`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2341`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2343`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2344`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2345`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2346`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2347`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2348`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2350`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2351`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2352`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2353`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2354`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2355`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2356`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2357`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2360`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2361`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2362`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2363`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2364`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2365`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2366`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2371`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2394`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2398`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2409`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval117`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval12`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval18`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval21`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval243`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval37`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval39`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval41`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval46`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval56`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval6`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval69`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval73`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval74`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval77`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval79`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval8`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval83`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval86`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval91`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval99`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval21`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval271`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval44`, `OAI.MUB6.Certificate.PairSemantics.boundarySound165`, `OAI.MUB6.Certificate.PairSemantics.boundarySound243`, `OAI.MUB6.Certificate.PairSemantics.boundarySound248`, `OAI.MUB6.Certificate.PairSemantics.boundarySound249`, `OAI.MUB6.Certificate.PairSemantics.boundarySound250`, `OAI.MUB6.Certificate.PairSemantics.boundarySound252`, `OAI.MUB6.Certificate.PairSemantics.boundarySound261`, `OAI.MUB6.Certificate.PairSemantics.boundarySound264`, `OAI.MUB6.Certificate.PairSemantics.boundarySound305`, `OAI.MUB6.Certificate.PairSemantics.boundarySound347`, `OAI.MUB6.Certificate.PairSemantics.sound1392`, `OAI.MUB6.Certificate.PairSemantics.sound1399`, `OAI.MUB6.Certificate.PairSemantics.sound1414`, `OAI.MUB6.Certificate.PairSemantics.sound1424`, `OAI.MUB6.Certificate.PairSemantics.sound1437`, `OAI.MUB6.Certificate.PairSemantics.sound1533`, `OAI.MUB6.Certificate.PairSemantics.sound1535`, `OAI.MUB6.Certificate.PairSemantics.sound1540`, `OAI.MUB6.Certificate.PairSemantics.sound1879`, `OAI.MUB6.Certificate.PairSemantics.sound2123`, `OAI.MUB6.Certificate.PairSemantics.sound2375`, `OAI.MUB6.Certificate.PairSemantics.sound2477`, `OAI.MUB6.Certificate.PairSemantics.sound2900`, `OAI.MUB6.Certificate.PairSemantics.sound3019`, `OAI.MUB6.Certificate.PairSemantics.sound3047`, `OAI.MUB6.Certificate.PairSemantics.sound3050`, `OAI.MUB6.Certificate.PairSemantics.sound3054`, `OAI.MUB6.Certificate.PairSemantics.sound3071`, `OAI.MUB6.Certificate.PairSemantics.sound3105`, `OAI.MUB6.Certificate.PairSemantics.sound3116`, `OAI.MUB6.Certificate.PairSemantics.sound3344`, `OAI.MUB6.Certificate.PairSemantics.sound3401`, `OAI.MUB6.Certificate.PairSemantics.sound3428`, `OAI.MUB6.Certificate.PairSemantics.sound381`, `OAI.MUB6.Certificate.PairSourceBridge.allRowsSound`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound0`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound1`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound10`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound100`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound101`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound102`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound103`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound104`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound105`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound106`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound107`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound108`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound111`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound112`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound113`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound114`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound115`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound116`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound117`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound118`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound119`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound12`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound120`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound121`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound124`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound125`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound126`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound127`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound128`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound129`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound13`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound130`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound131`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound132`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound133`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound134`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound135`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound136`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound137`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound139`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound14`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound140`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound141`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound142`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound146`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound148`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound15`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound150`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound151`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound153`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound154`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound155`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound156`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound157`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound158`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound159`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound16`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound160`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound161`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound162`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound163`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound164`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound165`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound166`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound167`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound168`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound169`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound17`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound170`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound171`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound173`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound174`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound175`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound176`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound177`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound178`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound179`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound18`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound180`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound181`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound182`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound183`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound184`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound185`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound186`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound187`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound188`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound19`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound190`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound191`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound192`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound193`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound194`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound195`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound196`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound2`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound20`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound201`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound21`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound22`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound224`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound228`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound23`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound239`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound24`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound25`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound26`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound27`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound28`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound3`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound30`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound31`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound32`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound34`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound38`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound44`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound64`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound91`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound92`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound93`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound94`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound95`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound96`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound97`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound98`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound99` and `OAI.MUB6.Certificate.PairTargetSemantics.certificate_zero1`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ106D000
import Definitions.Def_OAIQ106D002

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairData_Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Untrusted literal certificate data. The subsequent Check modules
check the linear identities. Hadamard interpretation is separate. -/
namespace MUB6.Certificate.PairData

def target1 : Integer.Sparse (Fin 271) := [(0, -8727264), (5, 4536000), (6, 272160), (62, -8709120), (66, -3265920), (2, -9253440), (7, -8709120), (34, -5806080), (8, -39191040), (113, 52254720), (3, 17418240), (13, -5806080), (17, -19595520), (20, -78382080), (23, -13063680), (24, 39191040), (12, -4354560), (134, -78382080), (137, -78382080), (138, -470292480), (4, 26127360), (27, -13608000), (1, -35199360), (146, 78382080), (28, -78382080), (29, 137168640), (30, -26127360), (150, -352719360)]

end MUB6.Certificate.PairData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value1 : Sparse (Fin 909) := [(58, (1 / 1))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value102 : Sparse (Fin 909) := [(7, (-1 / 3)), (35, (-1 / 3)), (67, (-1 / 3))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryRow0 : Integer.Sparse (Fin 909) := [(0, 9), (1, 170), (2, -25), (3, -80), (4, -160), (12, -40)]

def boundaryRow1 : Integer.Sparse (Fin 909) := [(0, -1), (1, -4), (5, -8), (6, 1), (27, 12)]

def boundaryRow2 : Integer.Sparse (Fin 909) := [(0, -1), (1, 18), (2, -8), (3, -64), (4, -32), (5, 3), (7, -16), (8, -8), (12, -24), (23, 12), (24, 24)]

def boundaryRow3 : Integer.Sparse (Fin 909) := [(0, -9), (1, 205), (2, -110), (3, -160), (4, -160), (5, 30), (7, -40), (8, -200), (24, 120), (30, 240)]

def boundaryRow10 : Integer.Sparse (Fin 909) := [(0, 11), (1, -890), (2, 45), (3, 1120), (4, 1080), (12, 440), (18, 360), (22, 720)]

def boundaryRow11 : Integer.Sparse (Fin 909) := [(0, 12), (1, -121), (2, 33), (3, 320), (4, 224), (12, 192), (15, 144), (17, 72), (23, -72), (24, -48), (25, -144), (27, 18), (30, -24), (31, -144)]

def boundaryRow12 : Integer.Sparse (Fin 909) := [(0, 3), (1, -65), (2, 11), (3, 80), (4, 80), (12, 20), (17, 36), (19, 36), (20, 36), (22, 36), (24, -60), (27, 9), (30, -12), (31, -48)]

def boundaryRow13 : Integer.Sparse (Fin 909) := [(0, 93), (1, -1715), (2, 210), (3, 2880), (4, 2400), (12, 1520), (21, 720), (22, 720), (31, -480)]

def boundaryRow14 : Integer.Sparse (Fin 909) := [(0, 16), (1, -315), (2, 65), (3, 960), (4, 600), (12, 360), (18, 360), (25, -240), (31, -240)]

def boundaryRow16 : Integer.Sparse (Fin 909) := [(0, -69), (1, -470), (2, 110), (3, 160), (4, 160), (12, 160), (17, 180), (23, -60), (27, 45), (28, 360), (30, -300)]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryRow17 : Integer.Sparse (Fin 909) := [(0, -11), (1, 220), (2, -250), (3, -1200), (4, -240), (5, 260), (6, -15), (7, -480), (8, -480), (12, -480), (13, -320), (35, -160), (51, 720), (52, -240)]

def boundaryRow18 : Integer.Sparse (Fin 909) := [(0, -32), (1, 615), (2, -60), (3, -2160), (4, -960), (5, 60), (6, -15), (12, -240), (13, -160), (26, -960), (35, -240), (55, 720)]

def boundaryRow19 : Integer.Sparse (Fin 909) := [(0, -7), (1, 125), (2, -70), (3, -480), (4, -160), (5, 160), (6, -20), (7, -80), (8, -160), (26, -160), (35, -80), (52, -160)]

def boundaryRow20 : Integer.Sparse (Fin 909) := [(0, -2), (1, 55), (2, -11), (3, -304), (4, -64), (5, 52), (6, -8), (7, -16), (8, -32), (12, -64), (13, -208), (26, -64), (35, -80), (52, -64), (54, 48), (56, 96)]

def boundaryRow21 : Integer.Sparse (Fin 909) := [(0, -11), (1, 215), (2, -95), (3, -720), (4, -240), (5, 160), (6, -15), (7, -240), (8, -240), (26, -240), (35, -80)]

def boundaryRow22 : Integer.Sparse (Fin 909) := [(0, 1), (1, 5), (3, -400), (5, 10), (7, -160), (12, -240), (13, -240), (23, 360), (25, 360), (35, -80), (54, 240)]

def boundaryRow23 : Integer.Sparse (Fin 909) := [(0, -7), (1, 180), (2, -15), (3, -720), (12, -360), (13, -960), (32, -80)]

def boundaryRow24 : Integer.Sparse (Fin 909) := [(0, -7), (1, 145), (2, -30), (3, -680), (4, -240), (12, -120), (13, -160), (26, -280), (33, 120), (34, -80)]

def boundaryRow25 : Integer.Sparse (Fin 909) := [(0, -19), (1, 300), (2, -75), (3, -640), (4, -480), (12, -200), (25, 240), (26, -80), (31, 480), (33, 240)]

def boundaryRow26 : Integer.Sparse (Fin 909) := [(0, 157), (1, -2040), (2, 585), (3, 5280), (4, 3520), (12, 2240), (13, 560), (25, -1200), (31, -2880), (33, -960), (50, 720)]

def boundaryRow27 : Integer.Sparse (Fin 909) := [(0, 59), (1, -575), (2, 320), (3, 1040), (4, 480), (5, -80), (7, 80), (8, 320), (12, 480), (23, -240), (25, -240), (27, 180), (30, -480), (31, -480), (33, -480), (45, 1440), (51, -480), (54, -240)]

def boundaryRow28 : Integer.Sparse (Fin 909) := [(0, 29), (1, -334), (2, 99), (3, 896), (4, 512), (12, 352), (13, 32), (25, -96), (26, 112), (31, -336), (33, -192), (43, 144), (45, 288)]

def boundaryRow29 : Integer.Sparse (Fin 909) := [(0, 128), (1, -1575), (2, 405), (3, 4480), (4, 2960), (12, 1360), (25, -960), (26, 960), (31, -1680), (43, 720), (44, 720), (45, 720), (46, 720)]

def boundaryRow30 : Integer.Sparse (Fin 909) := [(0, 58), (1, -605), (2, 235), (3, 1280), (4, 920), (5, -30), (7, 40), (8, 80), (12, 560), (23, -240), (24, -720), (25, -600), (27, 300), (30, -480), (31, -1200), (33, -480), (48, 360), (49, 720), (51, -360), (55, -240)]

def boundaryRow31 : Integer.Sparse (Fin 909) := [(0, 141), (1, -1765), (2, 580), (3, 3600), (4, 2560), (5, -60), (7, 80), (8, 160), (12, 1440), (13, 320), (23, -480), (24, -1440), (27, 600), (30, -960), (31, -1920), (47, 720), (49, 1440), (51, -720), (55, -480)]

def boundaryRow32 : Integer.Sparse (Fin 909) := [(0, 109), (1, -1300), (2, 565), (3, 2880), (4, 1760), (5, -120), (7, 160), (8, 320), (12, 800), (23, -480), (24, -1440), (26, 400), (27, 600), (30, -960), (31, -1200), (43, 720), (55, -480)]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryRow269 : Integer.Sparse (Fin 909) := [(0, 6), (1, -65), (2, -125), (3, -1360), (4, -160), (5, 420), (6, -70), (7, -320), (8, -160), (9, 60), (13, -960), (26, -640), (34, -400), (35, -1200), (52, -1040), (56, 480), (60, -400), (64, 240), (67, -160), (69, -240), (70, -160), (71, -160), (125, 480), (126, 240), (128, -320), (197, 240), (257, -160), (260, 240), (262, 480), (268, 480), (495, -240)]

def boundaryRow270 : Integer.Sparse (Fin 909) := [(0, 9), (1, -45), (2, -85), (3, -800), (4, -80), (5, 460), (6, -85), (7, -640), (8, -480), (9, 100), (26, -400), (35, -560), (51, 240), (52, -400), (69, -320), (70, -80), (71, -480), (123, 480), (124, 480), (126, 240), (197, 240), (236, 480), (259, 240), (495, -80)]

def boundaryRow271 : Integer.Sparse (Fin 909) := [(0, 1), (1, -3), (2, -12), (3, -112), (5, 16), (6, -2), (12, -32), (13, -144), (26, -16), (33, 48), (34, -32), (35, -32), (52, -96), (55, 96), (59, 96), (60, -16), (61, 48), (64, 96), (69, -32), (71, -16), (125, 96), (128, -32), (197, 48), (256, 48), (260, 48), (263, -96), (495, -16)]

def boundaryRow273 : Integer.Sparse (Fin 909) := [(0, 7), (1, 95), (2, -25), (3, -1920), (4, -560), (5, 180), (6, -15), (7, -720), (8, -160), (12, -160), (13, -80), (23, 240), (25, 480), (26, -1120), (33, 240), (34, -240), (35, -960), (51, 240), (52, -240), (54, 240), (55, 240), (64, 480), (67, -320), (69, -80), (70, -80), (81, 480), (123, 480), (124, 240), (125, 240), (256, 240), (257, -80), (259, 240), (266, 240), (487, -480), (495, -80)]

def boundaryRow275 : Integer.Sparse (Fin 909) := [(0, 8), (1, 35), (2, -340), (3, -3120), (4, -800), (5, 680), (6, -55), (7, -1920), (8, -800), (10, 240), (11, -160), (12, -80), (13, -160), (26, -1760), (33, 480), (34, -320), (35, -2640), (52, -800), (55, 240), (67, -800), (81, 1920), (82, -80), (228, 480), (273, 480), (276, -160), (306, 480), (307, 480)]

def boundaryRow276 : Integer.Sparse (Fin 909) := [(0, 1), (1, -12), (2, -27), (3, -224), (4, -16), (5, 52), (6, -8), (7, -16), (8, -16), (11, -16), (12, -88), (13, -304), (26, -32), (33, 96), (34, -32), (35, -144), (52, -176), (54, 48), (59, 240), (60, -64), (82, -32), (128, -96), (199, 24), (201, 48), (228, 48), (271, 48), (276, -16), (490, 96), (721, 96)]

def boundaryRow277 : Integer.Sparse (Fin 909) := [(0, 6), (1, 65), (2, -180), (3, -2880), (4, -720), (5, 440), (6, -35), (7, -1680), (8, -480), (11, -240), (13, -240), (26, -1920), (34, -480), (35, -2800), (52, -720), (60, -160), (67, -960), (81, 1440), (228, 720), (273, 720), (276, -240)]

def boundaryRow278 : Integer.Sparse (Fin 909) := [(0, 1), (1, 6), (2, -39), (3, -576), (4, -160), (5, 108), (6, -14), (7, -192), (8, -64), (11, -128), (12, -32), (13, -112), (26, -352), (33, 96), (34, -64), (35, -544), (52, -256), (54, 48), (56, 96), (59, 96), (60, -64), (67, -64), (81, 192), (128, -16), (228, 480), (271, 48), (275, 96), (276, -48), (490, 192), (721, 96)]

def boundaryRow285 : Integer.Sparse (Fin 909) := [(0, 7), (1, 105), (2, -120), (3, -1920), (4, -240), (12, -960), (13, -2000), (26, -240), (32, -80), (33, 1440), (34, -480), (51, 720), (52, -240), (60, -240), (61, 720), (127, 720), (128, -240), (489, 1440)]

def boundaryRow286 : Integer.Sparse (Fin 909) := [(0, 14), (1, -65), (2, -80), (3, -1200), (5, 340), (6, -65), (12, -160), (13, -1280), (26, -240), (33, 240), (34, -160), (35, -560), (52, -1120), (60, -160), (82, -80), (123, 480), (128, -320), (237, 480), (306, 240), (489, 480)]

def boundaryRow287 : Integer.Sparse (Fin 909) := [(0, 7), (1, -10), (2, -25), (3, -480), (5, 200), (6, -30), (11, -40), (12, -40), (13, -480), (26, -200), (33, 120), (35, -440), (52, -440), (55, 120), (63, 240), (82, -40), (123, 240), (128, -40), (237, 240), (306, 120), (721, 120)]

def boundaryRow297 : Integer.Sparse (Fin 909) := [(0, -5), (1, 131), (2, 228), (3, 224), (5, -556), (6, 42), (7, 656), (8, 928), (9, -120), (35, 224), (52, 192), (69, 848), (70, 272), (71, 1664), (256, -576), (277, -144), (279, 144), (280, 576), (281, 576), (726, -144), (818, -288)]

def boundaryRow298 : Integer.Sparse (Fin 909) := [(0, -23), (1, -195), (2, 220), (3, 3200), (5, -420), (6, 30), (7, 1520), (8, 640), (9, -40), (10, -240), (12, 560), (13, 160), (23, -1920), (24, -960), (26, 320), (27, 420), (35, 800), (51, -1440), (54, -1680), (55, -1440), (69, 400), (70, 240), (71, 160), (77, 2880), (79, 720), (228, -960), (277, -240), (290, 1440), (291, 2160)]

def boundaryRow300 : Integer.Sparse (Fin 909) := [(0, -19), (1, -115), (2, 430), (3, 3200), (5, -740), (6, 20), (7, 2800), (8, 1280), (9, -40), (10, -720), (12, 720), (13, 960), (23, -240), (24, -480), (27, 180), (35, 2240), (51, -1920), (52, 640), (54, -960), (59, -1920), (69, 720), (70, 400), (71, 320), (72, 720), (73, 1440), (74, 1440), (199, -720), (256, -960), (277, -240), (279, 720), (280, 1440), (726, -720)]

def boundaryRow301 : Integer.Sparse (Fin 909) := [(0, -3), (1, 41), (2, 126), (3, 176), (4, 48), (5, -208), (6, 16), (7, 304), (8, 352), (9, -32), (10, -96), (12, 32), (13, 16), (24, -96), (26, 32), (27, 24), (30, -48), (35, 80), (51, -144), (52, 48), (54, -48), (55, -48), (56, -192), (59, -96), (69, 144), (70, 16), (71, 480), (74, 288), (75, 144), (78, 288), (201, -96), (228, -96), (256, -96), (277, -48), (280, 144), (282, 144), (288, 288), (289, 288), (726, -48), (818, -48)]

def boundaryRow302 : Integer.Sparse (Fin 909) := [(0, -5), (1, 101), (2, 210), (3, 336), (4, 16), (5, -360), (6, 26), (7, 352), (8, 576), (9, -24), (35, 144), (51, -144), (52, 288), (69, 208), (70, 80), (71, 320), (81, -192), (86, 288), (256, -96), (281, 288), (322, 144), (325, 288), (327, 288), (818, -144)]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryRow303 : Integer.Sparse (Fin 909) := [(0, -13), (1, -30), (2, 155), (3, 2000), (5, -580), (6, 70), (7, 1840), (8, 960), (9, -160), (10, -480), (12, 160), (13, 80), (23, -720), (24, -240), (26, 160), (27, 120), (35, 1520), (51, -480), (52, 160), (54, -1200), (55, -240), (59, -480), (69, 1600), (70, 960), (71, 640), (72, 1440), (73, 720), (77, 1440), (199, -480), (228, -480), (256, -480), (277, -240), (279, 720), (282, 720), (286, 1440), (287, 1440), (726, -480)]

def boundaryRow304 : Integer.Sparse (Fin 909) := [(0, -11), (1, 10), (2, 605), (3, 3120), (4, 400), (5, -900), (6, 70), (7, 2400), (8, 720), (9, -80), (12, 160), (13, 320), (24, -240), (26, 480), (35, 2320), (51, -480), (52, 1920), (69, 640), (70, 320), (71, 640), (73, 1440), (81, -960), (84, 720), (85, 1440), (201, -480), (228, -720), (256, -1440), (277, -720), (279, 720), (280, 1440), (322, 2160), (327, 1440), (726, -240), (818, -720)]

def boundaryRow305 : Integer.Sparse (Fin 909) := [(0, -28), (1, 415), (2, 840), (3, 1760), (4, 400), (5, -1660), (6, 105), (7, 1920), (8, 2880), (9, -120), (13, 320), (26, 160), (35, 800), (51, -1680), (52, 640), (56, -1440), (59, -1200), (69, 1040), (70, 400), (71, 1600), (76, 2880), (77, 720), (201, -960), (228, -240), (256, -480), (281, 1440), (286, 1440), (287, 720), (288, 1440), (726, -240), (818, -480)]

def boundaryRow306 : Integer.Sparse (Fin 909) := [(0, -27), (1, 555), (2, 1085), (3, 1600), (4, 80), (5, -2280), (6, 225), (7, 2320), (8, 3040), (9, -160), (26, 160), (35, 880), (51, -720), (52, 1280), (69, 720), (70, 80), (71, 2400), (85, 1440), (228, -480), (256, -480), (277, -240), (280, 720), (322, 720), (325, 1440), (327, 1440), (818, -480)]

def boundaryRow307 : Integer.Sparse (Fin 909) := [(0, -9), (1, 20), (2, 95), (3, 800), (5, -180), (6, 20), (7, 480), (9, -40), (12, 160), (13, 160), (23, -240), (31, -480), (33, -480), (35, 320), (52, 320), (69, 160), (70, 160), (81, -960), (95, 1440), (124, -240), (196, -240), (256, -480), (322, 1440), (379, 1440), (818, -480)]

def boundaryRow308 : Integer.Sparse (Fin 909) := [(0, -4), (1, 15), (2, 20), (3, 2400), (4, 640), (5, -380), (6, 45), (7, 2560), (8, 480), (9, -40), (12, 320), (13, 160), (23, -480), (24, -480), (25, -1200), (26, 1120), (35, 1440), (52, 320), (54, -1200), (69, 240), (70, 80), (71, 160), (97, 2880), (113, 720), (124, -480), (197, -480), (228, -960), (256, -480), (277, -240), (291, 720), (378, 1440)]

def boundaryRow311 : Integer.Sparse (Fin 909) := [(0, -3), (1, -76), (2, 172), (3, 1232), (4, 224), (5, -136), (6, 11), (7, 352), (8, 224), (9, -8), (12, 256), (13, 160), (23, -144), (24, -96), (26, 256), (33, -768), (35, 208), (52, 224), (54, -240), (55, -48), (69, 48), (70, 16), (71, 32), (81, -576), (100, 576), (104, 288), (125, -96), (126, -96), (228, -192), (256, -96), (277, -48), (291, 144), (379, 288)]

def boundaryRow312 : Integer.Sparse (Fin 909) := [(0, -19), (1, -5), (2, 440), (3, 3680), (4, 160), (5, -1260), (6, 220), (7, 1760), (8, 320), (9, -160), (12, 400), (13, 2080), (23, -240), (26, 480), (35, 2720), (51, -480), (52, 3520), (54, -1200), (69, 560), (70, 400), (71, 160), (103, 2880), (125, -960), (126, -480), (228, -960), (256, -480), (277, -240), (291, 720), (322, 1440), (378, 1440), (818, -480)]

def boundaryRow313 : Integer.Sparse (Fin 909) := [(0, -33), (1, 100), (2, 985), (3, 5680), (5, -1360), (6, 170), (7, 1680), (8, 960), (9, -120), (12, 1840), (13, 4720), (23, -720), (35, 2800), (51, -480), (52, 3520), (54, -240), (59, -1200), (69, 560), (70, 400), (71, 160), (98, 1440), (102, 2880), (125, -1440), (126, -480), (201, -960), (256, -480), (287, 720), (327, 1440), (352, 1440), (726, -240), (818, -480)]

def boundaryRow314 : Integer.Sparse (Fin 909) := [(0, -19), (1, 50), (2, 170), (3, 2400), (5, -360), (6, 35), (7, 1760), (8, 800), (9, -40), (10, -480), (12, 960), (13, 880), (23, -240), (26, 320), (27, 360), (35, 720), (51, -1200), (52, 160), (55, -1200), (59, -480), (69, 240), (71, 240), (105, 1440), (124, -480), (228, -480), (236, -480), (256, -480), (277, -240), (290, 720), (352, 1440)]

def boundaryRow315 : Integer.Sparse (Fin 909) := [(0, -3), (1, 14), (2, 7), (3, 368), (5, -36), (6, 16), (7, 448), (8, 96), (9, -40), (10, -48), (12, 80), (13, 64), (23, -144), (26, 96), (27, 36), (35, 208), (51, -48), (54, -48), (55, -240), (69, 160), (70, 64), (71, 96), (87, 288), (124, -240), (196, -96), (197, -48), (228, -288), (236, -96), (277, -48), (282, 144), (290, 144), (726, -48)]

def boundaryRow332 : Integer.Sparse (Fin 909) := [(0, 1), (1, -320), (2, 200), (3, 2000), (4, 560), (5, -220), (6, 15), (7, 960), (9, -20), (12, 720), (13, 160), (23, -2160), (24, -2400), (25, -720), (27, 600), (35, 320), (48, 2160), (51, -720), (55, -1440), (63, -480), (68, 240), (69, 240), (70, 160), (124, -1440), (126, -1440), (196, -480), (197, -1440), (308, -240), (643, 1440), (751, 2160)]

def boundaryRow337 : Integer.Sparse (Fin 909) := [(0, 54), (1, -660), (2, 935), (3, 4320), (4, 2000), (5, -940), (6, 45), (7, 1920), (8, 1920), (12, 240), (13, 160), (26, 1200), (31, -3600), (35, 800), (43, 2160), (51, -3600), (56, -1440), (77, 2160), (97, 4320), (107, 4320), (228, -240), (238, -2400), (737, 1440)]

def boundaryRow338 : Integer.Sparse (Fin 909) := [(0, -3), (1, -190), (2, 385), (3, 2880), (4, 720), (5, -560), (6, 30), (7, 1440), (8, 960), (10, -1080), (11, 240), (12, 520), (13, 720), (26, 960), (35, 1120), (38, 1080), (40, 2160), (52, 240), (55, -1080), (59, -720), (72, 1080), (75, 2160), (199, -120), (228, -720), (321, 2160), (505, 720), (508, 4320), (727, -480)]

def boundaryRow339 : Integer.Sparse (Fin 909) := [(0, 9), (1, -315), (2, 170), (3, 2880), (4, 960), (5, -680), (6, 120), (7, 960), (9, -20), (11, 480), (12, 240), (26, 960), (33, -2880), (35, 2080), (36, 2160), (40, 4320), (52, 1440), (54, -720), (55, -2160), (69, 240), (70, 160), (228, -1440), (306, -2160), (312, 4320), (498, 2160), (721, -1440), (723, -240), (728, -960), (760, 4320), (783, 1440), (794, 8640)]

def boundaryRow340 : Integer.Sparse (Fin 909) := [(0, -29), (1, -490), (2, 485), (3, 3920), (5, -340), (7, 1840), (8, 160), (10, -240), (12, 1200), (13, 320), (23, -3360), (24, -2400), (25, -480), (26, 160), (27, 1020), (33, -480), (35, 160), (51, -2880), (54, -1200), (55, -2400), (65, -480), (79, 720), (94, 720), (122, 2880), (127, -240), (299, 1440), (300, 1440)]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryRow343 : Integer.Sparse (Fin 909) := [(0, -12), (1, -405), (2, 300), (3, 3440), (4, 640), (5, -260), (6, 5), (7, 1200), (8, 80), (9, -20), (10, -480), (12, 1040), (13, 320), (23, -3600), (24, -3120), (26, 160), (27, 780), (35, 320), (47, 1440), (51, -480), (52, 160), (55, -3360), (68, 180), (69, 240), (70, 160), (79, 1440), (113, 720), (124, -240), (125, -2160), (126, -1440), (197, -480), (291, 720), (308, -240), (538, 1440), (640, 1440), (727, -240), (751, 720)]

def boundaryRow345 : Integer.Sparse (Fin 909) := [(0, 29), (1, -515), (2, 480), (3, 1280), (4, 800), (5, -420), (6, 30), (7, 240), (8, 800), (9, -20), (12, 320), (23, -480), (24, -2880), (27, 1140), (30, -1680), (31, -960), (33, -960), (49, 1440), (51, -720), (52, 80), (55, -1920), (68, 180), (69, 80), (71, 320), (105, 720), (106, 1440), (124, -240), (126, -1680), (197, -960), (236, -1440), (237, -720), (290, 720), (299, 1440), (306, -480), (308, -240), (728, -240), (751, 720), (811, 1440), (812, 1440)]

def boundaryRow346 : Integer.Sparse (Fin 909) := [(0, -1), (1, -80), (2, 555), (3, 2800), (4, 960), (5, -660), (6, 40), (7, 1040), (8, 1440), (9, -20), (26, 640), (31, -960), (35, 480), (46, 1440), (51, -3360), (52, 480), (56, -1680), (69, 240), (70, 160), (71, 320), (77, 1440), (97, 720), (107, 1440), (228, -480), (238, -720), (262, -960), (286, 720), (309, -720), (327, 1440), (735, 1440), (736, 1440), (796, -240)]

def boundaryRow347 : Integer.Sparse (Fin 909) := [(0, 9), (1, -110), (2, 515), (3, 1040), (4, 320), (5, -740), (6, 80), (7, 400), (8, 1600), (9, -20), (12, 400), (23, -240), (27, 300), (30, -480), (33, -960), (45, 2880), (51, -2880), (52, 160), (54, -1440), (69, 80), (71, 640), (259, -960), (282, 720), (293, 1440), (308, -720), (325, 1440), (721, -480), (723, -240), (738, 2880), (739, 2880)]

def boundaryRow349 : Integer.Sparse (Fin 909) := [(0, -13), (1, -630), (2, 660), (3, 4800), (4, 960), (5, -660), (6, 35), (7, 1840), (8, 720), (9, -20), (12, 1440), (13, 720), (23, -2160), (24, -1200), (25, -2400), (26, 320), (27, 480), (31, -1920), (33, -960), (35, 1040), (48, 1440), (51, -4080), (52, 640), (54, -3120), (55, -960), (56, -1200), (64, -2400), (68, 180), (69, 240), (70, 160), (97, 720), (100, 4320), (104, 1440), (124, -240), (125, -2160), (126, -1440), (197, -480), (238, -1680), (291, 720), (300, 1440), (307, -480), (309, -240), (538, 720), (543, 1440), (643, 1440), (727, -240)]

def boundaryRow350 : Integer.Sparse (Fin 909) := [(0, 18), (1, -520), (2, 425), (3, 2760), (4, 720), (5, -510), (6, 35), (7, 1040), (8, 960), (9, -10), (10, -240), (12, 520), (13, 480), (24, -960), (26, 560), (27, 270), (30, -480), (31, -480), (35, 680), (49, 720), (51, -1080), (52, 80), (55, -840), (68, 90), (69, 40), (71, 160), (82, 80), (95, 720), (107, 1440), (124, -120), (126, -840), (197, -480), (236, -720), (238, -480), (290, 360), (309, -120), (538, 360), (728, -120), (810, 720), (811, 720)]

def boundaryRow351 : Integer.Sparse (Fin 909) := [(0, -2), (1, -195), (2, 360), (3, 2960), (4, 520), (5, -550), (6, 65), (7, 440), (8, 480), (9, -10), (11, 80), (12, 720), (13, 1680), (26, 480), (35, 1200), (45, 720), (51, -960), (52, 1360), (54, -480), (56, -480), (69, 120), (70, 80), (71, 160), (102, 1440), (103, 720), (228, -240), (262, -480), (286, 360), (309, -360), (327, 720), (739, 720), (796, -120), (870, 720)]

def boundaryRow353 : Integer.Sparse (Fin 909) := [(0, -8), (1, -345), (2, 605), (3, 5600), (4, 1280), (5, -1000), (6, 130), (7, 480), (8, 640), (11, 240), (12, 1280), (13, 2880), (26, 1440), (35, 2160), (43, 1440), (45, 1440), (51, -1200), (52, 2480), (54, -960), (55, -240), (56, -960), (77, 720), (102, 2880), (103, 2880), (228, -960), (546, 1440), (737, 1440), (739, 1440), (870, 1440)]

def boundaryRow354 : Integer.Sparse (Fin 909) := [(0, -29), (1, 370), (2, 835), (3, 4080), (5, -1460), (6, 210), (7, 1200), (8, 640), (9, -20), (10, -720), (12, 1280), (13, 3840), (33, -960), (35, 2560), (38, 1440), (52, 3040), (54, -960), (59, -960), (69, 240), (70, 160), (72, 720), (75, 1440), (82, 800), (128, 800), (199, -720), (201, -1920), (306, -720), (313, 2880), (498, 720), (505, 1440), (540, 1440), (721, -960), (723, -240), (760, 1440)]

def boundaryRow355 : Integer.Sparse (Fin 909) := [(0, -1), (1, -370), (2, 105), (3, 2400), (4, 720), (5, -40), (7, 480), (12, 1200), (13, 640), (23, -2160), (24, -2160), (25, -1440), (27, 300), (33, -1440), (35, 320), (55, -2880), (63, -960), (68, 60), (124, -720), (126, -720), (196, -480), (197, -1440), (290, 2160), (299, 2160), (306, -720), (728, -720)]

def boundaryRow356 : Integer.Sparse (Fin 909) := [(0, -2), (1, -69), (2, 24), (3, 432), (4, 48), (5, -36), (6, 3), (7, 192), (9, -4), (12, 240), (13, 64), (23, -432), (25, -144), (27, 84), (33, -288), (35, 96), (51, -432), (54, -576), (63, -96), (68, 24), (69, 48), (70, 32), (124, -288), (196, -192), (259, -288), (282, 432), (293, 432), (308, -144), (721, -144), (723, -144)]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryRow33 : Integer.Sparse (Fin 909) := [(0, 56), (1, -675), (2, 305), (3, 1760), (4, 1120), (5, -80), (7, 160), (8, 240), (12, 440), (24, -480), (26, 160), (27, 180), (30, -240), (31, -720), (45, 360), (46, 360), (51, -480), (56, -240)]

def boundaryRow34 : Integer.Sparse (Fin 909) := [(0, 67), (1, -1010), (2, 185), (3, 3200), (4, 960), (5, -60), (7, 80), (8, 160), (12, 1040), (13, 1200), (25, -960), (26, 640), (31, -960), (33, -960), (38, 720), (39, 1440), (54, -720)]

def boundaryRow35 : Integer.Sparse (Fin 909) := [(0, 8), (1, -151), (2, 109), (3, 624), (4, 192), (5, -44), (7, 48), (8, 160), (12, 96), (23, -48), (25, -96), (26, 128), (27, 36), (30, -96), (31, -192), (33, -384), (36, 144), (39, 288), (40, 288), (51, -192), (54, -240), (55, -144)]

def boundaryRow39 : Integer.Sparse (Fin 909) := [(0, 17), (1, -309), (2, 76), (3, 1008), (4, 480), (26, 528), (53, 144), (57, 144)]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryRow100 : Integer.Sparse (Fin 909) := [(0, 44), (1, -690), (2, 385), (3, 4960), (4, 2480), (5, -260), (6, 15), (7, 640), (8, 480), (12, 240), (13, 160), (24, -480), (26, 2160), (31, -480), (35, 320), (37, 2160), (40, 1440), (52, 160), (56, -1200), (81, -960), (83, 720), (85, 1440), (99, 1440), (107, 1440), (228, -960)]

def boundaryRow101 : Integer.Sparse (Fin 909) := [(0, -1), (1, -390), (2, 480), (3, 3520), (4, 1120), (5, -420), (6, 35), (7, 1200), (8, 240), (12, 880), (13, 720), (23, -240), (24, -240), (25, -480), (26, 880), (31, -720), (33, -1440), (35, 1200), (41, 720), (43, 1440), (51, -720), (52, 1120), (54, -480), (59, -480), (73, 720), (81, -480), (94, 1440), (95, 720), (103, 1440), (104, 1440), (201, -240)]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryRow102 : Integer.Sparse (Fin 909) := [(0, 23), (1, -385), (2, 310), (3, 1720), (4, 760), (5, -210), (6, 10), (7, 280), (8, 360), (12, 160), (13, 80), (24, -240), (25, -240), (26, 400), (31, -720), (33, -600), (35, 120), (39, 720), (42, 720), (44, 360), (52, 200), (54, -240), (56, -120), (81, -240), (85, 360), (86, 360), (97, 360), (99, 720), (100, 360), (228, -120)]

def boundaryRow103 : Integer.Sparse (Fin 909) := [(0, 21), (1, -255), (2, 170), (3, 880), (4, 432), (5, -88), (6, 4), (7, 80), (8, 192), (26, 288), (30, -96), (31, -96), (35, 32), (40, 288), (52, 80), (56, -96), (57, 288), (81, -96), (85, 144), (86, 144), (107, 288), (228, -48), (239, 288)]

def boundaryRow104 : Integer.Sparse (Fin 909) := [(0, 3), (1, -113), (2, 53), (3, 640), (4, 240), (5, -26), (6, 1), (7, 72), (8, 32), (12, 200), (13, 144), (25, -72), (26, 176), (33, -120), (35, 80), (37, 144), (38, 144), (39, 288), (40, 288), (51, -48), (52, 64), (54, -48), (55, -240), (81, -48), (84, 72), (85, 144), (89, 144), (104, 72), (228, -72)]

def boundaryRow105 : Integer.Sparse (Fin 909) := [(0, 7), (1, -235), (2, 111), (3, 1424), (4, 464), (5, -60), (6, 3), (7, 160), (8, 96), (12, 352), (13, 144), (23, -96), (25, -144), (26, 416), (31, -96), (33, -480), (35, 80), (36, 288), (37, 288), (39, 576), (40, 576), (52, 32), (54, -144), (55, -480), (81, -192), (83, 144), (85, 288), (87, 288), (100, 288), (228, -192)]

def boundaryRow106 : Integer.Sparse (Fin 909) := [(0, 11), (1, -185), (2, 160), (3, 1680), (4, 360), (5, -90), (7, 480), (8, 120), (12, 880), (13, 80), (23, -360), (24, -600), (25, -360), (27, 180), (31, -240), (33, -240), (35, 80), (48, 360), (51, -600), (54, -240), (100, 720), (105, 720)]

def boundaryRow107 : Integer.Sparse (Fin 909) := [(0, 21), (1, -333), (2, 124), (3, 1072), (4, 672), (5, -36), (7, 192), (8, 48), (12, 192), (23, -144), (24, -240), (25, -288), (26, 128), (27, 72), (31, -672), (35, 32), (46, 576), (47, 144), (51, -240), (54, -96), (97, 288), (106, 288)]

def boundaryRow108 : Integer.Sparse (Fin 909) := [(0, -18), (1, -560), (2, 555), (3, 5200), (4, 720), (5, -440), (6, 25), (7, 1200), (8, 560), (10, -720), (12, 2240), (13, 3200), (26, 640), (33, -960), (35, 1040), (37, 720), (39, 720), (40, 720), (41, 1440), (51, -960), (52, 800), (54, -480), (55, -720), (59, -960), (73, 720), (74, 720), (75, 720), (95, 1440), (102, 720), (103, 720), (201, -240)]

def boundaryRow128 : Integer.Sparse (Fin 909) := [(0, 4), (1, -44), (2, 7), (5, -12), (6, 3), (23, -144), (25, -144), (27, 84), (30, -144), (31, -288), (63, -96), (68, 24), (105, 432), (124, -144), (196, -48), (236, -288), (237, -144)]

def boundaryRow129 : Integer.Sparse (Fin 909) := [(0, 6), (1, -53), (2, 119), (3, 240), (5, -112), (6, 6), (7, 144), (8, 288), (12, 96), (13, 32), (23, -144), (27, 108), (30, -288), (35, 32), (51, -288), (54, -144), (68, 24), (124, -144), (196, -48), (236, -288)]

def boundaryRow130 : Integer.Sparse (Fin 909) := [(0, 37), (1, -930), (2, 975), (3, 4880), (4, 1360), (5, -840), (6, 40), (7, 1760), (8, 1920), (12, 960), (13, 480), (23, -480), (24, -1440), (26, 640), (27, 600), (30, -960), (31, -960), (35, 800), (51, -4320), (52, 320), (54, -960), (55, -480), (56, -1200), (95, 1440), (97, 720), (107, 1440), (238, -720)]

def boundaryRow131 : Integer.Sparse (Fin 909) := [(0, -1), (1, 110), (2, 5), (14, 2160), (23, -2400), (25, -1440), (63, -1440), (68, 60), (124, -960), (129, 1440), (196, -480), (230, 2160)]

def boundaryRow133 : Integer.Sparse (Fin 909) := [(0, -2), (1, -455), (2, 195), (3, 3040), (4, 720), (5, -80), (7, 480), (12, 1840), (13, 480), (15, 2160), (23, -2160), (24, -720), (25, -1440), (27, 420), (33, -1440), (35, 160), (51, -1440), (54, -1440), (63, -480), (68, 60), (124, -720), (126, -240), (144, 1440), (196, -480), (205, 2160)]

def boundaryRow134 : Integer.Sparse (Fin 909) := [(0, 8), (1, -30), (2, 25), (5, -12), (6, 3), (17, 432), (23, -288), (25, -624), (27, 48), (30, -144), (31, -576), (63, -96), (68, 12), (87, 432), (108, 432), (123, -432), (124, -144), (196, -96), (203, 432), (216, 288), (226, -144), (236, -48), (237, -144)]

def boundaryRow135 : Integer.Sparse (Fin 909) := [(0, 52), (1, -425), (2, 55), (17, 2160), (23, -1440), (25, -3600), (27, 480), (30, -960), (31, -4080), (63, -960), (105, 2160), (108, 2160), (123, -720), (231, 1440), (237, -720)]

def boundaryRow138 : Integer.Sparse (Fin 909) := [(0, -9), (1, -845), (2, 530), (3, 6960), (5, -160), (7, 960), (12, 3440), (13, 4560), (16, 2160), (23, -2880), (27, 540), (35, 320), (38, 4320), (51, -2880), (54, -2880), (55, -1440), (68, 60), (124, -720), (125, -240), (140, 2160), (141, 1440), (196, -480)]

def boundaryRow139 : Integer.Sparse (Fin 909) := [(0, 101), (1, -2045), (2, 420), (3, 8560), (4, 3280), (5, -20), (7, 240), (12, 2640), (13, 480), (18, 2160), (23, -1440), (24, -1440), (25, -1440), (26, 1760), (27, 240), (31, -1440), (33, -1440), (35, 160), (43, 4320), (47, 2160), (51, -240), (55, -1440), (63, -480), (143, 1440)]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryRow140 : Integer.Sparse (Fin 909) := [(0, 149), (1, -2280), (2, 265), (3, 6960), (4, 5280), (5, -40), (7, 480), (12, 1200), (13, 320), (23, -1440), (24, -1440), (25, -3600), (26, 2400), (27, 240), (31, -3600), (35, 560), (44, 4320), (55, -2160), (63, -480), (108, 2160), (123, -720)]

def boundaryRow144 : Integer.Sparse (Fin 909) := [(0, 32), (1, -25), (2, 95), (5, -60), (14, 1080), (17, 2160), (23, -1920), (25, -2880), (27, 480), (30, -720), (31, -2160), (63, -240), (108, 2160), (123, -720), (124, -480), (129, 720), (203, 4320), (230, 2160)]

def boundaryRow145 : Integer.Sparse (Fin 909) := [(0, 31), (1, -354), (2, 141), (3, 704), (4, 384), (5, -24), (12, 320), (13, 64), (15, 432), (20, 864), (23, -144), (24, -432), (27, 180), (30, -288), (51, -288), (52, 96), (126, -192), (144, 288), (205, 864), (208, 1728)]

def boundaryRow146 : Integer.Sparse (Fin 909) := [(0, 23), (1, -885), (2, 210), (3, 3840), (4, 1200), (12, 1840), (13, 960), (16, 1080), (17, 2160), (23, -1080), (26, 480), (35, 240), (38, 1080), (40, 2160), (51, -720), (52, 240), (55, -1800), (125, -480), (140, 2160), (141, 720), (146, 4320)]

def boundaryRow147 : Integer.Sparse (Fin 909) := [(0, -1), (1, -11), (2, 21), (5, -24), (6, 3), (17, 216), (23, -72), (25, -96), (27, 90), (28, 432), (30, -360), (31, -144), (203, 432), (216, 144), (236, -96), (253, 864)]

def boundaryRow150 : Integer.Sparse (Fin 909) := [(0, 3), (1, -290), (2, 165), (3, 2080), (4, 640), (5, -60), (7, 320), (12, 1120), (15, 1440), (23, -1680), (24, -1440), (25, -1200), (27, 360), (33, -480), (48, 1440), (51, -480), (55, -960), (68, 60), (124, -480), (126, -480), (137, 1440), (197, -480), (205, 1440), (230, 720)]

def boundaryRow151 : Integer.Sparse (Fin 909) := [(0, 17), (1, -725), (2, 260), (3, 4720), (4, 1120), (5, -120), (7, 640), (12, 2000), (13, 560), (16, 720), (23, -2880), (24, -1920), (27, 540), (47, 2880), (51, -960), (55, -1920), (68, 60), (124, -240), (125, -720), (126, -480), (140, 2160), (205, 1440)]

def boundaryRow152 : Integer.Sparse (Fin 909) := [(0, 9), (1, -160), (2, 40), (3, 1160), (4, 440), (5, -5), (7, 60), (12, 780), (13, 80), (23, -120), (25, -660), (26, 200), (33, -360), (38, 180), (43, 720), (50, 180), (54, -60), (64, -120), (110, 360)]

def boundaryRow153 : Integer.Sparse (Fin 909) := [(0, 47), (1, -1150), (2, 350), (3, 4640), (4, 2480), (5, -120), (6, 5), (7, 240), (8, 160), (12, 1120), (21, 1440), (23, -480), (24, -960), (25, -240), (26, 720), (27, 360), (31, -1680), (33, -480), (35, 160), (43, 720), (47, 1440), (48, 720), (51, -2880), (52, 240), (54, -480), (56, -1200), (97, 720), (191, 1440), (209, 1440), (238, -240)]

def boundaryRow156 : Integer.Sparse (Fin 909) := [(0, 9), (1, -206), (2, 31), (3, 1088), (4, 432), (5, -4), (7, 48), (12, 464), (13, 144), (18, 288), (23, -240), (24, -288), (25, -144), (26, 32), (27, 36), (33, -96), (35, 32), (47, 288), (48, 144), (50, 432), (51, -48), (55, -384), (113, 144), (177, 288)]

def boundaryRow157 : Integer.Sparse (Fin 909) := [(0, 32), (1, -825), (2, 235), (3, 4960), (4, 1760), (12, 3520), (13, 1440), (25, -1920), (26, 400), (33, -1440), (34, 160), (41, 720), (43, 2880), (50, 1440), (114, 720), (116, 1440)]

def boundaryRow158 : Integer.Sparse (Fin 909) := [(0, 29), (1, -340), (2, 105), (3, 1560), (4, 760), (12, 440), (13, 440), (26, 320), (31, -540), (33, -360), (34, 160), (42, 360), (44, 360), (45, 360), (115, 180), (119, 360), (120, 360)]

def boundaryRow161 : Integer.Sparse (Fin 909) := [(0, 116), (1, -1215), (2, 325), (3, 3200), (4, 2000), (5, -60), (7, 240), (8, 160), (12, 800), (13, 160), (22, 1440), (26, 480), (31, -2880), (35, 160), (43, 1440), (46, 1440), (47, 720), (49, 1440), (51, -1680), (56, -240), (97, 720), (107, 1440), (204, 1440), (238, -720)]

def boundaryRow162 : Integer.Sparse (Fin 909) := [(0, 29), (1, -1090), (2, 335), (3, 4880), (4, 2000), (12, 2080), (13, 1200), (25, -2880), (26, 800), (31, -2160), (33, -2400), (34, 320), (38, 720), (39, 1440), (43, 1440), (46, 1440), (50, 1440), (54, -720), (64, -720), (110, 720), (112, 1440), (115, 720), (116, 1440)]

def boundaryRow165 : Integer.Sparse (Fin 909) := [(0, 21), (1, -1115), (2, 610), (3, 5520), (4, 2560), (5, -220), (7, 320), (8, 640), (12, 2160), (13, 1360), (15, 1440), (23, -720), (24, -1440), (25, -960), (27, 360), (31, -1920), (33, -2400), (39, 2880), (42, 2880), (51, -2880), (55, -960), (56, -2400), (64, -480), (68, 60), (97, 1440), (110, 1440), (124, -240), (125, -240), (126, -480), (140, 720), (144, 1440), (145, 1440), (197, -480), (238, -480)]

def boundaryRow166 : Integer.Sparse (Fin 909) := [(0, 37), (1, -406), (2, 139), (3, 1216), (4, 704), (12, 384), (13, 16), (25, -144), (26, 224), (31, -576), (33, -96), (34, 32), (43, 288), (45, 576), (46, 576), (50, 144), (115, 288), (116, 288)]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryRow167 : Integer.Sparse (Fin 909) := [(0, 126), (1, -2265), (2, 305), (3, 7920), (4, 5120), (5, -20), (7, 240), (12, 2320), (21, 1440), (23, -1200), (24, -1440), (25, -2640), (26, 2000), (27, 180), (31, -1680), (33, -480), (35, 160), (43, 2160), (44, 4320), (47, 720), (48, 1440), (51, -240), (55, -1920), (113, 720), (114, 1440), (191, 1440)]

def boundaryRow168 : Integer.Sparse (Fin 909) := [(0, 39), (1, -1590), (2, 670), (3, 8160), (4, 2720), (5, -100), (6, 5), (7, 160), (8, 160), (12, 3200), (13, 3440), (18, 1440), (23, -240), (24, -480), (25, -1200), (26, 320), (27, 180), (31, -1920), (33, -2400), (35, 240), (38, 720), (39, 1440), (42, 4320), (47, 720), (51, -2400), (52, 240), (54, -720), (55, -720), (56, -1200), (64, -480), (97, 720), (110, 1440), (142, 1440), (143, 1440), (238, -240)]

def boundaryRow169 : Integer.Sparse (Fin 909) := [(0, 102), (1, -1245), (2, 365), (3, 3440), (4, 2120), (12, 1280), (13, 240), (25, -480), (26, 320), (31, -1440), (33, -720), (34, 80), (44, 720), (45, 2160), (46, 720), (114, 360), (115, 720), (120, 720)]

def boundaryRow171 : Integer.Sparse (Fin 909) := [(0, 9), (1, -341), (2, 78), (3, 1568), (4, 592), (5, -28), (6, 2), (7, 48), (8, 32), (12, 608), (13, 608), (22, 288), (23, -48), (24, -96), (25, -192), (26, 224), (27, 36), (31, -288), (33, -384), (35, 160), (36, 144), (39, 576), (42, 576), (51, -384), (52, 64), (54, -432), (55, -144), (56, -336), (97, 144), (204, 288), (217, 288), (238, -48)]

def boundaryRow173 : Integer.Sparse (Fin 909) := [(0, 9), (1, -307), (2, 90), (3, 1280), (4, 528), (5, -44), (6, 4), (7, 64), (8, 64), (12, 400), (13, 288), (17, 288), (22, 288), (23, -48), (24, -288), (25, -144), (26, 224), (27, 48), (31, -288), (33, -240), (35, 96), (39, 576), (42, 576), (51, -288), (52, 64), (54, -96), (55, -192), (56, -240), (68, 12), (97, 144), (99, 288), (123, -96), (124, -48), (126, -96), (137, 144), (146, 288), (197, -144), (204, 288), (216, 288), (217, 288), (237, -96), (238, -48)]

def boundaryRow175 : Integer.Sparse (Fin 909) := [(0, 53), (1, -1175), (2, 470), (3, 4400), (4, 2400), (5, -160), (7, 480), (8, 320), (12, 1520), (15, 720), (23, -1680), (24, -1680), (25, -3360), (26, 320), (27, 420), (31, -2880), (33, -1200), (44, 1440), (48, 2880), (51, -1920), (54, -960), (55, -960), (64, -480), (68, 60), (100, 1440), (125, -720), (126, -720), (137, 1440), (145, 720), (207, 1440), (238, -480)]

def boundaryRow176 : Integer.Sparse (Fin 909) := [(0, 54), (1, -1555), (2, 420), (3, 6320), (4, 3040), (5, -100), (6, 5), (7, 320), (8, 80), (12, 2400), (13, 560), (18, 720), (23, -960), (24, -480), (25, -3360), (26, 720), (27, 240), (31, -2640), (33, -1200), (35, 240), (43, 720), (44, 720), (47, 720), (48, 1440), (50, 1440), (51, -2160), (52, 240), (54, -960), (55, -480), (56, -480), (64, -480), (100, 720), (104, 720), (142, 720), (177, 1440), (209, 720), (238, -240)]

def boundaryRow183 : Integer.Sparse (Fin 909) := [(0, 2), (1, -173), (2, 136), (3, 1264), (4, 480), (5, -72), (6, 3), (7, 240), (8, 112), (12, 128), (13, 128), (15, 144), (23, -48), (24, -192), (25, -96), (26, 528), (27, 36), (31, -192), (33, -384), (34, 112), (35, 80), (37, 288), (51, -288), (52, 32), (55, -144), (64, -96), (68, 12), (107, 288), (112, 288), (125, -48), (126, -144), (137, 288), (138, 144), (145, 144), (146, 144), (197, -48), (236, -48), (238, -96)]

def boundaryRow184 : Integer.Sparse (Fin 909) := [(0, 103), (1, -1580), (2, 560), (3, 7920), (4, 3840), (5, -40), (6, 5), (12, 720), (13, 480), (18, 720), (26, 3920), (31, -480), (33, -960), (34, 720), (35, 160), (52, 160), (53, 1440), (55, -480), (57, 1440), (119, 1440), (139, 720), (177, 1440)]

def boundaryRow187 : Integer.Sparse (Fin 909) := [(0, 71), (1, -1455), (2, 410), (3, 8000), (4, 3920), (5, -80), (6, 10), (7, 160), (8, 80), (12, 560), (13, 560), (21, 720), (26, 4080), (31, -960), (33, -1440), (34, 720), (35, 320), (37, 1440), (40, 720), (51, -240), (52, 80), (53, 1440), (55, -720), (56, -480), (57, 720), (119, 1440), (190, 720), (204, 720)]

def boundaryRow240 : Integer.Sparse (Fin 909) := [(0, 1), (1, -49), (2, -91), (3, -48), (5, 276), (6, -54), (7, -48), (8, -96), (9, 284), (35, -96), (52, -192), (58, -11), (69, -96), (70, -32), (71, -192), (278, -48), (310, -144), (495, -192), (726, 144), (818, 288)]

def boundaryRow241 : Integer.Sparse (Fin 909) := [(0, 9), (1, -255), (2, -530), (3, -480), (5, 1520), (6, -180), (7, -1920), (8, -1920), (9, 740), (35, -640), (58, -20), (69, -2400), (70, -1280), (71, -3840), (277, 720), (278, -240)]

def boundaryRow242 : Integer.Sparse (Fin 909) := [(1, 3), (2, -28), (3, -192), (4, -48), (5, 76), (6, -12), (7, -144), (9, 28), (11, -48), (26, -96), (35, -224), (52, -144), (58, -1), (69, -96), (70, -64), (228, 144), (278, -48), (310, -48), (495, -96), (726, 144)]

def boundaryRow243 : Integer.Sparse (Fin 909) := [(0, -1), (1, 70), (2, -25), (3, -1440), (4, -480), (5, 420), (6, -75), (9, 100), (11, -480), (26, -960), (35, -1440), (52, -1280), (55, 720), (58, -5), (228, 1440), (278, -80), (727, 720), (728, 480)]

def boundaryRow244 : Integer.Sparse (Fin 909) := [(0, 6), (1, -105), (2, -260), (3, -1440), (5, 480), (6, -90), (7, -480), (9, 120), (12, -480), (13, -2160), (35, -1680), (52, -1440), (54, 720), (58, -5), (69, -240), (70, -160), (82, -1280), (128, -1200), (199, 1440), (201, 1440), (278, -320), (310, -240), (492, 720), (495, -480), (723, 480), (726, 720)]

def boundaryRow245 : Integer.Sparse (Fin 909) := [(0, 1), (1, -80), (2, -270), (3, -480), (4, -80), (5, 560), (6, -60), (7, -720), (8, -800), (9, 180), (35, -160), (51, 720), (52, -240), (58, -5), (69, -480), (70, -160), (71, -960), (308, 720), (309, 480), (310, -80)]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryRow246 : Integer.Sparse (Fin 909) := [(0, 6), (1, -185), (2, -235), (3, -400), (4, -80), (5, 440), (6, -90), (8, -320), (9, 300), (11, -80), (13, -320), (26, -160), (35, -480), (52, -880), (56, 480), (58, -10), (69, -80), (71, -320), (82, -320), (128, -400), (201, 960), (228, 240), (278, -80), (310, -160), (492, 240), (495, -160), (796, 960), (818, 480)]

def boundaryRow247 : Integer.Sparse (Fin 909) := [(0, -1), (1, -15), (2, -190), (3, -640), (4, -160), (5, 320), (6, -35), (7, -480), (8, -320), (9, 100), (26, -160), (27, -60), (35, -320), (51, 480), (52, -480), (58, -5), (68, -60), (69, -320), (71, -160), (124, 240), (126, 480), (308, 480), (310, -160), (493, 480), (495, -160)]

def boundaryRow248 : Integer.Sparse (Fin 909) := [(0, 1), (1, 60), (2, -15), (3, -1120), (4, -320), (5, 420), (6, -25), (9, 60), (11, -320), (26, -800), (27, -120), (35, -1120), (52, -320), (55, 240), (58, -5), (68, -120), (238, 960), (278, -80), (493, 480), (495, -160), (727, 240)]

def boundaryRow249 : Integer.Sparse (Fin 909) := [(0, 7), (1, -55), (2, -175), (3, -1040), (5, 460), (6, -60), (7, -400), (8, -160), (9, 80), (12, -320), (13, -1360), (35, -720), (51, 480), (52, -960), (54, 240), (58, -5), (68, -60), (69, -160), (70, -160), (71, -80), (82, -320), (125, 480), (126, 240), (128, -400), (278, -80), (309, 480), (310, -160), (492, 240), (494, 480), (495, -160)]

def boundaryRow250 : Integer.Sparse (Fin 909) := [(0, 1), (1, 64), (2, -38), (3, -640), (4, -192), (5, 24), (6, -3), (12, -192), (13, -256), (26, -192), (27, -36), (35, -192), (51, 576), (52, -192), (55, 576), (127, 144), (128, -48), (493, 576), (494, 384), (495, -64)]

def boundaryRow251 : Integer.Sparse (Fin 909) := [(0, 3), (1, -45), (2, -200), (3, -400), (5, 700), (6, -60), (7, -80), (8, -480), (9, 160), (27, -180), (52, -480), (58, -10), (68, -180), (69, -80), (71, -400), (126, 240), (236, 480), (237, 480), (308, 240), (310, -80)]

def boundaryRow252 : Integer.Sparse (Fin 909) := [(0, 8), (1, -40), (2, -40), (3, -560), (5, 420), (6, -25), (9, 60), (11, -160), (12, -80), (13, -720), (26, -320), (35, -880), (52, -560), (55, 240), (58, -5), (68, -120), (82, -160), (128, -160), (237, 480), (278, -80), (494, 480), (495, -160), (728, 240)]

def boundaryRow253 : Integer.Sparse (Fin 909) := [(0, 6), (1, -5), (2, -15), (3, -480), (4, -80), (5, 480), (6, -30), (7, -160), (8, -160), (9, 140), (11, -160), (13, -320), (26, -480), (35, -960), (52, -160), (56, 240), (58, -10), (68, -180), (70, -160), (71, -240), (82, -160), (197, 480), (236, 240), (238, 240), (278, -80), (309, 240), (310, -80), (796, 240)]

def boundaryRow261 : Integer.Sparse (Fin 909) := [(0, 1), (1, -33), (2, -51), (3, -48), (5, 148), (6, -15), (7, -144), (8, -192), (9, 36), (35, -80), (52, -96), (69, -288), (70, -112), (71, -432), (256, 144), (257, -32), (495, -48)]

def boundaryRow262 : Integer.Sparse (Fin 909) := [(0, 2), (1, -15), (2, -10), (3, -280), (5, 170), (6, -25), (7, -360), (9, 50), (13, -120), (26, -120), (35, -560), (52, -240), (54, 360), (60, -80), (69, -360), (70, -320), (71, -240), (257, -80), (259, 360), (260, 240), (495, -40)]

def boundaryRow263 : Integer.Sparse (Fin 909) := [(0, 9), (1, -225), (2, -300), (3, -480), (4, -80), (5, 840), (6, -100), (7, -320), (8, -960), (9, 80), (13, -320), (26, -80), (35, -400), (51, 240), (52, -880), (56, 480), (59, 480), (69, -560), (70, -80), (71, -1200), (128, -160), (256, 240), (259, 240), (262, 960), (495, -160)]

def boundaryRow264 : Integer.Sparse (Fin 909) := [(0, 3), (1, -30), (2, -80), (3, -560), (4, -80), (5, 260), (6, -25), (7, -640), (8, -320), (9, 40), (26, -240), (35, -720), (52, -240), (67, -160), (69, -400), (70, -240), (71, -320), (81, 240), (256, 240), (257, -80), (495, -80)]

def boundaryRow265 : Integer.Sparse (Fin 909) := [(1, -1), (2, 12), (6, 1), (9, 4), (13, -160), (32, -32), (35, -96), (60, -64), (63, 144), (70, -64), (196, 144), (257, -32), (264, 96)]

def boundaryRow266 : Integer.Sparse (Fin 909) := [(0, 7), (1, 60), (2, 40), (3, -1280), (5, 140), (6, -35), (7, -480), (9, 20), (12, -240), (13, -640), (26, -800), (34, -480), (35, -1360), (55, 720), (60, -160), (67, -480), (70, -240), (71, -80), (197, 720), (257, -160), (268, 480)]

def boundaryRow267 : Integer.Sparse (Fin 909) := [(0, -2), (1, 315), (2, -60), (3, -4080), (4, -960), (5, 220), (6, -45), (7, -960), (9, 20), (13, -1200), (26, -2880), (34, -1280), (35, -2000), (52, -480), (55, 720), (64, 1440), (67, -960), (69, -80), (70, -240), (125, 720), (257, -160), (266, 480)]

def boundaryRow268 : Integer.Sparse (Fin 909) := [(0, 3), (1, 20), (2, 35), (3, -480), (5, 200), (6, -40), (7, -480), (9, 80), (13, -160), (26, -480), (34, -160), (35, -960), (54, 480), (67, -320), (69, -160), (70, -320), (71, -160), (124, 240), (196, 240), (197, 480), (257, -160), (259, 480), (266, 480), (495, -160)]

end MUB6.Certificate.PairSemantics

end OAI
end


