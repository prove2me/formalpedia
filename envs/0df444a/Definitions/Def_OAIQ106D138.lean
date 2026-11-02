-- Prove2me | Definitions.Def_OAIQ106D138
-- name    : OAIQ106D138
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T13:28:29.191198+00:00
-- url     : https://prove2.me/theorems/89cd7e68-ca1e-4473-8909-e6a76c9743e4
-- title:
--   Definitions bundle OAIQ106D138 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 116 declarations of OpenAI's Lean: 116 definitions. The definitions and types are `OAI.MUB6.Certificate.PairSemantics.boundaryRow36`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow362`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow363`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow364`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow365`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow368`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow369`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow37`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow372`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow373`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow374`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow377`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow378`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow379`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow38`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow381`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow382`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow383`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow384`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow385`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow386`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow387`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow388`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow389`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow390`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow393`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow394`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow395`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow396`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow397`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow398`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow399`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow4`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow40`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow400`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow401`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow402`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow403`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow404`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow405` and 76 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_PairSemantics_Boundary0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/PairSemantics/Boundary0.lean), [`MutuallyUnbiased_PairSemantics_Boundary12`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/PairSemantics/Boundary12.lean), [`MutuallyUnbiased_PairSemantics_Boundary13`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/PairSemantics/Boundary13.lean), [`MutuallyUnbiased_PairSemantics_Boundary14`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/PairSemantics/Boundary14.lean), [`MutuallyUnbiased_PairSemantics_Boundary15`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/PairSemantics/Boundary15.lean), [`MutuallyUnbiased_PairSemantics_Boundary16`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/PairSemantics/Boundary16.lean), [`MutuallyUnbiased_PairSemantics_Boundary2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/PairSemantics/Boundary2.lean), [`MutuallyUnbiased_PairSemantics_Boundary3`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/PairSemantics/Boundary3.lean), [`MutuallyUnbiased_PairSemantics_Boundary4`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/PairSemantics/Boundary4.lean), [`MutuallyUnbiased_PairSemantics_Boundary5`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/PairSemantics/Boundary5.lean), [`MutuallyUnbiased_PairSemantics_Values15`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/PairSemantics/Values15.lean).
--
--   **Imports.** It imports the bundles `OAIQ106D000` and `OAIQ106D002` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.MUB6.Certificate.PairSemantics.boundarySound377`, `OAI.MUB6.Certificate.PairSemantics.boundarySound445`, `OAI.MUB6.Certificate.PairSemantics.boundarySound454`, `OAI.MUB6.Certificate.PairSemantics.boundarySound49`, `OAI.MUB6.Certificate.PairSemantics.boundarySound51`, `OAI.MUB6.Certificate.PairSemantics.boundarySound56`, `OAI.MUB6.Certificate.PairSemantics.boundarySound7`, `OAI.MUB6.Certificate.PairSemantics.boundarySound73`, `OAI.MUB6.Certificate.PairSemantics.boundarySound75` and `OAI.MUB6.Certificate.PairSemantics.boundarySound83`; the proofs of `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound135`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound138`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound139`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound140`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound148`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound149`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound150`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound151`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2170`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2171`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2172`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2174`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2175`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2200`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2201`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2202`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2204`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2205`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2206`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2207`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2208`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2211`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2212`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2214`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2216`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2217`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2218`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2219`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2221`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2222`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2223`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2224`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2225`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2226`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2227`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2228`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2229`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2230`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2231`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2232`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2233`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2235`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2238`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2240`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2241`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2242`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2244`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2245`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2246`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2258`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2261`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2263`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2273`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2274`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2280`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2288`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2292`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2297`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2301`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2367`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2368`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2369`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2371`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2372`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2373`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2374`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2375`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2377`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2378`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2379`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2380`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2381`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2382`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2383`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2384`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2385`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2386`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2388`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2389`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2390`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2391`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2393`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2394`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2395`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2396`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2397`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2398`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2399`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2400`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2401`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2402`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2403`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2404`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2405`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2406`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2407`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2408`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2409`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2410`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2411`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2413`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2414`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2415`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2418`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2419`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2420`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2423`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2424`, `OAI.MUB6.Certificate.PairSemantics.boundarySound377`, `OAI.MUB6.Certificate.PairSemantics.boundarySound445`, `OAI.MUB6.Certificate.PairSemantics.boundarySound454`, `OAI.MUB6.Certificate.PairSemantics.boundarySound49`, `OAI.MUB6.Certificate.PairSemantics.boundarySound51`, `OAI.MUB6.Certificate.PairSemantics.boundarySound56`, `OAI.MUB6.Certificate.PairSemantics.boundarySound7`, `OAI.MUB6.Certificate.PairSemantics.boundarySound73`, `OAI.MUB6.Certificate.PairSemantics.boundarySound75`, `OAI.MUB6.Certificate.PairSemantics.boundarySound83`, `OAI.MUB6.Certificate.PairSemantics.sound1643`, `OAI.MUB6.Certificate.PairSemantics.sound1648`, `OAI.MUB6.Certificate.PairSemantics.sound1652`, `OAI.MUB6.Certificate.PairSemantics.sound1774`, `OAI.MUB6.Certificate.PairSemantics.sound1800`, `OAI.MUB6.Certificate.PairSemantics.sound1803`, `OAI.MUB6.Certificate.PairSemantics.sound2315`, `OAI.MUB6.Certificate.PairSemantics.sound2709`, `OAI.MUB6.Certificate.PairSemantics.sound2732`, `OAI.MUB6.Certificate.PairSemantics.sound2733`, `OAI.MUB6.Certificate.PairSemantics.sound2913`, `OAI.MUB6.Certificate.PairSemantics.sound2917`, `OAI.MUB6.Certificate.PairSemantics.sound2922`, `OAI.MUB6.Certificate.PairSemantics.sound2931`, `OAI.MUB6.Certificate.PairSemantics.sound2968`, `OAI.MUB6.Certificate.PairSemantics.sound2969`, `OAI.MUB6.Certificate.PairSemantics.sound2975`, `OAI.MUB6.Certificate.PairSemantics.sound2977`, `OAI.MUB6.Certificate.PairSemantics.sound2979`, `OAI.MUB6.Certificate.PairSemantics.sound3002`, `OAI.MUB6.Certificate.PairSemantics.sound3004`, `OAI.MUB6.Certificate.PairSemantics.sound3012`, `OAI.MUB6.Certificate.PairSemantics.sound3023`, `OAI.MUB6.Certificate.PairSemantics.sound3027`, `OAI.MUB6.Certificate.PairSemantics.sound3033`, `OAI.MUB6.Certificate.PairSemantics.sound3042`, `OAI.MUB6.Certificate.PairSemantics.sound3043`, `OAI.MUB6.Certificate.PairSemantics.sound3051`, `OAI.MUB6.Certificate.PairSemantics.sound3065`, `OAI.MUB6.Certificate.PairSemantics.sound3066`, `OAI.MUB6.Certificate.PairSemantics.sound3067`, `OAI.MUB6.Certificate.PairSemantics.sound3076`, `OAI.MUB6.Certificate.PairSemantics.sound3079`, `OAI.MUB6.Certificate.PairSemantics.sound3081`, `OAI.MUB6.Certificate.PairSemantics.sound3084`, `OAI.MUB6.Certificate.PairSemantics.sound3085`, `OAI.MUB6.Certificate.PairSemantics.sound3093`, `OAI.MUB6.Certificate.PairSemantics.sound3095`, `OAI.MUB6.Certificate.PairSemantics.sound3099`, `OAI.MUB6.Certificate.PairSemantics.sound3100`, `OAI.MUB6.Certificate.PairSemantics.sound3113`, `OAI.MUB6.Certificate.PairSemantics.sound3116`, `OAI.MUB6.Certificate.PairSemantics.sound3128`, `OAI.MUB6.Certificate.PairSemantics.sound3129`, `OAI.MUB6.Certificate.PairSemantics.sound3130`, `OAI.MUB6.Certificate.PairSemantics.sound3136`, `OAI.MUB6.Certificate.PairSemantics.sound3142`, `OAI.MUB6.Certificate.PairSemantics.sound3152`, `OAI.MUB6.Certificate.PairSemantics.sound3153`, `OAI.MUB6.Certificate.PairSemantics.sound3155`, `OAI.MUB6.Certificate.PairSemantics.sound3167`, `OAI.MUB6.Certificate.PairSemantics.sound3169`, `OAI.MUB6.Certificate.PairSemantics.sound3170`, `OAI.MUB6.Certificate.PairSemantics.sound3174`, `OAI.MUB6.Certificate.PairSemantics.sound3186`, `OAI.MUB6.Certificate.PairSemantics.sound3187`, `OAI.MUB6.Certificate.PairSemantics.sound3195`, `OAI.MUB6.Certificate.PairSemantics.sound3200`, `OAI.MUB6.Certificate.PairSemantics.sound3203`, `OAI.MUB6.Certificate.PairSemantics.sound3204`, `OAI.MUB6.Certificate.PairSemantics.sound3206`, `OAI.MUB6.Certificate.PairSemantics.sound3208`, `OAI.MUB6.Certificate.PairSemantics.sound3212`, `OAI.MUB6.Certificate.PairSemantics.sound3216`, `OAI.MUB6.Certificate.PairSemantics.sound3217`, `OAI.MUB6.Certificate.PairSemantics.sound3219`, `OAI.MUB6.Certificate.PairSemantics.sound3268`, `OAI.MUB6.Certificate.PairSemantics.sound3269`, `OAI.MUB6.Certificate.PairSemantics.sound3270`, `OAI.MUB6.Certificate.PairSemantics.sound3271`, `OAI.MUB6.Certificate.PairSemantics.sound3275`, `OAI.MUB6.Certificate.PairSemantics.sound3276`, `OAI.MUB6.Certificate.PairSemantics.sound3280`, `OAI.MUB6.Certificate.PairSemantics.sound3281`, `OAI.MUB6.Certificate.PairSemantics.sound3282`, `OAI.MUB6.Certificate.PairSemantics.sound3283`, `OAI.MUB6.Certificate.PairSemantics.sound3295`, `OAI.MUB6.Certificate.PairSemantics.sound3296`, `OAI.MUB6.Certificate.PairSemantics.sound3301`, `OAI.MUB6.Certificate.PairSemantics.sound3313`, `OAI.MUB6.Certificate.PairSemantics.sound3315`, `OAI.MUB6.Certificate.PairSemantics.sound3316`, `OAI.MUB6.Certificate.PairSemantics.sound3322`, `OAI.MUB6.Certificate.PairSemantics.sound3325`, `OAI.MUB6.Certificate.PairSemantics.sound3327`, `OAI.MUB6.Certificate.PairSemantics.sound3328`, `OAI.MUB6.Certificate.PairSemantics.sound3355`, `OAI.MUB6.Certificate.PairSemantics.sound3357`, `OAI.MUB6.Certificate.PairSemantics.sound3370`, `OAI.MUB6.Certificate.PairSemantics.sound3371`, `OAI.MUB6.Certificate.PairSemantics.sound3375`, `OAI.MUB6.Certificate.PairSemantics.sound3391`, `OAI.MUB6.Certificate.PairSemantics.sound3396`, `OAI.MUB6.Certificate.PairSemantics.sound3423`, `OAI.MUB6.Certificate.PairSemantics.sound3426`, `OAI.MUB6.Certificate.PairSemantics.sound3436`, `OAI.MUB6.Certificate.PairSemantics.sound3437`, `OAI.MUB6.Certificate.PairSemantics.sound3461`, `OAI.MUB6.Certificate.PairSourceBridge.allRowsSound`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound105`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound106`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound112`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound121`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound125`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound130`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound134`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound197`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound198`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound199`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound200`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound201`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound202`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound203`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound204`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound205`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound207`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound208`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound209`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound210`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound211`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound212`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound213`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound214`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound215`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound216`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound217`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound218`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound219`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound220`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound221`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound222`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound223`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound224`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound225`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound226`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound227`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound228`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound229`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound230`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound231`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound232`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound233`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound234`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound235`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound236`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound237`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound238`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound239`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound240`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound241`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound242`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound243`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound244`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound245`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound246`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound248`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound249`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound250`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound253`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound254`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound35`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound36`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound39`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound4`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound40`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound41`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound42`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound43`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound44`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound45`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound46`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound47`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound49`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound5`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound51`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound52`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound53`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound54`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound56`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound57`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound58`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound59`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound6`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound60`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound61`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound62`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound63`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound64`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound65`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound66`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound67`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound69`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound70`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound72`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound74`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound76`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound77`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound78`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound8`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound9`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound90`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound93` and `OAI.MUB6.Certificate.PairSourceBridge.rowSound95`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ106D000
import Definitions.Def_OAIQ106D002

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value1000 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-5 / 48)), (3, (1 / 9)), (4, (1 / 9)), (12, (1 / 9))]

def value1001 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 144)), (2, (1 / 36)), (3, (2 / 9)), (13, (2 / 9)), (34, (1 / 9)), (52, (1 / 9))]

def value1002 : Sparse (Fin 909) := [(0, (1 / 180)), (1, (-1 / 12)), (3, (2 / 9)), (12, (2 / 9))]

def value1003 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-1 / 48)), (2, (1 / 24)), (3, (2 / 9)), (26, (1 / 9))]

def value1004 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (-1 / 144)), (5, (-1 / 18)), (6, (1 / 144)), (7, (2 / 9)), (8, (1 / 9)), (35, (2 / 9)), (67, (1 / 9))]

def value1005 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (-5 / 72)), (25, (-1 / 3)), (31, (-1 / 3))]

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

def boundaryRow4 : Integer.Sparse (Fin 909) := [(0, -4), (1, 95), (2, -25), (3, -320), (4, -160), (12, -160), (13, -80)]

def boundaryRow5 : Integer.Sparse (Fin 909) := [(0, -11), (1, 250), (2, -45), (3, -800), (4, -480), (12, -320), (25, 120), (26, -160)]

def boundaryRow6 : Integer.Sparse (Fin 909) := [(0, -9), (1, 315), (2, -70), (3, -480), (4, -400), (12, -80), (26, -80), (31, 240)]

def boundaryRow7 : Integer.Sparse (Fin 909) := [(0, 1), (1, -8), (2, 4), (14, 18), (17, 72), (23, -48), (25, -96), (27, 9), (30, -24), (31, -96)]

def boundaryRow8 : Integer.Sparse (Fin 909) := [(0, 149), (1, -1760), (2, 285), (3, 2080), (4, 2880), (12, 800), (15, 720), (20, 1440), (23, -240), (24, -720), (25, -480), (27, 180), (30, -480), (31, -960)]

def boundaryRow9 : Integer.Sparse (Fin 909) := [(0, -11), (1, -150), (2, 80), (3, 640), (4, 320), (12, 240), (16, 180), (17, 360), (23, -240), (27, 45), (30, -120)]

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

def boundaryRow362 : Integer.Sparse (Fin 909) := [(1, -93), (2, 175), (3, 784), (4, 192), (5, -216), (6, 16), (7, 416), (8, 336), (9, -8), (12, 32), (13, 32), (24, -336), (26, 112), (27, 96), (30, -96), (31, -192), (35, 176), (46, 144), (51, -528), (52, 144), (55, -96), (56, -96), (68, 24), (69, 96), (70, 48), (71, 80), (95, 288), (106, 144), (107, 288), (126, -288), (197, -96), (236, -96), (237, -48), (238, -96), (262, -96), (308, -48), (309, -48), (322, 144), (327, 144), (735, 288), (736, 144), (738, 144)]

def boundaryRow363 : Integer.Sparse (Fin 909) := [(0, -7), (1, -580), (2, 570), (3, 6160), (4, 1440), (5, -460), (6, 25), (7, 1440), (8, 480), (10, -720), (12, 2000), (13, 2880), (25, -1440), (26, 1440), (31, -720), (33, -1440), (35, 2080), (38, 2160), (39, 4320), (51, -720), (52, 1520), (54, -2160), (55, -720), (59, -1440), (60, 320), (81, -1440), (82, 240), (84, 2160), (85, 4320), (128, 480), (228, -2160), (311, 2160), (321, 4320), (323, 1440), (329, 4320), (330, 4320), (490, -720), (492, -960)]

def boundaryRow364 : Integer.Sparse (Fin 909) := [(0, 21), (1, -705), (2, 350), (3, 6240), (4, 2720), (5, -580), (6, 30), (7, 1920), (8, 960), (10, -720), (11, 240), (12, 480), (13, 640), (26, 3120), (35, 2000), (37, 2160), (40, 4320), (52, 240), (55, -720), (56, -2160), (81, -1440), (82, 240), (83, 2160), (85, 4320), (228, -3120), (501, 4320), (508, 4320), (784, 1440), (794, 4320), (796, -960)]

def boundaryRow365 : Integer.Sparse (Fin 909) := [(1, -78), (2, 19), (3, 432), (4, 96), (5, -64), (6, 9), (7, 144), (9, -4), (11, 48), (12, 144), (23, -144), (25, -288), (26, 96), (27, 36), (31, -288), (33, -576), (35, 224), (36, 432), (39, 864), (51, -288), (52, 144), (54, -720), (55, -144), (68, 12), (69, 48), (70, 32), (87, 432), (123, -288), (124, -144), (196, -96), (226, -144), (228, -144), (237, -144), (259, -288), (282, 432), (306, -288), (308, -144), (312, 432), (315, 864), (498, 864), (507, 864), (721, -432), (723, -336), (728, -48), (764, 864), (783, 288)]

def boundaryRow368 : Integer.Sparse (Fin 909) := [(0, 1), (1, -98), (2, 113), (3, 1488), (4, 512), (5, -160), (6, 14), (7, 560), (8, 128), (11, 128), (26, 896), (35, 896), (52, 368), (53, 288), (67, 128), (81, -672), (83, 144), (84, 432), (85, 576), (228, -816), (460, 288), (702, 288), (709, 576)]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryRow369 : Integer.Sparse (Fin 909) := [(0, -9), (1, -25), (2, 600), (3, 4480), (4, 1120), (5, -1400), (6, 190), (7, 2400), (8, 480), (9, -40), (11, 640), (24, -480), (26, 1920), (27, 120), (31, -480), (33, -960), (35, 3520), (37, 1440), (51, -480), (52, 2560), (55, -480), (68, 60), (69, 640), (70, 480), (81, -960), (83, 720), (85, 1440), (99, 1440), (123, -480), (124, -240), (126, -480), (197, -480), (228, -3360), (237, -480), (259, -480), (306, -960), (308, -480), (312, 720), (315, 1440), (322, 1440), (517, 2880), (541, 1440), (721, -720), (728, -240), (784, 1440)]

def boundaryRow372 : Integer.Sparse (Fin 909) := [(0, -2), (1, -63), (2, 107), (3, 1024), (4, 288), (5, -152), (6, 8), (7, 480), (8, 224), (10, -288), (11, 48), (12, 208), (13, 176), (25, -48), (26, 384), (33, -192), (35, 544), (37, 288), (39, 288), (40, 288), (52, 160), (54, -48), (55, -288), (56, -96), (59, -288), (67, 64), (73, 288), (74, 288), (75, 288), (81, -288), (84, 144), (85, 288), (201, -48), (228, -288), (307, -144), (321, 288), (330, 576), (425, 144), (428, 288), (501, 576), (503, 288), (507, 288), (508, 864), (727, -192)]

def boundaryRow373 : Integer.Sparse (Fin 909) := [(0, -11), (1, -15), (2, 415), (3, 4080), (4, 880), (5, -980), (6, 145), (7, 640), (8, 480), (11, 320), (12, 880), (13, 2320), (26, 1280), (33, -960), (35, 2320), (37, 1440), (39, 1440), (40, 1440), (52, 2080), (54, -720), (55, -1440), (56, -480), (81, -960), (82, 320), (83, 720), (85, 1440), (128, 320), (199, -240), (201, -480), (228, -1920), (306, -1440), (312, 1440), (329, 2880), (500, 1440), (517, 1440), (541, 2880), (721, -480), (728, -960), (760, 1440), (764, 1440), (784, 1440), (794, 4320)]

def boundaryRow374 : Integer.Sparse (Fin 909) := [(0, 7), (1, -142), (2, 152), (3, 544), (4, 256), (5, -128), (6, 7), (7, 192), (8, 224), (9, -4), (12, 48), (23, -336), (24, -960), (26, 32), (27, 324), (30, -384), (31, -288), (35, 48), (47, 144), (51, -144), (52, 64), (55, -528), (68, 48), (69, 32), (70, 16), (71, 32), (106, 576), (125, -192), (126, -480), (197, -96), (236, -192), (237, -192), (308, -48), (538, 288), (640, 144), (812, 288)]

def boundaryRow377 : Integer.Sparse (Fin 909) := [(0, -18), (1, 295), (2, 700), (3, 3040), (4, 160), (5, -1260), (6, 135), (7, 2240), (8, 720), (9, -60), (12, 320), (13, 1440), (23, -240), (26, 160), (27, 60), (35, 3200), (38, 720), (52, 2960), (54, -240), (55, -240), (59, -720), (60, 560), (68, 60), (69, 800), (70, 400), (81, -960), (82, 80), (84, 1440), (98, 720), (125, -720), (126, -480), (128, 400), (201, -240), (228, -480), (237, -240), (260, -480), (287, 720), (306, -480), (308, -240), (323, 1440), (392, 720), (492, -240), (499, 1440), (540, 720), (541, 1440), (728, -240)]

def boundaryRow378 : Integer.Sparse (Fin 909) := [(0, -24), (1, 360), (2, 715), (3, 4240), (4, 80), (5, -1360), (6, 175), (7, 1760), (8, 800), (10, -720), (11, 80), (12, 1280), (13, 4400), (26, 160), (33, -480), (35, 3920), (41, 720), (52, 3440), (54, -720), (59, -1920), (60, 640), (73, 720), (74, 720), (75, 720), (81, -480), (82, 960), (84, 720), (128, 1360), (199, -960), (201, -1680), (228, -480), (306, -720), (313, 1440), (324, 1440), (392, 720), (399, 720), (500, 720), (502, 1440), (517, 720), (545, 720), (721, -480), (760, 720)]

def boundaryRow379 : Integer.Sparse (Fin 909) := [(0, -31), (1, -330), (2, 410), (3, 6720), (4, 160), (5, -400), (6, 15), (7, 2320), (8, 320), (10, -2640), (12, 3120), (13, 5760), (23, -240), (26, 320), (27, 60), (33, -960), (34, 320), (35, 3680), (38, 1440), (51, -960), (52, 1760), (54, -960), (55, -480), (59, -3360), (60, 640), (72, 720), (73, 720), (74, 1440), (75, 1440), (82, 640), (84, 1440), (128, 640), (199, -720), (201, -720), (228, -480), (273, -480), (311, 2880), (313, 2880), (318, 1440)]

def boundaryRow381 : Integer.Sparse (Fin 909) := [(0, -6), (1, -205), (2, 175), (3, 2560), (4, 720), (5, -220), (6, 20), (7, 400), (8, 240), (10, -120), (12, 760), (13, 720), (23, -120), (25, -240), (26, 800), (27, 30), (31, -240), (33, -1440), (34, 160), (35, 560), (36, 720), (39, 1440), (51, -480), (52, 240), (54, -1200), (55, -960), (59, -480), (72, 360), (74, 720), (81, -960), (83, 720), (85, 1440), (199, -360), (228, -960), (273, -240), (311, 720), (312, 1440), (314, 1440), (316, 720), (321, 720), (329, 1440), (330, 2880), (490, -720), (492, -480)]

def boundaryRow382 : Integer.Sparse (Fin 909) := [(0, 9), (1, -570), (2, 380), (3, 6240), (4, 2400), (5, -400), (6, 45), (7, 1360), (8, 160), (11, 480), (12, 480), (13, 640), (26, 3040), (35, 3040), (37, 1440), (40, 2880), (52, 1280), (55, -1440), (56, -1440), (67, 160), (73, 720), (75, 1440), (81, -1440), (84, 1440), (85, 2880), (201, -720), (228, -2880), (501, 1440), (503, 1440), (508, 5760), (541, 2880), (794, 2880), (796, -960)]

def boundaryRow383 : Integer.Sparse (Fin 909) := [(0, -12), (1, -195), (2, 375), (3, 3920), (4, 800), (5, -900), (6, 130), (7, 880), (8, 480), (10, -240), (11, 480), (12, 1120), (13, 1680), (23, -240), (25, -1920), (26, 1280), (27, 60), (31, -960), (33, -960), (35, 2480), (38, 1440), (39, 2880), (51, -1440), (52, 1920), (54, -3120), (56, -480), (59, -960), (72, 720), (74, 1440), (82, 320), (87, 1440), (89, 2880), (123, -1920), (128, 320), (199, -960), (201, -480), (226, -1440), (228, -1440), (237, -480), (306, -480), (313, 1440), (315, 2880), (498, 1440), (505, 1440), (507, 5760), (540, 2880), (721, -1440), (723, -960), (764, 2880)]

def boundaryRow384 : Integer.Sparse (Fin 909) := [(0, -13), (1, -150), (2, 375), (3, 3840), (4, 800), (5, -700), (6, 30), (7, 2960), (8, 960), (10, -240), (12, 160), (13, 80), (23, -240), (24, -480), (25, -480), (26, 1760), (27, 60), (35, 3680), (38, 720), (51, -480), (52, 1120), (54, -720), (55, -480), (59, -480), (64, -960), (67, 800), (72, 720), (73, 1440), (81, -1920), (84, 1440), (104, 1440), (199, -240), (228, -480), (271, -480), (318, 1440), (425, 1440), (499, 1440)]

def boundaryRow385 : Integer.Sparse (Fin 909) := [(0, -9), (1, -280), (2, 565), (3, 7040), (4, 2160), (5, -860), (6, 70), (7, 3120), (8, 800), (11, 640), (12, 80), (13, 160), (26, 3920), (33, -480), (34, 320), (35, 4800), (37, 720), (52, 1920), (56, -240), (67, 640), (73, 720), (81, -2880), (83, 720), (84, 1440), (85, 2880), (201, -240), (228, -4320), (275, -480), (317, 1440), (428, 1440), (460, 1440), (517, 1440), (709, 1440)]

def boundaryRow386 : Integer.Sparse (Fin 909) := [(0, -12), (1, -20), (2, 615), (3, 4880), (4, 1120), (5, -1320), (6, 175), (7, 1760), (8, 720), (10, -240), (11, 640), (12, 320), (13, 1040), (24, -240), (26, 1840), (27, 60), (31, -480), (33, -480), (35, 3840), (41, 720), (51, -960), (52, 3200), (56, -480), (59, -960), (60, 160), (73, 720), (81, -480), (82, 80), (84, 720), (85, 1440), (99, 1440), (103, 1440), (123, -960), (128, 240), (201, -240), (228, -3120), (237, -480), (306, -480), (313, 720), (315, 1440), (324, 1440), (502, 720), (517, 1440), (545, 1440), (721, -720)]

def boundaryRow387 : Integer.Sparse (Fin 909) := [(0, -2), (1, -39), (2, 93), (3, 976), (4, 352), (5, -116), (6, 6), (7, 272), (8, 192), (10, -144), (12, 112), (13, 192), (26, 416), (33, -288), (34, 64), (35, 256), (36, 144), (40, 288), (52, 64), (54, -144), (55, -144), (56, -192), (59, -192), (72, 144), (75, 288), (81, -384), (83, 288), (85, 576), (199, -48), (228, -384), (271, -96), (307, -288), (316, 288), (330, 576), (426, 288), (428, 576), (498, 288), (501, 576), (508, 1152), (727, -192)]

def boundaryRow388 : Integer.Sparse (Fin 909) := [(0, -13), (1, 80), (2, 605), (3, 4480), (4, 800), (5, -1220), (6, 170), (7, 1200), (8, 640), (12, 720), (13, 2880), (26, 960), (35, 3040), (38, 720), (40, 1440), (52, 2720), (54, -480), (55, -720), (56, -960), (59, -480), (60, 160), (81, -960), (82, 560), (84, 1440), (85, 2880), (128, 560), (199, -480), (201, -960), (228, -1440), (306, -720), (323, 1440), (329, 2880), (499, 720), (540, 1440), (541, 2880), (728, -960), (760, 1440), (794, 5760)]

def boundaryRow389 : Integer.Sparse (Fin 909) := [(0, -5), (1, 76), (2, 127), (3, 656), (5, -216), (6, 24), (7, 384), (8, 128), (10, -48), (12, 112), (13, 512), (23, -48), (27, 12), (35, 720), (51, -96), (52, 544), (54, -192), (59, -240), (60, 160), (62, -192), (72, 144), (73, 288), (81, -192), (82, 32), (98, 288), (128, 112), (199, -96), (201, -96), (237, -96), (267, -96), (284, 288), (306, -96), (392, 288), (499, 288), (502, 288)]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryRow390 : Integer.Sparse (Fin 909) := [(0, -29), (1, 550), (2, 855), (3, 4480), (5, -1500), (6, 190), (7, 1680), (8, 960), (10, -720), (12, 1120), (13, 5120), (32, 320), (35, 3680), (52, 4160), (59, -1920), (60, 640), (72, 720), (73, 1440), (75, 1440), (81, -960), (82, 880), (128, 1680), (199, -720), (201, -2400), (267, -480), (284, 1440), (306, -720), (399, 2880), (499, 720), (502, 2880), (760, 1440)]

def boundaryRow393 : Integer.Sparse (Fin 909) := [(0, -38), (1, -325), (2, 555), (3, 5040), (5, -820), (6, 30), (7, 2880), (8, 1440), (9, -20), (10, -2160), (12, 2720), (13, 4000), (23, -1440), (27, 360), (35, 1760), (38, 2160), (51, -4320), (54, -4320), (55, -720), (59, -3600), (68, 60), (69, 240), (70, 160), (72, 4320), (74, 4320), (82, 240), (124, -720), (196, -480), (199, -2400), (259, -1440), (282, 2160), (308, -720), (321, 2160), (505, 1440), (723, -720), (727, -240)]

def boundaryRow394 : Integer.Sparse (Fin 909) := [(0, -14), (1, -100), (2, 255), (3, 3440), (4, 400), (5, -660), (6, 45), (7, 3040), (8, 640), (10, -240), (12, 640), (13, 960), (24, -240), (26, 960), (27, 60), (34, 160), (35, 3840), (37, 1440), (51, -480), (52, 1520), (55, -480), (59, -480), (60, 320), (67, 160), (73, 720), (81, -480), (83, 1440), (84, 3600), (228, -1200), (273, -480), (311, 1440), (317, 1440)]

def boundaryRow395 : Integer.Sparse (Fin 909) := [(0, -3), (1, -31), (2, 91), (3, 656), (4, 48), (5, -164), (6, 9), (7, 592), (8, 256), (9, -8), (10, -192), (12, 80), (13, 64), (24, -192), (26, 96), (27, 48), (35, 512), (37, 288), (51, -288), (52, 144), (55, -96), (59, -240), (67, 32), (68, 12), (69, 128), (70, 96), (73, 576), (81, -96), (84, 144), (124, -48), (126, -96), (197, -96), (228, -48), (259, -96), (308, -96), (321, 144), (322, 288), (501, 288), (503, 288), (727, -48)]

def boundaryRow396 : Integer.Sparse (Fin 909) := [(0, -12), (1, -195), (2, 775), (3, 6320), (4, 1840), (5, -1040), (6, 70), (7, 2800), (8, 1280), (10, -240), (11, 240), (12, 80), (13, 80), (24, -240), (26, 2880), (27, 60), (31, -240), (33, -960), (34, 160), (35, 3280), (37, 1440), (51, -480), (52, 1760), (55, -480), (59, -480), (67, 160), (73, 720), (81, -3840), (83, 2880), (84, 2880), (85, 4320), (228, -4080), (273, -480), (311, 720), (314, 1440), (317, 1440), (490, -720)]

def boundaryRow397 : Integer.Sparse (Fin 909) := [(0, -1), (1, -310), (2, 730), (3, 6400), (4, 2080), (5, -1120), (6, 105), (7, 3040), (8, 960), (11, 560), (26, 3520), (35, 4160), (52, 2240), (53, 1440), (67, 160), (81, -2880), (83, 1440), (84, 3600), (85, 4320), (228, -4800), (702, 1440), (709, 1440)]

def boundaryRow398 : Integer.Sparse (Fin 909) := [(0, -14), (1, -15), (2, 45), (3, 2320), (5, -440), (6, 70), (7, 1680), (8, 640), (9, -60), (10, -480), (23, -480), (25, -240), (26, 640), (27, 120), (35, 2480), (36, 720), (52, 480), (54, -1200), (55, -240), (64, -480), (67, 400), (68, 60), (69, 800), (70, 400), (72, 1440), (83, 1440), (125, -720), (126, -480), (199, -480), (228, -960), (260, -480), (271, -480), (287, 720), (308, -240), (316, 1440), (425, 720), (492, -240), (498, 720), (501, 1440), (727, -240)]

def boundaryRow399 : Integer.Sparse (Fin 909) := [(0, -3), (1, 15), (2, 108), (3, 768), (4, 144), (5, -196), (6, 20), (7, 480), (8, 176), (11, 16), (12, 32), (13, 112), (26, 272), (34, 32), (35, 768), (37, 144), (52, 480), (56, -48), (59, -48), (60, 32), (67, 64), (73, 288), (81, -384), (83, 144), (84, 432), (128, 16), (201, -96), (228, -288), (275, -96), (317, 288), (428, 144), (460, 144), (517, 144), (709, 144)]

def boundaryRow400 : Integer.Sparse (Fin 909) := [(0, -33), (1, 235), (2, 950), (3, 4480), (4, 160), (5, -1600), (6, 100), (7, 3680), (8, 2240), (10, -2400), (12, 1360), (13, 2560), (26, 160), (33, -480), (34, 160), (35, 3440), (38, 720), (52, 2240), (54, -240), (59, -3840), (60, 160), (72, 1440), (73, 2880), (74, 1440), (75, 2880), (81, -1440), (82, 320), (84, 1440), (128, 400), (199, -720), (201, -960), (228, -480), (271, -480), (307, -720), (318, 1440), (426, 720), (428, 1440), (499, 720)]

def boundaryRow401 : Integer.Sparse (Fin 909) := [(0, -29), (1, -45), (2, 1290), (3, 6720), (4, 960), (5, -1080), (6, 60), (7, 1680), (8, 1440), (10, -720), (12, 2160), (13, 4400), (31, -720), (33, -1440), (35, 1680), (42, 4320), (51, -2880), (52, 3120), (59, -2880), (60, 480), (81, -1440), (82, 240), (86, 4320), (128, 960), (311, 2160), (326, 4320), (328, 4320), (490, -720)]

def boundaryRow402 : Integer.Sparse (Fin 909) := [(0, 3), (1, -230), (2, 1095), (3, 6480), (4, 1520), (5, -1720), (6, 150), (7, 3040), (8, 1760), (11, 240), (26, 2560), (35, 4000), (52, 2640), (57, 1440), (67, 800), (81, -3360), (86, 2880), (228, -720), (460, 1440), (855, 4320)]

def boundaryRow403 : Integer.Sparse (Fin 909) := [(0, -16), (1, 140), (2, 1155), (3, 4000), (4, 880), (5, -1820), (6, 95), (7, 3760), (8, 3040), (12, 80), (13, 160), (26, 1120), (31, -960), (33, -960), (35, 2480), (42, 1440), (51, -960), (52, 1120), (56, -240), (59, -960), (67, 480), (76, 1440), (81, -2400), (86, 1440), (97, 720), (107, 1440), (201, -240), (238, -720), (307, -720), (326, 2880), (425, 720), (428, 1440), (506, 1440)]

def boundaryRow404 : Integer.Sparse (Fin 909) := [(0, -1), (1, 64), (2, 143), (3, 304), (4, 32), (5, -412), (6, 60), (7, 48), (8, 256), (9, -4), (11, 32), (12, 16), (25, -96), (26, 64), (31, -192), (33, -192), (35, 288), (39, 288), (52, 608), (54, -96), (69, 16), (71, 64), (87, 144), (123, -192), (226, -48), (228, -96), (237, -144), (239, 288), (306, -144), (315, 576), (498, 144), (507, 288), (721, -192), (723, -48), (760, 288), (764, 288)]

def boundaryRow405 : Integer.Sparse (Fin 909) := [(0, -27), (1, 505), (2, 1080), (3, 3840), (5, -2140), (6, 250), (7, 2160), (8, 1920), (9, -20), (12, 560), (13, 2640), (35, 3680), (51, -480), (52, 4080), (54, -240), (59, -1200), (60, 720), (69, 160), (71, 560), (82, 400), (86, 1440), (128, 800), (199, -240), (201, -960), (260, -480), (262, -480), (289, 720), (309, -720), (327, 1440), (328, 1440), (392, 720), (492, -240)]

def boundaryRow406 : Integer.Sparse (Fin 909) := [(0, -29), (1, 535), (2, 1010), (3, 3600), (4, 160), (5, -2000), (6, 240), (7, 1600), (8, 1600), (12, 560), (13, 2720), (26, 80), (35, 3120), (42, 720), (51, -480), (52, 4240), (56, -480), (59, -1920), (60, 800), (76, 720), (82, 240), (86, 720), (102, 720), (103, 720), (128, 880), (201, -960), (328, 1440), (392, 720), (399, 720), (506, 1440), (798, 720)]

def boundaryRow407 : Integer.Sparse (Fin 909) := [(0, -21), (1, 275), (2, 450), (3, 1440), (4, 160), (5, -1240), (6, 200), (7, 640), (8, 1040), (9, -20), (11, 160), (12, 160), (13, 720), (25, -240), (26, 320), (35, 1360), (39, 720), (51, -480), (52, 2000), (54, -480), (56, -480), (59, -480), (69, 80), (71, 320), (74, 720), (82, 160), (89, 720), (123, -480), (128, 400), (199, -240), (201, -480), (226, -240), (228, -480), (315, 1440), (507, 2160), (540, 720), (721, -480), (723, -240), (764, 720)]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryRow408 : Integer.Sparse (Fin 909) := [(0, -23), (1, -105), (2, 1130), (3, 5680), (4, 1200), (5, -1300), (6, 90), (7, 1760), (8, 2000), (10, -240), (12, 1600), (13, 2800), (24, -240), (26, 480), (27, 60), (31, -720), (33, -1920), (34, 320), (35, 1040), (39, 1440), (42, 1440), (51, -3120), (52, 1920), (55, -480), (56, -960), (59, -2400), (60, 320), (74, 720), (76, 1440), (81, -960), (85, 1440), (86, 1440), (128, 480), (201, -720), (228, -480), (273, -480), (311, 2160), (314, 1440), (315, 2880), (319, 1440), (326, 2880), (328, 1440), (490, -720)]

def boundaryRow409 : Integer.Sparse (Fin 909) := [(0, -14), (1, 15), (2, 500), (3, 3840), (4, 960), (5, -1260), (6, 175), (7, 480), (8, 960), (9, -20), (12, 960), (13, 2880), (24, -480), (26, 800), (27, 120), (31, -480), (33, -960), (35, 2080), (39, 1440), (42, 1440), (51, -960), (52, 2080), (54, -960), (55, -480), (56, -2400), (68, 60), (69, 80), (71, 320), (82, 640), (99, 1440), (123, -480), (124, -240), (126, -480), (128, 640), (197, -480), (199, -480), (201, -960), (237, -480), (259, -480), (262, -960), (286, 720), (288, 1440), (306, -960), (308, -480), (309, -240), (312, 720), (315, 1440), (328, 1440), (329, 1440), (500, 2880), (506, 1440), (721, -720), (728, -240), (764, 1440), (796, -720), (798, 2880)]

def boundaryRow410 : Integer.Sparse (Fin 909) := [(0, -2), (1, 11), (2, 115), (3, 424), (4, 64), (5, -170), (6, 8), (7, 384), (8, 296), (12, 32), (13, 40), (25, -24), (26, 104), (31, -48), (33, -72), (34, 16), (35, 232), (39, 72), (51, -48), (52, 80), (54, -48), (59, -48), (64, -48), (67, 40), (74, 72), (81, -240), (85, 144), (86, 144), (100, 72), (107, 144), (199, -24), (228, -48), (238, -72), (271, -48), (307, -72), (319, 144), (326, 144), (425, 72), (426, 72), (428, 144), (500, 144)]

def boundaryRow412 : Integer.Sparse (Fin 909) := [(0, -6), (1, 72), (2, 193), (3, 624), (4, 80), (5, -340), (6, 31), (7, 448), (8, 384), (11, 32), (12, 16), (13, 64), (26, 176), (33, -96), (35, 384), (52, 368), (59, -48), (67, 32), (75, 144), (81, -288), (85, 432), (86, 288), (128, 16), (201, -48), (228, -288), (428, 288), (517, 144), (760, 144), (855, 144)]

def boundaryRow419 : Integer.Sparse (Fin 909) := [(0, 27), (1, -905), (2, 610), (3, 2960), (4, 2000), (5, -400), (6, 20), (7, 240), (8, 560), (9, -20), (12, 560), (23, -240), (24, -1680), (26, 160), (27, 900), (31, -2400), (47, 720), (51, -5040), (52, 400), (56, -960), (68, 180), (69, 80), (71, 80), (124, -240), (126, -1440), (205, 720), (207, 1440), (209, 1440), (238, -960), (262, -480), (308, -240), (309, -240), (538, 720), (751, 720), (753, 1440)]

def boundaryRow422 : Integer.Sparse (Fin 909) := [(0, 33), (1, -685), (2, 305), (3, 6480), (4, 2720), (5, -380), (6, 45), (7, 1120), (8, 80), (12, 400), (13, 400), (24, -240), (26, 3360), (31, -720), (33, -480), (34, 640), (35, 2000), (44, 1440), (52, 1040), (67, 640), (81, -960), (95, 720), (99, 1440), (119, 1440), (453, 1440), (460, 1440)]

def boundaryRow423 : Integer.Sparse (Fin 909) := [(0, -3), (1, -39), (2, 91), (3, 768), (4, 192), (5, -68), (6, 5), (7, 144), (8, 64), (12, 176), (13, 176), (25, -192), (26, 256), (31, -144), (33, -672), (34, 64), (35, 224), (43, 288), (51, -48), (52, 160), (59, -192), (64, -144), (67, 64), (81, -192), (95, 144), (103, 288), (104, 288), (110, 144), (112, 288), (201, -48), (307, -144), (425, 144), (428, 288), (472, 288)]

def boundaryRow425 : Integer.Sparse (Fin 909) := [(0, -11), (1, -790), (2, 850), (3, 5920), (4, 1280), (5, -520), (6, 35), (7, 640), (8, 320), (9, -20), (12, 2000), (13, 1440), (23, -1200), (25, -2880), (26, 480), (27, 720), (31, -3840), (33, -3840), (35, 400), (51, -5760), (52, 800), (54, -960), (55, -2160), (64, -2880), (68, 180), (69, 80), (70, 80), (124, -240), (125, -960), (126, -480), (140, 720), (142, 2880), (145, 1440), (238, -1920), (260, -480), (309, -480), (383, 1440), (538, 1440)]

def boundaryRow430 : Integer.Sparse (Fin 909) := [(0, -21), (1, 80), (2, 365), (3, 4080), (5, -900), (6, 170), (7, 560), (9, -60), (12, 1200), (13, 4160), (23, -960), (25, -960), (27, 240), (31, -960), (33, -1920), (35, 1760), (52, 2240), (54, -1440), (63, -2640), (68, 180), (69, 240), (70, 160), (123, -960), (124, -240), (125, -480), (126, -480), (129, 720), (144, 1440), (196, -720), (231, 1440), (237, -1920), (306, -720), (498, 720), (721, -960), (723, -240), (760, 1440)]

def boundaryRow433 : Integer.Sparse (Fin 909) := [(0, -26), (1, -335), (2, 380), (3, 3600), (4, 160), (5, -320), (6, 5), (7, 1040), (8, 480), (9, -20), (10, -960), (12, 1920), (13, 1920), (23, -1200), (24, -480), (27, 660), (35, 160), (38, 720), (47, 1440), (51, -3120), (52, 80), (54, -480), (55, -1680), (59, -1200), (68, 120), (69, 160), (124, -720), (125, -480), (126, -240), (140, 1440), (205, 720), (259, -480), (308, -480), (321, 720), (538, 1440), (539, 1440), (727, -240)]

def boundaryRow434 : Integer.Sparse (Fin 909) := [(0, -9), (1, -10), (2, -35), (3, 3040), (4, 800), (5, -320), (6, 40), (7, 2240), (8, 320), (9, -20), (12, 320), (13, 80), (23, -480), (25, -2160), (26, 1440), (33, -480), (35, 960), (38, 720), (51, -480), (52, 160), (54, -2640), (64, -960), (69, 240), (97, 2880), (124, -480), (228, -960), (260, -480), (321, 720), (383, 1440), (492, -240)]

def boundaryRow436 : Integer.Sparse (Fin 909) := [(0, 6), (1, -240), (2, 565), (3, 4160), (4, 1680), (5, -480), (6, 35), (7, 800), (8, 880), (9, -20), (24, -240), (26, 1520), (27, 60), (31, -480), (35, 320), (37, 720), (46, 1440), (51, -1440), (52, 800), (56, -1680), (69, 160), (71, 80), (81, -1200), (107, 1440), (124, -240), (126, -240), (228, -960), (262, -480), (501, 720), (735, 1440), (745, 1440), (753, 1440), (796, -240)]

def boundaryRow444 : Integer.Sparse (Fin 909) := [(0, 1), (1, -490), (2, 640), (3, 3520), (4, 720), (5, -740), (6, 65), (7, 880), (8, 1120), (9, -40), (10, -480), (11, 80), (12, 800), (13, 720), (23, -480), (24, -240), (26, 480), (27, 420), (30, -240), (31, -720), (35, 560), (40, 720), (43, 720), (51, -2160), (52, 800), (55, -1200), (68, 120), (69, 160), (71, 240), (95, 1440), (125, -480), (126, -960), (146, 1440), (208, 720), (236, -480), (237, -240), (238, -240), (308, -240), (508, 720), (538, 720), (546, 720), (727, -240), (738, 720)]

def boundaryRow445 : Integer.Sparse (Fin 909) := [(0, -14), (1, -145), (2, 360), (3, 4400), (4, 640), (5, -760), (6, 115), (7, 1120), (8, 240), (9, -20), (12, 560), (13, 2640), (25, -240), (26, 1360), (34, 560), (35, 2320), (39, 720), (52, 2480), (54, -1440), (60, 560), (64, -480), (69, 160), (71, 80), (82, 80), (99, 1440), (103, 1440), (116, 720), (126, -480), (128, 400), (228, -480), (260, -480), (329, 720), (392, 720), (400, 1440), (492, -240)]

def boundaryRow446 : Integer.Sparse (Fin 909) := [(0, 3), (1, -80), (2, 51), (3, 608), (4, 232), (5, -60), (6, 6), (7, 80), (8, 72), (11, 24), (12, 64), (13, 64), (26, 240), (27, 6), (31, -72), (35, 144), (43, 72), (45, 72), (51, -120), (52, 64), (56, -96), (57, 72), (81, -48), (107, 216), (204, 144), (228, -48), (237, -24), (238, -72), (546, 72), (745, 144), (855, 72), (870, 72)]

def boundaryRow447 : Integer.Sparse (Fin 909) := [(0, -29), (1, -5), (2, 660), (3, 5920), (4, 560), (5, -800), (6, 110), (7, 480), (8, 240), (12, 1840), (13, 5520), (26, 880), (33, -480), (34, 640), (35, 2320), (42, 720), (51, -240), (52, 3120), (59, -960), (60, 640), (82, 240), (98, 1440), (99, 720), (102, 1440), (103, 720), (116, 720), (120, 720), (128, 800), (201, -480), (237, -240), (328, 720), (392, 720), (398, 1440), (399, 720)]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryRow448 : Integer.Sparse (Fin 909) := [(0, -36), (1, 35), (2, 615), (3, 3440), (5, -860), (6, 100), (7, 560), (8, 800), (9, -20), (12, 1200), (13, 3360), (33, -960), (35, 640), (38, 720), (51, -1440), (52, 1840), (54, -1200), (59, -1440), (69, 80), (71, 160), (82, 160), (102, 1440), (126, -480), (128, 400), (199, -480), (237, -480), (259, -480), (539, 1440), (540, 720), (721, -480), (723, -240), (739, 1440)]

def boundaryRow454 : Integer.Sparse (Fin 909) := [(0, -18), (1, -455), (2, 160), (3, 7200), (4, 1520), (5, -260), (6, 45), (11, 80), (12, 1280), (13, 3680), (26, 3120), (34, 2400), (35, 1920), (41, 720), (52, 880), (55, -480), (56, -720), (60, 720), (82, 80), (128, 160), (139, 1440), (190, 1440), (204, 1440), (238, -480), (324, 720), (398, 1440)]

def boundaryRow455 : Integer.Sparse (Fin 909) := [(0, -38), (1, -205), (2, 240), (3, 5840), (4, 160), (5, -560), (6, 75), (7, 640), (8, 160), (9, -20), (12, 1360), (13, 4160), (23, -240), (26, 2240), (27, 180), (34, 1920), (35, 2320), (38, 720), (51, -1440), (52, 1280), (54, -480), (55, -1200), (60, 560), (64, -1440), (68, 120), (70, 80), (71, 80), (82, 320), (125, -480), (128, 400), (138, 1440), (139, 1440), (146, 720), (197, -720), (236, -240), (238, -960), (260, -480), (309, -480), (323, 720), (400, 1440), (728, -240), (810, 1440)]

def boundaryRow460 : Integer.Sparse (Fin 909) := [(0, -3), (1, -280), (2, 45), (3, 3440), (4, 1000), (5, -210), (6, 30), (7, 280), (8, 120), (11, 160), (12, 80), (13, 800), (26, 2200), (34, 960), (35, 1240), (51, -120), (52, 200), (53, 360), (55, -360), (56, -480), (64, -720), (67, 360), (107, 360), (139, 720), (190, 720), (228, -120), (238, -480), (453, 720), (546, 360), (702, 360), (870, 360)]

def boundaryRow461 : Integer.Sparse (Fin 909) := [(0, -22), (1, -190), (2, 355), (3, 5680), (4, 800), (5, -620), (6, 95), (7, 1280), (8, 240), (9, -40), (11, 80), (12, 480), (13, 2400), (24, -240), (26, 3040), (27, 120), (31, -240), (33, -480), (34, 1520), (35, 2400), (37, 720), (51, -1440), (52, 1120), (55, -960), (64, -2400), (67, 560), (68, 120), (69, 160), (70, 240), (125, -1200), (126, -240), (138, 1440), (139, 1440), (146, 720), (197, -480), (204, 720), (237, -240), (238, -1200), (307, -480), (309, -240), (472, 1440), (503, 720), (543, 720), (546, 720), (727, -240), (736, 720)]

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

def boundaryRow36 : Integer.Sparse (Fin 909) := [(0, 19), (1, -288), (2, 91), (3, 928), (4, 512), (5, -12), (7, 16), (8, 32), (12, 48), (13, 32), (26, 368), (37, 144), (40, 288), (56, -144), (57, 288)]

def boundaryRow37 : Integer.Sparse (Fin 909) := [(0, 37), (1, -580), (2, 255), (3, 1920), (4, 320), (5, -80), (7, 80), (8, 320), (12, 720), (13, 880), (23, -120), (26, 160), (27, 90), (30, -240), (38, 360), (40, 720), (51, -480), (54, -240), (55, -360)]

def boundaryRow38 : Integer.Sparse (Fin 909) := [(0, 16), (1, -255), (2, 93), (3, 896), (4, 304), (12, 384), (13, 448), (26, 112), (31, -192), (33, -192), (41, 144), (42, 288)]

def boundaryRow40 : Integer.Sparse (Fin 909) := [(0, 9), (1, -179), (2, 82), (3, 720), (4, 288), (5, -32), (7, 64), (8, 96), (12, 160), (13, 128), (24, -96), (26, 176), (27, 36), (30, -48), (31, -96), (33, -192), (37, 144), (39, 144), (40, 144), (42, 144), (51, -192), (55, -144), (56, -96)]

def boundaryRow41 : Integer.Sparse (Fin 909) := [(0, 1), (1, -145), (2, 70), (3, 1200), (4, 400), (5, -10), (7, 80), (12, 720), (14, 360), (15, 1440), (23, -840), (24, -480), (25, -840), (27, 120), (33, -480), (36, 720), (48, 720), (51, -240), (54, -240), (55, -240)]

def boundaryRow42 : Integer.Sparse (Fin 909) := [(0, 83), (1, -1010), (2, 145), (3, 5280), (4, 1920), (12, 1760), (13, 720), (15, 1440), (16, 720), (18, 2880), (23, -480), (24, -480), (25, -720), (27, 60), (38, 1440), (50, 720), (55, -480)]

def boundaryRow43 : Integer.Sparse (Fin 909) := [(0, 88), (1, -1245), (2, 255), (3, 4080), (4, 1760), (5, -20), (7, 80), (8, 80), (12, 880), (15, 720), (18, 720), (19, 1440), (21, 1440), (23, -240), (24, -1440), (25, -240), (26, 480), (27, 180), (31, -960), (37, 1440), (47, 720), (48, 720), (51, -480), (56, -480)]

def boundaryRow44 : Integer.Sparse (Fin 909) := [(0, 79), (1, -810), (2, 195), (3, 1040), (4, 1320), (5, -20), (7, 80), (8, 120), (12, 160), (17, 360), (20, 720), (23, -120), (24, -600), (25, -360), (26, 80), (27, 90), (30, -360), (31, -720), (44, 720), (45, 720), (48, 360), (51, -120)]

def boundaryRow45 : Integer.Sparse (Fin 909) := [(0, 1), (1, -25), (2, -25), (9, -100), (58, 5)]

def boundaryRow46 : Integer.Sparse (Fin 909) := [(0, 1), (1, -24), (2, 36), (5, -120), (6, 15), (9, -16), (27, 180), (68, 240)]

def boundaryRow47 : Integer.Sparse (Fin 909) := [(0, 1), (1, -25), (2, -150), (3, -240), (5, 320), (6, -30), (7, -480), (8, -480), (9, 40), (35, -160), (69, -240), (70, -80), (71, -480)]

def boundaryRow48 : Integer.Sparse (Fin 909) := [(0, -1), (1, 55), (2, -10), (3, -480), (5, -20), (7, -480), (9, 20), (12, -320), (13, -160), (23, 720), (35, -320), (69, -320), (70, -160), (124, 720), (125, 480)]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryRow49 : Integer.Sparse (Fin 909) := [(0, -9), (1, 135), (2, -160), (3, -1280), (4, -480), (5, 260), (6, -30), (7, -720), (8, -240), (9, 20), (24, 720), (26, -480), (35, -640), (52, -480), (69, -240), (70, -160), (71, -80), (126, 720), (197, 480)]

def boundaryRow50 : Integer.Sparse (Fin 909) := [(0, 3), (1, 105), (2, -90), (3, -1440), (5, 210), (6, -30), (7, -480), (9, 10), (12, -600), (13, -1240), (23, 360), (35, -720), (52, -480), (54, 720), (69, -120), (70, -120), (125, 360), (196, 240)]

def boundaryRow51 : Integer.Sparse (Fin 909) := [(0, -4), (1, 45), (2, -230), (3, -640), (4, -160), (5, 280), (6, -15), (7, -480), (8, -480), (9, 20), (24, 480), (27, -60), (51, 480), (52, -160), (69, -160), (71, -320), (124, 240), (126, 960)]

def boundaryRow52 : Integer.Sparse (Fin 909) := [(0, -14), (1, 65), (2, -250), (3, -320), (5, 440), (6, -45), (7, -160), (8, -800), (9, 20), (27, -60), (30, 480), (52, -160), (69, -80), (71, -400), (126, 240), (236, 960)]

def boundaryRow53 : Integer.Sparse (Fin 909) := [(0, -2), (1, 95), (2, -60), (3, -880), (4, -320), (5, 460), (6, -65), (7, -160), (8, -480), (9, 20), (13, -400), (24, 480), (26, -320), (35, -400), (52, -320), (55, 240), (56, 960), (69, -80), (70, -80), (71, -320), (125, 240), (197, 960)]

def boundaryRow54 : Integer.Sparse (Fin 909) := [(0, -1), (1, 35), (2, -140), (3, -480), (5, 265), (6, -15), (7, -600), (8, -480), (10, 180), (12, -120), (13, -160), (35, -320), (82, -60)]

def boundaryRow55 : Integer.Sparse (Fin 909) := [(0, -1), (1, 10), (2, -205), (3, -1200), (4, -240), (5, 680), (6, -90), (7, -480), (8, -480), (11, -240), (26, -480), (35, -1120), (52, -1200), (228, 720)]

def boundaryRow56 : Integer.Sparse (Fin 909) := [(0, 1), (1, -30), (2, -50), (3, -160), (5, 90), (6, -15), (7, -40), (8, -80), (12, -20), (13, -160), (35, -160), (52, -320), (82, -120), (128, -160), (199, 60), (201, 240)]

def boundaryRow57 : Integer.Sparse (Fin 909) := [(0, -1), (1, -10), (2, -5), (3, -480), (5, 10), (7, -240), (10, 360), (12, -240), (13, -640), (35, -320), (82, -120), (127, 360), (128, -120)]

def boundaryRow58 : Integer.Sparse (Fin 909) := [(0, -9), (1, 525), (2, 90), (3, -3360), (4, -1200), (5, 140), (6, -30), (7, -240), (11, -240), (12, -960), (13, -1680), (25, 720), (26, -1440), (35, -1520), (52, -240), (54, 2160), (56, 1440), (226, 480), (228, 720)]

def boundaryRow59 : Integer.Sparse (Fin 909) := [(0, -19), (1, 270), (2, -105), (3, -1360), (4, -560), (5, 240), (6, -40), (11, -80), (26, -640), (27, -120), (31, 480), (35, -480), (52, -400), (55, 480), (228, 240), (237, 480), (238, 480)]

def boundaryRow60 : Integer.Sparse (Fin 909) := [(1, 35), (2, -13), (3, -400), (4, -64), (5, 44), (6, -8), (7, -48), (12, -144), (13, -368), (26, -64), (35, -208), (52, -128), (54, 144), (56, 96), (82, -64), (128, -64), (199, 48), (201, 96)]

def boundaryRow64 : Integer.Sparse (Fin 909) := [(0, 7), (1, -140), (2, -465), (3, -1680), (5, 1240), (6, -160), (7, -960), (8, -960), (12, -240), (13, -1120), (35, -1520), (52, -1920), (59, 720), (60, -320), (128, -240)]

def boundaryRow65 : Integer.Sparse (Fin 909) := [(0, 1), (1, -5), (2, -120), (3, -480), (4, -80), (5, 240), (6, -20), (7, -480), (8, -320), (26, -160), (35, -400), (52, -160), (67, -80), (81, 240)]

def boundaryRow66 : Integer.Sparse (Fin 909) := [(0, 12), (1, 50), (2, -15), (3, -1760), (5, 20), (6, -5), (12, -720), (13, -2000), (26, -560), (32, -160), (33, 720), (34, -480), (35, -240), (55, 720), (60, -160), (61, 480)]

def boundaryRow67 : Integer.Sparse (Fin 909) := [(0, 2), (1, 6), (2, -5), (3, -256), (5, 8), (6, -1), (12, -96), (13, -224), (25, 48), (26, -64), (33, 192), (34, -32), (35, -32), (52, -32), (55, 96), (63, 48), (64, 96)]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryRow68 : Integer.Sparse (Fin 909) := [(0, 8), (1, 40), (2, -15), (3, -1120), (5, 60), (6, -15), (7, -160), (12, -320), (13, -800), (23, 240), (26, -480), (33, 480), (34, -320), (35, -480), (54, 480), (55, 480), (63, 240), (65, 480), (67, -160)]

def boundaryRow69 : Integer.Sparse (Fin 909) := [(0, -2), (1, 67), (2, -13), (3, -528), (4, -224), (5, 16), (6, -2), (7, -16), (8, -16), (12, -16), (13, -80), (24, 48), (26, -336), (33, 48), (34, -112), (35, -64), (52, -16), (55, 144), (56, 96), (64, 48), (66, 96), (67, -32)]

def boundaryRow70 : Integer.Sparse (Fin 909) := [(0, 9), (1, -5), (2, -65), (3, -1440), (5, 60), (6, -5), (12, -720), (13, -2640), (26, -240), (32, -320), (34, -480), (35, -240), (52, -480), (59, 720), (60, -400), (61, 720), (128, -240)]

def boundaryRow71 : Integer.Sparse (Fin 909) := [(0, 1), (2, -7), (3, -144), (5, 14), (6, -2), (7, -24), (12, -48), (13, -160), (26, -24), (32, -16), (33, 72), (35, -72), (52, -48), (54, 72), (60, -16), (62, 48)]

def boundaryRow72 : Integer.Sparse (Fin 909) := [(0, -16), (1, 485), (2, -240), (3, -3440), (4, -1280), (5, 120), (6, -5), (7, -480), (8, -160), (12, -320), (13, -320), (25, 240), (26, -1600), (31, 480), (33, 960), (34, -400), (35, -560), (51, 480), (52, -240), (64, 240), (67, -160), (81, 480), (123, 480)]

def boundaryRow73 : Integer.Sparse (Fin 909) := [(1, 42), (2, -35), (3, -448), (4, -64), (5, 44), (6, -5), (7, -112), (8, -32), (12, -128), (13, -272), (26, -160), (34, -80), (35, -160), (51, 96), (52, -112), (54, 48), (64, 48), (67, -32)]

def boundaryRow74 : Integer.Sparse (Fin 909) := [(0, -9), (1, 345), (2, -120), (3, -2560), (4, -880), (7, -80), (12, -800), (13, -480), (23, 240), (25, 720), (26, -880), (31, 480), (33, 1440), (34, -320), (35, -160), (54, 480), (65, 240), (67, -80), (81, 240), (195, -480)]

def boundaryRow75 : Integer.Sparse (Fin 909) := [(0, 1), (1, 65), (2, -40), (3, -620), (4, -140), (5, 5), (12, -260), (13, -340), (25, 60), (26, -100), (27, -15), (31, 120), (33, 360), (34, -80), (35, -20), (51, 180), (52, -60), (55, 60), (59, 120), (60, -20), (61, 60), (128, -20), (194, -120)]

def boundaryRow77 : Integer.Sparse (Fin 909) := [(0, 5), (1, -73), (2, 44), (3, 160), (4, 64), (5, -15), (7, 20), (8, 40), (10, -36), (12, 56), (13, 32), (23, -120), (24, -336), (27, 123), (30, -192), (55, -192), (79, 36), (80, 72)]

def boundaryRow78 : Integer.Sparse (Fin 909) := [(0, 17), (1, -570), (2, 730), (3, 3040), (4, 1040), (5, -620), (6, 15), (7, 1120), (8, 1760), (12, 400), (23, -480), (24, -1440), (26, 480), (27, 600), (30, -960), (35, 160), (51, -3600), (54, -960), (55, -480), (56, -1920), (77, 720), (78, 1440), (228, -720)]

def boundaryRow79 : Integer.Sparse (Fin 909) := [(0, -3), (1, 20), (2, 240), (3, 560), (5, -350), (6, 20), (7, 600), (8, 520), (10, -180), (12, 180), (13, 240), (23, -60), (27, 45), (30, -120), (35, 240), (51, -480), (52, 160), (54, -240), (59, -480), (72, 180), (74, 360), (75, 360), (199, -180)]

def boundaryRow80 : Integer.Sparse (Fin 909) := [(0, -14), (1, 260), (2, 1255), (3, 3120), (4, 400), (5, -2280), (6, 205), (7, 3040), (8, 2720), (26, 480), (35, 2240), (52, 2320), (81, -960), (84, 720), (85, 1440), (86, 1440), (228, -720)]

def boundaryRow81 : Integer.Sparse (Fin 909) := [(0, -17), (1, 80), (2, 990), (3, 2880), (4, 320), (5, -1580), (6, 95), (7, 2800), (8, 2640), (10, -720), (12, 400), (13, 640), (24, -480), (27, 180), (30, -240), (35, 1440), (51, -1920), (52, 640), (56, -960), (59, -1920), (73, 720), (74, 720), (75, 720), (76, 1440), (201, -720)]

def boundaryRow82 : Integer.Sparse (Fin 909) := [(0, -17), (1, 280), (2, 1440), (3, 3840), (5, -2160), (6, 185), (7, 2480), (8, 2400), (12, 480), (13, 640), (35, 2400), (52, 3200), (73, 720), (75, 1440), (81, -960), (86, 2880), (201, -720)]

def boundaryRow83 : Integer.Sparse (Fin 909) := [(0, -3), (1, 10), (2, 950), (3, 3360), (4, 720), (5, -1240), (6, 95), (7, 1520), (8, 1600), (26, 960), (35, 960), (52, 1280), (81, -1920), (83, 720), (85, 2880), (86, 1440), (228, -1440)]

def boundaryRow84 : Integer.Sparse (Fin 909) := [(0, 13), (1, -580), (2, 285), (3, 4800), (4, 800), (5, -100), (7, 560), (8, 160), (10, -240), (12, 1920), (13, 1520), (23, -1920), (24, -1440), (25, -240), (27, 420), (47, 2880), (48, 1440), (50, 720), (51, -1440), (55, -960), (59, -480), (79, 720), (94, 1440)]

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

def boundaryRow85 : Integer.Sparse (Fin 909) := [(0, 8), (1, -124), (2, 37), (3, 800), (4, 352), (5, -12), (6, 1), (7, 64), (12, 592), (13, 80), (23, -96), (25, -384), (26, 128), (33, -96), (35, 64), (43, 576), (50, 144), (52, 32), (55, -96), (104, 288), (113, 144)]

def boundaryRow87 : Integer.Sparse (Fin 909) := [(0, 64), (1, -710), (2, 515), (3, 3760), (4, 1760), (5, -260), (6, 5), (7, 480), (8, 800), (12, 240), (23, -240), (24, -480), (26, 880), (27, 60), (31, -1680), (43, 720), (46, 1440), (51, -1440), (52, 80), (56, -960), (77, 720), (81, -480), (106, 1440), (107, 1440), (122, 1440), (228, -240)]

end MUB6.Certificate.PairSemantics

end OAI
end


