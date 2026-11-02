-- Prove2me | Definitions.Def_OAIQ106D063
-- name    : OAIQ106D063
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T12:28:56.705642+00:00
-- url     : https://prove2.me/theorems/dc08bfe4-bb36-4a4f-985c-04e42dc92e07
-- title:
--   Definitions bundle OAIQ106D063 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1920 declarations of OpenAI's Lean: 1920 definitions. The definitions and types are `OAI.MUB6.Certificate.PairSemantics.raw6896step0`, `OAI.MUB6.Certificate.PairSemantics.raw6896step1`, `OAI.MUB6.Certificate.PairSemantics.raw6896step2`, `OAI.MUB6.Certificate.PairSemantics.raw6897`, `OAI.MUB6.Certificate.PairSemantics.raw6897step0`, `OAI.MUB6.Certificate.PairSemantics.raw6897step1`, `OAI.MUB6.Certificate.PairSemantics.raw6897step2`, `OAI.MUB6.Certificate.PairSemantics.raw6898`, `OAI.MUB6.Certificate.PairSemantics.raw6898step0`, `OAI.MUB6.Certificate.PairSemantics.raw6898step1`, `OAI.MUB6.Certificate.PairSemantics.raw6898step2`, `OAI.MUB6.Certificate.PairSemantics.raw6899`, `OAI.MUB6.Certificate.PairSemantics.raw6899step0`, `OAI.MUB6.Certificate.PairSemantics.raw6899step1`, `OAI.MUB6.Certificate.PairSemantics.raw6899step2`, `OAI.MUB6.Certificate.PairSemantics.raw69`, `OAI.MUB6.Certificate.PairSemantics.raw690`, `OAI.MUB6.Certificate.PairSemantics.raw6900`, `OAI.MUB6.Certificate.PairSemantics.raw6900step0`, `OAI.MUB6.Certificate.PairSemantics.raw6900step1`, `OAI.MUB6.Certificate.PairSemantics.raw6900step2`, `OAI.MUB6.Certificate.PairSemantics.raw6901`, `OAI.MUB6.Certificate.PairSemantics.raw6901step0`, `OAI.MUB6.Certificate.PairSemantics.raw6901step1`, `OAI.MUB6.Certificate.PairSemantics.raw6901step2`, `OAI.MUB6.Certificate.PairSemantics.raw6902`, `OAI.MUB6.Certificate.PairSemantics.raw6902step0`, `OAI.MUB6.Certificate.PairSemantics.raw6902step1`, `OAI.MUB6.Certificate.PairSemantics.raw6902step2`, `OAI.MUB6.Certificate.PairSemantics.raw6903`, `OAI.MUB6.Certificate.PairSemantics.raw6903step0`, `OAI.MUB6.Certificate.PairSemantics.raw6903step1`, `OAI.MUB6.Certificate.PairSemantics.raw6903step2`, `OAI.MUB6.Certificate.PairSemantics.raw6904`, `OAI.MUB6.Certificate.PairSemantics.raw6904step0`, `OAI.MUB6.Certificate.PairSemantics.raw6904step1`, `OAI.MUB6.Certificate.PairSemantics.raw6904step2`, `OAI.MUB6.Certificate.PairSemantics.raw6905`, `OAI.MUB6.Certificate.PairSemantics.raw6905step0`, `OAI.MUB6.Certificate.PairSemantics.raw6905step1` and 1880 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_PairSemantics_Canonical0`, `MutuallyUnbiased_PairSemantics_Canonical2`, `MutuallyUnbiased_PairSemantics_Canonical21`, `MutuallyUnbiased_PairSemantics_Canonical215`, `MutuallyUnbiased_PairSemantics_Canonical216`, `MutuallyUnbiased_PairSemantics_Canonical217`, `MutuallyUnbiased_PairSemantics_Canonical218`, `MutuallyUnbiased_PairSemantics_Canonical219`, `MutuallyUnbiased_PairSemantics_Canonical22`, `MutuallyUnbiased_PairSemantics_Canonical220`, `MutuallyUnbiased_PairSemantics_Canonical221`, `MutuallyUnbiased_PairSemantics_Canonical222`, `MutuallyUnbiased_PairSemantics_Canonical223`, `MutuallyUnbiased_PairSemantics_Canonical224`, `MutuallyUnbiased_PairSemantics_Canonical225`, `MutuallyUnbiased_PairSemantics_Canonical226`, `MutuallyUnbiased_PairSemantics_Canonical227`, `MutuallyUnbiased_PairSemantics_Canonical228`, `MutuallyUnbiased_PairSemantics_Canonical229`, `MutuallyUnbiased_PairSemantics_Canonical23`, `MutuallyUnbiased_PairSemantics_Canonical230`, `MutuallyUnbiased_PairSemantics_Canonical231`, `MutuallyUnbiased_PairSemantics_Canonical232`, `MutuallyUnbiased_PairSemantics_Canonical233`, `MutuallyUnbiased_PairSemantics_Canonical234`, `MutuallyUnbiased_PairSemantics_Canonical235`, `MutuallyUnbiased_PairSemantics_Canonical236`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1162`, `OAI.MUB6.Certificate.MixedSemantics.sound1164`, `OAI.MUB6.Certificate.MixedSemantics.sound1265`, `OAI.MUB6.Certificate.MixedSemantics.sound1299`, `OAI.MUB6.Certificate.MixedSemantics.sound1339`, `OAI.MUB6.Certificate.MixedSemantics.sound1343`, `OAI.MUB6.Certificate.MixedSemantics.sound1409`, `OAI.MUB6.Certificate.MixedSemantics.sound1412`, `OAI.MUB6.Certificate.MixedSemantics.sound1417`, `OAI.MUB6.Certificate.MixedSemantics.sound1477`, `OAI.MUB6.Certificate.MixedSemantics.sound171`, `OAI.MUB6.Certificate.MixedSemantics.sound174`, `OAI.MUB6.Certificate.MixedSemantics.sound207`, `OAI.MUB6.Certificate.MixedSemantics.sound2530`, `OAI.MUB6.Certificate.MixedSemantics.sound2593`, `OAI.MUB6.Certificate.MixedSemantics.sound2595`, `OAI.MUB6.Certificate.MixedSemantics.sound2599`, `OAI.MUB6.Certificate.MixedSemantics.sound2766`, `OAI.MUB6.Certificate.MixedSemantics.sound2904`, `OAI.MUB6.Certificate.MixedSemantics.sound293`, `OAI.MUB6.Certificate.MixedSemantics.sound294`, `OAI.MUB6.Certificate.MixedSemantics.sound2957`, `OAI.MUB6.Certificate.MixedSemantics.sound2958`, `OAI.MUB6.Certificate.MixedSemantics.sound2959`, `OAI.MUB6.Certificate.MixedSemantics.sound2960`, `OAI.MUB6.Certificate.MixedSemantics.sound2961`, `OAI.MUB6.Certificate.MixedSemantics.sound2988`, `OAI.MUB6.Certificate.MixedSemantics.sound2990`, `OAI.MUB6.Certificate.MixedSemantics.sound2996`, `OAI.MUB6.Certificate.MixedSemantics.sound3082`, `OAI.MUB6.Certificate.MixedSemantics.sound3087`, `OAI.MUB6.Certificate.MixedSemantics.sound3088`, `OAI.MUB6.Certificate.MixedSemantics.sound3089`, `OAI.MUB6.Certificate.MixedSemantics.sound3090`, `OAI.MUB6.Certificate.MixedSemantics.sound3093`, `OAI.MUB6.Certificate.MixedSemantics.sound3094`, `OAI.MUB6.Certificate.MixedSemantics.sound3099`, `OAI.MUB6.Certificate.MixedSemantics.sound3100`, `OAI.MUB6.Certificate.MixedSemantics.sound3106`, `OAI.MUB6.Certificate.MixedSemantics.sound3109`, `OAI.MUB6.Certificate.MixedSemantics.sound3110`, `OAI.MUB6.Certificate.MixedSemantics.sound3116`, `OAI.MUB6.Certificate.MixedSemantics.sound3143`, `OAI.MUB6.Certificate.MixedSemantics.sound3144`, `OAI.MUB6.Certificate.MixedSemantics.sound3178`, `OAI.MUB6.Certificate.MixedSemantics.sound3185`, `OAI.MUB6.Certificate.MixedSemantics.sound3190`, `OAI.MUB6.Certificate.MixedSemantics.sound3206`, `OAI.MUB6.Certificate.MixedSemantics.sound3210`, `OAI.MUB6.Certificate.MixedSemantics.sound3226`, `OAI.MUB6.Certificate.MixedSemantics.sound370`, `OAI.MUB6.Certificate.MixedSemantics.sound371`, `OAI.MUB6.Certificate.MixedSemantics.sound3711`, `OAI.MUB6.Certificate.MixedSemantics.sound3726`, `OAI.MUB6.Certificate.MixedSemantics.sound3727`, `OAI.MUB6.Certificate.MixedSemantics.sound3735`, `OAI.MUB6.Certificate.MixedSemantics.sound3818`, `OAI.MUB6.Certificate.MixedSemantics.sound3821`, `OAI.MUB6.Certificate.MixedSemantics.sound3823`, `OAI.MUB6.Certificate.MixedSemantics.sound3829`, `OAI.MUB6.Certificate.MixedSemantics.sound3847`, `OAI.MUB6.Certificate.MixedSemantics.sound3851`, `OAI.MUB6.Certificate.MixedSemantics.sound3853`, `OAI.MUB6.Certificate.MixedSemantics.sound3882`, `OAI.MUB6.Certificate.MixedSemantics.sound3887`, `OAI.MUB6.Certificate.MixedSemantics.sound3925`, `OAI.MUB6.Certificate.MixedSemantics.sound3931`, `OAI.MUB6.Certificate.MixedSemantics.sound3936`, `OAI.MUB6.Certificate.MixedSemantics.sound3937`, `OAI.MUB6.Certificate.MixedSemantics.sound3965`, `OAI.MUB6.Certificate.MixedSemantics.sound3966`, `OAI.MUB6.Certificate.MixedSemantics.sound3967`, `OAI.MUB6.Certificate.MixedSemantics.sound3977`, `OAI.MUB6.Certificate.MixedSemantics.sound3980`, `OAI.MUB6.Certificate.MixedSemantics.sound3984`, `OAI.MUB6.Certificate.MixedSemantics.sound3992`, `OAI.MUB6.Certificate.MixedSemantics.sound3993`, `OAI.MUB6.Certificate.MixedSemantics.sound3994`, `OAI.MUB6.Certificate.MixedSemantics.sound3997`, `OAI.MUB6.Certificate.MixedSemantics.sound3998`, `OAI.MUB6.Certificate.MixedSemantics.sound4002`, `OAI.MUB6.Certificate.MixedSemantics.sound4003`, `OAI.MUB6.Certificate.MixedSemantics.sound4023`, `OAI.MUB6.Certificate.MixedSemantics.sound4026`, `OAI.MUB6.Certificate.MixedSemantics.sound4027`, `OAI.MUB6.Certificate.MixedSemantics.sound4029`, `OAI.MUB6.Certificate.MixedSemantics.sound4032`, `OAI.MUB6.Certificate.MixedSemantics.sound4033`, `OAI.MUB6.Certificate.MixedSemantics.sound4039`, `OAI.MUB6.Certificate.MixedSemantics.sound4053`, `OAI.MUB6.Certificate.MixedSemantics.sound436`, `OAI.MUB6.Certificate.MixedSemantics.sound455`, `OAI.MUB6.Certificate.MixedSemantics.sound511`, `OAI.MUB6.Certificate.MixedSemantics.sound521`, `OAI.MUB6.Certificate.MixedSemantics.sound5452`, `OAI.MUB6.Certificate.MixedSemantics.sound5464`, `OAI.MUB6.Certificate.MixedSemantics.sound5492`, `OAI.MUB6.Certificate.MixedSemantics.sound5498`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound137`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound139`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound140`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound141`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound142`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound147`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound148`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound151`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1423`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero539`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound110`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1124`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1179`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound130`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1312`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1318`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound141`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound16`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1703`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1717`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1785`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1840`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1847`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1874`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound19`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1972`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2166`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2168`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2169`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2170`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2171`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2172`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2174`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2175`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2176`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2178`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2179`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2180`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2181`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2182`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2183`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2184`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2185`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2187`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2188`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2189`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2190`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2191`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2192`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2197`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2198`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2199`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2200`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2201`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2202`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2203`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2204`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2205`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2206`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2207`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2208`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2211`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2214`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2216`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2217`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2218`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2219`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2222`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2223`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2224`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2225`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2226`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2227`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2228`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2229`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2230`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2232`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2233`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2235`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2238`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2240`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2241`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2242`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2244`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2245`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2246`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2247`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2248`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2249`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2250`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2251`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2252`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2254`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2255`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2257`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2258`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2259`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2260`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2261`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2263`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2264`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2266`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2267`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2268`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2269`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2270`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2271`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2272`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2273`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2274`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2275`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2276`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2279`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2280`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2282`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2283`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2284`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2286`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2287`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2288`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2291`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2292`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2293`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2294`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2296`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2297`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2298`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2299`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2300`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2301`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2302`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2303`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2306`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2307`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2309`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2313`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2315`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2317`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2318`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2320`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2321`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2322`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2323`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2325`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2326`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2327`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2329`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2330`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2331`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2333`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2334`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2335`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2336`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2337`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2338`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2340`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2341`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2344`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2345`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2346`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2347`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2348`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2350`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2351`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2352`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2354`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2355`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2356`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2357`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2360`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2361`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2362`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2363`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2364`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2365`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2366`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2367`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2368`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2369`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2371`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2372`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2374`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2375`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2377`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2378`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2379`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2380`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2381`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2383`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2384`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2386`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2388`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2389`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2391`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2393`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2394`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2395`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2396`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2397`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2398`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2399`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2400`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2401`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2402`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2403`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2405`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2406`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2407`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2408`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2409`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2410`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2411`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2413`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2414`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2415`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2418`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2419`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2420`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2423`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2424`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound344`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound359`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound368`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound370`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound371`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound404`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound482`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound485`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound5`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound504`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound516`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound521`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound532`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound534`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound579`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound6`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound631`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound635`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound718`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound731`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound734`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound741`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound790`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound794`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound796`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound864`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound866`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound877`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound909`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound927`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound971`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval106`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval109`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1192`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval120`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1210`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval133`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval134`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval141`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval145`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval146`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval164`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval167`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval174`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval18`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval185`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval202`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval203`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval21`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval214`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval215`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval218`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval220`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval224`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval225`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval226`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval234`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval242`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval243`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval245`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval249`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval255`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval258`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval270`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval271`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval273`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval278`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval280`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval285`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval286`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval287`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval292`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval296`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval301`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval308`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval310`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval325`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval331`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval332`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval335`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval343`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval344`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval348`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval353`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval359`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval366`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval371`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval372`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval373`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval377`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval380`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval383`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval389`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval39`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval391`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval394`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval401`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval403`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval408`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval413`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval414`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval444`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval46`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval475`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval52`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval69`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval73`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval74`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval86`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval91`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval99`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval113`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval119`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval147`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval208`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval215`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval271`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval359`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval362`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval373`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval375`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval384`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval44`, `OAI.MUB6.Certificate.PairSemantics.boundarySound165`, `OAI.MUB6.Certificate.PairSemantics.boundarySound248`, `OAI.MUB6.Certificate.PairSemantics.boundarySound249`, `OAI.MUB6.Certificate.PairSemantics.boundarySound250`, `OAI.MUB6.Certificate.PairSemantics.boundarySound261`, `OAI.MUB6.Certificate.PairSemantics.boundarySound305`, `OAI.MUB6.Certificate.PairSemantics.boundarySound347`, `OAI.MUB6.Certificate.PairSemantics.boundarySound445`, `OAI.MUB6.Certificate.PairSemantics.boundarySound454`, `OAI.MUB6.Certificate.PairSemantics.boundarySound49`, `OAI.MUB6.Certificate.PairSemantics.boundarySound51`, `OAI.MUB6.Certificate.PairSemantics.boundarySound56`, `OAI.MUB6.Certificate.PairSemantics.boundarySound7`, `OAI.MUB6.Certificate.PairSemantics.boundarySound73`, `OAI.MUB6.Certificate.PairSemantics.boundarySound75`, `OAI.MUB6.Certificate.PairSemantics.boundarySound83`, `OAI.MUB6.Certificate.PairSemantics.boundarySound97`, `OAI.MUB6.Certificate.PairSemantics.sound1141`, `OAI.MUB6.Certificate.PairSemantics.sound1151`, `OAI.MUB6.Certificate.PairSemantics.sound1152`, `OAI.MUB6.Certificate.PairSemantics.sound1294`, `OAI.MUB6.Certificate.PairSemantics.sound1392`, `OAI.MUB6.Certificate.PairSemantics.sound1395`, `OAI.MUB6.Certificate.PairSemantics.sound1399`, `OAI.MUB6.Certificate.PairSemantics.sound1414`, `OAI.MUB6.Certificate.PairSemantics.sound1419`, `OAI.MUB6.Certificate.PairSemantics.sound1423`, `OAI.MUB6.Certificate.PairSemantics.sound1424`, `OAI.MUB6.Certificate.PairSemantics.sound1425`, `OAI.MUB6.Certificate.PairSemantics.sound1432`, `OAI.MUB6.Certificate.PairSemantics.sound1434`, `OAI.MUB6.Certificate.PairSemantics.sound1443`, `OAI.MUB6.Certificate.PairSemantics.sound1458`, `OAI.MUB6.Certificate.PairSemantics.sound1486`, `OAI.MUB6.Certificate.PairSemantics.sound1500`, `OAI.MUB6.Certificate.PairSemantics.sound1504`, `OAI.MUB6.Certificate.PairSemantics.sound1506`, `OAI.MUB6.Certificate.PairSemantics.sound1512`, `OAI.MUB6.Certificate.PairSemantics.sound1518`, `OAI.MUB6.Certificate.PairSemantics.sound1520`, `OAI.MUB6.Certificate.PairSemantics.sound1523`, `OAI.MUB6.Certificate.PairSemantics.sound1530`, `OAI.MUB6.Certificate.PairSemantics.sound1533`, `OAI.MUB6.Certificate.PairSemantics.sound1535`, `OAI.MUB6.Certificate.PairSemantics.sound1548`, `OAI.MUB6.Certificate.PairSemantics.sound1552`, `OAI.MUB6.Certificate.PairSemantics.sound1563`, `OAI.MUB6.Certificate.PairSemantics.sound1585`, `OAI.MUB6.Certificate.PairSemantics.sound1605`, `OAI.MUB6.Certificate.PairSemantics.sound1614`, `OAI.MUB6.Certificate.PairSemantics.sound1617`, `OAI.MUB6.Certificate.PairSemantics.sound1627`, `OAI.MUB6.Certificate.PairSemantics.sound1631`, `OAI.MUB6.Certificate.PairSemantics.sound1634`, `OAI.MUB6.Certificate.PairSemantics.sound1635`, `OAI.MUB6.Certificate.PairSemantics.sound1637`, `OAI.MUB6.Certificate.PairSemantics.sound1643`, `OAI.MUB6.Certificate.PairSemantics.sound1646`, `OAI.MUB6.Certificate.PairSemantics.sound1648`, `OAI.MUB6.Certificate.PairSemantics.sound1652`, `OAI.MUB6.Certificate.PairSemantics.sound1668`, `OAI.MUB6.Certificate.PairSemantics.sound1669`, `OAI.MUB6.Certificate.PairSemantics.sound1682`, `OAI.MUB6.Certificate.PairSemantics.sound1685`, `OAI.MUB6.Certificate.PairSemantics.sound1686`, `OAI.MUB6.Certificate.PairSemantics.sound1707`, `OAI.MUB6.Certificate.PairSemantics.sound1716`, `OAI.MUB6.Certificate.PairSemantics.sound1718`, `OAI.MUB6.Certificate.PairSemantics.sound1736`, `OAI.MUB6.Certificate.PairSemantics.sound1739`, `OAI.MUB6.Certificate.PairSemantics.sound1768`, `OAI.MUB6.Certificate.PairSemantics.sound1769`, `OAI.MUB6.Certificate.PairSemantics.sound1770`, `OAI.MUB6.Certificate.PairSemantics.sound1774`, `OAI.MUB6.Certificate.PairSemantics.sound1784`, `OAI.MUB6.Certificate.PairSemantics.sound1793`, `OAI.MUB6.Certificate.PairSemantics.sound1800`, `OAI.MUB6.Certificate.PairSemantics.sound1826`, `OAI.MUB6.Certificate.PairSemantics.sound1828`, `OAI.MUB6.Certificate.PairSemantics.sound1830`, `OAI.MUB6.Certificate.PairSemantics.sound1860`, `OAI.MUB6.Certificate.PairSemantics.sound1865`, `OAI.MUB6.Certificate.PairSemantics.sound1866`, `OAI.MUB6.Certificate.PairSemantics.sound1867`, `OAI.MUB6.Certificate.PairSemantics.sound1870`, `OAI.MUB6.Certificate.PairSemantics.sound1872`, `OAI.MUB6.Certificate.PairSemantics.sound1885`, `OAI.MUB6.Certificate.PairSemantics.sound1890`, `OAI.MUB6.Certificate.PairSemantics.sound1938`, `OAI.MUB6.Certificate.PairSemantics.sound1968`, `OAI.MUB6.Certificate.PairSemantics.sound1977`, `OAI.MUB6.Certificate.PairSemantics.sound1978`, `OAI.MUB6.Certificate.PairSemantics.sound1980`, `OAI.MUB6.Certificate.PairSemantics.sound1986`, `OAI.MUB6.Certificate.PairSemantics.sound1987`, `OAI.MUB6.Certificate.PairSemantics.sound2041`, `OAI.MUB6.Certificate.PairSemantics.sound2106`, `OAI.MUB6.Certificate.PairSemantics.sound2108`, `OAI.MUB6.Certificate.PairSemantics.sound2113`, `OAI.MUB6.Certificate.PairSemantics.sound2117`, `OAI.MUB6.Certificate.PairSemantics.sound2122`, `OAI.MUB6.Certificate.PairSemantics.sound2128`, `OAI.MUB6.Certificate.PairSemantics.sound2132`, `OAI.MUB6.Certificate.PairSemantics.sound2152`, `OAI.MUB6.Certificate.PairSemantics.sound2168`, `OAI.MUB6.Certificate.PairSemantics.sound2175`, `OAI.MUB6.Certificate.PairSemantics.sound2177`, `OAI.MUB6.Certificate.PairSemantics.sound2183`, `OAI.MUB6.Certificate.PairSemantics.sound2190`, `OAI.MUB6.Certificate.PairSemantics.sound2192`, `OAI.MUB6.Certificate.PairSemantics.sound2197`, `OAI.MUB6.Certificate.PairSemantics.sound2201`, `OAI.MUB6.Certificate.PairSemantics.sound2202`, `OAI.MUB6.Certificate.PairSemantics.sound2204`, `OAI.MUB6.Certificate.PairSemantics.sound2213`, `OAI.MUB6.Certificate.PairSemantics.sound2216`, `OAI.MUB6.Certificate.PairSemantics.sound2228`, `OAI.MUB6.Certificate.PairSemantics.sound2243`, `OAI.MUB6.Certificate.PairSemantics.sound2262`, `OAI.MUB6.Certificate.PairSemantics.sound2284`, `OAI.MUB6.Certificate.PairSemantics.sound2285`, `OAI.MUB6.Certificate.PairSemantics.sound2286`, `OAI.MUB6.Certificate.PairSemantics.sound2293`, `OAI.MUB6.Certificate.PairSemantics.sound2294`, `OAI.MUB6.Certificate.PairSemantics.sound2295`, `OAI.MUB6.Certificate.PairSemantics.sound2296`, `OAI.MUB6.Certificate.PairSemantics.sound2298`, `OAI.MUB6.Certificate.PairSemantics.sound2307`, `OAI.MUB6.Certificate.PairSemantics.sound2312`, `OAI.MUB6.Certificate.PairSemantics.sound2315`, `OAI.MUB6.Certificate.PairSemantics.sound2324`, `OAI.MUB6.Certificate.PairSemantics.sound2325`, `OAI.MUB6.Certificate.PairSemantics.sound2327`, `OAI.MUB6.Certificate.PairSemantics.sound2338`, `OAI.MUB6.Certificate.PairSemantics.sound2349`, `OAI.MUB6.Certificate.PairSemantics.sound2357`, `OAI.MUB6.Certificate.PairSemantics.sound2382`, `OAI.MUB6.Certificate.PairSemantics.sound2390`, `OAI.MUB6.Certificate.PairSemantics.sound2391`, `OAI.MUB6.Certificate.PairSemantics.sound2399`, `OAI.MUB6.Certificate.PairSemantics.sound2400`, `OAI.MUB6.Certificate.PairSemantics.sound2403`, `OAI.MUB6.Certificate.PairSemantics.sound2411`, `OAI.MUB6.Certificate.PairSemantics.sound2413`, `OAI.MUB6.Certificate.PairSemantics.sound2415`, `OAI.MUB6.Certificate.PairSemantics.sound2416`, `OAI.MUB6.Certificate.PairSemantics.sound2420`, `OAI.MUB6.Certificate.PairSemantics.sound2428`, `OAI.MUB6.Certificate.PairSemantics.sound2433`, `OAI.MUB6.Certificate.PairSemantics.sound2434`, `OAI.MUB6.Certificate.PairSemantics.sound2435`, `OAI.MUB6.Certificate.PairSemantics.sound2436`, `OAI.MUB6.Certificate.PairSemantics.sound2440`, `OAI.MUB6.Certificate.PairSemantics.sound2441`, `OAI.MUB6.Certificate.PairSemantics.sound2442`, `OAI.MUB6.Certificate.PairSemantics.sound2443`, `OAI.MUB6.Certificate.PairSemantics.sound2444`, `OAI.MUB6.Certificate.PairSemantics.sound2445`, `OAI.MUB6.Certificate.PairSemantics.sound2455`, `OAI.MUB6.Certificate.PairSemantics.sound2462`, `OAI.MUB6.Certificate.PairSemantics.sound2463`, `OAI.MUB6.Certificate.PairSemantics.sound2464`, `OAI.MUB6.Certificate.PairSemantics.sound2466`, `OAI.MUB6.Certificate.PairSemantics.sound2470`, `OAI.MUB6.Certificate.PairSemantics.sound2472`, `OAI.MUB6.Certificate.PairSemantics.sound2477`, `OAI.MUB6.Certificate.PairSemantics.sound2479`, `OAI.MUB6.Certificate.PairSemantics.sound2486`, `OAI.MUB6.Certificate.PairSemantics.sound2489`, `OAI.MUB6.Certificate.PairSemantics.sound2490`, `OAI.MUB6.Certificate.PairSemantics.sound2491`, `OAI.MUB6.Certificate.PairSemantics.sound2492`, `OAI.MUB6.Certificate.PairSemantics.sound2507`, `OAI.MUB6.Certificate.PairSemantics.sound2520`, `OAI.MUB6.Certificate.PairSemantics.sound2521`, `OAI.MUB6.Certificate.PairSemantics.sound2524`, `OAI.MUB6.Certificate.PairSemantics.sound2525`, `OAI.MUB6.Certificate.PairSemantics.sound2533`, `OAI.MUB6.Certificate.PairSemantics.sound2540`, `OAI.MUB6.Certificate.PairSemantics.sound2546`, `OAI.MUB6.Certificate.PairSemantics.sound2547`, `OAI.MUB6.Certificate.PairSemantics.sound2548`, `OAI.MUB6.Certificate.PairSemantics.sound2557`, `OAI.MUB6.Certificate.PairSemantics.sound2558`, `OAI.MUB6.Certificate.PairSemantics.sound2559`, `OAI.MUB6.Certificate.PairSemantics.sound2564`, `OAI.MUB6.Certificate.PairSemantics.sound2565`, `OAI.MUB6.Certificate.PairSemantics.sound2566`, `OAI.MUB6.Certificate.PairSemantics.sound2573`, `OAI.MUB6.Certificate.PairSemantics.sound2578`, `OAI.MUB6.Certificate.PairSemantics.sound2579`, `OAI.MUB6.Certificate.PairSemantics.sound2580`, `OAI.MUB6.Certificate.PairSemantics.sound2602`, `OAI.MUB6.Certificate.PairSemantics.sound2604`, `OAI.MUB6.Certificate.PairSemantics.sound2606`, `OAI.MUB6.Certificate.PairSemantics.sound2619`, `OAI.MUB6.Certificate.PairSemantics.sound2626`, `OAI.MUB6.Certificate.PairSemantics.sound2627`, `OAI.MUB6.Certificate.PairSemantics.sound2641`, `OAI.MUB6.Certificate.PairSemantics.sound2657`, `OAI.MUB6.Certificate.PairSemantics.sound2661`, `OAI.MUB6.Certificate.PairSemantics.sound2666`, `OAI.MUB6.Certificate.PairSemantics.sound2670`, `OAI.MUB6.Certificate.PairSemantics.sound2671`, `OAI.MUB6.Certificate.PairSemantics.sound2674`, `OAI.MUB6.Certificate.PairSemantics.sound2683`, `OAI.MUB6.Certificate.PairSemantics.sound2686`, `OAI.MUB6.Certificate.PairSemantics.sound2690`, `OAI.MUB6.Certificate.PairSemantics.sound2693`, `OAI.MUB6.Certificate.PairSemantics.sound2709`, `OAI.MUB6.Certificate.PairSemantics.sound2710`, `OAI.MUB6.Certificate.PairSemantics.sound2711`, `OAI.MUB6.Certificate.PairSemantics.sound2714`, `OAI.MUB6.Certificate.PairSemantics.sound2717`, `OAI.MUB6.Certificate.PairSemantics.sound2723`, `OAI.MUB6.Certificate.PairSemantics.sound2732`, `OAI.MUB6.Certificate.PairSemantics.sound2733`, `OAI.MUB6.Certificate.PairSemantics.sound2757`, `OAI.MUB6.Certificate.PairSemantics.sound2765`, `OAI.MUB6.Certificate.PairSemantics.sound2788`, `OAI.MUB6.Certificate.PairSemantics.sound2790`, `OAI.MUB6.Certificate.PairSemantics.sound2793`, `OAI.MUB6.Certificate.PairSemantics.sound2827`, `OAI.MUB6.Certificate.PairSemantics.sound2829`, `OAI.MUB6.Certificate.PairSemantics.sound2836`, `OAI.MUB6.Certificate.PairSemantics.sound2839`, `OAI.MUB6.Certificate.PairSemantics.sound284`, `OAI.MUB6.Certificate.PairSemantics.sound2845`, `OAI.MUB6.Certificate.PairSemantics.sound2850`, `OAI.MUB6.Certificate.PairSemantics.sound2852`, `OAI.MUB6.Certificate.PairSemantics.sound2854`, `OAI.MUB6.Certificate.PairSemantics.sound2863`, `OAI.MUB6.Certificate.PairSemantics.sound2864`, `OAI.MUB6.Certificate.PairSemantics.sound2865`, `OAI.MUB6.Certificate.PairSemantics.sound2866`, `OAI.MUB6.Certificate.PairSemantics.sound2867`, `OAI.MUB6.Certificate.PairSemantics.sound2868`, `OAI.MUB6.Certificate.PairSemantics.sound2872`, `OAI.MUB6.Certificate.PairSemantics.sound2873`, `OAI.MUB6.Certificate.PairSemantics.sound2874`, `OAI.MUB6.Certificate.PairSemantics.sound2875`, `OAI.MUB6.Certificate.PairSemantics.sound2878`, `OAI.MUB6.Certificate.PairSemantics.sound2879`, `OAI.MUB6.Certificate.PairSemantics.sound2880`, `OAI.MUB6.Certificate.PairSemantics.sound2881`, `OAI.MUB6.Certificate.PairSemantics.sound2882`, `OAI.MUB6.Certificate.PairSemantics.sound2883`, `OAI.MUB6.Certificate.PairSemantics.sound2884`, `OAI.MUB6.Certificate.PairSemantics.sound2886`, `OAI.MUB6.Certificate.PairSemantics.sound2887`, `OAI.MUB6.Certificate.PairSemantics.sound2888`, `OAI.MUB6.Certificate.PairSemantics.sound2889`, `OAI.MUB6.Certificate.PairSemantics.sound2890`, `OAI.MUB6.Certificate.PairSemantics.sound2891`, `OAI.MUB6.Certificate.PairSemantics.sound2892`, `OAI.MUB6.Certificate.PairSemantics.sound2894`, `OAI.MUB6.Certificate.PairSemantics.sound2895`, `OAI.MUB6.Certificate.PairSemantics.sound2896`, `OAI.MUB6.Certificate.PairSemantics.sound2897`, `OAI.MUB6.Certificate.PairSemantics.sound2898`, `OAI.MUB6.Certificate.PairSemantics.sound2899`, `OAI.MUB6.Certificate.PairSemantics.sound2900`, `OAI.MUB6.Certificate.PairSemantics.sound2901`, `OAI.MUB6.Certificate.PairSemantics.sound2902`, `OAI.MUB6.Certificate.PairSemantics.sound2903`, `OAI.MUB6.Certificate.PairSemantics.sound2906`, `OAI.MUB6.Certificate.PairSemantics.sound2909`, `OAI.MUB6.Certificate.PairSemantics.sound2910`, `OAI.MUB6.Certificate.PairSemantics.sound2913`, `OAI.MUB6.Certificate.PairSemantics.sound2914`, `OAI.MUB6.Certificate.PairSemantics.sound2915`, `OAI.MUB6.Certificate.PairSemantics.sound2916`, `OAI.MUB6.Certificate.PairSemantics.sound2917`, `OAI.MUB6.Certificate.PairSemantics.sound2918`, `OAI.MUB6.Certificate.PairSemantics.sound2919`, `OAI.MUB6.Certificate.PairSemantics.sound2920`, `OAI.MUB6.Certificate.PairSemantics.sound2922`, `OAI.MUB6.Certificate.PairSemantics.sound2924`, `OAI.MUB6.Certificate.PairSemantics.sound2927`, `OAI.MUB6.Certificate.PairSemantics.sound2928`, `OAI.MUB6.Certificate.PairSemantics.sound2929`, `OAI.MUB6.Certificate.PairSemantics.sound2930`, `OAI.MUB6.Certificate.PairSemantics.sound2931`, `OAI.MUB6.Certificate.PairSemantics.sound2933`, `OAI.MUB6.Certificate.PairSemantics.sound2934`, `OAI.MUB6.Certificate.PairSemantics.sound2935`, `OAI.MUB6.Certificate.PairSemantics.sound2936`, `OAI.MUB6.Certificate.PairSemantics.sound2939`, `OAI.MUB6.Certificate.PairSemantics.sound2940`, `OAI.MUB6.Certificate.PairSemantics.sound2941`, `OAI.MUB6.Certificate.PairSemantics.sound2943`, `OAI.MUB6.Certificate.PairSemantics.sound2944`, `OAI.MUB6.Certificate.PairSemantics.sound2947`, `OAI.MUB6.Certificate.PairSemantics.sound2948`, `OAI.MUB6.Certificate.PairSemantics.sound2949`, `OAI.MUB6.Certificate.PairSemantics.sound2950`, `OAI.MUB6.Certificate.PairSemantics.sound2952`, `OAI.MUB6.Certificate.PairSemantics.sound2953`, `OAI.MUB6.Certificate.PairSemantics.sound2955`, `OAI.MUB6.Certificate.PairSemantics.sound2956`, `OAI.MUB6.Certificate.PairSemantics.sound2957`, `OAI.MUB6.Certificate.PairSemantics.sound2958`, `OAI.MUB6.Certificate.PairSemantics.sound2959`, `OAI.MUB6.Certificate.PairSemantics.sound2960`, `OAI.MUB6.Certificate.PairSemantics.sound2962`, `OAI.MUB6.Certificate.PairSemantics.sound2964`, `OAI.MUB6.Certificate.PairSemantics.sound2965`, `OAI.MUB6.Certificate.PairSemantics.sound2966`, `OAI.MUB6.Certificate.PairSemantics.sound2967`, `OAI.MUB6.Certificate.PairSemantics.sound2968`, `OAI.MUB6.Certificate.PairSemantics.sound2969`, `OAI.MUB6.Certificate.PairSemantics.sound2970`, `OAI.MUB6.Certificate.PairSemantics.sound2972`, `OAI.MUB6.Certificate.PairSemantics.sound2973`, `OAI.MUB6.Certificate.PairSemantics.sound2974`, `OAI.MUB6.Certificate.PairSemantics.sound2975`, `OAI.MUB6.Certificate.PairSemantics.sound2976`, `OAI.MUB6.Certificate.PairSemantics.sound2977`, `OAI.MUB6.Certificate.PairSemantics.sound2979`, `OAI.MUB6.Certificate.PairSemantics.sound2980`, `OAI.MUB6.Certificate.PairSemantics.sound2982`, `OAI.MUB6.Certificate.PairSemantics.sound2985`, `OAI.MUB6.Certificate.PairSemantics.sound2986`, `OAI.MUB6.Certificate.PairSemantics.sound2987`, `OAI.MUB6.Certificate.PairSemantics.sound2988`, `OAI.MUB6.Certificate.PairSemantics.sound2989`, `OAI.MUB6.Certificate.PairSemantics.sound2990`, `OAI.MUB6.Certificate.PairSemantics.sound2991`, `OAI.MUB6.Certificate.PairSemantics.sound2993`, `OAI.MUB6.Certificate.PairSemantics.sound2994`, `OAI.MUB6.Certificate.PairSemantics.sound2996`, `OAI.MUB6.Certificate.PairSemantics.sound2997`, `OAI.MUB6.Certificate.PairSemantics.sound2998`, `OAI.MUB6.Certificate.PairSemantics.sound2999`, `OAI.MUB6.Certificate.PairSemantics.sound3000`, `OAI.MUB6.Certificate.PairSemantics.sound3001`, `OAI.MUB6.Certificate.PairSemantics.sound3002`, `OAI.MUB6.Certificate.PairSemantics.sound3004`, `OAI.MUB6.Certificate.PairSemantics.sound3006`, `OAI.MUB6.Certificate.PairSemantics.sound3009`, `OAI.MUB6.Certificate.PairSemantics.sound3010`, `OAI.MUB6.Certificate.PairSemantics.sound3011`, `OAI.MUB6.Certificate.PairSemantics.sound3012`, `OAI.MUB6.Certificate.PairSemantics.sound3013`, `OAI.MUB6.Certificate.PairSemantics.sound3014`, `OAI.MUB6.Certificate.PairSemantics.sound3015`, `OAI.MUB6.Certificate.PairSemantics.sound3016`, `OAI.MUB6.Certificate.PairSemantics.sound3017`, `OAI.MUB6.Certificate.PairSemantics.sound3018`, `OAI.MUB6.Certificate.PairSemantics.sound3019`, `OAI.MUB6.Certificate.PairSemantics.sound3020`, `OAI.MUB6.Certificate.PairSemantics.sound3021`, `OAI.MUB6.Certificate.PairSemantics.sound3022`, `OAI.MUB6.Certificate.PairSemantics.sound3023`, `OAI.MUB6.Certificate.PairSemantics.sound3024`, `OAI.MUB6.Certificate.PairSemantics.sound3025`, `OAI.MUB6.Certificate.PairSemantics.sound3026`, `OAI.MUB6.Certificate.PairSemantics.sound3027`, `OAI.MUB6.Certificate.PairSemantics.sound3028`, `OAI.MUB6.Certificate.PairSemantics.sound3029`, `OAI.MUB6.Certificate.PairSemantics.sound3030`, `OAI.MUB6.Certificate.PairSemantics.sound3031`, `OAI.MUB6.Certificate.PairSemantics.sound3032`, `OAI.MUB6.Certificate.PairSemantics.sound3033`, `OAI.MUB6.Certificate.PairSemantics.sound3034`, `OAI.MUB6.Certificate.PairSemantics.sound3035`, `OAI.MUB6.Certificate.PairSemantics.sound3036`, `OAI.MUB6.Certificate.PairSemantics.sound3038`, `OAI.MUB6.Certificate.PairSemantics.sound3039`, `OAI.MUB6.Certificate.PairSemantics.sound3040`, `OAI.MUB6.Certificate.PairSemantics.sound3041`, `OAI.MUB6.Certificate.PairSemantics.sound3042`, `OAI.MUB6.Certificate.PairSemantics.sound3043`, `OAI.MUB6.Certificate.PairSemantics.sound3044`, `OAI.MUB6.Certificate.PairSemantics.sound3045`, `OAI.MUB6.Certificate.PairSemantics.sound3047`, `OAI.MUB6.Certificate.PairSemantics.sound3048`, `OAI.MUB6.Certificate.PairSemantics.sound3049`, `OAI.MUB6.Certificate.PairSemantics.sound3050`, `OAI.MUB6.Certificate.PairSemantics.sound3051`, `OAI.MUB6.Certificate.PairSemantics.sound3053`, `OAI.MUB6.Certificate.PairSemantics.sound3054`, `OAI.MUB6.Certificate.PairSemantics.sound3056`, `OAI.MUB6.Certificate.PairSemantics.sound3058`, `OAI.MUB6.Certificate.PairSemantics.sound3059`, `OAI.MUB6.Certificate.PairSemantics.sound3060`, `OAI.MUB6.Certificate.PairSemantics.sound3061`, `OAI.MUB6.Certificate.PairSemantics.sound3062`, `OAI.MUB6.Certificate.PairSemantics.sound3063`, `OAI.MUB6.Certificate.PairSemantics.sound3065`, `OAI.MUB6.Certificate.PairSemantics.sound3066`, `OAI.MUB6.Certificate.PairSemantics.sound3067`, `OAI.MUB6.Certificate.PairSemantics.sound3068`, `OAI.MUB6.Certificate.PairSemantics.sound3069`, `OAI.MUB6.Certificate.PairSemantics.sound3071`, `OAI.MUB6.Certificate.PairSemantics.sound3072`, `OAI.MUB6.Certificate.PairSemantics.sound3073`, `OAI.MUB6.Certificate.PairSemantics.sound3074`, `OAI.MUB6.Certificate.PairSemantics.sound3075`, `OAI.MUB6.Certificate.PairSemantics.sound3076`, `OAI.MUB6.Certificate.PairSemantics.sound3077`, `OAI.MUB6.Certificate.PairSemantics.sound3078`, `OAI.MUB6.Certificate.PairSemantics.sound3079`, `OAI.MUB6.Certificate.PairSemantics.sound3080`, `OAI.MUB6.Certificate.PairSemantics.sound3081`, `OAI.MUB6.Certificate.PairSemantics.sound3082`, `OAI.MUB6.Certificate.PairSemantics.sound3083`, `OAI.MUB6.Certificate.PairSemantics.sound3084`, `OAI.MUB6.Certificate.PairSemantics.sound3085`, `OAI.MUB6.Certificate.PairSemantics.sound3086`, `OAI.MUB6.Certificate.PairSemantics.sound3090`, `OAI.MUB6.Certificate.PairSemantics.sound3091`, `OAI.MUB6.Certificate.PairSemantics.sound3092`, `OAI.MUB6.Certificate.PairSemantics.sound3093`, `OAI.MUB6.Certificate.PairSemantics.sound3094`, `OAI.MUB6.Certificate.PairSemantics.sound3095`, `OAI.MUB6.Certificate.PairSemantics.sound3096`, `OAI.MUB6.Certificate.PairSemantics.sound3097`, `OAI.MUB6.Certificate.PairSemantics.sound3098`, `OAI.MUB6.Certificate.PairSemantics.sound3099`, `OAI.MUB6.Certificate.PairSemantics.sound3100`, `OAI.MUB6.Certificate.PairSemantics.sound3101`, `OAI.MUB6.Certificate.PairSemantics.sound3102`, `OAI.MUB6.Certificate.PairSemantics.sound3105`, `OAI.MUB6.Certificate.PairSemantics.sound3106`, `OAI.MUB6.Certificate.PairSemantics.sound3107`, `OAI.MUB6.Certificate.PairSemantics.sound3108`, `OAI.MUB6.Certificate.PairSemantics.sound3109`, `OAI.MUB6.Certificate.PairSemantics.sound3110`, `OAI.MUB6.Certificate.PairSemantics.sound3111`, `OAI.MUB6.Certificate.PairSemantics.sound3112`, `OAI.MUB6.Certificate.PairSemantics.sound3113`, `OAI.MUB6.Certificate.PairSemantics.sound3114`, `OAI.MUB6.Certificate.PairSemantics.sound3115`, `OAI.MUB6.Certificate.PairSemantics.sound3116`, `OAI.MUB6.Certificate.PairSemantics.sound3118`, `OAI.MUB6.Certificate.PairSemantics.sound3119`, `OAI.MUB6.Certificate.PairSemantics.sound3120`, `OAI.MUB6.Certificate.PairSemantics.sound3121`, `OAI.MUB6.Certificate.PairSemantics.sound3122`, `OAI.MUB6.Certificate.PairSemantics.sound3123`, `OAI.MUB6.Certificate.PairSemantics.sound3124`, `OAI.MUB6.Certificate.PairSemantics.sound3125`, `OAI.MUB6.Certificate.PairSemantics.sound3128`, `OAI.MUB6.Certificate.PairSemantics.sound3129`, `OAI.MUB6.Certificate.PairSemantics.sound3130`, `OAI.MUB6.Certificate.PairSemantics.sound3131`, `OAI.MUB6.Certificate.PairSemantics.sound3133`, `OAI.MUB6.Certificate.PairSemantics.sound3135`, `OAI.MUB6.Certificate.PairSemantics.sound3136`, `OAI.MUB6.Certificate.PairSemantics.sound3138`, `OAI.MUB6.Certificate.PairSemantics.sound3139`, `OAI.MUB6.Certificate.PairSemantics.sound3140`, `OAI.MUB6.Certificate.PairSemantics.sound3141`, `OAI.MUB6.Certificate.PairSemantics.sound3142`, `OAI.MUB6.Certificate.PairSemantics.sound3144`, `OAI.MUB6.Certificate.PairSemantics.sound3145`, `OAI.MUB6.Certificate.PairSemantics.sound3146`, `OAI.MUB6.Certificate.PairSemantics.sound3150`, `OAI.MUB6.Certificate.PairSemantics.sound3151`, `OAI.MUB6.Certificate.PairSemantics.sound3152`, `OAI.MUB6.Certificate.PairSemantics.sound3153`, `OAI.MUB6.Certificate.PairSemantics.sound3155`, `OAI.MUB6.Certificate.PairSemantics.sound3158`, `OAI.MUB6.Certificate.PairSemantics.sound3159`, `OAI.MUB6.Certificate.PairSemantics.sound3160`, `OAI.MUB6.Certificate.PairSemantics.sound3161`, `OAI.MUB6.Certificate.PairSemantics.sound3162`, `OAI.MUB6.Certificate.PairSemantics.sound3163`, `OAI.MUB6.Certificate.PairSemantics.sound3164`, `OAI.MUB6.Certificate.PairSemantics.sound3166`, `OAI.MUB6.Certificate.PairSemantics.sound3167`, `OAI.MUB6.Certificate.PairSemantics.sound3168`, `OAI.MUB6.Certificate.PairSemantics.sound3169`, `OAI.MUB6.Certificate.PairSemantics.sound3170`, `OAI.MUB6.Certificate.PairSemantics.sound3171`, `OAI.MUB6.Certificate.PairSemantics.sound3172`, `OAI.MUB6.Certificate.PairSemantics.sound3173`, `OAI.MUB6.Certificate.PairSemantics.sound3174`, `OAI.MUB6.Certificate.PairSemantics.sound3176`, `OAI.MUB6.Certificate.PairSemantics.sound3178`, `OAI.MUB6.Certificate.PairSemantics.sound3180`, `OAI.MUB6.Certificate.PairSemantics.sound3181`, `OAI.MUB6.Certificate.PairSemantics.sound3183`, `OAI.MUB6.Certificate.PairSemantics.sound3184`, `OAI.MUB6.Certificate.PairSemantics.sound3185`, `OAI.MUB6.Certificate.PairSemantics.sound3186`, `OAI.MUB6.Certificate.PairSemantics.sound3187`, `OAI.MUB6.Certificate.PairSemantics.sound3188`, `OAI.MUB6.Certificate.PairSemantics.sound3189`, `OAI.MUB6.Certificate.PairSemantics.sound3191`, `OAI.MUB6.Certificate.PairSemantics.sound3192`, `OAI.MUB6.Certificate.PairSemantics.sound3193`, `OAI.MUB6.Certificate.PairSemantics.sound3194`, `OAI.MUB6.Certificate.PairSemantics.sound3195`, `OAI.MUB6.Certificate.PairSemantics.sound3196`, `OAI.MUB6.Certificate.PairSemantics.sound3197`, `OAI.MUB6.Certificate.PairSemantics.sound3198`, `OAI.MUB6.Certificate.PairSemantics.sound3199`, `OAI.MUB6.Certificate.PairSemantics.sound3200`, `OAI.MUB6.Certificate.PairSemantics.sound3201`, `OAI.MUB6.Certificate.PairSemantics.sound3202`, `OAI.MUB6.Certificate.PairSemantics.sound3203`, `OAI.MUB6.Certificate.PairSemantics.sound3204`, `OAI.MUB6.Certificate.PairSemantics.sound3205`, `OAI.MUB6.Certificate.PairSemantics.sound3206`, `OAI.MUB6.Certificate.PairSemantics.sound3208`, `OAI.MUB6.Certificate.PairSemantics.sound3211`, `OAI.MUB6.Certificate.PairSemantics.sound3212`, `OAI.MUB6.Certificate.PairSemantics.sound3213`, `OAI.MUB6.Certificate.PairSemantics.sound3214`, `OAI.MUB6.Certificate.PairSemantics.sound3215`, `OAI.MUB6.Certificate.PairSemantics.sound3216`, `OAI.MUB6.Certificate.PairSemantics.sound3217`, `OAI.MUB6.Certificate.PairSemantics.sound3218`, `OAI.MUB6.Certificate.PairSemantics.sound3219`, `OAI.MUB6.Certificate.PairSemantics.sound3221`, `OAI.MUB6.Certificate.PairSemantics.sound3222`, `OAI.MUB6.Certificate.PairSemantics.sound3223`, `OAI.MUB6.Certificate.PairSemantics.sound3224`, `OAI.MUB6.Certificate.PairSemantics.sound3226`, `OAI.MUB6.Certificate.PairSemantics.sound3227`, `OAI.MUB6.Certificate.PairSemantics.sound3228`, `OAI.MUB6.Certificate.PairSemantics.sound3230`, `OAI.MUB6.Certificate.PairSemantics.sound3231`, `OAI.MUB6.Certificate.PairSemantics.sound3233`, `OAI.MUB6.Certificate.PairSemantics.sound3234`, `OAI.MUB6.Certificate.PairSemantics.sound3235`, `OAI.MUB6.Certificate.PairSemantics.sound3237`, `OAI.MUB6.Certificate.PairSemantics.sound3238`, `OAI.MUB6.Certificate.PairSemantics.sound3239`, `OAI.MUB6.Certificate.PairSemantics.sound3240`, `OAI.MUB6.Certificate.PairSemantics.sound3241`, `OAI.MUB6.Certificate.PairSemantics.sound3242`, `OAI.MUB6.Certificate.PairSemantics.sound3243`, `OAI.MUB6.Certificate.PairSemantics.sound3244`, `OAI.MUB6.Certificate.PairSemantics.sound3246`, `OAI.MUB6.Certificate.PairSemantics.sound3247`, `OAI.MUB6.Certificate.PairSemantics.sound3248`, `OAI.MUB6.Certificate.PairSemantics.sound3249`, `OAI.MUB6.Certificate.PairSemantics.sound3250`, `OAI.MUB6.Certificate.PairSemantics.sound3251`, `OAI.MUB6.Certificate.PairSemantics.sound3253`, `OAI.MUB6.Certificate.PairSemantics.sound3254`, `OAI.MUB6.Certificate.PairSemantics.sound3255`, `OAI.MUB6.Certificate.PairSemantics.sound3256`, `OAI.MUB6.Certificate.PairSemantics.sound3258`, `OAI.MUB6.Certificate.PairSemantics.sound3259`, `OAI.MUB6.Certificate.PairSemantics.sound3261`, `OAI.MUB6.Certificate.PairSemantics.sound3262`, `OAI.MUB6.Certificate.PairSemantics.sound3263`, `OAI.MUB6.Certificate.PairSemantics.sound3266`, `OAI.MUB6.Certificate.PairSemantics.sound3267`, `OAI.MUB6.Certificate.PairSemantics.sound3268`, `OAI.MUB6.Certificate.PairSemantics.sound3269`, `OAI.MUB6.Certificate.PairSemantics.sound3270`, `OAI.MUB6.Certificate.PairSemantics.sound3271`, `OAI.MUB6.Certificate.PairSemantics.sound3273`, `OAI.MUB6.Certificate.PairSemantics.sound3275`, `OAI.MUB6.Certificate.PairSemantics.sound3276`, `OAI.MUB6.Certificate.PairSemantics.sound3277`, `OAI.MUB6.Certificate.PairSemantics.sound3279`, `OAI.MUB6.Certificate.PairSemantics.sound3280`, `OAI.MUB6.Certificate.PairSemantics.sound3281`, `OAI.MUB6.Certificate.PairSemantics.sound3282`, `OAI.MUB6.Certificate.PairSemantics.sound3283`, `OAI.MUB6.Certificate.PairSemantics.sound3284`, `OAI.MUB6.Certificate.PairSemantics.sound3288`, `OAI.MUB6.Certificate.PairSemantics.sound3289`, `OAI.MUB6.Certificate.PairSemantics.sound3290`, `OAI.MUB6.Certificate.PairSemantics.sound3291`, `OAI.MUB6.Certificate.PairSemantics.sound3292`, `OAI.MUB6.Certificate.PairSemantics.sound3293`, `OAI.MUB6.Certificate.PairSemantics.sound3294`, `OAI.MUB6.Certificate.PairSemantics.sound3295`, `OAI.MUB6.Certificate.PairSemantics.sound3296`, `OAI.MUB6.Certificate.PairSemantics.sound3297`, `OAI.MUB6.Certificate.PairSemantics.sound3298`, `OAI.MUB6.Certificate.PairSemantics.sound3300`, `OAI.MUB6.Certificate.PairSemantics.sound3301`, `OAI.MUB6.Certificate.PairSemantics.sound3302`, `OAI.MUB6.Certificate.PairSemantics.sound3304`, `OAI.MUB6.Certificate.PairSemantics.sound3305`, `OAI.MUB6.Certificate.PairSemantics.sound3307`, `OAI.MUB6.Certificate.PairSemantics.sound3308`, `OAI.MUB6.Certificate.PairSemantics.sound3310`, `OAI.MUB6.Certificate.PairSemantics.sound3311`, `OAI.MUB6.Certificate.PairSemantics.sound3312`, `OAI.MUB6.Certificate.PairSemantics.sound3313`, `OAI.MUB6.Certificate.PairSemantics.sound3314`, `OAI.MUB6.Certificate.PairSemantics.sound3315`, `OAI.MUB6.Certificate.PairSemantics.sound3316`, `OAI.MUB6.Certificate.PairSemantics.sound3317`, `OAI.MUB6.Certificate.PairSemantics.sound3319`, `OAI.MUB6.Certificate.PairSemantics.sound3322`, `OAI.MUB6.Certificate.PairSemantics.sound3323`, `OAI.MUB6.Certificate.PairSemantics.sound3324`, `OAI.MUB6.Certificate.PairSemantics.sound3325`, `OAI.MUB6.Certificate.PairSemantics.sound3327`, `OAI.MUB6.Certificate.PairSemantics.sound3328`, `OAI.MUB6.Certificate.PairSemantics.sound3332`, `OAI.MUB6.Certificate.PairSemantics.sound3333`, `OAI.MUB6.Certificate.PairSemantics.sound3334`, `OAI.MUB6.Certificate.PairSemantics.sound3335`, `OAI.MUB6.Certificate.PairSemantics.sound3336`, `OAI.MUB6.Certificate.PairSemantics.sound3338`, `OAI.MUB6.Certificate.PairSemantics.sound3340`, `OAI.MUB6.Certificate.PairSemantics.sound3341`, `OAI.MUB6.Certificate.PairSemantics.sound3342`, `OAI.MUB6.Certificate.PairSemantics.sound3343`, `OAI.MUB6.Certificate.PairSemantics.sound3344`, `OAI.MUB6.Certificate.PairSemantics.sound3345`, `OAI.MUB6.Certificate.PairSemantics.sound3346`, `OAI.MUB6.Certificate.PairSemantics.sound3347`, `OAI.MUB6.Certificate.PairSemantics.sound3348`, `OAI.MUB6.Certificate.PairSemantics.sound3349`, `OAI.MUB6.Certificate.PairSemantics.sound3350`, `OAI.MUB6.Certificate.PairSemantics.sound3351`, `OAI.MUB6.Certificate.PairSemantics.sound3352`, `OAI.MUB6.Certificate.PairSemantics.sound3353`, `OAI.MUB6.Certificate.PairSemantics.sound3354`, `OAI.MUB6.Certificate.PairSemantics.sound3355`, `OAI.MUB6.Certificate.PairSemantics.sound3356`, `OAI.MUB6.Certificate.PairSemantics.sound3357`, `OAI.MUB6.Certificate.PairSemantics.sound3359`, `OAI.MUB6.Certificate.PairSemantics.sound3360`, `OAI.MUB6.Certificate.PairSemantics.sound3361`, `OAI.MUB6.Certificate.PairSemantics.sound3362`, `OAI.MUB6.Certificate.PairSemantics.sound3364`, `OAI.MUB6.Certificate.PairSemantics.sound3365`, `OAI.MUB6.Certificate.PairSemantics.sound3366`, `OAI.MUB6.Certificate.PairSemantics.sound3367`, `OAI.MUB6.Certificate.PairSemantics.sound3369`, `OAI.MUB6.Certificate.PairSemantics.sound3370`, `OAI.MUB6.Certificate.PairSemantics.sound3371`, `OAI.MUB6.Certificate.PairSemantics.sound3372`, `OAI.MUB6.Certificate.PairSemantics.sound3373`, `OAI.MUB6.Certificate.PairSemantics.sound3375`, `OAI.MUB6.Certificate.PairSemantics.sound3376`, `OAI.MUB6.Certificate.PairSemantics.sound3377`, `OAI.MUB6.Certificate.PairSemantics.sound3378`, `OAI.MUB6.Certificate.PairSemantics.sound3380`, `OAI.MUB6.Certificate.PairSemantics.sound3381`, `OAI.MUB6.Certificate.PairSemantics.sound3382`, `OAI.MUB6.Certificate.PairSemantics.sound3383`, `OAI.MUB6.Certificate.PairSemantics.sound3384`, `OAI.MUB6.Certificate.PairSemantics.sound3385`, `OAI.MUB6.Certificate.PairSemantics.sound3388`, `OAI.MUB6.Certificate.PairSemantics.sound3390`, `OAI.MUB6.Certificate.PairSemantics.sound3391`, `OAI.MUB6.Certificate.PairSemantics.sound3392`, `OAI.MUB6.Certificate.PairSemantics.sound3393`, `OAI.MUB6.Certificate.PairSemantics.sound3394`, `OAI.MUB6.Certificate.PairSemantics.sound3395`, `OAI.MUB6.Certificate.PairSemantics.sound3396`, `OAI.MUB6.Certificate.PairSemantics.sound3399`, `OAI.MUB6.Certificate.PairSemantics.sound3400`, `OAI.MUB6.Certificate.PairSemantics.sound3401`, `OAI.MUB6.Certificate.PairSemantics.sound3402`, `OAI.MUB6.Certificate.PairSemantics.sound3405`, `OAI.MUB6.Certificate.PairSemantics.sound3407`, `OAI.MUB6.Certificate.PairSemantics.sound3408`, `OAI.MUB6.Certificate.PairSemantics.sound3411`, `OAI.MUB6.Certificate.PairSemantics.sound3412`, `OAI.MUB6.Certificate.PairSemantics.sound3413`, `OAI.MUB6.Certificate.PairSemantics.sound3414`, `OAI.MUB6.Certificate.PairSemantics.sound3415`, `OAI.MUB6.Certificate.PairSemantics.sound3416`, `OAI.MUB6.Certificate.PairSemantics.sound3417`, `OAI.MUB6.Certificate.PairSemantics.sound3418`, `OAI.MUB6.Certificate.PairSemantics.sound3420`, `OAI.MUB6.Certificate.PairSemantics.sound3421`, `OAI.MUB6.Certificate.PairSemantics.sound3422`, `OAI.MUB6.Certificate.PairSemantics.sound3423`, `OAI.MUB6.Certificate.PairSemantics.sound3424`, `OAI.MUB6.Certificate.PairSemantics.sound3425`, `OAI.MUB6.Certificate.PairSemantics.sound3426`, `OAI.MUB6.Certificate.PairSemantics.sound3428`, `OAI.MUB6.Certificate.PairSemantics.sound3431`, `OAI.MUB6.Certificate.PairSemantics.sound3433`, `OAI.MUB6.Certificate.PairSemantics.sound3434`, `OAI.MUB6.Certificate.PairSemantics.sound3435`, `OAI.MUB6.Certificate.PairSemantics.sound3436`, `OAI.MUB6.Certificate.PairSemantics.sound3437`, `OAI.MUB6.Certificate.PairSemantics.sound3438`, `OAI.MUB6.Certificate.PairSemantics.sound3439`, `OAI.MUB6.Certificate.PairSemantics.sound3440`, `OAI.MUB6.Certificate.PairSemantics.sound3441`, `OAI.MUB6.Certificate.PairSemantics.sound3445`, `OAI.MUB6.Certificate.PairSemantics.sound3447`, `OAI.MUB6.Certificate.PairSemantics.sound3449`, `OAI.MUB6.Certificate.PairSemantics.sound3454`, `OAI.MUB6.Certificate.PairSemantics.sound3456`, `OAI.MUB6.Certificate.PairSemantics.sound3457`, `OAI.MUB6.Certificate.PairSemantics.sound3458`, `OAI.MUB6.Certificate.PairSemantics.sound3459`, `OAI.MUB6.Certificate.PairSemantics.sound3460`, `OAI.MUB6.Certificate.PairSemantics.sound3461`, `OAI.MUB6.Certificate.PairSemantics.sound3462`, `OAI.MUB6.Certificate.PairSemantics.sound3463`, `OAI.MUB6.Certificate.PairSemantics.sound3467`, `OAI.MUB6.Certificate.PairSemantics.sound3468`, `OAI.MUB6.Certificate.PairSemantics.sound659`, `OAI.MUB6.Certificate.PairSemantics.sound711`, `OAI.MUB6.Certificate.PairSourceBridge.allRowsSound`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound0`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound10`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound100`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound101`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound102`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound103`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound104`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound105`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound106`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound107`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound108`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound111`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound112`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound113`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound114`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound115`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound116`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound117`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound118`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound119`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound12`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound120`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound121`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound124`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound125`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound126`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound127`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound129`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound13`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound130`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound131`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound132`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound133`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound134`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound135`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound136`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound139`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound14`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound140`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound142`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound146`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound148`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound15`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound150`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound151`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound153`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound154`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound155`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound157`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound159`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound16`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound160`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound161`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound163`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound164`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound165`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound166`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound167`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound168`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound17`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound170`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound171`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound174`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound175`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound176`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound177`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound178`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound18`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound180`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound181`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound182`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound184`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound185`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound186`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound187`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound188`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound19`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound190`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound191`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound192`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound193`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound194`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound195`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound196`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound197`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound198`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound199`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound2`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound20`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound200`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound201`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound202`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound204`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound205`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound207`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound208`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound209`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound210`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound211`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound213`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound214`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound216`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound218`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound219`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound22`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound221`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound223`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound224`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound225`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound226`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound227`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound228`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound229`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound23`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound230`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound231`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound232`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound233`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound235`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound236`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound237`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound238`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound239`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound24`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound240`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound241`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound243`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound244`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound245`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound246`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound248`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound249`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound25`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound250`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound253`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound254`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound26`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound27`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound28`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound3`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound30`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound31`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound32`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound34`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound35`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound36`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound38`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound39`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound4`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound40`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound41`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound42`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound43`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound46`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound49`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound5`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound51`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound52`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound53`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound54`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound57`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound58`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound59`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound6`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound60`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound61`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound62`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound63`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound64`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound66`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound67`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound69`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound70`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound72`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound74`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound76`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound77`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound78`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound79`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound8`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound80`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound81`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound82`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound83`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound84`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound85`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound86`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound87`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound89`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound9`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound90`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound91`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound92`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound93`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound94`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound95`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound96`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound97`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound98`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound99`, `OAI.MUB6.Certificate.PairTargetSemantics.partition12`, `OAI.MUB6.Certificate.PairTargetSemantics.partition16`, `OAI.MUB6.Certificate.PairTargetSemantics.partition19`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm11`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm21`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm23`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm26`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm6`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm7`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm8` and `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm9`.
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

def raw6step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]

def raw6step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def raw7 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw69 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]

def raw69step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![1, -3, 2], ![1, -1, 0]]

def raw72 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]

def raw72step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]

def raw72step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![1, -2, 1], ![1, -2, 1]]

def raw74 : Matrix (Fin 3) (Fin 4) ℤ := ![![-4, 1, 1, 2], ![2, -2, 1, -1], ![2, 1, -2, -1]]

def raw74step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]

def raw74step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]

def raw74step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]

def raw75 : Matrix (Fin 3) (Fin 4) ℤ := ![![-4, 1, 2, 1], ![2, -2, -1, 1], ![2, 1, -1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw690 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![2, 1, -3]]

def raw690step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]

def raw690step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -3, 2], ![1, 2, -3]]

def raw691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

def raw692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def raw693 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]

def raw694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw695 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

def raw696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]

def raw696step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1]]

def raw697 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]

def raw697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1]]

def raw698 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]

def raw699 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![3, 0, -3]]

def raw699step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

def raw700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def raw701 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

def raw702 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

def raw703 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1], ![1, 0, -1]]

def raw703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical215
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6896step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![2, 1, -3], ![0, -1, 1]]

def raw6896step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -2, 1], ![-2, -1, 3], ![0, 1, -1]]

def raw6896step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

def raw6897 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-2, 3, -2, 1], ![3, -2, 0, -1]]

def raw6897step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![2, -2, 0], ![0, 1, -1]]

def raw6897step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -3, 2], ![-2, 2, 0], ![0, -1, 1]]

def raw6897step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -3, 2], ![1, 2, -3]]

def raw6898 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-2, 3, 0, -1], ![3, -2, -2, 1]]

def raw6898step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![2, 0, -2], ![0, -1, 1]]

def raw6898step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -3, 2], ![-2, 0, 2], ![0, 1, -1]]

def raw6898step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -3, 2], ![1, 2, -3]]

def raw6899 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-2, 4, -1, -1], ![3, -3, -1, 1]]

def raw6899step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 4, -3], ![2, -1, -1], ![0, -1, 1]]

def raw6899step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -4, 3], ![-2, 1, 1], ![0, 1, -1]]

def raw6899step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -3, 2], ![1, 3, -4]]

def raw6900 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-1, -2, 1, 2], ![2, 3, -3, -2]]

def raw6900step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![2, 1, -3], ![0, 2, -2]]

def raw6900step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 2, -3], ![-2, -1, 3], ![0, -2, 2]]

def raw6900step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 1, -2], ![1, 2, -3]]

def raw6901 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-1, -2, 2, 1], ![2, 3, -4, -1]]

def raw6901step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![2, 2, -4], ![0, 1, -1]]

def raw6901step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 2, -3], ![-2, -2, 4], ![0, -1, 1]]

def raw6901step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![1, 1, -2], ![1, 2, -3]]

def raw6902 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-1, -1, -2, 4], ![2, 2, 0, -4]]

def raw6902step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![2, -2, 0], ![0, 4, -4]]

def raw6902step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-2, 2, 0], ![0, -4, 4]]

def raw6902step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![1, -2, 1], ![1, -2, 1]]

def raw6903 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-1, -1, -1, 3], ![2, 2, -1, -3]]

def raw6903step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![2, -1, -1], ![0, 3, -3]]

def raw6903step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-2, 1, 1], ![0, -3, 3]]

def raw6903step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]

def raw6904 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-1, -1, 3, -1], ![2, 2, -5, 1]]

def raw6904step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![2, 3, -5], ![0, -1, 1]]

def raw6904step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-2, -3, 5], ![0, 1, -1]]

def raw6904step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

def raw6905 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-1, 2, -3, 2], ![2, -1, 1, -2]]

def raw6905step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![2, -3, 1], ![0, 2, -2]]

def raw6905step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -2, 1], ![-2, 3, -1], ![0, -2, 2]]

def raw6905step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def raw6906 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-1, 2, -2, 1], ![2, -1, 0, -1]]

def raw6906step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![2, -2, 0], ![0, 1, -1]]

def raw6906step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -2, 1], ![-2, 2, 0], ![0, -1, 1]]

def raw6906step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw6907 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-1, 2, 0, -1], ![2, -1, -2, 1]]

def raw6907step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![2, 0, -2], ![0, -1, 1]]

def raw6907step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -2, 1], ![-2, 0, 2], ![0, 1, -1]]

def raw6907step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw6908 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-1, 2, 1, -2], ![2, -1, -3, 2]]

def raw6908step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![2, 1, -3], ![0, -2, 2]]

def raw6908step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -2, 1], ![-2, -1, 3], ![0, 2, -2]]

def raw6908step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def raw6909 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-1, 3, -4, 2], ![2, -2, 2, -2]]

def raw6909step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![2, -4, 2], ![0, 2, -2]]

def raw6909step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -3, 2], ![-2, 4, -2], ![0, -2, 2]]

def raw6909step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -2, 1], ![1, 2, -3]]

def raw6910 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-1, 3, -1, -1], ![2, -2, -1, 1]]

def raw6910step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![2, -1, -1], ![0, -1, 1]]

def raw6910step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -3, 2], ![-2, 1, 1], ![0, 1, -1]]

def raw6910step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

def raw6911 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-1, 3, 0, -2], ![2, -2, -2, 2]]

def raw6911step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![2, 0, -2], ![0, -2, 2]]

def raw6911step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -3, 2], ![-2, 0, 2], ![0, 2, -2]]

def raw6911step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical216
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6912 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-1, 4, -1, -2], ![2, -3, -1, 2]]

def raw6912step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 4, -3], ![2, -1, -1], ![0, -2, 2]]

def raw6912step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -4, 3], ![-2, 1, 1], ![0, 2, -2]]

def raw6912step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -2, 1], ![1, 3, -4]]

def raw6913 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -3, 1, 2], ![1, 4, -3, -2]]

def raw6913step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![2, 1, -3], ![0, 2, -2]]

def raw6913step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 3, -4], ![-2, -1, 3], ![0, -2, 2]]

def raw6913step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 3, -4]]

def raw6914 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -2, -1, 3], ![1, 3, -1, -3]]

def raw6914step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![2, -1, -1], ![0, 3, -3]]

def raw6914step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 2, -3], ![-2, 1, 1], ![0, -3, 3]]

def raw6914step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 0, -1], ![1, 2, -3]]

def raw6915 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -2, 1, 1], ![1, 3, -3, -1]]

def raw6915step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![2, 1, -3], ![0, 1, -1]]

def raw6915step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]

def raw6916 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -3, 4], ![0, 1, 1, -2], ![1, 1, 0, -2]]

def raw6916step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -2, 0], ![0, 1, 3, -4], ![0, -1, -1, 2], ![-1, -1, 0, 2]]

def raw6916step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, 1, -2, 0]]

def raw6917 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -3, 4], ![1, 2, 1, -4]]

def raw6917step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![2, -3, 1], ![0, 4, -4]]

def raw6917step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 1, -2], ![-2, 3, -1], ![0, -4, 4]]

def raw6917step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 4, -4], ![1, -2, 1], ![1, -1, 0]]

def raw6918 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -2, 3], ![0, 1, 0, -1], ![1, 1, 0, -2]]

def raw6918step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 1, 1], ![2, -2, 0, 0], ![0, 3, -1, -2]]

def raw6918step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, -1, -1]]

def raw6919 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -2, 3], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw6919step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![2, -2, 0, 0], ![0, 3, -2, -1]]

def raw6919step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw6920 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -2, 3], ![1, 2, 0, -3]]

def raw6920step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![2, -2, 0], ![0, 3, -3]]

def raw6920step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 1, -2], ![-2, 2, 0], ![0, -3, 3]]

def raw6920step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

def raw6921 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -1, 2], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw6921step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw6922 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, 0, 1], ![0, 2, 1, -3], ![1, 0, -3, 2]]

def raw6922step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, -3, 1], ![1, 0, 2, -3]]

def raw6923 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, 2, -1], ![1, 2, -4, 1]]

def raw6923step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![2, 2, -4], ![0, -1, 1]]

def raw6923step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 1, -2], ![-2, -2, 4], ![0, 1, -1]]

def raw6923step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw6924 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, 3, -2], ![1, 2, -5, 2]]

def raw6924step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![2, 3, -5], ![0, -2, 2]]

def raw6924step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 1, -2], ![-2, -3, 5], ![0, 2, -2]]

def raw6924step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def raw6925 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 0, -3, 3], ![0, 2, 1, -3], ![1, -1, 0, 0]]

def raw6925step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 2, -3, 1], ![1, -1, 0, 0]]

def raw6926 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw6926step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def raw6927 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw6927step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw6928 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 0, -2, 2], ![1, 1, 0, -2]]

def raw6928step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![2, -2, 0], ![0, 2, -2]]

def raw6928step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

def raw6929 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw6929step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![2, -1, 0, -1], ![0, 1, -2, 1]]

def raw6929step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 0, -2, 1], ![-2, 1, 0, 1], ![0, -1, 2, -1]]

def raw6929step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw6930 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, -2, 2]]

def raw6930step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, -1, 2, -2]]

def raw6931 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -3, 3]]

def raw6931step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![2, 1, 0, -3], ![0, -1, -2, 3]]

def raw6931step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 2, -3]]

def raw6932 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 1, -3, 2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw6932step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw6933 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw6933step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![2, 0, 0, -2], ![0, -1, -1, 2]]

def raw6933step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, -1, -1]]

def raw6934 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 2, -3, 1], ![1, -1, 1, -1]]

def raw6934step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![2, -3, 1], ![0, 1, -1]]

def raw6934step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -2, 1], ![-2, 3, -1], ![0, -1, 1]]

def raw6934step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw6935 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw6935step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![0, -2, 2]]

def raw6935step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

def raw6936 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 2, 1, -3], ![1, -1, -3, 3]]

def raw6936step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![2, 1, -3], ![0, -3, 3]]

def raw6936step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -2, 1], ![-2, -1, 3], ![0, 3, -3]]

def raw6936step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw6937 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 3, -4, 1], ![1, -2, 2, -1]]

def raw6937step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 3, -2], ![2, -4, 2], ![0, 1, -1]]

def raw6937step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -3, 2], ![-2, 4, -2], ![0, -1, 1]]

def raw6937step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw6938 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 3, -1, -2], ![1, -2, -1, 2]]

def raw6938step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 3, -2], ![2, -1, -1], ![0, -2, 2]]

def raw6938step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -3, 2], ![-2, 1, 1], ![0, 2, -2]]

def raw6938step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

def raw6939 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 3, 0, -3], ![1, -2, -2, 3]]

def raw6939step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 3, -2], ![2, 0, -2], ![0, -3, 3]]

def raw6939step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -3, 2], ![-2, 0, 2], ![0, 3, -3]]

def raw6939step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

def raw6940 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 4, -1, -3], ![1, -3, -1, 3]]

def raw6940step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 4, -3], ![2, -1, -1], ![0, -3, 3]]

def raw6940step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -4, 3], ![-2, 1, 1], ![0, 3, -3]]

def raw6940step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, -1, 0], ![1, 3, -4]]

def raw6941 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![1, -3, 0, 2], ![0, 4, -2, -2]]

def raw6941step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![2, 0, -2], ![0, 2, -2]]

def raw6941step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![1, 3, -4], ![-2, 0, 2], ![0, -2, 2]]

def raw6941step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

def raw6942 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![1, -3, 1, 1], ![0, 4, -3, -1]]

def raw6942step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![2, 1, -3], ![0, 1, -1]]

def raw6942step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![1, 3, -4], ![-2, -1, 3], ![0, -1, 1]]

def raw6942step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def raw6943 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![1, -2, -1, 2], ![0, 3, -1, -2]]

def raw6943step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![2, -1, -1], ![0, 2, -2]]

def raw6943step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![1, 2, -3], ![-2, 1, 1], ![0, -2, 2]]

def raw6943step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical217
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6944 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![1, -1, -3, 3], ![0, 2, 1, -3]]

def raw6944step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![2, -3, 1], ![0, 3, -3]]

def raw6944step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![1, 1, -2], ![-2, 3, -1], ![0, -3, 3]]

def raw6944step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw6945 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![1, -1, -2, 2], ![0, 2, 0, -2]]

def raw6945step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![2, -2, 0], ![0, 2, -2]]

def raw6945step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

def raw6946 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![1, -1, 2, -2], ![0, 2, -4, 2]]

def raw6946step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![2, 2, -4], ![0, -2, 2]]

def raw6946step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![1, 1, -2], ![-2, -2, 4], ![0, 2, -2]]

def raw6946step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def raw6947 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![2, -3, 0, 1], ![-1, 4, -2, -1]]

def raw6947step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -3, 4], ![2, 0, -2], ![0, 1, -1]]

def raw6947step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![1, 3, -4], ![-2, 0, 2], ![0, -1, 1]]

def raw6947step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -2, 1], ![1, 3, -4]]

def raw6948 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![2, -2, 1, -1], ![-1, 3, -3, 1]]

def raw6948step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![2, 1, -3], ![0, -1, 1]]

def raw6948step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![1, 2, -3], ![-2, -1, 3], ![0, 1, -1]]

def raw6948step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

def raw6949 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![2, -1, 0, -1], ![-1, 2, -2, 1]]

def raw6949step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![2, 0, -2], ![0, -1, 1]]

def raw6949step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![1, 1, -2], ![-2, 0, 2], ![0, 1, -1]]

def raw6949step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw6950 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![2, -1, 1, -2], ![-1, 2, -3, 2]]

def raw6950step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![2, 1, -3], ![0, -2, 2]]

def raw6950step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![1, 1, -2], ![-2, -1, 3], ![0, 2, -2]]

def raw6950step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def raw6951 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![3, -2, 0, -1], ![-2, 3, -2, 1]]

def raw6951step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -2, 3], ![2, 0, -2], ![0, -1, 1]]

def raw6951step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 2, -3], ![-2, 0, 2], ![0, 1, -1]]

def raw6951step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -3, 2], ![1, 2, -3]]

def raw6952 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![3, -1, 0, -2], ![-2, 2, -2, 2]]

def raw6952step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![2, 0, -2], ![0, -2, 2]]

def raw6952step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 1, -2], ![-2, 0, 2], ![0, 2, -2]]

def raw6952step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

def raw6953 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![-1, 0, -3, 4], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw6953step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, -3, 1], ![1, 0, 3, -4], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, -1, 0, 2]]

def raw6953step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 0, 0, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 1, -3, 1]]

def raw6954 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![-1, 0, -3, 4], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw6954step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![0, -1, -3, 4], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw6955 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![-1, 0, -3, 4], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw6955step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, -3, 1], ![1, 0, 3, -4], ![0, -2, 0, 2], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw6955step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 1, -3, 1]]

def raw6956 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![-1, 0, -2, 3], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def raw6956step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, -3, 1], ![1, 0, 2, -3], ![0, -1, 0, 1], ![-1, 1, 1, -1], ![-1, -1, 0, 2]]

def raw6956step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 0, 0, 1], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 1, -3, 1]]

def raw6957 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![-1, 0, -2, 3], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw6957step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw6958 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![-1, 0, -2, 3], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw6958step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, -3, 1], ![1, 0, 2, -3], ![0, -2, 0, 2], ![-1, 1, 1, -1], ![-1, 0, 0, 1]]

def raw6958step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 1, -3, 1]]

def raw6959 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![-1, 1, -3, 3], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw6959step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 0, 0], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw6960 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![-1, 1, -2, 2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw6960step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 1, -1], ![0, 1, -1, 0], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw6961 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![-1, 3, -2, 0], ![2, -2, -1, 1]]

def raw6961step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![3, -2, -1], ![-1, 0, 1]]

def raw6961step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -3, 2], ![-3, 2, 1], ![1, 0, -1]]

def raw6961step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

def raw6962 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![0, -1, -3, 4], ![0, 1, 0, -1], ![1, 1, 0, -2]]

def raw6962step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 1, 1], ![3, -3, 0, 0], ![-1, 4, -1, -2]]

def raw6962step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, 1, -1, -1]]

def raw6963 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw6963step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![3, -3, 0, 0], ![-1, 4, -2, -1]]

def raw6963step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 3, -3], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw6964 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![0, 0, -3, 3], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw6964step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def raw6965 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def raw6965step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw6966 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw6966step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def raw6967 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![0, 2, -1, -1], ![1, -1, -2, 2]]

def raw6967step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![3, -1, -2], ![-1, -1, 2]]

def raw6967step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -2, 1], ![-3, 1, 2], ![1, 1, -2]]

def raw6967step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

def raw6968 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![0, 2, 0, -2], ![1, -1, -3, 3]]

def raw6968step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![3, 0, -3], ![-1, -2, 3]]

def raw6968step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![2, -1, -1]]

def raw6969 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![0, 3, -2, -1], ![1, -2, -1, 2]]

def raw6969step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 3, -2], ![3, -2, -1], ![-1, -1, 2]]

def raw6969step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -3, 2], ![-3, 2, 1], ![1, 1, -2]]

def raw6969step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

def raw6970 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![1, -2, 1, 0], ![0, 3, -4, 1]]

def raw6970step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![3, 1, -4], ![-1, 0, 1]]

def raw6970step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def raw6971 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![2, -2, 1, -1], ![-1, 3, -4, 2]]

def raw6971step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![3, 1, -4], ![-1, -1, 2]]

def raw6971step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![1, 2, -3], ![-3, -1, 4], ![1, 1, -2]]

def raw6971step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]

def raw6972 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, -1, 2, 0], ![1, 0, 1, -2], ![1, 1, 0, -2]]

def raw6972step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 3, -4], ![1, 1, -2, 0], ![-1, 0, -1, 2], ![-1, -1, 0, 2]]

def raw6972step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, 1, -2, 0]]

def raw6973 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 0, 3, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw6973step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 3, -4], ![1, 0, -3, 2], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw6973step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 1, -3, 2], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw6974 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 1, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw6975 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 1, 1, -1], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, -1, 0, 0]]

def raw6975step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 1, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical218
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6976 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 1, 1, -1], ![0, 1, 1, -2], ![2, -2, 1, -1]]

def raw6976step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 1, -2], ![-3, 1, 1, 1], ![4, -1, -2, -1]]

def raw6976step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 1, -2, 0], ![1, 1, 1, -3]]

def raw6977 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 1, 1, -1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw6978 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 1, 1, -1], ![0, 1, 2, -3], ![2, -2, 0, 0]]

def raw6978step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 1, -2], ![-3, 1, 2, 0], ![4, -1, -3, 0]]

def raw6978step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 0, -2], ![0, -1, -1, 2], ![3, -1, -2, 0], ![-4, 1, 3, 0]]

def raw6978step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -2, 3], ![0, 1, 3, -4], ![2, -1, -1, 0]]

def raw6979 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 1, 1, -1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw6979step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 3, -4], ![1, -1, -1, 1], ![-1, 1, -1, 1], ![-1, 0, -1, 2]]

def raw6979step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def raw6980 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 1, 1, -1], ![1, 0, 1, -2], ![1, -1, 1, -1]]

def raw6980step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 3, -4], ![1, -1, -1, 1], ![-1, 0, -1, 2], ![-1, 1, -1, 1]]

def raw6980step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def raw6981 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 1, 1, -1], ![1, 0, 2, -3], ![1, -1, 0, 0]]

def raw6981step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 3, -4], ![1, -1, -1, 1], ![-1, 0, -2, 3], ![-1, 1, 0, 0]]

def raw6981step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, -2, 3], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw6982 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 1, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw6983 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 1, 2, -2], ![0, 1, 1, -2], ![2, -2, 0, 0]]

def raw6983step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 1, -2], ![-3, 2, 1, 0], ![4, -2, -2, 0]]

def raw6983step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -2, 1, 0], ![1, 0, 2, -3]]

def raw6984 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 1, 2, -2], ![1, 0, 1, -2], ![1, -1, 0, 0]]

def raw6984step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, 0, -1], ![-3, 2, 1, 0], ![4, -2, -2, 0]]

def raw6984step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![0, -1, 0, 1], ![3, -2, -1, 0], ![-4, 2, 2, 0]]

def raw6984step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw6985 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -2, 2, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw6986 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -2, 2, 0], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw6987 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -2, 2, 0], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw6988 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -2, 2, 0], ![1, 2, 1, -4]]

def raw6988step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![-3, 2, 1], ![4, 0, -4]]

def raw6988step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 2, -2], ![3, -2, -1], ![-4, 0, 4]]

def raw6988step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 4, -4], ![2, -2, 0]]

def raw6989 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -2, 3, -1], ![0, 1, 0, -1], ![1, 1, 0, -2]]

def raw6989step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![-3, 3, 0, 0], ![4, -1, -1, -2]]

def raw6989step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def raw6990 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -2, 3, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw6990step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![-3, 3, 0, 0], ![4, -1, -2, -1]]

def raw6990step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw6991 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw6992 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw6993 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw6994 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw6995 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 2, 0, -2], ![1, -1, 2, -2]]

def raw6996 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw6997 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw6998 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw6999 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw7000 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, -1, 0, 0]]

def raw7000step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![-3, 2, 1, 0], ![4, -1, -3, 0]]

def raw7000step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -3, 4], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw7001 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![1, 1, 1, -3]]

def raw7001step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-3, 2, 1], ![4, -1, -3]]

def raw7001step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 1, -1], ![3, -2, -1], ![-4, 1, 3]]

def raw7001step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def raw7002 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw7002step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![-3, 3, 0, 0], ![4, -2, -1, -1]]

def raw7002step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw7003 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 3, -2], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw7004 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 3, -2], ![1, 1, 0, -2]]

def raw7004step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-3, 3, 0], ![4, -2, -2]]

def raw7004step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw7005 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw7005step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw7006 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw7007 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -2, 1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical219
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7008 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, 0, 0, -1]]

def raw7008step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

def raw7009 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, 2, -1]]

def raw7010 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -2, 1, 0]]

def raw7011 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw7011step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -2, 1, 0]]

def raw7012 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw7013 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw7013step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![-3, 1, 2, 0], ![4, -1, -3, 0]]

def raw7013step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def raw7014 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -2, 2, -1]]

def raw7014step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![-3, 1, 0, 2], ![4, -1, -2, -1]]

def raw7014step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 2, -3]]

def raw7015 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -2, 1, 0]]

def raw7015step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![-3, 1, 1, 1], ![4, -1, -3, 0]]

def raw7015step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, -2, 2], ![3, -1, -1, -1], ![-4, 1, 3, 0]]

def raw7015step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 0, 1], ![0, 2, -2, 0], ![1, 0, 3, -4]]

def raw7016 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![1, 0, 2, -3]]

def raw7016step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![1, 2, -3]]

def raw7017 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw7018 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 1, -1]]

def raw7019 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw7020 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -2, 1, 0]]

def raw7021 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![1, 0, 1, -2]]

def raw7021step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![1, 1, -2]]

def raw7022 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 3, -3], ![1, 0, 0, -1]]

def raw7022step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 3, -3], ![1, 0, -1]]

def raw7023 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, 3, -2]]

def raw7023step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![-3, 0, 0, 3], ![4, -1, -1, -2]]

def raw7023step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 3, -3], ![1, 1, -2, 0]]

def raw7024 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -2, 2, -1]]

def raw7024step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![-3, 0, 1, 2], ![4, -1, -2, -1]]

def raw7024step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, 2, -3], ![1, 1, -2, 0]]

def raw7025 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw7026 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 0, -1], ![1, -1, 3, -3]]

def raw7026step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-3, 0, 3], ![4, -1, -3]]

def raw7026step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0]]

def raw7027 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 1, -2], ![-1, 1, 2, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw7027step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 1, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw7028 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 1, -2], ![0, 0, 2, -2], ![1, -1, 0, 0]]

def raw7028step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw7029 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 1, -2], ![0, 1, 0, -1], ![1, -2, 2, -1]]

def raw7029step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![-3, 1, 0, 2], ![4, -2, -1, -1]]

def raw7029step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, 2, -3], ![1, 1, -2, 0]]

def raw7030 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![0, -1, 1, 0], ![1, -1, 0, 0]]

def raw7030step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw7031 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -2, 1, 0]]

def raw7032 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -1, 0, 0], ![0, -1, 1, 0]]

def raw7032step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw7033 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 1, -2], ![1, -1, 2, -2]]

def raw7033step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-3, 1, 2], ![4, -2, -2]]

def raw7033step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw7034 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 2, -3], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw7034step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw7035 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 2, -3], ![1, -1, 1, -1]]

def raw7035step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-3, 2, 1], ![4, -3, -1]]

def raw7035step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3]]

def raw7036 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw7036step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-3, 3, 0], ![4, -4, 0]]

def raw7036step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 4, -4], ![1, -1, 0]]

def raw7037 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 2, 0, -2], ![1, -2, 3, -2]]

def raw7037step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![-3, 0, 3], ![4, -2, -2]]

def raw7037step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 3, -3], ![2, -2, 0]]

def raw7038 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 2, 2, -4], ![1, -2, 1, 0]]

def raw7038step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![-3, 2, 1], ![4, -4, 0]]

def raw7038step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![1, -3, 2], ![1, -1, 0]]

def raw7039 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![1, -2, 2, -1], ![0, 2, 1, -3]]

def raw7039step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -2, 2], ![-3, 2, 1], ![4, -1, -3]]

def raw7039step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw704 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]

def raw705 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]

def raw706 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

def raw707 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]

def raw708 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]

def raw709 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0], ![1, 2, -3]]

def raw709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

def raw710 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]

def raw710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2]]

def raw711 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]

def raw711step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -3, 2], ![1, 2, -3]]

def raw712 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]

def raw712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2]]

def raw713 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]

def raw713step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

def raw714 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]

def raw715 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 3, -4], ![2, -2, 0]]

def raw716 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![2, -2, 0], ![1, 3, -4]]

def raw716step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 3, -4], ![2, -2, 0]]

def raw717 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![2, -1, -1], ![1, 2, -3]]

def raw717step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]

def raw718 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![2, 0, -2], ![1, 1, -2]]

def raw718step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

def raw719 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![3, 1, -4]]

def raw719step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![2, 2, -4]]

def raw719step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 2, -1], ![-2, -2, 4]]

def raw719step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, -1, -1]]

def raw720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]

def raw720step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1]]

def raw721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]

def raw721step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]

def raw721step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

def raw722 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]

def raw722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]

def raw722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]

def raw723 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]

def raw723step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]

def raw723step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3]]

def raw724 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]

def raw724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![-2, -1, 3]]

def raw724step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-2, -1, 3]]

def raw724step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1]]

def raw725 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]

def raw725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![-2, 1, 1]]

def raw725step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]

def raw725step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

def raw726 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2]]

def raw726step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]

def raw726step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3]]

def raw727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]

def raw728 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]

def raw729 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]

def raw731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def raw731step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]

def raw731step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw732 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

def raw732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]

def raw732step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw733 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def raw733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]

def raw733step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw734 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]

def raw735 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]

def raw735step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical220
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7040 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![1, -2, 3, -2], ![0, 2, 0, -2]]

def raw7040step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -2, 2], ![-3, 3, 0], ![4, -2, -2]]

def raw7040step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 3, -3], ![2, -2, 0]]

def raw7041 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![1, -1, 2, -2], ![0, 1, 1, -2]]

def raw7041step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![-3, 2, 1], ![4, -2, -2]]

def raw7041step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw7042 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, -1, 2, 0], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw7042step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, 1, -1, -1]]

def raw7043 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, 0, 2, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw7043step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 2, -3], ![1, 0, -2, 1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, -1, 2]]

def raw7043step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![0, 1, -3, 2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw7044 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, 0, 2, -1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw7044step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 2, -3], ![1, 0, -2, 1], ![0, -1, 1, 0], ![-1, 1, -1, 1], ![-1, 0, 0, 1]]

def raw7044step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 1, -3, 2], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw7045 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, 0, 2, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw7045step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 2, -3], ![1, 0, -2, 1], ![0, -1, 0, 1], ![-1, 1, -1, 1], ![-1, 0, 1, 0]]

def raw7045step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, -1, 1]]

def raw7046 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, 0, 2, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw7046step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 2, -3], ![1, 0, -2, 1], ![0, -1, -1, 2], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw7046step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw7047 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, 0, 2, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw7047step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 2, -3], ![1, 0, -2, 1], ![-1, 1, -1, 1], ![-1, -1, 1, 1]]

def raw7047step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -3, 2], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw7048 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, 0, 3, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw7048step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 2, -3], ![1, 0, -3, 2], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw7048step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 1, -3, 2], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw7049 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, 0, 3, -2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw7049step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 2, -3], ![1, 0, -3, 2], ![0, -1, 0, 1], ![-1, 1, 1, -1], ![-1, 0, 0, 1]]

def raw7049step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 1, -3, 2], ![0, 1, 2, -3], ![1, -1, 1, -1]]

def raw7050 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, 0, 3, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw7050step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 2, -3], ![1, 0, -3, 2], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw7050step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 1, -3, 2], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw7051 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, 0, 3, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw7051step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 2, -3], ![1, 0, -3, 2], ![-1, 1, 0, 0], ![-1, -1, 1, 1]]

def raw7051step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -3, 2], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw7052 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, 1, -1, 1], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw7052step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, -1, -2, 3], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def raw7053 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, 1, -1, 1], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def raw7053step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 2, -3], ![1, -1, 1, -1], ![-1, 1, -3, 3], ![-1, 0, 0, 1]]

def raw7053step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, 0, 1], ![0, 1, 2, -3], ![1, -1, -3, 3]]

def raw7054 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, 1, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw7054step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw7055 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, 1, 1, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw7055step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, -1, 1]]

def raw7056 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, 1, 3, -3], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw7057 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, 1, 3, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw7057step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -1, 0], ![-2, 3, 0, -1], ![3, -3, 0, 0]]

def raw7057step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![0, -1, 1, 0], ![2, -3, 0, 1], ![-3, 3, 0, 0]]

def raw7057step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -3, 3], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def raw7058 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, 1, 3, -3], ![1, 0, -1, 0], ![1, -1, 0, 0]]

def raw7058step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, 0, -1], ![-2, 3, -1, 0], ![3, -3, 0, 0]]

def raw7058step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![0, -1, 0, 1], ![2, -3, 1, 0], ![-3, 3, 0, 0]]

def raw7058step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -3, 3], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def raw7059 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, 2, 2, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw7059step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 2, -1, -1], ![-2, 2, 0, 0], ![3, -3, 0, 0]]

def raw7059step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, 1, -1, -1]]

def raw7060 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw7061 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 1, 1], ![1, 2, 1, -4]]

def raw7061step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![-2, 1, 1], ![3, 1, -4]]

def raw7061step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -2, 1], ![1, 3, -4]]

def raw7062 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 2, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw7063 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 2, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw7064 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 2, 0], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw7065 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 2, 0], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw7065step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw7066 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 2, 0], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw7067 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 2, 0], ![1, 2, 0, -3]]

def raw7067step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![-2, 2, 0], ![3, 0, -3]]

def raw7067step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![2, -2, 0]]

def raw7068 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 3, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def raw7068step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![-2, 3, 0, -1], ![3, -1, -1, -1]]

def raw7068step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def raw7069 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 3, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw7069step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![-2, 3, -1, 0], ![3, -1, -1, -1]]

def raw7069step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw7070 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 3, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw7071 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 3, -1], ![1, 2, -1, -2]]

def raw7071step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![-2, 3, -1], ![3, -1, -2]]

def raw7071step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 2, -2], ![2, -3, 1], ![-3, 1, 2]]

def raw7071step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical221
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7072 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw7073 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw7074 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw7075 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw7076 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def raw7077 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw7077step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw7078 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw7079 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def raw7080 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw7081 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw7081step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![-2, 2, 0, 0], ![3, -1, -1, -1]]

def raw7081step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw7082 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw7083 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def raw7084 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw7084step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw7085 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![1, 1, 0, -2]]

def raw7085step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-2, 2, 0], ![3, -1, -2]]

def raw7085step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw7086 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw7087 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw7088 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def raw7089 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 3, -2], ![1, 1, -1, -1]]

def raw7089step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-2, 3, -1], ![3, -2, -1]]

def raw7089step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1]]

def raw7090 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 0, 0], ![1, 0, 2, -3]]

def raw7090step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![-2, 0, 2], ![3, 0, -3]]

def raw7090step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![3, 0, -3]]

def raw7090step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![3, -3]]

def raw7090step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw7091 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 1, -1], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def raw7091step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def raw7092 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0]]

def raw7093 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -2, 1, 0]]

def raw7094 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, 0, -1]]

def raw7094step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw7095 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, 0, -1, 0]]

def raw7095step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def raw7096 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw7096step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def raw7097 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 1, -1]]

def raw7097step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![-2, 1, 0, 1], ![3, -1, -1, -1]]

def raw7097step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw7098 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw7098step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![-2, 1, 1, 0], ![3, -1, -2, 0]]

def raw7098step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw7099 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -2, 2, -1]]

def raw7099step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![-2, 1, -1, 2], ![3, -1, -1, -1]]

def raw7099step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 2, -2]]

def raw7100 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -2, 1, 0]]

def raw7100step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![-2, 1, 0, 1], ![3, -1, -2, 0]]

def raw7100step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def raw7101 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 1, -1], ![1, 0, 1, -2]]

def raw7101step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![1, 1, -2]]

def raw7102 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 0, 0, 0], ![1, 0, 0, -1]]

def raw7102step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![1, 0, 0, -1]]

def raw7102step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![1, 0, -1]]

def raw7103 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 0, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical222
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7104 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, -1, 1]]

def raw7105 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -2, 1, 0]]

def raw7106 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![1, 0, 0, -1]]

def raw7106step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![1, 0, -1]]

def raw7107 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw7108 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 3, -3], ![1, 0, -1, 0]]

def raw7108step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 3, -3], ![1, -1, 0]]

def raw7109 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 4, -4], ![1, 0, -2, 1]]

def raw7109step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 4, -4], ![1, -2, 1]]

def raw7110 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, -2, 1], ![1, -1, 4, -4]]

def raw7110step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-2, -2, 4], ![3, 1, -4]]

def raw7110step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![1, 0, -1], ![1, 3, -4]]

def raw7111 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 3, -2]]

def raw7111step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![-2, -1, 0, 3], ![3, 0, -1, -2]]

def raw7111step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, -1, -1, 2], ![2, 1, 0, -3], ![-3, 0, 1, 2]]

def raw7111step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -3, 2], ![1, 0, 2, -3]]

def raw7112 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw7113 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw7114 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, -1, 0], ![1, -1, 3, -3]]

def raw7114step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-2, -1, 3], ![3, 0, -3]]

def raw7114step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1]]

def raw7115 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, 2, -1]]

def raw7115step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![-2, 0, 0, 2], ![3, -1, -1, -1]]

def raw7115step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, 1, -2, 0]]

def raw7116 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -2, 1, 0]]

def raw7116step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw7117 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, 0, -1], ![1, -1, 2, -2]]

def raw7117step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-2, 0, 2], ![3, -1, -2]]

def raw7117step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def raw7118 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, 1, -2], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw7118step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw7119 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw7119step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-2, 1, 1], ![3, -2, -1]]

def raw7119step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw7120 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw7120step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-2, 2, 0], ![3, -3, 0]]

def raw7120step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0]]

def raw7121 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def raw7121step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-2, 3, -1], ![3, -4, 1]]

def raw7121step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -1, 1], ![2, -3, 1], ![-3, 4, -1]]

def raw7121step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3]]

def raw7122 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 2, -1, -1], ![1, -2, 3, -2]]

def raw7122step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![-2, -1, 3], ![3, -1, -2]]

def raw7122step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -2, 2], ![2, 1, -3], ![-3, 1, 2]]

def raw7122step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -3, 2], ![1, 2, -3]]

def raw7123 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 2, 1, -3], ![1, -2, 1, 0]]

def raw7123step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![-2, 1, 1], ![3, -3, 0]]

def raw7123step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

def raw7124 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 2, 2, -4], ![1, -2, 0, 1]]

def raw7124step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![-2, 2, 0], ![3, -4, 1]]

def raw7124step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

def raw7125 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![1, -2, 0, 1], ![0, 2, 2, -4]]

def raw7125step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2], ![3, 1, -4]]

def raw7125step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

def raw7126 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![1, -2, 1, 0], ![0, 2, 1, -3]]

def raw7126step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -2, 2], ![-2, 1, 1], ![3, 0, -3]]

def raw7126step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

def raw7127 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![1, -2, 2, -1], ![0, 2, 0, -2]]

def raw7127step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -2, 2], ![-2, 2, 0], ![3, -1, -2]]

def raw7127step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def raw7128 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![1, -2, 3, -2], ![0, 2, -1, -1]]

def raw7128step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -2, 2], ![-2, 3, -1], ![3, -2, -1]]

def raw7128step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, 2, -2], ![2, -3, 1], ![-3, 2, 1]]

def raw7128step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -3, 2], ![1, 2, -3]]

def raw7129 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![1, -1, 1, -1], ![0, 1, 1, -2]]

def raw7129step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![-2, 1, 1], ![3, -1, -2]]

def raw7129step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw7130 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![1, -1, 4, -4], ![0, 1, -2, 1]]

def raw7130step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![-2, 4, -2], ![3, -4, 1]]

def raw7130step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![1, 0, -1], ![1, 3, -4]]

def raw7131 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, -1, 1, 1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw7131step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw7132 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw7132step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 1, -2], ![1, 0, 1, -2], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, -3, 4]]

def raw7132step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -3, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw7133 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 0, -1, 2], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw7133step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 1, -2], ![1, 0, 1, -2], ![0, -1, -3, 4], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw7133step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw7134 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 0, 2, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw7134step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![1, 0, -2, 1], ![-1, 1, -1, 1], ![-1, -1, 2, 0]]

def raw7134step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw7135 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 0, 3, -2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw7135step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 1, -2], ![1, 0, -3, 2], ![0, -1, 2, -1], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw7135step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical223
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7136 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 0, 3, -2], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def raw7136step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![1, 0, -3, 2], ![-1, 1, 1, -1], ![-1, -1, 1, 1]]

def raw7136step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -3, 2], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw7137 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 0, 3, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw7137step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![1, 0, -3, 2], ![-1, 1, 0, 0], ![-1, -1, 2, 0]]

def raw7137step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw7138 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, -2, 2], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw7138step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -1, 0], ![-1, -2, 0, 3], ![2, 2, 0, -4]]

def raw7138step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -2, 3], ![0, 2, 2, -4], ![1, -1, -1, 1]]

def raw7139 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, -2, 2], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def raw7139step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -1, 0], ![-1, -2, 3, 0], ![2, 2, -3, -1]]

def raw7139step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![0, -1, 1, 0], ![1, 2, -3, 0], ![-2, -2, 3, 1]]

def raw7139step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -2, -2, 3]]

def raw7140 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, -1, 1], ![1, -1, -1, 1], ![1, 0, 3, -4]]

def raw7140step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def raw7141 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, -1, 1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw7141step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, -1, -1, 1]]

def raw7142 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, -1, 1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw7142step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -1, 0], ![-1, -1, 3, -1], ![2, 1, -3, 0]]

def raw7142step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw7143 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, -1, 1], ![1, 0, 0, -1], ![1, -1, 2, -2]]

def raw7143step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![1, -1, 1, -1], ![-1, 0, 0, 1], ![-1, 1, -2, 2]]

def raw7143step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, -1, -2, 2]]

def raw7144 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, 1, -1], ![1, -1, 2, -2], ![1, 0, -2, 1]]

def raw7144step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, -1, -1, 1]]

def raw7145 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw7145step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def raw7146 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, 3, -3], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw7147 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, 3, -3], ![0, 1, -2, 1], ![2, -2, 0, 0]]

def raw7147step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 1, -2], ![-1, 3, -2, 0], ![2, -3, 1, 0]]

def raw7147step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 0, -2, 1], ![1, 2, 0, -3]]

def raw7148 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, 3, -3], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw7149 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, 3, -3], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, -1, 1]]

def raw7149step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, 3, -3], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw7150 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, 3, -3], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw7150step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -1, 0], ![-1, 3, -1, -1], ![2, -3, 1, 0]]

def raw7150step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 0, 1], ![0, 1, 2, -3], ![1, 1, -1, -1]]

def raw7151 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, 3, -3], ![1, 0, -2, 1], ![1, -1, 0, 0]]

def raw7151step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, 0, -1], ![-1, 3, -2, 0], ![2, -3, 1, 0]]

def raw7151step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![0, -1, 0, 1], ![1, -3, 2, 0], ![-2, 3, -1, 0]]

def raw7151step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw7152 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 2, -2, 1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def raw7152step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![1, -2, 2, -1], ![-1, 1, -1, 1], ![-1, 1, -2, 2]]

def raw7152step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def raw7153 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 2, 2, -3], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw7153step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 2, -1, -1], ![-1, 2, -1, 0], ![2, -3, 1, 0]]

def raw7153step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, 1, -1, -1]]

def raw7154 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 0, 2], ![0, 1, 3, -4], ![1, 1, -2, 0]]

def raw7154step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 2, 0, -2], ![0, -1, -3, 4], ![-1, -1, 2, 0]]

def raw7154step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw7155 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 0, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw7155step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -1, 0, 0]]

def raw7156 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 1, -2, 1], ![1, 1, 2, -4]]

def raw7156step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 2, -1, -1], ![0, -1, 2, -1], ![-1, -1, -2, 4]]

def raw7156step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw7157 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw7158 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 1, 2, -3], ![1, 1, -2, 0]]

def raw7158step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 2, -1, -1], ![0, -1, -2, 3], ![-1, -1, 2, 0]]

def raw7158step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, 0, -2, 1]]

def raw7159 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw7159step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw7160 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw7161 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 2, 0], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw7161step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw7162 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 2, 0], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw7162step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw7163 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 2, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw7164 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 3, -1], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def raw7164step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 2, -3, 1], ![0, -1, 2, -1], ![-1, -1, 0, 2]]

def raw7164step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -3, 1], ![1, 0, 1, -2]]

def raw7165 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 3, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw7165step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 2, -3, 1], ![0, -2, 2, 0], ![-1, 0, 0, 1]]

def raw7165step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, 0, 2], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw7166 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw7167 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, 0, 3, -4]]

def raw7167step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 1, 1, -2], ![0, -1, 1, 0], ![-1, 0, -3, 4]]

def raw7167step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical224
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7168 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def raw7168step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 1, 1, -2], ![0, -1, -2, 3], ![-1, 0, 0, 1]]

def raw7168step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw7169 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def raw7169step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 1, 1, -2], ![0, -1, -3, 4], ![-1, 0, 1, 0]]

def raw7169step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw7170 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, -1, 0, 0]]

def raw7170step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw7171 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 0, 1], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw7171step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 1, 0, -1], ![0, -1, -2, 3], ![-1, 0, 1, 0]]

def raw7171step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw7172 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 0, 1], ![0, 2, 2, -4], ![1, -1, -1, 1]]

def raw7172step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![-1, 0, 2, -1], ![2, 1, -4, 1]]

def raw7172step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, -2, 1], ![1, 0, -2, 1], ![-2, -1, 4, -1]]

def raw7172step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw7173 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw7173step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 1, -1, 0], ![0, 0, 1, -1], ![0, -1, -2, 3], ![-1, 0, 1, 0]]

def raw7173step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw7174 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 0, 2, -2], ![1, 0, -1, 0]]

def raw7174step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 1, -1, 0], ![0, -1, 1, 0], ![0, 0, -2, 2], ![-1, 0, 1, 0]]

def raw7174step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw7175 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1]]

def raw7176 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 0, -2, 2], ![1, 1, 1, -3]]

def raw7176step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 1, -2, 1], ![0, 0, 2, -2], ![-1, -1, -1, 3]]

def raw7176step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 1, -2]]

def raw7177 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw7178 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw7179 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, -1, 1, -1]]

def raw7179step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw7180 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def raw7180step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw7181 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![1, 1, -1, -1]]

def raw7181step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 2, -1], ![2, -1, -1]]

def raw7181step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![-2, 1, 1]]

def raw7181step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]

def raw7182 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw7182step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw7183 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, 0, -2, 1]]

def raw7183step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw7184 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 3, -2], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw7184step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 1, -3, 2], ![0, -2, 2, 0], ![-1, 1, 0, 0]]

def raw7184step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -2, 0, 1]]

def raw7185 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw7186 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 3, -2], ![1, 1, -2, 0]]

def raw7186step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 3, -2], ![2, -2, 0]]

def raw7186step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw7187 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, 0, 0, -1]]

def raw7187step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

def raw7188 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 3, -3]]

def raw7189 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw7189step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 0, 2, -2], ![0, -1, -3, 4], ![-1, 1, 0, 0]]

def raw7189step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw7190 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -2, 3, -2]]

def raw7191 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![1, 0, 3, -4]]

def raw7191step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 0, 2, -2], ![-1, 0, -3, 4]]

def raw7191step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-1, -3, 4]]

def raw7191step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![1, 1, -2]]

def raw7192 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw7192step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, -3, 4], ![-1, 1, 0, 0]]

def raw7192step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw7193 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-1, -1, 2, 0], ![1, 2, 1, -4]]

def raw7193step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![1, 1, -2, 0], ![-1, -2, -1, 4]]

def raw7193step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw7194 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 0, 3, -3], ![1, -1, 0, 0]]

def raw7194step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw7195 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw7196 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw7197 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-1, -1, 1, 1], ![1, 1, 2, -4]]

def raw7197step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![1, 1, -1, -1], ![-1, -1, -2, 4]]

def raw7197step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw7198 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 2, -2]]

def raw7199 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw7199step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![-1, -1, 2, 0], ![2, 1, -3, 0]]

def raw7199step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, -1, 1], ![1, 1, -2, 0], ![-2, -1, 3, 0]]

def raw7199step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical225
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7200 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def raw7200step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 0, 1, -1], ![0, -1, -3, 4], ![-1, 1, 1, -1]]

def raw7200step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw7201 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -2, 3, -2]]

def raw7201step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![-1, -1, -1, 3], ![2, 1, -1, -2]]

def raw7201step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, -2, 2], ![1, 1, 1, -3], ![-2, -1, 1, 2]]

def raw7201step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 1, 1, -3]]

def raw7202 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -2, 0, 1]]

def raw7202step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![-1, -1, 2, 0], ![2, 1, -4, 1]]

def raw7202step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, -2, 2], ![1, 1, -2, 0], ![-2, -1, 4, -1]]

def raw7202step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

def raw7203 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 1, -1, 1], ![0, 1, 3, -4]]

def raw7203step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![1, -1, 1, -1], ![0, -1, -3, 4]]

def raw7203step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 1, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw7204 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 1, 1], ![0, 2, 2, -4]]

def raw7204step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, 1, -1, -1], ![0, -2, -2, 4]]

def raw7204step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw7205 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 0, 0], ![0, 1, 2, -3], ![1, -1, -1, 1]]

def raw7205step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![-1, 0, 2, -1], ![2, 0, -3, 1]]

def raw7205step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, -1, 1], ![1, 0, -2, 1], ![-2, 0, 3, -1]]

def raw7205step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -1, 1], ![1, -2, 1], ![-2, 3, -1]]

def raw7205step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw7206 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 0, 0], ![1, 0, 1, -2]]

def raw7206step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2]]

def raw7206step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![2, 0, -2]]

def raw7206step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw7206step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw7207 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 0, 0, 0], ![1, 0, 0, -1]]

def raw7207step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![1, 0, 0, -1]]

def raw7207step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![1, 0, -1]]

def raw7208 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw7209 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, -1, 0]]

def raw7209step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw7210 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 1, -1]]

def raw7211 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0]]

def raw7211step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw7212 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -2, 1, 0]]

def raw7212step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 0, -1, 1], ![0, -2, 1, 1], ![-1, 2, -1, 0]]

def raw7212step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw7213 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![1, 0, 0, -1]]

def raw7213step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![1, 0, -1]]

def raw7214 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, 1, -1]]

def raw7215 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw7216 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1]]

def raw7217 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -2, 1, 0]]

def raw7217step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -2, 0, 1]]

def raw7218 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![1, 0, -1, 0]]

def raw7218step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -1, 0]]

def raw7219 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -1, 0, 0]]

def raw7220 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 0, 1]]

def raw7221 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, -1, 1]]

def raw7222 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -2, 0, 1]]

def raw7223 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![1, 0, -2, 1]]

def raw7223step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -2, 1]]

def raw7224 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 0, 1, -1], ![1, -1, 2, -2]]

def raw7224step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 2, -2]]

def raw7225 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 0, 3, -3], ![1, -1, 0, 0]]

def raw7225step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -1, 0, 0]]

def raw7226 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -2, 3, -2]]

def raw7226step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![-1, -2, 0, 3], ![2, 1, -1, -2]]

def raw7226step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, -1, -1, 2], ![1, 2, 0, -3], ![-2, -1, 1, 2]]

def raw7226step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -2, 2]]

def raw7227 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -2, 2, -1]]

def raw7228 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw7229 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw7230 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![1, -1, 1, -1], ![0, 0, 2, -2]]

def raw7230step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, 1, -1]]

def raw7231 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![1, -1, 3, -3]]

def raw7231step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-1, -2, 3], ![2, 1, -3]]

def raw7231step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical226
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7232 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 0, 3, -3], ![1, -1, -1, 1]]

def raw7232step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, -1, 1]]

def raw7233 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 3, -2]]

def raw7233step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![-1, -1, -1, 3], ![2, 0, 0, -2]]

def raw7233step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def raw7234 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-1, -1, 0, 2], ![1, 0, 3, -4]]

def raw7234step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw7235 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 2, -1]]

def raw7235step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![-1, -1, 0, 2], ![2, 0, -1, -1]]

def raw7235step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, -1, -1, 2], ![1, 1, 0, -2], ![-2, 0, 1, 1]]

def raw7235step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 1, -2]]

def raw7236 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -2, 1, 0]]

def raw7236step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw7237 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -2, 0, 1]]

def raw7237step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw7238 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, -1, 2]]

def raw7238step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![-1, -1, 3, -1], ![2, 0, -4, 2]]

def raw7238step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw7239 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 0, -1, 2], ![0, 1, 3, -4]]

def raw7239step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![1, 0, 1, -2], ![0, -1, -3, 4]]

def raw7239step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 0, 1, 0], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw7240 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 0, 2], ![0, 1, 3, -4]]

def raw7240step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw7241 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -1, 0], ![1, -1, 2, -2]]

def raw7241step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-1, -1, 2], ![2, 0, -2]]

def raw7241step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

def raw7242 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, 0, -1], ![1, -1, 1, -1]]

def raw7242step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![2, -1, -1]]

def raw7242step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw7243 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw7243step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0]]

def raw7243step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0]]

def raw7244 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, 2, -3], ![0, 1, -1, 0], ![1, -2, 0, 1]]

def raw7244step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw7245 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, 2, -3], ![1, -1, -1, 1]]

def raw7245step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1], ![2, -3, 1]]

def raw7245step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -1, 1], ![1, -2, 1], ![-2, 3, -1]]

def raw7245step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw7246 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, 3, -4], ![1, -1, -2, 2]]

def raw7246step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-1, 3, -2], ![2, -4, 2]]

def raw7246step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -1, 1], ![1, -3, 2], ![-2, 4, -2]]

def raw7246step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw7247 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 2, 1, -3], ![1, -2, 0, 1]]

def raw7247step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![-1, 1, 0], ![2, -3, 1]]

def raw7247step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -2, 2], ![1, -1, 0], ![-2, 3, -1]]

def raw7247step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw7248 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 2, 2, -4], ![1, -2, -1, 2]]

def raw7248step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![-1, 2, -1], ![2, -4, 2]]

def raw7248step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -2, 2], ![1, -2, 1], ![-2, 4, -2]]

def raw7248step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def raw7249 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![1, -1, 3, -3], ![0, 1, -2, 1]]

def raw7249step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![-1, 3, -2], ![2, -3, 1]]

def raw7249step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]

def raw7250 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-3, 2, 2, -1], ![4, -2, -2, 0]]

def raw7250step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0]]

def raw7251 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, -2, 2, 2], ![3, 2, -2, -3]]

def raw7251step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -2, 2], ![0, 2, -2], ![1, 2, -3]]

def raw7252 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, -2, 3, 1], ![3, 2, -3, -2]]

def raw7252step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -2, 2], ![0, 3, -3], ![1, 1, -2]]

def raw7253 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, -2, 4, 0], ![3, 2, -4, -1]]

def raw7253step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -2, 2], ![0, 4, -4], ![1, 0, -1]]

def raw7254 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 2, 2, -2], ![3, -2, -2, 1]]

def raw7254step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1]]

def raw7255 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -3, 3, 1], ![2, 3, -3, -2]]

def raw7255step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -3, 3], ![0, 3, -3], ![1, 1, -2]]

def raw7256 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -3, 4, 0], ![2, 3, -4, -1]]

def raw7256step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -3, 3], ![0, 4, -4], ![1, 0, -1]]

def raw7257 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -2, 2, 1], ![2, 2, -2, -2]]

def raw7257step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

def raw7258 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -2, 3, 0], ![2, 2, -3, -1]]

def raw7258step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

def raw7259 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -2, 4, -1], ![2, 2, -4, 0]]

def raw7259step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 4, -4], ![1, -1, 0]]

def raw7260 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw7260step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 1, 0, -2], ![0, 1, 0, -1], ![0, -1, 1, 0], ![-1, 0, 1, 0], ![-1, -1, -2, 4]]

def raw7260step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw7261 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![2, 1, 1, -4]]

def raw7261step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 1, 0, -2], ![0, 1, -1, 0], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-2, -1, -1, 4]]

def raw7261step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw7262 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 1, -3]]

def raw7262step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 1, 0, -2], ![0, 1, -1, 0], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-2, 0, -1, 3]]

def raw7262step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw7263 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw7263step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 1, 0, -2], ![0, 1, -1, 0], ![0, -1, 1, 0], ![-1, 0, 1, 0], ![-1, -1, -1, 3]]

def raw7263step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 1, 0], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical227
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7264 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 2, 2, -5]]

def raw7264step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 1, 0, -2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, -2, -2, 5]]

def raw7264step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw7265 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw7265step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 1, 0, -2], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, -1, -2, 4]]

def raw7265step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw7266 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 0, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, 2, -4]]

def raw7266step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 1, 0, -2], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![0, -2, -2, 4]]

def raw7266step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw7267 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw7267step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 1, 0, -2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, -2, 3]]

def raw7267step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw7268 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 0, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 1, 2, -3]]

def raw7268step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 1, 0, -2], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![0, -1, -2, 3]]

def raw7268step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw7269 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw7269step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0]]

def raw7270 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 1, 1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw7270step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1]]

def raw7271 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, -1, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![0, 2, 2, -4]]

def raw7271step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 0, 1, -2], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![0, -2, -2, 4]]

def raw7271step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw7272 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![0, 1, 2, -3]]

def raw7272step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 0, 1, -2], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![0, -1, -2, 3]]

def raw7272step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw7273 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw7273step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw7274 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, -2, 2], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw7274step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -1, 0], ![0, -2, 3, -1], ![1, 2, -3, 0]]

def raw7274step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![0, -1, 1, 0], ![0, 2, -3, 1], ![-1, -2, 3, 0]]

def raw7274step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -1, 1, -1]]

def raw7275 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, -1, 1], ![1, -1, 3, -3], ![1, 0, -2, 1]]

def raw7275step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -1, 0], ![0, -1, 3, -2], ![1, 1, -3, 1]]

def raw7275step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![0, -1, 1, 0], ![0, 1, -3, 2], ![-1, -1, 3, -1]]

def raw7275step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 0, 1], ![0, 1, 2, -3], ![1, 1, -1, -1]]

def raw7276 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -3, 3, 0], ![1, 3, -3, -1]]

def raw7276step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 3, -3], ![1, 0, -1]]

def raw7277 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -3, 4, -1], ![1, 3, -4, 0]]

def raw7277step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 4, -4], ![1, -1, 0]]

def raw7278 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw7278step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 2, -1, -1], ![0, -1, -1, 2], ![-1, -1, 2, 0]]

def raw7278step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw7279 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def raw7279step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 2, -1, -1], ![0, -2, 2, 0], ![-1, 0, -1, 2]]

def raw7279step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw7280 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw7280step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 2, -2, 0], ![0, -2, 0, 2], ![-1, 0, 2, -1]]

def raw7280step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw7281 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![1, 2, -2, -1]]

def raw7281step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

def raw7282 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 3, -1], ![1, 2, -3, 0]]

def raw7282step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0]]

def raw7283 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 4, -2], ![1, 2, -4, 1]]

def raw7283step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 4, -4], ![1, -2, 1]]

def raw7283step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 2, -2], ![0, -4, 4], ![-1, 2, -1]]

def raw7283step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 4, -4], ![1, -1, 0]]

def raw7284 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, -2, 3], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def raw7284step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 0, 1], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def raw7285 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, -2, 3], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def raw7285step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 2, -3], ![0, -1, -3, 4], ![-1, 0, 1, 0]]

def raw7285step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def raw7286 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, -1, 2], ![0, 1, -2, 1], ![1, 0, 3, -4]]

def raw7286step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 1, -2], ![0, -1, 2, -1], ![-1, 0, -3, 4]]

def raw7286step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw7287 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def raw7287step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 1, -2], ![0, -1, 1, 0], ![-1, 0, -2, 3]]

def raw7287step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw7288 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw7288step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 1, 0, -2]]

def raw7289 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, 0, -2, 1]]

def raw7289step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 1, -2], ![0, -1, -3, 4], ![-1, 0, 2, -1]]

def raw7289step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw7290 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![-1, -1, 0, 2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw7290step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![1, 1, 0, -2], ![0, -1, 1, 0], ![-1, 0, 1, 0], ![-1, -1, -2, 4]]

def raw7290step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw7291 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![2, 1, 1, -4]]

def raw7291step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![1, 1, -1, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-2, -1, -1, 4]]

def raw7291step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw7292 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![-1, -1, 1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 1, -3]]

def raw7292step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![1, 1, -1, -1], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-2, 0, -1, 3]]

def raw7292step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw7293 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![-1, -1, 1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw7293step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![1, 1, -1, -1], ![0, -1, 1, 0], ![-1, 0, 1, 0], ![-1, -1, -1, 3]]

def raw7293step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 1, 0], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw7294 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![-1, 0, -1, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 2, 2, -5]]

def raw7294step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, -2, -2, 5]]

def raw7294step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw7295 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw7295step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, -1, -2, 4]]

def raw7295step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical228
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7296 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![-1, 0, -1, 2], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, 2, -4]]

def raw7296step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![0, -2, -2, 4]]

def raw7296step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw7297 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw7297step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, -2, 3]]

def raw7297step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw7298 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![-1, 1, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 1, 2, -3]]

def raw7298step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![0, -1, -2, 3]]

def raw7298step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw7299 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 1, -1, 1], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw7299step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![-1, 0, 1, 0], ![-1, -1, -2, 4]]

def raw7299step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw7300 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 0, -1, 1], ![1, 1, 2, -4]]

def raw7300step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![0, -1, 1, 0], ![0, 0, 1, -1], ![-1, -1, -2, 4]]

def raw7300step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw7301 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![0, 1, 2, -3]]

def raw7301step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw7302 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![2, 1, 1, -4]]

def raw7302step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, 0, 1, -2], ![0, -1, 1, 0], ![-2, -1, -1, 4]]

def raw7302step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw7303 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![2, 0, 1, -3]]

def raw7303step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![0, -1, 1, 0], ![-2, 0, -1, 3]]

def raw7303step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw7304 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![-1, 1, -1, 1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw7304step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![-1, 0, 1, 0], ![-1, -1, -1, 3]]

def raw7304step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw7305 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![-1, 1, -1, 1], ![2, 1, 1, -4]]

def raw7305step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![0, 0, 1, -1], ![1, -1, 1, -1], ![-2, -1, -1, 4]]

def raw7305step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw7306 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 1, 1, -3]]

def raw7306step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-1, -1, -1, 3]]

def raw7306step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw7307 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![-1, 1, -1, 1], ![2, 0, 1, -3]]

def raw7307step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![0, -1, 1, 0], ![1, -1, 1, -1], ![-2, 0, -1, 3]]

def raw7307step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw7308 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 0, -1, 1], ![1, 1, 1, -3]]

def raw7308step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![0, -1, 1, 0], ![0, 0, 1, -1], ![-1, -1, -1, 3]]

def raw7308step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw7309 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw7309step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-1, 0, -1, 2]]

def raw7309step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw7310 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![0, 1, 1, -2]]

def raw7310step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw7311 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![-1, 0, -1, 2], ![1, -1, 0, 0], ![1, 2, 2, -5]]

def raw7311step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, 0, 1, -1], ![1, 0, 1, -2], ![-1, 1, 0, 0], ![-1, -2, -2, 5]]

def raw7311step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw7312 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![-1, 1, -1, 1], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw7312step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![-1, 1, 0, 0], ![-1, -1, -2, 4]]

def raw7312step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw7313 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, -1, 0, 1], ![1, 0, -1, 0], ![0, 2, 2, -4]]

def raw7313step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw7314 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -1, 0, 1], ![1, 2, 2, -5]]

def raw7314step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-1, -2, -2, 5]]

def raw7314step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw7315 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![0, 2, 2, -4]]

def raw7315step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw7316 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, -1, 0, 1], ![1, 1, 2, -4]]

def raw7316step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![0, 1, 0, -1], ![-1, -1, -2, 4]]

def raw7316step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw7317 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![0, 1, 2, -3]]

def raw7317step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw7318 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![0, 0, -1, 1], ![0, 2, 2, -4]]

def raw7318step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw7319 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, 2, 2, -3]]

def raw7319step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, -2, -2, 3]]

def raw7319step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw7320 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![-1, 1, -1, 1], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw7320step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, -1, 1, 0], ![1, -1, 1, -1], ![-1, 1, 0, 0], ![-1, 0, -2, 3]]

def raw7320step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw7321 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, -1, 0, 1], ![1, 0, -1, 0], ![0, 1, 2, -3]]

def raw7321step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw7322 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![0, -1, 0, 1], ![1, 0, 2, -3]]

def raw7322step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, 0, -1], ![-1, 0, -2, 3]]

def raw7322step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw7323 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![0, 0, 2, -2]]

def raw7323step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![0, 0, -2, 2]]

def raw7323step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw7324 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![0, 0, -1, 1], ![0, 1, 2, -3]]

def raw7324step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw7325 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, 1, 2, -2]]

def raw7325step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw7326 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 3, -2], ![0, 0, -2, 2], ![1, 1, -1, -1]]

def raw7326step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, -3, 2], ![0, 0, 2, -2], ![-1, -1, 1, 1]]

def raw7326step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def raw7327 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 3, -2], ![0, 1, -3, 2], ![1, 0, 0, -1]]

def raw7327step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical229
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7328 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -3, 3], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw7328step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, 3, -3], ![0, -1, -3, 4], ![-1, 1, 0, 0]]

def raw7328step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -1, 0, 0]]

def raw7329 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -3, 3], ![1, 0, 3, -4]]

def raw7329step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, 3, -3], ![-1, 0, -3, 4]]

def raw7329step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 0, -1], ![0, 3, -3], ![-1, -3, 4]]

def raw7329step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 3, -3], ![1, 0, -1]]

def raw7330 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw7330step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, 2, -2], ![0, -1, -2, 3], ![-1, 1, 0, 0]]

def raw7330step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 0, 0]]

def raw7331 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def raw7331step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, 2, -2], ![0, -1, -3, 4], ![-1, 1, 1, -1]]

def raw7331step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 1, -1]]

def raw7332 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -2, 2], ![0, 2, -1, -1], ![1, -2, 3, -2]]

def raw7332step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![0, -2, -1, 3], ![1, 2, -1, -2]]

def raw7332step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, -2, 2], ![0, 2, 1, -3], ![-1, -2, 1, 2]]

def raw7332step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw7333 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -2, 2], ![1, 0, 2, -3]]

def raw7333step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, 2, -2], ![-1, 0, -2, 3]]

def raw7333step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 0, -1], ![0, 2, -2], ![-1, -2, 3]]

def raw7333step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![1, 0, -1]]

def raw7334 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![-1, 0, -1, 2], ![1, -1, 0, 0], ![1, -1, 0, 0], ![0, 2, 2, -4]]

def raw7334step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, 1, -1], ![1, 0, 1, -2], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![0, -2, -2, 4]]

def raw7334step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw7335 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![-1, 1, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![0, 1, 2, -3]]

def raw7335step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![0, -1, -2, 3]]

def raw7335step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw7336 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -1, 0, 1], ![1, -1, 0, 0], ![0, 2, 2, -4]]

def raw7336step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw7337 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -2, 0, 1]]

def raw7337step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw7338 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![0, -1, 0, 1], ![0, 2, 2, -4]]

def raw7338step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw7339 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 2, 2, -3]]

def raw7339step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![1, -2, -2, 3]]

def raw7339step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw7340 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, -1, 0, 1], ![1, -1, 0, 0], ![0, 1, 2, -3]]

def raw7340step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw7341 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![0, -1, 0, 1], ![0, 1, 2, -3]]

def raw7341step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw7342 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 1, 2, -2]]

def raw7342step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw7343 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -2, 0, 1]]

def raw7343step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![0, -1, 1, 0], ![1, 1, -3, 1]]

def raw7343step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![-1, -1, 3, -1]]

def raw7343step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw7344 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -2, -1, 2]]

def raw7344step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![0, -1, 2, -1], ![1, 1, -4, 2]]

def raw7344step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, -2, 2], ![0, 1, -2, 1], ![-1, -1, 4, -2]]

def raw7344step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw7345 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw7345step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw7346 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![-1, 1, -1, 1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw7346step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw7347 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![0, -1, 0, 1], ![1, -1, 1, -1]]

def raw7347step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, -1, 1], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, 0, -1], ![-1, 1, -1, 1]]

def raw7347step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw7348 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![0, -1, 1, 0]]

def raw7348step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw7349 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw7349step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw7350 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -2, -1, 2]]

def raw7350step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, -1, 1], ![0, -2, 0, 2], ![-1, 2, 1, -2]]

def raw7350step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 2, -2]]

def raw7351 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw7351step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, -2, 2], ![0, -1, 0, 1], ![-1, 1, 2, -2]]

def raw7351step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 2, -2]]

def raw7352 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, -3, 2], ![1, -1, 3, -3]]

def raw7352step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![0, -3, 3], ![1, 2, -3]]

def raw7352step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -1, 1], ![0, 3, -3], ![-1, -2, 3]]

def raw7352step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1]]

def raw7353 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, -2, 1], ![1, -1, 2, -2]]

def raw7353step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![1, 1, -2]]

def raw7353step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -1, 1], ![0, 2, -2], ![-1, -1, 2]]

def raw7353step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

def raw7354 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, -1, 0], ![1, -1, 1, -1]]

def raw7354step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1]]

def raw7354step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]

def raw7355 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -2, -1, 2]]

def raw7355step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, -1, 0, 1], ![0, -1, -1, 2], ![-1, 2, 1, -2]]

def raw7355step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 2, -2]]

def raw7356 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 2, -3], ![1, -1, -2, 2]]

def raw7356step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2]]

def raw7356step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 3, -2]]

def raw7356step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def raw7357 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, -3, 3, -1], ![0, 3, -3, 0]]

def raw7357step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -3, 3], ![0, 3, -3], ![1, -1, 0]]

def raw7357step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 3, -3], ![1, 0, -1]]

def raw7358 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, -2, 2, -1], ![0, 2, -2, 0]]

def raw7358step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0]]

def raw7358step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

def raw7359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]

def raw7359step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![2, 0, -2], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-2, -3, 5]]

def raw7359step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]

def raw737 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]

def raw738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw739 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]

def raw740 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

def raw741 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]

def raw742 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 3, -4]]

def raw743 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]

def raw744 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]

def raw745 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -2, 1], ![1, 3, -4]]

def raw745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 3, -4]]

def raw746 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

def raw747 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]

def raw747step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw748 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]

def raw748step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-2, -1, 3]]

def raw748step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1]]

def raw750 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]

def raw750step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]

def raw750step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

def raw751 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]

def raw752 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]

def raw752step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]

def raw752step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

def raw753 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

def raw753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 0, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]

def raw753step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]

def raw753step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw754 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]

def raw754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]

def raw754step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]

def raw754step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw755 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]

def raw755step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 0, 3], ![1, 0, 1, -2], ![2, 0, -1, -1]]

def raw755step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]

def raw755step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -2, 1]]

def raw756 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

def raw757 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical230
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]

def raw7360step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -3, 4]]

def raw7360step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw7361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]

def raw7361step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-2, -2, 4]]

def raw7361step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def raw7362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![2, 1, -3]]

def raw7362step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![-2, -1, 3]]

def raw7362step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

def raw7363 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def raw7363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def raw7364 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw7364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw7365 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

def raw7365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

def raw7366 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 3, -4]]

def raw7366step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 2, -3], ![-1, 1, 0], ![-1, -3, 4]]

def raw7366step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3]]

def raw7367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 4, -5]]

def raw7367step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, 1, -2], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -4, 5]]

def raw7367step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -4, 5], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw7368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw7368step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, 1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -2, 3]]

def raw7368step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw7369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 4, -4]]

def raw7369step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

def raw7370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![0, 3, -3]]

def raw7370step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw7371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw7371step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw7372 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw7372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw7373 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw7373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]

def raw7373step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw7374 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw7374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw7375 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw7375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw7376 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 3, -4]]

def raw7376step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 1, -2], ![-1, 2, -1], ![-1, -3, 4]]

def raw7376step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2]]

def raw7377 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2]]

def raw7377step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

def raw7378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]

def raw7378step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-2, -3, 5]]

def raw7378step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw7379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]

def raw7379step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -3, 4]]

def raw7379step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

def raw7380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2], ![1, -1, 0], ![2, 3, -5]]

def raw7380step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, 1, -2], ![-1, 1, 0], ![-2, -3, 5]]

def raw7380step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw7381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 3, -5]]

def raw7381step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, -3, 5]]

def raw7381step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw7382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def raw7382step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -3, 4]]

def raw7382step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw7383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![0, -1, 1], ![1, 3, -4]]

def raw7383step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, -3, 4]]

def raw7383step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw7384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 3, -3]]

def raw7384step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw7385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]

def raw7387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]

def raw7387step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-2, -2, 4]]

def raw7387step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw7388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![2, 1, -3]]

def raw7388step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]

def raw7389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2], ![1, -1, 0], ![2, 2, -4]]

def raw7389step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![-1, 1, 0], ![-2, -2, 4]]

def raw7389step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw7390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 2, -4]]

def raw7390step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, -2, 4]]

def raw7390step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw7391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]

def raw7391step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -2, 3]]

def raw7391step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical231
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw7393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]

def raw7393step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![-2, -1, 3]]

def raw7393step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw7394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![-1, -2, 3], ![2, 1, -3]]

def raw7394step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

def raw7395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2]]

def raw7395step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![-1, -1, 2]]

def raw7395step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw7396 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]

def raw7396step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw7397 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1]]

def raw7397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, -1, 0], ![0, -2, 2], ![-1, 3, -2], ![-1, 0, 1]]

def raw7397step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw7398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![-1, 3, -2], ![1, -3, 2]]

def raw7398step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

def raw7399 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]

def raw7399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw7400 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 3, -2], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1]]

def raw7400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, -3, 2], ![0, 3, -3], ![-1, 0, 1], ![-1, 0, 1]]

def raw7400step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

def raw7401 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 3, -2], ![1, -3, 2], ![1, 0, -1]]

def raw7401step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3]]

def raw7402 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 4, -3], ![1, -2, 1], ![1, -2, 1]]

def raw7402step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2]]

def raw7403 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1]]

def raw7403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![0, 3, -3], ![1, -3, 2], ![-1, 0, 1], ![-1, 0, 1]]

def raw7403step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

def raw7404 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 2, -2], ![1, 1, -2]]

def raw7404step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 3, -3], ![0, -2, 2], ![-1, -1, 2]]

def raw7404step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

def raw7405 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1]]

def raw7405step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 3, -3], ![1, 0, -1]]

def raw7406 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 3, -3], ![1, 0, -1]]

def raw7407 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 3, -3], ![1, 0, -1], ![0, 0, 0]]

def raw7407step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 3, -3], ![1, 0, -1]]

def raw7408 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![1, 3, -4]]

def raw7408step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 0, -1], ![0, 3, -3], ![-1, -3, 4]]

def raw7408step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 3, -3], ![1, 0, -1]]

def raw7409 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1]]

def raw7409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw7410 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![-1, 4, -3], ![1, -1, 0], ![1, -1, 0]]

def raw7410step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw7411 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2]]

def raw7411step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2]]

def raw7411step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

def raw7412 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

def raw7413 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1]]

def raw7413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![0, 2, -2], ![0, -3, 3], ![0, 1, -1], ![-1, 0, 1]]

def raw7413step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

def raw7415 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![0, 0, 0]]

def raw7415step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0]]

def raw7416 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 4, -4], ![0, -1, 1], ![1, -1, 0]]

def raw7416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0]]

def raw7417 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 4, -4], ![1, -2, 1]]

def raw7417step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 2, -2], ![0, -4, 4], ![-1, 2, -1]]

def raw7417step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 4, -4], ![1, -1, 0]]

def raw7418 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 4, -4], ![1, -1, 0], ![0, -1, 1]]

def raw7418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0]]

def raw7419 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![1, 2, -3]]

def raw7419step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 0, -1], ![0, 2, -2], ![-1, -2, 3]]

def raw7419step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![1, 0, -1]]

def raw7420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 4, -5]]

def raw7420step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![0, 1, -1], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, -4, 5]]

def raw7420step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -4, 5], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw7421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw7421step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![0, 1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, -2, 3]]

def raw7421step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw7422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![0, 4, -4]]

def raw7422step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

def raw7423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![0, 3, -3]]

def raw7423step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical232
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw7424step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw7425 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 3, -2], ![1, -2, 1], ![1, 0, -1]]

def raw7425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw7426 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0]]

def raw7426step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw7427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 4, -5]]

def raw7427step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, -4, 5]]

def raw7427step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -4, 5], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw7428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3]]

def raw7428step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]

def raw7428step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw7429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 4, -5]]

def raw7429step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, -4, 5]]

def raw7429step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw7430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 4, -4]]

def raw7430step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0]]

def raw7431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 3, -3]]

def raw7431step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![0, -3, 3]]

def raw7431step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw7432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3]]

def raw7432step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![-1, -2, 3]]

def raw7432step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw7433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 2, -2]]

def raw7433step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def raw7434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![0, -1, 1], ![0, 4, -4]]

def raw7434step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0]]

def raw7435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 3, -3]]

def raw7435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 3, -3]]

def raw7435step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

def raw7436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![-1, 4, -3]]

def raw7436step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw7437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-1, 3, -2]]

def raw7437step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw7438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw7438step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw7439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1]]

def raw7439step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw7440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0]]

def raw7440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw7441 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![0, -2, 2], ![1, 0, -1]]

def raw7441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![0, 1, -1], ![0, -3, 3], ![0, 2, -2], ![-1, 0, 1]]

def raw7441step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

def raw7442 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0]]

def raw7442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

def raw7443 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![1, -2, 1], ![0, 0, 0]]

def raw7443step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![0, 1, -1], ![0, -3, 3], ![-1, 2, -1], ![0, 0, 0]]

def raw7443step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 1, -1], ![0, -3, 3], ![-1, 2, -1]]

def raw7443step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

def raw7444 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![0, -1, 1]]

def raw7444step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

def raw7445 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]

def raw7445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw7446 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1], ![1, -3, 2], ![1, 0, -1]]

def raw7446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![0, -1, 1], ![1, -2, 1], ![-1, 3, -2], ![-1, 0, 1]]

def raw7446step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw7447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![-1, 3, -2], ![1, -3, 2]]

def raw7447step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw7448 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0]]

def raw7448step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw7449 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1]]

def raw7449step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1]]

def raw7449step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw7450 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1]]

def raw7450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw7451 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![0, -3, 3], ![1, 0, -1]]

def raw7451step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

def raw7452 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![0, 0, 0]]

def raw7452step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 3, -2], ![0, 0, 0]]

def raw7452step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 3, -2]]

def raw7452step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def raw7453 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![1, -1, 0]]

def raw7454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 3, -2], ![1, -3, 2]]

def raw7454step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![-1, 3, -2]]

def raw7454step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![1, -3, 2], ![-1, 3, -2]]

def raw7454step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw7455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, 3, -1], ![1, -3, 2]]

def raw7455step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical233
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-1, 3, -2], ![0, -3, 3]]

def raw7456step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw7457 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![1, -2, 1]]

def raw7457step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 0, -1], ![0, -2, 2], ![-1, 2, -1]]

def raw7457step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -1, 0]]

def raw7458 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 3, -3], ![0, -3, 3], ![1, 0, -1]]

def raw7458step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 3, -3], ![1, 0, -1]]

def raw7459 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 3, -3], ![1, -3, 2]]

def raw7459step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 0, -1], ![0, -3, 3], ![-1, 3, -2]]

def raw7459step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 3, -3], ![1, -1, 0]]

def raw7460 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 3, -3], ![1, -3, 2], ![0, 0, 0]]

def raw7460step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -3, 3], ![-1, 3, -2], ![0, 0, 0]]

def raw7460step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 0, -1], ![0, -3, 3], ![-1, 3, -2]]

def raw7460step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 3, -3], ![1, -1, 0]]

def raw7461 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 4, -4], ![1, -4, 3]]

def raw7461step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 0, -1], ![0, -4, 4], ![-1, 4, -3]]

def raw7461step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 4, -4], ![1, -1, 0]]

def raw7462 : Matrix (Fin 2) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1]]

def raw7462step0 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

def raw7463 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-4, 2, 1, 1], ![5, -2, -2, -1]]

def raw7463step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 2, -2], ![1, 1, -2], ![0, 1, -1]]

def raw7463step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 1, -1], ![0, 2, -2], ![1, 1, -2]]

def raw7464 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-3, 2, -2, 3], ![4, -2, 1, -3]]

def raw7464step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![1, -2, 1], ![0, 3, -3]]

def raw7464step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![0, 3, -3], ![1, -2, 1]]

def raw7465 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-3, 3, -2, 2], ![4, -3, 1, -2]]

def raw7465step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 3, -3], ![1, -2, 1], ![0, 2, -2]]

def raw7465step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![0, 3, -3], ![1, -2, 1]]

def raw7466 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-3, 3, 1, -1], ![4, -3, -2, 1]]

def raw7466step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 3, -3], ![1, 1, -2], ![0, -1, 1]]

def raw7466step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, -1, 1], ![0, 3, -3], ![1, 1, -2]]

def raw7467 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-2, -2, 1, 3], ![3, 2, -2, -3]]

def raw7467step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -2, 2], ![1, 1, -2], ![0, 3, -3]]

def raw7467step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -2, 2], ![0, 3, -3], ![1, 1, -2]]

def raw7468 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-2, 2, -2, 2], ![3, -2, 1, -2]]

def raw7468step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![1, -2, 1], ![0, 2, -2]]

def raw7468step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1]]

def raw7469 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-2, 2, 1, -1], ![3, -2, -2, 1]]

def raw7469step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![1, 1, -2], ![0, -1, 1]]

def raw7469step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2]]

def raw7470 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-2, 3, -2, 1], ![3, -3, 1, -1]]

def raw7470step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 3, -3], ![1, -2, 1], ![0, 1, -1]]

def raw7470step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 3, -3], ![1, -2, 1]]

def raw7471 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-1, -3, 1, 3], ![2, 3, -2, -3]]

def raw7471step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -3, 3], ![1, 1, -2], ![0, 3, -3]]

def raw7471step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -3, 3], ![0, 3, -3], ![1, 1, -2]]

def raw7472 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-1, -2, -2, 5], ![2, 2, 1, -5]]

def raw7472step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![1, -2, 1], ![0, 5, -5]]

def raw7472step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 5, -5], ![1, -2, 1]]

def raw7473 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-1, -2, 1, 2], ![2, 2, -2, -2]]

def raw7473step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![1, 1, -2], ![0, 2, -2]]

def raw7473step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

def raw7474 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw7474step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, -1, 0], ![1, 1, 0, -2], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, -1, -1, 3]]

def raw7474step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw7475 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-1, -1, 0, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, 1, -3]]

def raw7475step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, -1, 0], ![1, 1, 0, -2], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![0, -2, -1, 3]]

def raw7475step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw7476 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-1, 2, -4, 3], ![2, -2, 3, -3]]

def raw7476step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -4, 3], ![0, 3, -3]]

def raw7476step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, -2, 2], ![-1, 4, -3], ![0, -3, 3]]

def raw7476step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![0, 3, -3], ![1, -2, 1]]

def raw7477 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-1, 2, -3, 2], ![2, -2, 2, -2]]

def raw7477step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -3, 2], ![0, 2, -2]]

def raw7477step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, -2, 2], ![-1, 3, -2], ![0, -2, 2]]

def raw7477step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1]]

def raw7478 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-1, 2, -2, 1], ![2, -2, 1, -1]]

def raw7478step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -2, 1], ![0, 1, -1]]

def raw7478step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1]]

def raw7479 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-1, 3, -4, 2], ![2, -3, 3, -2]]

def raw7479step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -4, 3], ![0, 2, -2]]

def raw7479step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, -3, 3], ![-1, 4, -3], ![0, -2, 2]]

def raw7479step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![0, 3, -3], ![1, -2, 1]]

def raw7480 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-1, 4, -2, -1], ![2, -4, 1, 1]]

def raw7480step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 4, -4], ![1, -2, 1], ![0, -1, 1]]

def raw7480step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 4, -4], ![1, -2, 1]]

def raw7481 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -3, 1, 2], ![1, 3, -2, -2]]

def raw7481step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![1, 1, -2], ![0, 2, -2]]

def raw7481step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 3, -3], ![-1, -1, 2], ![0, -2, 2]]

def raw7481step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

def raw7482 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, -2, 4], ![1, 2, 1, -4]]

def raw7482step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![1, -2, 1], ![0, 4, -4]]

def raw7482step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 2, -2], ![-1, 2, -1], ![0, -4, 4]]

def raw7482step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 4, -4], ![1, -1, 0]]

def raw7483 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, 1, 1], ![1, 2, -2, -1]]

def raw7483step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![1, 1, -2], ![0, 1, -1]]

def raw7483step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 2, -2], ![-1, -1, 2], ![0, -1, 1]]

def raw7483step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

def raw7484 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -3, 4], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def raw7484step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![0, 1, 3, -4], ![0, 0, -2, 2], ![-1, -1, 0, 2]]

def raw7484step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, 0, 3, -4]]

def raw7485 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -3, 4], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw7485step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw7486 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -3, 4], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def raw7486step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def raw7487 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -2, 3], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw7487step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical234
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7488 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -1, 2], ![0, 0, -2, 2], ![1, 1, 2, -4]]

def raw7488step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![0, 1, 1, -2], ![0, 0, 2, -2], ![-1, -1, -2, 4]]

def raw7488step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw7489 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw7489step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, -1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, -1, -1, 3]]

def raw7489step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw7490 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![-1, 0, -1, 2], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, 1, -3]]

def raw7490step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, -1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![0, -2, -1, 3]]

def raw7490step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw7491 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![-1, 1, -1, 1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw7491step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, -1, 0], ![0, 1, 0, -1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![-1, 1, 0, 0], ![-1, -1, -1, 3]]

def raw7491step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw7492 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, -1, 0, 1], ![1, 0, -1, 0], ![0, 2, 1, -3]]

def raw7492step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, -1, 0], ![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-1, 0, 1, 0], ![0, -2, -1, 3]]

def raw7492step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, -1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw7493 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, -1, 0, 1], ![1, 1, 1, -3]]

def raw7493step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, -1, 0], ![0, 1, 0, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![0, 1, 0, -1], ![-1, -1, -1, 3]]

def raw7493step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw7494 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![0, 1, 1, -2]]

def raw7494step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw7495 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![0, 0, -1, 1], ![0, 2, 1, -3]]

def raw7495step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, -1, 0], ![0, 1, 0, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![0, 0, 1, -1], ![0, -2, -1, 3]]

def raw7495step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -2, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0]]

def raw7496 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, 2, 1, -2]]

def raw7496step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw7497 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -3, 3], ![1, 0, 2, -3]]

def raw7497step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, -1, 0], ![0, 0, 3, -3], ![-1, 0, -2, 3]]

def raw7497step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -1, 0], ![0, 3, -3], ![-1, -2, 3]]

def raw7497step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 3, -3], ![1, -1, 0]]

def raw7498 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 1, -1]]

def raw7498step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![1, -2, 0, 1], ![0, 2, -1, -1]]

def raw7498step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw7499 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -2, 2], ![1, 0, 1, -2]]

def raw7499step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, -1, 0], ![0, 0, 2, -2], ![-1, 0, -1, 2]]

def raw7499step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -1, 0], ![0, 2, -2], ![-1, -1, 2]]

def raw7499step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -1, 0]]

def raw7500 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, -3, 2], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw7500step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw7501 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -1, 1]]

def raw7501step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![0, 0, -1, 1], ![0, -1, 1, 0], ![-1, 1, 1, -1]]

def raw7501step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw7502 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

def raw7503 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw7503step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![1, 1, 0, -2], ![0, -1, -1, 2]]

def raw7503step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw7504 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -2, -2, 3]]

def raw7504step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![1, 1, 0, -2], ![0, -1, -2, 3]]

def raw7504step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, -2, 2], ![-1, -1, 0, 2], ![0, 1, 2, -3]]

def raw7504step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def raw7505 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 1, -3, 2], ![1, -1, 2, -2]]

def raw7505step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![1, -3, 2], ![0, 2, -2]]

def raw7505step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -1, 1], ![-1, 3, -2], ![0, -2, 2]]

def raw7505step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def raw7506 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -1, 2]]

def raw7506step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![1, 0, 0, -1], ![0, -1, -1, 2]]

def raw7506step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 1, 0, -2]]

def raw7507 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 1, 1, -2], ![1, -1, -2, 2]]

def raw7507step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![0, -2, 2]]

def raw7507step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![0, 2, -2]]

def raw7507step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

def raw7508 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 1, 2, -3], ![1, -1, -3, 3]]

def raw7508step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![0, -3, 3]]

def raw7508step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -1, 1], ![-1, -2, 3], ![0, 3, -3]]

def raw7508step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1]]

def raw7509 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 2, -4, 2], ![1, -2, 3, -2]]

def raw7509step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![1, -4, 3], ![0, 2, -2]]

def raw7509step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -2, 2], ![-1, 4, -3], ![0, -2, 2]]

def raw7509step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0]]

def raw7510 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 2, -3, 1], ![1, -2, 2, -1]]

def raw7510step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![1, -3, 2], ![0, 1, -1]]

def raw7510step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -2, 2], ![-1, 3, -2], ![0, -1, 1]]

def raw7510step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def raw7511 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 2, 0, -2], ![1, -2, -1, 2]]

def raw7511step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![0, -2, 2]]

def raw7511step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

def raw7512 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 2, 1, -3], ![1, -2, -2, 3]]

def raw7512step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![0, -3, 3]]

def raw7512step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![0, 3, -3]]

def raw7512step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

def raw7513 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 3, -4, 1], ![1, -3, 3, -1]]

def raw7513step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 3, -3], ![1, -4, 3], ![0, 1, -1]]

def raw7513step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -3, 3], ![-1, 4, -3], ![0, -1, 1]]

def raw7513step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0]]

def raw7514 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 4, -2, -2], ![1, -4, 1, 2]]

def raw7514step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 4, -4], ![1, -2, 1], ![0, -2, 2]]

def raw7514step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -4, 4], ![-1, 2, -1], ![0, 2, -2]]

def raw7514step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 4, -4], ![1, -1, 0]]

def raw7515 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![1, -3, 1, 1], ![0, 3, -2, -1]]

def raw7515step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -3, 3], ![1, 1, -2], ![0, 1, -1]]

def raw7515step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, 3, -3], ![-1, -1, 2], ![0, -1, 1]]

def raw7515step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

def raw7516 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![1, -2, -2, 3], ![0, 2, 1, -3]]

def raw7516step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -2, 2], ![1, -2, 1], ![0, 3, -3]]

def raw7516step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, 2, -2], ![-1, 2, -1], ![0, -3, 3]]

def raw7516step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

def raw7517 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-3, 2, -2, 3], ![4, -2, 0, -2]]

def raw7517step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![2, -2, 0], ![-1, 3, -2]]

def raw7517step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, -2, 2], ![-2, 2, 0], ![1, -3, 2]]

def raw7517step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -4, 3], ![1, 2, -3]]

def raw7518 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-3, 2, -1, 2], ![4, -2, -1, -1]]

def raw7518step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![2, -1, -1], ![-1, 2, -1]]

def raw7518step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, -2, 2], ![-2, 1, 1], ![1, -2, 1]]

def raw7518step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -2, 1], ![1, 3, -4]]

def raw7519 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-3, 2, 0, 1], ![4, -2, -2, 0]]

def raw7519step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![2, 0, -2], ![-1, 1, 0]]

def raw7519step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, -2, 2], ![-2, 0, 2], ![1, -1, 0]]

def raw7519step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical235
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7520 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-3, 3, -1, 1], ![4, -3, -1, 0]]

def raw7520step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 3, -3], ![2, -1, -1], ![-1, 1, 0]]

def raw7520step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, -3, 3], ![-2, 1, 1], ![1, -1, 0]]

def raw7520step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, -1, 0], ![1, 3, -4]]

def raw7521 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-3, 3, 0, 0], ![4, -3, -2, 1]]

def raw7521step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 3, -3], ![2, 0, -2], ![-1, 0, 1]]

def raw7521step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, -3, 3], ![-2, 0, 2], ![1, 0, -1]]

def raw7521step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 0, -1], ![1, 3, -4]]

def raw7522 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-2, 2, -2, 2], ![3, -2, 0, -1]]

def raw7522step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![2, -2, 0], ![-1, 2, -1]]

def raw7522step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, -2, 2], ![-2, 2, 0], ![1, -2, 1]]

def raw7522step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

def raw7523 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-2, 2, -1, 1], ![3, -2, -1, 0]]

def raw7523step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![2, -1, -1], ![-1, 1, 0]]

def raw7523step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, -2, 2], ![-2, 1, 1], ![1, -1, 0]]

def raw7523step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

def raw7524 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-2, 2, 0, 0], ![3, -2, -2, 1]]

def raw7524step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![2, 0, -2], ![-1, 0, 1]]

def raw7524step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

def raw7525 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-2, 3, -1, 0], ![3, -3, -1, 1]]

def raw7525step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 3, -3], ![2, -1, -1], ![-1, 0, 1]]

def raw7525step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, -3, 3], ![-2, 1, 1], ![1, 0, -1]]

def raw7525step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 0, -1], ![1, 2, -3]]

def raw7526 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-2, 4, -2, 0], ![3, -4, 0, 1]]

def raw7526step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 4, -4], ![2, -2, 0], ![-1, 0, 1]]

def raw7526step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, -4, 4], ![-2, 2, 0], ![1, 0, -1]]

def raw7526step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![1, -3, 2], ![1, -1, 0]]

def raw7527 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, -3, 0, 4], ![2, 3, -2, -3]]

def raw7527step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -3, 3], ![2, 0, -2], ![-1, 4, -3]]

def raw7527step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 3, -3], ![-2, 0, 2], ![1, -4, 3]]

def raw7527step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -4, 3], ![1, 1, -2]]

def raw7528 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, -3, 2, 2], ![2, 3, -4, -1]]

def raw7528step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -3, 3], ![2, 2, -4], ![-1, 2, -1]]

def raw7528step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 3, -3], ![-2, -2, 4], ![1, -2, 1]]

def raw7528step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, -2, 1], ![1, 1, -2]]

def raw7529 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, -2, -2, 5], ![2, 2, 0, -4]]

def raw7529step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![2, -2, 0], ![-1, 5, -4]]

def raw7529step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-2, 2, 0], ![1, -5, 4]]

def raw7529step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -2, 1], ![1, 4, -5]]

def raw7530 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, -2, -1, 4], ![2, 2, -1, -3]]

def raw7530step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![2, -1, -1], ![-1, 4, -3]]

def raw7530step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-2, 1, 1], ![1, -4, 3]]

def raw7530step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -2, 1], ![1, 3, -4]]

def raw7531 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, -2, 0, 3], ![2, 2, -2, -2]]

def raw7531step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![2, 0, -2], ![-1, 3, -2]]

def raw7531step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-2, 0, 2], ![1, -3, 2]]

def raw7531step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

def raw7532 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, -2, 1, 2], ![2, 2, -3, -1]]

def raw7532step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![2, 1, -3], ![-1, 2, -1]]

def raw7532step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-2, -1, 3], ![1, -2, 1]]

def raw7532step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def raw7533 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, -2, 2, 1], ![2, 2, -4, 0]]

def raw7533step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![2, 2, -4], ![-1, 1, 0]]

def raw7533step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-2, -2, 4], ![1, -1, 0]]

def raw7533step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def raw7534 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, -2, 3, 0], ![2, 2, -5, 1]]

def raw7534step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![2, 3, -5], ![-1, 0, 1]]

def raw7534step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-2, -3, 5], ![1, 0, -1]]

def raw7534step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def raw7535 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, 2, -4, 3], ![2, -2, 2, -2]]

def raw7535step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![2, -4, 2], ![-1, 3, -2]]

def raw7535step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, -2, 2], ![-2, 4, -2], ![1, -3, 2]]

def raw7535step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -2, 1], ![1, 2, -3]]

def raw7536 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, 2, -3, 2], ![2, -2, 1, -1]]

def raw7536step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![2, -3, 1], ![-1, 2, -1]]

def raw7536step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, -2, 2], ![-2, 3, -1], ![1, -2, 1]]

def raw7536step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def raw7537 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, 2, -2, 1], ![2, -2, 0, 0]]

def raw7537step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![2, -2, 0], ![-1, 1, 0]]

def raw7537step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

def raw7538 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, 2, -1, 0], ![2, -2, -1, 1]]

def raw7538step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![2, -1, -1], ![-1, 0, 1]]

def raw7538step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, -2, 2], ![-2, 1, 1], ![1, 0, -1]]

def raw7538step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw7539 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, 2, 0, -1], ![2, -2, -2, 2]]

def raw7539step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![2, 0, -2], ![-1, -1, 2]]

def raw7539step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, -2, 2], ![-2, 0, 2], ![1, 1, -2]]

def raw7539step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]

def raw7540 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, 2, 1, -2], ![2, -2, -3, 3]]

def raw7540step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![2, 1, -3], ![-1, -2, 3]]

def raw7540step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, -2, 2], ![-2, -1, 3], ![1, 2, -3]]

def raw7540step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 1, -2], ![1, 2, -3]]

def raw7541 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, 3, -4, 2], ![2, -3, 2, -1]]

def raw7541step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![2, -4, 2], ![-1, 2, -1]]

def raw7541step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, -3, 3], ![-2, 4, -2], ![1, -2, 1]]

def raw7541step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, -2, 1], ![1, 1, -2]]

def raw7542 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, 3, -2, 0], ![2, -3, 0, 1]]

def raw7542step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![2, -2, 0], ![-1, 0, 1]]

def raw7542step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, -3, 3], ![-2, 2, 0], ![1, 0, -1]]

def raw7542step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

def raw7543 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, 3, -1, -1], ![2, -3, -1, 2]]

def raw7543step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![2, -1, -1], ![-1, -1, 2]]

def raw7543step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, -3, 3], ![-2, 1, 1], ![1, 1, -2]]

def raw7543step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]

def raw7544 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, 3, 0, -2], ![2, -3, -2, 3]]

def raw7544step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![2, 0, -2], ![-1, -2, 3]]

def raw7544step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, -3, 3], ![-2, 0, 2], ![1, 2, -3]]

def raw7544step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 1, -2], ![1, 2, -3]]

def raw7545 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, 4, -3, 0], ![2, -4, 1, 1]]

def raw7545step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 4, -4], ![2, -3, 1], ![-1, 0, 1]]

def raw7545step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, -4, 4], ![-2, 3, -1], ![1, 0, -1]]

def raw7545step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 4, -4], ![1, -2, 1], ![1, -1, 0]]

def raw7546 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -3, 0, 3], ![1, 3, -2, -2]]

def raw7546step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![2, 0, -2], ![-1, 3, -2]]

def raw7546step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 3, -3], ![-2, 0, 2], ![1, -3, 2]]

def raw7546step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

def raw7547 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -3, 1, 2], ![1, 3, -3, -1]]

def raw7547step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![2, 1, -3], ![-1, 2, -1]]

def raw7547step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 3, -3], ![-2, -1, 3], ![1, -2, 1]]

def raw7547step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw7548 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -3, 2, 1], ![1, 3, -4, 0]]

def raw7548step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![2, 2, -4], ![-1, 1, 0]]

def raw7548step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 3, -3], ![-2, -2, 4], ![1, -1, 0]]

def raw7548step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw7549 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, -2, 4], ![1, 2, 0, -3]]

def raw7549step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![2, -2, 0], ![-1, 4, -3]]

def raw7549step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 2, -2], ![-2, 2, 0], ![1, -4, 3]]

def raw7549step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

def raw7550 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, -1, 3], ![1, 2, -1, -2]]

def raw7550step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![-1, 3, -2]]

def raw7550step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 2, -2], ![-2, 1, 1], ![1, -3, 2]]

def raw7550step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

def raw7551 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def raw7551step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, -2, 0], ![1, 0, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical236
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7552 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw7553 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 2, 1, -3], ![1, 0, -3, 2]]

def raw7554 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![1, 2, -2, -1]]

def raw7554step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![2, 0, -2], ![-1, 2, -1]]

def raw7554step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

def raw7555 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 1, 1], ![1, 2, -3, 0]]

def raw7555step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![2, 1, -3], ![-1, 1, 0]]

def raw7555step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 2, -2], ![-2, -1, 3], ![1, -1, 0]]

def raw7555step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw7556 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 2, 0], ![1, 2, -4, 1]]

def raw7556step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![2, 2, -4], ![-1, 0, 1]]

def raw7556step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 2, -2], ![-2, -2, 4], ![1, 0, -1]]

def raw7556step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw7557 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 3, -1], ![1, 2, -5, 2]]

def raw7557step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![2, 3, -5], ![-1, -1, 2]]

def raw7557step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 2, -2], ![-2, -3, 5], ![1, 1, -2]]

def raw7557step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def raw7558 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -3, 4], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw7558step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw7559 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw7560 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -3, 4], ![0, 2, 1, -3], ![1, -1, 0, 0]]

def raw7561 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -3, 4], ![1, 1, 1, -3]]

def raw7561step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![2, -3, 1], ![-1, 4, -3]]

def raw7561step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 1, -1], ![-2, 3, -1], ![1, -4, 3]]

def raw7561step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def raw7562 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -2, 3], ![0, 1, 0, -1], ![1, 0, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end


