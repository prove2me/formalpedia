-- Prove2me | Definitions.Def_OAIQ106D045
-- name    : OAIQ106D045
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T12:23:28.006406+00:00
-- url     : https://prove2.me/theorems/3bfe4961-4ce0-42e4-91a7-d1aa39ca8bca
-- title:
--   Definitions bundle OAIQ106D045 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 621 declarations of OpenAI's Lean: 621 definitions. The definitions and types are `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1952`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1953`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1954`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1955`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1956`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1957`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1958`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1959`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1960`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1961`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1962`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1963`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1964`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1965`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1966`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1967`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1968`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1969`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1970`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1971`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1972`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1973`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1974`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1975`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1976`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1977`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1978`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1979`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1980`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1981`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1982`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1983`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1984`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1985`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1986`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1987`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1988`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1989`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1990`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1991` and 581 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_PairSemantics_Sound0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/PairSemantics/Sound0.lean), [`MutuallyUnbiased_PairSemantics_Sound3`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/PairSemantics/Sound3.lean), [`MutuallyUnbiased_PairSemantics_Sound30`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/PairSemantics/Sound30.lean), [`MutuallyUnbiased_PairSemantics_Sound31`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/PairSemantics/Sound31.lean), [`MutuallyUnbiased_PairSemantics_Sound32`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/PairSemantics/Sound32.lean), [`MutuallyUnbiased_PairSemantics_Sound33`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/PairSemantics/Sound33.lean), [`MutuallyUnbiased_PairSemantics_Sound34`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/PairSemantics/Sound34.lean), [`MutuallyUnbiased_PairSemantics_Sound35`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/PairSemantics/Sound35.lean), [`MutuallyUnbiased_PairSemantics_Sound36`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/PairSemantics/Sound36.lean), [`MutuallyUnbiased_PairSemantics_Sound37`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/PairSemantics/Sound37.lean), [`MutuallyUnbiased_PairSemantics_Sound38`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/PairSemantics/Sound38.lean), [`MutuallyUnbiased_PairSemantics_Sound39`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/PairSemantics/Sound39.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1161`, `OAI.MUB6.Certificate.MixedSemantics.sound1162`, `OAI.MUB6.Certificate.MixedSemantics.sound1164`, `OAI.MUB6.Certificate.MixedSemantics.sound1265`, `OAI.MUB6.Certificate.MixedSemantics.sound1298`, `OAI.MUB6.Certificate.MixedSemantics.sound1299`, `OAI.MUB6.Certificate.MixedSemantics.sound1339`, `OAI.MUB6.Certificate.MixedSemantics.sound1340`, `OAI.MUB6.Certificate.MixedSemantics.sound1341`, `OAI.MUB6.Certificate.MixedSemantics.sound1342`, `OAI.MUB6.Certificate.MixedSemantics.sound1343`, `OAI.MUB6.Certificate.MixedSemantics.sound1344`, `OAI.MUB6.Certificate.MixedSemantics.sound1346`, `OAI.MUB6.Certificate.MixedSemantics.sound1395`, `OAI.MUB6.Certificate.MixedSemantics.sound1396`, `OAI.MUB6.Certificate.MixedSemantics.sound1397`, `OAI.MUB6.Certificate.MixedSemantics.sound1399`, `OAI.MUB6.Certificate.MixedSemantics.sound1401`, `OAI.MUB6.Certificate.MixedSemantics.sound1409`, `OAI.MUB6.Certificate.MixedSemantics.sound1410`, `OAI.MUB6.Certificate.MixedSemantics.sound1411`, `OAI.MUB6.Certificate.MixedSemantics.sound1412`, `OAI.MUB6.Certificate.MixedSemantics.sound1413`, `OAI.MUB6.Certificate.MixedSemantics.sound1414`, `OAI.MUB6.Certificate.MixedSemantics.sound1416`, `OAI.MUB6.Certificate.MixedSemantics.sound1417`, `OAI.MUB6.Certificate.MixedSemantics.sound1427`, `OAI.MUB6.Certificate.MixedSemantics.sound1441`, `OAI.MUB6.Certificate.MixedSemantics.sound1443`, `OAI.MUB6.Certificate.MixedSemantics.sound1451`, `OAI.MUB6.Certificate.MixedSemantics.sound1475`, `OAI.MUB6.Certificate.MixedSemantics.sound1477`, `OAI.MUB6.Certificate.MixedSemantics.sound1478`, `OAI.MUB6.Certificate.MixedSemantics.sound1479`, `OAI.MUB6.Certificate.MixedSemantics.sound1480`, `OAI.MUB6.Certificate.MixedSemantics.sound171`, `OAI.MUB6.Certificate.MixedSemantics.sound174`, `OAI.MUB6.Certificate.MixedSemantics.sound206`, `OAI.MUB6.Certificate.MixedSemantics.sound207`, `OAI.MUB6.Certificate.MixedSemantics.sound2357`, `OAI.MUB6.Certificate.MixedSemantics.sound2358`, `OAI.MUB6.Certificate.MixedSemantics.sound2527`, `OAI.MUB6.Certificate.MixedSemantics.sound2530`, `OAI.MUB6.Certificate.MixedSemantics.sound2531`, `OAI.MUB6.Certificate.MixedSemantics.sound2532`, `OAI.MUB6.Certificate.MixedSemantics.sound2570`, `OAI.MUB6.Certificate.MixedSemantics.sound2572`, `OAI.MUB6.Certificate.MixedSemantics.sound2574`, `OAI.MUB6.Certificate.MixedSemantics.sound2576`, `OAI.MUB6.Certificate.MixedSemantics.sound2593`, `OAI.MUB6.Certificate.MixedSemantics.sound2594`, `OAI.MUB6.Certificate.MixedSemantics.sound2595`, `OAI.MUB6.Certificate.MixedSemantics.sound2596`, `OAI.MUB6.Certificate.MixedSemantics.sound2598`, `OAI.MUB6.Certificate.MixedSemantics.sound2599`, `OAI.MUB6.Certificate.MixedSemantics.sound2601`, `OAI.MUB6.Certificate.MixedSemantics.sound2636`, `OAI.MUB6.Certificate.MixedSemantics.sound2637`, `OAI.MUB6.Certificate.MixedSemantics.sound2638`, `OAI.MUB6.Certificate.MixedSemantics.sound2640`, `OAI.MUB6.Certificate.MixedSemantics.sound2753`, `OAI.MUB6.Certificate.MixedSemantics.sound2766`, `OAI.MUB6.Certificate.MixedSemantics.sound2828`, `OAI.MUB6.Certificate.MixedSemantics.sound2904`, `OAI.MUB6.Certificate.MixedSemantics.sound293`, `OAI.MUB6.Certificate.MixedSemantics.sound2936`, `OAI.MUB6.Certificate.MixedSemantics.sound2937`, `OAI.MUB6.Certificate.MixedSemantics.sound2939`, `OAI.MUB6.Certificate.MixedSemantics.sound2941`, `OAI.MUB6.Certificate.MixedSemantics.sound2943`, `OAI.MUB6.Certificate.MixedSemantics.sound2957`, `OAI.MUB6.Certificate.MixedSemantics.sound2958`, `OAI.MUB6.Certificate.MixedSemantics.sound2959`, `OAI.MUB6.Certificate.MixedSemantics.sound2960`, `OAI.MUB6.Certificate.MixedSemantics.sound2961`, `OAI.MUB6.Certificate.MixedSemantics.sound2963`, `OAI.MUB6.Certificate.MixedSemantics.sound2965`, `OAI.MUB6.Certificate.MixedSemantics.sound2966`, `OAI.MUB6.Certificate.MixedSemantics.sound2968`, `OAI.MUB6.Certificate.MixedSemantics.sound2969`, `OAI.MUB6.Certificate.MixedSemantics.sound2986`, `OAI.MUB6.Certificate.MixedSemantics.sound2987`, `OAI.MUB6.Certificate.MixedSemantics.sound2988`, `OAI.MUB6.Certificate.MixedSemantics.sound2990`, `OAI.MUB6.Certificate.MixedSemantics.sound2996`, `OAI.MUB6.Certificate.MixedSemantics.sound2997`, `OAI.MUB6.Certificate.MixedSemantics.sound2998`, `OAI.MUB6.Certificate.MixedSemantics.sound3003`, `OAI.MUB6.Certificate.MixedSemantics.sound3005`, `OAI.MUB6.Certificate.MixedSemantics.sound3082`, `OAI.MUB6.Certificate.MixedSemantics.sound3087`, `OAI.MUB6.Certificate.MixedSemantics.sound3093`, `OAI.MUB6.Certificate.MixedSemantics.sound3094`, `OAI.MUB6.Certificate.MixedSemantics.sound3099`, `OAI.MUB6.Certificate.MixedSemantics.sound3100`, `OAI.MUB6.Certificate.MixedSemantics.sound3106`, `OAI.MUB6.Certificate.MixedSemantics.sound3109`, `OAI.MUB6.Certificate.MixedSemantics.sound3116`, `OAI.MUB6.Certificate.MixedSemantics.sound3120`, `OAI.MUB6.Certificate.MixedSemantics.sound3143`, `OAI.MUB6.Certificate.MixedSemantics.sound3178`, `OAI.MUB6.Certificate.MixedSemantics.sound3184`, `OAI.MUB6.Certificate.MixedSemantics.sound3185`, `OAI.MUB6.Certificate.MixedSemantics.sound3190`, `OAI.MUB6.Certificate.MixedSemantics.sound3191`, `OAI.MUB6.Certificate.MixedSemantics.sound3203`, `OAI.MUB6.Certificate.MixedSemantics.sound3204`, `OAI.MUB6.Certificate.MixedSemantics.sound3205`, `OAI.MUB6.Certificate.MixedSemantics.sound3206`, `OAI.MUB6.Certificate.MixedSemantics.sound3207`, `OAI.MUB6.Certificate.MixedSemantics.sound3209`, `OAI.MUB6.Certificate.MixedSemantics.sound3210`, `OAI.MUB6.Certificate.MixedSemantics.sound3211`, `OAI.MUB6.Certificate.MixedSemantics.sound3223`, `OAI.MUB6.Certificate.MixedSemantics.sound3226`, `OAI.MUB6.Certificate.MixedSemantics.sound3227`, `OAI.MUB6.Certificate.MixedSemantics.sound370`, `OAI.MUB6.Certificate.MixedSemantics.sound371`, `OAI.MUB6.Certificate.MixedSemantics.sound3711`, `OAI.MUB6.Certificate.MixedSemantics.sound3726`, `OAI.MUB6.Certificate.MixedSemantics.sound3727`, `OAI.MUB6.Certificate.MixedSemantics.sound3734`, `OAI.MUB6.Certificate.MixedSemantics.sound3735`, `OAI.MUB6.Certificate.MixedSemantics.sound3736`, `OAI.MUB6.Certificate.MixedSemantics.sound3737`, `OAI.MUB6.Certificate.MixedSemantics.sound3738`, `OAI.MUB6.Certificate.MixedSemantics.sound3739`, `OAI.MUB6.Certificate.MixedSemantics.sound3818`, `OAI.MUB6.Certificate.MixedSemantics.sound3821`, `OAI.MUB6.Certificate.MixedSemantics.sound3822`, `OAI.MUB6.Certificate.MixedSemantics.sound3823`, `OAI.MUB6.Certificate.MixedSemantics.sound3824`, `OAI.MUB6.Certificate.MixedSemantics.sound3829`, `OAI.MUB6.Certificate.MixedSemantics.sound3831`, `OAI.MUB6.Certificate.MixedSemantics.sound3847`, `OAI.MUB6.Certificate.MixedSemantics.sound3851`, `OAI.MUB6.Certificate.MixedSemantics.sound3853`, `OAI.MUB6.Certificate.MixedSemantics.sound3855`, `OAI.MUB6.Certificate.MixedSemantics.sound3856`, `OAI.MUB6.Certificate.MixedSemantics.sound3858`, `OAI.MUB6.Certificate.MixedSemantics.sound3882`, `OAI.MUB6.Certificate.MixedSemantics.sound3883`, `OAI.MUB6.Certificate.MixedSemantics.sound3887`, `OAI.MUB6.Certificate.MixedSemantics.sound3888`, `OAI.MUB6.Certificate.MixedSemantics.sound3925`, `OAI.MUB6.Certificate.MixedSemantics.sound3931`, `OAI.MUB6.Certificate.MixedSemantics.sound3933`, `OAI.MUB6.Certificate.MixedSemantics.sound3936`, `OAI.MUB6.Certificate.MixedSemantics.sound3937`, `OAI.MUB6.Certificate.MixedSemantics.sound3965`, `OAI.MUB6.Certificate.MixedSemantics.sound3966`, `OAI.MUB6.Certificate.MixedSemantics.sound3967`, `OAI.MUB6.Certificate.MixedSemantics.sound3977`, `OAI.MUB6.Certificate.MixedSemantics.sound3984`, `OAI.MUB6.Certificate.MixedSemantics.sound3987`, `OAI.MUB6.Certificate.MixedSemantics.sound3993`, `OAI.MUB6.Certificate.MixedSemantics.sound3994`, `OAI.MUB6.Certificate.MixedSemantics.sound3997`, `OAI.MUB6.Certificate.MixedSemantics.sound3998`, `OAI.MUB6.Certificate.MixedSemantics.sound4002`, `OAI.MUB6.Certificate.MixedSemantics.sound4003`, `OAI.MUB6.Certificate.MixedSemantics.sound4012`, `OAI.MUB6.Certificate.MixedSemantics.sound4014`, `OAI.MUB6.Certificate.MixedSemantics.sound4023`, `OAI.MUB6.Certificate.MixedSemantics.sound4026`, `OAI.MUB6.Certificate.MixedSemantics.sound4027`, `OAI.MUB6.Certificate.MixedSemantics.sound4029`, `OAI.MUB6.Certificate.MixedSemantics.sound4031`, `OAI.MUB6.Certificate.MixedSemantics.sound4032`, `OAI.MUB6.Certificate.MixedSemantics.sound4033`, `OAI.MUB6.Certificate.MixedSemantics.sound4039`, `OAI.MUB6.Certificate.MixedSemantics.sound436`, `OAI.MUB6.Certificate.MixedSemantics.sound454`, `OAI.MUB6.Certificate.MixedSemantics.sound455`, `OAI.MUB6.Certificate.MixedSemantics.sound511`, `OAI.MUB6.Certificate.MixedSemantics.sound5176`, `OAI.MUB6.Certificate.MixedSemantics.sound5177`, `OAI.MUB6.Certificate.MixedSemantics.sound521`, `OAI.MUB6.Certificate.MixedSemantics.sound5306`, `OAI.MUB6.Certificate.MixedSemantics.sound5415`, `OAI.MUB6.Certificate.MixedSemantics.sound5443`, `OAI.MUB6.Certificate.MixedSemantics.sound5452`, `OAI.MUB6.Certificate.MixedSemantics.sound5453`, `OAI.MUB6.Certificate.MixedSemantics.sound5464`, `OAI.MUB6.Certificate.MixedSemantics.sound5492`, `OAI.MUB6.Certificate.MixedSemantics.sound5498`, `OAI.MUB6.Certificate.MixedSemantics.sound644`, `OAI.MUB6.Certificate.MixedSemantics.sound645`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound135`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound136`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound137`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound138`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound140`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound141`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound142`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound143`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound145`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound146`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound147`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound148`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound149`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound150`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound151`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1423`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero925`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound100`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound110`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound114`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1159`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound116`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound117`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1170`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1179`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound126`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1264`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1269`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound127`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1294`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound13`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound130`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1301`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1303`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1312`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1318`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound141`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1472`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1480`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1484`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1493`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1517`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1521`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound153`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound16`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1651`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1653`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1656`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1662`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1669`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1674`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1703`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1709`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1781`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1785`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1840`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1845`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1846`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1847`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1849`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1856`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1859`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1866`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1874`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound188`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound19`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1911`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1917`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1964`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1972`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound198`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound199`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2034`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2037`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2049`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound207`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2166`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2168`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2170`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2171`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2172`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2175`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2176`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2178`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2179`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2180`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2181`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2182`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2183`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2184`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2185`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2187`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2188`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2189`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2190`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2191`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2192`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2197`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2200`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2201`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2203`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2204`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2205`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2206`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2207`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2208`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2212`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2214`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2216`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2217`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2218`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2219`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2221`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2222`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2223`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2224`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2225`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2226`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2227`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2228`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2229`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2230`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2231`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2232`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2233`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2235`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2240`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2242`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2244`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2245`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2246`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2247`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2248`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2249`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2250`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2251`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2252`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2254`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2255`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2257`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2258`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2259`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2260`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2261`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2263`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2264`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2266`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2267`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2269`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2270`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2271`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2272`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2273`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2274`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2275`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2276`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2279`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2280`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2282`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2283`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2284`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2286`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2287`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2288`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2291`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2292`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2293`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2294`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2296`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2297`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2298`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2299`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2300`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2301`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2302`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2303`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2304`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2306`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2307`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2308`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2309`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2313`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2315`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2317`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2318`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2320`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2321`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2322`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2323`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2324`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2325`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2326`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2327`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2329`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2330`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2331`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2332`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2333`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2334`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2335`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2336`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2337`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2338`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2340`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2341`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2344`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2345`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2346`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2347`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2348`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2350`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2352`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2354`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2355`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2356`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2357`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound236`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2360`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2361`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2362`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2363`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2364`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2365`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2366`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2367`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2368`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2369`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2371`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2372`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2374`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2375`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2377`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2378`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2379`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2380`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2381`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2383`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2384`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2386`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2388`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2389`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2391`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2393`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2395`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2396`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2397`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2398`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2400`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2401`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2402`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2403`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2404`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2405`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2406`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2407`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2408`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2409`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2410`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2411`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2413`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2415`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2418`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2419`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2420`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2423`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2424`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound244`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound245`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound255`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound269`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound286`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound287`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound296`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound340`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound344`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound345`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound35`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound356`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound359`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound366`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound368`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound371`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound380`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound388`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound391`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound392`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound395`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound412`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound413`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound418`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound428`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound445`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound456`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound462`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound463`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound474`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound482`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound485`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound488`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound5`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound504`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound516`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound521`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound525`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound526`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound532`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound534`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound547`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound552`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound555`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound558`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound565`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound568`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound571`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound572`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound579`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound58`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound582`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound585`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound59`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound6`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound600`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound613`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound621`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound629`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound631`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound633`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound635`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound649`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound659`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound663`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound664`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound675`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound711`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound718`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound731`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound732`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound734`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound736`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound741`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound743`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound779`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound780`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound788`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound790`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound792`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound794`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound796`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound8`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound800`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound802`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound864`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound866`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound877`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound881`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound885`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound888`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound909`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound911`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound927`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound933`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound94`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound971`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval106`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1074`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval109`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval116`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval117`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1192`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval12`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval120`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1210`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval124`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1254`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval130`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval133`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval134`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval141`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval143`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval145`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval146`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval147`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval149`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval155`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1553`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval159`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval164`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval165`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval167`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval173`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval174`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval18`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval181`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval182`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval185`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval202`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval207`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval21`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval214`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval215`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval218`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval220`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval224`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval225`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval226`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval229`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval231`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval234`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval235`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval242`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval243`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval245`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval249`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval255`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval257`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval258`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval263`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval270`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval271`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval273`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval278`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval280`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval285`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval286`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval287`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval292`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval296`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval301`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval308`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval310`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval323`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval325`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval331`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval332`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval334`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval335`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval343`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval344`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval348`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval353`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval358`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval359`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval366`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval368`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval37`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval370`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval371`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval372`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval373`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval377`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval380`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval383`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval389`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval39`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval391`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval394`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval401`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval403`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval408`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval41`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval413`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval414`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval444`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval46`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval475`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval476`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval477`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval52`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval54`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval56`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval6`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval63`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval69`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval74`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval79`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval8`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval86`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval91`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval99`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval113`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval119`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval147`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval150`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval208`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval21`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval215`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval216`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval220`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval222`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval271`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval359`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval360`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval362`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval373`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval375`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval384`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval44`, `OAI.MUB6.Certificate.PairSemantics.boundarySound165`, `OAI.MUB6.Certificate.PairSemantics.boundarySound243`, `OAI.MUB6.Certificate.PairSemantics.boundarySound248`, `OAI.MUB6.Certificate.PairSemantics.boundarySound249`, `OAI.MUB6.Certificate.PairSemantics.boundarySound250`, `OAI.MUB6.Certificate.PairSemantics.boundarySound252`, `OAI.MUB6.Certificate.PairSemantics.boundarySound261`, `OAI.MUB6.Certificate.PairSemantics.boundarySound264`, `OAI.MUB6.Certificate.PairSemantics.boundarySound305`, `OAI.MUB6.Certificate.PairSemantics.boundarySound347`, `OAI.MUB6.Certificate.PairSemantics.boundarySound445`, `OAI.MUB6.Certificate.PairSemantics.boundarySound454`, `OAI.MUB6.Certificate.PairSemantics.boundarySound49`, `OAI.MUB6.Certificate.PairSemantics.boundarySound51`, `OAI.MUB6.Certificate.PairSemantics.boundarySound56`, `OAI.MUB6.Certificate.PairSemantics.boundarySound73`, `OAI.MUB6.Certificate.PairSemantics.boundarySound75`, `OAI.MUB6.Certificate.PairSemantics.boundarySound83`, `OAI.MUB6.Certificate.PairSemantics.boundarySound97`, `OAI.MUB6.Certificate.PairSemantics.sound1141`, `OAI.MUB6.Certificate.PairSemantics.sound117`, `OAI.MUB6.Certificate.PairSemantics.sound1381`, `OAI.MUB6.Certificate.PairSemantics.sound1383`, `OAI.MUB6.Certificate.PairSemantics.sound1384`, `OAI.MUB6.Certificate.PairSemantics.sound1387`, `OAI.MUB6.Certificate.PairSemantics.sound1390`, `OAI.MUB6.Certificate.PairSemantics.sound1391`, `OAI.MUB6.Certificate.PairSemantics.sound1392`, `OAI.MUB6.Certificate.PairSemantics.sound1395`, `OAI.MUB6.Certificate.PairSemantics.sound1399`, `OAI.MUB6.Certificate.PairSemantics.sound1414`, `OAI.MUB6.Certificate.PairSemantics.sound1419`, `OAI.MUB6.Certificate.PairSemantics.sound1423`, `OAI.MUB6.Certificate.PairSemantics.sound1424`, `OAI.MUB6.Certificate.PairSemantics.sound1425`, `OAI.MUB6.Certificate.PairSemantics.sound1432`, `OAI.MUB6.Certificate.PairSemantics.sound1434`, `OAI.MUB6.Certificate.PairSemantics.sound1486`, `OAI.MUB6.Certificate.PairSemantics.sound1500`, `OAI.MUB6.Certificate.PairSemantics.sound1512`, `OAI.MUB6.Certificate.PairSemantics.sound1518`, `OAI.MUB6.Certificate.PairSemantics.sound1520`, `OAI.MUB6.Certificate.PairSemantics.sound1523`, `OAI.MUB6.Certificate.PairSemantics.sound1530`, `OAI.MUB6.Certificate.PairSemantics.sound1531`, `OAI.MUB6.Certificate.PairSemantics.sound1533`, `OAI.MUB6.Certificate.PairSemantics.sound1535`, `OAI.MUB6.Certificate.PairSemantics.sound1548`, `OAI.MUB6.Certificate.PairSemantics.sound1552`, `OAI.MUB6.Certificate.PairSemantics.sound1563`, `OAI.MUB6.Certificate.PairSemantics.sound1585`, `OAI.MUB6.Certificate.PairSemantics.sound1605`, `OAI.MUB6.Certificate.PairSemantics.sound1624`, `OAI.MUB6.Certificate.PairSemantics.sound1625`, `OAI.MUB6.Certificate.PairSemantics.sound1628`, `OAI.MUB6.Certificate.PairSemantics.sound1631`, `OAI.MUB6.Certificate.PairSemantics.sound1634`, `OAI.MUB6.Certificate.PairSemantics.sound1635`, `OAI.MUB6.Certificate.PairSemantics.sound1638`, `OAI.MUB6.Certificate.PairSemantics.sound1643`, `OAI.MUB6.Certificate.PairSemantics.sound1646`, `OAI.MUB6.Certificate.PairSemantics.sound1648`, `OAI.MUB6.Certificate.PairSemantics.sound1652`, `OAI.MUB6.Certificate.PairSemantics.sound1668`, `OAI.MUB6.Certificate.PairSemantics.sound1669`, `OAI.MUB6.Certificate.PairSemantics.sound1682`, `OAI.MUB6.Certificate.PairSemantics.sound1685`, `OAI.MUB6.Certificate.PairSemantics.sound1686`, `OAI.MUB6.Certificate.PairSemantics.sound1707`, `OAI.MUB6.Certificate.PairSemantics.sound1716`, `OAI.MUB6.Certificate.PairSemantics.sound1718`, `OAI.MUB6.Certificate.PairSemantics.sound1736`, `OAI.MUB6.Certificate.PairSemantics.sound1739`, `OAI.MUB6.Certificate.PairSemantics.sound1768`, `OAI.MUB6.Certificate.PairSemantics.sound1769`, `OAI.MUB6.Certificate.PairSemantics.sound1770`, `OAI.MUB6.Certificate.PairSemantics.sound1774`, `OAI.MUB6.Certificate.PairSemantics.sound1784`, `OAI.MUB6.Certificate.PairSemantics.sound1793`, `OAI.MUB6.Certificate.PairSemantics.sound1800`, `OAI.MUB6.Certificate.PairSemantics.sound1803`, `OAI.MUB6.Certificate.PairSemantics.sound1826`, `OAI.MUB6.Certificate.PairSemantics.sound1828`, `OAI.MUB6.Certificate.PairSemantics.sound1830`, `OAI.MUB6.Certificate.PairSemantics.sound1849`, `OAI.MUB6.Certificate.PairSemantics.sound1858`, `OAI.MUB6.Certificate.PairSemantics.sound1860`, `OAI.MUB6.Certificate.PairSemantics.sound1865`, `OAI.MUB6.Certificate.PairSemantics.sound1866`, `OAI.MUB6.Certificate.PairSemantics.sound1867`, `OAI.MUB6.Certificate.PairSemantics.sound1869`, `OAI.MUB6.Certificate.PairSemantics.sound1870`, `OAI.MUB6.Certificate.PairSemantics.sound1872`, `OAI.MUB6.Certificate.PairSemantics.sound1885`, `OAI.MUB6.Certificate.PairSemantics.sound1890`, `OAI.MUB6.Certificate.PairSemantics.sound1938`, `OAI.MUB6.Certificate.PairSemantics.sound1968`, `OAI.MUB6.Certificate.PairSemantics.sound1977`, `OAI.MUB6.Certificate.PairSemantics.sound1978`, `OAI.MUB6.Certificate.PairSemantics.sound1980`, `OAI.MUB6.Certificate.PairSemantics.sound1986`, `OAI.MUB6.Certificate.PairSemantics.sound1987`, `OAI.MUB6.Certificate.PairSemantics.sound2041`, `OAI.MUB6.Certificate.PairSemantics.sound2058`, `OAI.MUB6.Certificate.PairSemantics.sound2106`, `OAI.MUB6.Certificate.PairSemantics.sound2108`, `OAI.MUB6.Certificate.PairSemantics.sound2113`, `OAI.MUB6.Certificate.PairSemantics.sound2117`, `OAI.MUB6.Certificate.PairSemantics.sound2122`, `OAI.MUB6.Certificate.PairSemantics.sound2123`, `OAI.MUB6.Certificate.PairSemantics.sound2128`, `OAI.MUB6.Certificate.PairSemantics.sound2132`, `OAI.MUB6.Certificate.PairSemantics.sound2152`, `OAI.MUB6.Certificate.PairSemantics.sound2168`, `OAI.MUB6.Certificate.PairSemantics.sound2175`, `OAI.MUB6.Certificate.PairSemantics.sound2177`, `OAI.MUB6.Certificate.PairSemantics.sound2183`, `OAI.MUB6.Certificate.PairSemantics.sound2190`, `OAI.MUB6.Certificate.PairSemantics.sound2192`, `OAI.MUB6.Certificate.PairSemantics.sound2197`, `OAI.MUB6.Certificate.PairSemantics.sound2201`, `OAI.MUB6.Certificate.PairSemantics.sound2202`, `OAI.MUB6.Certificate.PairSemantics.sound2204`, `OAI.MUB6.Certificate.PairSemantics.sound2213`, `OAI.MUB6.Certificate.PairSemantics.sound2216`, `OAI.MUB6.Certificate.PairSemantics.sound2228`, `OAI.MUB6.Certificate.PairSemantics.sound2243`, `OAI.MUB6.Certificate.PairSemantics.sound2244`, `OAI.MUB6.Certificate.PairSemantics.sound2262`, `OAI.MUB6.Certificate.PairSemantics.sound2284`, `OAI.MUB6.Certificate.PairSemantics.sound2285`, `OAI.MUB6.Certificate.PairSemantics.sound2286`, `OAI.MUB6.Certificate.PairSemantics.sound2293`, `OAI.MUB6.Certificate.PairSemantics.sound2294`, `OAI.MUB6.Certificate.PairSemantics.sound2295`, `OAI.MUB6.Certificate.PairSemantics.sound2296`, `OAI.MUB6.Certificate.PairSemantics.sound2298`, `OAI.MUB6.Certificate.PairSemantics.sound2304`, `OAI.MUB6.Certificate.PairSemantics.sound2307`, `OAI.MUB6.Certificate.PairSemantics.sound2312`, `OAI.MUB6.Certificate.PairSemantics.sound2315`, `OAI.MUB6.Certificate.PairSemantics.sound232`, `OAI.MUB6.Certificate.PairSemantics.sound2324`, `OAI.MUB6.Certificate.PairSemantics.sound2325`, `OAI.MUB6.Certificate.PairSemantics.sound2327`, `OAI.MUB6.Certificate.PairSemantics.sound2338`, `OAI.MUB6.Certificate.PairSemantics.sound2349`, `OAI.MUB6.Certificate.PairSemantics.sound2357`, `OAI.MUB6.Certificate.PairSemantics.sound2375`, `OAI.MUB6.Certificate.PairSemantics.sound2382`, `OAI.MUB6.Certificate.PairSemantics.sound2389`, `OAI.MUB6.Certificate.PairSemantics.sound2390`, `OAI.MUB6.Certificate.PairSemantics.sound2391`, `OAI.MUB6.Certificate.PairSemantics.sound2399`, `OAI.MUB6.Certificate.PairSemantics.sound2400`, `OAI.MUB6.Certificate.PairSemantics.sound2403`, `OAI.MUB6.Certificate.PairSemantics.sound2411`, `OAI.MUB6.Certificate.PairSemantics.sound2413`, `OAI.MUB6.Certificate.PairSemantics.sound2414`, `OAI.MUB6.Certificate.PairSemantics.sound2415`, `OAI.MUB6.Certificate.PairSemantics.sound2416`, `OAI.MUB6.Certificate.PairSemantics.sound2417`, `OAI.MUB6.Certificate.PairSemantics.sound2420`, `OAI.MUB6.Certificate.PairSemantics.sound2428`, `OAI.MUB6.Certificate.PairSemantics.sound2433`, `OAI.MUB6.Certificate.PairSemantics.sound2434`, `OAI.MUB6.Certificate.PairSemantics.sound2435`, `OAI.MUB6.Certificate.PairSemantics.sound2436`, `OAI.MUB6.Certificate.PairSemantics.sound2440`, `OAI.MUB6.Certificate.PairSemantics.sound2441`, `OAI.MUB6.Certificate.PairSemantics.sound2442`, `OAI.MUB6.Certificate.PairSemantics.sound2443`, `OAI.MUB6.Certificate.PairSemantics.sound2444`, `OAI.MUB6.Certificate.PairSemantics.sound2445`, `OAI.MUB6.Certificate.PairSemantics.sound2455`, `OAI.MUB6.Certificate.PairSemantics.sound2456`, `OAI.MUB6.Certificate.PairSemantics.sound2457`, `OAI.MUB6.Certificate.PairSemantics.sound2462`, `OAI.MUB6.Certificate.PairSemantics.sound2463`, `OAI.MUB6.Certificate.PairSemantics.sound2464`, `OAI.MUB6.Certificate.PairSemantics.sound2465`, `OAI.MUB6.Certificate.PairSemantics.sound2466`, `OAI.MUB6.Certificate.PairSemantics.sound2470`, `OAI.MUB6.Certificate.PairSemantics.sound2472`, `OAI.MUB6.Certificate.PairSemantics.sound2473`, `OAI.MUB6.Certificate.PairSemantics.sound2477`, `OAI.MUB6.Certificate.PairSemantics.sound2479`, `OAI.MUB6.Certificate.PairSemantics.sound2486`, `OAI.MUB6.Certificate.PairSemantics.sound2489`, `OAI.MUB6.Certificate.PairSemantics.sound2490`, `OAI.MUB6.Certificate.PairSemantics.sound2491`, `OAI.MUB6.Certificate.PairSemantics.sound2492`, `OAI.MUB6.Certificate.PairSemantics.sound2507`, `OAI.MUB6.Certificate.PairSemantics.sound2520`, `OAI.MUB6.Certificate.PairSemantics.sound2521`, `OAI.MUB6.Certificate.PairSemantics.sound2524`, `OAI.MUB6.Certificate.PairSemantics.sound2525`, `OAI.MUB6.Certificate.PairSemantics.sound2533`, `OAI.MUB6.Certificate.PairSemantics.sound2540`, `OAI.MUB6.Certificate.PairSemantics.sound2546`, `OAI.MUB6.Certificate.PairSemantics.sound2547`, `OAI.MUB6.Certificate.PairSemantics.sound2548`, `OAI.MUB6.Certificate.PairSemantics.sound2557`, `OAI.MUB6.Certificate.PairSemantics.sound2558`, `OAI.MUB6.Certificate.PairSemantics.sound2559`, `OAI.MUB6.Certificate.PairSemantics.sound2564`, `OAI.MUB6.Certificate.PairSemantics.sound2565`, `OAI.MUB6.Certificate.PairSemantics.sound2566`, `OAI.MUB6.Certificate.PairSemantics.sound2573`, `OAI.MUB6.Certificate.PairSemantics.sound2579`, `OAI.MUB6.Certificate.PairSemantics.sound2602`, `OAI.MUB6.Certificate.PairSemantics.sound2604`, `OAI.MUB6.Certificate.PairSemantics.sound2606`, `OAI.MUB6.Certificate.PairSemantics.sound2619`, `OAI.MUB6.Certificate.PairSemantics.sound2626`, `OAI.MUB6.Certificate.PairSemantics.sound2627`, `OAI.MUB6.Certificate.PairSemantics.sound2657`, `OAI.MUB6.Certificate.PairSemantics.sound2658`, `OAI.MUB6.Certificate.PairSemantics.sound2661`, `OAI.MUB6.Certificate.PairSemantics.sound2666`, `OAI.MUB6.Certificate.PairSemantics.sound2670`, `OAI.MUB6.Certificate.PairSemantics.sound2671`, `OAI.MUB6.Certificate.PairSemantics.sound2683`, `OAI.MUB6.Certificate.PairSemantics.sound2686`, `OAI.MUB6.Certificate.PairSemantics.sound2690`, `OAI.MUB6.Certificate.PairSemantics.sound2693`, `OAI.MUB6.Certificate.PairSemantics.sound2709`, `OAI.MUB6.Certificate.PairSemantics.sound2710`, `OAI.MUB6.Certificate.PairSemantics.sound2714`, `OAI.MUB6.Certificate.PairSemantics.sound2717`, `OAI.MUB6.Certificate.PairSemantics.sound2723`, `OAI.MUB6.Certificate.PairSemantics.sound2732`, `OAI.MUB6.Certificate.PairSemantics.sound2733`, `OAI.MUB6.Certificate.PairSemantics.sound2754`, `OAI.MUB6.Certificate.PairSemantics.sound2757`, `OAI.MUB6.Certificate.PairSemantics.sound2765`, `OAI.MUB6.Certificate.PairSemantics.sound2788`, `OAI.MUB6.Certificate.PairSemantics.sound2790`, `OAI.MUB6.Certificate.PairSemantics.sound2793`, `OAI.MUB6.Certificate.PairSemantics.sound2829`, `OAI.MUB6.Certificate.PairSemantics.sound2836`, `OAI.MUB6.Certificate.PairSemantics.sound2845`, `OAI.MUB6.Certificate.PairSemantics.sound2854`, `OAI.MUB6.Certificate.PairSemantics.sound2863`, `OAI.MUB6.Certificate.PairSemantics.sound2864`, `OAI.MUB6.Certificate.PairSemantics.sound2865`, `OAI.MUB6.Certificate.PairSemantics.sound2866`, `OAI.MUB6.Certificate.PairSemantics.sound2867`, `OAI.MUB6.Certificate.PairSemantics.sound2868`, `OAI.MUB6.Certificate.PairSemantics.sound2873`, `OAI.MUB6.Certificate.PairSemantics.sound2875`, `OAI.MUB6.Certificate.PairSemantics.sound2878`, `OAI.MUB6.Certificate.PairSemantics.sound2879`, `OAI.MUB6.Certificate.PairSemantics.sound2880`, `OAI.MUB6.Certificate.PairSemantics.sound2881`, `OAI.MUB6.Certificate.PairSemantics.sound2882`, `OAI.MUB6.Certificate.PairSemantics.sound2883`, `OAI.MUB6.Certificate.PairSemantics.sound2884`, `OAI.MUB6.Certificate.PairSemantics.sound2886`, `OAI.MUB6.Certificate.PairSemantics.sound2887`, `OAI.MUB6.Certificate.PairSemantics.sound2889`, `OAI.MUB6.Certificate.PairSemantics.sound2890`, `OAI.MUB6.Certificate.PairSemantics.sound2891`, `OAI.MUB6.Certificate.PairSemantics.sound2892`, `OAI.MUB6.Certificate.PairSemantics.sound2895`, `OAI.MUB6.Certificate.PairSemantics.sound2896`, `OAI.MUB6.Certificate.PairSemantics.sound2898`, `OAI.MUB6.Certificate.PairSemantics.sound2899`, `OAI.MUB6.Certificate.PairSemantics.sound2900`, `OAI.MUB6.Certificate.PairSemantics.sound2901`, `OAI.MUB6.Certificate.PairSemantics.sound2902`, `OAI.MUB6.Certificate.PairSemantics.sound2903`, `OAI.MUB6.Certificate.PairSemantics.sound2906`, `OAI.MUB6.Certificate.PairSemantics.sound2909`, `OAI.MUB6.Certificate.PairSemantics.sound2910`, `OAI.MUB6.Certificate.PairSemantics.sound2912`, `OAI.MUB6.Certificate.PairSemantics.sound2913`, `OAI.MUB6.Certificate.PairSemantics.sound2914`, `OAI.MUB6.Certificate.PairSemantics.sound2915`, `OAI.MUB6.Certificate.PairSemantics.sound2916`, `OAI.MUB6.Certificate.PairSemantics.sound2917`, `OAI.MUB6.Certificate.PairSemantics.sound2918`, `OAI.MUB6.Certificate.PairSemantics.sound2919`, `OAI.MUB6.Certificate.PairSemantics.sound2922`, `OAI.MUB6.Certificate.PairSemantics.sound2924`, `OAI.MUB6.Certificate.PairSemantics.sound2927`, `OAI.MUB6.Certificate.PairSemantics.sound2928`, `OAI.MUB6.Certificate.PairSemantics.sound2929`, `OAI.MUB6.Certificate.PairSemantics.sound2930`, `OAI.MUB6.Certificate.PairSemantics.sound2931`, `OAI.MUB6.Certificate.PairSemantics.sound2933`, `OAI.MUB6.Certificate.PairSemantics.sound2934`, `OAI.MUB6.Certificate.PairSemantics.sound2935`, `OAI.MUB6.Certificate.PairSemantics.sound2936`, `OAI.MUB6.Certificate.PairSemantics.sound2939`, `OAI.MUB6.Certificate.PairSemantics.sound2940`, `OAI.MUB6.Certificate.PairSemantics.sound2941`, `OAI.MUB6.Certificate.PairSemantics.sound2943`, `OAI.MUB6.Certificate.PairSemantics.sound2944`, `OAI.MUB6.Certificate.PairSemantics.sound2948`, `OAI.MUB6.Certificate.PairSemantics.sound2949`, `OAI.MUB6.Certificate.PairSemantics.sound2950`, `OAI.MUB6.Certificate.PairSemantics.sound2952`, `OAI.MUB6.Certificate.PairSemantics.sound2953`, `OAI.MUB6.Certificate.PairSemantics.sound2954`, `OAI.MUB6.Certificate.PairSemantics.sound2955`, `OAI.MUB6.Certificate.PairSemantics.sound2956`, `OAI.MUB6.Certificate.PairSemantics.sound2957`, `OAI.MUB6.Certificate.PairSemantics.sound2958`, `OAI.MUB6.Certificate.PairSemantics.sound2959`, `OAI.MUB6.Certificate.PairSemantics.sound2960`, `OAI.MUB6.Certificate.PairSemantics.sound2962`, `OAI.MUB6.Certificate.PairSemantics.sound2965`, `OAI.MUB6.Certificate.PairSemantics.sound2966`, `OAI.MUB6.Certificate.PairSemantics.sound2967`, `OAI.MUB6.Certificate.PairSemantics.sound2968`, `OAI.MUB6.Certificate.PairSemantics.sound2969`, `OAI.MUB6.Certificate.PairSemantics.sound2970`, `OAI.MUB6.Certificate.PairSemantics.sound2972`, `OAI.MUB6.Certificate.PairSemantics.sound2973`, `OAI.MUB6.Certificate.PairSemantics.sound2974`, `OAI.MUB6.Certificate.PairSemantics.sound2975`, `OAI.MUB6.Certificate.PairSemantics.sound2976`, `OAI.MUB6.Certificate.PairSemantics.sound2977`, `OAI.MUB6.Certificate.PairSemantics.sound2979`, `OAI.MUB6.Certificate.PairSemantics.sound2980`, `OAI.MUB6.Certificate.PairSemantics.sound2982`, `OAI.MUB6.Certificate.PairSemantics.sound2985`, `OAI.MUB6.Certificate.PairSemantics.sound2986`, `OAI.MUB6.Certificate.PairSemantics.sound2987`, `OAI.MUB6.Certificate.PairSemantics.sound2988`, `OAI.MUB6.Certificate.PairSemantics.sound2989`, `OAI.MUB6.Certificate.PairSemantics.sound2990`, `OAI.MUB6.Certificate.PairSemantics.sound2991`, `OAI.MUB6.Certificate.PairSemantics.sound2993`, `OAI.MUB6.Certificate.PairSemantics.sound2994`, `OAI.MUB6.Certificate.PairSemantics.sound2996`, `OAI.MUB6.Certificate.PairSemantics.sound2997`, `OAI.MUB6.Certificate.PairSemantics.sound2998`, `OAI.MUB6.Certificate.PairSemantics.sound2999`, `OAI.MUB6.Certificate.PairSemantics.sound3000`, `OAI.MUB6.Certificate.PairSemantics.sound3001`, `OAI.MUB6.Certificate.PairSemantics.sound3002`, `OAI.MUB6.Certificate.PairSemantics.sound3004`, `OAI.MUB6.Certificate.PairSemantics.sound3006`, `OAI.MUB6.Certificate.PairSemantics.sound3009`, `OAI.MUB6.Certificate.PairSemantics.sound3010`, `OAI.MUB6.Certificate.PairSemantics.sound3011`, `OAI.MUB6.Certificate.PairSemantics.sound3012`, `OAI.MUB6.Certificate.PairSemantics.sound3013`, `OAI.MUB6.Certificate.PairSemantics.sound3014`, `OAI.MUB6.Certificate.PairSemantics.sound3015`, `OAI.MUB6.Certificate.PairSemantics.sound3016`, `OAI.MUB6.Certificate.PairSemantics.sound3017`, `OAI.MUB6.Certificate.PairSemantics.sound3018`, `OAI.MUB6.Certificate.PairSemantics.sound3019`, `OAI.MUB6.Certificate.PairSemantics.sound3020`, `OAI.MUB6.Certificate.PairSemantics.sound3021`, `OAI.MUB6.Certificate.PairSemantics.sound3022`, `OAI.MUB6.Certificate.PairSemantics.sound3023`, `OAI.MUB6.Certificate.PairSemantics.sound3024`, `OAI.MUB6.Certificate.PairSemantics.sound3025`, `OAI.MUB6.Certificate.PairSemantics.sound3026`, `OAI.MUB6.Certificate.PairSemantics.sound3027`, `OAI.MUB6.Certificate.PairSemantics.sound3028`, `OAI.MUB6.Certificate.PairSemantics.sound3029`, `OAI.MUB6.Certificate.PairSemantics.sound3030`, `OAI.MUB6.Certificate.PairSemantics.sound3031`, `OAI.MUB6.Certificate.PairSemantics.sound3032`, `OAI.MUB6.Certificate.PairSemantics.sound3033`, `OAI.MUB6.Certificate.PairSemantics.sound3034`, `OAI.MUB6.Certificate.PairSemantics.sound3035`, `OAI.MUB6.Certificate.PairSemantics.sound3036`, `OAI.MUB6.Certificate.PairSemantics.sound3038`, `OAI.MUB6.Certificate.PairSemantics.sound3039`, `OAI.MUB6.Certificate.PairSemantics.sound3040`, `OAI.MUB6.Certificate.PairSemantics.sound3041`, `OAI.MUB6.Certificate.PairSemantics.sound3042`, `OAI.MUB6.Certificate.PairSemantics.sound3043`, `OAI.MUB6.Certificate.PairSemantics.sound3044`, `OAI.MUB6.Certificate.PairSemantics.sound3045`, `OAI.MUB6.Certificate.PairSemantics.sound3047`, `OAI.MUB6.Certificate.PairSemantics.sound3048`, `OAI.MUB6.Certificate.PairSemantics.sound3049`, `OAI.MUB6.Certificate.PairSemantics.sound3050`, `OAI.MUB6.Certificate.PairSemantics.sound3051`, `OAI.MUB6.Certificate.PairSemantics.sound3053`, `OAI.MUB6.Certificate.PairSemantics.sound3054`, `OAI.MUB6.Certificate.PairSemantics.sound3056`, `OAI.MUB6.Certificate.PairSemantics.sound3058`, `OAI.MUB6.Certificate.PairSemantics.sound3059`, `OAI.MUB6.Certificate.PairSemantics.sound3060`, `OAI.MUB6.Certificate.PairSemantics.sound3061`, `OAI.MUB6.Certificate.PairSemantics.sound3062`, `OAI.MUB6.Certificate.PairSemantics.sound3063`, `OAI.MUB6.Certificate.PairSemantics.sound3065`, `OAI.MUB6.Certificate.PairSemantics.sound3066`, `OAI.MUB6.Certificate.PairSemantics.sound3067`, `OAI.MUB6.Certificate.PairSemantics.sound3068`, `OAI.MUB6.Certificate.PairSemantics.sound3069`, `OAI.MUB6.Certificate.PairSemantics.sound3071`, `OAI.MUB6.Certificate.PairSemantics.sound3072`, `OAI.MUB6.Certificate.PairSemantics.sound3073`, `OAI.MUB6.Certificate.PairSemantics.sound3074`, `OAI.MUB6.Certificate.PairSemantics.sound3075`, `OAI.MUB6.Certificate.PairSemantics.sound3076`, `OAI.MUB6.Certificate.PairSemantics.sound3077`, `OAI.MUB6.Certificate.PairSemantics.sound3078`, `OAI.MUB6.Certificate.PairSemantics.sound3079`, `OAI.MUB6.Certificate.PairSemantics.sound3080`, `OAI.MUB6.Certificate.PairSemantics.sound3081`, `OAI.MUB6.Certificate.PairSemantics.sound3082`, `OAI.MUB6.Certificate.PairSemantics.sound3083`, `OAI.MUB6.Certificate.PairSemantics.sound3084`, `OAI.MUB6.Certificate.PairSemantics.sound3085`, `OAI.MUB6.Certificate.PairSemantics.sound3086`, `OAI.MUB6.Certificate.PairSemantics.sound3090`, `OAI.MUB6.Certificate.PairSemantics.sound3091`, `OAI.MUB6.Certificate.PairSemantics.sound3092`, `OAI.MUB6.Certificate.PairSemantics.sound3093`, `OAI.MUB6.Certificate.PairSemantics.sound3094`, `OAI.MUB6.Certificate.PairSemantics.sound3095`, `OAI.MUB6.Certificate.PairSemantics.sound3096`, `OAI.MUB6.Certificate.PairSemantics.sound3097`, `OAI.MUB6.Certificate.PairSemantics.sound3098`, `OAI.MUB6.Certificate.PairSemantics.sound3099`, `OAI.MUB6.Certificate.PairSemantics.sound3100`, `OAI.MUB6.Certificate.PairSemantics.sound3101`, `OAI.MUB6.Certificate.PairSemantics.sound3102`, `OAI.MUB6.Certificate.PairSemantics.sound3105`, `OAI.MUB6.Certificate.PairSemantics.sound3106`, `OAI.MUB6.Certificate.PairSemantics.sound3107`, `OAI.MUB6.Certificate.PairSemantics.sound3108`, `OAI.MUB6.Certificate.PairSemantics.sound3109`, `OAI.MUB6.Certificate.PairSemantics.sound3110`, `OAI.MUB6.Certificate.PairSemantics.sound3111`, `OAI.MUB6.Certificate.PairSemantics.sound3112`, `OAI.MUB6.Certificate.PairSemantics.sound3113`, `OAI.MUB6.Certificate.PairSemantics.sound3114`, `OAI.MUB6.Certificate.PairSemantics.sound3115`, `OAI.MUB6.Certificate.PairSemantics.sound3116`, `OAI.MUB6.Certificate.PairSemantics.sound3118`, `OAI.MUB6.Certificate.PairSemantics.sound3119`, `OAI.MUB6.Certificate.PairSemantics.sound3120`, `OAI.MUB6.Certificate.PairSemantics.sound3121`, `OAI.MUB6.Certificate.PairSemantics.sound3122`, `OAI.MUB6.Certificate.PairSemantics.sound3123`, `OAI.MUB6.Certificate.PairSemantics.sound3124`, `OAI.MUB6.Certificate.PairSemantics.sound3125`, `OAI.MUB6.Certificate.PairSemantics.sound3128`, `OAI.MUB6.Certificate.PairSemantics.sound3129`, `OAI.MUB6.Certificate.PairSemantics.sound3130`, `OAI.MUB6.Certificate.PairSemantics.sound3131`, `OAI.MUB6.Certificate.PairSemantics.sound3133`, `OAI.MUB6.Certificate.PairSemantics.sound3135`, `OAI.MUB6.Certificate.PairSemantics.sound3136`, `OAI.MUB6.Certificate.PairSemantics.sound3138`, `OAI.MUB6.Certificate.PairSemantics.sound3139`, `OAI.MUB6.Certificate.PairSemantics.sound3140`, `OAI.MUB6.Certificate.PairSemantics.sound3141`, `OAI.MUB6.Certificate.PairSemantics.sound3142`, `OAI.MUB6.Certificate.PairSemantics.sound3144`, `OAI.MUB6.Certificate.PairSemantics.sound3145`, `OAI.MUB6.Certificate.PairSemantics.sound3146`, `OAI.MUB6.Certificate.PairSemantics.sound3150`, `OAI.MUB6.Certificate.PairSemantics.sound3151`, `OAI.MUB6.Certificate.PairSemantics.sound3152`, `OAI.MUB6.Certificate.PairSemantics.sound3153`, `OAI.MUB6.Certificate.PairSemantics.sound3155`, `OAI.MUB6.Certificate.PairSemantics.sound3158`, `OAI.MUB6.Certificate.PairSemantics.sound3159`, `OAI.MUB6.Certificate.PairSemantics.sound3160`, `OAI.MUB6.Certificate.PairSemantics.sound3161`, `OAI.MUB6.Certificate.PairSemantics.sound3162`, `OAI.MUB6.Certificate.PairSemantics.sound3163`, `OAI.MUB6.Certificate.PairSemantics.sound3164`, `OAI.MUB6.Certificate.PairSemantics.sound3166`, `OAI.MUB6.Certificate.PairSemantics.sound3167`, `OAI.MUB6.Certificate.PairSemantics.sound3168`, `OAI.MUB6.Certificate.PairSemantics.sound3169`, `OAI.MUB6.Certificate.PairSemantics.sound3170`, `OAI.MUB6.Certificate.PairSemantics.sound3171`, `OAI.MUB6.Certificate.PairSemantics.sound3172`, `OAI.MUB6.Certificate.PairSemantics.sound3173`, `OAI.MUB6.Certificate.PairSemantics.sound3174`, `OAI.MUB6.Certificate.PairSemantics.sound3176`, `OAI.MUB6.Certificate.PairSemantics.sound3178`, `OAI.MUB6.Certificate.PairSemantics.sound3179`, `OAI.MUB6.Certificate.PairSemantics.sound3180`, `OAI.MUB6.Certificate.PairSemantics.sound3181`, `OAI.MUB6.Certificate.PairSemantics.sound3183`, `OAI.MUB6.Certificate.PairSemantics.sound3184`, `OAI.MUB6.Certificate.PairSemantics.sound3185`, `OAI.MUB6.Certificate.PairSemantics.sound3186`, `OAI.MUB6.Certificate.PairSemantics.sound3187`, `OAI.MUB6.Certificate.PairSemantics.sound3188`, `OAI.MUB6.Certificate.PairSemantics.sound3189`, `OAI.MUB6.Certificate.PairSemantics.sound3191`, `OAI.MUB6.Certificate.PairSemantics.sound3192`, `OAI.MUB6.Certificate.PairSemantics.sound3193`, `OAI.MUB6.Certificate.PairSemantics.sound3194`, `OAI.MUB6.Certificate.PairSemantics.sound3195`, `OAI.MUB6.Certificate.PairSemantics.sound3196`, `OAI.MUB6.Certificate.PairSemantics.sound3197`, `OAI.MUB6.Certificate.PairSemantics.sound3198`, `OAI.MUB6.Certificate.PairSemantics.sound3199`, `OAI.MUB6.Certificate.PairSemantics.sound3200`, `OAI.MUB6.Certificate.PairSemantics.sound3201`, `OAI.MUB6.Certificate.PairSemantics.sound3202`, `OAI.MUB6.Certificate.PairSemantics.sound3203`, `OAI.MUB6.Certificate.PairSemantics.sound3204`, `OAI.MUB6.Certificate.PairSemantics.sound3205`, `OAI.MUB6.Certificate.PairSemantics.sound3206`, `OAI.MUB6.Certificate.PairSemantics.sound3208`, `OAI.MUB6.Certificate.PairSemantics.sound3211`, `OAI.MUB6.Certificate.PairSemantics.sound3212`, `OAI.MUB6.Certificate.PairSemantics.sound3213`, `OAI.MUB6.Certificate.PairSemantics.sound3214`, `OAI.MUB6.Certificate.PairSemantics.sound3215`, `OAI.MUB6.Certificate.PairSemantics.sound3216`, `OAI.MUB6.Certificate.PairSemantics.sound3217`, `OAI.MUB6.Certificate.PairSemantics.sound3218`, `OAI.MUB6.Certificate.PairSemantics.sound3219`, `OAI.MUB6.Certificate.PairSemantics.sound3221`, `OAI.MUB6.Certificate.PairSemantics.sound3222`, `OAI.MUB6.Certificate.PairSemantics.sound3223`, `OAI.MUB6.Certificate.PairSemantics.sound3224`, `OAI.MUB6.Certificate.PairSemantics.sound3226`, `OAI.MUB6.Certificate.PairSemantics.sound3227`, `OAI.MUB6.Certificate.PairSemantics.sound3228`, `OAI.MUB6.Certificate.PairSemantics.sound3230`, `OAI.MUB6.Certificate.PairSemantics.sound3231`, `OAI.MUB6.Certificate.PairSemantics.sound3233`, `OAI.MUB6.Certificate.PairSemantics.sound3234`, `OAI.MUB6.Certificate.PairSemantics.sound3235`, `OAI.MUB6.Certificate.PairSemantics.sound3237`, `OAI.MUB6.Certificate.PairSemantics.sound3238`, `OAI.MUB6.Certificate.PairSemantics.sound3239`, `OAI.MUB6.Certificate.PairSemantics.sound3240`, `OAI.MUB6.Certificate.PairSemantics.sound3241`, `OAI.MUB6.Certificate.PairSemantics.sound3242`, `OAI.MUB6.Certificate.PairSemantics.sound3243`, `OAI.MUB6.Certificate.PairSemantics.sound3244`, `OAI.MUB6.Certificate.PairSemantics.sound3246`, `OAI.MUB6.Certificate.PairSemantics.sound3247`, `OAI.MUB6.Certificate.PairSemantics.sound3248`, `OAI.MUB6.Certificate.PairSemantics.sound3249`, `OAI.MUB6.Certificate.PairSemantics.sound3250`, `OAI.MUB6.Certificate.PairSemantics.sound3251`, `OAI.MUB6.Certificate.PairSemantics.sound3253`, `OAI.MUB6.Certificate.PairSemantics.sound3254`, `OAI.MUB6.Certificate.PairSemantics.sound3255`, `OAI.MUB6.Certificate.PairSemantics.sound3256`, `OAI.MUB6.Certificate.PairSemantics.sound3258`, `OAI.MUB6.Certificate.PairSemantics.sound3259`, `OAI.MUB6.Certificate.PairSemantics.sound3261`, `OAI.MUB6.Certificate.PairSemantics.sound3262`, `OAI.MUB6.Certificate.PairSemantics.sound3263`, `OAI.MUB6.Certificate.PairSemantics.sound3266`, `OAI.MUB6.Certificate.PairSemantics.sound3267`, `OAI.MUB6.Certificate.PairSemantics.sound3268`, `OAI.MUB6.Certificate.PairSemantics.sound3269`, `OAI.MUB6.Certificate.PairSemantics.sound3270`, `OAI.MUB6.Certificate.PairSemantics.sound3271`, `OAI.MUB6.Certificate.PairSemantics.sound3273`, `OAI.MUB6.Certificate.PairSemantics.sound3275`, `OAI.MUB6.Certificate.PairSemantics.sound3276`, `OAI.MUB6.Certificate.PairSemantics.sound3277`, `OAI.MUB6.Certificate.PairSemantics.sound3279`, `OAI.MUB6.Certificate.PairSemantics.sound3280`, `OAI.MUB6.Certificate.PairSemantics.sound3281`, `OAI.MUB6.Certificate.PairSemantics.sound3282`, `OAI.MUB6.Certificate.PairSemantics.sound3283`, `OAI.MUB6.Certificate.PairSemantics.sound3284`, `OAI.MUB6.Certificate.PairSemantics.sound3288`, `OAI.MUB6.Certificate.PairSemantics.sound3289`, `OAI.MUB6.Certificate.PairSemantics.sound3290`, `OAI.MUB6.Certificate.PairSemantics.sound3291`, `OAI.MUB6.Certificate.PairSemantics.sound3292`, `OAI.MUB6.Certificate.PairSemantics.sound3293`, `OAI.MUB6.Certificate.PairSemantics.sound3294`, `OAI.MUB6.Certificate.PairSemantics.sound3295`, `OAI.MUB6.Certificate.PairSemantics.sound3296`, `OAI.MUB6.Certificate.PairSemantics.sound3297`, `OAI.MUB6.Certificate.PairSemantics.sound3298`, `OAI.MUB6.Certificate.PairSemantics.sound3299`, `OAI.MUB6.Certificate.PairSemantics.sound3300`, `OAI.MUB6.Certificate.PairSemantics.sound3301`, `OAI.MUB6.Certificate.PairSemantics.sound3302`, `OAI.MUB6.Certificate.PairSemantics.sound3304`, `OAI.MUB6.Certificate.PairSemantics.sound3305`, `OAI.MUB6.Certificate.PairSemantics.sound3307`, `OAI.MUB6.Certificate.PairSemantics.sound3308`, `OAI.MUB6.Certificate.PairSemantics.sound3310`, `OAI.MUB6.Certificate.PairSemantics.sound3311`, `OAI.MUB6.Certificate.PairSemantics.sound3312`, `OAI.MUB6.Certificate.PairSemantics.sound3313`, `OAI.MUB6.Certificate.PairSemantics.sound3314`, `OAI.MUB6.Certificate.PairSemantics.sound3315`, `OAI.MUB6.Certificate.PairSemantics.sound3316`, `OAI.MUB6.Certificate.PairSemantics.sound3317`, `OAI.MUB6.Certificate.PairSemantics.sound3319`, `OAI.MUB6.Certificate.PairSemantics.sound3322`, `OAI.MUB6.Certificate.PairSemantics.sound3323`, `OAI.MUB6.Certificate.PairSemantics.sound3324`, `OAI.MUB6.Certificate.PairSemantics.sound3325`, `OAI.MUB6.Certificate.PairSemantics.sound3327`, `OAI.MUB6.Certificate.PairSemantics.sound3328`, `OAI.MUB6.Certificate.PairSemantics.sound3332`, `OAI.MUB6.Certificate.PairSemantics.sound3333`, `OAI.MUB6.Certificate.PairSemantics.sound3334`, `OAI.MUB6.Certificate.PairSemantics.sound3335`, `OAI.MUB6.Certificate.PairSemantics.sound3336`, `OAI.MUB6.Certificate.PairSemantics.sound3338`, `OAI.MUB6.Certificate.PairSemantics.sound3340`, `OAI.MUB6.Certificate.PairSemantics.sound3341`, `OAI.MUB6.Certificate.PairSemantics.sound3342`, `OAI.MUB6.Certificate.PairSemantics.sound3343`, `OAI.MUB6.Certificate.PairSemantics.sound3344`, `OAI.MUB6.Certificate.PairSemantics.sound3345`, `OAI.MUB6.Certificate.PairSemantics.sound3346`, `OAI.MUB6.Certificate.PairSemantics.sound3347`, `OAI.MUB6.Certificate.PairSemantics.sound3348`, `OAI.MUB6.Certificate.PairSemantics.sound3349`, `OAI.MUB6.Certificate.PairSemantics.sound3350`, `OAI.MUB6.Certificate.PairSemantics.sound3351`, `OAI.MUB6.Certificate.PairSemantics.sound3352`, `OAI.MUB6.Certificate.PairSemantics.sound3353`, `OAI.MUB6.Certificate.PairSemantics.sound3354`, `OAI.MUB6.Certificate.PairSemantics.sound3355`, `OAI.MUB6.Certificate.PairSemantics.sound3356`, `OAI.MUB6.Certificate.PairSemantics.sound3357`, `OAI.MUB6.Certificate.PairSemantics.sound3359`, `OAI.MUB6.Certificate.PairSemantics.sound3360`, `OAI.MUB6.Certificate.PairSemantics.sound3361`, `OAI.MUB6.Certificate.PairSemantics.sound3362`, `OAI.MUB6.Certificate.PairSemantics.sound3364`, `OAI.MUB6.Certificate.PairSemantics.sound3365`, `OAI.MUB6.Certificate.PairSemantics.sound3366`, `OAI.MUB6.Certificate.PairSemantics.sound3367`, `OAI.MUB6.Certificate.PairSemantics.sound3369`, `OAI.MUB6.Certificate.PairSemantics.sound3370`, `OAI.MUB6.Certificate.PairSemantics.sound3371`, `OAI.MUB6.Certificate.PairSemantics.sound3372`, `OAI.MUB6.Certificate.PairSemantics.sound3373`, `OAI.MUB6.Certificate.PairSemantics.sound3375`, `OAI.MUB6.Certificate.PairSemantics.sound3376`, `OAI.MUB6.Certificate.PairSemantics.sound3377`, `OAI.MUB6.Certificate.PairSemantics.sound3378`, `OAI.MUB6.Certificate.PairSemantics.sound3380`, `OAI.MUB6.Certificate.PairSemantics.sound3381`, `OAI.MUB6.Certificate.PairSemantics.sound3382`, `OAI.MUB6.Certificate.PairSemantics.sound3383`, `OAI.MUB6.Certificate.PairSemantics.sound3384`, `OAI.MUB6.Certificate.PairSemantics.sound3385`, `OAI.MUB6.Certificate.PairSemantics.sound3388`, `OAI.MUB6.Certificate.PairSemantics.sound3390`, `OAI.MUB6.Certificate.PairSemantics.sound3391`, `OAI.MUB6.Certificate.PairSemantics.sound3392`, `OAI.MUB6.Certificate.PairSemantics.sound3393`, `OAI.MUB6.Certificate.PairSemantics.sound3394`, `OAI.MUB6.Certificate.PairSemantics.sound3395`, `OAI.MUB6.Certificate.PairSemantics.sound3396`, `OAI.MUB6.Certificate.PairSemantics.sound3400`, `OAI.MUB6.Certificate.PairSemantics.sound3401`, `OAI.MUB6.Certificate.PairSemantics.sound3402`, `OAI.MUB6.Certificate.PairSemantics.sound3405`, `OAI.MUB6.Certificate.PairSemantics.sound3407`, `OAI.MUB6.Certificate.PairSemantics.sound3408`, `OAI.MUB6.Certificate.PairSemantics.sound3411`, `OAI.MUB6.Certificate.PairSemantics.sound3412`, `OAI.MUB6.Certificate.PairSemantics.sound3413`, `OAI.MUB6.Certificate.PairSemantics.sound3414`, `OAI.MUB6.Certificate.PairSemantics.sound3415`, `OAI.MUB6.Certificate.PairSemantics.sound3416`, `OAI.MUB6.Certificate.PairSemantics.sound3417`, `OAI.MUB6.Certificate.PairSemantics.sound3418`, `OAI.MUB6.Certificate.PairSemantics.sound3420`, `OAI.MUB6.Certificate.PairSemantics.sound3421`, `OAI.MUB6.Certificate.PairSemantics.sound3422`, `OAI.MUB6.Certificate.PairSemantics.sound3423`, `OAI.MUB6.Certificate.PairSemantics.sound3424`, `OAI.MUB6.Certificate.PairSemantics.sound3425`, `OAI.MUB6.Certificate.PairSemantics.sound3426`, `OAI.MUB6.Certificate.PairSemantics.sound3428`, `OAI.MUB6.Certificate.PairSemantics.sound3431`, `OAI.MUB6.Certificate.PairSemantics.sound3433`, `OAI.MUB6.Certificate.PairSemantics.sound3434`, `OAI.MUB6.Certificate.PairSemantics.sound3435`, `OAI.MUB6.Certificate.PairSemantics.sound3436`, `OAI.MUB6.Certificate.PairSemantics.sound3437`, `OAI.MUB6.Certificate.PairSemantics.sound3438`, `OAI.MUB6.Certificate.PairSemantics.sound3440`, `OAI.MUB6.Certificate.PairSemantics.sound3441`, `OAI.MUB6.Certificate.PairSemantics.sound3445`, `OAI.MUB6.Certificate.PairSemantics.sound3447`, `OAI.MUB6.Certificate.PairSemantics.sound3449`, `OAI.MUB6.Certificate.PairSemantics.sound3454`, `OAI.MUB6.Certificate.PairSemantics.sound3456`, `OAI.MUB6.Certificate.PairSemantics.sound3458`, `OAI.MUB6.Certificate.PairSemantics.sound3459`, `OAI.MUB6.Certificate.PairSemantics.sound3460`, `OAI.MUB6.Certificate.PairSemantics.sound3461`, `OAI.MUB6.Certificate.PairSemantics.sound3462`, `OAI.MUB6.Certificate.PairSemantics.sound3463`, `OAI.MUB6.Certificate.PairSemantics.sound3467`, `OAI.MUB6.Certificate.PairSemantics.sound3468`, `OAI.MUB6.Certificate.PairSemantics.sound381`, `OAI.MUB6.Certificate.PairSemantics.sound659`, `OAI.MUB6.Certificate.PairSemantics.sound711`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound0`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound1`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound10`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound101`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound102`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound103`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound104`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound105`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound106`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound107`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound108`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound111`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound112`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound113`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound114`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound115`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound116`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound117`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound118`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound119`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound12`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound120`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound121`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound124`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound125`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound126`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound127`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound128`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound129`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound13`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound130`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound131`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound132`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound133`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound134`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound135`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound136`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound137`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound139`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound14`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound140`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound141`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound142`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound146`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound148`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound15`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound150`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound151`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound153`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound154`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound155`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound156`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound157`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound158`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound159`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound16`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound160`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound161`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound162`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound163`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound164`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound165`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound166`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound167`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound168`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound17`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound170`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound171`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound174`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound175`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound176`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound177`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound178`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound179`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound18`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound180`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound182`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound184`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound185`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound186`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound187`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound188`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound19`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound190`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound191`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound192`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound193`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound194`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound195`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound196`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound197`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound198`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound199`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound2`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound20`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound200`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound201`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound202`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound204`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound205`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound207`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound208`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound209`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound21`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound210`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound211`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound213`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound214`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound216`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound218`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound219`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound22`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound221`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound222`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound223`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound225`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound226`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound227`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound228`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound23`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound230`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound231`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound232`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound233`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound234`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound235`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound236`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound237`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound238`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound239`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound24`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound240`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound241`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound242`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound243`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound245`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound246`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound248`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound249`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound25`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound250`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound253`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound254`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound26`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound27`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound28`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound30`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound31`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound32`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound35`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound36`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound38`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound39`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound4`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound40`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound41`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound42`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound43`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound44`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound45`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound47`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound49`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound5`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound51`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound52`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound53`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound54`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound56`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound57`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound58`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound59`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound6`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound60`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound61`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound62`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound63`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound64`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound65`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound66`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound67`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound72`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound74`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound76`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound77`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound78`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound79`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound80`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound81`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound82`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound83`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound84`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound85`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound86`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound87`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound89`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound9`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound90`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound91`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound92`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound93`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound94`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound95`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound96`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound97`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound98`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound99`, `OAI.MUB6.Certificate.PairTargetSemantics.partition12`, `OAI.MUB6.Certificate.PairTargetSemantics.partition19`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm11`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm23`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm26` and `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm7`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix24 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-3, 3], ![1, -1], ![3, -3]]

def pivotMatrix25 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-3, 3], ![2, -2], ![2, -2]]

def pivotMatrix26 : Matrix (Fin 4) (Fin 2) ℤ := ![![1, -1], ![-3, 3], ![1, -1], ![1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix201 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-2, 0, 2], ![0, -2, 2], ![1, 3, -4]]

def pivotMatrix203 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, 2, -2], ![2, -1, -1]]

def pivotMatrix204 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, 3, -3], ![2, -2, 0]]

def pivotMatrix205 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![1, -3, 2], ![1, 4, -5]]

def pivotMatrix206 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![1, -2, 1], ![1, 3, -4]]

def pivotMatrix207 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![0, 1, -1], ![2, -2, 0]]

def pivotMatrix208 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![1, -4, 3], ![1, 3, -4]]

def pivotMatrix209 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![1, -3, 2], ![1, 2, -3]]

def pivotMatrix210 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![1, -2, 1], ![1, 1, -2]]

def pivotMatrix214 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-2, 0, 2], ![0, 3, -3], ![1, -3, 2]]

def pivotMatrix215 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-2, 0, 2], ![0, 3, -3], ![1, -2, 1]]

def pivotMatrix216 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-2, 0, 2], ![0, 4, -4], ![1, -4, 3]]

def pivotMatrix217 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-2, 0, 2], ![0, 4, -4], ![1, -3, 2]]

def pivotMatrix221 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-2, 1, 1], ![0, -3, 3], ![1, 3, -4]]

def pivotMatrix222 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-2, 1, 1], ![0, -3, 3], ![1, 2, -3]]

def pivotMatrix226 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-2, 1, 1], ![0, -2, 2], ![1, 2, -3]]

def pivotMatrix227 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1]]

def pivotMatrix228 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 1, 1], ![1, -3, 2], ![1, 3, -4]]

def pivotMatrix229 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 2, -3]]

def pivotMatrix230 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2]]

def pivotMatrix231 : Matrix (Fin 5) (Fin 2) ℤ := ![![1, -1], ![-2, 2], ![-2, 2], ![1, -1], ![2, -2]]

def pivotMatrix232 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]

def pivotMatrix233 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, -4, 5], ![-1, 2, -1], ![1, 2, -3]]

def pivotMatrix235 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, -4, 5], ![-1, 3, -2], ![1, 1, -2]]

def pivotMatrix236 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, -4, 5], ![-1, 4, -3], ![1, 0, -1]]

def pivotMatrix237 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -4, 5], ![0, 1, -1], ![1, 2, -3]]

def pivotMatrix238 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -4, 5], ![0, 2, -2], ![1, 1, -2]]

def pivotMatrix239 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -4, 5], ![0, 3, -3], ![1, 0, -1]]

def pivotMatrix240 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, -4, 5], ![0, 2, -2], ![0, 2, -2]]

def pivotMatrix241 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![1, 1, -2], ![1, 2, -3]]

def pivotMatrix242 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![1, -1, 0], ![1, 3, -4]]

def pivotMatrix243 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![1, 0, -1], ![1, 2, -3]]

def pivotMatrix244 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![1, 1, -2], ![1, 1, -2]]

def pivotMatrix245 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-1, -3, 4], ![-1, 2, -1], ![1, 2, -3]]

def pivotMatrix246 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, -3, 4], ![-1, 2, -1], ![1, 1, -2]]

def pivotMatrix247 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-1, -3, 4], ![-1, 3, -2], ![1, 1, -2]]

def pivotMatrix248 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, -3, 4], ![-1, 3, -2], ![1, 0, -1]]

def pivotMatrix249 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-1, -3, 4], ![-1, 4, -3], ![1, 0, -1]]

def pivotMatrix250 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -3, 4], ![0, 2, -2], ![1, 2, -3]]

def pivotMatrix251 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -3, 4], ![0, 3, -3], ![1, 1, -2]]

def pivotMatrix252 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -3, 4], ![0, 4, -4], ![1, 0, -1]]

def pivotMatrix253 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -3, 4], ![0, 1, -1], ![1, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix1952 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![2, -2, 0, 0]]

def pivotMatrix1953 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, -1, 3], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def pivotMatrix1954 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def pivotMatrix1955 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -2, 1, -1]]

def pivotMatrix1956 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def pivotMatrix1957 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def pivotMatrix1958 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def pivotMatrix1959 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, -2, 1, -1]]

def pivotMatrix1960 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def pivotMatrix1961 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -1, 3], ![0, 0, 2, -2], ![1, -2, 1, 0], ![1, 1, -1, -1]]

def pivotMatrix1962 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, -1, 3], ![0, 0, 2, -2], ![1, -2, 1, 0], ![1, 1, -2, 0]]

def pivotMatrix1963 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -2, 1, 0]]

def pivotMatrix1964 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 1, -1]]

def pivotMatrix1965 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -2, 1, 0]]

def pivotMatrix1966 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -1, 3], ![0, 0, 3, -3], ![0, 1, -1, 0], ![2, -2, 0, 0]]

def pivotMatrix1967 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 0, -1, 3], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def pivotMatrix1968 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, -1, 3], ![0, 1, -2, 1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def pivotMatrix1969 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, -1, 3], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def pivotMatrix1970 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, -1, 3], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def pivotMatrix1971 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 2, -2]]

def pivotMatrix1972 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 1, -1]]

def pivotMatrix1973 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def pivotMatrix1974 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -1, 3], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def pivotMatrix1975 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -1, 3], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 0, 2, -3]]

def pivotMatrix1976 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -1, 3], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 1, -2]]

def pivotMatrix1977 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -1, 3], ![0, 1, -1, 0], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def pivotMatrix1978 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -1, 3], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def pivotMatrix1979 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -1, 3], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def pivotMatrix1980 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -1, 3], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, -1, 0]]

def pivotMatrix1981 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -1, 3], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 3, -3]]

def pivotMatrix1982 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -1, 3], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def pivotMatrix1983 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -1, 3], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, -1, 2, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix1984 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -1, 3], ![0, 1, 2, -3], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def pivotMatrix1985 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -1, 3], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, -1, 1, -1]]

def pivotMatrix1986 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -1, 3], ![0, 1, 3, -4], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def pivotMatrix1987 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -1, 3], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def pivotMatrix1988 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, -2, 0, 2], ![0, 1, 3, -4], ![2, 0, -2, 0]]

def pivotMatrix1989 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, -2, 0, 2], ![1, 0, 3, -4], ![1, 1, -2, 0]]

def pivotMatrix1990 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 0, 2], ![0, -2, 1, 1], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def pivotMatrix1991 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, -2, 1], ![1, 1, 2, -4]]

def pivotMatrix1992 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, -2, 1, 1], ![1, 0, -2, 1], ![1, 1, 2, -4]]

def pivotMatrix1993 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, -2, 1, 1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def pivotMatrix1994 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, -2, 1, 1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def pivotMatrix1995 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, 0, 2], ![0, -2, 1, 1], ![1, 0, 1, -2], ![1, 1, -2, 0]]

def pivotMatrix1996 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def pivotMatrix1997 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def pivotMatrix1998 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def pivotMatrix1999 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def pivotMatrix2000 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, -2, 2, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def pivotMatrix2001 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def pivotMatrix2002 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, 0, 2], ![0, -2, 2, 0], ![1, 0, -2, 1], ![1, 1, 0, -2]]

def pivotMatrix2003 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, 0, 2], ![0, -2, 2, 0], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def pivotMatrix2004 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def pivotMatrix2005 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, 1, -2, 0]]

def pivotMatrix2006 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 2, -2, 0], ![1, 0, 3, -4]]

def pivotMatrix2007 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 0, 2], ![0, -1, 1, 0], ![1, 1, -2, 0], ![1, 1, 1, -3]]

def pivotMatrix2008 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, 2, -3, 1], ![2, -1, 1, -2]]

def pivotMatrix2009 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 0, 2], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 1, -3, 1]]

def pivotMatrix2010 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 0, 2], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 1, -3, 1]]

def pivotMatrix2011 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 0, 2], ![0, 2, -3, 1], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def pivotMatrix2012 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 0, 2], ![0, 2, -3, 1], ![1, -1, 1, -1], ![1, 0, 2, -3]]

def pivotMatrix2013 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def pivotMatrix2014 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, 0, 2], ![0, -1, 1, 0], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def pivotMatrix2015 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -1, -1, 0]]

def pivotMatrix2016 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, 0, 2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def pivotMatrix2017 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, 0, 2], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def pivotMatrix2018 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, 0, 2], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def pivotMatrix2019 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, 0, 2], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -3, 1]]

def pivotMatrix2020 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, 0, 2], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 1, -3, 1]]

def pivotMatrix2021 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, 0, 2], ![0, -1, 2, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def pivotMatrix2022 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 1, -3, 1]]

def pivotMatrix2023 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def pivotMatrix2024 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![2, -2, 3, -3]]

def pivotMatrix2025 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, -2, 2, -2]]

def pivotMatrix2026 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, 3, -4], ![2, -2, 0, 0]]

def pivotMatrix2027 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, 0, -2, 2], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def pivotMatrix2028 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, 0, 2], ![0, 0, -2, 2], ![1, -2, 3, -2], ![1, 1, -1, -1]]

def pivotMatrix2029 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 2, -1, -1], ![1, -2, 3, -2]]

def pivotMatrix2030 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![2, -2, 0, 0]]

def pivotMatrix2031 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 0, 2], ![0, 1, -2, 1], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def pivotMatrix2032 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 3, -3]]

def pivotMatrix2033 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![2, -2, -1, 1]]

def pivotMatrix2034 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, 0, 2], ![0, 1, -3, 2], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def pivotMatrix2035 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def pivotMatrix2036 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, -2, 1, -1]]

def pivotMatrix2037 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, 0, 2], ![0, 1, -3, 2], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def pivotMatrix2038 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 0, 0, 2], ![0, 1, -3, 2], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def pivotMatrix2039 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, 1, -2, 1], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def pivotMatrix2040 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, 1, -2, 1], ![1, -2, 2, -1], ![1, 0, 1, -2]]

def pivotMatrix2041 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, 1, -2, 1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def pivotMatrix2042 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def pivotMatrix2043 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, 0, 2], ![0, 1, -2, 1], ![1, -2, 3, -2], ![1, 0, -1, 0]]

def pivotMatrix2044 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -2, 2, -1]]

def pivotMatrix2045 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def pivotMatrix2046 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def pivotMatrix2047 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, 1, -1, 0], ![1, -2, -1, 2], ![1, 0, 3, -4]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix2048 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, -1, 3, -3]]

def pivotMatrix2049 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, -2, 1]]

def pivotMatrix2050 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 0, -2, 1]]

def pivotMatrix2051 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, 1, 3, -4], ![1, -2, -1, 2], ![1, 0, -1, 0]]

def pivotMatrix2052 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, 1, 3, -4], ![1, -2, 0, 1], ![1, 0, -2, 1]]

def pivotMatrix2053 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, 1, 3, -4], ![1, -1, -2, 2], ![1, -1, 0, 0]]

def pivotMatrix2054 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, -1, 1]]

def pivotMatrix2055 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def pivotMatrix2056 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 1, 1], ![0, -2, 1, 1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def pivotMatrix2057 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 1, 1], ![0, -2, 1, 1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def pivotMatrix2058 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 1, 1], ![0, -1, -2, 3], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def pivotMatrix2059 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 1, 1], ![0, -1, -1, 2], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def pivotMatrix2060 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 1, -2, 1], ![1, 1, 2, -4]]

def pivotMatrix2061 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![2, -1, 2, -3]]

def pivotMatrix2062 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 1, 1], ![0, -1, -1, 2], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def pivotMatrix2063 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 1, 1], ![0, -1, -1, 2], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def pivotMatrix2064 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 1, 1], ![0, -1, 0, 1], ![1, 1, -2, 0], ![1, 1, 1, -3]]

def pivotMatrix2065 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 1, 1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -1, -1, 0]]

def pivotMatrix2066 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 1, 1], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, -1, -2, 1]]

def pivotMatrix2067 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 1, 1], ![0, 1, -3, 2], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def pivotMatrix2068 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 1, 1], ![0, 1, -3, 2], ![1, -1, 1, -1], ![1, 1, 1, -3]]

def pivotMatrix2069 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 1, 1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def pivotMatrix2070 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def pivotMatrix2071 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 1, 1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def pivotMatrix2072 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 1, 1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def pivotMatrix2073 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 1, 1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def pivotMatrix2074 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 1, 1], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -3, 1]]

def pivotMatrix2075 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 1, 1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 1, -3, 1]]

def pivotMatrix2076 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 1, 1], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def pivotMatrix2077 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def pivotMatrix2078 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, -2, 1, -1]]

def pivotMatrix2079 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 1, 1], ![0, 0, -2, 2], ![1, -2, 0, 1], ![1, 1, 2, -4]]

def pivotMatrix2080 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, 1, 1], ![0, 0, -2, 2], ![1, -2, 2, -1], ![1, 1, -1, -1]]

def pivotMatrix2081 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 1, 1], ![0, 1, -2, 1], ![1, -2, 0, 1], ![1, 1, 2, -4]]

def pivotMatrix2082 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, -2, -1, 1]]

def pivotMatrix2083 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 1, 1], ![0, 1, -1, 0], ![1, -2, -1, 2], ![1, 1, 2, -4]]

def pivotMatrix2084 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 1, 1], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 1, -1, -1]]

def pivotMatrix2085 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 1, 1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def pivotMatrix2086 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, 1, 1], ![0, 1, -3, 2], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def pivotMatrix2087 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def pivotMatrix2088 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 1, 1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 1, -1]]

def pivotMatrix2089 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

def pivotMatrix2090 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]

def pivotMatrix2091 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

def pivotMatrix2092 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def pivotMatrix2093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

def pivotMatrix2094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]

def pivotMatrix2095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

def pivotMatrix2096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

def pivotMatrix2097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]

def pivotMatrix2098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

def pivotMatrix2099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]

def pivotMatrix2100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]

def pivotMatrix2101 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]

def pivotMatrix2102 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]

def pivotMatrix2103 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]

def pivotMatrix2104 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

def pivotMatrix2105 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix2106 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![-1, 3, -2], ![1, -3, 2], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix2107 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -1, 0], ![-2, 0, 2], ![-1, 4, -3], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix2108 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![-1, 4, -3], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix2109 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def pivotMatrix2110 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def pivotMatrix2111 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![0, -3, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix2112 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

def pivotMatrix2113 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 3, -4]]

def pivotMatrix2114 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

def pivotMatrix2115 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def pivotMatrix2116 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix2117 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, -2, 2], ![0, 4, -4], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix2118 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def pivotMatrix2119 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def pivotMatrix2120 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix2121 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix2122 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def pivotMatrix2123 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 4, -5]]

def pivotMatrix2124 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 3, -4]]

def pivotMatrix2125 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def pivotMatrix2126 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def pivotMatrix2127 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 3, -4]]

def pivotMatrix2128 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def pivotMatrix2129 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def pivotMatrix2130 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def pivotMatrix2131 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix2132 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix2133 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, -1, 1], ![0, 4, -4], ![1, -2, 1], ![1, 0, -1]]

def pivotMatrix2134 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

def pivotMatrix2135 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

def pivotMatrix2136 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def pivotMatrix2137 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix2138 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

def pivotMatrix2139 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

def pivotMatrix2140 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

def pivotMatrix2141 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1]]

def pivotMatrix2142 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0]]

def pivotMatrix2143 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 0, 2, 0], ![0, -1, -3, 4], ![0, 1, 1, -2], ![1, 1, 0, -2]]

def pivotMatrix2144 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, 3, -1], ![0, -1, -3, 4], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def pivotMatrix2145 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, 3, -1], ![0, -1, -2, 3], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def pivotMatrix2146 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, 3, -1], ![0, 0, -2, 2], ![1, -2, -1, 2], ![1, 1, 0, -2]]

def pivotMatrix2147 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, 3, -1], ![0, 1, 0, -1], ![1, -2, -3, 4], ![1, 0, 0, -1]]

def pivotMatrix2148 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -3, 4], ![0, -1, 2, -1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def pivotMatrix2149 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 1, -3, 4], ![0, -1, 2, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def pivotMatrix2150 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 1, -3, 4], ![0, -1, 2, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def pivotMatrix2151 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 1, -3, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def pivotMatrix2152 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 1, -3, 4], ![0, -1, 3, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def pivotMatrix2153 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -3, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def pivotMatrix2154 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -3, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, -2, 0, 0]]

def pivotMatrix2155 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -3, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, 0, 0]]

def pivotMatrix2156 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -3, 4], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def pivotMatrix2157 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -3, 4], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def pivotMatrix2158 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -3, 4], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def pivotMatrix2159 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 1, -3, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def pivotMatrix2160 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 1, -3, 4], ![0, 0, 3, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def pivotMatrix2161 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 1, -2, 3], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def pivotMatrix2162 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 1, -2, 3], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def pivotMatrix2163 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -2, 3], ![0, -1, 2, -1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def pivotMatrix2164 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -2, 3], ![0, -1, 2, -1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def pivotMatrix2165 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def pivotMatrix2166 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -2, 3], ![0, -1, 2, -1], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def pivotMatrix2167 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -2, 3], ![0, -1, 2, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def pivotMatrix2168 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 1, -2, 3], ![0, -1, 2, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def pivotMatrix2169 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 1, -2, 3], ![0, -1, 2, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def pivotMatrix2170 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 1, -2, 3], ![0, -1, 2, -1], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def pivotMatrix2171 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 1, -2, 3], ![0, -1, 2, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def pivotMatrix2172 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, -1, -1, 1]]

def pivotMatrix2173 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def pivotMatrix2174 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -2, 3], ![0, -1, 3, -2], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def pivotMatrix2175 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 1, -2, 3], ![0, -1, 3, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix2176 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 1, -2, 3], ![0, -1, 3, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def pivotMatrix2177 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 1, -2, 3], ![0, -1, 3, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def pivotMatrix2178 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def pivotMatrix2179 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -2, 3], ![0, 0, 1, -1], ![1, -2, 1, 0], ![1, 1, 1, -3]]

def pivotMatrix2180 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -2, 3], ![0, 0, 1, -1], ![1, -2, 2, -1], ![1, 1, 0, -2]]

def pivotMatrix2181 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -2, 3], ![0, 0, 2, -2], ![1, -2, 1, 0], ![1, 1, 0, -2]]

def pivotMatrix2182 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -2, 3], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def pivotMatrix2183 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def pivotMatrix2184 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, -2, -1, 1]]

def pivotMatrix2185 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -2, 3], ![0, 0, 1, -1], ![1, -2, 1, 0], ![1, 1, -1, -1]]

def pivotMatrix2186 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, 0, 0]]

def pivotMatrix2187 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, -1, 1]]

def pivotMatrix2188 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -2, 3], ![0, 0, 2, -2], ![1, -2, 0, 1], ![1, 1, -1, -1]]

def pivotMatrix2189 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -2, 3], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def pivotMatrix2190 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -2, 3], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def pivotMatrix2191 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -2, 3], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def pivotMatrix2192 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -2, 3], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def pivotMatrix2193 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -2, 3], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def pivotMatrix2194 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -2, 3], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, -1, 1, -1]]

def pivotMatrix2195 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -2, 3], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def pivotMatrix2196 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 1, -2, 3], ![0, 0, 2, -2], ![1, -2, 1, 0], ![1, 0, 0, -1]]

def pivotMatrix2197 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 1, -2, 3], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def pivotMatrix2198 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 1, -2, 3], ![0, 0, 2, -2], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def pivotMatrix2199 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, -1, 1]]

def pivotMatrix2200 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 1, -2, 3], ![0, 0, 3, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def pivotMatrix2201 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 1, -2, 3], ![0, 0, 3, -3], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def pivotMatrix2202 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 1, -1, 2], ![0, -1, -1, 2], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def pivotMatrix2203 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 1, -1, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def pivotMatrix2204 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 1, -1, 2], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def pivotMatrix2205 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 0, -2, 2], ![1, 1, 1, -3]]

def pivotMatrix2206 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -1, 2], ![0, -1, 2, -1], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def pivotMatrix2207 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -1, 2], ![0, -1, 2, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def pivotMatrix2208 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -1, 2], ![0, -1, 2, -1], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def pivotMatrix2209 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -1, 2], ![0, -1, 3, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def pivotMatrix2210 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 1, -1, 2], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def pivotMatrix2211 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 1, -1, 2], ![0, -1, 3, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def pivotMatrix2212 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 1, -1, 2], ![0, -1, 3, -2], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def pivotMatrix2213 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 1, -1, 2], ![0, -1, 3, -2], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def pivotMatrix2214 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def pivotMatrix2215 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 1, -1, 2], ![0, 0, -2, 2], ![1, -2, 2, -1], ![1, 0, 1, -2]]

def pivotMatrix2216 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 1, -1, 2], ![0, 0, -2, 2], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def pivotMatrix2217 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, -2, 2, -1]]

def pivotMatrix2218 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def pivotMatrix2219 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![2, -2, 0, 0]]

def pivotMatrix2220 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -1, 2], ![0, 0, -1, 1], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def pivotMatrix2221 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -1, 2], ![0, 0, -1, 1], ![1, -2, 2, -1], ![1, 1, 1, -3]]

def pivotMatrix2222 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def pivotMatrix2223 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -1, 2], ![0, 0, 1, -1], ![1, -2, 2, -1], ![1, 1, -1, -1]]

def pivotMatrix2224 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def pivotMatrix2225 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -1, 2], ![0, 0, 2, -2], ![1, -2, 1, 0], ![1, 1, -1, -1]]

def pivotMatrix2226 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -1, 2], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def pivotMatrix2227 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -1, 2], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 1, -2]]

def pivotMatrix2228 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def pivotMatrix2229 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -1, 2], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def pivotMatrix2230 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -1, 2], ![0, 1, 3, -4], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def pivotMatrix2231 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -1, 2], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def pivotMatrix2232 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![2, -2, 1, -1]]

def pivotMatrix2233 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, -2, -2, 2]]

def pivotMatrix2234 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, -2, 0, 0]]

def pivotMatrix2235 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, -1, 1]]

def pivotMatrix2236 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, -2, 2]]

def pivotMatrix2237 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -1, 2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def pivotMatrix2238 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -1, 2], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def pivotMatrix2239 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -1, 2], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 0, -2, 1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix2240 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, 1, -1]]

def pivotMatrix2241 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 1, -1, 2], ![0, 0, 2, -2], ![1, -2, 1, 0], ![1, 0, -2, 1]]

def pivotMatrix2242 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 1, -1, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -1, 0, 0]]

def pivotMatrix2243 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 1, -1, 2], ![0, 0, 3, -3], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def pivotMatrix2244 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 1, -1, 2], ![0, 0, 3, -3], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def pivotMatrix2245 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 1, -1, 2], ![0, 0, 3, -3], ![1, -1, -2, 2], ![1, -1, 0, 0]]

def pivotMatrix2246 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 1, -1, 2], ![0, 0, 3, -3], ![1, -1, -1, 1], ![1, -1, -1, 1]]

def pivotMatrix2247 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 1, 0, 1], ![0, -1, -2, 3], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def pivotMatrix2248 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 1, 0, 1], ![0, -1, -2, 3], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def pivotMatrix2249 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, -2, 1], ![1, 0, 3, -4]]

def pivotMatrix2250 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 1, 0, 1], ![0, -1, -1, 2], ![1, -1, -1, 1], ![1, 0, 3, -4]]

def pivotMatrix2251 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 1, 0, 1], ![0, -1, -1, 2], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def pivotMatrix2252 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def pivotMatrix2253 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, 0, -2, 1]]

def pivotMatrix2254 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 1, 0, 1], ![0, 0, -1, 1], ![1, -1, 3, -3], ![1, 1, -2, 0]]

def pivotMatrix2255 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 1, 0, 1], ![0, 0, 1, -1], ![1, -1, 2, -2], ![1, 1, -3, 1]]

def pivotMatrix2256 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 1, 0, 1], ![0, 0, -1, 1], ![1, -1, -2, 2], ![1, 1, 2, -4]]

def pivotMatrix2257 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 1, 0, 1], ![0, 0, 1, -1], ![1, -1, -3, 3], ![1, 1, 1, -3]]

def pivotMatrix2258 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 1, 0, 1], ![0, 0, 2, -2], ![1, -1, -3, 3], ![1, 1, 0, -2]]

def pivotMatrix2259 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 0, 1], ![0, -1, 2, -1], ![1, -1, -2, 2], ![1, 1, 1, -3]]

def pivotMatrix2260 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, 0, 1], ![0, -1, 2, -1], ![1, -1, -3, 3], ![1, 1, 0, -2]]

def pivotMatrix2261 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 0, -2, 2], ![1, 1, -1, -1]]

def pivotMatrix2262 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, -3, 2], ![1, 0, 0, -1]]

def pivotMatrix2263 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, -1, -1, 1]]

def pivotMatrix2264 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 1, 0, 1], ![0, -1, 3, -2], ![1, -1, -2, 2], ![1, 0, 0, -1]]

def pivotMatrix2265 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 1, 0, 1], ![0, -1, 3, -2], ![1, -1, -2, 2], ![1, 0, -1, 0]]

def pivotMatrix2266 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 1, 0, 1], ![0, -1, 3, -2], ![1, -1, -1, 1], ![1, 0, -2, 1]]

def pivotMatrix2267 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 1, 0, 1], ![0, -1, 3, -2], ![1, -1, 0, 0], ![1, 0, -3, 2]]

def pivotMatrix2268 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, 0, 1], ![0, 0, -3, 3], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def pivotMatrix2269 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 1, 0, 1], ![0, 0, -3, 3], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def pivotMatrix2270 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 1, 3, -4], ![2, -2, 0, 0]]

def pivotMatrix2271 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 0, 1], ![0, 0, -2, 2], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def pivotMatrix2272 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def pivotMatrix2273 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![2, -2, 1, -1]]

def pivotMatrix2274 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 1, 0, 1], ![0, 0, -2, 2], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def pivotMatrix2275 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 1, 0, 1], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def pivotMatrix2276 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def pivotMatrix2277 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![2, -2, 3, -3]]

def pivotMatrix2278 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![2, -2, -1, 1]]

def pivotMatrix2279 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![2, -2, 2, -2]]

def pivotMatrix2280 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 1, 2, -3], ![2, -2, -2, 2]]

def pivotMatrix2281 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, -2, 1, -1]]

def pivotMatrix2282 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, 1, 1, -2], ![2, -2, -2, 2]]

def pivotMatrix2283 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 0, 1], ![0, 1, -2, 1], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def pivotMatrix2284 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 0, 1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def pivotMatrix2285 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 0, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, -1, 3, -3]]

def pivotMatrix2286 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 0, 1], ![0, 1, 3, -4], ![1, -1, -2, 2], ![1, -1, 0, 0]]

def pivotMatrix2287 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 0, 1], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, -1, 1]]

def pivotMatrix2288 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, -2, -3, 3]]

def pivotMatrix2289 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, -2, 2]]

def pivotMatrix2290 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, -3, 3]]

def pivotMatrix2291 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, 0, 1], ![0, 1, -1, 0], ![1, -1, -2, 2], ![1, -1, 2, -2]]

def pivotMatrix2292 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 1, 0, 1], ![0, 0, 2, -2], ![1, -1, -2, 2], ![1, -1, 1, -1]]

def pivotMatrix2293 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 1, 0, 1], ![0, 0, 3, -3], ![1, -1, -2, 2], ![1, -1, 0, 0]]

def pivotMatrix2294 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]

def pivotMatrix2295 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

def pivotMatrix2296 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 1, 1], ![0, -3, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def pivotMatrix2297 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 1, 1], ![0, -3, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix2298 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 1, 1], ![0, -3, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix2299 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def pivotMatrix2300 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix2301 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix2302 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def pivotMatrix2303 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix2304 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def pivotMatrix2305 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def pivotMatrix2306 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix2307 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, 1, 0], ![0, -1, -3, 4], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def pivotMatrix2308 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, 1, 0], ![0, -1, -3, 4], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def pivotMatrix2309 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def pivotMatrix2310 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def pivotMatrix2311 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def pivotMatrix2312 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def pivotMatrix2313 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 1, 0], ![0, -1, -2, 3], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def pivotMatrix2314 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, -1, -1, 2], ![1, 1, 2, -4]]

def pivotMatrix2315 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 1, 1, 0], ![0, -1, -1, 2], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def pivotMatrix2316 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, 0, -2, 2], ![1, 1, 2, -4]]

def pivotMatrix2317 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 1, 0], ![0, -1, -1, 2], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def pivotMatrix2318 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 1, 1, 0], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def pivotMatrix2319 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 1, 1, 0], ![0, 0, 1, -1], ![1, -1, -3, 3], ![1, 1, 1, -3]]

def pivotMatrix2320 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 1, 1, 0], ![0, 0, 2, -2], ![1, -1, -3, 3], ![1, 1, 0, -2]]

def pivotMatrix2321 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, 2, -1], ![0, -1, -3, 4], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def pivotMatrix2322 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 1, 2, -1], ![0, -1, -3, 4], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def pivotMatrix2323 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 1, 2, -1], ![0, 0, 1, -1], ![1, -1, -3, 3], ![1, 1, 0, -2]]

def pivotMatrix2324 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 1, 3, -2], ![0, -1, -3, 4], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def pivotMatrix2325 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 1, 3, -2], ![0, -1, -2, 3], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def pivotMatrix2326 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 1, 3, -2], ![0, -1, -1, 2], ![0, 0, -2, 2], ![1, 1, 0, -2]]

def pivotMatrix2327 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 1, 3, -2], ![0, -1, -1, 2], ![1, -1, -2, 2], ![1, 0, 0, -1]]

def pivotMatrix2328 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 2, -3, 3], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def pivotMatrix2329 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 2, -3, 3], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def pivotMatrix2330 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 2, -3, 3], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def pivotMatrix2331 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, 2, -2, 2], ![0, -1, -1, 2], ![0, -1, 2, -1], ![1, 0, 1, -2]]

def pivotMatrix2332 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, 2, -2, 2], ![0, -1, -1, 2], ![0, -1, 3, -2], ![1, 0, 0, -1]]

def pivotMatrix2333 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 2, -2, 2], ![0, -1, -1, 2], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def pivotMatrix2334 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 2, -2, 2], ![0, -1, -1, 2], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def pivotMatrix2335 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 2, -2, 2], ![0, -1, -1, 2], ![0, 0, 2, -2], ![1, 0, 1, -2]]

def pivotMatrix2336 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 2, -2, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def pivotMatrix2337 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 2, -2, 2], ![0, 0, -1, 1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def pivotMatrix2338 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 2, -2, 2], ![0, 0, -1, 1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def pivotMatrix2339 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 2, -2, 2], ![0, -1, 2, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def pivotMatrix2340 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 2, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, -2, 1, -1]]

def pivotMatrix2341 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 2, -2, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![2, -2, 0, 0]]

def pivotMatrix2342 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 2, -2, 2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def pivotMatrix2343 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 2, -2, 2], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def pivotMatrix2344 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 2, -2, 2], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def pivotMatrix2345 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 2, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, -2, -1, 1]]

def pivotMatrix2346 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 2, -2, 2], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, -1, 1, -1]]

def pivotMatrix2347 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 2, -2, 2], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def pivotMatrix2348 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 2, -1, 1], ![0, -1, -1, 2], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def pivotMatrix2349 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 2, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 0, 3, -4]]

def pivotMatrix2350 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 2, -1, 1], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def pivotMatrix2351 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![2, -2, 1, -1]]

def pivotMatrix2352 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![2, -2, 0, 0]]

def pivotMatrix2353 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 2, -1, 1], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def pivotMatrix2354 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 2, -1, 1], ![0, 0, -2, 2], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def pivotMatrix2355 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, -1, 1, -1]]

def pivotMatrix2356 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, -1, 0, 0]]

def pivotMatrix2357 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 2, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def pivotMatrix2358 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 2, -1, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![2, -2, -1, 1]]

def pivotMatrix2359 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 2, -1, 1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, -1, 2, -2]]

def pivotMatrix2360 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 2, -1, 1], ![0, 0, 1, -1], ![1, -1, -2, 2], ![1, -1, 1, -1]]

def pivotMatrix2361 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 2, -1, 1], ![0, 0, 2, -2], ![1, -1, -2, 2], ![1, -1, 0, 0]]

def pivotMatrix2362 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 2, -1, 1], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, -1, -1, 1]]

def pivotMatrix2363 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, -1, 2, -1], ![1, 0, 1, -2]]

def pivotMatrix2364 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 2, 0, 0], ![0, -1, -3, 4], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def pivotMatrix2365 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 2, 0, 0], ![0, -1, -3, 4], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def pivotMatrix2366 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 2, 0, 0], ![0, -1, -3, 4], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def pivotMatrix2367 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, 0, 2, -2], ![1, 0, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix2368 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, 0, 2, -2], ![1, -1, 1, -1]]

def pivotMatrix2369 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 2, 0, 0], ![0, -1, -1, 2], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def pivotMatrix2370 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 2, 0, 0], ![0, 0, -3, 3], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def pivotMatrix2371 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 2, 0, 0], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def pivotMatrix2372 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 2, 0, 0], ![0, 0, -2, 2], ![1, -1, -1, 1], ![1, -1, 2, -2]]

def pivotMatrix2373 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 2, 0, 0], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, -1, 3, -3]]

def pivotMatrix2374 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 2, 0, 0], ![0, 0, 1, -1], ![1, -1, -2, 2], ![1, -1, 2, -2]]

def pivotMatrix2375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -4, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def pivotMatrix2376 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -4, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def pivotMatrix2377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def pivotMatrix2378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix2379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def pivotMatrix2380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix2381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix2382 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -3, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix2383 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -3, 4], ![-1, 3, -2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix2384 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def pivotMatrix2385 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, 0, -2]]

def pivotMatrix2386 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def pivotMatrix2387 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, -2, 5], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def pivotMatrix2388 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 2, 0, -3]]

def pivotMatrix2389 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 2, -2, -1]]

def pivotMatrix2390 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 1, 0, -2]]

def pivotMatrix2391 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def pivotMatrix2392 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def pivotMatrix2393 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def pivotMatrix2394 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def pivotMatrix2395 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def pivotMatrix2396 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def pivotMatrix2397 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def pivotMatrix2398 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def pivotMatrix2399 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, -1, 4], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def pivotMatrix2400 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, -1, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def pivotMatrix2401 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, -1, 4], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def pivotMatrix2402 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def pivotMatrix2403 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def pivotMatrix2404 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 0, 1, -1], ![1, 2, 0, -3]]

def pivotMatrix2405 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def pivotMatrix2406 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def pivotMatrix2407 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 2, -1, -2]]

def pivotMatrix2408 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def pivotMatrix2409 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def pivotMatrix2410 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

def pivotMatrix2411 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def pivotMatrix2412 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def pivotMatrix2413 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def pivotMatrix2414 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 3, -4]]

def pivotMatrix2415 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 0, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def pivotMatrix2416 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 0, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def pivotMatrix2417 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 0, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def pivotMatrix2418 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 0, 3], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def pivotMatrix2419 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 1, -1, -1]]

def pivotMatrix2420 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def pivotMatrix2421 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def pivotMatrix2422 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def pivotMatrix2423 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def pivotMatrix2424 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def pivotMatrix2425 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, 0, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def pivotMatrix2426 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def pivotMatrix2427 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def pivotMatrix2428 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def pivotMatrix2429 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, -2, 1]]

def pivotMatrix2430 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -2, 0, 3], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def pivotMatrix2431 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix2432 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def pivotMatrix2433 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 1, 2, -4]]

def pivotMatrix2434 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 1, 1, -3]]

def pivotMatrix2435 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def pivotMatrix2436 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def pivotMatrix2437 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def pivotMatrix2438 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def pivotMatrix2439 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def pivotMatrix2440 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def pivotMatrix2441 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def pivotMatrix2442 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def pivotMatrix2443 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 1, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def pivotMatrix2444 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 1, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def pivotMatrix2445 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 1, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def pivotMatrix2446 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, 0, 0, -1]]

def pivotMatrix2447 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, 1, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def pivotMatrix2448 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, 1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def pivotMatrix2449 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, 1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def pivotMatrix2450 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, 1, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1]]

def pivotMatrix2451 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -2, 1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def pivotMatrix2452 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -2, 1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, -1, 0]]

def pivotMatrix2453 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -2, 2, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def pivotMatrix2454 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 2, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 1, 0, -2]]

def pivotMatrix2455 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 2, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def pivotMatrix2456 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -2, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def pivotMatrix2457 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -2, 3], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix2458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

def pivotMatrix2459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

def pivotMatrix2460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def pivotMatrix2461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix2462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def pivotMatrix2463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix2464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def pivotMatrix2465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def pivotMatrix2466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def pivotMatrix2467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix2468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix2469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix2470 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -2, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def pivotMatrix2471 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -2, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix2472 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -2, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix2473 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -2, 3], ![-1, 3, -2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix2474 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -2, 3], ![-1, 3, -2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix2475 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -2, 3], ![-1, 4, -3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix2476 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 2, -3]]

def pivotMatrix2477 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 3, -3], ![1, 0, -1]]

def pivotMatrix2478 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def pivotMatrix2479 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def pivotMatrix2480 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1]]

def pivotMatrix2481 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -2, 4], ![-1, -1, 2, 0], ![1, 0, 1, -2], ![1, 1, 0, -2]]

def pivotMatrix2482 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, -2, 4], ![-1, -1, 2, 0], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def pivotMatrix2483 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-1, -1, -2, 4], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def pivotMatrix2484 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, -1, -2, 4], ![-1, 0, 2, -1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def pivotMatrix2485 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, -2, 4], ![-1, 0, 3, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def pivotMatrix2486 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![-1, -1, -2, 4], ![0, 0, 1, -1], ![1, -1, 2, -2], ![1, 1, -1, -1]]

def pivotMatrix2487 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -2, 4], ![-1, 1, 1, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def pivotMatrix2488 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -2, 4], ![-1, 1, 1, -1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def pivotMatrix2489 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, -2, 4], ![-1, 1, 1, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def pivotMatrix2490 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def pivotMatrix2491 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def pivotMatrix2492 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def pivotMatrix2493 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

def pivotMatrix2494 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def pivotMatrix2495 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, -2, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix2496 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def pivotMatrix2497 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def pivotMatrix2498 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def pivotMatrix2499 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def pivotMatrix2500 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -2, 4], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def pivotMatrix2501 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 1, -1, -1]]

def pivotMatrix2502 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def pivotMatrix2503 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def pivotMatrix2504 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def pivotMatrix2505 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def pivotMatrix2506 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def pivotMatrix2507 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -2, 4], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 2, -2]]

def pivotMatrix2508 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 1, -1]]

def pivotMatrix2509 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, -1, 3], ![-1, -1, 1, 1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def pivotMatrix2510 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-1, -1, -1, 3], ![0, -1, 1, 0], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def pivotMatrix2511 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-1, -1, -1, 3], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def pivotMatrix2512 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-1, -1, -1, 3], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def pivotMatrix2513 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -1, 3], ![-1, 0, 2, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def pivotMatrix2514 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, -1, 3], ![-1, 0, 2, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def pivotMatrix2515 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def pivotMatrix2516 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def pivotMatrix2517 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -1, 3], ![-1, 0, 3, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def pivotMatrix2518 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, -1, 3], ![-1, 0, 3, -2], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def pivotMatrix2519 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, -1, 3], ![-1, 0, 3, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def pivotMatrix2520 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -1, 3], ![-1, 1, -1, 1], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def pivotMatrix2521 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -1, 3], ![-1, 1, -1, 1], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def pivotMatrix2522 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, -1, 3], ![-1, 1, -1, 1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def pivotMatrix2523 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-1, -1, -1, 3], ![-1, 1, -1, 1], ![0, 1, 1, -2], ![1, -1, 2, -2]]

def pivotMatrix2524 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, -1, -1, 3], ![-1, 1, -1, 1], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def pivotMatrix2525 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![-1, -1, -1, 3], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def pivotMatrix2526 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![-1, -1, -1, 3], ![0, 1, 0, -1], ![1, -1, 3, -3], ![1, 0, -2, 1]]

def pivotMatrix2527 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -1, 3], ![-1, 1, 1, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end


