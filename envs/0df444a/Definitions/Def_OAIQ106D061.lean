-- Prove2me | Definitions.Def_OAIQ106D061
-- name    : OAIQ106D061
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T12:28:18.300376+00:00
-- url     : https://prove2.me/theorems/5a823204-ec49-421f-bb19-f6950344b254
-- title:
--   Definitions bundle OAIQ106D061 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2315 declarations of OpenAI's Lean: 2315 definitions. The definitions and types are `OAI.MUB6.Certificate.PairSemantics.raw5144`, `OAI.MUB6.Certificate.PairSemantics.raw5144step0`, `OAI.MUB6.Certificate.PairSemantics.raw5145`, `OAI.MUB6.Certificate.PairSemantics.raw5145step0`, `OAI.MUB6.Certificate.PairSemantics.raw5146`, `OAI.MUB6.Certificate.PairSemantics.raw5146step0`, `OAI.MUB6.Certificate.PairSemantics.raw5146step1`, `OAI.MUB6.Certificate.PairSemantics.raw5146step2`, `OAI.MUB6.Certificate.PairSemantics.raw5147`, `OAI.MUB6.Certificate.PairSemantics.raw5147step0`, `OAI.MUB6.Certificate.PairSemantics.raw5147step1`, `OAI.MUB6.Certificate.PairSemantics.raw5148`, `OAI.MUB6.Certificate.PairSemantics.raw5148step0`, `OAI.MUB6.Certificate.PairSemantics.raw5148step1`, `OAI.MUB6.Certificate.PairSemantics.raw5148step2`, `OAI.MUB6.Certificate.PairSemantics.raw5149`, `OAI.MUB6.Certificate.PairSemantics.raw5149step0`, `OAI.MUB6.Certificate.PairSemantics.raw515`, `OAI.MUB6.Certificate.PairSemantics.raw5150`, `OAI.MUB6.Certificate.PairSemantics.raw5150step0`, `OAI.MUB6.Certificate.PairSemantics.raw5150step1`, `OAI.MUB6.Certificate.PairSemantics.raw5151`, `OAI.MUB6.Certificate.PairSemantics.raw5151step0`, `OAI.MUB6.Certificate.PairSemantics.raw5152`, `OAI.MUB6.Certificate.PairSemantics.raw5152step0`, `OAI.MUB6.Certificate.PairSemantics.raw5152step1`, `OAI.MUB6.Certificate.PairSemantics.raw5153`, `OAI.MUB6.Certificate.PairSemantics.raw5153step0`, `OAI.MUB6.Certificate.PairSemantics.raw5153step1`, `OAI.MUB6.Certificate.PairSemantics.raw5154`, `OAI.MUB6.Certificate.PairSemantics.raw5154step0`, `OAI.MUB6.Certificate.PairSemantics.raw5154step1`, `OAI.MUB6.Certificate.PairSemantics.raw5154step2`, `OAI.MUB6.Certificate.PairSemantics.raw5155`, `OAI.MUB6.Certificate.PairSemantics.raw5155step0`, `OAI.MUB6.Certificate.PairSemantics.raw5155step1`, `OAI.MUB6.Certificate.PairSemantics.raw5156`, `OAI.MUB6.Certificate.PairSemantics.raw5156step0`, `OAI.MUB6.Certificate.PairSemantics.raw5157`, `OAI.MUB6.Certificate.PairSemantics.raw5157step0` and 2275 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_PairSemantics_Canonical0`, `MutuallyUnbiased_PairSemantics_Canonical1`, `MutuallyUnbiased_PairSemantics_Canonical16`, `MutuallyUnbiased_PairSemantics_Canonical160`, `MutuallyUnbiased_PairSemantics_Canonical161`, `MutuallyUnbiased_PairSemantics_Canonical162`, `MutuallyUnbiased_PairSemantics_Canonical163`, `MutuallyUnbiased_PairSemantics_Canonical164`, `MutuallyUnbiased_PairSemantics_Canonical165`, `MutuallyUnbiased_PairSemantics_Canonical166`, `MutuallyUnbiased_PairSemantics_Canonical167`, `MutuallyUnbiased_PairSemantics_Canonical168`, `MutuallyUnbiased_PairSemantics_Canonical169`, `MutuallyUnbiased_PairSemantics_Canonical17`, `MutuallyUnbiased_PairSemantics_Canonical170`, `MutuallyUnbiased_PairSemantics_Canonical171`, `MutuallyUnbiased_PairSemantics_Canonical172`, `MutuallyUnbiased_PairSemantics_Canonical173`, `MutuallyUnbiased_PairSemantics_Canonical174`, `MutuallyUnbiased_PairSemantics_Canonical175`, `MutuallyUnbiased_PairSemantics_Canonical176`, `MutuallyUnbiased_PairSemantics_Canonical177`, `MutuallyUnbiased_PairSemantics_Canonical178`, `MutuallyUnbiased_PairSemantics_Canonical179`, `MutuallyUnbiased_PairSemantics_Canonical18`, `MutuallyUnbiased_PairSemantics_Canonical180`, `MutuallyUnbiased_PairSemantics_Canonical181`, `MutuallyUnbiased_PairSemantics_Canonical182`, `MutuallyUnbiased_PairSemantics_Canonical183`, `MutuallyUnbiased_PairSemantics_Canonical184`, `MutuallyUnbiased_PairSemantics_Canonical185`, `MutuallyUnbiased_PairSemantics_Canonical186`, `MutuallyUnbiased_PairSemantics_Canonical187`, `MutuallyUnbiased_PairSemantics_Canonical188`, `MutuallyUnbiased_PairSemantics_Canonical189`, `MutuallyUnbiased_PairSemantics_Canonical190`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the statement `OAI.MUB6.Certificate.PairSemantics.canonical5164`; the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1161`, `OAI.MUB6.Certificate.MixedSemantics.sound1162`, `OAI.MUB6.Certificate.MixedSemantics.sound1163`, `OAI.MUB6.Certificate.MixedSemantics.sound1164`, `OAI.MUB6.Certificate.MixedSemantics.sound1165`, `OAI.MUB6.Certificate.MixedSemantics.sound1166`, `OAI.MUB6.Certificate.MixedSemantics.sound1168`, `OAI.MUB6.Certificate.MixedSemantics.sound1170`, `OAI.MUB6.Certificate.MixedSemantics.sound1172`, `OAI.MUB6.Certificate.MixedSemantics.sound1173`, `OAI.MUB6.Certificate.MixedSemantics.sound1175`, `OAI.MUB6.Certificate.MixedSemantics.sound1265`, `OAI.MUB6.Certificate.MixedSemantics.sound1266`, `OAI.MUB6.Certificate.MixedSemantics.sound1267`, `OAI.MUB6.Certificate.MixedSemantics.sound1271`, `OAI.MUB6.Certificate.MixedSemantics.sound1298`, `OAI.MUB6.Certificate.MixedSemantics.sound1299`, `OAI.MUB6.Certificate.MixedSemantics.sound1301`, `OAI.MUB6.Certificate.MixedSemantics.sound1339`, `OAI.MUB6.Certificate.MixedSemantics.sound1340`, `OAI.MUB6.Certificate.MixedSemantics.sound1341`, `OAI.MUB6.Certificate.MixedSemantics.sound1342`, `OAI.MUB6.Certificate.MixedSemantics.sound1343`, `OAI.MUB6.Certificate.MixedSemantics.sound1344`, `OAI.MUB6.Certificate.MixedSemantics.sound1346`, `OAI.MUB6.Certificate.MixedSemantics.sound1395`, `OAI.MUB6.Certificate.MixedSemantics.sound1396`, `OAI.MUB6.Certificate.MixedSemantics.sound1397`, `OAI.MUB6.Certificate.MixedSemantics.sound1399`, `OAI.MUB6.Certificate.MixedSemantics.sound1401`, `OAI.MUB6.Certificate.MixedSemantics.sound1409`, `OAI.MUB6.Certificate.MixedSemantics.sound1410`, `OAI.MUB6.Certificate.MixedSemantics.sound1411`, `OAI.MUB6.Certificate.MixedSemantics.sound1412`, `OAI.MUB6.Certificate.MixedSemantics.sound1413`, `OAI.MUB6.Certificate.MixedSemantics.sound1414`, `OAI.MUB6.Certificate.MixedSemantics.sound1416`, `OAI.MUB6.Certificate.MixedSemantics.sound1417`, `OAI.MUB6.Certificate.MixedSemantics.sound1427`, `OAI.MUB6.Certificate.MixedSemantics.sound1441`, `OAI.MUB6.Certificate.MixedSemantics.sound1443`, `OAI.MUB6.Certificate.MixedSemantics.sound1451`, `OAI.MUB6.Certificate.MixedSemantics.sound1475`, `OAI.MUB6.Certificate.MixedSemantics.sound1477`, `OAI.MUB6.Certificate.MixedSemantics.sound1478`, `OAI.MUB6.Certificate.MixedSemantics.sound1479`, `OAI.MUB6.Certificate.MixedSemantics.sound1480`, `OAI.MUB6.Certificate.MixedSemantics.sound171`, `OAI.MUB6.Certificate.MixedSemantics.sound174`, `OAI.MUB6.Certificate.MixedSemantics.sound206`, `OAI.MUB6.Certificate.MixedSemantics.sound207`, `OAI.MUB6.Certificate.MixedSemantics.sound2357`, `OAI.MUB6.Certificate.MixedSemantics.sound2358`, `OAI.MUB6.Certificate.MixedSemantics.sound2359`, `OAI.MUB6.Certificate.MixedSemantics.sound2527`, `OAI.MUB6.Certificate.MixedSemantics.sound2530`, `OAI.MUB6.Certificate.MixedSemantics.sound2531`, `OAI.MUB6.Certificate.MixedSemantics.sound2532`, `OAI.MUB6.Certificate.MixedSemantics.sound2570`, `OAI.MUB6.Certificate.MixedSemantics.sound2572`, `OAI.MUB6.Certificate.MixedSemantics.sound2574`, `OAI.MUB6.Certificate.MixedSemantics.sound2576`, `OAI.MUB6.Certificate.MixedSemantics.sound2593`, `OAI.MUB6.Certificate.MixedSemantics.sound2594`, `OAI.MUB6.Certificate.MixedSemantics.sound2595`, `OAI.MUB6.Certificate.MixedSemantics.sound2596`, `OAI.MUB6.Certificate.MixedSemantics.sound2598`, `OAI.MUB6.Certificate.MixedSemantics.sound2599`, `OAI.MUB6.Certificate.MixedSemantics.sound2601`, `OAI.MUB6.Certificate.MixedSemantics.sound2636`, `OAI.MUB6.Certificate.MixedSemantics.sound2637`, `OAI.MUB6.Certificate.MixedSemantics.sound2638`, `OAI.MUB6.Certificate.MixedSemantics.sound2640`, `OAI.MUB6.Certificate.MixedSemantics.sound2753`, `OAI.MUB6.Certificate.MixedSemantics.sound2766`, `OAI.MUB6.Certificate.MixedSemantics.sound2828`, `OAI.MUB6.Certificate.MixedSemantics.sound2904`, `OAI.MUB6.Certificate.MixedSemantics.sound293`, `OAI.MUB6.Certificate.MixedSemantics.sound2936`, `OAI.MUB6.Certificate.MixedSemantics.sound2937`, `OAI.MUB6.Certificate.MixedSemantics.sound2939`, `OAI.MUB6.Certificate.MixedSemantics.sound294`, `OAI.MUB6.Certificate.MixedSemantics.sound2941`, `OAI.MUB6.Certificate.MixedSemantics.sound2943`, `OAI.MUB6.Certificate.MixedSemantics.sound2957`, `OAI.MUB6.Certificate.MixedSemantics.sound2958`, `OAI.MUB6.Certificate.MixedSemantics.sound2959`, `OAI.MUB6.Certificate.MixedSemantics.sound2960`, `OAI.MUB6.Certificate.MixedSemantics.sound2961`, `OAI.MUB6.Certificate.MixedSemantics.sound2963`, `OAI.MUB6.Certificate.MixedSemantics.sound2965`, `OAI.MUB6.Certificate.MixedSemantics.sound2966`, `OAI.MUB6.Certificate.MixedSemantics.sound2968`, `OAI.MUB6.Certificate.MixedSemantics.sound2969`, `OAI.MUB6.Certificate.MixedSemantics.sound2986`, `OAI.MUB6.Certificate.MixedSemantics.sound2987`, `OAI.MUB6.Certificate.MixedSemantics.sound2988`, `OAI.MUB6.Certificate.MixedSemantics.sound2990`, `OAI.MUB6.Certificate.MixedSemantics.sound2996`, `OAI.MUB6.Certificate.MixedSemantics.sound2997`, `OAI.MUB6.Certificate.MixedSemantics.sound2998`, `OAI.MUB6.Certificate.MixedSemantics.sound3003`, `OAI.MUB6.Certificate.MixedSemantics.sound3005`, `OAI.MUB6.Certificate.MixedSemantics.sound3082`, `OAI.MUB6.Certificate.MixedSemantics.sound3087`, `OAI.MUB6.Certificate.MixedSemantics.sound3088`, `OAI.MUB6.Certificate.MixedSemantics.sound3089`, `OAI.MUB6.Certificate.MixedSemantics.sound3090`, `OAI.MUB6.Certificate.MixedSemantics.sound3093`, `OAI.MUB6.Certificate.MixedSemantics.sound3094`, `OAI.MUB6.Certificate.MixedSemantics.sound3099`, `OAI.MUB6.Certificate.MixedSemantics.sound3100`, `OAI.MUB6.Certificate.MixedSemantics.sound3101`, `OAI.MUB6.Certificate.MixedSemantics.sound3102`, `OAI.MUB6.Certificate.MixedSemantics.sound3106`, `OAI.MUB6.Certificate.MixedSemantics.sound3109`, `OAI.MUB6.Certificate.MixedSemantics.sound3110`, `OAI.MUB6.Certificate.MixedSemantics.sound3116`, `OAI.MUB6.Certificate.MixedSemantics.sound3120`, `OAI.MUB6.Certificate.MixedSemantics.sound3143`, `OAI.MUB6.Certificate.MixedSemantics.sound3144`, `OAI.MUB6.Certificate.MixedSemantics.sound3178`, `OAI.MUB6.Certificate.MixedSemantics.sound3184`, `OAI.MUB6.Certificate.MixedSemantics.sound3185`, `OAI.MUB6.Certificate.MixedSemantics.sound3190`, `OAI.MUB6.Certificate.MixedSemantics.sound3191`, `OAI.MUB6.Certificate.MixedSemantics.sound3203`, `OAI.MUB6.Certificate.MixedSemantics.sound3204`, `OAI.MUB6.Certificate.MixedSemantics.sound3205`, `OAI.MUB6.Certificate.MixedSemantics.sound3206`, `OAI.MUB6.Certificate.MixedSemantics.sound3207`, `OAI.MUB6.Certificate.MixedSemantics.sound3209`, `OAI.MUB6.Certificate.MixedSemantics.sound3210`, `OAI.MUB6.Certificate.MixedSemantics.sound3211`, `OAI.MUB6.Certificate.MixedSemantics.sound3223`, `OAI.MUB6.Certificate.MixedSemantics.sound3226`, `OAI.MUB6.Certificate.MixedSemantics.sound3227`, `OAI.MUB6.Certificate.MixedSemantics.sound370`, `OAI.MUB6.Certificate.MixedSemantics.sound371`, `OAI.MUB6.Certificate.MixedSemantics.sound3711`, `OAI.MUB6.Certificate.MixedSemantics.sound3726`, `OAI.MUB6.Certificate.MixedSemantics.sound3727`, `OAI.MUB6.Certificate.MixedSemantics.sound3734`, `OAI.MUB6.Certificate.MixedSemantics.sound3735`, `OAI.MUB6.Certificate.MixedSemantics.sound3736`, `OAI.MUB6.Certificate.MixedSemantics.sound3737`, `OAI.MUB6.Certificate.MixedSemantics.sound3738`, `OAI.MUB6.Certificate.MixedSemantics.sound3739`, `OAI.MUB6.Certificate.MixedSemantics.sound3818`, `OAI.MUB6.Certificate.MixedSemantics.sound3821`, `OAI.MUB6.Certificate.MixedSemantics.sound3822`, `OAI.MUB6.Certificate.MixedSemantics.sound3823`, `OAI.MUB6.Certificate.MixedSemantics.sound3824`, `OAI.MUB6.Certificate.MixedSemantics.sound3829`, `OAI.MUB6.Certificate.MixedSemantics.sound3831`, `OAI.MUB6.Certificate.MixedSemantics.sound3847`, `OAI.MUB6.Certificate.MixedSemantics.sound3851`, `OAI.MUB6.Certificate.MixedSemantics.sound3852`, `OAI.MUB6.Certificate.MixedSemantics.sound3853`, `OAI.MUB6.Certificate.MixedSemantics.sound3855`, `OAI.MUB6.Certificate.MixedSemantics.sound3856`, `OAI.MUB6.Certificate.MixedSemantics.sound3858`, `OAI.MUB6.Certificate.MixedSemantics.sound3882`, `OAI.MUB6.Certificate.MixedSemantics.sound3883`, `OAI.MUB6.Certificate.MixedSemantics.sound3887`, `OAI.MUB6.Certificate.MixedSemantics.sound3888`, `OAI.MUB6.Certificate.MixedSemantics.sound3925`, `OAI.MUB6.Certificate.MixedSemantics.sound3931`, `OAI.MUB6.Certificate.MixedSemantics.sound3933`, `OAI.MUB6.Certificate.MixedSemantics.sound3936`, `OAI.MUB6.Certificate.MixedSemantics.sound3937`, `OAI.MUB6.Certificate.MixedSemantics.sound3965`, `OAI.MUB6.Certificate.MixedSemantics.sound3966`, `OAI.MUB6.Certificate.MixedSemantics.sound3967`, `OAI.MUB6.Certificate.MixedSemantics.sound3977`, `OAI.MUB6.Certificate.MixedSemantics.sound3980`, `OAI.MUB6.Certificate.MixedSemantics.sound3982`, `OAI.MUB6.Certificate.MixedSemantics.sound3987`, `OAI.MUB6.Certificate.MixedSemantics.sound3992`, `OAI.MUB6.Certificate.MixedSemantics.sound3993`, `OAI.MUB6.Certificate.MixedSemantics.sound3994`, `OAI.MUB6.Certificate.MixedSemantics.sound4002`, `OAI.MUB6.Certificate.MixedSemantics.sound4003`, `OAI.MUB6.Certificate.MixedSemantics.sound4012`, `OAI.MUB6.Certificate.MixedSemantics.sound4013`, `OAI.MUB6.Certificate.MixedSemantics.sound4014`, `OAI.MUB6.Certificate.MixedSemantics.sound4023`, `OAI.MUB6.Certificate.MixedSemantics.sound4026`, `OAI.MUB6.Certificate.MixedSemantics.sound4027`, `OAI.MUB6.Certificate.MixedSemantics.sound4029`, `OAI.MUB6.Certificate.MixedSemantics.sound4031`, `OAI.MUB6.Certificate.MixedSemantics.sound4032`, `OAI.MUB6.Certificate.MixedSemantics.sound4033`, `OAI.MUB6.Certificate.MixedSemantics.sound4039`, `OAI.MUB6.Certificate.MixedSemantics.sound4050`, `OAI.MUB6.Certificate.MixedSemantics.sound436`, `OAI.MUB6.Certificate.MixedSemantics.sound454`, `OAI.MUB6.Certificate.MixedSemantics.sound455`, `OAI.MUB6.Certificate.MixedSemantics.sound4623`, `OAI.MUB6.Certificate.MixedSemantics.sound4625`, `OAI.MUB6.Certificate.MixedSemantics.sound479`, `OAI.MUB6.Certificate.MixedSemantics.sound511`, `OAI.MUB6.Certificate.MixedSemantics.sound5176`, `OAI.MUB6.Certificate.MixedSemantics.sound5177`, `OAI.MUB6.Certificate.MixedSemantics.sound521`, `OAI.MUB6.Certificate.MixedSemantics.sound5293`, `OAI.MUB6.Certificate.MixedSemantics.sound5294`, `OAI.MUB6.Certificate.MixedSemantics.sound5296`, `OAI.MUB6.Certificate.MixedSemantics.sound5306`, `OAI.MUB6.Certificate.MixedSemantics.sound5310`, `OAI.MUB6.Certificate.MixedSemantics.sound5415`, `OAI.MUB6.Certificate.MixedSemantics.sound5443`, `OAI.MUB6.Certificate.MixedSemantics.sound5452`, `OAI.MUB6.Certificate.MixedSemantics.sound5453`, `OAI.MUB6.Certificate.MixedSemantics.sound5464`, `OAI.MUB6.Certificate.MixedSemantics.sound5492`, `OAI.MUB6.Certificate.MixedSemantics.sound644`, `OAI.MUB6.Certificate.MixedSemantics.sound645`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound135`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound136`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound137`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound138`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound139`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound140`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound141`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound142`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound143`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound145`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound146`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound147`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound148`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound149`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound150`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound151`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1098`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1423`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero15`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1780`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero539`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero733`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero863`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero925`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound10`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound100`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1008`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound101`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1010`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1013`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1021`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1033`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1093`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1094`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1095`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1096`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound11`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound110`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1103`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1108`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1109`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound111`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1110`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1111`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1115`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1121`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1124`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1131`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound114`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1159`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound116`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1167`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound117`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1170`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1178`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1179`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound126`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1262`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1263`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1264`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1267`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1268`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1269`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound127`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1272`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1279`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1294`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound13`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound130`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1301`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1303`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1310`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1311`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1312`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1318`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1324`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound138`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound140`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1409`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound141`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1410`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1414`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1417`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1418`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1420`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1421`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1429`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound143`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1435`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1437`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1442`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1470`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1472`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1480`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1484`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1493`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1517`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound152`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1521`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound153`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1560`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1568`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound16`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1649`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1651`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1653`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1656`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1662`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1669`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1674`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1703`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1709`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1717`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1781`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1782`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1783`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1785`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1786`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1787`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1789`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1796`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1816`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1840`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1844`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1845`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1846`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1847`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1849`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1853`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1854`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1856`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1859`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1866`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1874`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound188`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound19`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1905`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1911`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1915`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1917`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1964`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1972`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound198`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound199`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2034`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2035`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2037`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2038`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2040`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2046`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2049`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2050`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2059`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2062`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound207`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2075`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2166`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2168`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2169`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2170`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2171`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2172`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2174`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2175`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2176`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2178`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2179`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2181`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2182`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2183`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2184`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2185`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2187`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2188`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2189`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2190`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2191`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2192`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2197`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2199`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2200`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2201`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2203`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2204`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2205`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2206`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2207`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2208`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2211`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2212`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2214`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2216`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2217`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2218`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2219`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2221`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2222`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2223`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2224`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2225`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2226`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2227`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2228`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2229`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2230`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2231`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2232`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2233`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2235`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2238`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2240`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2242`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2244`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2245`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2246`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2247`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2248`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2249`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2250`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2251`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2252`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2254`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2255`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2257`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2258`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2259`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2260`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2261`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2263`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2264`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2266`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2267`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2268`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2269`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2270`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2271`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2272`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2273`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2274`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2275`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2276`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2279`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2280`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2282`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2283`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2284`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2286`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2287`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2288`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2291`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2292`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2293`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2294`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2296`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2297`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2298`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2299`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound23`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2300`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2301`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2302`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2303`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2304`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2306`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2307`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2308`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2309`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2313`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2315`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2317`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2318`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2320`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2321`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2322`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2323`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2324`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2325`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2326`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2327`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2329`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2330`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2331`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2332`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2333`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2334`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2335`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2336`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2337`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2338`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2340`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2341`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2344`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2345`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2346`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2347`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2348`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2350`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2351`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2352`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2354`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2355`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2356`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2357`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound236`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2360`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2361`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2362`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2363`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2364`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2365`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2366`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2367`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2368`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2371`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2372`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2374`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2375`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2377`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2378`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2379`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2380`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2381`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2383`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2384`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2386`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2388`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2389`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2391`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2393`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2394`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2395`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2396`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2397`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2398`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2399`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound24`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2400`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2401`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2402`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2403`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2404`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2405`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2406`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2407`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2408`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2409`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2410`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2411`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2413`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2414`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2415`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2418`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2419`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2420`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2423`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2424`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound244`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound245`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound25`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound255`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound268`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound269`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound286`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound287`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound29`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound296`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound3`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound310`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound339`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound340`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound341`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound342`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound344`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound345`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound349`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound35`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound354`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound356`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound358`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound359`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound366`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound368`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound370`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound371`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound372`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound380`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound388`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound391`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound392`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound395`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound396`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound404`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound412`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound413`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound418`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound428`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound438`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound445`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound453`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound456`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound462`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound463`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound474`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound482`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound484`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound485`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound488`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound498`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound5`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound500`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound501`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound504`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound515`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound516`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound518`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound519`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound521`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound522`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound523`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound525`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound526`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound532`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound534`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound543`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound545`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound547`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound548`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound552`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound554`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound555`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound558`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound565`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound567`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound568`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound571`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound572`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound579`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound58`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound581`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound582`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound585`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound59`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound590`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound6`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound600`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound613`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound621`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound629`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound631`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound633`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound635`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound649`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound659`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound663`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound664`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound667`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound675`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound711`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound718`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound731`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound732`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound734`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound736`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound737`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound741`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound743`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound750`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound779`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound780`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound787`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound788`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound790`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound792`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound794`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound796`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound8`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound800`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound802`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound813`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound864`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound865`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound866`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound872`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound877`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound878`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound881`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound885`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound888`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound899`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound9`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound909`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound911`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound92`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound923`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound927`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound933`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound936`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound94`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound940`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound947`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound949`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound97`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound971`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound976`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound98`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound989`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound991`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval106`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1074`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval109`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval116`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval117`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1192`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval12`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval120`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1210`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval124`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1254`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval130`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval133`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval134`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval141`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval143`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval145`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval146`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval147`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval149`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval155`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1553`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval159`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval164`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval165`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval167`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval173`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval174`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval18`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval181`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval182`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval185`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval202`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval203`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval207`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval21`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval214`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval215`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval218`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval220`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval224`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval225`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval226`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval229`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval231`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval234`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval235`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval242`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval243`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval245`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval249`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval255`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval257`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval258`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval263`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval270`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval271`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval273`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval278`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval280`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval285`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval286`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval287`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval292`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval296`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval301`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval308`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval310`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval323`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval325`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval331`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval332`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval334`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval335`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval343`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval344`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval348`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval353`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval358`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval359`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval366`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval368`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval37`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval370`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval371`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval372`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval373`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval377`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval380`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval383`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval389`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval39`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval391`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval394`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval401`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval403`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval408`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval41`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval413`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval414`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval444`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval46`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval475`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval476`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval477`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval52`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval54`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval56`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval6`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval63`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval69`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval73`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval74`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval77`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval79`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval8`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval83`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval86`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval91`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval99`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval113`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval119`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval147`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval150`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval208`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval21`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval215`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval216`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval220`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval222`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval271`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval359`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval360`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval362`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval373`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval375`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval384`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval44`, `OAI.MUB6.Certificate.PairSemantics.boundarySound165`, `OAI.MUB6.Certificate.PairSemantics.boundarySound243`, `OAI.MUB6.Certificate.PairSemantics.boundarySound248`, `OAI.MUB6.Certificate.PairSemantics.boundarySound249`, `OAI.MUB6.Certificate.PairSemantics.boundarySound250`, `OAI.MUB6.Certificate.PairSemantics.boundarySound252`, `OAI.MUB6.Certificate.PairSemantics.boundarySound261`, `OAI.MUB6.Certificate.PairSemantics.boundarySound264`, `OAI.MUB6.Certificate.PairSemantics.boundarySound305`, `OAI.MUB6.Certificate.PairSemantics.boundarySound347`, `OAI.MUB6.Certificate.PairSemantics.boundarySound445`, `OAI.MUB6.Certificate.PairSemantics.boundarySound454`, `OAI.MUB6.Certificate.PairSemantics.boundarySound49`, `OAI.MUB6.Certificate.PairSemantics.boundarySound51`, `OAI.MUB6.Certificate.PairSemantics.boundarySound56`, `OAI.MUB6.Certificate.PairSemantics.boundarySound7`, `OAI.MUB6.Certificate.PairSemantics.boundarySound73`, `OAI.MUB6.Certificate.PairSemantics.boundarySound75`, `OAI.MUB6.Certificate.PairSemantics.boundarySound83`, `OAI.MUB6.Certificate.PairSemantics.boundarySound97`, `OAI.MUB6.Certificate.PairSemantics.canonical5164`, `OAI.MUB6.Certificate.PairSemantics.sound11`, `OAI.MUB6.Certificate.PairSemantics.sound1141`, `OAI.MUB6.Certificate.PairSemantics.sound1151`, `OAI.MUB6.Certificate.PairSemantics.sound1152`, `OAI.MUB6.Certificate.PairSemantics.sound117`, `OAI.MUB6.Certificate.PairSemantics.sound1381`, `OAI.MUB6.Certificate.PairSemantics.sound1383`, `OAI.MUB6.Certificate.PairSemantics.sound1384`, `OAI.MUB6.Certificate.PairSemantics.sound1387`, `OAI.MUB6.Certificate.PairSemantics.sound1390`, `OAI.MUB6.Certificate.PairSemantics.sound1391`, `OAI.MUB6.Certificate.PairSemantics.sound1392`, `OAI.MUB6.Certificate.PairSemantics.sound1395`, `OAI.MUB6.Certificate.PairSemantics.sound1399`, `OAI.MUB6.Certificate.PairSemantics.sound1414`, `OAI.MUB6.Certificate.PairSemantics.sound1419`, `OAI.MUB6.Certificate.PairSemantics.sound1423`, `OAI.MUB6.Certificate.PairSemantics.sound1424`, `OAI.MUB6.Certificate.PairSemantics.sound1425`, `OAI.MUB6.Certificate.PairSemantics.sound1432`, `OAI.MUB6.Certificate.PairSemantics.sound1434`, `OAI.MUB6.Certificate.PairSemantics.sound1437`, `OAI.MUB6.Certificate.PairSemantics.sound1443`, `OAI.MUB6.Certificate.PairSemantics.sound1458`, `OAI.MUB6.Certificate.PairSemantics.sound1486`, `OAI.MUB6.Certificate.PairSemantics.sound1500`, `OAI.MUB6.Certificate.PairSemantics.sound1504`, `OAI.MUB6.Certificate.PairSemantics.sound1506`, `OAI.MUB6.Certificate.PairSemantics.sound1512`, `OAI.MUB6.Certificate.PairSemantics.sound1518`, `OAI.MUB6.Certificate.PairSemantics.sound1520`, `OAI.MUB6.Certificate.PairSemantics.sound1523`, `OAI.MUB6.Certificate.PairSemantics.sound1530`, `OAI.MUB6.Certificate.PairSemantics.sound1531`, `OAI.MUB6.Certificate.PairSemantics.sound1533`, `OAI.MUB6.Certificate.PairSemantics.sound1535`, `OAI.MUB6.Certificate.PairSemantics.sound1540`, `OAI.MUB6.Certificate.PairSemantics.sound1548`, `OAI.MUB6.Certificate.PairSemantics.sound1552`, `OAI.MUB6.Certificate.PairSemantics.sound1563`, `OAI.MUB6.Certificate.PairSemantics.sound1585`, `OAI.MUB6.Certificate.PairSemantics.sound1605`, `OAI.MUB6.Certificate.PairSemantics.sound1614`, `OAI.MUB6.Certificate.PairSemantics.sound1617`, `OAI.MUB6.Certificate.PairSemantics.sound1624`, `OAI.MUB6.Certificate.PairSemantics.sound1625`, `OAI.MUB6.Certificate.PairSemantics.sound1627`, `OAI.MUB6.Certificate.PairSemantics.sound1628`, `OAI.MUB6.Certificate.PairSemantics.sound1631`, `OAI.MUB6.Certificate.PairSemantics.sound1634`, `OAI.MUB6.Certificate.PairSemantics.sound1635`, `OAI.MUB6.Certificate.PairSemantics.sound1637`, `OAI.MUB6.Certificate.PairSemantics.sound1638`, `OAI.MUB6.Certificate.PairSemantics.sound1643`, `OAI.MUB6.Certificate.PairSemantics.sound1646`, `OAI.MUB6.Certificate.PairSemantics.sound1648`, `OAI.MUB6.Certificate.PairSemantics.sound1652`, `OAI.MUB6.Certificate.PairSemantics.sound1668`, `OAI.MUB6.Certificate.PairSemantics.sound1669`, `OAI.MUB6.Certificate.PairSemantics.sound1682`, `OAI.MUB6.Certificate.PairSemantics.sound1685`, `OAI.MUB6.Certificate.PairSemantics.sound1686`, `OAI.MUB6.Certificate.PairSemantics.sound1707`, `OAI.MUB6.Certificate.PairSemantics.sound1716`, `OAI.MUB6.Certificate.PairSemantics.sound1718`, `OAI.MUB6.Certificate.PairSemantics.sound1736`, `OAI.MUB6.Certificate.PairSemantics.sound1739`, `OAI.MUB6.Certificate.PairSemantics.sound1768`, `OAI.MUB6.Certificate.PairSemantics.sound1769`, `OAI.MUB6.Certificate.PairSemantics.sound1770`, `OAI.MUB6.Certificate.PairSemantics.sound1774`, `OAI.MUB6.Certificate.PairSemantics.sound1784`, `OAI.MUB6.Certificate.PairSemantics.sound1793`, `OAI.MUB6.Certificate.PairSemantics.sound1800`, `OAI.MUB6.Certificate.PairSemantics.sound1803`, `OAI.MUB6.Certificate.PairSemantics.sound1826`, `OAI.MUB6.Certificate.PairSemantics.sound1828`, `OAI.MUB6.Certificate.PairSemantics.sound1830`, `OAI.MUB6.Certificate.PairSemantics.sound1849`, `OAI.MUB6.Certificate.PairSemantics.sound1858`, `OAI.MUB6.Certificate.PairSemantics.sound1860`, `OAI.MUB6.Certificate.PairSemantics.sound1865`, `OAI.MUB6.Certificate.PairSemantics.sound1866`, `OAI.MUB6.Certificate.PairSemantics.sound1867`, `OAI.MUB6.Certificate.PairSemantics.sound1869`, `OAI.MUB6.Certificate.PairSemantics.sound1870`, `OAI.MUB6.Certificate.PairSemantics.sound1872`, `OAI.MUB6.Certificate.PairSemantics.sound1873`, `OAI.MUB6.Certificate.PairSemantics.sound1879`, `OAI.MUB6.Certificate.PairSemantics.sound1885`, `OAI.MUB6.Certificate.PairSemantics.sound1890`, `OAI.MUB6.Certificate.PairSemantics.sound1938`, `OAI.MUB6.Certificate.PairSemantics.sound1968`, `OAI.MUB6.Certificate.PairSemantics.sound1977`, `OAI.MUB6.Certificate.PairSemantics.sound1978`, `OAI.MUB6.Certificate.PairSemantics.sound1980`, `OAI.MUB6.Certificate.PairSemantics.sound1986`, `OAI.MUB6.Certificate.PairSemantics.sound1987`, `OAI.MUB6.Certificate.PairSemantics.sound2041`, `OAI.MUB6.Certificate.PairSemantics.sound2058`, `OAI.MUB6.Certificate.PairSemantics.sound2106`, `OAI.MUB6.Certificate.PairSemantics.sound2108`, `OAI.MUB6.Certificate.PairSemantics.sound2113`, `OAI.MUB6.Certificate.PairSemantics.sound2117`, `OAI.MUB6.Certificate.PairSemantics.sound2122`, `OAI.MUB6.Certificate.PairSemantics.sound2123`, `OAI.MUB6.Certificate.PairSemantics.sound2128`, `OAI.MUB6.Certificate.PairSemantics.sound2132`, `OAI.MUB6.Certificate.PairSemantics.sound2152`, `OAI.MUB6.Certificate.PairSemantics.sound2168`, `OAI.MUB6.Certificate.PairSemantics.sound2175`, `OAI.MUB6.Certificate.PairSemantics.sound2177`, `OAI.MUB6.Certificate.PairSemantics.sound2183`, `OAI.MUB6.Certificate.PairSemantics.sound2190`, `OAI.MUB6.Certificate.PairSemantics.sound2192`, `OAI.MUB6.Certificate.PairSemantics.sound2197`, `OAI.MUB6.Certificate.PairSemantics.sound2201`, `OAI.MUB6.Certificate.PairSemantics.sound2202`, `OAI.MUB6.Certificate.PairSemantics.sound2204`, `OAI.MUB6.Certificate.PairSemantics.sound2213`, `OAI.MUB6.Certificate.PairSemantics.sound2216`, `OAI.MUB6.Certificate.PairSemantics.sound2228`, `OAI.MUB6.Certificate.PairSemantics.sound2243`, `OAI.MUB6.Certificate.PairSemantics.sound2244`, `OAI.MUB6.Certificate.PairSemantics.sound2262`, `OAI.MUB6.Certificate.PairSemantics.sound2284`, `OAI.MUB6.Certificate.PairSemantics.sound2285`, `OAI.MUB6.Certificate.PairSemantics.sound2286`, `OAI.MUB6.Certificate.PairSemantics.sound2293`, `OAI.MUB6.Certificate.PairSemantics.sound2294`, `OAI.MUB6.Certificate.PairSemantics.sound2295`, `OAI.MUB6.Certificate.PairSemantics.sound2296`, `OAI.MUB6.Certificate.PairSemantics.sound2298`, `OAI.MUB6.Certificate.PairSemantics.sound2304`, `OAI.MUB6.Certificate.PairSemantics.sound2307`, `OAI.MUB6.Certificate.PairSemantics.sound2312`, `OAI.MUB6.Certificate.PairSemantics.sound2315`, `OAI.MUB6.Certificate.PairSemantics.sound232`, `OAI.MUB6.Certificate.PairSemantics.sound2324`, `OAI.MUB6.Certificate.PairSemantics.sound2325`, `OAI.MUB6.Certificate.PairSemantics.sound2327`, `OAI.MUB6.Certificate.PairSemantics.sound2338`, `OAI.MUB6.Certificate.PairSemantics.sound2349`, `OAI.MUB6.Certificate.PairSemantics.sound2357`, `OAI.MUB6.Certificate.PairSemantics.sound2375`, `OAI.MUB6.Certificate.PairSemantics.sound2382`, `OAI.MUB6.Certificate.PairSemantics.sound2389`, `OAI.MUB6.Certificate.PairSemantics.sound2390`, `OAI.MUB6.Certificate.PairSemantics.sound2391`, `OAI.MUB6.Certificate.PairSemantics.sound2399`, `OAI.MUB6.Certificate.PairSemantics.sound2400`, `OAI.MUB6.Certificate.PairSemantics.sound2403`, `OAI.MUB6.Certificate.PairSemantics.sound2411`, `OAI.MUB6.Certificate.PairSemantics.sound2413`, `OAI.MUB6.Certificate.PairSemantics.sound2414`, `OAI.MUB6.Certificate.PairSemantics.sound2415`, `OAI.MUB6.Certificate.PairSemantics.sound2416`, `OAI.MUB6.Certificate.PairSemantics.sound2417`, `OAI.MUB6.Certificate.PairSemantics.sound2420`, `OAI.MUB6.Certificate.PairSemantics.sound2428`, `OAI.MUB6.Certificate.PairSemantics.sound2433`, `OAI.MUB6.Certificate.PairSemantics.sound2434`, `OAI.MUB6.Certificate.PairSemantics.sound2435`, `OAI.MUB6.Certificate.PairSemantics.sound2436`, `OAI.MUB6.Certificate.PairSemantics.sound2440`, `OAI.MUB6.Certificate.PairSemantics.sound2441`, `OAI.MUB6.Certificate.PairSemantics.sound2442`, `OAI.MUB6.Certificate.PairSemantics.sound2443`, `OAI.MUB6.Certificate.PairSemantics.sound2444`, `OAI.MUB6.Certificate.PairSemantics.sound2445`, `OAI.MUB6.Certificate.PairSemantics.sound2455`, `OAI.MUB6.Certificate.PairSemantics.sound2456`, `OAI.MUB6.Certificate.PairSemantics.sound2457`, `OAI.MUB6.Certificate.PairSemantics.sound2462`, `OAI.MUB6.Certificate.PairSemantics.sound2463`, `OAI.MUB6.Certificate.PairSemantics.sound2464`, `OAI.MUB6.Certificate.PairSemantics.sound2465`, `OAI.MUB6.Certificate.PairSemantics.sound2466`, `OAI.MUB6.Certificate.PairSemantics.sound2470`, `OAI.MUB6.Certificate.PairSemantics.sound2472`, `OAI.MUB6.Certificate.PairSemantics.sound2473`, `OAI.MUB6.Certificate.PairSemantics.sound2477`, `OAI.MUB6.Certificate.PairSemantics.sound2479`, `OAI.MUB6.Certificate.PairSemantics.sound2486`, `OAI.MUB6.Certificate.PairSemantics.sound2489`, `OAI.MUB6.Certificate.PairSemantics.sound2490`, `OAI.MUB6.Certificate.PairSemantics.sound2491`, `OAI.MUB6.Certificate.PairSemantics.sound2492`, `OAI.MUB6.Certificate.PairSemantics.sound2507`, `OAI.MUB6.Certificate.PairSemantics.sound2520`, `OAI.MUB6.Certificate.PairSemantics.sound2521`, `OAI.MUB6.Certificate.PairSemantics.sound2524`, `OAI.MUB6.Certificate.PairSemantics.sound2525`, `OAI.MUB6.Certificate.PairSemantics.sound2533`, `OAI.MUB6.Certificate.PairSemantics.sound2540`, `OAI.MUB6.Certificate.PairSemantics.sound2546`, `OAI.MUB6.Certificate.PairSemantics.sound2547`, `OAI.MUB6.Certificate.PairSemantics.sound2548`, `OAI.MUB6.Certificate.PairSemantics.sound2557`, `OAI.MUB6.Certificate.PairSemantics.sound2558`, `OAI.MUB6.Certificate.PairSemantics.sound2559`, `OAI.MUB6.Certificate.PairSemantics.sound2564`, `OAI.MUB6.Certificate.PairSemantics.sound2565`, `OAI.MUB6.Certificate.PairSemantics.sound2566`, `OAI.MUB6.Certificate.PairSemantics.sound2573`, `OAI.MUB6.Certificate.PairSemantics.sound2578`, `OAI.MUB6.Certificate.PairSemantics.sound2579`, `OAI.MUB6.Certificate.PairSemantics.sound2580`, `OAI.MUB6.Certificate.PairSemantics.sound2602`, `OAI.MUB6.Certificate.PairSemantics.sound2604`, `OAI.MUB6.Certificate.PairSemantics.sound2606`, `OAI.MUB6.Certificate.PairSemantics.sound2619`, `OAI.MUB6.Certificate.PairSemantics.sound2626`, `OAI.MUB6.Certificate.PairSemantics.sound2627`, `OAI.MUB6.Certificate.PairSemantics.sound2641`, `OAI.MUB6.Certificate.PairSemantics.sound2657`, `OAI.MUB6.Certificate.PairSemantics.sound2658`, `OAI.MUB6.Certificate.PairSemantics.sound2661`, `OAI.MUB6.Certificate.PairSemantics.sound2666`, `OAI.MUB6.Certificate.PairSemantics.sound2670`, `OAI.MUB6.Certificate.PairSemantics.sound2671`, `OAI.MUB6.Certificate.PairSemantics.sound2674`, `OAI.MUB6.Certificate.PairSemantics.sound2683`, `OAI.MUB6.Certificate.PairSemantics.sound2686`, `OAI.MUB6.Certificate.PairSemantics.sound2690`, `OAI.MUB6.Certificate.PairSemantics.sound2693`, `OAI.MUB6.Certificate.PairSemantics.sound2709`, `OAI.MUB6.Certificate.PairSemantics.sound2710`, `OAI.MUB6.Certificate.PairSemantics.sound2711`, `OAI.MUB6.Certificate.PairSemantics.sound2714`, `OAI.MUB6.Certificate.PairSemantics.sound2717`, `OAI.MUB6.Certificate.PairSemantics.sound2723`, `OAI.MUB6.Certificate.PairSemantics.sound2732`, `OAI.MUB6.Certificate.PairSemantics.sound2733`, `OAI.MUB6.Certificate.PairSemantics.sound2754`, `OAI.MUB6.Certificate.PairSemantics.sound2757`, `OAI.MUB6.Certificate.PairSemantics.sound2765`, `OAI.MUB6.Certificate.PairSemantics.sound2788`, `OAI.MUB6.Certificate.PairSemantics.sound2790`, `OAI.MUB6.Certificate.PairSemantics.sound2793`, `OAI.MUB6.Certificate.PairSemantics.sound2827`, `OAI.MUB6.Certificate.PairSemantics.sound2829`, `OAI.MUB6.Certificate.PairSemantics.sound2836`, `OAI.MUB6.Certificate.PairSemantics.sound2839`, `OAI.MUB6.Certificate.PairSemantics.sound284`, `OAI.MUB6.Certificate.PairSemantics.sound2845`, `OAI.MUB6.Certificate.PairSemantics.sound2850`, `OAI.MUB6.Certificate.PairSemantics.sound2852`, `OAI.MUB6.Certificate.PairSemantics.sound2854`, `OAI.MUB6.Certificate.PairSemantics.sound2855`, `OAI.MUB6.Certificate.PairSemantics.sound2863`, `OAI.MUB6.Certificate.PairSemantics.sound2864`, `OAI.MUB6.Certificate.PairSemantics.sound2865`, `OAI.MUB6.Certificate.PairSemantics.sound2866`, `OAI.MUB6.Certificate.PairSemantics.sound2867`, `OAI.MUB6.Certificate.PairSemantics.sound2868`, `OAI.MUB6.Certificate.PairSemantics.sound2872`, `OAI.MUB6.Certificate.PairSemantics.sound2873`, `OAI.MUB6.Certificate.PairSemantics.sound2874`, `OAI.MUB6.Certificate.PairSemantics.sound2875`, `OAI.MUB6.Certificate.PairSemantics.sound2878`, `OAI.MUB6.Certificate.PairSemantics.sound2879`, `OAI.MUB6.Certificate.PairSemantics.sound2880`, `OAI.MUB6.Certificate.PairSemantics.sound2881`, `OAI.MUB6.Certificate.PairSemantics.sound2882`, `OAI.MUB6.Certificate.PairSemantics.sound2883`, `OAI.MUB6.Certificate.PairSemantics.sound2884`, `OAI.MUB6.Certificate.PairSemantics.sound2886`, `OAI.MUB6.Certificate.PairSemantics.sound2887`, `OAI.MUB6.Certificate.PairSemantics.sound2888`, `OAI.MUB6.Certificate.PairSemantics.sound2889`, `OAI.MUB6.Certificate.PairSemantics.sound2890`, `OAI.MUB6.Certificate.PairSemantics.sound2891`, `OAI.MUB6.Certificate.PairSemantics.sound2892`, `OAI.MUB6.Certificate.PairSemantics.sound2894`, `OAI.MUB6.Certificate.PairSemantics.sound2895`, `OAI.MUB6.Certificate.PairSemantics.sound2896`, `OAI.MUB6.Certificate.PairSemantics.sound2897`, `OAI.MUB6.Certificate.PairSemantics.sound2898`, `OAI.MUB6.Certificate.PairSemantics.sound2899`, `OAI.MUB6.Certificate.PairSemantics.sound2900`, `OAI.MUB6.Certificate.PairSemantics.sound2901`, `OAI.MUB6.Certificate.PairSemantics.sound2902`, `OAI.MUB6.Certificate.PairSemantics.sound2903`, `OAI.MUB6.Certificate.PairSemantics.sound2906`, `OAI.MUB6.Certificate.PairSemantics.sound2909`, `OAI.MUB6.Certificate.PairSemantics.sound2910`, `OAI.MUB6.Certificate.PairSemantics.sound2912`, `OAI.MUB6.Certificate.PairSemantics.sound2913`, `OAI.MUB6.Certificate.PairSemantics.sound2914`, `OAI.MUB6.Certificate.PairSemantics.sound2915`, `OAI.MUB6.Certificate.PairSemantics.sound2916`, `OAI.MUB6.Certificate.PairSemantics.sound2917`, `OAI.MUB6.Certificate.PairSemantics.sound2918`, `OAI.MUB6.Certificate.PairSemantics.sound2919`, `OAI.MUB6.Certificate.PairSemantics.sound2920`, `OAI.MUB6.Certificate.PairSemantics.sound2922`, `OAI.MUB6.Certificate.PairSemantics.sound2924`, `OAI.MUB6.Certificate.PairSemantics.sound2927`, `OAI.MUB6.Certificate.PairSemantics.sound2928`, `OAI.MUB6.Certificate.PairSemantics.sound2929`, `OAI.MUB6.Certificate.PairSemantics.sound2930`, `OAI.MUB6.Certificate.PairSemantics.sound2931`, `OAI.MUB6.Certificate.PairSemantics.sound2933`, `OAI.MUB6.Certificate.PairSemantics.sound2934`, `OAI.MUB6.Certificate.PairSemantics.sound2935`, `OAI.MUB6.Certificate.PairSemantics.sound2936`, `OAI.MUB6.Certificate.PairSemantics.sound2939`, `OAI.MUB6.Certificate.PairSemantics.sound2940`, `OAI.MUB6.Certificate.PairSemantics.sound2941`, `OAI.MUB6.Certificate.PairSemantics.sound2943`, `OAI.MUB6.Certificate.PairSemantics.sound2944`, `OAI.MUB6.Certificate.PairSemantics.sound2947`, `OAI.MUB6.Certificate.PairSemantics.sound2948`, `OAI.MUB6.Certificate.PairSemantics.sound2949`, `OAI.MUB6.Certificate.PairSemantics.sound2950`, `OAI.MUB6.Certificate.PairSemantics.sound2952`, `OAI.MUB6.Certificate.PairSemantics.sound2953`, `OAI.MUB6.Certificate.PairSemantics.sound2954`, `OAI.MUB6.Certificate.PairSemantics.sound2955`, `OAI.MUB6.Certificate.PairSemantics.sound2956`, `OAI.MUB6.Certificate.PairSemantics.sound2957`, `OAI.MUB6.Certificate.PairSemantics.sound2958`, `OAI.MUB6.Certificate.PairSemantics.sound2959`, `OAI.MUB6.Certificate.PairSemantics.sound2960`, `OAI.MUB6.Certificate.PairSemantics.sound2962`, `OAI.MUB6.Certificate.PairSemantics.sound2964`, `OAI.MUB6.Certificate.PairSemantics.sound2965`, `OAI.MUB6.Certificate.PairSemantics.sound2966`, `OAI.MUB6.Certificate.PairSemantics.sound2967`, `OAI.MUB6.Certificate.PairSemantics.sound2968`, `OAI.MUB6.Certificate.PairSemantics.sound2969`, `OAI.MUB6.Certificate.PairSemantics.sound2970`, `OAI.MUB6.Certificate.PairSemantics.sound2972`, `OAI.MUB6.Certificate.PairSemantics.sound2973`, `OAI.MUB6.Certificate.PairSemantics.sound2974`, `OAI.MUB6.Certificate.PairSemantics.sound2975`, `OAI.MUB6.Certificate.PairSemantics.sound2976`, `OAI.MUB6.Certificate.PairSemantics.sound2977`, `OAI.MUB6.Certificate.PairSemantics.sound2979`, `OAI.MUB6.Certificate.PairSemantics.sound2980`, `OAI.MUB6.Certificate.PairSemantics.sound2982`, `OAI.MUB6.Certificate.PairSemantics.sound2985`, `OAI.MUB6.Certificate.PairSemantics.sound2986`, `OAI.MUB6.Certificate.PairSemantics.sound2987`, `OAI.MUB6.Certificate.PairSemantics.sound2988`, `OAI.MUB6.Certificate.PairSemantics.sound2989`, `OAI.MUB6.Certificate.PairSemantics.sound2990`, `OAI.MUB6.Certificate.PairSemantics.sound2991`, `OAI.MUB6.Certificate.PairSemantics.sound2993`, `OAI.MUB6.Certificate.PairSemantics.sound2994`, `OAI.MUB6.Certificate.PairSemantics.sound2996`, `OAI.MUB6.Certificate.PairSemantics.sound2997`, `OAI.MUB6.Certificate.PairSemantics.sound2998`, `OAI.MUB6.Certificate.PairSemantics.sound2999`, `OAI.MUB6.Certificate.PairSemantics.sound3000`, `OAI.MUB6.Certificate.PairSemantics.sound3001`, `OAI.MUB6.Certificate.PairSemantics.sound3002`, `OAI.MUB6.Certificate.PairSemantics.sound3004`, `OAI.MUB6.Certificate.PairSemantics.sound3006`, `OAI.MUB6.Certificate.PairSemantics.sound3009`, `OAI.MUB6.Certificate.PairSemantics.sound3010`, `OAI.MUB6.Certificate.PairSemantics.sound3011`, `OAI.MUB6.Certificate.PairSemantics.sound3012`, `OAI.MUB6.Certificate.PairSemantics.sound3013`, `OAI.MUB6.Certificate.PairSemantics.sound3014`, `OAI.MUB6.Certificate.PairSemantics.sound3015`, `OAI.MUB6.Certificate.PairSemantics.sound3016`, `OAI.MUB6.Certificate.PairSemantics.sound3017`, `OAI.MUB6.Certificate.PairSemantics.sound3018`, `OAI.MUB6.Certificate.PairSemantics.sound3019`, `OAI.MUB6.Certificate.PairSemantics.sound3020`, `OAI.MUB6.Certificate.PairSemantics.sound3021`, `OAI.MUB6.Certificate.PairSemantics.sound3022`, `OAI.MUB6.Certificate.PairSemantics.sound3023`, `OAI.MUB6.Certificate.PairSemantics.sound3024`, `OAI.MUB6.Certificate.PairSemantics.sound3025`, `OAI.MUB6.Certificate.PairSemantics.sound3026`, `OAI.MUB6.Certificate.PairSemantics.sound3027`, `OAI.MUB6.Certificate.PairSemantics.sound3028`, `OAI.MUB6.Certificate.PairSemantics.sound3029`, `OAI.MUB6.Certificate.PairSemantics.sound3030`, `OAI.MUB6.Certificate.PairSemantics.sound3031`, `OAI.MUB6.Certificate.PairSemantics.sound3032`, `OAI.MUB6.Certificate.PairSemantics.sound3033`, `OAI.MUB6.Certificate.PairSemantics.sound3034`, `OAI.MUB6.Certificate.PairSemantics.sound3035`, `OAI.MUB6.Certificate.PairSemantics.sound3036`, `OAI.MUB6.Certificate.PairSemantics.sound3038`, `OAI.MUB6.Certificate.PairSemantics.sound3039`, `OAI.MUB6.Certificate.PairSemantics.sound3040`, `OAI.MUB6.Certificate.PairSemantics.sound3041`, `OAI.MUB6.Certificate.PairSemantics.sound3042`, `OAI.MUB6.Certificate.PairSemantics.sound3043`, `OAI.MUB6.Certificate.PairSemantics.sound3044`, `OAI.MUB6.Certificate.PairSemantics.sound3045`, `OAI.MUB6.Certificate.PairSemantics.sound3047`, `OAI.MUB6.Certificate.PairSemantics.sound3048`, `OAI.MUB6.Certificate.PairSemantics.sound3049`, `OAI.MUB6.Certificate.PairSemantics.sound3050`, `OAI.MUB6.Certificate.PairSemantics.sound3051`, `OAI.MUB6.Certificate.PairSemantics.sound3053`, `OAI.MUB6.Certificate.PairSemantics.sound3054`, `OAI.MUB6.Certificate.PairSemantics.sound3056`, `OAI.MUB6.Certificate.PairSemantics.sound3058`, `OAI.MUB6.Certificate.PairSemantics.sound3059`, `OAI.MUB6.Certificate.PairSemantics.sound3060`, `OAI.MUB6.Certificate.PairSemantics.sound3061`, `OAI.MUB6.Certificate.PairSemantics.sound3062`, `OAI.MUB6.Certificate.PairSemantics.sound3063`, `OAI.MUB6.Certificate.PairSemantics.sound3065`, `OAI.MUB6.Certificate.PairSemantics.sound3066`, `OAI.MUB6.Certificate.PairSemantics.sound3067`, `OAI.MUB6.Certificate.PairSemantics.sound3068`, `OAI.MUB6.Certificate.PairSemantics.sound3069`, `OAI.MUB6.Certificate.PairSemantics.sound3071`, `OAI.MUB6.Certificate.PairSemantics.sound3072`, `OAI.MUB6.Certificate.PairSemantics.sound3073`, `OAI.MUB6.Certificate.PairSemantics.sound3074`, `OAI.MUB6.Certificate.PairSemantics.sound3075`, `OAI.MUB6.Certificate.PairSemantics.sound3076`, `OAI.MUB6.Certificate.PairSemantics.sound3077`, `OAI.MUB6.Certificate.PairSemantics.sound3078`, `OAI.MUB6.Certificate.PairSemantics.sound3079`, `OAI.MUB6.Certificate.PairSemantics.sound3080`, `OAI.MUB6.Certificate.PairSemantics.sound3081`, `OAI.MUB6.Certificate.PairSemantics.sound3082`, `OAI.MUB6.Certificate.PairSemantics.sound3083`, `OAI.MUB6.Certificate.PairSemantics.sound3084`, `OAI.MUB6.Certificate.PairSemantics.sound3085`, `OAI.MUB6.Certificate.PairSemantics.sound3086`, `OAI.MUB6.Certificate.PairSemantics.sound3090`, `OAI.MUB6.Certificate.PairSemantics.sound3091`, `OAI.MUB6.Certificate.PairSemantics.sound3092`, `OAI.MUB6.Certificate.PairSemantics.sound3093`, `OAI.MUB6.Certificate.PairSemantics.sound3094`, `OAI.MUB6.Certificate.PairSemantics.sound3095`, `OAI.MUB6.Certificate.PairSemantics.sound3096`, `OAI.MUB6.Certificate.PairSemantics.sound3097`, `OAI.MUB6.Certificate.PairSemantics.sound3098`, `OAI.MUB6.Certificate.PairSemantics.sound3099`, `OAI.MUB6.Certificate.PairSemantics.sound3100`, `OAI.MUB6.Certificate.PairSemantics.sound3101`, `OAI.MUB6.Certificate.PairSemantics.sound3102`, `OAI.MUB6.Certificate.PairSemantics.sound3105`, `OAI.MUB6.Certificate.PairSemantics.sound3106`, `OAI.MUB6.Certificate.PairSemantics.sound3107`, `OAI.MUB6.Certificate.PairSemantics.sound3108`, `OAI.MUB6.Certificate.PairSemantics.sound3109`, `OAI.MUB6.Certificate.PairSemantics.sound3110`, `OAI.MUB6.Certificate.PairSemantics.sound3111`, `OAI.MUB6.Certificate.PairSemantics.sound3112`, `OAI.MUB6.Certificate.PairSemantics.sound3113`, `OAI.MUB6.Certificate.PairSemantics.sound3114`, `OAI.MUB6.Certificate.PairSemantics.sound3115`, `OAI.MUB6.Certificate.PairSemantics.sound3116`, `OAI.MUB6.Certificate.PairSemantics.sound3118`, `OAI.MUB6.Certificate.PairSemantics.sound3119`, `OAI.MUB6.Certificate.PairSemantics.sound3120`, `OAI.MUB6.Certificate.PairSemantics.sound3121`, `OAI.MUB6.Certificate.PairSemantics.sound3122`, `OAI.MUB6.Certificate.PairSemantics.sound3123`, `OAI.MUB6.Certificate.PairSemantics.sound3124`, `OAI.MUB6.Certificate.PairSemantics.sound3125`, `OAI.MUB6.Certificate.PairSemantics.sound3128`, `OAI.MUB6.Certificate.PairSemantics.sound3129`, `OAI.MUB6.Certificate.PairSemantics.sound3130`, `OAI.MUB6.Certificate.PairSemantics.sound3131`, `OAI.MUB6.Certificate.PairSemantics.sound3133`, `OAI.MUB6.Certificate.PairSemantics.sound3135`, `OAI.MUB6.Certificate.PairSemantics.sound3136`, `OAI.MUB6.Certificate.PairSemantics.sound3138`, `OAI.MUB6.Certificate.PairSemantics.sound3139`, `OAI.MUB6.Certificate.PairSemantics.sound3140`, `OAI.MUB6.Certificate.PairSemantics.sound3141`, `OAI.MUB6.Certificate.PairSemantics.sound3142`, `OAI.MUB6.Certificate.PairSemantics.sound3144`, `OAI.MUB6.Certificate.PairSemantics.sound3145`, `OAI.MUB6.Certificate.PairSemantics.sound3146`, `OAI.MUB6.Certificate.PairSemantics.sound3150`, `OAI.MUB6.Certificate.PairSemantics.sound3151`, `OAI.MUB6.Certificate.PairSemantics.sound3152`, `OAI.MUB6.Certificate.PairSemantics.sound3153`, `OAI.MUB6.Certificate.PairSemantics.sound3155`, `OAI.MUB6.Certificate.PairSemantics.sound3158`, `OAI.MUB6.Certificate.PairSemantics.sound3159`, `OAI.MUB6.Certificate.PairSemantics.sound3160`, `OAI.MUB6.Certificate.PairSemantics.sound3161`, `OAI.MUB6.Certificate.PairSemantics.sound3162`, `OAI.MUB6.Certificate.PairSemantics.sound3163`, `OAI.MUB6.Certificate.PairSemantics.sound3164`, `OAI.MUB6.Certificate.PairSemantics.sound3166`, `OAI.MUB6.Certificate.PairSemantics.sound3167`, `OAI.MUB6.Certificate.PairSemantics.sound3168`, `OAI.MUB6.Certificate.PairSemantics.sound3169`, `OAI.MUB6.Certificate.PairSemantics.sound3170`, `OAI.MUB6.Certificate.PairSemantics.sound3171`, `OAI.MUB6.Certificate.PairSemantics.sound3172`, `OAI.MUB6.Certificate.PairSemantics.sound3173`, `OAI.MUB6.Certificate.PairSemantics.sound3174`, `OAI.MUB6.Certificate.PairSemantics.sound3176`, `OAI.MUB6.Certificate.PairSemantics.sound3178`, `OAI.MUB6.Certificate.PairSemantics.sound3179`, `OAI.MUB6.Certificate.PairSemantics.sound3180`, `OAI.MUB6.Certificate.PairSemantics.sound3181`, `OAI.MUB6.Certificate.PairSemantics.sound3183`, `OAI.MUB6.Certificate.PairSemantics.sound3184`, `OAI.MUB6.Certificate.PairSemantics.sound3185`, `OAI.MUB6.Certificate.PairSemantics.sound3186`, `OAI.MUB6.Certificate.PairSemantics.sound3187`, `OAI.MUB6.Certificate.PairSemantics.sound3188`, `OAI.MUB6.Certificate.PairSemantics.sound3189`, `OAI.MUB6.Certificate.PairSemantics.sound3191`, `OAI.MUB6.Certificate.PairSemantics.sound3192`, `OAI.MUB6.Certificate.PairSemantics.sound3193`, `OAI.MUB6.Certificate.PairSemantics.sound3194`, `OAI.MUB6.Certificate.PairSemantics.sound3195`, `OAI.MUB6.Certificate.PairSemantics.sound3196`, `OAI.MUB6.Certificate.PairSemantics.sound3197`, `OAI.MUB6.Certificate.PairSemantics.sound3198`, `OAI.MUB6.Certificate.PairSemantics.sound3199`, `OAI.MUB6.Certificate.PairSemantics.sound3200`, `OAI.MUB6.Certificate.PairSemantics.sound3201`, `OAI.MUB6.Certificate.PairSemantics.sound3202`, `OAI.MUB6.Certificate.PairSemantics.sound3203`, `OAI.MUB6.Certificate.PairSemantics.sound3204`, `OAI.MUB6.Certificate.PairSemantics.sound3205`, `OAI.MUB6.Certificate.PairSemantics.sound3206`, `OAI.MUB6.Certificate.PairSemantics.sound3208`, `OAI.MUB6.Certificate.PairSemantics.sound3211`, `OAI.MUB6.Certificate.PairSemantics.sound3212`, `OAI.MUB6.Certificate.PairSemantics.sound3213`, `OAI.MUB6.Certificate.PairSemantics.sound3214`, `OAI.MUB6.Certificate.PairSemantics.sound3215`, `OAI.MUB6.Certificate.PairSemantics.sound3216`, `OAI.MUB6.Certificate.PairSemantics.sound3217`, `OAI.MUB6.Certificate.PairSemantics.sound3218`, `OAI.MUB6.Certificate.PairSemantics.sound3219`, `OAI.MUB6.Certificate.PairSemantics.sound3221`, `OAI.MUB6.Certificate.PairSemantics.sound3222`, `OAI.MUB6.Certificate.PairSemantics.sound3223`, `OAI.MUB6.Certificate.PairSemantics.sound3224`, `OAI.MUB6.Certificate.PairSemantics.sound3226`, `OAI.MUB6.Certificate.PairSemantics.sound3227`, `OAI.MUB6.Certificate.PairSemantics.sound3228`, `OAI.MUB6.Certificate.PairSemantics.sound3230`, `OAI.MUB6.Certificate.PairSemantics.sound3231`, `OAI.MUB6.Certificate.PairSemantics.sound3233`, `OAI.MUB6.Certificate.PairSemantics.sound3234`, `OAI.MUB6.Certificate.PairSemantics.sound3235`, `OAI.MUB6.Certificate.PairSemantics.sound3237`, `OAI.MUB6.Certificate.PairSemantics.sound3238`, `OAI.MUB6.Certificate.PairSemantics.sound3239`, `OAI.MUB6.Certificate.PairSemantics.sound3240`, `OAI.MUB6.Certificate.PairSemantics.sound3241`, `OAI.MUB6.Certificate.PairSemantics.sound3242`, `OAI.MUB6.Certificate.PairSemantics.sound3243`, `OAI.MUB6.Certificate.PairSemantics.sound3244`, `OAI.MUB6.Certificate.PairSemantics.sound3246`, `OAI.MUB6.Certificate.PairSemantics.sound3247`, `OAI.MUB6.Certificate.PairSemantics.sound3248`, `OAI.MUB6.Certificate.PairSemantics.sound3249`, `OAI.MUB6.Certificate.PairSemantics.sound3250`, `OAI.MUB6.Certificate.PairSemantics.sound3251`, `OAI.MUB6.Certificate.PairSemantics.sound3253`, `OAI.MUB6.Certificate.PairSemantics.sound3254`, `OAI.MUB6.Certificate.PairSemantics.sound3255`, `OAI.MUB6.Certificate.PairSemantics.sound3256`, `OAI.MUB6.Certificate.PairSemantics.sound3258`, `OAI.MUB6.Certificate.PairSemantics.sound3259`, `OAI.MUB6.Certificate.PairSemantics.sound3261`, `OAI.MUB6.Certificate.PairSemantics.sound3262`, `OAI.MUB6.Certificate.PairSemantics.sound3263`, `OAI.MUB6.Certificate.PairSemantics.sound3266`, `OAI.MUB6.Certificate.PairSemantics.sound3267`, `OAI.MUB6.Certificate.PairSemantics.sound3268`, `OAI.MUB6.Certificate.PairSemantics.sound3269`, `OAI.MUB6.Certificate.PairSemantics.sound3270`, `OAI.MUB6.Certificate.PairSemantics.sound3271`, `OAI.MUB6.Certificate.PairSemantics.sound3273`, `OAI.MUB6.Certificate.PairSemantics.sound3275`, `OAI.MUB6.Certificate.PairSemantics.sound3276`, `OAI.MUB6.Certificate.PairSemantics.sound3277`, `OAI.MUB6.Certificate.PairSemantics.sound3279`, `OAI.MUB6.Certificate.PairSemantics.sound3280`, `OAI.MUB6.Certificate.PairSemantics.sound3281`, `OAI.MUB6.Certificate.PairSemantics.sound3282`, `OAI.MUB6.Certificate.PairSemantics.sound3283`, `OAI.MUB6.Certificate.PairSemantics.sound3284`, `OAI.MUB6.Certificate.PairSemantics.sound3288`, `OAI.MUB6.Certificate.PairSemantics.sound3289`, `OAI.MUB6.Certificate.PairSemantics.sound3290`, `OAI.MUB6.Certificate.PairSemantics.sound3291`, `OAI.MUB6.Certificate.PairSemantics.sound3292`, `OAI.MUB6.Certificate.PairSemantics.sound3293`, `OAI.MUB6.Certificate.PairSemantics.sound3294`, `OAI.MUB6.Certificate.PairSemantics.sound3295`, `OAI.MUB6.Certificate.PairSemantics.sound3296`, `OAI.MUB6.Certificate.PairSemantics.sound3297`, `OAI.MUB6.Certificate.PairSemantics.sound3298`, `OAI.MUB6.Certificate.PairSemantics.sound3299`, `OAI.MUB6.Certificate.PairSemantics.sound3300`, `OAI.MUB6.Certificate.PairSemantics.sound3301`, `OAI.MUB6.Certificate.PairSemantics.sound3302`, `OAI.MUB6.Certificate.PairSemantics.sound3304`, `OAI.MUB6.Certificate.PairSemantics.sound3305`, `OAI.MUB6.Certificate.PairSemantics.sound3307`, `OAI.MUB6.Certificate.PairSemantics.sound3308`, `OAI.MUB6.Certificate.PairSemantics.sound3310`, `OAI.MUB6.Certificate.PairSemantics.sound3311`, `OAI.MUB6.Certificate.PairSemantics.sound3312`, `OAI.MUB6.Certificate.PairSemantics.sound3313`, `OAI.MUB6.Certificate.PairSemantics.sound3314`, `OAI.MUB6.Certificate.PairSemantics.sound3315`, `OAI.MUB6.Certificate.PairSemantics.sound3316`, `OAI.MUB6.Certificate.PairSemantics.sound3317`, `OAI.MUB6.Certificate.PairSemantics.sound3319`, `OAI.MUB6.Certificate.PairSemantics.sound3322`, `OAI.MUB6.Certificate.PairSemantics.sound3323`, `OAI.MUB6.Certificate.PairSemantics.sound3324`, `OAI.MUB6.Certificate.PairSemantics.sound3325`, `OAI.MUB6.Certificate.PairSemantics.sound3327`, `OAI.MUB6.Certificate.PairSemantics.sound3328`, `OAI.MUB6.Certificate.PairSemantics.sound3332`, `OAI.MUB6.Certificate.PairSemantics.sound3333`, `OAI.MUB6.Certificate.PairSemantics.sound3334`, `OAI.MUB6.Certificate.PairSemantics.sound3335`, `OAI.MUB6.Certificate.PairSemantics.sound3336`, `OAI.MUB6.Certificate.PairSemantics.sound3338`, `OAI.MUB6.Certificate.PairSemantics.sound3340`, `OAI.MUB6.Certificate.PairSemantics.sound3341`, `OAI.MUB6.Certificate.PairSemantics.sound3342`, `OAI.MUB6.Certificate.PairSemantics.sound3343`, `OAI.MUB6.Certificate.PairSemantics.sound3344`, `OAI.MUB6.Certificate.PairSemantics.sound3345`, `OAI.MUB6.Certificate.PairSemantics.sound3346`, `OAI.MUB6.Certificate.PairSemantics.sound3347`, `OAI.MUB6.Certificate.PairSemantics.sound3348`, `OAI.MUB6.Certificate.PairSemantics.sound3349`, `OAI.MUB6.Certificate.PairSemantics.sound3350`, `OAI.MUB6.Certificate.PairSemantics.sound3351`, `OAI.MUB6.Certificate.PairSemantics.sound3352`, `OAI.MUB6.Certificate.PairSemantics.sound3353`, `OAI.MUB6.Certificate.PairSemantics.sound3354`, `OAI.MUB6.Certificate.PairSemantics.sound3355`, `OAI.MUB6.Certificate.PairSemantics.sound3356`, `OAI.MUB6.Certificate.PairSemantics.sound3357`, `OAI.MUB6.Certificate.PairSemantics.sound3359`, `OAI.MUB6.Certificate.PairSemantics.sound3360`, `OAI.MUB6.Certificate.PairSemantics.sound3361`, `OAI.MUB6.Certificate.PairSemantics.sound3362`, `OAI.MUB6.Certificate.PairSemantics.sound3364`, `OAI.MUB6.Certificate.PairSemantics.sound3365`, `OAI.MUB6.Certificate.PairSemantics.sound3366`, `OAI.MUB6.Certificate.PairSemantics.sound3367`, `OAI.MUB6.Certificate.PairSemantics.sound3369`, `OAI.MUB6.Certificate.PairSemantics.sound3370`, `OAI.MUB6.Certificate.PairSemantics.sound3371`, `OAI.MUB6.Certificate.PairSemantics.sound3372`, `OAI.MUB6.Certificate.PairSemantics.sound3373`, `OAI.MUB6.Certificate.PairSemantics.sound3375`, `OAI.MUB6.Certificate.PairSemantics.sound3376`, `OAI.MUB6.Certificate.PairSemantics.sound3377`, `OAI.MUB6.Certificate.PairSemantics.sound3378`, `OAI.MUB6.Certificate.PairSemantics.sound3380`, `OAI.MUB6.Certificate.PairSemantics.sound3381`, `OAI.MUB6.Certificate.PairSemantics.sound3382`, `OAI.MUB6.Certificate.PairSemantics.sound3383`, `OAI.MUB6.Certificate.PairSemantics.sound3384`, `OAI.MUB6.Certificate.PairSemantics.sound3385`, `OAI.MUB6.Certificate.PairSemantics.sound3388`, `OAI.MUB6.Certificate.PairSemantics.sound3390`, `OAI.MUB6.Certificate.PairSemantics.sound3391`, `OAI.MUB6.Certificate.PairSemantics.sound3392`, `OAI.MUB6.Certificate.PairSemantics.sound3393`, `OAI.MUB6.Certificate.PairSemantics.sound3394`, `OAI.MUB6.Certificate.PairSemantics.sound3395`, `OAI.MUB6.Certificate.PairSemantics.sound3396`, `OAI.MUB6.Certificate.PairSemantics.sound3399`, `OAI.MUB6.Certificate.PairSemantics.sound3400`, `OAI.MUB6.Certificate.PairSemantics.sound3401`, `OAI.MUB6.Certificate.PairSemantics.sound3402`, `OAI.MUB6.Certificate.PairSemantics.sound3405`, `OAI.MUB6.Certificate.PairSemantics.sound3407`, `OAI.MUB6.Certificate.PairSemantics.sound3408`, `OAI.MUB6.Certificate.PairSemantics.sound3411`, `OAI.MUB6.Certificate.PairSemantics.sound3412`, `OAI.MUB6.Certificate.PairSemantics.sound3413`, `OAI.MUB6.Certificate.PairSemantics.sound3414`, `OAI.MUB6.Certificate.PairSemantics.sound3415`, `OAI.MUB6.Certificate.PairSemantics.sound3416`, `OAI.MUB6.Certificate.PairSemantics.sound3417`, `OAI.MUB6.Certificate.PairSemantics.sound3418`, `OAI.MUB6.Certificate.PairSemantics.sound3420`, `OAI.MUB6.Certificate.PairSemantics.sound3421`, `OAI.MUB6.Certificate.PairSemantics.sound3422`, `OAI.MUB6.Certificate.PairSemantics.sound3423`, `OAI.MUB6.Certificate.PairSemantics.sound3424`, `OAI.MUB6.Certificate.PairSemantics.sound3425`, `OAI.MUB6.Certificate.PairSemantics.sound3426`, `OAI.MUB6.Certificate.PairSemantics.sound3428`, `OAI.MUB6.Certificate.PairSemantics.sound3431`, `OAI.MUB6.Certificate.PairSemantics.sound3433`, `OAI.MUB6.Certificate.PairSemantics.sound3434`, `OAI.MUB6.Certificate.PairSemantics.sound3435`, `OAI.MUB6.Certificate.PairSemantics.sound3436`, `OAI.MUB6.Certificate.PairSemantics.sound3437`, `OAI.MUB6.Certificate.PairSemantics.sound3438`, `OAI.MUB6.Certificate.PairSemantics.sound3439`, `OAI.MUB6.Certificate.PairSemantics.sound3440`, `OAI.MUB6.Certificate.PairSemantics.sound3441`, `OAI.MUB6.Certificate.PairSemantics.sound3445`, `OAI.MUB6.Certificate.PairSemantics.sound3447`, `OAI.MUB6.Certificate.PairSemantics.sound3449`, `OAI.MUB6.Certificate.PairSemantics.sound3454`, `OAI.MUB6.Certificate.PairSemantics.sound3456`, `OAI.MUB6.Certificate.PairSemantics.sound3457`, `OAI.MUB6.Certificate.PairSemantics.sound3458`, `OAI.MUB6.Certificate.PairSemantics.sound3459`, `OAI.MUB6.Certificate.PairSemantics.sound3460`, `OAI.MUB6.Certificate.PairSemantics.sound3461`, `OAI.MUB6.Certificate.PairSemantics.sound3462`, `OAI.MUB6.Certificate.PairSemantics.sound3463`, `OAI.MUB6.Certificate.PairSemantics.sound3467`, `OAI.MUB6.Certificate.PairSemantics.sound3468`, `OAI.MUB6.Certificate.PairSemantics.sound381`, `OAI.MUB6.Certificate.PairSemantics.sound46`, `OAI.MUB6.Certificate.PairSemantics.sound545`, `OAI.MUB6.Certificate.PairSemantics.sound65`, `OAI.MUB6.Certificate.PairSemantics.sound659`, `OAI.MUB6.Certificate.PairSemantics.sound856`, `OAI.MUB6.Certificate.PairSemantics.sound858`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound0`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound1`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound10`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound100`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound101`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound102`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound103`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound104`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound105`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound106`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound107`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound108`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound111`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound112`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound113`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound114`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound115`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound116`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound117`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound118`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound119`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound12`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound120`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound121`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound124`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound125`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound126`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound127`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound128`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound129`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound13`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound130`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound131`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound132`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound133`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound134`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound135`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound136`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound137`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound139`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound140`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound141`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound142`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound146`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound148`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound15`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound150`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound151`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound153`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound154`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound155`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound156`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound157`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound158`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound159`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound16`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound160`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound161`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound162`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound163`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound164`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound165`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound166`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound167`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound168`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound17`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound170`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound171`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound174`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound175`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound176`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound177`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound178`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound179`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound18`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound180`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound181`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound182`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound184`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound185`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound186`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound187`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound188`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound19`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound190`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound191`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound192`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound193`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound194`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound195`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound196`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound197`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound198`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound2`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound20`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound200`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound201`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound202`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound204`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound205`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound207`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound208`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound209`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound21`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound210`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound211`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound213`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound214`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound216`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound218`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound219`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound22`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound221`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound222`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound223`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound224`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound225`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound226`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound227`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound228`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound229`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound23`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound230`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound231`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound232`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound233`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound234`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound235`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound236`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound237`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound238`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound239`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound24`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound240`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound241`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound242`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound243`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound244`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound245`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound246`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound248`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound249`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound25`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound250`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound253`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound254`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound26`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound27`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound28`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound3`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound30`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound31`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound32`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound34`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound35`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound36`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound38`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound39`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound4`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound40`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound41`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound42`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound43`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound44`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound45`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound46`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound47`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound49`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound5`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound51`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound52`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound53`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound54`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound56`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound57`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound58`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound59`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound6`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound60`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound61`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound62`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound63`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound64`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound65`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound66`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound67`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound69`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound70`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound72`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound74`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound76`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound77`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound78`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound79`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound8`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound80`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound81`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound82`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound83`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound84`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound85`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound86`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound87`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound89`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound9`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound90`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound91`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound92`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound93`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound94`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound95`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound96`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound97`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound98`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound99`, `OAI.MUB6.Certificate.PairTargetSemantics.certificate_zero1`, `OAI.MUB6.Certificate.PairTargetSemantics.expandedIdentity0`, `OAI.MUB6.Certificate.PairTargetSemantics.partition12`, `OAI.MUB6.Certificate.PairTargetSemantics.partition14`, `OAI.MUB6.Certificate.PairTargetSemantics.partition16`, `OAI.MUB6.Certificate.PairTargetSemantics.partition19`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm10`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm11`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm13`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm17`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm21`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm23`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm26`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm6`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm7`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm8` and `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm9`.
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

def raw5step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]

def raw5step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]

def raw6 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]

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

def raw52 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![3, -3], ![2, -2]]

def raw52step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![2, -2], ![3, -3]]

def raw53 : Matrix (Fin 2) (Fin 2) ℤ := ![![-5, 5], ![5, -5]]

def raw54 : Matrix (Fin 3) (Fin 4) ℤ := ![![-4, 0, 1, 3], ![1, 2, -2, -1], ![3, -2, 1, -2]]

def raw54step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]

def raw54step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 2, -1], ![-3, 1, 2]]

def raw54step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![1, -3, 2], ![2, -1, -1]]

def raw55 : Matrix (Fin 3) (Fin 4) ℤ := ![![-4, 0, 1, 3], ![2, -2, 1, -1], ![2, 2, -2, -2]]

def raw55step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 1, -2], ![3, -1, -2]]

def raw55step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 2, -2], ![-1, -1, 2], ![-3, 1, 2]]

def raw55step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 2, -3], ![2, -2, 0]]

def raw56 : Matrix (Fin 3) (Fin 4) ℤ := ![![-4, 0, 2, 2], ![1, 2, -2, -1], ![3, -2, 0, -1]]

def raw56step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]

def raw56step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]

def raw56step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

def raw57 : Matrix (Fin 3) (Fin 4) ℤ := ![![-4, 0, 3, 1], ![1, 2, -1, -2], ![3, -2, -2, 1]]

def raw57step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![3, -1, -2], ![1, -2, 1]]

def raw57step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-3, 1, 2], ![-1, 2, -1]]

def raw57step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![1, -3, 2], ![2, -1, -1]]

def raw58 : Matrix (Fin 3) (Fin 4) ℤ := ![![-4, 0, 3, 1], ![2, -2, -1, 1], ![2, 2, -2, -2]]

def raw58step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![3, -1, -2], ![1, 1, -2]]

def raw58step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 2, -2], ![-3, 1, 2], ![-1, -1, 2]]

def raw58step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 2, -3], ![2, -2, 0]]

def raw59 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]

def raw59step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

def raw60 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw515 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]

def raw516 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]

def raw517 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]

def raw517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw518step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw519 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

def raw519step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw520 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]

def raw520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw521 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

def raw522 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]

def raw522step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw523 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]

def raw524 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

def raw525 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]

def raw526 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]

def raw527 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]

def raw528 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 2, -3]]

def raw529 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]

def raw530 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]

def raw531 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

def raw531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw532 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]

def raw532step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 0, -1], ![1, 2, -3]]

def raw533 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![1, 2, -3]]

def raw533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]

def raw534 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

def raw534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]

def raw534step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw538 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]

def raw538step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

def raw539 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]

def raw540 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]

def raw540step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]

def raw541 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]

def raw541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

def raw542 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]

def raw542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]

def raw543 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]

def raw543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical160
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5144 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![-1, 1], ![1, -1], ![1, -1]]

def raw5144step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]

def raw5145 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![-1, 1], ![2, -2]]

def raw5145step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]

def raw5146 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![0, 0], ![0, 0], ![1, -1]]

def raw5146step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![0, 0], ![1, -1]]

def raw5146step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]

def raw5146step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw5147 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![0, 0], ![1, -1]]

def raw5147step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]

def raw5147step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw5148 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![0, 0], ![1, -1], ![0, 0]]

def raw5148step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![0, 0], ![1, -1]]

def raw5148step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]

def raw5148step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw5149 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]

def raw5149step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw5150 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1], ![0, 0]]

def raw5150step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]

def raw5150step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw5151 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]

def raw5151step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical161
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5152 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3], ![0, 0]]

def raw5152step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]

def raw5152step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw5153 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![0, 0], ![1, -1], ![2, -2]]

def raw5153step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![1, -1], ![2, -2]]

def raw5153step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw5154 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![0, 0], ![3, -3]]

def raw5154step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![3, -3]]

def raw5154step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]

def raw5154step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw5155 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![1, -1], ![0, 0], ![2, -2]]

def raw5155step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![1, -1], ![2, -2]]

def raw5155step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw5156 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw5156step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw5157 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![1, -1], ![2, -2]]

def raw5157step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw5158 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![1, -1], ![2, -2], ![0, 0]]

def raw5158step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![1, -1], ![2, -2]]

def raw5158step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw5159 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![2, -2], ![1, -1]]

def raw5159step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]

def raw5159step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw5160 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![2, -2], ![1, -1], ![0, 0]]

def raw5160step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![2, -2], ![1, -1]]

def raw5160step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]

def raw5160step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw5161 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![3, -3]]

def raw5161step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]

def raw5161step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw5162 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![-1, 1], ![2, -2], ![1, -1]]

def raw5162step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![2, -2], ![1, -1]]

def raw5162step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]

def raw5162step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw5163 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![0, 0], ![0, 0], ![2, -2]]

def raw5163step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![0, 0], ![2, -2]]

def raw5163step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![2, -2]]

def raw5163step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![2, -2]]

def raw5163step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

def raw5164 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![0, 0], ![1, -1], ![1, -1]]

def raw5164step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![1, -1], ![1, -1]]

def raw5164step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![1, -1]]

def raw5164step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw5165 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![0, 0], ![2, -2]]

def raw5165step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![2, -2]]

def raw5165step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![2, -2]]

def raw5165step2 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

def raw5166 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![1, -1], ![0, 0], ![1, -1]]

def raw5166step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![1, -1], ![1, -1]]

def raw5166step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![1, -1]]

def raw5166step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw5167 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![1, -1], ![1, -1]]

def raw5167step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![1, -1]]

def raw5167step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw5168 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![1, -1], ![1, -1], ![0, 0]]

def raw5168step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![1, -1], ![1, -1]]

def raw5168step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![1, -1]]

def raw5168step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw5169 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![2, -2]]

def raw5169step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![2, -2]]

def raw5169step1 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

def raw5170 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![2, -2], ![0, 0]]

def raw5170step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![2, -2]]

def raw5170step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![2, -2]]

def raw5170step2 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

def raw5171 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![-1, 1], ![0, 0], ![2, -2]]

def raw5171step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![-1, 1], ![2, -2]]

def raw5171step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]

def raw5171step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw5172 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![-1, 1], ![1, -1], ![1, -1]]

def raw5172step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![1, -1], ![1, -1]]

def raw5172step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw5173 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![-1, 1], ![2, -2]]

def raw5173step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]

def raw5173step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw5174 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![0, 0], ![0, 0], ![1, -1]]

def raw5174step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![0, 0], ![1, -1]]

def raw5174step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![1, -1]]

def raw5174step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw5175 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![0, 0], ![1, -1]]

def raw5175step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![1, -1]]

def raw5175step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw5176 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![0, 0], ![1, -1], ![0, 0]]

def raw5176step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![0, 0], ![1, -1]]

def raw5176step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![1, -1]]

def raw5176step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw5177 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![1, -1]]

def raw5177step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw5178 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![1, -1], ![-1, 1], ![1, -1]]

def raw5178step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![-1, 1], ![1, -1]]

def raw5178step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw5179 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![1, -1], ![0, 0]]

def raw5179step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![1, -1]]

def raw5179step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw5180 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![1, -1], ![0, 0], ![0, 0]]

def raw5180step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![1, -1], ![0, 0]]

def raw5180step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![1, -1]]

def raw5180step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw5181 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![1, -1], ![1, -1], ![-1, 1]]

def raw5181step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![-1, 1]]

def raw5181step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw5182 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![2, -2], ![-1, 1]]

def raw5182step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![2, -2], ![-1, 1]]

def raw5182step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw5183 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![2, -2]]

def raw5183step0 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical162
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5184 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![2, -2], ![-1, 1], ![1, -1]]

def raw5184step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![2, -2], ![-1, 1], ![1, -1]]

def raw5184step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw5185 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![2, -2], ![0, 0]]

def raw5185step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![2, -2]]

def raw5185step1 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

def raw5186 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![2, -2], ![0, 0], ![0, 0], ![0, 0]]

def raw5186step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![2, -2], ![0, 0], ![0, 0]]

def raw5186step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![2, -2], ![0, 0]]

def raw5186step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![2, -2]]

def raw5186step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

def raw5187 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-2, 2], ![1, -1], ![2, -2]]

def raw5187step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]

def raw5188 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![0, 0], ![1, -1], ![1, -1]]

def raw5188step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![1, -1], ![1, -1]]

def raw5188step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw5189 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![0, 0], ![2, -2]]

def raw5189step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]

def raw5189step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw5190 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![1, -1], ![1, -1]]

def raw5190step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw5191 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![1, -1], ![1, -1], ![0, 0]]

def raw5191step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![1, -1], ![1, -1]]

def raw5191step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw5192 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]

def raw5192step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw5193 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![2, -2], ![0, 0]]

def raw5193step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]

def raw5193step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw5194 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![-1, 1], ![2, -2]]

def raw5194step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]

def raw5194step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw5195 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![0, 0], ![0, 0], ![1, -1]]

def raw5195step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![0, 0], ![1, -1]]

def raw5195step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![1, -1]]

def raw5195step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw5196 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![0, 0], ![1, -1]]

def raw5196step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![1, -1]]

def raw5196step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw5197 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![1, -1]]

def raw5197step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw5198 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![1, -1], ![0, 0]]

def raw5198step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![1, -1]]

def raw5198step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw5199 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw5200 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![-2, 2], ![1, -1], ![1, -1]]

def raw5200step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]

def raw5201 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![-2, 2], ![2, -2]]

def raw5201step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]

def raw5202 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![-1, 1], ![0, 0], ![1, -1]]

def raw5202step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![-1, 1], ![1, -1]]

def raw5202step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw5203 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![-1, 1], ![1, -1]]

def raw5203step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw5204 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![0, 0]]

def raw5204step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw5205 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![0, 0], ![0, 0]]

def raw5205step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![0, 0]]

def raw5205step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw5206 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![0, 0], ![0, 0], ![0, 0]]

def raw5206step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![0, 0], ![0, 0]]

def raw5206step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![0, 0]]

def raw5206step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw5207 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![0, 0], ![-1, 1]]

def raw5207step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![-1, 1]]

def raw5207step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw5208 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![2, -2], ![-1, 1]]

def raw5208step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw5209 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![2, -2], ![-1, 1], ![0, 0]]

def raw5209step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![2, -2], ![-1, 1]]

def raw5209step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw5210 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

def raw5211 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![2, -2], ![-2, 2], ![2, -2]]

def raw5211step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![2, -2]]

def raw5212 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![2, -2], ![-1, 1], ![0, 0], ![1, -1]]

def raw5212step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![2, -2], ![-1, 1], ![1, -1]]

def raw5212step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw5213 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![2, -2], ![-1, 1], ![1, -1]]

def raw5213step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw5214 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![2, -2], ![0, 0]]

def raw5214step0 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

def raw5215 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![2, -2], ![0, 0], ![0, 0]]

def raw5215step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![2, -2], ![0, 0]]

def raw5215step1 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical163
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5216 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![2, -2], ![0, 0], ![0, 0], ![0, 0]]

def raw5216step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![2, -2], ![0, 0], ![0, 0]]

def raw5216step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![2, -2], ![0, 0]]

def raw5216step2 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

def raw5217 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![2, -2], ![1, -1], ![0, 0], ![-1, 1]]

def raw5217step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![2, -2], ![1, -1], ![-1, 1]]

def raw5217step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw5218 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![3, -3], ![-1, 1]]

def raw5218step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw5219 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -3, 3], ![0, -1, 2, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw5219step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![-3, 2, 0, 1], ![3, -1, 0, -2]]

def raw5219step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -2, 3], ![0, 2, 1, -3], ![1, 0, 1, -2]]

def raw5220 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -3, 3], ![0, -1, 2, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw5220step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![-3, 2, 1, 0], ![3, -1, -1, -1]]

def raw5220step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, 1, 0, -2]]

def raw5221 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -3, 3], ![0, -1, 3, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw5221step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![-3, 3, 0, 0], ![3, -2, 0, -1]]

def raw5221step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-2, 1, 1, 0], ![3, -3, 0, 0], ![-3, 2, 0, 1]]

def raw5221step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -3, 3], ![0, 1, 1, -2], ![1, 0, 2, -3]]

def raw5222 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -3, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw5223 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -3, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, -2, 1, -1]]

def raw5223step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![2, 0, 0, -2], ![-3, 1, 1, 1], ![3, -1, -1, -1]]

def raw5223step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 1, 1, -3]]

def raw5224 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -3, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw5225 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -3, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![2, -2, 0, 0]]

def raw5225step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![2, 0, 0, -2], ![-3, 1, 2, 0], ![3, -1, -2, 0]]

def raw5225step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 2, 0, -3]]

def raw5226 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -3, 3], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw5226step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-3, 1, 0, 2], ![3, -1, 0, -2]]

def raw5226step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 0, 2, -3]]

def raw5227 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -3, 3], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def raw5227step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-3, 1, 1, 1], ![3, -1, -1, -1]]

def raw5227step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 1, 1, -3]]

def raw5228 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -3, 3], ![0, 0, 2, -2], ![1, -2, 0, 1], ![1, 0, 1, -2]]

def raw5228step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -2, 0], ![-3, 2, 0, 1], ![3, -2, 1, -2]]

def raw5228step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, 1, 0, -3]]

def raw5229 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -3, 3], ![0, 0, 2, -2], ![1, -2, 1, 0], ![1, 0, 0, -1]]

def raw5229step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -2, 0], ![-3, 2, 1, 0], ![3, -2, 0, -1]]

def raw5229step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, 0, 1, -2]]

def raw5230 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -3, 3], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw5230step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-3, 2, 0, 1], ![3, -2, 0, -1]]

def raw5230step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -2, 3], ![0, 1, 2, -3], ![1, 1, 0, -2]]

def raw5231 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -3, 3], ![0, 0, 2, -2], ![1, -1, 1, -1], ![1, -1, 0, 0]]

def raw5231step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-3, 2, 1, 0], ![3, -2, -1, 0]]

def raw5231step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -2, 3], ![0, 1, 2, -3], ![1, 1, 0, -2]]

def raw5232 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -3, 3], ![0, 0, 3, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw5232step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-3, 3, 0, 0], ![3, -3, 0, 0]]

def raw5232step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -3, 3], ![0, 0, 3, -3], ![1, 1, 0, -2]]

def raw5233 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -2, 2, 0], ![0, 0, -1, 1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw5233step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def raw5234 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, -1, 2], ![0, -1, 2, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw5235 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, -1, 2], ![0, -1, 2, -1], ![1, 0, 1, -2], ![1, 0, 0, -1]]

def raw5235step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, -1, 2], ![0, -1, 2, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw5236 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, -1, 2], ![0, -1, 2, -1], ![2, 0, 1, -3]]

def raw5236step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -2, 2, -2], ![0, 1, 1, -2], ![0, 1, -2, 1], ![-2, 0, -1, 3]]

def raw5236step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -2, 2, -2]]

def raw5237 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, -1, 2], ![0, -1, 3, -2], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw5238 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, -1, 2], ![0, -1, 3, -2], ![2, 0, 0, -2]]

def raw5238step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -2, 2, -2], ![0, 1, 1, -2], ![0, 1, -3, 2], ![-2, 0, 0, 2]]

def raw5238step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -3, 2], ![0, 1, 1, -2], ![2, -2, 2, -2]]

def raw5239 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, -1, 2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw5240 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, -1, 2], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw5241 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, -1, 2], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw5242 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, -1, 2], ![0, 0, 2, -2], ![2, -1, 1, -2]]

def raw5242step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -2, 2, -2], ![0, 1, 1, -2], ![0, 0, -2, 2], ![-2, 1, -1, 2]]

def raw5242step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, -2, 2, -2]]

def raw5243 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, -1, 2], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw5243step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![-2, -1, 0, 3], ![2, 2, 0, -4]]

def raw5243step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 2, -4, 2], ![1, 0, 1, -2]]

def raw5244 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, -1, 2], ![1, -1, 1, -1], ![1, 0, 2, -3]]

def raw5244step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![-2, -1, 1, 2], ![2, 2, -1, -3]]

def raw5244step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-2, 1, 1, 0], ![2, 1, -1, -2], ![-2, -2, 1, 3]]

def raw5244step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -1, 2], ![1, -1, -2, 2], ![1, 1, 0, -2]]

def raw5245 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, -1, 2], ![1, -1, 2, -2], ![1, 0, 1, -2]]

def raw5246 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, -1, 2], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def raw5246step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![-2, -1, 3, 0], ![2, 2, -3, -1]]

def raw5246step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-2, 1, 1, 0], ![2, 1, -3, 0], ![-2, -2, 3, 1]]

def raw5246step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -3, 2], ![0, 1, 1, -2], ![1, -2, 3, -2]]

def raw5247 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 0, 1], ![0, -1, 2, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw5247step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical164
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5248 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 0, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw5248step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw5249 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 0, 1], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw5249step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![-2, 0, 0, 2], ![2, 1, 0, -3]]

def raw5249step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -3, 2], ![1, 0, 1, -2]]

def raw5250 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 0, 1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw5250step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![-2, 0, 1, 1], ![2, 1, -1, -2]]

def raw5250step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -1, -2, 2]]

def raw5251 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 0, 1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def raw5251step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![-2, 0, 2, 0], ![2, 1, -2, -1]]

def raw5251step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-2, 1, 1, 0], ![2, 0, -2, 0], ![-2, -1, 2, 1]]

def raw5251step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, -1, 2, -2]]

def raw5252 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 1, 0], ![0, -1, 0, 1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw5252step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw5253 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw5254 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![1, 0, 0, -1], ![1, -1, 2, -2]]

def raw5254step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def raw5255 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 1, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw5255step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![-2, 1, 0, 1], ![2, 0, 0, -2]]

def raw5255step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw5256 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 2, -1], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def raw5256step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![-2, 2, -1, 1], ![2, -1, 1, -2]]

def raw5256step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 0, 1, -2], ![1, 2, -1, -2]]

def raw5257 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 2, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw5257step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![-2, 2, 0, 0], ![2, -1, 0, -1]]

def raw5257step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-2, 1, 1, 0], ![2, -2, 0, 0], ![-2, 1, 0, 1]]

def raw5257step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw5258 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 2, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw5258step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![-2, 2, 1, -1], ![2, -1, -1, 0]]

def raw5258step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-2, 1, 1, 0], ![2, -2, -1, 1], ![-2, 1, 1, 0]]

def raw5258step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -1, -2, 2]]

def raw5259 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 3, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw5259step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![-2, 3, -1, 0], ![2, -2, 1, -1]]

def raw5259step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-2, 1, 1, 0], ![2, -3, 1, 0], ![-2, 2, -1, 1]]

def raw5259step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -3, 2], ![0, 1, 1, -2], ![1, -1, 2, -2]]

def raw5260 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 3, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw5260step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![-2, 3, 0, -1], ![2, -2, 0, 0]]

def raw5260step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-2, 1, 1, 0], ![2, -3, 0, 1], ![-2, 2, 0, 0]]

def raw5260step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -3, 2], ![1, 0, 1, -2]]

def raw5261 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, -1, 1], ![0, -1, 1, 0], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw5261step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw5262 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, -1, 1], ![0, -1, 1, 0], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw5262step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw5263 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, -1, 1], ![0, -1, 2, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw5263step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 2, -1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw5264 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, -2, 1, -1]]

def raw5265 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![2, -2, 0, 0]]

def raw5266 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -2, 0, 1], ![1, 0, 2, -3]]

def raw5266step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 2, -3], ![2, -2, -2, 2]]

def raw5267 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -2, 1, 0], ![1, 0, 1, -2]]

def raw5267step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![2, -2, 2, -2]]

def raw5268 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw5269 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def raw5270 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -2, 0, 1], ![1, 0, 1, -2]]

def raw5270step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, 1, -2], ![2, -2, -2, 2]]

def raw5271 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw5272 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, -1, 1], ![1, -2, 1, 0], ![1, 0, 2, -3]]

def raw5272step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -2, 0], ![-2, -1, 1, 2], ![2, 1, 0, -3]]

def raw5272step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-2, 0, 2, 0], ![2, 1, -1, -2], ![-2, -1, 0, 3]]

def raw5272step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw5273 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, -1, 1], ![1, -2, 2, -1], ![1, 0, 1, -2]]

def raw5273step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -2, 0], ![-2, -1, 2, 1], ![2, 1, -1, -2]]

def raw5273step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, -2, -1, 2]]

def raw5274 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, -1, 1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw5274step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -2, 0], ![-2, -1, 3, 0], ![2, 1, -2, -1]]

def raw5274step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, 2, -2]]

def raw5275 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw5275step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-2, -1, 0, 3], ![2, 1, 0, -3]]

def raw5275step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 0, 2, -3]]

def raw5276 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, -1, 1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def raw5276step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-2, -1, 1, 2], ![2, 1, -1, -2]]

def raw5276step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, -1, -2, 2]]

def raw5277 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, -1, 1], ![1, -1, 2, -2], ![1, -1, 1, -1]]

def raw5277step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-2, -1, 2, 1], ![2, 1, -2, -1]]

def raw5277step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, -1, -2, 2]]

def raw5278 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 0, 0], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw5278step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![2, 0, 0, -1, -1], ![-2, 0, 1, 0, 1], ![2, 0, -1, 0, -1]]

def raw5278step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-2, 1, 0, 1], ![2, -1, 0, -1]]

def raw5278step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw5279 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 0, 0], ![0, 0, 1, -1], ![2, -2, 1, -1]]

def raw5279step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![2, 0, 0, -2], ![-2, 0, 1, 1], ![2, 0, -1, -1]]

def raw5279step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![2, 0, -2], ![-2, 1, 1], ![2, -1, -1]]

def raw5279step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical165
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5280 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 0, 0], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw5280step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![2, 0, 0, -1, -1], ![-2, 0, 2, 0, 0], ![2, 0, -2, 0, 0]]

def raw5280step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-2, 2, 0, 0], ![2, -2, 0, 0]]

def raw5280step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def raw5281 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 0, 0], ![0, 0, 2, -2], ![2, -2, 0, 0]]

def raw5281step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![2, 0, 0, -2], ![-2, 0, 2, 0], ![2, 0, -2, 0]]

def raw5281step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![2, 0, -2], ![-2, 2, 0], ![2, -2, 0]]

def raw5281step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![2, 0, -2]]

def raw5282 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw5282step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-2, 0, 0, 2], ![2, 0, 0, -2]]

def raw5282step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![2, -1, -1], ![-2, 0, 2], ![2, 0, -2]]

def raw5282step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

def raw5283 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 0, 0], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def raw5283step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-2, 0, 1, 1], ![2, 0, -1, -1]]

def raw5283step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![2, -1, -1], ![-2, 1, 1], ![2, -1, -1]]

def raw5283step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![1, 1, -2], ![1, 1, -2]]

def raw5284 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 1, -1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw5284step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![2, 0, 0, -1, -1], ![-2, 1, 0, 0, 1], ![2, -1, 0, 0, -1]]

def raw5284step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-2, 1, 0, 1], ![2, -1, 0, -1]]

def raw5284step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw5285 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 1, -1], ![0, 0, 0, 0], ![2, -2, 1, -1]]

def raw5285step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![2, 0, 0, -2], ![-2, 1, 0, 1], ![2, -1, 0, -1]]

def raw5285step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![2, 0, -2], ![-2, 1, 1], ![2, -1, -1]]

def raw5285step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

def raw5286 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, -2, -1, 1]]

def raw5287 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, -1, 1, -1]]

def raw5288 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw5288step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw5289 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, -2, 0, 0]]

def raw5289step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![2, 0, 0, -2], ![-2, 1, 1, 0], ![2, -1, -1, 0]]

def raw5289step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def raw5290 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw5291 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, -1, 1]]

def raw5291step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw5292 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![2, -2, -1, 1]]

def raw5292step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![2, 0, 0, -2], ![-2, 1, 2, -1], ![2, -1, -2, 1]]

def raw5292step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 2, -1, -2]]

def raw5293 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, -1, 2, -2]]

def raw5293step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-2, 1, -1, 2], ![2, -1, 1, -2]]

def raw5293step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, -1, 2, -2]]

def raw5294 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw5294step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-2, 1, 0, 1], ![2, -1, 0, -1]]

def raw5294step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw5295 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, -1, 0, 0]]

def raw5295step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-2, 1, 1, 0], ![2, -1, -1, 0]]

def raw5295step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw5296 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 2, -2], ![0, 0, 1, -1], ![2, -2, -1, 1]]

def raw5296step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![2, 0, 0, -2], ![-2, 2, 1, -1], ![2, -2, -1, 1]]

def raw5296step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 2, -1, -2]]

def raw5297 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 2, -2], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def raw5297step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -2, 0], ![-2, 2, 1, -1], ![2, -2, 0, 0]]

def raw5297step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-2, 0, 2, 0], ![2, -2, -1, 1], ![-2, 2, 0, 0]]

def raw5297step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw5298 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, -1, 1, -1]]

def raw5298step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-2, 2, -1, 1], ![2, -2, 1, -1]]

def raw5298step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 1, 1, -2], ![2, 1, -1, -2]]

def raw5299 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw5299step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-2, 2, 0, 0], ![2, -2, 0, 0]]

def raw5299step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def raw5300 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 3, -3], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def raw5300step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -2, 0], ![-2, 3, 0, -1], ![2, -3, 1, 0]]

def raw5300step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-2, 0, 2, 0], ![2, -3, 0, 1], ![-2, 3, -1, 0]]

def raw5300step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 2, 0, -2], ![1, 0, -3, 2]]

def raw5301 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 3, -3], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw5301step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-2, 3, -1, 0], ![2, -3, 1, 0]]

def raw5301step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 1, -3, 2], ![1, 1, 0, -2]]

def raw5302 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![1, -2, -1, 2], ![0, 0, 2, -2], ![1, 0, 1, -2]]

def raw5302step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![2, -2, 0, 0], ![-2, -1, 2, 1], ![2, 2, -2, -2]]

def raw5302step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, 1, -1, -2]]

def raw5303 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![1, -1, -1, 1], ![0, -1, 2, -1], ![1, 0, 1, -2]]

def raw5303step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![2, -1, -1, 0], ![-2, -1, 2, 1], ![2, 1, -1, -2]]

def raw5303step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 0, 1, -2], ![1, 2, -1, -2]]

def raw5304 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![1, -1, -1, 1], ![0, -1, 3, -2], ![1, 0, 0, -1]]

def raw5304step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![2, -1, -1, 0], ![-2, -1, 3, 0], ![2, 1, -2, -1]]

def raw5304step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![-2, 1, 1, 0], ![2, 1, -3, 0], ![-2, -1, 2, 1]]

def raw5304step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -3, 2], ![0, 1, 1, -2], ![1, -1, 2, -2]]

def raw5305 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, -1, -2, 3], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw5305step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![-1, -2, 0, 3], ![1, 3, 0, -4]]

def raw5305step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -2, -1, 3], ![0, 3, 1, -4], ![1, 0, -2, 1]]

def raw5306 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, -1, -1, 2], ![0, -1, 2, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw5306step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw5307 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw5308 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, -1, -1, 2], ![1, -1, -1, 1], ![1, 0, 3, -4]]

def raw5308step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![-1, -1, -1, 3], ![1, 2, 1, -4]]

def raw5308step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-2, 1, 1, 0], ![1, 1, 1, -3], ![-1, -2, -1, 4]]

def raw5308step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 1, -2, 0], ![1, 1, 1, -3]]

def raw5309 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, -1, -1, 2], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw5309step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![-1, -1, 0, 2], ![1, 2, 0, -3]]

def raw5309step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -3, 1], ![1, 0, 1, -2]]

def raw5310 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, -1, -1, 2], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw5310step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def raw5311 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, -1, -1, 2], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw5311step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![-1, -1, 3, -1], ![1, 2, -3, 0]]

def raw5311step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, 0, -2, 1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical166
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5312 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, -1, 3, -2], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw5312step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -2, 1, -1], ![0, 1, -3, 2], ![0, 0, 2, -2], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw5312step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, -1, 1, 0], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw5313 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, -1, 3, -2], ![1, -1, -2, 2], ![1, 0, 0, -1]]

def raw5313step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![-1, 3, -2, 0], ![1, -2, 2, -1]]

def raw5313step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, -1, 2, -1], ![0, 3, -1, -2], ![1, 0, -2, 1]]

def raw5314 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, -1, 3, -2], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw5314step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![-1, 3, -1, -1], ![1, -2, 1, 0]]

def raw5314step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw5315 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, -1, 3, -2], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw5315step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![-1, 3, 0, -2], ![1, -2, 0, 1]]

def raw5315step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-2, 1, 1, 0], ![1, -3, 0, 2], ![-1, 2, 0, -1]]

def raw5315step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -3, 1], ![1, 0, 1, -2]]

def raw5316 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, -2, 1, -1]]

def raw5317 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![2, -2, 0, 0]]

def raw5318 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw5319 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def raw5320 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![2, -2, 2, -2]]

def raw5320step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![2, 0, 0, -2], ![-1, -2, 1, 2], ![1, 2, -1, -2]]

def raw5320step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, 1, -2], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, -2, -1, 2]]

def raw5321 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw5322 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, -1, 1, -1], ![1, -1, 0, 0]]

def raw5322step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw5323 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![2, -2, 1, -1]]

def raw5324 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw5325 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 3, -3], ![2, -2, 0, 0]]

def raw5325step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![2, 0, 0, -2], ![-1, -2, 3, 0], ![1, 2, -3, 0]]

def raw5325step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -2, 2, 0], ![0, 2, -2, 0], ![2, 0, 1, -3]]

def raw5326 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def raw5326step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -2, 0], ![-1, -2, 0, 3], ![1, 2, 1, -4]]

def raw5326step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-2, 0, 2, 0], ![1, 2, 0, -3], ![-1, -2, -1, 4]]

def raw5326step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, -2, 0], ![2, 0, 1, -3]]

def raw5327 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![1, -2, 1, 0], ![1, 0, 2, -3]]

def raw5327step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -2, 0], ![-1, -2, 1, 2], ![1, 2, 0, -3]]

def raw5327step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-2, 0, 2, 0], ![1, 2, -1, -2], ![-1, -2, 0, 3]]

def raw5327step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![2, -1, 1, -2]]

def raw5328 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![1, -2, 2, -1], ![1, 0, 1, -2]]

def raw5328step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, -2, 1, -1]]

def raw5329 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw5329step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -2, 0], ![-1, -2, 3, 0], ![1, 2, -2, -1]]

def raw5329step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-2, 0, 2, 0], ![1, 2, -3, 0], ![-1, -2, 2, 1]]

def raw5329step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -2, -1, 2]]

def raw5330 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw5330step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-1, -2, 0, 3], ![1, 2, 0, -3]]

def raw5330step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, -1, 3], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw5331 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def raw5331step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-1, -2, 1, 2], ![1, 2, -1, -2]]

def raw5331step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![2, -1, 1, -2]]

def raw5332 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![1, -1, 2, -2], ![1, -1, 1, -1]]

def raw5332step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-1, -2, 2, 1], ![1, 2, -2, -1]]

def raw5332step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![2, -1, 1, -2]]

def raw5333 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![1, -1, 3, -3], ![1, -1, 0, 0]]

def raw5333step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-1, -2, 3, 0], ![1, 2, -3, 0]]

def raw5333step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, -1, 3], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw5334 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, -1, -1, 2], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw5334step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw5335 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def raw5335step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![2, -2, -1, 1]]

def raw5336 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw5337 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 0, 1, -1], ![2, -2, 1, -1]]

def raw5337step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![2, 0, 0, 0, -2], ![-1, -1, 0, 1, 1], ![1, 1, 0, -1, -1]]

def raw5337step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![2, 0, 0, -2], ![-1, -1, 1, 1], ![1, 1, -1, -1]]

def raw5337step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, -1, 1, -1]]

def raw5338 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 0, 2, -2], ![2, -2, 0, 0]]

def raw5338step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![2, 0, 0, 0, -2], ![-1, -1, 0, 2, 0], ![1, 1, 0, -2, 0]]

def raw5338step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![2, 0, 0, -2], ![-1, -1, 2, 0], ![1, 1, -2, 0]]

def raw5338step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw5339 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw5339step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![2, 0, 0, -1, -1], ![-1, -1, 0, 0, 2], ![1, 1, 0, 0, -2]]

def raw5339step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-1, -1, 0, 2], ![1, 1, 0, -2]]

def raw5339step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 0, 1, -2]]

def raw5340 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![2, -2, 1, -1]]

def raw5340step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![2, 0, 0, 0, -2], ![-1, -1, 1, 0, 1], ![1, 1, -1, 0, -1]]

def raw5340step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![2, 0, 0, -2], ![-1, -1, 1, 1], ![1, 1, -1, -1]]

def raw5340step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, -1, 1, -1]]

def raw5341 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, -2, 0, 0]]

def raw5341step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw5342 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![2, -2, -1, 1]]

def raw5343 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, -1, 2, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical167
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5344 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw5344step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw5345 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![2, -2, 1, -1]]

def raw5345step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![2, 0, 0, -2], ![-1, -1, 1, 1], ![1, 1, -1, -1]]

def raw5345step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, -1, 1, -1]]

def raw5346 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw5346step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw5347 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, 2, -2], ![2, -2, 0, 0]]

def raw5347step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![2, 0, 0, -2], ![-1, -1, 2, 0], ![1, 1, -2, 0]]

def raw5347step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw5348 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![1, -2, -1, 2], ![1, 0, 3, -4]]

def raw5348step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -2, 0], ![-1, -1, -1, 3], ![1, 1, 2, -4]]

def raw5348step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-2, 0, 2, 0], ![1, 1, 1, -3], ![-1, -1, -2, 4]]

def raw5348step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 1, 1, -3]]

def raw5349 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, -1, 3, -3]]

def raw5349step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-1, -1, -1, 3], ![1, 1, 1, -3]]

def raw5349step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 1, 1, -3]]

def raw5350 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw5350step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-1, -1, 0, 2], ![1, 1, 0, -2]]

def raw5350step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 0, 1, -2]]

def raw5351 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def raw5351step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-1, -1, 1, 1], ![1, 1, -1, -1]]

def raw5351step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, -1, -1, 1]]

def raw5352 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, -2, -1, 1]]

def raw5352step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![2, 0, 0, 0, -2], ![-1, 0, 1, 1, -1], ![1, 0, -1, -1, 1]]

def raw5352step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![2, 0, 0, -2], ![-1, 1, 1, -1], ![1, -1, -1, 1]]

def raw5352step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 1, -1, -1]]

def raw5353 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, 0, 0], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, -1, 1, -1]]

def raw5353step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![2, 0, 0, -1, -1], ![-1, 0, 1, -1, 1], ![1, 0, -1, 1, -1]]

def raw5353step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-1, 1, -1, 1], ![1, -1, 1, -1]]

def raw5353step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw5354 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, 0, 0], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw5354step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![2, 0, 0, -1, -1], ![-1, 0, 2, -1, 0], ![1, 0, -2, 1, 0]]

def raw5354step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-1, 2, -1, 0], ![1, -2, 1, 0]]

def raw5354step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def raw5355 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, 0, 0], ![0, 0, 2, -2], ![2, -2, -1, 1]]

def raw5355step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![2, 0, 0, -2], ![-1, 0, 2, -1], ![1, 0, -2, 1]]

def raw5355step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![2, 0, -2], ![-1, 2, -1], ![1, -2, 1]]

def raw5355step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]

def raw5356 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, 0, 0], ![1, -1, -1, 1], ![1, -1, 2, -2]]

def raw5356step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-1, 0, -1, 2], ![1, 0, 1, -2]]

def raw5356step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![2, -1, -1], ![-1, -1, 2], ![1, 1, -2]]

def raw5356step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2]]

def raw5357 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 0, 1, -1], ![2, -2, -1, 1]]

def raw5357step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![2, 0, 0, 0, -2], ![-1, 1, 0, 1, -1], ![1, -1, 0, -1, 1]]

def raw5357step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![2, 0, 0, -2], ![-1, 1, 1, -1], ![1, -1, -1, 1]]

def raw5357step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 1, -1, -1]]

def raw5358 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![1, -1, -1, 1], ![1, -1, 1, -1]]

def raw5358step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![2, 0, 0, -1, -1], ![-1, 1, 0, -1, 1], ![1, -1, 0, 1, -1]]

def raw5358step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-1, 1, -1, 1], ![1, -1, 1, -1]]

def raw5358step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw5359 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![2, -2, -1, 1]]

def raw5359step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![2, 0, 0, 0, -2], ![-1, 1, 1, 0, -1], ![1, -1, -1, 0, 1]]

def raw5359step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![2, 0, 0, -2], ![-1, 1, 1, -1], ![1, -1, -1, 1]]

def raw5359step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 1, -1, -1]]

def raw5360 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, -2, -2, 2]]

def raw5360step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, -2, -1, 1]]

def raw5361 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, -2, 2], ![1, -1, 1, -1]]

def raw5362 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw5362step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw5363 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, -2, -1, 1]]

def raw5363step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![2, 0, 0, -2], ![-1, 1, 1, -1], ![1, -1, -1, 1]]

def raw5363step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 1, -1, -1]]

def raw5364 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, -2, 2], ![1, -1, 0, 0]]

def raw5365 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, -1, -1, 1]]

def raw5366 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![2, -2, -2, 2]]

def raw5366step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![2, 0, 0, -2], ![-1, 1, 2, -2], ![1, -1, -2, 2]]

def raw5366step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 2, -1, -2]]

def raw5367 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, 1, -1], ![1, -1, -2, 2], ![1, -1, 2, -2]]

def raw5367step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-1, 1, -2, 2], ![1, -1, 2, -2]]

def raw5367step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 2, -1, -2]]

def raw5368 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, -1, 1, -1]]

def raw5368step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-1, 1, -1, 1], ![1, -1, 1, -1]]

def raw5368step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw5369 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, 2, -2], ![1, -2, 1, 0], ![1, 0, -2, 1]]

def raw5369step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -2, 1, -1], ![0, 0, -2, 2], ![-1, 2, -1, 0], ![-1, 0, 2, -1]]

def raw5369step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw5370 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, 2, -2], ![1, -1, -2, 2], ![1, -1, 1, -1]]

def raw5370step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-1, 2, -2, 1], ![1, -2, 2, -1]]

def raw5370step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![2, 1, -1, -2]]

def raw5371 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw5371step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-1, 2, -1, 0], ![1, -2, 1, 0]]

def raw5371step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def raw5372 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, -1, 1]]

def raw5372step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-1, 2, 0, -1], ![1, -2, 0, 1]]

def raw5372step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def raw5373 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, 3, -3], ![1, -1, -2, 2], ![1, -1, 0, 0]]

def raw5373step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-1, 3, -2, 0], ![1, -3, 2, 0]]

def raw5373step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -2, 3, -1], ![0, 2, -3, 1], ![1, 1, 0, -2]]

def raw5374 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, 3, -3], ![1, -1, -1, 1], ![1, -1, -1, 1]]

def raw5375 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![1, -1, -2, 2], ![0, 0, 2, -2], ![1, -1, 1, -1]]

def raw5375step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![2, -1, 0, -1], ![-1, -2, 2, 1], ![1, 2, -2, -1]]

def raw5375step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![2, 1, -1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical168
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5376 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![1, -1, -2, 2], ![0, 0, 3, -3], ![1, -1, 0, 0]]

def raw5376step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![2, -1, 0, -1], ![-1, -2, 3, 0], ![1, 2, -3, 0]]

def raw5376step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -2, 3, -1], ![0, 2, -3, 1], ![1, 1, 0, -2]]

def raw5377 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

def raw5377step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]

def raw5377step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw5378 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -3, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw5378step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw5379 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -3, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw5379step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw5380 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -3, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw5380step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw5381 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -3, 3], ![1, -1, 0], ![1, 2, -3]]

def raw5381step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

def raw5382 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -3, 3], ![1, 0, -1], ![1, 1, -2]]

def raw5382step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

def raw5383 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw5383step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw5384 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1]]

def raw5384step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

def raw5385 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2]]

def raw5385step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -2, 0], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2]]

def raw5385step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

def raw5386 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -2, -2, 4], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw5386step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

def raw5387 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, -1, 2, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw5388 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, -1, 2, -1], ![2, 0, 1, -3]]

def raw5388step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -2, 0, 0], ![0, 1, 3, -4], ![0, 1, -2, 1], ![-2, 0, -1, 3]]

def raw5388step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 3, -4], ![2, -2, 0, 0]]

def raw5389 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw5390 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw5391 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def raw5392 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, -1, 2, -2]]

def raw5392step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def raw5393 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw5394 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, 0, 2, -2], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw5395 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, 0, 2, -2], ![2, -1, 1, -2]]

def raw5395step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![2, -1, 0, -1], ![0, -3, 2, 1], ![0, 4, -2, -2]]

def raw5395step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 2, -1, -1], ![2, 0, 1, -3]]

def raw5396 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw5396step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![0, -3, 0, 3], ![0, 4, 0, -4]]

def raw5396step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, -1, 0], ![0, 0, -3, 3], ![0, 0, 4, -4], ![1, -2, 0, 1]]

def raw5397 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![1, -1, 1, -1], ![1, 0, 2, -3]]

def raw5397step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![0, -3, 1, 2], ![0, 4, -1, -3]]

def raw5397step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-2, 1, 1, 0], ![0, 3, -1, -2], ![0, -4, 1, 3]]

def raw5397step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -2, 3], ![0, 1, 3, -4], ![2, -1, -1, 0]]

def raw5398 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![1, -1, 2, -2], ![1, 0, 1, -2]]

def raw5398step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![0, -3, 2, 1], ![0, 4, -2, -2]]

def raw5398step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -2, 1, 0], ![1, 0, 2, -3]]

def raw5399 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def raw5399step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![0, -3, 3, 0], ![0, 4, -3, -1]]

def raw5399step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 3, -3], ![0, 2, -1, -1], ![1, -2, 1, 0]]

def raw5400 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![1, 0, 2, -3], ![1, -1, 1, -1]]

def raw5400step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, 0, -1], ![0, -3, 2, 1], ![0, 4, -3, -1]]

def raw5400step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-2, 1, 0, 1], ![0, 3, -2, -1], ![0, -4, 3, 1]]

def raw5400step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -2, 3], ![0, 1, 3, -4], ![2, -1, -1, 0]]

def raw5401 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -2, 3], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw5401step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw5402 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -2, 3], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw5402step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw5403 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -2, 3], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw5403step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![0, -2, 0, 2], ![0, 3, 0, -3]]

def raw5403step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, -1, 0], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, -2, 0, 1]]

def raw5404 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -2, 3], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw5404step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![0, -2, 1, 1], ![0, 3, -1, -2]]

def raw5404step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def raw5405 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -2, 3], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def raw5405step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![0, -2, 2, 0], ![0, 3, -2, -1]]

def raw5405step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -2, 1, 0]]

def raw5406 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -2, 3], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw5406step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![0, -2, 3, -1], ![0, 3, -3, 0]]

def raw5406step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 3, -3], ![0, 2, -1, -1], ![1, -2, 0, 1]]

def raw5407 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical169
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5408 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -1, 2], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw5408step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![0, -1, 2, -1], ![0, 2, -2, 0]]

def raw5408step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw5409 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -1, 2], ![1, -1, 3, -3], ![1, 0, -2, 1]]

def raw5409step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![0, -1, 3, -2], ![0, 2, -3, 1]]

def raw5409step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 0, -2, 1], ![1, 2, 0, -3]]

def raw5410 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, 3, -2], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw5410step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, 0, 0, -2]]

def raw5411 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, 3, -2], ![1, -1, -2, 2], ![1, 0, -1, 0]]

def raw5411step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![0, 3, -2, -1], ![0, -2, 2, 0]]

def raw5411step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -2, 1, 0]]

def raw5412 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, 3, -2], ![1, -1, -1, 1], ![1, 0, -2, 1]]

def raw5412step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![0, 3, -1, -2], ![0, -2, 1, 1]]

def raw5412step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def raw5413 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, 3, -2], ![1, -1, 0, 0], ![1, 0, -3, 2]]

def raw5413step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![0, 3, 0, -3], ![0, -2, 0, 2]]

def raw5413step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, -1, 0], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, -2, 0, 1]]

def raw5414 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -3, 3], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw5415 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -3, 3], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw5415step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![0, -3, 0, 3], ![0, 3, 0, -3]]

def raw5415step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, 0, -1], ![0, 0, -3, 3], ![0, 0, 3, -3], ![1, -2, 0, 1]]

def raw5416 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -3, 3], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def raw5416step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![0, -3, 1, 2], ![0, 3, -1, -2]]

def raw5416step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, -3, 2], ![2, -1, 0, -1]]

def raw5417 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -2, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw5418 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -2, 2], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw5418step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![2, 0, 0, -1, -1], ![0, -2, 0, 0, 2], ![0, 2, 0, 0, -2]]

def raw5418step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![0, -2, 0, 2], ![0, 2, 0, -2]]

def raw5418step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw5419 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -2, 2], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, -1, 2, -2]]

def raw5420 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -2, 2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw5420step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw5421 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -2, 2], ![0, 0, 1, -1], ![2, -2, 1, -1]]

def raw5421step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![2, 0, 0, -2], ![0, -2, 1, 1], ![0, 2, -1, -1]]

def raw5421step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw5422 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw5422step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw5423 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -2, 2], ![0, 0, 2, -2], ![2, -2, 0, 0]]

def raw5423step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 2, -2, 0], ![2, 0, 0, -2]]

def raw5424 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -2, 2], ![1, -1, -1, 1], ![1, -1, 3, -3]]

def raw5424step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![0, -2, -1, 3], ![0, 2, 1, -3]]

def raw5424step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -2, 1], ![2, 1, 0, -3]]

def raw5425 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw5425step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![0, -2, 0, 2], ![0, 2, 0, -2]]

def raw5425step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw5426 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -2, 2], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def raw5426step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def raw5427 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -1, 1], ![0, -1, -1, 2], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw5427step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw5428 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -1, 1], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw5428step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -2, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw5429 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -2, 3, -2], ![1, 0, -1, 0]]

def raw5429step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw5430 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, -1, 3, -3]]

def raw5431 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw5431step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw5432 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 3, -3], ![1, -1, -1, 1]]

def raw5432step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, -1, 3, -3]]

def raw5433 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -1, 1], ![0, 0, 0, 0], ![1, -1, -1, 1], ![1, -1, 2, -2]]

def raw5433step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![2, 0, 0, -1, -1], ![0, -1, 0, -1, 2], ![0, 1, 0, 1, -2]]

def raw5433step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![0, -1, -1, 2], ![0, 1, 1, -2]]

def raw5433step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def raw5434 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, -2, 2], ![1, -1, 2, -2]]

def raw5435 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, -1, 1, -1]]

def raw5435step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw5436 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -1, 1], ![1, -1, -2, 2], ![1, -1, 3, -3]]

def raw5436step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![0, -1, -2, 3], ![0, 1, 2, -3]]

def raw5436step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 1, 1], ![0, 2, -1, -1], ![1, 0, 2, -3]]

def raw5437 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, -1, 2, -2]]

def raw5437step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![0, -1, -1, 2], ![0, 1, 1, -2]]

def raw5437step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def raw5438 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, 0, 0], ![1, -1, -2, 2], ![1, -1, 2, -2]]

def raw5438step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![0, 0, -2, 2], ![0, 0, 2, -2]]

def raw5438step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![2, -1, -1], ![0, -2, 2], ![0, 2, -2]]

def raw5438step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]

def raw5439 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, 1, -1], ![1, -1, -3, 3], ![1, -1, 2, -2]]

def raw5439step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![0, 1, -3, 2], ![0, -1, 3, -2]]

def raw5439step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 1, 1], ![0, 2, -1, -1], ![1, 0, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw544 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![3, -3, 0]]

def raw544step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]

def raw545 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]

def raw546 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1]]

def raw546step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]

def raw547 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]

def raw548 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]

def raw549 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]

def raw549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]

def raw549step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![2, -1, -1]]

def raw550 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]

def raw550step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]

def raw550step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

def raw551 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw551step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]

def raw551step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw552 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]

def raw552step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]

def raw552step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

def raw553 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

def raw553step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![2, -2, 0]]

def raw554 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]

def raw555 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![2, -3, 1], ![1, 1, -2]]

def raw555step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]

def raw556 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]

def raw556step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![2, -2, 0]]

def raw557 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]

def raw557step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -3, 3], ![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1]]

def raw557step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]

def raw558 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -3, 2], ![2, 0, -2]]

def raw558step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -3, 3], ![-1, 3, -2], ![-2, 0, 2]]

def raw558step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![3, -1, -2]]

def raw559 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

def raw559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -3, 3], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]

def raw559step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]

def raw560 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]

def raw561 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1]]

def raw561step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -3, 3], ![-1, 1, 0], ![-1, 2, -1], ![-1, 0, 1]]

def raw561step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]

def raw562 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]

def raw562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]

def raw563 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]

def raw563step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]

def raw564 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, 0, -1], ![2, -3, 1]]

def raw564step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -3, 3], ![-1, 0, 1], ![-2, 3, -1]]

def raw564step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![3, -2, -1]]

def raw565 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![3, -3, 0]]

def raw566 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def raw566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]

def raw567 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![0, 2, -2], ![2, 1, -3]]

def raw567step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]

def raw568 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def raw568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 3, -2], ![0, -3, 3], ![-1, 0, 1], ![-1, 0, 1]]

def raw568step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]

def raw569 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![0, 3, -3], ![2, 0, -2]]

def raw569step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 3, -2], ![0, -3, 3], ![-2, 0, 2]]

def raw569step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![3, -1, -2]]

def raw570 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![1, 0, -1], ![1, 3, -4]]

def raw570step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 3, -2], ![-1, 0, 1], ![-1, -3, 4]]

def raw570step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]

def raw571 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![1, 1, -2], ![1, 2, -3]]

def raw572 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![2, 3, -5]]

def raw572step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 3, -2], ![-2, -3, 5]]

def raw572step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![3, -1, -2]]

def raw573 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![0, 3, -3], ![2, -1, -1]]

def raw573step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]

def raw574 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, -1, 0], ![1, 3, -4]]

def raw574step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 2, -1], ![-1, 1, 0], ![-1, -3, 4]]

def raw574step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]

def raw575 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]

def raw575step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3]]

def raw575step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![2, -1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical170
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5440 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, 1, -1], ![1, -1, -2, 2], ![1, -1, 1, -1]]

def raw5440step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![0, 1, -2, 1], ![0, -1, 2, -1]]

def raw5440step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def raw5441 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, 2, -2], ![1, -1, -2, 2], ![1, -1, 0, 0]]

def raw5441step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![0, 2, -2, 0], ![0, -2, 2, 0]]

def raw5441step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw5442 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, -1, -1, 1]]

def raw5442step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def raw5443 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![1, -2, -3, 4], ![0, 0, 2, -2], ![1, 0, 1, -2]]

def raw5443step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![2, -2, 0, 0], ![0, -3, 2, 1], ![0, 4, -2, -2]]

def raw5443step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, 1, 0, -3]]

def raw5444 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![1, -1, -3, 3], ![0, -1, 2, -1], ![1, 0, 1, -2]]

def raw5444step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![2, -1, -1, 0], ![0, -3, 2, 1], ![0, 3, -1, -2]]

def raw5444step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 0, -2, 1], ![1, 2, 0, -3]]

def raw5445 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![1, -1, -3, 3], ![0, 0, 2, -2], ![1, -1, 1, -1]]

def raw5445step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![2, -1, 0, -1], ![0, -3, 2, 1], ![0, 3, -2, -1]]

def raw5445step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -2, 1], ![2, 1, 0, -3]]

def raw5446 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 1, -1], ![0, -1, -3, 4], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw5446step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -2, -1, 1], ![0, 1, 3, -4], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, -1, 2]]

def raw5446step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw5447 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 1, -1], ![0, -1, -3, 4], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw5447step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -2, -1, 1], ![0, 1, 3, -4], ![0, 0, -1, 1], ![-1, 1, -1, 1], ![-1, 0, 0, 1]]

def raw5447step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 0, 3, -4]]

def raw5448 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 1, -1], ![0, -1, -3, 4], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw5448step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![1, -3, 0, 2], ![-1, 4, 0, -3]]

def raw5448step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-2, 1, 1, 0], ![-1, 3, 0, -2], ![1, -4, 0, 3]]

def raw5448step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -2, -1, 3], ![0, 3, 1, -4], ![1, 0, -2, 1]]

def raw5449 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 1, -1], ![0, -1, -3, 4], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw5449step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![1, -3, 1, 1], ![-1, 4, -1, -2]]

def raw5449step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 1, -2, 0], ![1, 1, 1, -3]]

def raw5450 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 1, -1], ![0, -1, -3, 4], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def raw5450step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![1, -3, 2, 0], ![-1, 4, -2, -1]]

def raw5450step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, 1, -2, 0]]

def raw5451 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 1, -1], ![0, 0, -3, 3], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw5451step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![1, -3, 0, 2], ![-1, 3, 0, -2]]

def raw5451step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -2, 3, -1], ![0, 2, -3, 1], ![1, 1, 0, -2]]

def raw5452 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 1, -1], ![0, 0, -2, 2], ![1, -1, -1, 1], ![1, -1, 2, -2]]

def raw5452step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![1, -2, -1, 2], ![-1, 2, 1, -2]]

def raw5452step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![2, 1, -1, -2]]

def raw5453 : Matrix (Fin 2) (Fin 4) ℤ := ![![-2, 2, 2, -2], ![2, -2, -2, 2]]

def raw5453step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![2, -2], ![2, -2], ![-2, 2]]

def raw5453step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![2, -2]]

def raw5454 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 3, -3], ![0, -1, -3, 4], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw5454step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![3, -3, 0, 0], ![-3, 4, 0, -1]]

def raw5454step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-2, 1, 1, 0], ![-3, 3, 0, 0], ![3, -4, 0, 1]]

def raw5454step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -4, 3], ![1, 0, 1, -2]]

def raw5455 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 3, -3], ![0, -1, -2, 3], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw5455step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![3, -2, -1, 0], ![-3, 3, 1, -1]]

def raw5455step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-2, 1, 1, 0], ![-3, 2, 1, 0], ![3, -3, -1, 1]]

def raw5455step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 1, -2], ![0, 1, 2, -3], ![1, -1, -3, 3]]

def raw5456 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 3, -3], ![0, -1, -1, 2], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw5456step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -2, -3, 3], ![0, 1, 1, -2], ![0, 0, 2, -2], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw5456step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -3, 3], ![0, -1, 0, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw5457 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, 3, -3], ![0, -1, -1, 2], ![1, -1, -2, 2], ![1, 0, 0, -1]]

def raw5457step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![3, -1, -2, 0], ![-3, 2, 2, -1]]

def raw5457step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-2, 1, 1, 0], ![-3, 1, 2, 0], ![3, -2, -2, 1]]

def raw5457step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, 1, -2], ![0, 1, 2, -3], ![1, -2, -2, 3]]

def raw5458 : Matrix (Fin 2) (Fin 3) ℤ := ![![-2, 3, -1], ![2, -3, 1]]

def raw5458step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![3, -3], ![-1, 1]]

def raw5458step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw5459 : Matrix (Fin 2) (Fin 3) ℤ := ![![-2, 4, -2], ![2, -4, 2]]

def raw5459step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![4, -4], ![-2, 2]]

def raw5459step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![2, -2]]

def raw5460 : Matrix (Fin 2) (Fin 3) ℤ := ![![-2, 5, -3], ![2, -5, 3]]

def raw5460step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![5, -5], ![-3, 3]]

def raw5460step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![2, -2], ![3, -3]]

def raw5461 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -4, 5], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw5462 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -4, 5], ![-1, 2, -1], ![1, 0, -1], ![1, 2, -3]]

def raw5463 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -4, 5], ![-1, 2, -1], ![1, 1, -2], ![1, 1, -2]]

def raw5464 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -4, 5], ![-1, 2, -1], ![2, 2, -4]]

def raw5464step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 4, -5], ![1, -2, 1], ![-2, -2, 4]]

def raw5464step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![1, -2, 1], ![1, 4, -5]]

def raw5465 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -4, 5], ![-1, 3, -2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw5466 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -4, 5], ![-1, 3, -2], ![1, 0, -1], ![1, 1, -2]]

def raw5467 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -4, 5], ![-1, 3, -2], ![1, 1, -2], ![1, 0, -1]]

def raw5467step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -4, 5], ![-1, 3, -2], ![1, 0, -1], ![1, 1, -2]]

def raw5468 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -4, 5], ![-1, 3, -2], ![2, 1, -3]]

def raw5468step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 4, -5], ![1, -3, 2], ![-2, -1, 3]]

def raw5468step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -3, 2], ![1, 4, -5]]

def raw5469 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -4, 5], ![-1, 4, -3], ![1, 0, -1], ![1, 0, -1]]

def raw5470 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -4, 5], ![-1, 4, -3], ![2, 0, -2]]

def raw5470step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![-4, 4, 0], ![5, -3, -2]]

def raw5470step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 4, -4], ![2, -1, -1]]

def raw5471 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2]]

def raw5471step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -4, 5], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical171
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5472 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]

def raw5473 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

def raw5474 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![0, 2, -2]]

def raw5474step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

def raw5475 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 1, -1], ![0, 1, -1], ![1, 2, -3]]

def raw5476 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 1, -1], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1]]

def raw5476step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

def raw5477 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 1, -1], ![0, 2, -2], ![1, 1, -2]]

def raw5478 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 1, -1], ![0, 3, -3], ![1, 0, -1]]

def raw5479 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 1, -1], ![1, 3, -4]]

def raw5480 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 2, -2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw5480step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

def raw5481 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 2, -2], ![0, 1, -1], ![1, 1, -2]]

def raw5481step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 1, -1], ![0, 2, -2], ![1, 1, -2]]

def raw5482 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 2, -2], ![0, 2, -2], ![1, 0, -1]]

def raw5483 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 2, -2], ![1, 2, -3]]

def raw5484 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 3, -3], ![1, 1, -2]]

def raw5485 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 4, -4], ![1, 0, -1]]

def raw5486 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -4, 5], ![1, 2, -3], ![0, 2, -2]]

def raw5486step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 2, -2], ![1, 2, -3]]

def raw5487step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![4, -4]]

def raw5488 : Matrix (Fin 2) (Fin 4) ℤ := ![![-1, -3, 3, 1], ![1, 3, -3, -1]]

def raw5488step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-3, 3], ![3, -3], ![1, -1]]

def raw5488step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]

def raw5489 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 0, 1], ![1, 1, -2], ![1, 2, -3]]

def raw5490 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw5491 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw5492 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3]]

def raw5493 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2]]

def raw5494 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw5495 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw5496 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw5497 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![0, 2, -2], ![2, -1, -1]]

def raw5497step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -2, 1], ![0, -2, 2], ![-2, 1, 1]]

def raw5497step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -2, 1], ![1, 3, -4]]

def raw5498 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 2, -3]]

def raw5499 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2]]

def raw5500 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, 1, -2], ![1, 0, -1]]

def raw5500step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2]]

def raw5501 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![2, 1, -3]]

def raw5501step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![1, -2, 1], ![-2, -1, 3]]

def raw5501step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -2, 1], ![1, 3, -4]]

def raw5502 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]

def raw5502step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1]]

def raw5503 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical172
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5504 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]

def raw5504step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw5505 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![1, -1, 0], ![1, 1, -2]]

def raw5506 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1]]

def raw5507 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![2, 0, -2]]

def raw5507step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![4, -2, -2]]

def raw5507step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, -1, -1]]

def raw5508 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 4, -3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

def raw5509 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 4, -3], ![1, -1, 0], ![1, 0, -1]]

def raw5510 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 4, -3], ![1, 0, -1], ![1, -1, 0]]

def raw5510step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 4, -3], ![1, -1, 0], ![1, 0, -1]]

def raw5511 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 4, -3], ![2, -1, -1]]

def raw5511step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![1, -4, 3], ![-2, 1, 1]]

def raw5511step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -4, 3], ![1, 3, -4]]

def raw5512 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 2, -3]]

def raw5513 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, -1, 1], ![0, 1, -1], ![0, 3, -3], ![1, 0, -1]]

def raw5514 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, -1, 1], ![0, 2, -2], ![1, 2, -3]]

def raw5515 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, -1, 1], ![0, 4, -4], ![1, 0, -1]]

def raw5516 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, -1, 1], ![1, 1, -2], ![0, 3, -3]]

def raw5516step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, -1, 1], ![0, 3, -3], ![1, 1, -2]]

def raw5517 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 0, 0], ![0, 1, -1], ![1, 2, -3]]

def raw5517step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![1, 2, -3]]

def raw5518 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 0, 0], ![0, 3, -3], ![1, 0, -1]]

def raw5518step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 3, -3], ![1, 0, -1]]

def raw5519 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 0, 0], ![1, 3, -4]]

def raw5519step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 0, 3], ![4, 0, -4]]

def raw5519step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-3, 3], ![4, -4]]

def raw5519step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]

def raw5520 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw5520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw5521 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

def raw5521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw5522 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1]]

def raw5522step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw5523 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1]]

def raw5523step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw5524 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3]]

def raw5524step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![1, 2, -3]]

def raw5525 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2]]

def raw5525step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]

def raw5526 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw5527 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def raw5528 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![0, 2, -2]]

def raw5528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def raw5529 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1]]

def raw5529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw5530 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]

def raw5531 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1]]

def raw5531step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

def raw5532 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0]]

def raw5532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def raw5533 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![0, 1, -1]]

def raw5533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def raw5534 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

def raw5535 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![0, 0, 0]]

def raw5535step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical173
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5536 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0]]

def raw5537 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![1, -1, 0], ![0, 3, -3]]

def raw5537step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0]]

def raw5538 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![1, 0, -1], ![0, 2, -2]]

def raw5538step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

def raw5539 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![1, 1, -2], ![0, 1, -1]]

def raw5539step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]

def raw5540 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![1, 2, -3]]

def raw5541 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2]]

def raw5541step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![1, 1, -2]]

def raw5542 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw5542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def raw5543 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1]]

def raw5543step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

def raw5544 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0]]

def raw5545 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![1, -1, 0], ![0, 2, -2]]

def raw5545step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0]]

def raw5546 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![1, 0, -1], ![0, 1, -1]]

def raw5546step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

def raw5547 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![1, 1, -2]]

def raw5548 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1]]

def raw5548step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 3, -3], ![1, 0, -1]]

def raw5549 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 3, -3], ![1, -1, 0], ![0, 1, -1]]

def raw5549step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0]]

def raw5550 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 3, -3], ![1, 0, -1]]

def raw5551 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 3, -3], ![1, 0, -1], ![0, 0, 0]]

def raw5551step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 3, -3], ![1, 0, -1]]

def raw5552 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 4, -4], ![1, -1, 0]]

def raw5553 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![1, -1, 0], ![0, 4, -4]]

def raw5553step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 4, -4], ![1, -1, 0]]

def raw5554 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![1, 0, -1], ![0, 3, -3]]

def raw5554step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 3, -3], ![1, 0, -1]]

def raw5555 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![1, 1, -2], ![0, 2, -2]]

def raw5555step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![1, 1, -2]]

def raw5556 : Matrix (Fin 2) (Fin 3) ℤ := ![![-1, -3, 4], ![1, 3, -4]]

def raw5556step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-3, 3], ![4, -4]]

def raw5556step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]

def raw5557 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw5558 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 2, 0, -3]]

def raw5558step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 0, 2], ![-2, 1, 1, 0], ![5, -1, -1, -3]]

def raw5558step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -3, 5], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def raw5559 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw5559step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, 0, -2]]

def raw5560 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw5561 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, 1, -3]]

def raw5561step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![-2, 1, 0, 1], ![5, -1, -1, -3]]

def raw5561step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -3, 5], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw5562 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 1, 1, -2], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw5562step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw5563 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, 0, -2]]

def raw5564 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw5565 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw5565step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 2, 0], ![-2, 1, 1, 0], ![5, -1, -3, -1]]

def raw5565step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -3, 5], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw5566 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 2, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw5566step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw5567 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 1, 0, -2]]

def raw5567step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical174
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5568 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw5569 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 2, -2], ![1, 2, 0, -3]]

def raw5569step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-2, 2, 0], ![5, -2, -3]]

def raw5569step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

def raw5570 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw5570step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, 0, -2]]

def raw5571 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def raw5571step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![-2, 0, 2, 0], ![5, -1, -3, -1]]

def raw5571step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -3, 5], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw5572 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw5573 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 1, 1, -2], ![1, 1, 1, -3]]

def raw5573step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1], ![5, -2, -3]]

def raw5573step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

def raw5574 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 1, 2, -3], ![1, 1, 0, -2]]

def raw5574step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-2, 2, 0], ![5, -3, -2]]

def raw5574step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def raw5575 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 2, 0, -2], ![1, 0, 2, -3]]

def raw5575step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2], ![5, -2, -3]]

def raw5575step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

def raw5576 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 2, 1, -3], ![1, 0, 1, -2]]

def raw5576step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1], ![5, -3, -2]]

def raw5576step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def raw5577 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![1, 0, 2, -3], ![0, 2, 0, -2]]

def raw5577step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![-2, 2, 0], ![5, -3, -2]]

def raw5577step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

def raw5578 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![1, 1, 1, -3], ![0, 1, 1, -2]]

def raw5578step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![-2, 1, 1], ![5, -3, -2]]

def raw5578step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

def raw5579 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 2, 0, -3]]

def raw5580 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 0, 0], ![0, 0, 1, -1], ![1, 2, 0, -3]]

def raw5580step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 0, 2], ![-1, 0, 1, 0], ![4, 0, -1, -3]]

def raw5580step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 1, 0], ![4, -1, -3]]

def raw5580step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

def raw5581 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 0, 0], ![1, 2, 0, -3]]

def raw5581step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 0, 2], ![-1, 1, 0, 0], ![4, -1, 0, -3]]

def raw5581step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 1, 0], ![4, -1, -3]]

def raw5581step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

def raw5582 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def raw5583 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw5584 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def raw5585 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw5586 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw5587 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 2, -1, -2]]

def raw5587step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 0, 2], ![-1, 1, 1, -1], ![4, -1, -1, -2]]

def raw5587step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, 1, -1, -1]]

def raw5588 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def raw5589 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw5590 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw5591 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, 2, -2, -1]]

def raw5592 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw5593 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw5594 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 1, 1, -3]]

def raw5594step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![-1, 1, -1, 1], ![4, -1, 0, -3]]

def raw5594step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw5595 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw5595step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw5596 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, 0, -2]]

def raw5596step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw5597 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw5598 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, 2, -3], ![1, 1, -2, 0]]

def raw5599 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical175
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5600 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw5601 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw5601step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw5602 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw5602step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 2, 0], ![-1, 1, 1, -1], ![4, -1, -3, 0]]

def raw5602step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 1, -1]]

def raw5603 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![1, 2, 0, -3]]

def raw5603step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 1, 0], ![4, -1, -3]]

def raw5603step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

def raw5604 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def raw5604step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def raw5605 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw5605step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw5606 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw5606step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw5607 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 0, 1, -1], ![1, 2, -2, -1]]

def raw5607step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, 2, -2, -1]]

def raw5608 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw5609 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

def raw5610 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def raw5610step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![-1, 2, 0, -1], ![4, -2, -1, -1]]

def raw5610step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw5611 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw5612 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def raw5613 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw5614 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw5615 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![1, 2, -1, -2]]

def raw5615step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 2, -1], ![4, -2, -2]]

def raw5615step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def raw5616 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def raw5617 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw5618 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 3, -3], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw5619 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 3, -3], ![1, 2, -2, -1]]

def raw5619step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 3, -2], ![4, -3, -1]]

def raw5619step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]

def raw5620 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 3, -4]]

def raw5620step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![-1, -1, -1, 3], ![4, 0, 0, -4]]

def raw5620step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 4, -4], ![1, 1, -2, 0]]

def raw5621 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def raw5621step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![-1, -1, 0, 2], ![4, 0, -1, -3]]

def raw5621step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![2, -1, -1, 0], ![1, 1, 0, -2], ![-4, 0, 1, 3]]

def raw5621step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, 0, 3, -4]]

def raw5622 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw5623 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def raw5623step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![-1, -1, 2, 0], ![4, 0, -3, -1]]

def raw5623step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw5624 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def raw5624step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![-1, -1, 3, -1], ![4, 0, -4, 0]]

def raw5624step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 4, -4], ![0, 1, -2, 1], ![1, 0, -1, 0]]

def raw5625 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw5625step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 1, 0, -2]]

def raw5626 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw5626step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw5627 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw5627step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![-1, 0, 2, -1], ![4, -1, -3, 0]]

def raw5627step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw5628 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, 0, -1], ![1, 1, 1, -3]]

def raw5628step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1], ![4, -1, -3]]

def raw5628step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]

def raw5629 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, 1, -2], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw5629step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw5630 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw5631 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, 1, -2], ![1, 1, 0, -2]]

def raw5631step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 1, 0], ![4, -2, -2]]

def raw5631step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical176
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5632 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, 2, -3], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw5632step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![-1, 2, 0, -1], ![4, -3, -1, 0]]

def raw5632step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw5633 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, 2, -3], ![1, 1, -1, -1]]

def raw5633step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 2, -1], ![4, -3, -1]]

def raw5633step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2]]

def raw5634 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, 3, -4], ![1, 1, -2, 0]]

def raw5634step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 3, -2], ![4, -4, 0]]

def raw5634step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 4, -4], ![1, -2, 1], ![1, -1, 0]]

def raw5635 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 2, -2, 0], ![1, 0, 3, -4]]

def raw5635step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![-1, -2, 3], ![4, 0, -4]]

def raw5635step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 4, -4], ![2, -2, 0]]

def raw5636 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 2, -1, -1], ![1, 0, 2, -3]]

def raw5636step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![-1, -1, 2], ![4, -1, -3]]

def raw5636step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![2, -2, 0], ![1, 1, -2], ![-4, 1, 3]]

def raw5636step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -2, 1], ![1, 3, -4]]

def raw5637 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw5637step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![-1, 0, 1], ![4, -2, -2]]

def raw5637step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw5638 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw5638step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![-1, 1, 0], ![4, -3, -1]]

def raw5638step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

def raw5639 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![1, 0, 1, -2], ![0, 2, 0, -2]]

def raw5639step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![-1, 1, 0], ![4, -2, -2]]

def raw5639step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw5640 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![1, 0, 2, -3], ![0, 2, -1, -1]]

def raw5640step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![-1, 2, -1], ![4, -3, -1]]

def raw5640step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![2, 0, -2], ![1, -2, 1], ![-4, 3, 1]]

def raw5640step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -2, 1], ![1, 3, -4]]

def raw5641 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![1, 0, 3, -4], ![0, 2, -2, 0]]

def raw5641step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![-1, 3, -2], ![4, -4, 0]]

def raw5641step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 4, -4], ![2, -2, 0]]

def raw5642 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![1, 1, 0, -2], ![0, 1, 1, -2]]

def raw5642step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![-1, 0, 1], ![4, -2, -2]]

def raw5642step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw5643 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 2, 0, -3]]

def raw5644 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 0, 1, -1], ![1, 2, 1, -4]]

def raw5644step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 2, 0, -3], ![0, 0, 2, -2], ![0, 0, -1, 1], ![-1, -2, -1, 4]]

def raw5644step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 2, 0, -3]]

def raw5645 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 2, 0, -3]]

def raw5646 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 1, 2, -4]]

def raw5646step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 2, 0, -3], ![0, 0, 2, -2], ![0, -1, 0, 1], ![-1, -1, -2, 4]]

def raw5646step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, 2, -3]]

def raw5647 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, 1, 0, -2]]

def raw5648 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 2, -3]]

def raw5649 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, 0, 0, -1]]

def raw5650 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![1, 2, 2, -5]]

def raw5650step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, -2, 2], ![3, 2, -5]]

def raw5650step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![2, 0, -2], ![0, 2, -2], ![-3, -2, 5]]

def raw5650step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

def raw5651 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 0, 1, -1], ![1, 2, 0, -3]]

def raw5651step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 2, 0, -3]]

def raw5651step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 0, 1], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def raw5652 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![1, 2, 0, -3]]

def raw5652step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 2, 0, -3]]

def raw5652step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 0, 1], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def raw5653 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 2, -1, -2]]

def raw5654 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw5654step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw5655 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 2, 0, -3]]

def raw5655step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 0, 1], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def raw5656 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 3, -4]]

def raw5657 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def raw5658 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def raw5659 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 1, 2, -4]]

def raw5659step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![0, -1, -1, 2], ![3, 1, 0, -4]]

def raw5659step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, 0, 3, -4]]

def raw5660 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 1, 1, -3]]

def raw5660step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 2, 0, -3], ![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, -1, -1, 3]]

def raw5660step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def raw5661 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw5661step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 2, 0, -3], ![0, 0, 1, -1], ![0, -2, 0, 2], ![-1, 0, -1, 2]]

def raw5661step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def raw5662 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw5662step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 0, 1], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def raw5663 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw5663step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 2, 0], ![0, -1, 2, -1], ![3, 1, -4, 0]]

def raw5663step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, 0, 3, -4]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical177
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5664 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw5664step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw5664step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 0, 0]]

def raw5665 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 0, 0], ![0, 0, 1, -1], ![1, 2, -1, -2]]

def raw5665step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 0, 2], ![0, 0, 1, -1], ![3, 0, -1, -2]]

def raw5665step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![3, -1, -2]]

def raw5665step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def raw5666 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 0, 0], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw5666step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 2, 0], ![0, 0, -1, 1], ![3, 0, -1, -2]]

def raw5666step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![3, -1, -2]]

def raw5666step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw5667 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 0, 0], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw5667step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 2, 0], ![0, 0, 1, -1], ![3, 0, -3, 0]]

def raw5667step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, 1, -1], ![3, -3, 0]]

def raw5667step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0]]

def raw5668 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw5668step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw5668step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 0, 0]]

def raw5669 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 0, 0, 0], ![1, 2, -1, -2]]

def raw5669step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 0, 2], ![0, 1, 0, -1], ![3, -1, 0, -2]]

def raw5669step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![3, -1, -2]]

def raw5669step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def raw5670 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def raw5671 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw5672 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw5673 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw5674 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 2, -2, -1]]

def raw5674step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 0, 2], ![0, 1, 1, -2], ![3, -1, -1, -1]]

def raw5674step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, 1, -2, 0]]

def raw5675 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw5676 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw5676step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw5677 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 1, 0, -2]]

def raw5677step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw5678 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw5678step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw5679 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw5679step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0]]

def raw5680 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def raw5680step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![0, 1, 0, -1], ![3, -1, -1, -1]]

def raw5680step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw5681 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw5682 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def raw5683 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw5683step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 2, 0], ![0, 1, -1, 0], ![3, -1, -1, -1]]

def raw5683step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw5684 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw5684step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 0, 0]]

def raw5685 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw5686 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![1, 2, -1, -2]]

def raw5686step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![3, -1, -2]]

def raw5686step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def raw5687 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def raw5688 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw5689 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw5690 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, -1, -1]]

def raw5691 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def raw5691step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![0, 2, 0, -2], ![3, -2, -1, 0]]

def raw5691step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def raw5692 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw5693 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw5694 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw5695 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![1, 2, -2, -1]]

def raw5695step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 2, -2], ![3, -2, -1]]

def raw5695step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical178
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5696 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 3, -3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def raw5697 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, 1, -2, 0]]

def raw5698 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, 0, -1, 0]]

def raw5699 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 3, -3], ![1, 2, -3, 0]]

def raw5699step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 3, -3], ![3, -3, 0]]

def raw5699step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]

def raw5700 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, 0, 3, -4]]

def raw5700step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![0, -2, -1, 3], ![3, 1, 0, -4]]

def raw5700step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, 1, -2, 0]]

def raw5701 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def raw5701step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 2, 0, -3], ![0, -1, 2, -1], ![0, -1, 0, 1], ![-1, 0, -2, 3]]

def raw5701step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 2, -3]]

def raw5702 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw5703 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def raw5704 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def raw5705 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -2, 1], ![1, 1, 2, -4]]

def raw5705step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2], ![3, 1, -4]]

def raw5705step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -2, 1], ![1, 3, -4]]

def raw5706 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -1, 0], ![0, 1, -2, 1], ![1, 0, 3, -4]]

def raw5706step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![0, -1, -2, 3], ![3, 0, 1, -4]]

def raw5706step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, 1, -2, 0]]

def raw5707 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def raw5707step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![0, -1, -1, 2], ![3, 0, 0, -3]]

def raw5707step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 3, -3], ![1, 1, -2, 0]]

def raw5708 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw5708step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 2, 0, -3], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 0, -1, 2]]

def raw5708step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def raw5709 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw5709step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw5710 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw5710step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![0, -1, 2, -1], ![3, 0, -3, 0]]

def raw5710step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, -1, 0]]

def raw5711 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -2, 1]]

def raw5712 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -1, 0], ![1, 1, 1, -3]]

def raw5712step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![3, 0, -3]]

def raw5712step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![2, -1, -1], ![0, 1, -1], ![-3, 0, 3]]

def raw5712step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

def raw5713 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw5713step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 2, 0, -3], ![0, -1, 0, 1], ![0, -1, 1, 0], ![-1, 0, -1, 2]]

def raw5713step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def raw5714 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw5714step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![0, 0, 1, -1], ![3, -1, -2, 0]]

def raw5714step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw5715 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, -2, 1]]

def raw5716 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 1, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw5716step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw5717 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 1, -2], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw5717step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![0, 1, 0, -1], ![3, -2, -1, 0]]

def raw5717step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw5718 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw5718step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![3, -2, -1]]

def raw5718step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw5719 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 2, -3], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw5719step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def raw5720 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 2, -3], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def raw5720step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![0, 2, -1, -1], ![3, -3, 0, 0]]

def raw5720step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, -1, 0]]

def raw5721 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 2, -3], ![0, 1, 0, -1], ![1, 0, -2, 1]]

def raw5721step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, -2, 1]]

def raw5722 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 2, -3], ![1, 1, -2, 0]]

def raw5722step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 2, -2], ![3, -3, 0]]

def raw5722step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

def raw5723 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 3, -4], ![1, 1, -3, 1]]

def raw5723step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 3, -3], ![3, -4, 1]]

def raw5723step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![2, -1, -1], ![0, -3, 3], ![-3, 4, -1]]

def raw5723step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]

def raw5724 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 2, -2, 0], ![1, 0, 2, -3]]

def raw5724step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -2, 2], ![3, 0, -3]]

def raw5724step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![2, -2, 0]]

def raw5725 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw5725step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![3, -1, -2]]

def raw5725step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw5726 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw5726step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, 1, -1], ![3, -3, 0]]

def raw5726step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0]]

def raw5727 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw5727step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, 2, -2], ![3, -4, 1]]

def raw5727step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical179
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5728 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![1, 0, -2, 1], ![0, 2, 2, -4]]

def raw5728step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2], ![3, 1, -4]]

def raw5728step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

def raw5729 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![1, 0, 1, -2], ![0, 2, -1, -1]]

def raw5729step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 1, -1], ![3, -2, -1]]

def raw5729step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw5730 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![1, 0, 2, -3], ![0, 2, -2, 0]]

def raw5730step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 2, -2], ![3, -3, 0]]

def raw5730step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![2, -2, 0]]

def raw5731 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![1, 1, -3, 1], ![0, 1, 3, -4]]

def raw5731step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3], ![3, 1, -4]]

def raw5731step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![2, -1, -1], ![0, 3, -3], ![-3, -1, 4]]

def raw5731step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]

def raw5732 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![1, 1, -2, 0], ![0, 1, 2, -3]]

def raw5732step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2], ![3, 0, -3]]

def raw5732step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

def raw5733 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw5734 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 0, 1, -1], ![1, 2, 0, -3]]

def raw5734step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 2, -1, -2], ![0, 0, 2, -2], ![0, 0, -1, 1], ![-1, -2, 0, 3]]

def raw5734step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 2, -1, -2]]

def raw5735 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, 1, 2, -4]]

def raw5736 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 1, 1, -3]]

def raw5737 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 1, 0, -2]]

def raw5738 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw5739 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw5740 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw5741 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![1, 2, 1, -4]]

def raw5741step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![1, -2, 1], ![2, 2, -4]]

def raw5741step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![2, 0, -2], ![-1, 2, -1], ![-2, -2, 4]]

def raw5741step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def raw5742 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw5743 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw5744 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw5744step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 2, -1, -2], ![0, 0, 1, -1], ![0, 0, 0, 0], ![0, -2, 0, 2], ![-1, 0, 0, 1]]

def raw5744step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 2, -1, -2], ![0, 0, 1, -1], ![0, -2, 0, 2], ![-1, 0, 0, 1]]

def raw5744step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 2, -2]]

def raw5745 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw5746 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw5747 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, 1, 2, -4]]

def raw5748 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def raw5749 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw5750 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw5751 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 1, 1, -3]]

def raw5751step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![1, -1, -1, 1], ![2, 1, 0, -3]]

def raw5751step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, 0, 2, -3]]

def raw5752 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 1, 0, -2]]

def raw5752step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 2, -1, -2], ![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, -1, 0, 2]]

def raw5752step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 2, -2]]

def raw5753 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw5754 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw5754step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 2, -1, -2], ![0, 0, 1, -1], ![0, -2, 0, 2], ![-1, 0, 0, 1]]

def raw5754step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 2, -2]]

def raw5755 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw5755step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 2, 0], ![1, -1, 1, -1], ![2, 1, -3, 0]]

def raw5755step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def raw5756 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw5756step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 2, 0], ![1, -1, 2, -2], ![2, 1, -4, 1]]

def raw5756step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, 1, 2, -4]]

def raw5757 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 0, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw5757step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-1, 0, 0, 0, 1], ![-2, 0, 1, 1, 0], ![1, 0, -1, 0, 0], ![2, 0, 0, -1, -1]]

def raw5757step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![1, -1, 0, 0], ![2, 0, -1, -1]]

def raw5757step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw5758 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def raw5758step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![1, 0, 0, -1], ![2, 0, -1, -1]]

def raw5758step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1]]

def raw5758step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

def raw5759 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 0, 0], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw5759step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 2, 0], ![1, 0, -1, 0], ![2, 0, -1, -1]]

def raw5759step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1]]

def raw5759step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw576 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]

def raw576step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]

def raw577 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![2, 2, -4]]

def raw577step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 2, -1], ![-2, -2, 4]]

def raw577step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, -1, -1]]

def raw578 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

def raw578step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]

def raw578step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw579 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![1, -2, 1], ![1, 1, -2]]

def raw579step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]

def raw581 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![1, -3, 2], ![1, 1, -2]]

def raw581step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![1, 1, -2], ![1, 2, -3]]

def raw582 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![2, -2, 0]]

def raw582step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, -2, 3], ![-2, 2, 0]]

def raw582step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![2, -2, 0]]

def raw583 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 3, -4], ![2, -3, 1]]

def raw583step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, -3, 4], ![-2, 3, -1]]

def raw583step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![3, -2, -1]]

def raw584 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 3, 0], ![-1, 2, -2, 1], ![4, -2, -1, -1]]

def raw584step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![3, -2, -1], ![0, 1, -1]]

def raw584step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]

def raw585 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 3, 0], ![0, 2, -1, -1], ![3, -2, -2, 1]]

def raw585step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -1, -2], ![0, -1, 1]]

def raw585step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 1, 2], ![0, 1, -1]]

def raw585step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

def raw586 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 3, 0], ![1, -2, -1, 2], ![2, 2, -2, -2]]

def raw586step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![3, -1, -2], ![0, 2, -2]]

def raw586step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]

def raw587 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 3, 0], ![1, 2, -1, -2], ![2, -2, -2, 2]]

def raw587step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -1, -2], ![0, -2, 2]]

def raw587step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]

def raw588 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 3, 0], ![2, -2, -1, 1], ![1, 2, -2, -1]]

def raw588step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![3, -1, -2], ![0, 1, -1]]

def raw588step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]

def raw589 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 1, 1, 1], ![-1, -2, 1, 2], ![4, 1, -2, -3]]

def raw589step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]

def raw590 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 1, 1, 1], ![-1, -2, 2, 1], ![4, 1, -3, -2]]

def raw590step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 2, -3], ![1, 1, -2]]

def raw590step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]

def raw591 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 1, 1, 1], ![-1, 1, 2, -2], ![4, -2, -3, 1]]

def raw591step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 1, -2], ![1, 2, -3], ![1, -2, 1]]

def raw591step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]

def raw592 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 1, 1, 1], ![0, -2, 1, 1], ![3, 1, -2, -2]]

def raw592step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]

def raw592step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]

def raw593 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 1, 1, 1], ![0, 1, 1, -2], ![3, -2, -2, 1]]

def raw593step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]

def raw593step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]

def raw594 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 1, 1, 1], ![1, -2, 1, 0], ![2, 1, -2, -1]]

def raw594step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]

def raw594step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

def raw595 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 1, 1, 1], ![1, -2, 3, -2], ![2, 1, -4, 1]]

def raw595step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 3, -4], ![1, -2, 1]]

def raw595step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -2, 1], ![1, 3, -4]]

def raw596 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 1, 1, 1], ![2, -2, 1, -1], ![1, 1, -2, 0]]

def raw596step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 1, -2], ![1, -1, 0]]

def raw596step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

def raw597 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]

def raw597step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]

def raw597step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

def raw600 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]

def raw600step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 2, -3]]

def raw601 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]

def raw601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![1, 2, -3]]

def raw603 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]

def raw603step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 1, -2], ![1, 2, -3]]

def raw604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]

def raw604step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]

def raw604step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]

def raw605 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical180
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5760 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 0, 0], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw5760step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 2, 0], ![1, 0, 0, -1], ![2, 0, -2, 0]]

def raw5760step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0]]

def raw5760step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

def raw5761 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, 0, 0, -1]]

def raw5762 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw5763 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw5764 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw5765 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 1, -1, -1]]

def raw5765step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![1, 1, -1, -1], ![2, -1, 0, -1]]

def raw5765step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![2, 0, -1, -1], ![-1, -1, 1, 1], ![-2, 1, 0, 1]]

def raw5765step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw5766 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def raw5766step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![1, 1, 0, -2], ![2, -1, -1, 0]]

def raw5766step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 1, -2]]

def raw5767 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, 0, 1, -2]]

def raw5768 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw5768step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 2, 0], ![1, 1, -2, 0], ![2, -1, 0, -1]]

def raw5768step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw5769 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw5769step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 2, 0], ![1, 1, -1, -1], ![2, -1, -1, 0]]

def raw5769step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1]]

def raw5770 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw5771 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 1, -1, -1]]

def raw5772 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 2, -2], ![0, 2, -3, 1], ![1, 0, 0, -1]]

def raw5773 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, 0, -1, 0]]

def raw5773step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw5774 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 2, -2], ![1, 2, -3, 0]]

def raw5774step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![1, 2, -3], ![2, -2, 0]]

def raw5774step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![2, 0, -2], ![-1, -2, 3], ![-2, 2, 0]]

def raw5774step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def raw5775 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -3, 2], ![1, 1, 2, -4]]

def raw5775step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2], ![2, 2, -4]]

def raw5775step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]

def raw5776 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def raw5776step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![1, -2, -1, 2], ![2, 1, 0, -3]]

def raw5776step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 1, -2, 0]]

def raw5777 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw5778 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw5779 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw5780 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -2, 1], ![1, 1, 1, -3]]

def raw5780step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1], ![2, 1, -3]]

def raw5780step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

def raw5781 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -1, 0], ![0, 1, -2, 1], ![1, 0, 2, -3]]

def raw5781step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![1, -1, -2, 2], ![2, 0, 1, -3]]

def raw5781step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 1, -2, 0]]

def raw5782 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw5782step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![1, -1, -1, 1], ![2, 0, 0, -2]]

def raw5782step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![2, -1, -1, 0], ![-1, 1, 1, -1], ![-2, 0, 0, 2]]

def raw5782step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, -1, -1]]

def raw5783 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw5783step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![1, -1, 0, 0], ![2, 0, -1, -1]]

def raw5783step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw5784 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw5784step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![1, -1, 1, -1], ![2, 0, -2, 0]]

def raw5784step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw5785 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -2, 1]]

def raw5786 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

def raw5786step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, -1, 0], ![2, 0, -2]]

def raw5786step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![2, -1, -1], ![-1, 1, 0], ![-2, 0, 2]]

def raw5786step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

def raw5787 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw5787step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![1, 0, -1, 0], ![2, -1, 0, -1]]

def raw5787step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw5788 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw5788step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![1, 0, 0, -1], ![2, -1, -1, 0]]

def raw5788step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 1, 0, -2]]

def raw5789 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -2, 1]]

def raw5789step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![1, 0, 1, -2], ![2, -1, -2, 1]]

def raw5789step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def raw5790 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def raw5790step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1]]

def raw5790step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

def raw5791 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, 1, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw5791step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical181
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5792 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, 1, -2], ![0, 1, 0, -1], ![1, 0, -2, 1]]

def raw5792step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![1, 1, 0, -2], ![2, -2, -1, 1]]

def raw5792step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def raw5793 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw5793step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0]]

def raw5793step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw5794 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, 2, -3], ![0, 1, -2, 1], ![1, 0, -1, 0]]

def raw5794step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw5795 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, 2, -3], ![1, 1, -3, 1]]

def raw5795step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, 2, -3], ![2, -3, 1]]

def raw5795step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

def raw5796 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 2, -3, 1], ![1, 0, 2, -3]]

def raw5796step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![1, -3, 2], ![2, 1, -3]]

def raw5796step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]

def raw5797 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def raw5797step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![1, -2, 1], ![2, 0, -2]]

def raw5797step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![2, -2, 0], ![-1, 2, -1], ![-2, 0, 2]]

def raw5797step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

def raw5798 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw5798step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1]]

def raw5798step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

def raw5799 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw5799step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0]]

def raw5799step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

def raw5800 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw5800step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![1, 1, -2], ![2, -3, 1]]

def raw5800step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

def raw5801 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 2, 2, -4], ![1, 0, -3, 2]]

def raw5801step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![1, 2, -3], ![2, -4, 2]]

def raw5801step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]

def raw5802 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![1, 0, -3, 2], ![0, 2, 2, -4]]

def raw5802step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2], ![2, 2, -4]]

def raw5802step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]

def raw5803 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![1, 0, -2, 1], ![0, 2, 1, -3]]

def raw5803step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![1, -2, 1], ![2, 1, -3]]

def raw5803step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

def raw5804 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![1, 0, 2, -3], ![0, 2, -3, 1]]

def raw5804step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![1, 2, -3], ![2, -3, 1]]

def raw5804step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]

def raw5805 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![1, 1, -3, 1], ![0, 1, 2, -3]]

def raw5805step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![1, -3, 2], ![2, 1, -3]]

def raw5805step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

def raw5806 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![1, 1, -2, 0], ![0, 1, 1, -2]]

def raw5806step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![1, -2, 1], ![2, 0, -2]]

def raw5806step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw5807 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![-3, 1, 0, 2], ![4, 1, -2, -3]]

def raw5807step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-2, 1, 1], ![2, 0, -2], ![1, 2, -3]]

def raw5807step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]

def raw5808 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![-3, 2, -1, 2], ![4, 0, -1, -3]]

def raw5808step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-2, 2, 0], ![2, -1, -1], ![1, 2, -3]]

def raw5808step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![1, -3, 2], ![2, -1, -1]]

def raw5809 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![-3, 2, 0, 1], ![4, 0, -2, -2]]

def raw5809step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-2, 2, 0], ![2, 0, -2], ![1, 1, -2]]

def raw5809step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

def raw5810 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![-3, 3, -1, 1], ![4, -1, -1, -2]]

def raw5810step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-2, 3, -1], ![2, -1, -1], ![1, 1, -2]]

def raw5810step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 4, -3], ![1, -2, 1], ![2, -1, -1]]

def raw5811 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![-2, 1, -1, 2], ![3, 1, -1, -3]]

def raw5811step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-2, 1, 1], ![2, -1, -1], ![1, 2, -3]]

def raw5811step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![2, 1, -3]]

def raw5812 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![-2, 1, 2, -1], ![3, 1, -4, 0]]

def raw5812step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-2, 1, 1], ![2, 2, -4], ![1, -1, 0]]

def raw5812step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-2, -2, 4], ![-1, 1, 0]]

def raw5812step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]

def raw5813 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![-2, 2, -1, 1], ![3, 0, -1, -2]]

def raw5813step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-2, 2, 0], ![2, -1, -1], ![1, 1, -2]]

def raw5813step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]

def raw5813step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

def raw5814 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![-2, 2, 1, -1], ![3, 0, -3, 0]]

def raw5814step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-2, 2, 0], ![2, 1, -3], ![1, -1, 0]]

def raw5814step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]

def raw5815 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![-2, 2, 2, -2], ![3, 0, -4, 1]]

def raw5815step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-2, 2, 0], ![2, 2, -4], ![1, -2, 1]]

def raw5815step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, -2, 4], ![-1, 2, -1]]

def raw5815step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 2, -3], ![2, -2, 0]]

def raw5816 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![-2, 4, 0, -2], ![3, -2, -2, 1]]

def raw5816step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-2, 4, -2], ![2, 0, -2], ![1, -2, 1]]

def raw5816step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![1, 1, -2], ![2, -2, 0]]

def raw5817 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![-1, 0, 3, -2], ![2, 2, -5, 1]]

def raw5817step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 0, 2], ![2, 3, -5], ![1, -2, 1]]

def raw5817step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-2, -3, 5], ![-1, 2, -1]]

def raw5817step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

def raw5818 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![-1, 1, 2, -2], ![2, 1, -4, 1]]

def raw5818step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 1, 1], ![2, 2, -4], ![1, -2, 1]]

def raw5818step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-2, -2, 4], ![-1, 2, -1]]

def raw5818step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]

def raw5819 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![-1, 2, 1, -2], ![2, 0, -3, 1]]

def raw5819step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![2, 1, -3], ![1, -2, 1]]

def raw5819step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

def raw5820 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![-1, 3, -3, 1], ![2, -1, 1, -2]]

def raw5820step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![2, -3, 1], ![1, 1, -2]]

def raw5820step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![2, 1, -3]]

def raw5821 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, -1, 2, -1], ![1, 3, -4, 0]]

def raw5821step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, -1, 3], ![2, 2, -4], ![1, -1, 0]]

def raw5821step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![2, 1, -3], ![-2, -2, 4], ![-1, 1, 0]]

def raw5821step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw5822 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 1, 0, -2]]

def raw5823 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical182
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5824 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -2, 2], ![1, 2, 0, -3]]

def raw5824step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![2, -2, 0], ![1, 2, -3]]

def raw5824step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![2, 0, -2], ![-2, 2, 0], ![-1, -2, 3]]

def raw5824step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def raw5825 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw5826 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw5826step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, 0, 0, -1]]

def raw5827 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw5827step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw5828 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 1, 0, -2]]

def raw5828step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![2, -1, -1, 0], ![1, 1, 0, -2]]

def raw5828step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 1, -2]]

def raw5829 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw5829step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw5830 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def raw5830step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![2, -1, 0, -1], ![1, 1, -1, -1]]

def raw5830step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![2, 0, -1, -1], ![-2, 1, 0, 1], ![-1, -1, 1, 1]]

def raw5830step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw5831 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw5831step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 2, 0], ![2, -1, -1, 0], ![1, 1, -1, -1]]

def raw5831step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1]]

def raw5832 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw5832step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 2, 0], ![2, -1, 0, -1], ![1, 1, -2, 0]]

def raw5832step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw5833 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, 1, -1], ![0, 1, -3, 2], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw5833step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw5834 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, 0, 0, -1]]

def raw5834step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 2, 0], ![2, 1, -3, 0], ![1, -1, 1, -1]]

def raw5834step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def raw5835 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, 2, -2], ![1, 2, -4, 1]]

def raw5835step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![2, 2, -4], ![1, -2, 1]]

def raw5835step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![2, 0, -2], ![-2, -2, 4], ![-1, 2, -1]]

def raw5835step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def raw5836 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw5836step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![2, -2, 0, 0], ![1, 1, -1, -1]]

def raw5836step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw5837 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def raw5837step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![2, -2, 0], ![1, 1, -2]]

def raw5837step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw5838 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw5838step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![2, -1, -1, 0], ![1, 0, 0, -1]]

def raw5838step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 1, 0, -2]]

def raw5839 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw5839step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![2, -1, 0, -1], ![1, 0, -1, 0]]

def raw5839step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw5840 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1]]

def raw5840step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![2, 0, 0, -2], ![1, -1, -1, 1]]

def raw5840step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![2, -1, -1, 0], ![-2, 0, 0, 2], ![-1, 1, 1, -1]]

def raw5840step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, -1, -1]]

def raw5841 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 1, 2, -3], ![1, 1, -4, 2]]

def raw5841step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![2, 2, -4], ![1, -3, 2]]

def raw5841step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]

def raw5842 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 2, -3, 1], ![1, 0, 1, -2]]

def raw5842step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![2, -3, 1], ![1, 1, -2]]

def raw5842step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

def raw5843 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw5843step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![2, 0, -2], ![1, -2, 1]]

def raw5843step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![2, -2, 0], ![-2, 0, 2], ![-1, 2, -1]]

def raw5843step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

def raw5844 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 3, -3, 0], ![1, -1, 1, -1]]

def raw5844step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 3, -1], ![2, -3, 1], ![1, 0, -1]]

def raw5844step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3]]

def raw5845 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![1, -1, 2, -2], ![0, 3, -4, 1]]

def raw5845step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![2, 2, -4], ![1, -2, 1]]

def raw5845step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![2, 1, -3], ![-2, -2, 4], ![-1, 2, -1]]

def raw5845step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]

def raw5846 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![1, 0, -2, 1], ![0, 2, 0, -2]]

def raw5846step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![2, -2, 0], ![1, 1, -2]]

def raw5846step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![2, 0, -2], ![-2, 2, 0], ![-1, -1, 2]]

def raw5846step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

def raw5847 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![1, 0, 2, -3], ![0, 2, -4, 2]]

def raw5847step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![2, 2, -4], ![1, -3, 2]]

def raw5847step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]

def raw5848 : Matrix (Fin 2) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![1, 2, -2, -1]]

def raw5848step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]

def raw5848step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw5849 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![2, -1, 1, -2], ![-1, 3, -3, 1]]

def raw5849step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-2, -1, 3], ![2, 1, -3], ![1, -2, 1]]

def raw5849step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![2, 1, -3]]

def raw5850 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![2, 0, 0, -2], ![-1, 2, -2, 1]]

def raw5850step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-2, 0, 2], ![2, 0, -2], ![1, -2, 1]]

def raw5850step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]

def raw5851 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![2, 0, 1, -3], ![-1, 2, -3, 2]]

def raw5851step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-2, 0, 2], ![2, 1, -3], ![1, -3, 2]]

def raw5851step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]

def raw5852 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 3, -4]]

def raw5852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, -3, 4]]

def raw5852step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 2, -3]]

def raw5853 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

def raw5854 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

def raw5855 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical183
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5856 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def raw5857 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 2, -2], ![2, 1, -3]]

def raw5857step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, -2, 2], ![-2, -1, 3]]

def raw5857step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 1, -2], ![1, 2, -3]]

def raw5858 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![1, 1, -2]]

def raw5859 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def raw5860 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 3, -3], ![2, 0, -2]]

def raw5860step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, -3, 3], ![-2, 0, 2]]

def raw5860step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 1, -2], ![1, 2, -3]]

def raw5861 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 4, -4], ![1, -1, 0], ![1, 0, -1]]

def raw5862 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 4, -4], ![2, -1, -1]]

def raw5862step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, -4, 4], ![-2, 1, 1]]

def raw5862step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -4, 4], ![1, 1, -2], ![1, 2, -3]]

def raw5863 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 3, -4]]

def raw5863step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![-1, 0, 1], ![-1, -3, 4]]

def raw5863step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 0, 1], ![1, 1, -2], ![1, 2, -3]]

def raw5864 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![1, 1, -2], ![1, 2, -3]]

def raw5865 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![1, 2, -3], ![1, 1, -2]]

def raw5865step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![1, 1, -2], ![1, 2, -3]]

def raw5866 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![1, 3, -4], ![1, 0, -1]]

def raw5866step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![-1, -3, 4], ![-1, 0, 1]]

def raw5866step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 0, 1], ![1, 1, -2], ![1, 2, -3]]

def raw5867 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw5868 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw5868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw5869 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw5869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw5870 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw5871 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3]]

def raw5871step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![2, 1, -3]]

def raw5872 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2]]

def raw5872step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]

def raw5873 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw5874 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw5874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw5875 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw5876 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw5876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -3, 3], ![-1, 1, 0], ![-1, 1, 0]]

def raw5876step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

def raw5877 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3]]

def raw5878 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw5878step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw5879 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]

def raw5879step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

def raw5880 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]

def raw5880step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1]]

def raw5880step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw5881 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw5882 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw5883 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]

def raw5883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw5884 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

def raw5885 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

def raw5885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]

def raw5886 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, 2, -2], ![2, -2, 0]]

def raw5886step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -2, 1], ![0, -2, 2], ![-2, 2, 0]]

def raw5886step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

def raw5887 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical184
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5888 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

def raw5889 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1]]

def raw5889step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw5890 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, 2, -3], ![1, -2, 1]]

def raw5890step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 2, -3]]

def raw5891 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![2, 0, -2]]

def raw5891step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]

def raw5892 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]

def raw5893 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]

def raw5893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]

def raw5894 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![0, -2, 2], ![2, 1, -3]]

def raw5894step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -3, 2], ![0, 2, -2], ![-2, -1, 3]]

def raw5894step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -3, 2], ![1, 2, -3]]

def raw5895 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

def raw5896 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]

def raw5896step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1]]

def raw5897 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

def raw5897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]

def raw5898 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]

def raw5898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

def raw5899 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![1, -2, 1], ![1, 1, -2]]

def raw5900 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1]]

def raw5901 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![1, 0, -1], ![1, -1, 0]]

def raw5901step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1]]

def raw5902 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![2, -1, -1]]

def raw5902step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![1, -3, 2], ![-2, 1, 1]]

def raw5902step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -3, 2], ![1, 2, -3]]

def raw5903 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 4, -3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]

def raw5904 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 4, -3], ![0, -2, 2], ![2, 0, -2]]

def raw5904step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -4, 3], ![0, 2, -2], ![-2, 0, 2]]

def raw5904step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -4, 3], ![1, 2, -3]]

def raw5905 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 4, -3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]

def raw5905step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw5906 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 4, -3], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]

def raw5906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw5907 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 4, -3], ![1, -2, 1], ![1, 0, -1]]

def raw5907step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![1, -1, 0], ![1, 1, -2]]

def raw5908 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 4, -3], ![1, -1, 0], ![1, -1, 0]]

def raw5908step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1]]

def raw5909 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 4, -3], ![2, -2, 0]]

def raw5909step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 4, -2], ![3, -3, 0]]

def raw5909step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, -1, -1]]

def raw5910 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 2, -3]]

def raw5911 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -2, 2], ![0, 1, -1], ![0, 3, -3], ![1, 0, -1]]

def raw5912 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -2, 2], ![0, 1, -1], ![1, 3, -4]]

def raw5912step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 2, -2], ![0, -1, 1], ![-1, -3, 4]]

def raw5912step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, -1, 1], ![0, 2, -2], ![1, 2, -3]]

def raw5913 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -2, 2], ![0, 2, -2], ![1, 2, -3]]

def raw5914 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -2, 2], ![0, 3, -3], ![1, 1, -2]]

def raw5915 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -2, 2], ![0, 4, -4], ![1, 0, -1]]

def raw5916 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -2, 2], ![1, 4, -5]]

def raw5916step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![0, 2, -2], ![-1, -4, 5]]

def raw5916step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 2, -2], ![1, 2, -3]]

def raw5917 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3]]

def raw5917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]

def raw5917step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw5918 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2]]

def raw5918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]

def raw5919 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 2, -3]]

def raw5919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, -2, 3]]

def raw5919step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical185
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5920 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2]]

def raw5920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]

def raw5921 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1]]

def raw5921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

def raw5922 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![-1, 4, -3], ![1, -1, 0], ![1, 0, -1]]

def raw5922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw5923 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, -1, 1], ![0, 4, -4], ![1, 0, -1]]

def raw5924 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 2, -3]]

def raw5924step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3]]

def raw5925 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 0, 0], ![0, 3, -3], ![1, 0, -1]]

def raw5925step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1]]

def raw5926 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3]]

def raw5926step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3]]

def raw5927 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]

def raw5928 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

def raw5929 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0]]

def raw5930 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 3, -3]]

def raw5930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0]]

def raw5931 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![0, 2, -2]]

def raw5931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

def raw5932 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![0, 1, -1]]

def raw5932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]

def raw5933 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3]]

def raw5934 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2]]

def raw5934step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2]]

def raw5935 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1]]

def raw5935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

def raw5936 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![0, 1, -1]]

def raw5936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

def raw5937 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2]]

def raw5938 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1]]

def raw5938step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1]]

def raw5939 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![0, 1, -1]]

def raw5939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0]]

def raw5940 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1]]

def raw5941 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![0, 0, 0]]

def raw5941step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1]]

def raw5942 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0]]

def raw5943 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![1, 1, -2], ![0, 2, -2]]

def raw5943step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2]]

def raw5944 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw5944step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw5945 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def raw5945step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def raw5946 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2]]

def raw5946step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![1, 1, -2]]

def raw5947 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1]]

def raw5947step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![1, 0, -1]]

def raw5948 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 0, 0], ![0, 3, -3], ![1, -1, 0]]

def raw5948step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 3, -3], ![1, -1, 0]]

def raw5949 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 0, 0], ![1, 2, -3]]

def raw5949step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![3, 0, -3]]

def raw5949step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![3, -3]]

def raw5949step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw5950 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2]]

def raw5950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw5951 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1]]

def raw5951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical186
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5952 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0]]

def raw5952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

def raw5953 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3]]

def raw5953step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3]]

def raw5954 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1]]

def raw5954step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw5955 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0]]

def raw5955step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def raw5956 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2]]

def raw5956step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![1, 1, -2]]

def raw5957 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2]]

def raw5957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]

def raw5958 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1]]

def raw5958step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw5959 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw5960 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1]]

def raw5961 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1]]

def raw5961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw5962 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw5963 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1]]

def raw5963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

def raw5964 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1]]

def raw5964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1]]

def raw5965 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def raw5966 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0]]

def raw5966step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def raw5967 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0]]

def raw5967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0]]

def raw5968 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 3, -3], ![1, -2, 1]]

def raw5969 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![0, -1, 1]]

def raw5969step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0]]

def raw5970 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![1, -2, 1], ![0, 3, -3]]

def raw5970step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 3, -3], ![1, -2, 1]]

def raw5971 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![0, 2, -2]]

def raw5971step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def raw5972 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![1, 1, -2]]

def raw5973 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2]]

def raw5973step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2]]

def raw5974 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1]]

def raw5974step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![1, 0, -1]]

def raw5975 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1]]

def raw5975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1]]

def raw5976 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0]]

def raw5976step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def raw5977 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1]]

def raw5978 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![1, -1, 0], ![0, 1, -1]]

def raw5978step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def raw5979 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![1, 0, -1]]

def raw5980 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 3, -3], ![0, -2, 2], ![1, 1, -2]]

def raw5980step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -2, 2], ![0, 3, -3], ![1, 1, -2]]

def raw5981 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1]]

def raw5981step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1]]

def raw5982 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 3, -3], ![1, -1, 0]]

def raw5983 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 3, -3], ![1, -1, 0], ![0, 0, 0]]

def raw5983step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 3, -3], ![1, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical187
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5984 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 4, -4], ![0, -2, 2], ![1, 0, -1]]

def raw5984step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -2, 2], ![0, 4, -4], ![1, 0, -1]]

def raw5985 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 4, -4], ![0, -1, 1], ![1, -1, 0]]

def raw5985step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0]]

def raw5986 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 4, -4], ![1, -2, 1]]

def raw5987 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 4, -4], ![1, -1, 0], ![0, -1, 1]]

def raw5987step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0]]

def raw5988 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![1, -2, 1], ![0, 4, -4]]

def raw5988step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 4, -4], ![1, -2, 1]]

def raw5989 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![1, -1, 0], ![0, 3, -3]]

def raw5989step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 3, -3], ![1, -1, 0]]

def raw5990 : Matrix (Fin 2) (Fin 3) ℤ := ![![-1, -2, 3], ![1, 2, -3]]

def raw5990step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![3, -3]]

def raw5990step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw5991 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 3, 0], ![-2, 2, 1, -1], ![3, 0, -4, 1]]

def raw5991step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-2, 2, 0], ![3, 1, -4], ![0, -1, 1]]

def raw5991step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-3, -1, 4], ![0, 1, -1]]

def raw5991step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]

def raw5992 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 3, 0], ![-1, 2, 1, -2], ![2, 0, -4, 2]]

def raw5992step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![3, 1, -4], ![0, -2, 2]]

def raw5992step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![2, -2, 0], ![-3, -1, 4], ![0, 2, -2]]

def raw5992step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

def raw5993 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 3, 0], ![-1, 3, -1, -1], ![2, -1, -2, 1]]

def raw5993step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![3, -1, -2], ![0, -1, 1]]

def raw5993step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![2, -3, 1], ![-3, 1, 2], ![0, 1, -1]]

def raw5993step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

def raw5994 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 3, 0], ![0, 1, -3, 2], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw5994step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![3, -3, 0, 0], ![0, 2, -1, -1]]

def raw5994step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, -1, 0]]

def raw5995 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 3, 0], ![0, 3, -1, -2], ![1, -1, -2, 2]]

def raw5995step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 3, -1], ![3, -1, -2], ![0, -2, 2]]

def raw5995step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![2, -3, 1], ![-3, 1, 2], ![0, 2, -2]]

def raw5995step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]

def raw5996 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 3, 0], ![1, -1, 1, -1], ![0, 3, -4, 1]]

def raw5996step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![3, 1, -4], ![0, -1, 1]]

def raw5996step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![2, 1, -3], ![-3, -1, 4], ![0, 1, -1]]

def raw5996step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3]]

def raw5997 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 3, 0], ![2, -1, 1, -2], ![-1, 3, -4, 2]]

def raw5997step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-2, -1, 3], ![3, 1, -4], ![0, -2, 2]]

def raw5997step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![2, 1, -3], ![-3, -1, 4], ![0, 2, -2]]

def raw5997step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]

def raw5998 : Matrix (Fin 2) (Fin 4) ℤ := ![![-1, -2, 5, -2], ![1, 2, -5, 2]]

def raw5998step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![5, -5], ![-2, 2]]

def raw5998step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![2, -2], ![2, -2]]

def raw5999 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -3, 5], ![0, 0, 2, -2], ![1, 1, 1, -3]]

def raw5999step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1], ![5, -2, -3]]

def raw5999step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]

def raw6000 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -3, 5], ![0, 0, 3, -3], ![1, 1, 0, -2]]

def raw6000step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0], ![5, -3, -2]]

def raw6000step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def raw6001 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -3, 5], ![0, 1, 1, -2], ![1, 0, 2, -3]]

def raw6001step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-3, 1, 2], ![5, -2, -3]]

def raw6001step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

def raw6002 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -3, 5], ![0, 1, 2, -3], ![1, 0, 1, -2]]

def raw6002step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-3, 2, 1], ![5, -3, -2]]

def raw6002step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

def raw6003 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, -1, 2, 0], ![0, 1, -1, 0], ![1, 0, 1, -2], ![1, 1, 0, -2]]

def raw6004 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, -1, 2, 0], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw6005 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, -1, 2, 0], ![1, 0, 1, -2], ![1, 2, -1, -2]]

def raw6005step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 2, -4], ![1, 1, -2, 0], ![-1, 0, -1, 2], ![-1, -2, 1, 2]]

def raw6005step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 1, -2, 0], ![1, 1, 2, -4]]

def raw6006 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, -1, 2, 0], ![1, 1, 0, -2], ![1, 1, 0, -2]]

def raw6006step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, -1, 1, 1], ![-2, 2, 0, 0], ![4, 0, -2, -2]]

def raw6006step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def raw6007 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, -1, 2, 0], ![1, 1, 1, -3], ![1, 1, -1, -1]]

def raw6007step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, -1, 1, 1], ![-2, 2, 1, -1], ![4, 0, -3, -1]]

def raw6007step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![1, 1, -1, -1], ![2, -2, -1, 1], ![-4, 0, 3, 1]]

def raw6007step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, -1, 1]]

def raw6008 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 0, 1, 0], ![1, 0, 1, -2], ![1, 1, 0, -2]]

def raw6008step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw6009 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 0, 2, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw6010 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 0, 2, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw6010step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw6011 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 0, 2, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw6011step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw6012 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 0, 3, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw6013 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 0, 3, -2], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw6013step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 3, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw6014 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 0, 3, -2], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw6014step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 2, -4], ![1, 0, -3, 2], ![0, -2, 1, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw6014step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, -3, 2], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw6015 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 0, 3, -2], ![1, -1, 0, 0], ![1, 2, -1, -2]]

def raw6015step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 0, -1, 2], ![-2, 3, 0, -1], ![4, -2, 0, -2]]

def raw6015step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![1, 0, 1, -2], ![2, -3, 0, 1], ![-4, 2, 0, 2]]

def raw6015step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -3, 2], ![0, 2, 2, -4], ![1, -2, 0, 1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical188
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6016 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 0, 3, -2], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw6016step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def raw6017 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 1, 0, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw6017step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def raw6018 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 1, 1, -1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw6019 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 1, 1, -1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw6020 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 1, 1, -1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def raw6020step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw6021 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 1, 1, -1], ![1, -1, 2, -2], ![1, 1, -1, -1]]

def raw6022 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 1, 1, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw6022step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw6023 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 1, 1, -1], ![1, 0, 2, -3], ![1, 0, -1, 0]]

def raw6023step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 1, -1]]

def raw6024 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 1, 2, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw6024step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -1, -2]]

def raw6025 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 1, 2, -2], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw6025step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 1, 1, -1], ![1, -1, 2, -2], ![1, 1, -1, -1]]

def raw6026 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 1, 3, -3], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw6026step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 1, -1, 1], ![-2, 3, 0, -1], ![4, -3, 0, -1]]

def raw6026step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![1, -1, 1, -1], ![2, -3, 0, 1], ![-4, 3, 0, 1]]

def raw6026step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -4, 3], ![0, 1, 2, -3], ![1, -1, 1, -1]]

def raw6027 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 2, 0, -1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw6027step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def raw6028 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 2, 1, -2], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw6028step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 2, -1, 0], ![-2, 1, 2, -1], ![4, -2, -2, 0]]

def raw6028step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![1, -2, 1, 0], ![2, -1, -2, 1], ![-4, 2, 2, 0]]

def raw6028step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -2, 1], ![0, 2, 2, -4], ![1, -2, -1, 2]]

def raw6029 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![1, 0, 1, -2], ![1, 1, 0, -2]]

def raw6029step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw6030 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![-1, 1, 1, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw6030step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 0, 1, 0], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw6031 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw6031step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw6032 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def raw6032step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

def raw6033 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2], ![0, 1, 1, -2]]

def raw6033step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw6034 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 0, 2, -2], ![1, 1, -1, -1]]

def raw6034step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def raw6035 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2], ![0, 1, 0, -1]]

def raw6035step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 1, 0, -2]]

def raw6036 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw6036step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

def raw6037 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def raw6038 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw6039 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw6040 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw6041 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 1, 0, -2]]

def raw6041step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw6042 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw6043 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw6044 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw6044step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw6045 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw6046 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![1, 2, 0, -3]]

def raw6046step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0], ![4, -1, -3]]

def raw6046step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 1, -2], ![2, -2, 0], ![-4, 1, 3]]

def raw6046step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -2, 1], ![1, 3, -4]]

def raw6047 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical189
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6048 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def raw6049 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw6050 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 3, -2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw6051 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 3, -2], ![1, 2, -1, -2]]

def raw6051step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-2, 3, -1], ![4, -2, -2]]

def raw6051step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 1, -2], ![2, -3, 1], ![-4, 2, 2]]

def raw6051step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]

def raw6052 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 0, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw6052step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 1, 0], ![-2, 0, 1, 1], ![4, 0, -2, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical190
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6083 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![1, 1, 1, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end


