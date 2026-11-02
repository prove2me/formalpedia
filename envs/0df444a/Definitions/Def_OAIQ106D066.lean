-- Prove2me | Definitions.Def_OAIQ106D066
-- name    : OAIQ106D066
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T12:30:01.357495+00:00
-- url     : https://prove2.me/theorems/9997be2c-9eed-4f51-bfbe-09530c99bf49
-- title:
--   Definitions bundle OAIQ106D066 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1776 declarations of OpenAI's Lean: 1776 definitions. The definitions and types are `OAI.MUB6.Certificate.PairSemantics.raw8897step2`, `OAI.MUB6.Certificate.PairSemantics.raw8898`, `OAI.MUB6.Certificate.PairSemantics.raw8898step0`, `OAI.MUB6.Certificate.PairSemantics.raw8898step1`, `OAI.MUB6.Certificate.PairSemantics.raw8898step2`, `OAI.MUB6.Certificate.PairSemantics.raw8899`, `OAI.MUB6.Certificate.PairSemantics.raw8899step0`, `OAI.MUB6.Certificate.PairSemantics.raw8899step1`, `OAI.MUB6.Certificate.PairSemantics.raw8899step2`, `OAI.MUB6.Certificate.PairSemantics.raw889step1`, `OAI.MUB6.Certificate.PairSemantics.raw889step2`, `OAI.MUB6.Certificate.PairSemantics.raw88step0`, `OAI.MUB6.Certificate.PairSemantics.raw89`, `OAI.MUB6.Certificate.PairSemantics.raw890`, `OAI.MUB6.Certificate.PairSemantics.raw8900`, `OAI.MUB6.Certificate.PairSemantics.raw8900step0`, `OAI.MUB6.Certificate.PairSemantics.raw8900step1`, `OAI.MUB6.Certificate.PairSemantics.raw8900step2`, `OAI.MUB6.Certificate.PairSemantics.raw8901`, `OAI.MUB6.Certificate.PairSemantics.raw8901step0`, `OAI.MUB6.Certificate.PairSemantics.raw8901step1`, `OAI.MUB6.Certificate.PairSemantics.raw8901step2`, `OAI.MUB6.Certificate.PairSemantics.raw8902`, `OAI.MUB6.Certificate.PairSemantics.raw8902step0`, `OAI.MUB6.Certificate.PairSemantics.raw8902step1`, `OAI.MUB6.Certificate.PairSemantics.raw8902step2`, `OAI.MUB6.Certificate.PairSemantics.raw8903`, `OAI.MUB6.Certificate.PairSemantics.raw8903step0`, `OAI.MUB6.Certificate.PairSemantics.raw8903step1`, `OAI.MUB6.Certificate.PairSemantics.raw8903step2`, `OAI.MUB6.Certificate.PairSemantics.raw8904`, `OAI.MUB6.Certificate.PairSemantics.raw8904step0`, `OAI.MUB6.Certificate.PairSemantics.raw8904step1`, `OAI.MUB6.Certificate.PairSemantics.raw8904step2`, `OAI.MUB6.Certificate.PairSemantics.raw8905`, `OAI.MUB6.Certificate.PairSemantics.raw8905step0`, `OAI.MUB6.Certificate.PairSemantics.raw8906`, `OAI.MUB6.Certificate.PairSemantics.raw8906step0`, `OAI.MUB6.Certificate.PairSemantics.raw8906step1`, `OAI.MUB6.Certificate.PairSemantics.raw8906step2` and 1736 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_PairSemantics_Canonical0`, `MutuallyUnbiased_PairSemantics_Canonical2`, `MutuallyUnbiased_PairSemantics_Canonical27`, `MutuallyUnbiased_PairSemantics_Canonical278`, `MutuallyUnbiased_PairSemantics_Canonical279`, `MutuallyUnbiased_PairSemantics_Canonical28`, `MutuallyUnbiased_PairSemantics_Canonical280`, `MutuallyUnbiased_PairSemantics_Canonical281`, `MutuallyUnbiased_PairSemantics_Canonical282`, `MutuallyUnbiased_PairSemantics_Canonical283`, `MutuallyUnbiased_PairSemantics_Canonical284`, `MutuallyUnbiased_PairSemantics_Canonical285`, `MutuallyUnbiased_PairSemantics_Canonical286`, `MutuallyUnbiased_PairSemantics_Canonical287`, `MutuallyUnbiased_PairSemantics_Canonical288`, `MutuallyUnbiased_PairSemantics_Canonical289`, `MutuallyUnbiased_PairSemantics_Canonical29`, `MutuallyUnbiased_PairSemantics_Canonical290`, `MutuallyUnbiased_PairSemantics_Canonical291`, `MutuallyUnbiased_PairSemantics_Canonical292`, `MutuallyUnbiased_PairSemantics_Canonical293`, `MutuallyUnbiased_PairSemantics_Canonical294`, `MutuallyUnbiased_PairSemantics_Canonical295`, `MutuallyUnbiased_PairSemantics_Canonical296`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the statement `OAI.MUB6.Certificate.PairSemantics.canonical9056`; the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1161`, `OAI.MUB6.Certificate.MixedSemantics.sound1162`, `OAI.MUB6.Certificate.MixedSemantics.sound1163`, `OAI.MUB6.Certificate.MixedSemantics.sound1164`, `OAI.MUB6.Certificate.MixedSemantics.sound1165`, `OAI.MUB6.Certificate.MixedSemantics.sound1166`, `OAI.MUB6.Certificate.MixedSemantics.sound1168`, `OAI.MUB6.Certificate.MixedSemantics.sound1170`, `OAI.MUB6.Certificate.MixedSemantics.sound1172`, `OAI.MUB6.Certificate.MixedSemantics.sound1173`, `OAI.MUB6.Certificate.MixedSemantics.sound1175`, `OAI.MUB6.Certificate.MixedSemantics.sound1265`, `OAI.MUB6.Certificate.MixedSemantics.sound1266`, `OAI.MUB6.Certificate.MixedSemantics.sound1267`, `OAI.MUB6.Certificate.MixedSemantics.sound1271`, `OAI.MUB6.Certificate.MixedSemantics.sound1298`, `OAI.MUB6.Certificate.MixedSemantics.sound1299`, `OAI.MUB6.Certificate.MixedSemantics.sound1301`, `OAI.MUB6.Certificate.MixedSemantics.sound1339`, `OAI.MUB6.Certificate.MixedSemantics.sound1340`, `OAI.MUB6.Certificate.MixedSemantics.sound1341`, `OAI.MUB6.Certificate.MixedSemantics.sound1342`, `OAI.MUB6.Certificate.MixedSemantics.sound1343`, `OAI.MUB6.Certificate.MixedSemantics.sound1344`, `OAI.MUB6.Certificate.MixedSemantics.sound1346`, `OAI.MUB6.Certificate.MixedSemantics.sound1395`, `OAI.MUB6.Certificate.MixedSemantics.sound1396`, `OAI.MUB6.Certificate.MixedSemantics.sound1397`, `OAI.MUB6.Certificate.MixedSemantics.sound1399`, `OAI.MUB6.Certificate.MixedSemantics.sound1401`, `OAI.MUB6.Certificate.MixedSemantics.sound1409`, `OAI.MUB6.Certificate.MixedSemantics.sound1410`, `OAI.MUB6.Certificate.MixedSemantics.sound1411`, `OAI.MUB6.Certificate.MixedSemantics.sound1412`, `OAI.MUB6.Certificate.MixedSemantics.sound1413`, `OAI.MUB6.Certificate.MixedSemantics.sound1414`, `OAI.MUB6.Certificate.MixedSemantics.sound1416`, `OAI.MUB6.Certificate.MixedSemantics.sound1417`, `OAI.MUB6.Certificate.MixedSemantics.sound1427`, `OAI.MUB6.Certificate.MixedSemantics.sound1441`, `OAI.MUB6.Certificate.MixedSemantics.sound1443`, `OAI.MUB6.Certificate.MixedSemantics.sound1451`, `OAI.MUB6.Certificate.MixedSemantics.sound1475`, `OAI.MUB6.Certificate.MixedSemantics.sound1477`, `OAI.MUB6.Certificate.MixedSemantics.sound1478`, `OAI.MUB6.Certificate.MixedSemantics.sound1479`, `OAI.MUB6.Certificate.MixedSemantics.sound1480`, `OAI.MUB6.Certificate.MixedSemantics.sound171`, `OAI.MUB6.Certificate.MixedSemantics.sound174`, `OAI.MUB6.Certificate.MixedSemantics.sound206`, `OAI.MUB6.Certificate.MixedSemantics.sound207`, `OAI.MUB6.Certificate.MixedSemantics.sound2357`, `OAI.MUB6.Certificate.MixedSemantics.sound2358`, `OAI.MUB6.Certificate.MixedSemantics.sound2359`, `OAI.MUB6.Certificate.MixedSemantics.sound2527`, `OAI.MUB6.Certificate.MixedSemantics.sound2530`, `OAI.MUB6.Certificate.MixedSemantics.sound2531`, `OAI.MUB6.Certificate.MixedSemantics.sound2532`, `OAI.MUB6.Certificate.MixedSemantics.sound2570`, `OAI.MUB6.Certificate.MixedSemantics.sound2572`, `OAI.MUB6.Certificate.MixedSemantics.sound2574`, `OAI.MUB6.Certificate.MixedSemantics.sound2576`, `OAI.MUB6.Certificate.MixedSemantics.sound2593`, `OAI.MUB6.Certificate.MixedSemantics.sound2594`, `OAI.MUB6.Certificate.MixedSemantics.sound2595`, `OAI.MUB6.Certificate.MixedSemantics.sound2596`, `OAI.MUB6.Certificate.MixedSemantics.sound2598`, `OAI.MUB6.Certificate.MixedSemantics.sound2599`, `OAI.MUB6.Certificate.MixedSemantics.sound2601`, `OAI.MUB6.Certificate.MixedSemantics.sound2636`, `OAI.MUB6.Certificate.MixedSemantics.sound2637`, `OAI.MUB6.Certificate.MixedSemantics.sound2638`, `OAI.MUB6.Certificate.MixedSemantics.sound2640`, `OAI.MUB6.Certificate.MixedSemantics.sound2753`, `OAI.MUB6.Certificate.MixedSemantics.sound2766`, `OAI.MUB6.Certificate.MixedSemantics.sound2828`, `OAI.MUB6.Certificate.MixedSemantics.sound2904`, `OAI.MUB6.Certificate.MixedSemantics.sound293`, `OAI.MUB6.Certificate.MixedSemantics.sound2936`, `OAI.MUB6.Certificate.MixedSemantics.sound2937`, `OAI.MUB6.Certificate.MixedSemantics.sound2939`, `OAI.MUB6.Certificate.MixedSemantics.sound294`, `OAI.MUB6.Certificate.MixedSemantics.sound2941`, `OAI.MUB6.Certificate.MixedSemantics.sound2943`, `OAI.MUB6.Certificate.MixedSemantics.sound2957`, `OAI.MUB6.Certificate.MixedSemantics.sound2958`, `OAI.MUB6.Certificate.MixedSemantics.sound2959`, `OAI.MUB6.Certificate.MixedSemantics.sound2960`, `OAI.MUB6.Certificate.MixedSemantics.sound2961`, `OAI.MUB6.Certificate.MixedSemantics.sound2963`, `OAI.MUB6.Certificate.MixedSemantics.sound2965`, `OAI.MUB6.Certificate.MixedSemantics.sound2966`, `OAI.MUB6.Certificate.MixedSemantics.sound2968`, `OAI.MUB6.Certificate.MixedSemantics.sound2969`, `OAI.MUB6.Certificate.MixedSemantics.sound2986`, `OAI.MUB6.Certificate.MixedSemantics.sound2987`, `OAI.MUB6.Certificate.MixedSemantics.sound2988`, `OAI.MUB6.Certificate.MixedSemantics.sound2990`, `OAI.MUB6.Certificate.MixedSemantics.sound2996`, `OAI.MUB6.Certificate.MixedSemantics.sound2997`, `OAI.MUB6.Certificate.MixedSemantics.sound2998`, `OAI.MUB6.Certificate.MixedSemantics.sound3003`, `OAI.MUB6.Certificate.MixedSemantics.sound3005`, `OAI.MUB6.Certificate.MixedSemantics.sound3082`, `OAI.MUB6.Certificate.MixedSemantics.sound3087`, `OAI.MUB6.Certificate.MixedSemantics.sound3088`, `OAI.MUB6.Certificate.MixedSemantics.sound3089`, `OAI.MUB6.Certificate.MixedSemantics.sound3090`, `OAI.MUB6.Certificate.MixedSemantics.sound3093`, `OAI.MUB6.Certificate.MixedSemantics.sound3094`, `OAI.MUB6.Certificate.MixedSemantics.sound3099`, `OAI.MUB6.Certificate.MixedSemantics.sound3100`, `OAI.MUB6.Certificate.MixedSemantics.sound3101`, `OAI.MUB6.Certificate.MixedSemantics.sound3102`, `OAI.MUB6.Certificate.MixedSemantics.sound3106`, `OAI.MUB6.Certificate.MixedSemantics.sound3109`, `OAI.MUB6.Certificate.MixedSemantics.sound3110`, `OAI.MUB6.Certificate.MixedSemantics.sound3116`, `OAI.MUB6.Certificate.MixedSemantics.sound3120`, `OAI.MUB6.Certificate.MixedSemantics.sound3143`, `OAI.MUB6.Certificate.MixedSemantics.sound3144`, `OAI.MUB6.Certificate.MixedSemantics.sound3178`, `OAI.MUB6.Certificate.MixedSemantics.sound3184`, `OAI.MUB6.Certificate.MixedSemantics.sound3185`, `OAI.MUB6.Certificate.MixedSemantics.sound3190`, `OAI.MUB6.Certificate.MixedSemantics.sound3191`, `OAI.MUB6.Certificate.MixedSemantics.sound3203`, `OAI.MUB6.Certificate.MixedSemantics.sound3204`, `OAI.MUB6.Certificate.MixedSemantics.sound3205`, `OAI.MUB6.Certificate.MixedSemantics.sound3206`, `OAI.MUB6.Certificate.MixedSemantics.sound3207`, `OAI.MUB6.Certificate.MixedSemantics.sound3209`, `OAI.MUB6.Certificate.MixedSemantics.sound3210`, `OAI.MUB6.Certificate.MixedSemantics.sound3211`, `OAI.MUB6.Certificate.MixedSemantics.sound3223`, `OAI.MUB6.Certificate.MixedSemantics.sound3226`, `OAI.MUB6.Certificate.MixedSemantics.sound3227`, `OAI.MUB6.Certificate.MixedSemantics.sound370`, `OAI.MUB6.Certificate.MixedSemantics.sound371`, `OAI.MUB6.Certificate.MixedSemantics.sound3711`, `OAI.MUB6.Certificate.MixedSemantics.sound3726`, `OAI.MUB6.Certificate.MixedSemantics.sound3727`, `OAI.MUB6.Certificate.MixedSemantics.sound3734`, `OAI.MUB6.Certificate.MixedSemantics.sound3735`, `OAI.MUB6.Certificate.MixedSemantics.sound3736`, `OAI.MUB6.Certificate.MixedSemantics.sound3737`, `OAI.MUB6.Certificate.MixedSemantics.sound3738`, `OAI.MUB6.Certificate.MixedSemantics.sound3739`, `OAI.MUB6.Certificate.MixedSemantics.sound3818`, `OAI.MUB6.Certificate.MixedSemantics.sound3821`, `OAI.MUB6.Certificate.MixedSemantics.sound3822`, `OAI.MUB6.Certificate.MixedSemantics.sound3823`, `OAI.MUB6.Certificate.MixedSemantics.sound3824`, `OAI.MUB6.Certificate.MixedSemantics.sound3829`, `OAI.MUB6.Certificate.MixedSemantics.sound3831`, `OAI.MUB6.Certificate.MixedSemantics.sound3847`, `OAI.MUB6.Certificate.MixedSemantics.sound3851`, `OAI.MUB6.Certificate.MixedSemantics.sound3852`, `OAI.MUB6.Certificate.MixedSemantics.sound3853`, `OAI.MUB6.Certificate.MixedSemantics.sound3855`, `OAI.MUB6.Certificate.MixedSemantics.sound3856`, `OAI.MUB6.Certificate.MixedSemantics.sound3858`, `OAI.MUB6.Certificate.MixedSemantics.sound3882`, `OAI.MUB6.Certificate.MixedSemantics.sound3883`, `OAI.MUB6.Certificate.MixedSemantics.sound3887`, `OAI.MUB6.Certificate.MixedSemantics.sound3888`, `OAI.MUB6.Certificate.MixedSemantics.sound3925`, `OAI.MUB6.Certificate.MixedSemantics.sound3931`, `OAI.MUB6.Certificate.MixedSemantics.sound3933`, `OAI.MUB6.Certificate.MixedSemantics.sound3936`, `OAI.MUB6.Certificate.MixedSemantics.sound3937`, `OAI.MUB6.Certificate.MixedSemantics.sound3965`, `OAI.MUB6.Certificate.MixedSemantics.sound3966`, `OAI.MUB6.Certificate.MixedSemantics.sound3967`, `OAI.MUB6.Certificate.MixedSemantics.sound3977`, `OAI.MUB6.Certificate.MixedSemantics.sound3980`, `OAI.MUB6.Certificate.MixedSemantics.sound3982`, `OAI.MUB6.Certificate.MixedSemantics.sound3987`, `OAI.MUB6.Certificate.MixedSemantics.sound3992`, `OAI.MUB6.Certificate.MixedSemantics.sound3993`, `OAI.MUB6.Certificate.MixedSemantics.sound3994`, `OAI.MUB6.Certificate.MixedSemantics.sound4002`, `OAI.MUB6.Certificate.MixedSemantics.sound4003`, `OAI.MUB6.Certificate.MixedSemantics.sound4012`, `OAI.MUB6.Certificate.MixedSemantics.sound4023`, `OAI.MUB6.Certificate.MixedSemantics.sound4026`, `OAI.MUB6.Certificate.MixedSemantics.sound4027`, `OAI.MUB6.Certificate.MixedSemantics.sound4029`, `OAI.MUB6.Certificate.MixedSemantics.sound4031`, `OAI.MUB6.Certificate.MixedSemantics.sound4032`, `OAI.MUB6.Certificate.MixedSemantics.sound4033`, `OAI.MUB6.Certificate.MixedSemantics.sound4039`, `OAI.MUB6.Certificate.MixedSemantics.sound4053`, `OAI.MUB6.Certificate.MixedSemantics.sound436`, `OAI.MUB6.Certificate.MixedSemantics.sound454`, `OAI.MUB6.Certificate.MixedSemantics.sound455`, `OAI.MUB6.Certificate.MixedSemantics.sound4623`, `OAI.MUB6.Certificate.MixedSemantics.sound4625`, `OAI.MUB6.Certificate.MixedSemantics.sound479`, `OAI.MUB6.Certificate.MixedSemantics.sound511`, `OAI.MUB6.Certificate.MixedSemantics.sound5176`, `OAI.MUB6.Certificate.MixedSemantics.sound5177`, `OAI.MUB6.Certificate.MixedSemantics.sound521`, `OAI.MUB6.Certificate.MixedSemantics.sound5293`, `OAI.MUB6.Certificate.MixedSemantics.sound5294`, `OAI.MUB6.Certificate.MixedSemantics.sound5296`, `OAI.MUB6.Certificate.MixedSemantics.sound5306`, `OAI.MUB6.Certificate.MixedSemantics.sound5310`, `OAI.MUB6.Certificate.MixedSemantics.sound5415`, `OAI.MUB6.Certificate.MixedSemantics.sound5443`, `OAI.MUB6.Certificate.MixedSemantics.sound5452`, `OAI.MUB6.Certificate.MixedSemantics.sound5453`, `OAI.MUB6.Certificate.MixedSemantics.sound5464`, `OAI.MUB6.Certificate.MixedSemantics.sound5498`, `OAI.MUB6.Certificate.MixedSemantics.sound644`, `OAI.MUB6.Certificate.MixedSemantics.sound645`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound135`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound136`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound137`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound138`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound139`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound140`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound141`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound142`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound143`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound145`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound146`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound147`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound148`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound149`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound150`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound151`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1098`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1423`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1780`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero539`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero925`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound10`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound100`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1008`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound101`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1010`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1013`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1021`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1094`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1096`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound110`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1103`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1109`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound111`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1110`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1111`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1115`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1121`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1124`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1131`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound114`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1159`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound116`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1167`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound117`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1170`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1178`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1179`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound126`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1262`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1264`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1267`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1269`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound127`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1272`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1279`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1294`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound13`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound130`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1301`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1303`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1311`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1312`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1318`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound138`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound140`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound141`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1410`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1414`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1418`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1421`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1429`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1435`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1437`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1442`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1470`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1472`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1480`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1484`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1493`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1517`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1521`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound153`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1560`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1568`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound16`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1649`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1651`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1653`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1656`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1662`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1669`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1674`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1703`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1709`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1717`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1781`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1782`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1783`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1785`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1786`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1787`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1789`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1796`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1816`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1840`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1844`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1845`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1846`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1847`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1849`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1853`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1854`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1856`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1859`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1866`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1874`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound188`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1905`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1911`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1915`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1917`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1964`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1972`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound198`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound199`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2034`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2035`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2037`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2038`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2040`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2046`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2049`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2050`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2059`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2062`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound207`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2075`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2166`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2168`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2169`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2170`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2171`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2172`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2174`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2175`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2176`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2177`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2178`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2179`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2180`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2181`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2182`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2183`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2184`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2185`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2187`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2188`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2189`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2190`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2191`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2192`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2194`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2197`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2199`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2200`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2201`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2203`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2204`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2205`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2206`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2207`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2208`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2211`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2212`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2214`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2216`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2217`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2218`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2219`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2221`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2222`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2223`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2224`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2225`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2226`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2227`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2228`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2229`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2230`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2231`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2232`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2233`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2235`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2238`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2240`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2242`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2244`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2245`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2246`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2247`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2248`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2249`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2250`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2251`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2252`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2254`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2255`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2257`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2258`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2259`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2260`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2261`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2263`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2264`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2266`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2267`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2268`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2269`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2270`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2271`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2272`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2273`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2274`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2275`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2276`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2277`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2278`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2279`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2280`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2282`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2283`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2284`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2286`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2287`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2288`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2289`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2291`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2292`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2293`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2294`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2296`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2297`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2298`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2299`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2300`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2301`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2302`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2303`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2304`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2306`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2307`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2308`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2309`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2313`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2315`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2317`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2318`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2320`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2321`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2322`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2323`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2324`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2325`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2326`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2327`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2329`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2330`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2331`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2332`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2333`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2334`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2335`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2336`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2337`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2338`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2340`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2341`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2344`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2345`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2346`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2347`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2348`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2350`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2351`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2352`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2353`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2354`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2355`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2356`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2357`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound236`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2360`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2361`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2362`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2363`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2364`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2365`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2366`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2367`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2368`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2369`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2371`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2372`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2373`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2374`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2375`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2377`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2378`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2379`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2380`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2381`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2383`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2384`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2386`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2388`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2391`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2393`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2394`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2395`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2396`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2397`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2398`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2399`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2400`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2401`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2402`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2403`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2404`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2405`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2406`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2407`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2408`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2409`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2410`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2411`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2413`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2414`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2415`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2418`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2419`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2420`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2423`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2424`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound244`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound245`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound255`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound268`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound269`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound286`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound287`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound296`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound3`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound310`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound339`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound340`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound342`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound344`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound345`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound349`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound35`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound354`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound356`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound358`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound359`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound366`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound368`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound370`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound371`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound372`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound380`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound388`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound391`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound392`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound395`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound396`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound404`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound412`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound413`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound418`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound428`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound438`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound445`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound453`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound456`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound462`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound463`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound474`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound482`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound484`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound485`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound488`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound498`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound5`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound500`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound501`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound504`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound515`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound516`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound521`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound522`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound525`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound526`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound532`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound534`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound543`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound545`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound547`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound548`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound552`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound554`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound555`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound558`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound565`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound567`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound568`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound571`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound572`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound579`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound58`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound581`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound582`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound585`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound59`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound6`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound600`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound613`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound621`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound629`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound631`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound633`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound635`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound649`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound659`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound663`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound664`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound667`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound675`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound711`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound718`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound731`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound732`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound734`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound736`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound741`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound743`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound779`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound780`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound787`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound788`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound790`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound792`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound794`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound796`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound8`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound800`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound802`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound813`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound864`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound865`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound866`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound872`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound877`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound878`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound881`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound885`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound888`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound899`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound911`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound92`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound923`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound933`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound936`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound94`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound940`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound947`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound97`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound98`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval106`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1074`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval109`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval116`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval117`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1192`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval12`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval120`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1210`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval124`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1254`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval130`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval133`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval134`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval141`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval143`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval145`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval146`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval147`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval149`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval155`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1553`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval159`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval164`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval165`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval167`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval173`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval174`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval18`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval181`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval182`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval185`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval202`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval203`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval207`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval21`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval214`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval215`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval218`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval220`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval224`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval225`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval226`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval229`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval231`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval234`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval235`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval242`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval243`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval245`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval249`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval255`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval257`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval258`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval263`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval270`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval271`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval273`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval278`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval280`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval285`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval286`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval287`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval292`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval296`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval301`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval308`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval310`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval323`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval325`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval331`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval332`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval334`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval335`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval343`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval344`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval348`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval353`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval358`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval359`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval366`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval368`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval37`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval370`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval371`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval372`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval373`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval377`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval380`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval383`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval389`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval39`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval391`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval394`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval401`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval403`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval408`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval41`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval413`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval414`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval444`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval46`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval475`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval476`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval477`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval52`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval54`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval56`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval6`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval63`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval69`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval73`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval74`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval77`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval79`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval8`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval83`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval86`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval91`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval99`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval113`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval119`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval147`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval150`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval208`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval21`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval215`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval216`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval220`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval222`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval271`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval359`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval360`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval362`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval373`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval375`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval384`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval44`, `OAI.MUB6.Certificate.PairSemantics.boundarySound165`, `OAI.MUB6.Certificate.PairSemantics.boundarySound243`, `OAI.MUB6.Certificate.PairSemantics.boundarySound248`, `OAI.MUB6.Certificate.PairSemantics.boundarySound249`, `OAI.MUB6.Certificate.PairSemantics.boundarySound250`, `OAI.MUB6.Certificate.PairSemantics.boundarySound252`, `OAI.MUB6.Certificate.PairSemantics.boundarySound261`, `OAI.MUB6.Certificate.PairSemantics.boundarySound264`, `OAI.MUB6.Certificate.PairSemantics.boundarySound305`, `OAI.MUB6.Certificate.PairSemantics.boundarySound347`, `OAI.MUB6.Certificate.PairSemantics.boundarySound377`, `OAI.MUB6.Certificate.PairSemantics.boundarySound445`, `OAI.MUB6.Certificate.PairSemantics.boundarySound454`, `OAI.MUB6.Certificate.PairSemantics.boundarySound49`, `OAI.MUB6.Certificate.PairSemantics.boundarySound51`, `OAI.MUB6.Certificate.PairSemantics.boundarySound56`, `OAI.MUB6.Certificate.PairSemantics.boundarySound7`, `OAI.MUB6.Certificate.PairSemantics.boundarySound73`, `OAI.MUB6.Certificate.PairSemantics.boundarySound75`, `OAI.MUB6.Certificate.PairSemantics.boundarySound83`, `OAI.MUB6.Certificate.PairSemantics.boundarySound97`, `OAI.MUB6.Certificate.PairSemantics.canonical9056`, `OAI.MUB6.Certificate.PairSemantics.sound1141`, `OAI.MUB6.Certificate.PairSemantics.sound1151`, `OAI.MUB6.Certificate.PairSemantics.sound1152`, `OAI.MUB6.Certificate.PairSemantics.sound117`, `OAI.MUB6.Certificate.PairSemantics.sound1381`, `OAI.MUB6.Certificate.PairSemantics.sound1383`, `OAI.MUB6.Certificate.PairSemantics.sound1384`, `OAI.MUB6.Certificate.PairSemantics.sound1387`, `OAI.MUB6.Certificate.PairSemantics.sound1390`, `OAI.MUB6.Certificate.PairSemantics.sound1391`, `OAI.MUB6.Certificate.PairSemantics.sound1392`, `OAI.MUB6.Certificate.PairSemantics.sound1395`, `OAI.MUB6.Certificate.PairSemantics.sound1399`, `OAI.MUB6.Certificate.PairSemantics.sound1414`, `OAI.MUB6.Certificate.PairSemantics.sound1419`, `OAI.MUB6.Certificate.PairSemantics.sound1423`, `OAI.MUB6.Certificate.PairSemantics.sound1424`, `OAI.MUB6.Certificate.PairSemantics.sound1425`, `OAI.MUB6.Certificate.PairSemantics.sound1432`, `OAI.MUB6.Certificate.PairSemantics.sound1434`, `OAI.MUB6.Certificate.PairSemantics.sound1437`, `OAI.MUB6.Certificate.PairSemantics.sound1443`, `OAI.MUB6.Certificate.PairSemantics.sound1458`, `OAI.MUB6.Certificate.PairSemantics.sound1486`, `OAI.MUB6.Certificate.PairSemantics.sound1500`, `OAI.MUB6.Certificate.PairSemantics.sound1504`, `OAI.MUB6.Certificate.PairSemantics.sound1506`, `OAI.MUB6.Certificate.PairSemantics.sound1512`, `OAI.MUB6.Certificate.PairSemantics.sound1518`, `OAI.MUB6.Certificate.PairSemantics.sound1520`, `OAI.MUB6.Certificate.PairSemantics.sound1523`, `OAI.MUB6.Certificate.PairSemantics.sound1530`, `OAI.MUB6.Certificate.PairSemantics.sound1531`, `OAI.MUB6.Certificate.PairSemantics.sound1533`, `OAI.MUB6.Certificate.PairSemantics.sound1535`, `OAI.MUB6.Certificate.PairSemantics.sound1540`, `OAI.MUB6.Certificate.PairSemantics.sound1548`, `OAI.MUB6.Certificate.PairSemantics.sound1552`, `OAI.MUB6.Certificate.PairSemantics.sound1563`, `OAI.MUB6.Certificate.PairSemantics.sound1585`, `OAI.MUB6.Certificate.PairSemantics.sound1605`, `OAI.MUB6.Certificate.PairSemantics.sound1614`, `OAI.MUB6.Certificate.PairSemantics.sound1617`, `OAI.MUB6.Certificate.PairSemantics.sound1624`, `OAI.MUB6.Certificate.PairSemantics.sound1625`, `OAI.MUB6.Certificate.PairSemantics.sound1627`, `OAI.MUB6.Certificate.PairSemantics.sound1628`, `OAI.MUB6.Certificate.PairSemantics.sound1631`, `OAI.MUB6.Certificate.PairSemantics.sound1634`, `OAI.MUB6.Certificate.PairSemantics.sound1635`, `OAI.MUB6.Certificate.PairSemantics.sound1637`, `OAI.MUB6.Certificate.PairSemantics.sound1638`, `OAI.MUB6.Certificate.PairSemantics.sound1643`, `OAI.MUB6.Certificate.PairSemantics.sound1646`, `OAI.MUB6.Certificate.PairSemantics.sound1648`, `OAI.MUB6.Certificate.PairSemantics.sound1652`, `OAI.MUB6.Certificate.PairSemantics.sound1668`, `OAI.MUB6.Certificate.PairSemantics.sound1669`, `OAI.MUB6.Certificate.PairSemantics.sound1682`, `OAI.MUB6.Certificate.PairSemantics.sound1685`, `OAI.MUB6.Certificate.PairSemantics.sound1686`, `OAI.MUB6.Certificate.PairSemantics.sound1707`, `OAI.MUB6.Certificate.PairSemantics.sound1716`, `OAI.MUB6.Certificate.PairSemantics.sound1718`, `OAI.MUB6.Certificate.PairSemantics.sound1736`, `OAI.MUB6.Certificate.PairSemantics.sound1739`, `OAI.MUB6.Certificate.PairSemantics.sound1768`, `OAI.MUB6.Certificate.PairSemantics.sound1769`, `OAI.MUB6.Certificate.PairSemantics.sound1770`, `OAI.MUB6.Certificate.PairSemantics.sound1774`, `OAI.MUB6.Certificate.PairSemantics.sound1784`, `OAI.MUB6.Certificate.PairSemantics.sound1793`, `OAI.MUB6.Certificate.PairSemantics.sound1800`, `OAI.MUB6.Certificate.PairSemantics.sound1803`, `OAI.MUB6.Certificate.PairSemantics.sound1826`, `OAI.MUB6.Certificate.PairSemantics.sound1828`, `OAI.MUB6.Certificate.PairSemantics.sound1830`, `OAI.MUB6.Certificate.PairSemantics.sound1849`, `OAI.MUB6.Certificate.PairSemantics.sound1858`, `OAI.MUB6.Certificate.PairSemantics.sound1860`, `OAI.MUB6.Certificate.PairSemantics.sound1865`, `OAI.MUB6.Certificate.PairSemantics.sound1866`, `OAI.MUB6.Certificate.PairSemantics.sound1867`, `OAI.MUB6.Certificate.PairSemantics.sound1869`, `OAI.MUB6.Certificate.PairSemantics.sound1870`, `OAI.MUB6.Certificate.PairSemantics.sound1872`, `OAI.MUB6.Certificate.PairSemantics.sound1873`, `OAI.MUB6.Certificate.PairSemantics.sound1879`, `OAI.MUB6.Certificate.PairSemantics.sound1885`, `OAI.MUB6.Certificate.PairSemantics.sound1890`, `OAI.MUB6.Certificate.PairSemantics.sound1938`, `OAI.MUB6.Certificate.PairSemantics.sound1968`, `OAI.MUB6.Certificate.PairSemantics.sound1977`, `OAI.MUB6.Certificate.PairSemantics.sound1978`, `OAI.MUB6.Certificate.PairSemantics.sound1980`, `OAI.MUB6.Certificate.PairSemantics.sound1986`, `OAI.MUB6.Certificate.PairSemantics.sound1987`, `OAI.MUB6.Certificate.PairSemantics.sound2041`, `OAI.MUB6.Certificate.PairSemantics.sound2058`, `OAI.MUB6.Certificate.PairSemantics.sound2106`, `OAI.MUB6.Certificate.PairSemantics.sound2108`, `OAI.MUB6.Certificate.PairSemantics.sound2113`, `OAI.MUB6.Certificate.PairSemantics.sound2117`, `OAI.MUB6.Certificate.PairSemantics.sound2122`, `OAI.MUB6.Certificate.PairSemantics.sound2123`, `OAI.MUB6.Certificate.PairSemantics.sound2128`, `OAI.MUB6.Certificate.PairSemantics.sound2132`, `OAI.MUB6.Certificate.PairSemantics.sound2152`, `OAI.MUB6.Certificate.PairSemantics.sound2168`, `OAI.MUB6.Certificate.PairSemantics.sound2175`, `OAI.MUB6.Certificate.PairSemantics.sound2177`, `OAI.MUB6.Certificate.PairSemantics.sound2183`, `OAI.MUB6.Certificate.PairSemantics.sound2190`, `OAI.MUB6.Certificate.PairSemantics.sound2192`, `OAI.MUB6.Certificate.PairSemantics.sound2197`, `OAI.MUB6.Certificate.PairSemantics.sound2201`, `OAI.MUB6.Certificate.PairSemantics.sound2202`, `OAI.MUB6.Certificate.PairSemantics.sound2204`, `OAI.MUB6.Certificate.PairSemantics.sound2213`, `OAI.MUB6.Certificate.PairSemantics.sound2216`, `OAI.MUB6.Certificate.PairSemantics.sound2228`, `OAI.MUB6.Certificate.PairSemantics.sound2243`, `OAI.MUB6.Certificate.PairSemantics.sound2244`, `OAI.MUB6.Certificate.PairSemantics.sound2262`, `OAI.MUB6.Certificate.PairSemantics.sound2284`, `OAI.MUB6.Certificate.PairSemantics.sound2285`, `OAI.MUB6.Certificate.PairSemantics.sound2286`, `OAI.MUB6.Certificate.PairSemantics.sound2293`, `OAI.MUB6.Certificate.PairSemantics.sound2294`, `OAI.MUB6.Certificate.PairSemantics.sound2295`, `OAI.MUB6.Certificate.PairSemantics.sound2296`, `OAI.MUB6.Certificate.PairSemantics.sound2298`, `OAI.MUB6.Certificate.PairSemantics.sound2304`, `OAI.MUB6.Certificate.PairSemantics.sound2307`, `OAI.MUB6.Certificate.PairSemantics.sound2312`, `OAI.MUB6.Certificate.PairSemantics.sound2315`, `OAI.MUB6.Certificate.PairSemantics.sound232`, `OAI.MUB6.Certificate.PairSemantics.sound2324`, `OAI.MUB6.Certificate.PairSemantics.sound2325`, `OAI.MUB6.Certificate.PairSemantics.sound2327`, `OAI.MUB6.Certificate.PairSemantics.sound2338`, `OAI.MUB6.Certificate.PairSemantics.sound2349`, `OAI.MUB6.Certificate.PairSemantics.sound2357`, `OAI.MUB6.Certificate.PairSemantics.sound2375`, `OAI.MUB6.Certificate.PairSemantics.sound2382`, `OAI.MUB6.Certificate.PairSemantics.sound2389`, `OAI.MUB6.Certificate.PairSemantics.sound2390`, `OAI.MUB6.Certificate.PairSemantics.sound2391`, `OAI.MUB6.Certificate.PairSemantics.sound2399`, `OAI.MUB6.Certificate.PairSemantics.sound2400`, `OAI.MUB6.Certificate.PairSemantics.sound2403`, `OAI.MUB6.Certificate.PairSemantics.sound2411`, `OAI.MUB6.Certificate.PairSemantics.sound2413`, `OAI.MUB6.Certificate.PairSemantics.sound2414`, `OAI.MUB6.Certificate.PairSemantics.sound2415`, `OAI.MUB6.Certificate.PairSemantics.sound2416`, `OAI.MUB6.Certificate.PairSemantics.sound2417`, `OAI.MUB6.Certificate.PairSemantics.sound2420`, `OAI.MUB6.Certificate.PairSemantics.sound2428`, `OAI.MUB6.Certificate.PairSemantics.sound2433`, `OAI.MUB6.Certificate.PairSemantics.sound2434`, `OAI.MUB6.Certificate.PairSemantics.sound2435`, `OAI.MUB6.Certificate.PairSemantics.sound2436`, `OAI.MUB6.Certificate.PairSemantics.sound2440`, `OAI.MUB6.Certificate.PairSemantics.sound2441`, `OAI.MUB6.Certificate.PairSemantics.sound2442`, `OAI.MUB6.Certificate.PairSemantics.sound2443`, `OAI.MUB6.Certificate.PairSemantics.sound2444`, `OAI.MUB6.Certificate.PairSemantics.sound2445`, `OAI.MUB6.Certificate.PairSemantics.sound2455`, `OAI.MUB6.Certificate.PairSemantics.sound2456`, `OAI.MUB6.Certificate.PairSemantics.sound2457`, `OAI.MUB6.Certificate.PairSemantics.sound2462`, `OAI.MUB6.Certificate.PairSemantics.sound2463`, `OAI.MUB6.Certificate.PairSemantics.sound2464`, `OAI.MUB6.Certificate.PairSemantics.sound2465`, `OAI.MUB6.Certificate.PairSemantics.sound2466`, `OAI.MUB6.Certificate.PairSemantics.sound2470`, `OAI.MUB6.Certificate.PairSemantics.sound2472`, `OAI.MUB6.Certificate.PairSemantics.sound2473`, `OAI.MUB6.Certificate.PairSemantics.sound2477`, `OAI.MUB6.Certificate.PairSemantics.sound2479`, `OAI.MUB6.Certificate.PairSemantics.sound2486`, `OAI.MUB6.Certificate.PairSemantics.sound2489`, `OAI.MUB6.Certificate.PairSemantics.sound2490`, `OAI.MUB6.Certificate.PairSemantics.sound2491`, `OAI.MUB6.Certificate.PairSemantics.sound2492`, `OAI.MUB6.Certificate.PairSemantics.sound2507`, `OAI.MUB6.Certificate.PairSemantics.sound2520`, `OAI.MUB6.Certificate.PairSemantics.sound2521`, `OAI.MUB6.Certificate.PairSemantics.sound2524`, `OAI.MUB6.Certificate.PairSemantics.sound2525`, `OAI.MUB6.Certificate.PairSemantics.sound2533`, `OAI.MUB6.Certificate.PairSemantics.sound2540`, `OAI.MUB6.Certificate.PairSemantics.sound2546`, `OAI.MUB6.Certificate.PairSemantics.sound2547`, `OAI.MUB6.Certificate.PairSemantics.sound2548`, `OAI.MUB6.Certificate.PairSemantics.sound2557`, `OAI.MUB6.Certificate.PairSemantics.sound2558`, `OAI.MUB6.Certificate.PairSemantics.sound2559`, `OAI.MUB6.Certificate.PairSemantics.sound2564`, `OAI.MUB6.Certificate.PairSemantics.sound2565`, `OAI.MUB6.Certificate.PairSemantics.sound2566`, `OAI.MUB6.Certificate.PairSemantics.sound2573`, `OAI.MUB6.Certificate.PairSemantics.sound2578`, `OAI.MUB6.Certificate.PairSemantics.sound2579`, `OAI.MUB6.Certificate.PairSemantics.sound2580`, `OAI.MUB6.Certificate.PairSemantics.sound2602`, `OAI.MUB6.Certificate.PairSemantics.sound2604`, `OAI.MUB6.Certificate.PairSemantics.sound2606`, `OAI.MUB6.Certificate.PairSemantics.sound2619`, `OAI.MUB6.Certificate.PairSemantics.sound2626`, `OAI.MUB6.Certificate.PairSemantics.sound2627`, `OAI.MUB6.Certificate.PairSemantics.sound2641`, `OAI.MUB6.Certificate.PairSemantics.sound2657`, `OAI.MUB6.Certificate.PairSemantics.sound2658`, `OAI.MUB6.Certificate.PairSemantics.sound2661`, `OAI.MUB6.Certificate.PairSemantics.sound2666`, `OAI.MUB6.Certificate.PairSemantics.sound2670`, `OAI.MUB6.Certificate.PairSemantics.sound2671`, `OAI.MUB6.Certificate.PairSemantics.sound2674`, `OAI.MUB6.Certificate.PairSemantics.sound2683`, `OAI.MUB6.Certificate.PairSemantics.sound2686`, `OAI.MUB6.Certificate.PairSemantics.sound2690`, `OAI.MUB6.Certificate.PairSemantics.sound2693`, `OAI.MUB6.Certificate.PairSemantics.sound2709`, `OAI.MUB6.Certificate.PairSemantics.sound2710`, `OAI.MUB6.Certificate.PairSemantics.sound2711`, `OAI.MUB6.Certificate.PairSemantics.sound2714`, `OAI.MUB6.Certificate.PairSemantics.sound2717`, `OAI.MUB6.Certificate.PairSemantics.sound2723`, `OAI.MUB6.Certificate.PairSemantics.sound2732`, `OAI.MUB6.Certificate.PairSemantics.sound2733`, `OAI.MUB6.Certificate.PairSemantics.sound2754`, `OAI.MUB6.Certificate.PairSemantics.sound2757`, `OAI.MUB6.Certificate.PairSemantics.sound2765`, `OAI.MUB6.Certificate.PairSemantics.sound2788`, `OAI.MUB6.Certificate.PairSemantics.sound2790`, `OAI.MUB6.Certificate.PairSemantics.sound2793`, `OAI.MUB6.Certificate.PairSemantics.sound2827`, `OAI.MUB6.Certificate.PairSemantics.sound2829`, `OAI.MUB6.Certificate.PairSemantics.sound2836`, `OAI.MUB6.Certificate.PairSemantics.sound2839`, `OAI.MUB6.Certificate.PairSemantics.sound284`, `OAI.MUB6.Certificate.PairSemantics.sound2845`, `OAI.MUB6.Certificate.PairSemantics.sound2850`, `OAI.MUB6.Certificate.PairSemantics.sound2852`, `OAI.MUB6.Certificate.PairSemantics.sound2854`, `OAI.MUB6.Certificate.PairSemantics.sound2855`, `OAI.MUB6.Certificate.PairSemantics.sound2863`, `OAI.MUB6.Certificate.PairSemantics.sound2864`, `OAI.MUB6.Certificate.PairSemantics.sound2865`, `OAI.MUB6.Certificate.PairSemantics.sound2866`, `OAI.MUB6.Certificate.PairSemantics.sound2867`, `OAI.MUB6.Certificate.PairSemantics.sound2868`, `OAI.MUB6.Certificate.PairSemantics.sound2872`, `OAI.MUB6.Certificate.PairSemantics.sound2873`, `OAI.MUB6.Certificate.PairSemantics.sound2874`, `OAI.MUB6.Certificate.PairSemantics.sound2875`, `OAI.MUB6.Certificate.PairSemantics.sound2878`, `OAI.MUB6.Certificate.PairSemantics.sound2879`, `OAI.MUB6.Certificate.PairSemantics.sound2880`, `OAI.MUB6.Certificate.PairSemantics.sound2881`, `OAI.MUB6.Certificate.PairSemantics.sound2882`, `OAI.MUB6.Certificate.PairSemantics.sound2883`, `OAI.MUB6.Certificate.PairSemantics.sound2884`, `OAI.MUB6.Certificate.PairSemantics.sound2886`, `OAI.MUB6.Certificate.PairSemantics.sound2887`, `OAI.MUB6.Certificate.PairSemantics.sound2888`, `OAI.MUB6.Certificate.PairSemantics.sound2889`, `OAI.MUB6.Certificate.PairSemantics.sound2890`, `OAI.MUB6.Certificate.PairSemantics.sound2891`, `OAI.MUB6.Certificate.PairSemantics.sound2892`, `OAI.MUB6.Certificate.PairSemantics.sound2894`, `OAI.MUB6.Certificate.PairSemantics.sound2895`, `OAI.MUB6.Certificate.PairSemantics.sound2896`, `OAI.MUB6.Certificate.PairSemantics.sound2897`, `OAI.MUB6.Certificate.PairSemantics.sound2898`, `OAI.MUB6.Certificate.PairSemantics.sound2899`, `OAI.MUB6.Certificate.PairSemantics.sound2900`, `OAI.MUB6.Certificate.PairSemantics.sound2901`, `OAI.MUB6.Certificate.PairSemantics.sound2902`, `OAI.MUB6.Certificate.PairSemantics.sound2903`, `OAI.MUB6.Certificate.PairSemantics.sound2906`, `OAI.MUB6.Certificate.PairSemantics.sound2909`, `OAI.MUB6.Certificate.PairSemantics.sound2910`, `OAI.MUB6.Certificate.PairSemantics.sound2912`, `OAI.MUB6.Certificate.PairSemantics.sound2913`, `OAI.MUB6.Certificate.PairSemantics.sound2914`, `OAI.MUB6.Certificate.PairSemantics.sound2915`, `OAI.MUB6.Certificate.PairSemantics.sound2916`, `OAI.MUB6.Certificate.PairSemantics.sound2917`, `OAI.MUB6.Certificate.PairSemantics.sound2918`, `OAI.MUB6.Certificate.PairSemantics.sound2919`, `OAI.MUB6.Certificate.PairSemantics.sound2920`, `OAI.MUB6.Certificate.PairSemantics.sound2922`, `OAI.MUB6.Certificate.PairSemantics.sound2924`, `OAI.MUB6.Certificate.PairSemantics.sound2927`, `OAI.MUB6.Certificate.PairSemantics.sound2928`, `OAI.MUB6.Certificate.PairSemantics.sound2929`, `OAI.MUB6.Certificate.PairSemantics.sound2930`, `OAI.MUB6.Certificate.PairSemantics.sound2931`, `OAI.MUB6.Certificate.PairSemantics.sound2933`, `OAI.MUB6.Certificate.PairSemantics.sound2934`, `OAI.MUB6.Certificate.PairSemantics.sound2935`, `OAI.MUB6.Certificate.PairSemantics.sound2936`, `OAI.MUB6.Certificate.PairSemantics.sound2939`, `OAI.MUB6.Certificate.PairSemantics.sound2940`, `OAI.MUB6.Certificate.PairSemantics.sound2941`, `OAI.MUB6.Certificate.PairSemantics.sound2943`, `OAI.MUB6.Certificate.PairSemantics.sound2944`, `OAI.MUB6.Certificate.PairSemantics.sound2947`, `OAI.MUB6.Certificate.PairSemantics.sound2948`, `OAI.MUB6.Certificate.PairSemantics.sound2949`, `OAI.MUB6.Certificate.PairSemantics.sound2950`, `OAI.MUB6.Certificate.PairSemantics.sound2952`, `OAI.MUB6.Certificate.PairSemantics.sound2953`, `OAI.MUB6.Certificate.PairSemantics.sound2954`, `OAI.MUB6.Certificate.PairSemantics.sound2955`, `OAI.MUB6.Certificate.PairSemantics.sound2956`, `OAI.MUB6.Certificate.PairSemantics.sound2957`, `OAI.MUB6.Certificate.PairSemantics.sound2958`, `OAI.MUB6.Certificate.PairSemantics.sound2959`, `OAI.MUB6.Certificate.PairSemantics.sound2960`, `OAI.MUB6.Certificate.PairSemantics.sound2962`, `OAI.MUB6.Certificate.PairSemantics.sound2964`, `OAI.MUB6.Certificate.PairSemantics.sound2965`, `OAI.MUB6.Certificate.PairSemantics.sound2966`, `OAI.MUB6.Certificate.PairSemantics.sound2967`, `OAI.MUB6.Certificate.PairSemantics.sound2968`, `OAI.MUB6.Certificate.PairSemantics.sound2969`, `OAI.MUB6.Certificate.PairSemantics.sound2970`, `OAI.MUB6.Certificate.PairSemantics.sound2972`, `OAI.MUB6.Certificate.PairSemantics.sound2973`, `OAI.MUB6.Certificate.PairSemantics.sound2974`, `OAI.MUB6.Certificate.PairSemantics.sound2975`, `OAI.MUB6.Certificate.PairSemantics.sound2976`, `OAI.MUB6.Certificate.PairSemantics.sound2977`, `OAI.MUB6.Certificate.PairSemantics.sound2979`, `OAI.MUB6.Certificate.PairSemantics.sound2980`, `OAI.MUB6.Certificate.PairSemantics.sound2982`, `OAI.MUB6.Certificate.PairSemantics.sound2985`, `OAI.MUB6.Certificate.PairSemantics.sound2986`, `OAI.MUB6.Certificate.PairSemantics.sound2987`, `OAI.MUB6.Certificate.PairSemantics.sound2988`, `OAI.MUB6.Certificate.PairSemantics.sound2989`, `OAI.MUB6.Certificate.PairSemantics.sound2990`, `OAI.MUB6.Certificate.PairSemantics.sound2991`, `OAI.MUB6.Certificate.PairSemantics.sound2993`, `OAI.MUB6.Certificate.PairSemantics.sound2994`, `OAI.MUB6.Certificate.PairSemantics.sound2996`, `OAI.MUB6.Certificate.PairSemantics.sound2997`, `OAI.MUB6.Certificate.PairSemantics.sound2998`, `OAI.MUB6.Certificate.PairSemantics.sound2999`, `OAI.MUB6.Certificate.PairSemantics.sound3000`, `OAI.MUB6.Certificate.PairSemantics.sound3001`, `OAI.MUB6.Certificate.PairSemantics.sound3002`, `OAI.MUB6.Certificate.PairSemantics.sound3004`, `OAI.MUB6.Certificate.PairSemantics.sound3006`, `OAI.MUB6.Certificate.PairSemantics.sound3009`, `OAI.MUB6.Certificate.PairSemantics.sound3010`, `OAI.MUB6.Certificate.PairSemantics.sound3011`, `OAI.MUB6.Certificate.PairSemantics.sound3012`, `OAI.MUB6.Certificate.PairSemantics.sound3013`, `OAI.MUB6.Certificate.PairSemantics.sound3014`, `OAI.MUB6.Certificate.PairSemantics.sound3015`, `OAI.MUB6.Certificate.PairSemantics.sound3016`, `OAI.MUB6.Certificate.PairSemantics.sound3017`, `OAI.MUB6.Certificate.PairSemantics.sound3018`, `OAI.MUB6.Certificate.PairSemantics.sound3019`, `OAI.MUB6.Certificate.PairSemantics.sound3020`, `OAI.MUB6.Certificate.PairSemantics.sound3021`, `OAI.MUB6.Certificate.PairSemantics.sound3022`, `OAI.MUB6.Certificate.PairSemantics.sound3023`, `OAI.MUB6.Certificate.PairSemantics.sound3024`, `OAI.MUB6.Certificate.PairSemantics.sound3025`, `OAI.MUB6.Certificate.PairSemantics.sound3026`, `OAI.MUB6.Certificate.PairSemantics.sound3027`, `OAI.MUB6.Certificate.PairSemantics.sound3028`, `OAI.MUB6.Certificate.PairSemantics.sound3029`, `OAI.MUB6.Certificate.PairSemantics.sound3030`, `OAI.MUB6.Certificate.PairSemantics.sound3031`, `OAI.MUB6.Certificate.PairSemantics.sound3032`, `OAI.MUB6.Certificate.PairSemantics.sound3033`, `OAI.MUB6.Certificate.PairSemantics.sound3034`, `OAI.MUB6.Certificate.PairSemantics.sound3035`, `OAI.MUB6.Certificate.PairSemantics.sound3036`, `OAI.MUB6.Certificate.PairSemantics.sound3038`, `OAI.MUB6.Certificate.PairSemantics.sound3039`, `OAI.MUB6.Certificate.PairSemantics.sound3040`, `OAI.MUB6.Certificate.PairSemantics.sound3041`, `OAI.MUB6.Certificate.PairSemantics.sound3042`, `OAI.MUB6.Certificate.PairSemantics.sound3043`, `OAI.MUB6.Certificate.PairSemantics.sound3044`, `OAI.MUB6.Certificate.PairSemantics.sound3045`, `OAI.MUB6.Certificate.PairSemantics.sound3047`, `OAI.MUB6.Certificate.PairSemantics.sound3048`, `OAI.MUB6.Certificate.PairSemantics.sound3049`, `OAI.MUB6.Certificate.PairSemantics.sound3050`, `OAI.MUB6.Certificate.PairSemantics.sound3051`, `OAI.MUB6.Certificate.PairSemantics.sound3053`, `OAI.MUB6.Certificate.PairSemantics.sound3054`, `OAI.MUB6.Certificate.PairSemantics.sound3056`, `OAI.MUB6.Certificate.PairSemantics.sound3058`, `OAI.MUB6.Certificate.PairSemantics.sound3059`, `OAI.MUB6.Certificate.PairSemantics.sound3060`, `OAI.MUB6.Certificate.PairSemantics.sound3061`, `OAI.MUB6.Certificate.PairSemantics.sound3062`, `OAI.MUB6.Certificate.PairSemantics.sound3063`, `OAI.MUB6.Certificate.PairSemantics.sound3065`, `OAI.MUB6.Certificate.PairSemantics.sound3066`, `OAI.MUB6.Certificate.PairSemantics.sound3067`, `OAI.MUB6.Certificate.PairSemantics.sound3068`, `OAI.MUB6.Certificate.PairSemantics.sound3069`, `OAI.MUB6.Certificate.PairSemantics.sound3071`, `OAI.MUB6.Certificate.PairSemantics.sound3072`, `OAI.MUB6.Certificate.PairSemantics.sound3073`, `OAI.MUB6.Certificate.PairSemantics.sound3074`, `OAI.MUB6.Certificate.PairSemantics.sound3075`, `OAI.MUB6.Certificate.PairSemantics.sound3076`, `OAI.MUB6.Certificate.PairSemantics.sound3077`, `OAI.MUB6.Certificate.PairSemantics.sound3078`, `OAI.MUB6.Certificate.PairSemantics.sound3079`, `OAI.MUB6.Certificate.PairSemantics.sound3080`, `OAI.MUB6.Certificate.PairSemantics.sound3081`, `OAI.MUB6.Certificate.PairSemantics.sound3082`, `OAI.MUB6.Certificate.PairSemantics.sound3083`, `OAI.MUB6.Certificate.PairSemantics.sound3084`, `OAI.MUB6.Certificate.PairSemantics.sound3085`, `OAI.MUB6.Certificate.PairSemantics.sound3086`, `OAI.MUB6.Certificate.PairSemantics.sound3090`, `OAI.MUB6.Certificate.PairSemantics.sound3091`, `OAI.MUB6.Certificate.PairSemantics.sound3092`, `OAI.MUB6.Certificate.PairSemantics.sound3093`, `OAI.MUB6.Certificate.PairSemantics.sound3094`, `OAI.MUB6.Certificate.PairSemantics.sound3095`, `OAI.MUB6.Certificate.PairSemantics.sound3096`, `OAI.MUB6.Certificate.PairSemantics.sound3097`, `OAI.MUB6.Certificate.PairSemantics.sound3098`, `OAI.MUB6.Certificate.PairSemantics.sound3099`, `OAI.MUB6.Certificate.PairSemantics.sound3100`, `OAI.MUB6.Certificate.PairSemantics.sound3101`, `OAI.MUB6.Certificate.PairSemantics.sound3102`, `OAI.MUB6.Certificate.PairSemantics.sound3105`, `OAI.MUB6.Certificate.PairSemantics.sound3106`, `OAI.MUB6.Certificate.PairSemantics.sound3107`, `OAI.MUB6.Certificate.PairSemantics.sound3108`, `OAI.MUB6.Certificate.PairSemantics.sound3109`, `OAI.MUB6.Certificate.PairSemantics.sound3110`, `OAI.MUB6.Certificate.PairSemantics.sound3111`, `OAI.MUB6.Certificate.PairSemantics.sound3112`, `OAI.MUB6.Certificate.PairSemantics.sound3113`, `OAI.MUB6.Certificate.PairSemantics.sound3114`, `OAI.MUB6.Certificate.PairSemantics.sound3115`, `OAI.MUB6.Certificate.PairSemantics.sound3116`, `OAI.MUB6.Certificate.PairSemantics.sound3118`, `OAI.MUB6.Certificate.PairSemantics.sound3119`, `OAI.MUB6.Certificate.PairSemantics.sound3120`, `OAI.MUB6.Certificate.PairSemantics.sound3121`, `OAI.MUB6.Certificate.PairSemantics.sound3122`, `OAI.MUB6.Certificate.PairSemantics.sound3123`, `OAI.MUB6.Certificate.PairSemantics.sound3124`, `OAI.MUB6.Certificate.PairSemantics.sound3125`, `OAI.MUB6.Certificate.PairSemantics.sound3128`, `OAI.MUB6.Certificate.PairSemantics.sound3129`, `OAI.MUB6.Certificate.PairSemantics.sound3130`, `OAI.MUB6.Certificate.PairSemantics.sound3131`, `OAI.MUB6.Certificate.PairSemantics.sound3133`, `OAI.MUB6.Certificate.PairSemantics.sound3135`, `OAI.MUB6.Certificate.PairSemantics.sound3136`, `OAI.MUB6.Certificate.PairSemantics.sound3138`, `OAI.MUB6.Certificate.PairSemantics.sound3139`, `OAI.MUB6.Certificate.PairSemantics.sound3140`, `OAI.MUB6.Certificate.PairSemantics.sound3141`, `OAI.MUB6.Certificate.PairSemantics.sound3142`, `OAI.MUB6.Certificate.PairSemantics.sound3144`, `OAI.MUB6.Certificate.PairSemantics.sound3145`, `OAI.MUB6.Certificate.PairSemantics.sound3146`, `OAI.MUB6.Certificate.PairSemantics.sound3150`, `OAI.MUB6.Certificate.PairSemantics.sound3151`, `OAI.MUB6.Certificate.PairSemantics.sound3152`, `OAI.MUB6.Certificate.PairSemantics.sound3153`, `OAI.MUB6.Certificate.PairSemantics.sound3155`, `OAI.MUB6.Certificate.PairSemantics.sound3158`, `OAI.MUB6.Certificate.PairSemantics.sound3159`, `OAI.MUB6.Certificate.PairSemantics.sound3160`, `OAI.MUB6.Certificate.PairSemantics.sound3161`, `OAI.MUB6.Certificate.PairSemantics.sound3162`, `OAI.MUB6.Certificate.PairSemantics.sound3163`, `OAI.MUB6.Certificate.PairSemantics.sound3164`, `OAI.MUB6.Certificate.PairSemantics.sound3166`, `OAI.MUB6.Certificate.PairSemantics.sound3167`, `OAI.MUB6.Certificate.PairSemantics.sound3168`, `OAI.MUB6.Certificate.PairSemantics.sound3169`, `OAI.MUB6.Certificate.PairSemantics.sound3170`, `OAI.MUB6.Certificate.PairSemantics.sound3171`, `OAI.MUB6.Certificate.PairSemantics.sound3172`, `OAI.MUB6.Certificate.PairSemantics.sound3173`, `OAI.MUB6.Certificate.PairSemantics.sound3176`, `OAI.MUB6.Certificate.PairSemantics.sound3178`, `OAI.MUB6.Certificate.PairSemantics.sound3179`, `OAI.MUB6.Certificate.PairSemantics.sound3180`, `OAI.MUB6.Certificate.PairSemantics.sound3181`, `OAI.MUB6.Certificate.PairSemantics.sound3183`, `OAI.MUB6.Certificate.PairSemantics.sound3184`, `OAI.MUB6.Certificate.PairSemantics.sound3185`, `OAI.MUB6.Certificate.PairSemantics.sound3186`, `OAI.MUB6.Certificate.PairSemantics.sound3187`, `OAI.MUB6.Certificate.PairSemantics.sound3188`, `OAI.MUB6.Certificate.PairSemantics.sound3189`, `OAI.MUB6.Certificate.PairSemantics.sound3191`, `OAI.MUB6.Certificate.PairSemantics.sound3192`, `OAI.MUB6.Certificate.PairSemantics.sound3193`, `OAI.MUB6.Certificate.PairSemantics.sound3194`, `OAI.MUB6.Certificate.PairSemantics.sound3195`, `OAI.MUB6.Certificate.PairSemantics.sound3196`, `OAI.MUB6.Certificate.PairSemantics.sound3197`, `OAI.MUB6.Certificate.PairSemantics.sound3198`, `OAI.MUB6.Certificate.PairSemantics.sound3199`, `OAI.MUB6.Certificate.PairSemantics.sound3200`, `OAI.MUB6.Certificate.PairSemantics.sound3201`, `OAI.MUB6.Certificate.PairSemantics.sound3202`, `OAI.MUB6.Certificate.PairSemantics.sound3203`, `OAI.MUB6.Certificate.PairSemantics.sound3204`, `OAI.MUB6.Certificate.PairSemantics.sound3205`, `OAI.MUB6.Certificate.PairSemantics.sound3206`, `OAI.MUB6.Certificate.PairSemantics.sound3208`, `OAI.MUB6.Certificate.PairSemantics.sound3211`, `OAI.MUB6.Certificate.PairSemantics.sound3212`, `OAI.MUB6.Certificate.PairSemantics.sound3213`, `OAI.MUB6.Certificate.PairSemantics.sound3214`, `OAI.MUB6.Certificate.PairSemantics.sound3215`, `OAI.MUB6.Certificate.PairSemantics.sound3216`, `OAI.MUB6.Certificate.PairSemantics.sound3217`, `OAI.MUB6.Certificate.PairSemantics.sound3218`, `OAI.MUB6.Certificate.PairSemantics.sound3219`, `OAI.MUB6.Certificate.PairSemantics.sound3221`, `OAI.MUB6.Certificate.PairSemantics.sound3222`, `OAI.MUB6.Certificate.PairSemantics.sound3223`, `OAI.MUB6.Certificate.PairSemantics.sound3224`, `OAI.MUB6.Certificate.PairSemantics.sound3226`, `OAI.MUB6.Certificate.PairSemantics.sound3227`, `OAI.MUB6.Certificate.PairSemantics.sound3228`, `OAI.MUB6.Certificate.PairSemantics.sound3230`, `OAI.MUB6.Certificate.PairSemantics.sound3231`, `OAI.MUB6.Certificate.PairSemantics.sound3233`, `OAI.MUB6.Certificate.PairSemantics.sound3234`, `OAI.MUB6.Certificate.PairSemantics.sound3235`, `OAI.MUB6.Certificate.PairSemantics.sound3237`, `OAI.MUB6.Certificate.PairSemantics.sound3238`, `OAI.MUB6.Certificate.PairSemantics.sound3239`, `OAI.MUB6.Certificate.PairSemantics.sound3240`, `OAI.MUB6.Certificate.PairSemantics.sound3241`, `OAI.MUB6.Certificate.PairSemantics.sound3242`, `OAI.MUB6.Certificate.PairSemantics.sound3243`, `OAI.MUB6.Certificate.PairSemantics.sound3244`, `OAI.MUB6.Certificate.PairSemantics.sound3246`, `OAI.MUB6.Certificate.PairSemantics.sound3247`, `OAI.MUB6.Certificate.PairSemantics.sound3248`, `OAI.MUB6.Certificate.PairSemantics.sound3249`, `OAI.MUB6.Certificate.PairSemantics.sound3250`, `OAI.MUB6.Certificate.PairSemantics.sound3251`, `OAI.MUB6.Certificate.PairSemantics.sound3253`, `OAI.MUB6.Certificate.PairSemantics.sound3254`, `OAI.MUB6.Certificate.PairSemantics.sound3255`, `OAI.MUB6.Certificate.PairSemantics.sound3256`, `OAI.MUB6.Certificate.PairSemantics.sound3258`, `OAI.MUB6.Certificate.PairSemantics.sound3259`, `OAI.MUB6.Certificate.PairSemantics.sound3261`, `OAI.MUB6.Certificate.PairSemantics.sound3262`, `OAI.MUB6.Certificate.PairSemantics.sound3263`, `OAI.MUB6.Certificate.PairSemantics.sound3266`, `OAI.MUB6.Certificate.PairSemantics.sound3267`, `OAI.MUB6.Certificate.PairSemantics.sound3268`, `OAI.MUB6.Certificate.PairSemantics.sound3269`, `OAI.MUB6.Certificate.PairSemantics.sound3270`, `OAI.MUB6.Certificate.PairSemantics.sound3271`, `OAI.MUB6.Certificate.PairSemantics.sound3273`, `OAI.MUB6.Certificate.PairSemantics.sound3275`, `OAI.MUB6.Certificate.PairSemantics.sound3276`, `OAI.MUB6.Certificate.PairSemantics.sound3277`, `OAI.MUB6.Certificate.PairSemantics.sound3279`, `OAI.MUB6.Certificate.PairSemantics.sound3280`, `OAI.MUB6.Certificate.PairSemantics.sound3281`, `OAI.MUB6.Certificate.PairSemantics.sound3282`, `OAI.MUB6.Certificate.PairSemantics.sound3283`, `OAI.MUB6.Certificate.PairSemantics.sound3284`, `OAI.MUB6.Certificate.PairSemantics.sound3288`, `OAI.MUB6.Certificate.PairSemantics.sound3289`, `OAI.MUB6.Certificate.PairSemantics.sound3290`, `OAI.MUB6.Certificate.PairSemantics.sound3291`, `OAI.MUB6.Certificate.PairSemantics.sound3292`, `OAI.MUB6.Certificate.PairSemantics.sound3293`, `OAI.MUB6.Certificate.PairSemantics.sound3294`, `OAI.MUB6.Certificate.PairSemantics.sound3295`, `OAI.MUB6.Certificate.PairSemantics.sound3296`, `OAI.MUB6.Certificate.PairSemantics.sound3297`, `OAI.MUB6.Certificate.PairSemantics.sound3298`, `OAI.MUB6.Certificate.PairSemantics.sound3299`, `OAI.MUB6.Certificate.PairSemantics.sound3300`, `OAI.MUB6.Certificate.PairSemantics.sound3301`, `OAI.MUB6.Certificate.PairSemantics.sound3302`, `OAI.MUB6.Certificate.PairSemantics.sound3304`, `OAI.MUB6.Certificate.PairSemantics.sound3305`, `OAI.MUB6.Certificate.PairSemantics.sound3307`, `OAI.MUB6.Certificate.PairSemantics.sound3308`, `OAI.MUB6.Certificate.PairSemantics.sound3310`, `OAI.MUB6.Certificate.PairSemantics.sound3311`, `OAI.MUB6.Certificate.PairSemantics.sound3312`, `OAI.MUB6.Certificate.PairSemantics.sound3313`, `OAI.MUB6.Certificate.PairSemantics.sound3314`, `OAI.MUB6.Certificate.PairSemantics.sound3315`, `OAI.MUB6.Certificate.PairSemantics.sound3316`, `OAI.MUB6.Certificate.PairSemantics.sound3317`, `OAI.MUB6.Certificate.PairSemantics.sound3319`, `OAI.MUB6.Certificate.PairSemantics.sound3322`, `OAI.MUB6.Certificate.PairSemantics.sound3323`, `OAI.MUB6.Certificate.PairSemantics.sound3324`, `OAI.MUB6.Certificate.PairSemantics.sound3325`, `OAI.MUB6.Certificate.PairSemantics.sound3327`, `OAI.MUB6.Certificate.PairSemantics.sound3328`, `OAI.MUB6.Certificate.PairSemantics.sound3332`, `OAI.MUB6.Certificate.PairSemantics.sound3333`, `OAI.MUB6.Certificate.PairSemantics.sound3334`, `OAI.MUB6.Certificate.PairSemantics.sound3335`, `OAI.MUB6.Certificate.PairSemantics.sound3336`, `OAI.MUB6.Certificate.PairSemantics.sound3338`, `OAI.MUB6.Certificate.PairSemantics.sound3340`, `OAI.MUB6.Certificate.PairSemantics.sound3341`, `OAI.MUB6.Certificate.PairSemantics.sound3342`, `OAI.MUB6.Certificate.PairSemantics.sound3343`, `OAI.MUB6.Certificate.PairSemantics.sound3344`, `OAI.MUB6.Certificate.PairSemantics.sound3345`, `OAI.MUB6.Certificate.PairSemantics.sound3346`, `OAI.MUB6.Certificate.PairSemantics.sound3347`, `OAI.MUB6.Certificate.PairSemantics.sound3348`, `OAI.MUB6.Certificate.PairSemantics.sound3349`, `OAI.MUB6.Certificate.PairSemantics.sound3350`, `OAI.MUB6.Certificate.PairSemantics.sound3351`, `OAI.MUB6.Certificate.PairSemantics.sound3352`, `OAI.MUB6.Certificate.PairSemantics.sound3353`, `OAI.MUB6.Certificate.PairSemantics.sound3354`, `OAI.MUB6.Certificate.PairSemantics.sound3355`, `OAI.MUB6.Certificate.PairSemantics.sound3356`, `OAI.MUB6.Certificate.PairSemantics.sound3357`, `OAI.MUB6.Certificate.PairSemantics.sound3359`, `OAI.MUB6.Certificate.PairSemantics.sound3360`, `OAI.MUB6.Certificate.PairSemantics.sound3361`, `OAI.MUB6.Certificate.PairSemantics.sound3362`, `OAI.MUB6.Certificate.PairSemantics.sound3364`, `OAI.MUB6.Certificate.PairSemantics.sound3365`, `OAI.MUB6.Certificate.PairSemantics.sound3366`, `OAI.MUB6.Certificate.PairSemantics.sound3367`, `OAI.MUB6.Certificate.PairSemantics.sound3369`, `OAI.MUB6.Certificate.PairSemantics.sound3370`, `OAI.MUB6.Certificate.PairSemantics.sound3371`, `OAI.MUB6.Certificate.PairSemantics.sound3372`, `OAI.MUB6.Certificate.PairSemantics.sound3373`, `OAI.MUB6.Certificate.PairSemantics.sound3375`, `OAI.MUB6.Certificate.PairSemantics.sound3376`, `OAI.MUB6.Certificate.PairSemantics.sound3377`, `OAI.MUB6.Certificate.PairSemantics.sound3378`, `OAI.MUB6.Certificate.PairSemantics.sound3380`, `OAI.MUB6.Certificate.PairSemantics.sound3381`, `OAI.MUB6.Certificate.PairSemantics.sound3382`, `OAI.MUB6.Certificate.PairSemantics.sound3383`, `OAI.MUB6.Certificate.PairSemantics.sound3384`, `OAI.MUB6.Certificate.PairSemantics.sound3385`, `OAI.MUB6.Certificate.PairSemantics.sound3388`, `OAI.MUB6.Certificate.PairSemantics.sound3390`, `OAI.MUB6.Certificate.PairSemantics.sound3391`, `OAI.MUB6.Certificate.PairSemantics.sound3392`, `OAI.MUB6.Certificate.PairSemantics.sound3393`, `OAI.MUB6.Certificate.PairSemantics.sound3394`, `OAI.MUB6.Certificate.PairSemantics.sound3395`, `OAI.MUB6.Certificate.PairSemantics.sound3396`, `OAI.MUB6.Certificate.PairSemantics.sound3399`, `OAI.MUB6.Certificate.PairSemantics.sound3400`, `OAI.MUB6.Certificate.PairSemantics.sound3401`, `OAI.MUB6.Certificate.PairSemantics.sound3402`, `OAI.MUB6.Certificate.PairSemantics.sound3405`, `OAI.MUB6.Certificate.PairSemantics.sound3407`, `OAI.MUB6.Certificate.PairSemantics.sound3408`, `OAI.MUB6.Certificate.PairSemantics.sound3411`, `OAI.MUB6.Certificate.PairSemantics.sound3412`, `OAI.MUB6.Certificate.PairSemantics.sound3413`, `OAI.MUB6.Certificate.PairSemantics.sound3414`, `OAI.MUB6.Certificate.PairSemantics.sound3415`, `OAI.MUB6.Certificate.PairSemantics.sound3416`, `OAI.MUB6.Certificate.PairSemantics.sound3417`, `OAI.MUB6.Certificate.PairSemantics.sound3418`, `OAI.MUB6.Certificate.PairSemantics.sound3420`, `OAI.MUB6.Certificate.PairSemantics.sound3421`, `OAI.MUB6.Certificate.PairSemantics.sound3422`, `OAI.MUB6.Certificate.PairSemantics.sound3423`, `OAI.MUB6.Certificate.PairSemantics.sound3424`, `OAI.MUB6.Certificate.PairSemantics.sound3425`, `OAI.MUB6.Certificate.PairSemantics.sound3426`, `OAI.MUB6.Certificate.PairSemantics.sound3428`, `OAI.MUB6.Certificate.PairSemantics.sound3431`, `OAI.MUB6.Certificate.PairSemantics.sound3433`, `OAI.MUB6.Certificate.PairSemantics.sound3434`, `OAI.MUB6.Certificate.PairSemantics.sound3435`, `OAI.MUB6.Certificate.PairSemantics.sound3436`, `OAI.MUB6.Certificate.PairSemantics.sound3437`, `OAI.MUB6.Certificate.PairSemantics.sound3438`, `OAI.MUB6.Certificate.PairSemantics.sound3439`, `OAI.MUB6.Certificate.PairSemantics.sound3440`, `OAI.MUB6.Certificate.PairSemantics.sound3441`, `OAI.MUB6.Certificate.PairSemantics.sound3445`, `OAI.MUB6.Certificate.PairSemantics.sound3447`, `OAI.MUB6.Certificate.PairSemantics.sound3449`, `OAI.MUB6.Certificate.PairSemantics.sound3454`, `OAI.MUB6.Certificate.PairSemantics.sound3456`, `OAI.MUB6.Certificate.PairSemantics.sound3457`, `OAI.MUB6.Certificate.PairSemantics.sound3458`, `OAI.MUB6.Certificate.PairSemantics.sound3459`, `OAI.MUB6.Certificate.PairSemantics.sound3460`, `OAI.MUB6.Certificate.PairSemantics.sound3461`, `OAI.MUB6.Certificate.PairSemantics.sound3462`, `OAI.MUB6.Certificate.PairSemantics.sound3463`, `OAI.MUB6.Certificate.PairSemantics.sound3467`, `OAI.MUB6.Certificate.PairSemantics.sound3468`, `OAI.MUB6.Certificate.PairSemantics.sound381`, `OAI.MUB6.Certificate.PairSemantics.sound46`, `OAI.MUB6.Certificate.PairSemantics.sound5`, `OAI.MUB6.Certificate.PairSemantics.sound545`, `OAI.MUB6.Certificate.PairSemantics.sound659`, `OAI.MUB6.Certificate.PairSemantics.sound856`, `OAI.MUB6.Certificate.PairSemantics.sound858`, `OAI.MUB6.Certificate.PairSourceBridge.allRowsSound`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound0`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound1`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound10`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound100`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound101`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound102`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound103`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound104`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound105`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound106`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound107`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound108`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound111`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound112`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound113`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound114`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound115`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound116`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound117`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound118`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound119`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound12`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound120`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound121`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound124`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound125`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound126`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound127`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound128`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound129`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound13`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound130`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound131`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound132`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound133`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound134`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound135`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound136`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound137`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound139`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound14`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound140`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound141`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound142`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound146`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound148`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound15`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound150`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound151`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound153`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound154`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound155`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound156`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound157`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound158`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound159`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound16`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound160`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound161`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound162`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound163`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound164`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound165`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound166`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound167`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound168`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound17`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound170`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound171`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound174`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound175`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound176`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound177`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound178`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound179`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound18`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound180`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound181`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound182`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound183`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound184`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound185`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound186`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound187`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound188`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound19`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound190`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound191`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound192`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound193`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound194`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound195`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound196`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound197`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound198`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound199`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound2`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound20`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound200`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound201`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound202`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound203`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound204`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound205`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound207`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound208`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound209`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound21`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound210`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound211`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound213`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound214`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound216`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound218`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound22`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound221`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound222`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound223`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound224`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound225`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound226`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound227`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound228`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound229`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound23`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound230`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound231`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound232`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound233`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound234`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound235`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound236`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound237`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound238`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound239`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound24`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound240`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound241`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound242`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound243`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound244`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound245`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound246`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound248`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound249`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound25`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound250`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound253`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound254`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound26`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound27`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound28`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound3`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound30`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound31`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound32`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound34`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound35`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound36`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound38`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound39`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound4`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound40`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound41`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound42`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound43`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound44`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound45`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound46`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound47`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound49`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound5`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound51`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound52`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound53`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound54`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound56`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound57`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound58`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound59`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound6`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound60`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound61`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound62`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound63`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound64`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound65`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound66`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound67`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound69`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound70`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound72`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound74`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound76`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound77`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound78`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound79`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound8`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound80`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound81`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound82`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound83`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound84`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound85`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound86`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound87`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound89`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound9`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound90`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound91`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound92`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound93`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound94`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound95`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound96`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound97`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound98`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound99`, `OAI.MUB6.Certificate.PairTargetSemantics.partition12`, `OAI.MUB6.Certificate.PairTargetSemantics.partition16`, `OAI.MUB6.Certificate.PairTargetSemantics.partition19`, `OAI.MUB6.Certificate.PairTargetSemantics.partition24`, `OAI.MUB6.Certificate.PairTargetSemantics.partition25`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm11`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm18`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm21`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm23`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm26`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm6`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm7`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm8` and `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm9`.
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

def raw8step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 0, 1], ![-4, 3, 1]]

def raw8step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]

def raw9 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]

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

def raw88step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![1, 0, -1], ![1, 3, -4]]

def raw89 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]

def raw89step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 0, -1], ![1, 3, -4]]

def raw90 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]

def raw90step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 3, -4]]

def raw91 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]

def raw91step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-2, -1, 3], ![-3, 3, 0]]

def raw91step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]

def raw92 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]

def raw92step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]

def raw92step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]

def raw93 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]

def raw93step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-2, 2, 0], ![-3, 1, 2]]

def raw93step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]

def raw94 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw889step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![2, -2]]

def raw889step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw890 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![0, 0], ![1, -1], ![1, -1]]

def raw890step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![1, -1], ![1, -1]]

def raw890step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

def raw891 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![0, 0], ![2, -2]]

def raw891step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![2, -2]]

def raw891step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw892 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![1, -1], ![0, 0], ![1, -1]]

def raw892step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![1, -1], ![1, -1]]

def raw892step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

def raw893 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![1, -1], ![1, -1]]

def raw893step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

def raw894 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![1, -1], ![1, -1], ![0, 0]]

def raw894step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![1, -1], ![1, -1]]

def raw894step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

def raw895 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![2, -2]]

def raw895step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical278
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8897step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def raw8898 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-2, 3, -1, 0], ![2, -2, -1, 1]]

def raw8898step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 3, -2], ![2, -1, -1], ![-1, 0, 1]]

def raw8898step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, -3, 2], ![-2, 1, 1], ![1, 0, -1]]

def raw8898step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

def raw8899 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-2, 3, 0, -1], ![2, -2, -2, 2]]

def raw8899step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 3, -2], ![2, 0, -2], ![-1, -1, 2]]

def raw8899step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, -3, 2], ![-2, 0, 2], ![1, 1, -2]]

def raw8899step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

def raw8900 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-2, 4, -1, -1], ![2, -3, -1, 2]]

def raw8900step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 4, -3], ![2, -1, -1], ![-1, -1, 2]]

def raw8900step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, -4, 3], ![-2, 1, 1], ![1, 1, -2]]

def raw8900step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -2, 1], ![1, 3, -4]]

def raw8901 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-1, -2, 2, 1], ![1, 3, -4, 0]]

def raw8901step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -2, 3], ![2, 2, -4], ![-1, 1, 0]]

def raw8901step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![1, 2, -3], ![-2, -2, 4], ![1, -1, 0]]

def raw8901step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw8902 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-1, -1, -2, 4], ![1, 2, 0, -3]]

def raw8902step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![2, -2, 0], ![-1, 4, -3]]

def raw8902step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![1, 1, -2], ![-2, 2, 0], ![1, -4, 3]]

def raw8902step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -2, 1], ![1, 3, -4]]

def raw8903 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-1, -1, -1, 3], ![1, 2, -1, -2]]

def raw8903step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![2, -1, -1], ![-1, 3, -2]]

def raw8903step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![1, 1, -2], ![-2, 1, 1], ![1, -3, 2]]

def raw8903step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

def raw8904 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-1, -1, 3, -1], ![1, 2, -5, 2]]

def raw8904step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![2, 3, -5], ![-1, -1, 2]]

def raw8904step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![1, 1, -2], ![-2, -3, 5], ![1, 1, -2]]

def raw8904step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

def raw8905 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-1, 0, -1, 2], ![0, 2, 1, -3], ![1, -1, -2, 2]]

def raw8905step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, -1, -2, 2]]

def raw8906 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-1, 0, 1, 0], ![0, 2, 0, -2], ![1, -1, -3, 3]]

def raw8906step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![2, 1, 0, -3], ![-1, 0, -2, 3]]

def raw8906step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, 0, -2, 1], ![-2, -1, 0, 3], ![1, 0, 2, -3]]

def raw8906step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def raw8907 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-1, 1, -3, 3], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw8907step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, 1, -1], ![2, -3, 1, 0], ![-1, 3, -2, 0]]

def raw8907step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw8908 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-1, 1, 0, 0], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw8908step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, 1, -1], ![2, 0, 0, -2], ![-1, 0, -1, 2]]

def raw8908step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, -1, -1, 1], ![-2, 0, 0, 2], ![1, 0, 1, -2]]

def raw8908step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw8909 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-1, 2, 0, -1], ![1, -1, -2, 2]]

def raw8909step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 2, -1], ![2, 0, -2], ![-1, -1, 2]]

def raw8909step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![1, -2, 1], ![-2, 0, 2], ![1, 1, -2]]

def raw8909step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw8910 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-1, 2, 1, -2], ![1, -1, -3, 3]]

def raw8910step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 2, -1], ![2, 1, -3], ![-1, -2, 3]]

def raw8910step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![1, -2, 1], ![-2, -1, 3], ![1, 2, -3]]

def raw8910step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

def raw8911 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-1, 3, -1, -1], ![1, -2, -1, 2]]

def raw8911step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 3, -2], ![2, -1, -1], ![-1, -1, 2]]

def raw8911step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![1, -3, 2], ![-2, 1, 1], ![1, 1, -2]]

def raw8911step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

def raw8912 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-1, 3, 0, -2], ![1, -2, -2, 3]]

def raw8912step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 3, -2], ![2, 0, -2], ![-1, -2, 3]]

def raw8912step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![1, -3, 2], ![-2, 0, 2], ![1, 2, -3]]

def raw8912step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -3, 2], ![1, 2, -3]]

def raw8913 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-1, 4, -1, -2], ![1, -3, -1, 3]]

def raw8913step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 4, -3], ![2, -1, -1], ![-1, -2, 3]]

def raw8913step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![1, -4, 3], ![-2, 1, 1], ![1, 2, -3]]

def raw8913step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -3, 2], ![1, 3, -4]]

def raw8914 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![0, -1, -3, 4], ![0, 2, 1, -3]]

def raw8914step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, -2, 1], ![0, 1, 3, -4], ![0, -2, -1, 3]]

def raw8914step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -2, 1], ![1, 3, -4], ![-2, -1, 3]]

def raw8914step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -2, 1], ![1, 3, -4]]

def raw8915 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 2, -1], ![0, 0, -1, 1], ![-1, 2, 1, -2], ![1, -1, -2, 2]]

def raw8915step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -2, 1], ![0, 0, 1, -1], ![1, -2, -1, 2], ![-1, 1, 2, -2]]

def raw8915step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -2, 2, -1]]

def raw8916 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 2, -1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![0, -1, -2, 3]]

def raw8916step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -2, 1], ![0, 0, 1, -1], ![0, -2, -1, 3], ![0, 1, 2, -3]]

def raw8916step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![0, 1, -1], ![-2, -1, 3], ![1, 2, -3]]

def raw8916step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

def raw8917 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 2, -1], ![0, 0, 1, -1], ![-1, 2, 0, -1], ![1, -1, -3, 3]]

def raw8917step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![2, 1, 0, -3], ![-1, -1, -1, 3]]

def raw8917step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, 0, -2, 1], ![-2, -1, 0, 3], ![1, 1, 1, -3]]

def raw8917step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 1, 1, -3]]

def raw8918 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![0, -1, -3, 4]]

def raw8918step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -2, 1], ![0, 0, -1, 1], ![0, -2, 0, 2], ![0, 1, 3, -4]]

def raw8918step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![-2, 0, 2], ![1, 3, -4]]

def raw8918step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -2, 1], ![1, 3, -4]]

def raw8919 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 2, -1], ![0, 1, -3, 2], ![-1, 1, 1, -1], ![1, -1, 0, 0]]

def raw8919step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw8920 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 2, -1], ![0, 1, -3, 2], ![0, 1, 1, -2], ![0, -1, 0, 1]]

def raw8920step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -2, 1], ![0, -1, 3, -2], ![0, -1, -1, 2], ![0, 1, 0, -1]]

def raw8920step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![-1, 3, -2], ![-1, -1, 2], ![1, 0, -1]]

def raw8920step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

def raw8921 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 2, -1], ![0, 1, 0, -1], ![-1, 1, 0, 0], ![1, -1, -2, 2]]

def raw8921step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 1, -1], ![2, 0, 0, -2], ![-1, -1, 0, 2]]

def raw8921step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, -1, -1, 1], ![-2, 0, 0, 2], ![1, 1, 0, -2]]

def raw8921step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw8922 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![0, -1, -2, 3]]

def raw8922step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![-1, -2, 3]]

def raw8922step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw8923 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![0, 2, 0, -2], ![0, -1, -2, 3]]

def raw8923step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 2, -1], ![2, 0, -2], ![-1, -2, 3]]

def raw8923step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]

def raw8924 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![0, 2, 1, -3], ![0, -1, -3, 4]]

def raw8924step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, -2, 1], ![0, -2, -1, 3], ![0, 1, 3, -4]]

def raw8924step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -2, 1], ![-2, -1, 3], ![1, 3, -4]]

def raw8924step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -2, 1], ![1, 3, -4]]

def raw8925 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![1, -3, 0, 2], ![-1, 4, -2, -1]]

def raw8925step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -3, 4], ![2, 0, -2], ![-1, 2, -1]]

def raw8925step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![1, 3, -4], ![-2, 0, 2], ![1, -2, 1]]

def raw8925step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -2, 1], ![1, 3, -4]]

def raw8926 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![1, -2, 1, 0], ![-1, 3, -3, 1]]

def raw8926step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -2, 3], ![2, 1, -3], ![-1, 0, 1]]

def raw8926step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]

def raw8927 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![1, -1, 0, 0], ![-1, 2, -2, 1]]

def raw8927step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -1, 2], ![2, 0, -2], ![-1, 0, 1]]

def raw8927step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical279
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8928 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![1, -1, 1, -1], ![-1, 2, -3, 2]]

def raw8928step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -1, 2], ![2, 1, -3], ![-1, -1, 2]]

def raw8928step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![1, 1, -2], ![-2, -1, 3], ![1, 1, -2]]

def raw8928step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]

def raw8929 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![1, 2, 0, -3], ![-1, -1, -2, 4]]

def raw8929step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 2, -1], ![2, 0, -2], ![-1, -3, 4]]

def raw8929step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![1, -2, 1], ![-2, 0, 2], ![1, 3, -4]]

def raw8929step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -2, 1], ![1, 3, -4]]

def raw8930 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![2, -3, 0, 1], ![-2, 4, -2, 0]]

def raw8930step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![-1, -3, 4], ![2, 0, -2], ![-1, 1, 0]]

def raw8930step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![1, 3, -4], ![-2, 0, 2], ![1, -1, 0]]

def raw8930step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

def raw8931 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![2, -2, 0, 0], ![-2, 3, -2, 1]]

def raw8931step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![-1, -2, 3], ![2, 0, -2], ![-1, 0, 1]]

def raw8931step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

def raw8932 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![2, -2, 1, -1], ![-2, 3, -3, 2]]

def raw8932step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![-1, -2, 3], ![2, 1, -3], ![-1, -1, 2]]

def raw8932step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![1, 2, -3], ![-2, -1, 3], ![1, 1, -2]]

def raw8932step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 1, -2], ![1, 2, -3]]

def raw8933 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![2, -1, 0, -1], ![-2, 2, -2, 2]]

def raw8933step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![-1, -1, 2], ![2, 0, -2], ![-1, -1, 2]]

def raw8933step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![1, 1, -2], ![-2, 0, 2], ![1, 1, -2]]

def raw8933step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]

def raw8934 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![2, -1, 1, -2], ![-2, 2, -3, 3]]

def raw8934step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![-1, -1, 2], ![2, 1, -3], ![-1, -2, 3]]

def raw8934step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![1, 1, -2], ![-2, -1, 3], ![1, 2, -3]]

def raw8934step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 1, -2], ![1, 2, -3]]

def raw8935 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![3, -2, 0, -1], ![-3, 3, -2, 2]]

def raw8935step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![-1, -2, 3], ![2, 0, -2], ![-1, -1, 2]]

def raw8935step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![1, 2, -3], ![-2, 0, 2], ![1, 1, -2]]

def raw8935step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 1, -2], ![1, 2, -3]]

def raw8936 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![3, -1, 0, -2], ![-3, 2, -2, 3]]

def raw8936step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![-1, -1, 2], ![2, 0, -2], ![-1, -2, 3]]

def raw8936step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![1, 1, -2], ![-2, 0, 2], ![1, 2, -3]]

def raw8936step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 1, -2], ![1, 2, -3]]

def raw8937 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 3, -2], ![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def raw8937step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 3, -2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def raw8938 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 3, -2], ![-1, 0, -1, 2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw8938step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw8939 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 3, -2], ![-1, 2, -1, 0], ![1, -1, -2, 2]]

def raw8939step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 2, -1], ![3, -1, -2], ![-2, 0, 2]]

def raw8939step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![1, -2, 1], ![-3, 1, 2], ![2, 0, -2]]

def raw8939step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

def raw8940 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 3, -2], ![0, 0, -1, 1], ![-1, 0, -1, 2], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def raw8940step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 3, -2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def raw8941 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 3, -2], ![0, 0, -1, 1], ![-1, 2, -1, 0], ![1, -1, -1, 1]]

def raw8941step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![3, -1, -1, -1], ![-2, 1, 0, 1]]

def raw8941step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw8942 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 3, -2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 2, -1, 0], ![1, -1, 0, 0]]

def raw8942step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -3, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -2, 1, 0], ![-1, 1, 0, 0]]

def raw8942step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw8943 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 3, -2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![0, -1, 0, 1]]

def raw8943step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -3, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -2, 1, 1], ![0, 1, 0, -1]]

def raw8943step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![1, 0, -1]]

def raw8943step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]

def raw8944 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 3, -2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![0, -1, -1, 2]]

def raw8944step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -3, 2], ![0, 0, 1, -1], ![0, -2, 1, 1], ![0, 1, 1, -2]]

def raw8944step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![0, 1, -1], ![-2, 1, 1], ![1, 1, -2]]

def raw8944step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

def raw8945 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 3, -2], ![0, 2, -1, -1], ![0, -1, -2, 3]]

def raw8945step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, -3, 2], ![0, -2, 1, 1], ![0, 1, 2, -3]]

def raw8945step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 1, 1], ![1, 2, -3]]

def raw8945step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -3, 2], ![1, 2, -3]]

def raw8946 : Matrix (Fin 1) (Fin 2) ℤ := ![![0, 0]]

def raw8946step0 : Matrix (Fin 0) (Fin 2) ℤ := ![]

def raw8946step1 : Matrix (Fin 0) (Fin 1) ℤ := ![]

def raw8946step2 : Matrix (Fin 0) (Fin 0) ℤ := ![]

def raw8947 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![0, 0], ![0, 0], ![3, -3]]

def raw8947step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![0, 0], ![3, -3]]

def raw8947step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![3, -3]]

def raw8947step2 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]

def raw8948 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![0, 0], ![2, -2], ![1, -1]]

def raw8948step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![2, -2], ![1, -1]]

def raw8948step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]

def raw8948step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw8949 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![1, -1], ![0, 0], ![0, 0], ![2, -2]]

def raw8949step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![1, -1], ![0, 0], ![2, -2]]

def raw8949step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![1, -1], ![2, -2]]

def raw8949step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw8950 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![1, -1], ![0, 0], ![2, -2]]

def raw8950step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![1, -1], ![2, -2]]

def raw8950step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw8951 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

def raw8951step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

def raw8952 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![1, -1], ![1, -1], ![1, -1], ![0, 0]]

def raw8952step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

def raw8952step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

def raw8953 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![1, -1], ![2, -2]]

def raw8953step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw8954 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![1, -1], ![2, -2], ![0, 0]]

def raw8954step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![1, -1], ![2, -2]]

def raw8954step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw8955 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![2, -2], ![1, -1]]

def raw8955step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]

def raw8955step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw8956 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![3, -3]]

def raw8956step0 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]

def raw8957 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-1, 1], ![0, 0], ![0, 0], ![3, -3]]

def raw8957step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-1, 1], ![0, 0], ![3, -3]]

def raw8957step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-1, 1], ![3, -3]]

def raw8957step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]

def raw8957step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw8958 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-1, 1], ![0, 0], ![2, -2], ![1, -1]]

def raw8958step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]

def raw8958step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]

def raw8958step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw8959 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-1, 1], ![0, 0], ![3, -3]]

def raw8959step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-1, 1], ![3, -3]]

def raw8959step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]

def raw8959step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw896 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![2, -2], ![0, 0]]

def raw896step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![2, -2]]

def raw896step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw897 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![2, -2], ![0, 0], ![1, -1]]

def raw897step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![2, -2], ![1, -1]]

def raw897step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]

def raw897step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw898 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![2, -2], ![1, -1]]

def raw898step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]

def raw898step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw899 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![2, -2], ![1, -1], ![0, 0]]

def raw899step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![2, -2], ![1, -1]]

def raw899step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]

def raw899step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw900 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![3, -3]]

def raw900step0 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]

def raw901 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![3, -3], ![0, 0]]

def raw901step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![3, -3]]

def raw901step1 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]

def raw902 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![1, -1], ![2, -2]]

def raw902step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]

def raw903 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![3, -3]]

def raw903step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]

def raw904 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![0, 0], ![0, 0], ![2, -2]]

def raw904step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![0, 0], ![2, -2]]

def raw904step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![2, -2]]

def raw904step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw905 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![0, 0], ![1, -1], ![1, -1]]

def raw905step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![1, -1], ![1, -1]]

def raw905step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

def raw906 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![0, 0], ![2, -2]]

def raw906step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![2, -2]]

def raw906step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw907 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![1, -1], ![1, -1]]

def raw907step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

def raw908 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![1, -1], ![1, -1], ![0, 0]]

def raw908step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![1, -1], ![1, -1]]

def raw908step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

def raw909 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![2, -2]]

def raw909step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw910 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![2, -2], ![0, 0]]

def raw910step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![2, -2]]

def raw910step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw911 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![0, 0], ![0, 0], ![1, -1]]

def raw911step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![0, 0], ![1, -1]]

def raw911step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

def raw912 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![0, 0], ![1, -1]]

def raw912step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

def raw913 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![0, 0], ![1, -1], ![0, 0]]

def raw913step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![0, 0], ![1, -1]]

def raw913step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

def raw914 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

def raw915 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1], ![0, 0]]

def raw915step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

def raw916 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1], ![0, 0], ![0, 0]]

def raw916step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1], ![0, 0]]

def raw916step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

def raw917 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw918 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2], ![0, 0]]

def raw918step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw919 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2], ![0, 0], ![0, 0]]

def raw919step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2], ![0, 0]]

def raw919step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw920 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![0, 0], ![0, 0], ![1, -1]]

def raw920step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![0, 0], ![1, -1]]

def raw920step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![1, -1]]

def raw920step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]

def raw920step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw921 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![0, 0], ![1, -1]]

def raw921step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![1, -1]]

def raw921step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]

def raw921step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw922 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![1, -1]]

def raw922step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]

def raw922step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw923 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![1, -1], ![0, 0]]

def raw923step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![1, -1]]

def raw923step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]

def raw923step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw924 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]

def raw924step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw925 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1], ![0, 0]]

def raw925step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]

def raw925step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw926 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]

def raw927 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![3, -3], ![0, 0]]

def raw927step0 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical280
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8960 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-1, 1], ![1, -1], ![0, 0], ![2, -2]]

def raw8960step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw8960step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw8961 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw8961step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw8962 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw8962step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw8963 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-1, 1], ![1, -1], ![2, -2], ![0, 0]]

def raw8963step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw8963step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw8964 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]

def raw8964step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]

def raw8964step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw8965 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-1, 1], ![2, -2], ![1, -1], ![0, 0]]

def raw8965step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]

def raw8965step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]

def raw8965step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw8966 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-1, 1], ![3, -3]]

def raw8966step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]

def raw8966step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw8967 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![0, 0], ![-1, 1], ![3, -3]]

def raw8967step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-1, 1], ![3, -3]]

def raw8967step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]

def raw8967step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw8968 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![0, 0], ![0, 0], ![0, 0], ![2, -2]]

def raw8968step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![0, 0], ![0, 0], ![2, -2]]

def raw8968step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![0, 0], ![2, -2]]

def raw8968step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![2, -2]]

def raw8968step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

def raw8969 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![0, 0], ![0, 0], ![2, -2]]

def raw8969step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![0, 0], ![2, -2]]

def raw8969step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![2, -2]]

def raw8969step2 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

def raw8970 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![0, 0], ![0, 0], ![2, -2], ![0, 0]]

def raw8970step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![0, 0], ![0, 0], ![2, -2]]

def raw8970step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![0, 0], ![2, -2]]

def raw8970step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![2, -2]]

def raw8970step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

def raw8971 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![0, 0], ![1, -1], ![1, -1]]

def raw8971step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![1, -1], ![1, -1]]

def raw8971step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw8972 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![0, 0], ![2, -2]]

def raw8972step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![2, -2]]

def raw8972step1 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

def raw8973 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![0, 0], ![2, -2], ![0, 0]]

def raw8973step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![0, 0], ![2, -2]]

def raw8973step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![2, -2]]

def raw8973step2 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

def raw8974 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]

def raw8974step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]

def raw8974step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw8975 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![1, -1], ![-1, 1], ![2, -2], ![0, 0]]

def raw8975step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]

def raw8975step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]

def raw8975step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw8976 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![1, -1], ![0, 0], ![-1, 1], ![2, -2]]

def raw8976step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]

def raw8976step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]

def raw8976step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw8977 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![1, -1], ![0, 0], ![0, 0], ![1, -1]]

def raw8977step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![1, -1], ![0, 0], ![1, -1]]

def raw8977step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![1, -1], ![1, -1]]

def raw8977step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw8978 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![1, -1], ![0, 0], ![1, -1]]

def raw8978step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![1, -1], ![1, -1]]

def raw8978step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw8979 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![1, -1], ![1, -1]]

def raw8979step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw8980 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![1, -1], ![1, -1], ![-1, 1], ![1, -1]]

def raw8980step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![-1, 1], ![1, -1]]

def raw8980step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw8981 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![1, -1], ![1, -1], ![0, 0]]

def raw8981step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![1, -1], ![1, -1]]

def raw8981step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw8982 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![1, -1], ![1, -1], ![0, 0], ![0, 0]]

def raw8982step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![1, -1], ![1, -1], ![0, 0]]

def raw8982step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![1, -1], ![1, -1]]

def raw8982step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw8983 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![-1, 1]]

def raw8983step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![-1, 1]]

def raw8983step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw8984 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![1, -1], ![2, -2], ![-1, 1]]

def raw8984step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![2, -2], ![-1, 1]]

def raw8984step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw8985 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![2, -2]]

def raw8985step0 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

def raw8986 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![2, -2], ![-1, 1], ![1, -1]]

def raw8986step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![2, -2], ![-1, 1], ![1, -1]]

def raw8986step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw8987 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![2, -2], ![0, 0]]

def raw8987step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![2, -2]]

def raw8987step1 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

def raw8988 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![2, -2], ![0, 0], ![0, 0]]

def raw8988step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![2, -2], ![0, 0]]

def raw8988step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![2, -2]]

def raw8988step2 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

def raw8989 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![2, -2], ![0, 0], ![0, 0], ![0, 0]]

def raw8989step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![2, -2], ![0, 0], ![0, 0]]

def raw8989step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![2, -2], ![0, 0]]

def raw8989step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![2, -2]]

def raw8989step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

def raw8990 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![2, -2], ![1, -1], ![0, 0], ![-1, 1]]

def raw8990step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![2, -2], ![1, -1], ![-1, 1]]

def raw8990step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![2, -2], ![1, -1], ![-1, 1]]

def raw8990step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw8991 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-2, 2], ![0, 0], ![2, -2], ![1, -1]]

def raw8991step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]

def raw8991step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]

def raw8991step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical281
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8992 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-2, 2], ![0, 0], ![3, -3]]

def raw8992step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-2, 2], ![3, -3]]

def raw8992step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![3, -3]]

def raw8992step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw8993 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-2, 2], ![1, -1], ![0, 0], ![2, -2]]

def raw8993step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]

def raw8993step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]

def raw8993step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw8994 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]

def raw8994step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]

def raw8994step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw8995 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]

def raw8995step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]

def raw8995step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw8996 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-2, 2], ![1, -1], ![2, -2], ![0, 0]]

def raw8996step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]

def raw8996step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]

def raw8996step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw8997 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-2, 2], ![2, -2], ![0, 0], ![1, -1]]

def raw8997step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]

def raw8997step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]

def raw8997step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw8998 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]

def raw8998step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]

def raw8998step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw8999 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-2, 2], ![2, -2], ![1, -1], ![0, 0]]

def raw8999step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]

def raw8999step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]

def raw8999step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw9000 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-2, 2], ![3, -3]]

def raw9000step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![3, -3]]

def raw9000step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw9001 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![-1, 1], ![0, 0], ![3, -3]]

def raw9001step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]

def raw9001step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]

def raw9001step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

def raw9002 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]

def raw9002step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]

def raw9002step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw9003 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1]]

def raw9003step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1]]

def raw9003step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw9004 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]

def raw9004step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]

def raw9004step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

def raw9005 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![0, 0], ![-1, 1], ![3, -3]]

def raw9005step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]

def raw9005step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]

def raw9005step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

def raw9006 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![0, 0], ![0, 0], ![2, -2]]

def raw9006step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![0, 0], ![2, -2]]

def raw9006step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![2, -2]]

def raw9006step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw9006step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw9007 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![0, 0], ![1, -1], ![1, -1]]

def raw9007step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw9007step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw9008 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![0, 0], ![2, -2]]

def raw9008step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![2, -2]]

def raw9008step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw9008step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw9009 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![0, 0], ![2, -2], ![0, 0]]

def raw9009step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![0, 0], ![2, -2]]

def raw9009step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![2, -2]]

def raw9009step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw9009step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw9010 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![1, -1], ![0, 0], ![1, -1]]

def raw9010step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw9010step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw9011 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw9011step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw9012 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![0, 0]]

def raw9012step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw9012step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw9013 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![2, -2]]

def raw9013step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw9013step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw9014 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![2, -2], ![-1, 1], ![1, -1]]

def raw9014step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2], ![-1, 1], ![1, -1]]

def raw9014step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw9015 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![2, -2], ![0, 0]]

def raw9015step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![2, -2]]

def raw9015step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw9015step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw9016 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![2, -2], ![0, 0], ![0, 0]]

def raw9016step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![2, -2], ![0, 0]]

def raw9016step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![2, -2]]

def raw9016step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw9016step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw9017 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1], ![-1, 1]]

def raw9017step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2], ![1, -1], ![-1, 1]]

def raw9017step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw9018 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![0, 0], ![-1, 1], ![2, -2]]

def raw9018step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![2, -2]]

def raw9018step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw9018step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw9022 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![1, -1], ![-2, 2], ![0, 0], ![2, -2]]

def raw9022step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![1, -1], ![-2, 2], ![2, -2]]

def raw9022step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-2, 2], ![2, -2]]

def raw9022step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw9023 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![1, -1], ![-1, 1], ![-1, 1], ![2, -2]]

def raw9023step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![-1, 1], ![2, -2]]

def raw9023step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical282
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9024 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![1, -1], ![-1, 1], ![0, 0], ![1, -1]]

def raw9024step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![1, -1], ![-1, 1], ![1, -1]]

def raw9024step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![1, -1]]

def raw9024step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw9025 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![1, -1], ![-1, 1], ![1, -1]]

def raw9025step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![1, -1]]

def raw9025step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw9026 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![1, -1], ![-1, 1], ![1, -1], ![0, 0]]

def raw9026step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![1, -1], ![-1, 1], ![1, -1]]

def raw9026step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![1, -1]]

def raw9026step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw9030 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![1, -1], ![1, -1], ![-1, 1]]

def raw9030step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![1, -1], ![-1, 1]]

def raw9030step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw9031 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![1, -1], ![1, -1], ![0, 0], ![-1, 1]]

def raw9031step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![1, -1], ![1, -1], ![-1, 1]]

def raw9031step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![1, -1], ![-1, 1]]

def raw9031step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw9032 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![2, -2], ![-1, 1]]

def raw9032step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1]]

def raw9032step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw9033 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![2, -2], ![-1, 1], ![0, 0]]

def raw9033step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![2, -2], ![-1, 1]]

def raw9033step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1]]

def raw9033step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw9034 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![2, -2], ![0, 0], ![-1, 1]]

def raw9034step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![2, -2], ![-1, 1]]

def raw9034step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1]]

def raw9034step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw9035 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-2, 2], ![0, 0], ![0, 0], ![2, -2]]

def raw9035step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-2, 2], ![0, 0], ![2, -2]]

def raw9035step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-2, 2], ![2, -2]]

def raw9035step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![2, -2]]

def raw9035step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

def raw9036 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-2, 2], ![0, 0], ![2, -2]]

def raw9036step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-2, 2], ![2, -2]]

def raw9036step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![2, -2]]

def raw9036step2 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

def raw9037 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]

def raw9037step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]

def raw9037step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]

def raw9037step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw9038 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-2, 2], ![1, -1], ![0, 0], ![1, -1]]

def raw9038step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-2, 2], ![1, -1], ![1, -1]]

def raw9038step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![1, -1], ![1, -1]]

def raw9038step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw9040 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-2, 2], ![1, -1], ![1, -1], ![0, 0]]

def raw9040step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-2, 2], ![1, -1], ![1, -1]]

def raw9040step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![1, -1], ![1, -1]]

def raw9040step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw9042 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]

def raw9042step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]

def raw9042step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]

def raw9042step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw9043 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-1, 1], ![-1, 1], ![0, 0], ![2, -2]]

def raw9043step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-1, 1], ![-1, 1], ![2, -2]]

def raw9043step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![2, -2]]

def raw9043step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw9043step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw9044 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw9044step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw9044step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw9045 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-1, 1], ![-1, 1], ![2, -2]]

def raw9045step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![2, -2]]

def raw9045step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw9045step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw9047 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-1, 1], ![0, 0], ![-1, 1], ![2, -2]]

def raw9047step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-1, 1], ![-1, 1], ![2, -2]]

def raw9047step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![2, -2]]

def raw9047step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw9047step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw9050 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-1, 1], ![1, -1], ![-1, 1], ![1, -1]]

def raw9050step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![1, -1], ![-1, 1], ![1, -1]]

def raw9050step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![1, -1]]

def raw9050step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical283
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9056 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![0, 0], ![0, 0], ![0, 0], ![0, 0]]

def raw9056step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![0, 0], ![0, 0], ![0, 0]]

def raw9056step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![0, 0], ![0, 0]]

def raw9056step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![0, 0]]

def raw9056step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![0, 0], ![0, 0]]

def raw9056step4 : Matrix (Fin 1) (Fin 2) ℤ := ![![0, 0]]

def raw9056step5 : Matrix (Fin 0) (Fin 2) ℤ := ![]

def raw9056step6 : Matrix (Fin 0) (Fin 1) ℤ := ![]

def raw9056step7 : Matrix (Fin 0) (Fin 0) ℤ := ![]

def raw9060 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, -4, 4], ![0, -1, 3, -2], ![0, 1, 1, -2]]

def raw9060step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -4, 4], ![-1, 3, -2], ![1, 1, -2]]

def raw9060step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 4, -4], ![1, -2, 1]]

def raw9061 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -3, 3], ![-1, 1, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw9061step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -2, 0, 1]]

def raw9062 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -3, 3], ![-1, 1, 1, -1], ![0, 0, 2, -2], ![1, -1, 0, 0]]

def raw9062step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, -1, 0, 0]]

def raw9063 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -3, 3], ![-1, 1, 1, -1], ![0, 1, 0, -1], ![1, -2, 2, -1]]

def raw9063step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, 1, -2], ![-3, 1, 0, 2], ![3, -1, -1, -1]]

def raw9063step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 2, -3], ![1, 1, -2, 0]]

def raw9064 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -3, 3], ![-1, 1, 2, -2], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw9064step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, 1, -2], ![-3, 2, 0, 1], ![3, -2, -1, 0]]

def raw9064step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw9065 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, -3, 3], ![-1, 2, 2, -3], ![1, -2, 1, 0]]

def raw9065step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 2, -2], ![-3, 2, 1], ![3, -3, 0]]

def raw9065step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

def raw9066 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, -3, 3], ![-1, 2, 3, -4], ![1, -2, 0, 1]]

def raw9066step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 2, -2], ![-3, 3, 0], ![3, -4, 1]]

def raw9066step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 0, -1], ![1, 3, -4]]

def raw9067 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, -3, 3], ![0, -2, 1, 1], ![0, 2, 2, -4]]

def raw9067step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 3, -3], ![0, 2, -1, -1], ![0, -2, -2, 4]]

def raw9067step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-2, -2, 4]]

def raw9067step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, -1, -1]]

def raw9068 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, -3, 3], ![0, -2, 2, 0], ![0, 2, 1, -3]]

def raw9068step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 3, -3], ![0, 2, -2, 0], ![0, -2, -1, 3]]

def raw9068step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-2, -1, 3]]

def raw9068step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![2, -2, 0]]

def raw9069 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, -3, 3], ![0, -2, 3, -1], ![0, 2, 0, -2]]

def raw9069step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -3, 3], ![-2, 3, -1], ![2, 0, -2]]

def raw9069step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![2, -2, 0]]

def raw9070 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, -3, 3], ![0, -1, 2, -1], ![0, 1, 1, -2]]

def raw9070step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -3, 3], ![-1, 2, -1], ![1, 1, -2]]

def raw9070step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -2, 1]]

def raw9071 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -3, 3], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw9071step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -2, 0, 1]]

def raw9072 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -3, 3], ![0, 0, 1, -1], ![-1, 2, 0, -1], ![1, -2, 2, -1]]

def raw9072step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 2, -2], ![-3, 1, 0, 2], ![3, -1, -1, -1]]

def raw9072step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 2, -2, 0], ![1, 0, 2, -3]]

def raw9073 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -3, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 2, 0, -1], ![1, -2, 1, 0]]

def raw9073step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 2, -1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 3, -3], ![1, -2, 0, 1]]

def raw9074 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -3, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, -1, 1, 0]]

def raw9074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![-1, 1, 0]]

def raw9074step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

def raw9075 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -3, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, -1, 2, -1]]

def raw9075step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![0, 1, -1], ![1, 0, -1], ![-1, 2, -1]]

def raw9075step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

def raw9076 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -3, 3], ![0, 0, 2, -2], ![-1, 2, 0, -1], ![1, -2, 1, 0]]

def raw9076step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, -1, 0], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, -2, 0, 1]]

def raw9077 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -3, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![0, -1, 1, 0]]

def raw9077step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![0, 2, -2], ![1, 0, -1], ![-1, 1, 0]]

def raw9077step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0]]

def raw9078 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, -3, 3], ![0, 1, 2, -3], ![0, -1, 1, 0]]

def raw9078step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 3, -3], ![0, -1, -2, 3], ![0, 1, -1, 0]]

def raw9078step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![-1, -2, 3], ![1, -1, 0]]

def raw9078step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 3, -3], ![1, -1, 0]]

def raw9079 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, -3, 3], ![0, 1, 3, -4], ![0, -1, 0, 1]]

def raw9079step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 3, -3], ![0, -1, -3, 4], ![0, 1, 0, -1]]

def raw9079step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![-1, -3, 4], ![1, 0, -1]]

def raw9079step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 3, -3], ![1, 0, -1]]

def raw9080 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, -3, 3], ![0, 2, 2, -4], ![0, -2, 1, 1]]

def raw9080step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 3, -3], ![0, -2, -2, 4], ![0, 2, -1, -1]]

def raw9080step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![-2, -2, 4], ![2, -1, -1]]

def raw9080step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, -1, -1]]

def raw9081 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -2, 2], ![-1, 0, 0, 1], ![0, 2, 2, -4], ![1, -2, 0, 1]]

def raw9081step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![-2, 0, 2, 0], ![2, 1, -4, 1]]

def raw9081step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, -2, 2], ![2, 0, -2, 0], ![-2, -1, 4, -1]]

def raw9081step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw9082 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -2, 2], ![-1, 0, 1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1]]

def raw9082step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![-2, 1, 0, 1], ![2, 0, -1, -1]]

def raw9082step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw9083 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -2, 2], ![-1, 1, -1, 1], ![0, 0, 2, -2], ![1, -1, 1, -1]]

def raw9083step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, -1, 1, -1]]

def raw9084 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -2, 2], ![-1, 1, -1, 1], ![0, 0, 3, -3], ![1, -1, 0, 0]]

def raw9084step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, -1, 0, 0]]

def raw9085 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -2, 2], ![-1, 1, -1, 1], ![0, 1, 0, -1], ![1, -2, 3, -2]]

def raw9085step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, 1, -2], ![-2, -1, 0, 3], ![2, 1, -1, -2]]

def raw9085step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, -1, -1, 2], ![2, 1, 0, -3], ![-2, -1, 1, 2]]

def raw9085step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, -1, -2, 2]]

def raw9086 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, -2, 2], ![-1, 1, 0, 0], ![1, -1, 2, -2]]

def raw9086step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![-2, 0, 2], ![2, 0, -2]]

def raw9086step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

def raw9087 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -2, 2], ![-1, 1, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0]]

def raw9087step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, 0, -1], ![-2, 1, 1, 0], ![2, -1, -1, 0]]

def raw9087step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical284
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9088 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, -2, 2], ![-1, 1, 2, -2], ![1, -1, 0, 0]]

def raw9088step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![-2, 2, 0], ![2, -2, 0]]

def raw9088step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

def raw9089 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -2, 2], ![-1, 1, 3, -3], ![0, 1, 0, -1], ![1, -2, -1, 2]]

def raw9089step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, 1, -2], ![-2, 3, 0, -1], ![2, -3, -1, 2]]

def raw9089step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, -1, -1, 2], ![2, -3, 0, 1], ![-2, 3, 1, -2]]

def raw9089step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -2, -2, 3]]

def raw9090 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, -2, 2], ![-1, 2, 2, -3], ![1, -2, 0, 1]]

def raw9090step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 2, -2], ![-2, 2, 0], ![2, -3, 1]]

def raw9090step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, -2, 2], ![2, -2, 0], ![-2, 3, -1]]

def raw9090step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

def raw9091 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, -2, 2], ![-1, 2, 3, -4], ![1, -2, -1, 2]]

def raw9091step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 2, -2], ![-2, 3, -1], ![2, -4, 2]]

def raw9091step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, -2, 2], ![2, -3, 1], ![-2, 4, -2]]

def raw9091step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 2, -2], ![2, 1, -3]]

def raw9092 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, -1, 1], ![-1, 2, 0, -1], ![1, -2, 3, -2]]

def raw9092step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 2, -2], ![-2, -1, 0, 3], ![2, 1, -1, -2]]

def raw9092step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 2, -1, -2]]

def raw9093 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, -1, 1], ![-1, 2, 3, -4], ![1, -2, 0, 1]]

def raw9093step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 2, -2], ![-2, -1, 3, 0], ![2, 1, -4, 1]]

def raw9093step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -2, 2], ![2, 1, -3, 0], ![-2, -1, 4, -1]]

def raw9093step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 2, 0, -3]]

def raw9094 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-2, 2, 0, 0], ![2, -2, 1, -1]]

def raw9094step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![2, -2, 0, 0]]

def raw9095 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -2, 2, -2]]

def raw9095step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw9096 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 1, 2, -1]]

def raw9096step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, 0, 0]]

def raw9097 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![-2, 2, 0, 0], ![1, -1, 2, -2]]

def raw9097step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw9098 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 2, 2, -2]]

def raw9098step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw9099 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1], ![-2, 2, 1, -1]]

def raw9099step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw9100 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, -1, 3, -2]]

def raw9100step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 3, -2]]

def raw9100step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def raw9101 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 0, 3, -1]]

def raw9101step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 0, 0]]

def raw9102 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 1, 1, 0], ![1, -1, 2, -2]]

def raw9102step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, -2, 2], ![1, -1, 0, 0]]

def raw9103 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, 3, -2]]

def raw9103step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw9104 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 1, 1, 0], ![1, -2, 2, -1]]

def raw9104step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def raw9105 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![0, -2, 1, 1]]

def raw9105step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 2, -2], ![0, 0, 1, -1], ![0, -2, -2, 4], ![0, 2, -1, -1]]

def raw9105step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-2, -2, 4], ![2, -1, -1]]

def raw9105step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def raw9106 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 1, 1], ![0, 2, 2, -4]]

def raw9106step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 2, -2], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![2, 0, -1, -1], ![0, -2, -2, 4]]

def raw9106step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw9107 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 2, 0], ![0, 2, 1, -3]]

def raw9107step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 2, -2], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![2, 0, -2, 0], ![0, -2, -1, 3]]

def raw9107step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw9108 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, 0, 1], ![0, 1, 3, -4]]

def raw9108step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw9109 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 0, 2, -1], ![-1, 2, 1, -2]]

def raw9109step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 2, -2], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![1, 0, -2, 1], ![1, -2, -1, 2]]

def raw9109step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw9110 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 1, 1, -1], ![-1, 1, 2, -2]]

def raw9110step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw9111 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![0, 0, 2, -2], ![-2, 2, 1, -1]]

def raw9111step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw9112 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, 1, 1], ![-1, 2, 2, -3]]

def raw9112step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 2, -2], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![1, 1, -1, -1], ![1, -2, -2, 3]]

def raw9112step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw9113 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![1, -1, 1, -1]]

def raw9113step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![-2, 1, 0, 1], ![2, -1, 0, -1]]

def raw9113step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw9114 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![1, -1, 0, 0]]

def raw9114step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![-2, 1, 1, 0], ![2, -1, -1, 0]]

def raw9114step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw9115 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 0, 0]]

def raw9115step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1]]

def raw9115step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![0, 1, -1]]

def raw9115step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw9116 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -2, 0, 0]]

def raw9116step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9117 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 1, 0], ![2, -2, -1, 1]]

def raw9117step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def raw9118 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![-2, -1, 0, 3], ![1, 2, 0, -3]]

def raw9118step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 2, 0, -3]]

def raw9119 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 2, 0, 0]]

def raw9119step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical285
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9120 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![-2, 0, 0, 2], ![2, -2, 2, -2]]

def raw9120step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw9121 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![-2, 0, 1, 1], ![2, -2, 1, -1]]

def raw9121step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def raw9122 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 0, -1], ![-2, -1, 2, 1]]

def raw9122step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw9123 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, -1, 1, 2], ![1, 1, 1, -3]]

def raw9123step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw9124 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 0, -2], ![-2, -1, 2, 1]]

def raw9124step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw9125 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, -1, 1, 0]]

def raw9125step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![-1, 1, 0]]

def raw9125step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0]]

def raw9126 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, -1, 0, 3], ![2, -1, 1, -2]]

def raw9126step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, 1, -2]]

def raw9127 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, 0, 2], ![2, -2, 1, -1]]

def raw9127step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 2, -2], ![0, 0, -1, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![2, 0, 0, -2], ![-2, 2, -1, 1]]

def raw9127step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, 0, -2]]

def raw9128 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, 1, 1], ![2, -2, 0, 0]]

def raw9128step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def raw9129 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, 2, 0], ![2, -2, -1, 1]]

def raw9129step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def raw9130 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0], ![-2, -1, 2, 1]]

def raw9130step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def raw9131 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, 0, -1], ![-2, -1, 1, 2]]

def raw9131step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def raw9132 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1], ![-2, -2, 2, 2]]

def raw9132step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw9133 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, 0, -2], ![-2, -2, 1, 3]]

def raw9133step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw9134 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 1, 0, 1], ![1, -1, 1, -1]]

def raw9134step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw9135 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, 1, 0]]

def raw9135step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw9136 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![1, -2, 2, -1]]

def raw9136step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def raw9137 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 1, -1, 2], ![1, -2, 2, -1]]

def raw9137step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw9138 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![1, -2, 1, 0]]

def raw9138step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw9139 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![0, 2, 1, -3]]

def raw9139step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 2, -2], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![2, 0, 0, -2], ![0, -2, -1, 3]]

def raw9139step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw9140 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 0, -1, 2], ![-1, 2, 2, -3]]

def raw9140step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 2, -2], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![1, 0, 1, -2], ![1, -2, -2, 3]]

def raw9140step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw9141 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 1, 2], ![0, 2, 1, -3]]

def raw9141step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw9142 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 0, 2], ![-1, 2, 2, -3]]

def raw9142step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 2, -2], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, 1, 0, -2], ![1, -2, -2, 3]]

def raw9142step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw9143 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 1, 1], ![-1, 2, 1, -2]]

def raw9143step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 2, -2], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, 1, -1, -1], ![1, -2, -1, 2]]

def raw9143step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw9144 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, 0, -2], ![-2, -1, 2, 1]]

def raw9144step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw9145 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, 0, 2], ![-1, 2, 1, -2]]

def raw9145step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 2, -2], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![1, 1, 0, -2], ![1, -2, -1, 2]]

def raw9145step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw9146 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, -1, -1, 2], ![-2, 2, 2, -2]]

def raw9146step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 2, -2], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![0, 1, 1, -2], ![2, -2, -2, 2]]

def raw9146step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw9147 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, 2, 0, -2], ![-2, -1, 1, 2]]

def raw9147step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw9148 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 2, -2], ![0, 0, 0, 0]]

def raw9148step0 : Matrix (Fin 2) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 2, -2]]

def raw9148step1 : Matrix (Fin 2) (Fin 3) ℤ := ![![0, -2, 2], ![0, 2, -2]]

def raw9148step2 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

def raw9149 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 3, -3], ![-1, 2, 0, -1], ![1, -2, -1, 2]]

def raw9149step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, 0, -1], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, -2, -1, 2]]

def raw9150 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 3, -3], ![0, 1, 0, -1], ![0, -1, -1, 2]]

def raw9150step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![-1, -1, 2]]

def raw9150step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

def raw9151 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![0, 1, 3, -4]]

def raw9151step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical286
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9152 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![0, -1, 3, -2]]

def raw9152step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw9153 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, 0, 2], ![-1, 1, 3, -3]]

def raw9153step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, 0, 0], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw9154 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 1, 0, -1], ![0, -1, 2, -1]]

def raw9154step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -2, 2], ![1, 0, -1], ![-1, 2, -1]]

def raw9154step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -1, 0]]

def raw9155 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, -1, 0, 3], ![1, 0, 2, -3]]

def raw9155step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 2, -2], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![2, 1, 0, -3], ![-1, 0, -2, 3]]

def raw9155step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![2, 0, 0, -2]]

def raw9156 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![1, -1, 2, -2]]

def raw9156step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 2, -2], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![2, 0, 0, -2], ![-1, 1, -2, 2]]

def raw9156step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, 0, -2]]

def raw9157 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 2, 0]]

def raw9157step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw9158 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, -1, 2, 1]]

def raw9158step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw9159 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, -2, 0, 1], ![-2, 0, 3, -1]]

def raw9159step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 0, 0, -1]]

def raw9160 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, -1, 1, -1], ![-2, -1, 2, 1]]

def raw9160step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw9161 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, -1, 0, 3], ![1, -1, 2, -2]]

def raw9161step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def raw9162 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 0, 3, -1], ![1, -2, -1, 2]]

def raw9162step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -1, 2], ![1, 0, 0, -1]]

def raw9163 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, -1, 1, -1], ![-2, -1, 1, 2]]

def raw9163step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw9164 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1], ![-2, -2, 2, 2]]

def raw9164step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9165 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![0, 1, 2, -3]]

def raw9165step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 2, -2], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![2, 0, 0, -2], ![0, -1, -2, 3]]

def raw9165step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw9166 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, -1, 2], ![0, 0, 3, -3]]

def raw9166step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw9167 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![0, -1, 3, -2]]

def raw9167step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw9168 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 0, 2], ![-1, 1, 3, -3]]

def raw9168step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, 0, 0], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def raw9169 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, -1, 0, 3], ![0, 1, 2, -3]]

def raw9169step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 2, -2], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![2, 1, 0, -3], ![0, -1, -2, 3]]

def raw9169step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, 0, 0, -2]]

def raw9170 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, 0, 2], ![-1, 1, 2, -2]]

def raw9170step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 2, -2], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![1, 1, 0, -2], ![1, -1, -2, 2]]

def raw9170step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def raw9171 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, -1, -1, 2], ![-2, 1, 3, -2]]

def raw9171step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw9172 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![0, -2, 3, -1]]

def raw9172step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def raw9173 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-1, 1, 1, -1], ![-1, -2, 2, 1]]

def raw9173step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw9174 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -2, 0, 2], ![-2, 1, 3, -2]]

def raw9174step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw9175 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -2, 1, 1], ![-2, 1, 2, -1]]

def raw9175step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw9176 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 2, 1, -3], ![0, -2, 1, 1]]

def raw9176step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![0, -2, -1, 3], ![0, 2, -1, -1]]

def raw9176step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 2, -2], ![-2, -1, 3], ![2, -1, -1]]

def raw9176step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]

def raw9177 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 2, 2, -4], ![0, -2, 0, 2]]

def raw9177step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![0, -2, -2, 4], ![0, 2, 0, -2]]

def raw9177step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 2, -2], ![-2, -2, 4], ![2, 0, -2]]

def raw9177step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![2, 0, -2]]

def raw9178 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, -1, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-1, -1, 2, 0], ![1, 2, 1, -4]]

def raw9178step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, 0, 1, -2], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![1, 1, -2, 0], ![-1, -2, -1, 4]]

def raw9178step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw9179 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw9179step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw9180 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw9180step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw9181 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-1, -1, 1, 1], ![1, 1, 2, -4]]

def raw9181step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, 0, 1, -2], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![1, 1, -1, -1], ![-1, -1, -2, 4]]

def raw9181step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw9182 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, -1, 2], ![0, 1, 0, -1], ![1, -1, 2, -2]]

def raw9182step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 2, -2]]

def raw9183 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, -1, 2], ![0, 2, -1, -1], ![1, -2, 3, -2]]

def raw9183step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![-1, -1, -1, 3], ![1, 2, -1, -2]]

def raw9183step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, -2, 2], ![1, 1, 1, -3], ![-1, -2, 1, 2]]

def raw9183step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 1, 1, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical287
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9184 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, -1, 2], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 1, -1, 1], ![0, 1, 3, -4]]

def raw9184step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, 0, 1, -2], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![1, -1, 1, -1], ![0, -1, -3, 4]]

def raw9184step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 1, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw9185 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, -1, 2], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 1, 1], ![0, 2, 2, -4]]

def raw9185step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, 0, 1, -2], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, 1, -1, -1], ![0, -2, -2, 4]]

def raw9185step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw9186 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -2, 0, 1]]

def raw9186step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw9187 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 0, 1], ![0, 2, 1, -3], ![1, -2, 0, 1]]

def raw9187step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![-1, 0, 1, 0], ![1, 1, -3, 1]]

def raw9187step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, -2, 2], ![1, 0, -1, 0], ![-1, -1, 3, -1]]

def raw9187step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw9188 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 0, 1], ![0, 2, 2, -4], ![1, -2, -1, 2]]

def raw9188step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![-1, 0, 2, -1], ![1, 1, -4, 2]]

def raw9188step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, -2, 2], ![1, 0, -2, 1], ![-1, -1, 4, -2]]

def raw9188step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw9189 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw9189step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw9190 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1]]

def raw9190step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw9191 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw9191step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw9192 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![0, 2, 0, -2], ![1, -2, -1, 2]]

def raw9192step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -2, -1, 2]]

def raw9193 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 3, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 0, 1]]

def raw9193step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def raw9194 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -2, 3, -2]]

def raw9194step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -2, 3, -2]]

def raw9195 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw9195step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw9196 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw9196step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw9197 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-1, -1, 0, 2], ![1, 0, 3, -4]]

def raw9197step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw9198 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, -1, 1], ![0, 1, 3, -4], ![1, -2, -1, 2]]

def raw9198step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, 1, -2], ![-1, -1, 3, -1], ![1, 1, -4, 2]]

def raw9198step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, -1, -1, 2], ![1, 1, -3, 1], ![-1, -1, 4, -2]]

def raw9198step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 1, 1, -3]]

def raw9199 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 0, -1, 2], ![0, 1, 3, -4]]

def raw9199step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, -1, 1, -1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![1, 0, 1, -2], ![0, -1, -3, 4]]

def raw9199step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 1, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw9200 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 0, 2], ![0, 1, 3, -4]]

def raw9200step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw9201 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 1, -1], ![0, 1, 1, -2], ![1, -2, -1, 2]]

def raw9201step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, -1, -2, 2]]

def raw9202 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 1, -1], ![0, 1, 2, -3], ![1, -2, -2, 3]]

def raw9202step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -2, -2, 3]]

def raw9203 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 2, -2], ![0, 1, 1, -2], ![1, -2, -2, 3]]

def raw9203step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -2, -2, 3]]

def raw9204 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, -2, 3], ![0, 1, 3, -4]]

def raw9204step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 2, -3], ![0, -1, -3, 4]]

def raw9204step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 1, -1], ![1, 2, -3], ![-1, -3, 4]]

def raw9204step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![1, 2, -3]]

def raw9205 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-2, 0, 2, 0], ![1, 2, 1, -4]]

def raw9205step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 1, -2], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![2, 0, -2, 0], ![-1, -2, -1, 4]]

def raw9205step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw9206 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-2, 1, 1, 0], ![1, 1, 2, -4]]

def raw9206step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw9207 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-2, 2, 0, 0], ![1, 0, 3, -4]]

def raw9207step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 1, -2], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![2, -2, 0, 0], ![-1, 0, -3, 4]]

def raw9207step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw9208 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, -1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, -1, 1, 2], ![2, 1, 0, -3]]

def raw9208step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 1, -2], ![0, 0, -1, 1], ![0, -1, 0, 1], ![2, 1, -1, -2], ![-2, -1, 0, 3]]

def raw9208step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, 1, -1, -2]]

def raw9209 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, -1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -1, 1, -2]]

def raw9209step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 1, -2], ![0, 0, -1, 1], ![0, -1, 0, 1], ![2, -1, 0, -1], ![-2, 1, -1, 2]]

def raw9209step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw9210 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, -1, 2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 2, 1, -1]]

def raw9210step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 1, -2], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![2, -2, -1, 1]]

def raw9210step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw9211 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, 0, 1, 1], ![1, 1, 2, -4]]

def raw9211step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw9212 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, 1, 0, 1], ![1, 0, 3, -4]]

def raw9212step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw9213 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, 3, -2]]

def raw9213step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw9214 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, -1, 2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, 2, -1]]

def raw9214step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 1, -2], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![2, -1, -2, 1]]

def raw9214step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw9215 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, -1, 2], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![1, -1, 2, -2]]

def raw9215step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 1, -2], ![0, -1, 0, 1], ![-1, 0, 0, 1], ![2, -1, 0, -1], ![-1, 1, -2, 2]]

def raw9215step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical288
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9216 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, -1, 2], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![0, 2, 2, -4]]

def raw9216step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 1, -2], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![2, 0, -1, -1], ![0, -2, -2, 4]]

def raw9216step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw9217 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, -1, 2], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![0, 1, 3, -4]]

def raw9217step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw9218 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![-2, -1, 0, 3], ![2, 1, 0, -3]]

def raw9218step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, 0, -3]]

def raw9219 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 2, 0, 0]]

def raw9219step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw9220 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, 1, 0]]

def raw9220step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw9221 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 1, 1, 0]]

def raw9221step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw9222 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 2, 1, -3]]

def raw9222step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![2, 0, 0, -2], ![0, -2, -1, 3]]

def raw9222step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw9223 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1], ![0, -1, 2, -1], ![-2, 2, -2, 2]]

def raw9223step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, 1, -2, 1], ![2, -2, 2, -2]]

def raw9223step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 0, -1, 1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw9224 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-2, 2, 0, 0], ![2, -2, 1, -1]]

def raw9224step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![2, -2, 0, 0]]

def raw9225 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -2, 2, -2]]

def raw9225step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw9226 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 1, 2, -1]]

def raw9226step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, 0, 0]]

def raw9227 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![-2, 2, 0, 0], ![1, -1, 2, -2]]

def raw9227step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw9228 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 2, 2, -2]]

def raw9228step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw9229 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1], ![-2, 2, 1, -1]]

def raw9229step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw9230 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -2, 2], ![0, 0, 3, -3]]

def raw9230step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![0, 3, -3]]

def raw9230step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![3, -3]]

def raw9230step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw9231 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 0, 3, -1]]

def raw9231step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 0, 0]]

def raw9232 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 1, 1, 0], ![1, -1, 2, -2]]

def raw9232step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, -2, 2], ![1, -1, 0, 0]]

def raw9233 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, 3, -2]]

def raw9233step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw9234 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 1, 1, 0], ![1, -2, 2, -1]]

def raw9234step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def raw9235 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 1, 1], ![0, 2, 2, -4]]

def raw9235step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 2, -2], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![2, 0, -1, -1], ![0, -2, -2, 4]]

def raw9235step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw9236 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 2, 0], ![0, 2, 1, -3]]

def raw9236step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 2, -2], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![2, 0, -2, 0], ![0, -2, -1, 3]]

def raw9236step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw9237 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, 0, 1], ![0, 1, 3, -4]]

def raw9237step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw9238 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 0, 2, -1], ![-1, 2, 1, -2]]

def raw9238step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 2, -2], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![1, 0, -2, 1], ![1, -2, -1, 2]]

def raw9238step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw9239 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 1, 1, -1], ![-1, 1, 2, -2]]

def raw9239step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw9240 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, -1, 0, 0], ![0, 0, 2, -2], ![-2, 2, 1, -1]]

def raw9240step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw9241 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, 1, 1], ![-1, 2, 2, -3]]

def raw9241step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 2, -2], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![1, 1, -1, -1], ![1, -2, -2, 3]]

def raw9241step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw9242 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 0, -1, 2], ![1, -1, 0, 0], ![-1, -1, 2, 0], ![1, 2, 1, -4]]

def raw9242step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, 1, -2], ![-1, 1, 0, 0], ![1, 1, -2, 0], ![-1, -2, -1, 4]]

def raw9242step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw9243 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 0, 0, 1], ![0, 2, 2, -4], ![1, -2, 0, 1]]

def raw9243step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw9244 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 1, -1, 1], ![0, 1, 0, -1], ![1, -2, 3, -2]]

def raw9244step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -2, 3, -2]]

def raw9245 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 1, -1, 1], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw9245step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw9246 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 1, -1, 1], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw9246step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw9247 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 1, -1, 1], ![1, -1, 0, 0], ![-1, -1, 1, 1], ![1, 1, 2, -4]]

def raw9247step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![-1, 1, 0, 0], ![1, 1, -1, -1], ![-1, -1, -2, 4]]

def raw9247step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 1, 0, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical289
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9248 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![1, -1, 2, -2]]

def raw9248step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![-1, -1, 0, 2], ![1, 1, 0, -2]]

def raw9248step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 1, 0, -2]]

def raw9249 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 2, -1, 0], ![1, -2, 3, -2]]

def raw9249step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 2, -2], ![-1, -1, -1, 3], ![1, 1, 0, -2]]

def raw9249step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def raw9250 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 2, 2, -3], ![1, -2, 0, 1]]

def raw9250step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 2, -2], ![-1, -1, 2, 0], ![1, 1, -3, 1]]

def raw9250step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -2, 2], ![1, 1, -2, 0], ![-1, -1, 3, -1]]

def raw9250step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def raw9251 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 2, 3, -4], ![1, -2, -1, 2]]

def raw9251step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 2, -2], ![-1, -1, 3, -1], ![1, 1, -4, 2]]

def raw9251step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -2, 2], ![1, 1, -3, 1], ![-1, -1, 4, -2]]

def raw9251step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, 1, -3]]

def raw9252 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -1, -1, 2], ![1, -1, 0, 0], ![-2, 0, 2, 0], ![1, 2, 1, -4]]

def raw9252step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![-1, 1, 0, 0], ![2, 0, -2, 0], ![-1, -2, -1, 4]]

def raw9252step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw9253 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -1, -1, 2], ![1, -1, 0, 0], ![-2, 1, 1, 0], ![1, 1, 2, -4]]

def raw9253step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw9254 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -1, -1, 2], ![1, -1, 0, 0], ![-2, 2, 0, 0], ![1, 0, 3, -4]]

def raw9254step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![-1, 1, 0, 0], ![2, -2, 0, 0], ![-1, 0, -3, 4]]

def raw9254step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw9255 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -1, 0, 1], ![1, -1, 0, 0], ![-1, 1, -1, 1], ![0, 1, 3, -4]]

def raw9255step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw9256 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -1, 0, 1], ![1, 0, -1, 0], ![-1, -1, 1, 1], ![0, 2, 2, -4]]

def raw9256step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw9257 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -1, 1, 0], ![0, 1, 0, -1], ![-2, -1, 1, 2], ![2, 1, 0, -3]]

def raw9257step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, -1, 0, 1], ![2, 1, -1, -2], ![-2, -1, 0, 3]]

def raw9257step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, -1, -2]]

def raw9258 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -1, 1, 0], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -1, 1, -2]]

def raw9258step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, -1, 0, 1], ![2, -1, 0, -1], ![-2, 1, -1, 2]]

def raw9258step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw9259 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -1, 1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 2, 1, -1]]

def raw9259step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw9260 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 2, 0, -1], ![1, -2, 3, -2]]

def raw9260step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -2, 0, 1], ![-1, 2, -3, 2]]

def raw9260step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 2, -3, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -2, 0, 1]]

def raw9261 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 2, 2, -3], ![1, -2, 1, 0]]

def raw9261step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 2, -3, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -2, 0, 1]]

def raw9262 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 2, 3, -4], ![1, -2, 0, 1]]

def raw9262step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -2, -3, 4], ![-1, 2, 0, -1]]

def raw9262step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 2, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -2, -3, 4]]

def raw9263 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -1, 0, 1], ![-1, -1, 2, 0], ![1, 2, 1, -4]]

def raw9263step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -2, 0], ![-1, -2, -1, 4]]

def raw9263step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def raw9264 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, -1, 3, -2]]

def raw9264step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![-1, 3, -2]]

def raw9264step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw9265 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![0, -1, 1, 0]]

def raw9265step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, -2, 3], ![0, 1, -1, 0]]

def raw9265step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, -2, 3], ![1, -1, 0]]

def raw9265step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw9266 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![0, -1, 0, 1]]

def raw9266step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, -3, 4], ![0, 1, 0, -1]]

def raw9266step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, -3, 4], ![1, 0, -1]]

def raw9266step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw9267 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![0, -2, 1, 1]]

def raw9267step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -2, -2, 4], ![0, 2, -1, -1]]

def raw9267step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, -2, 4], ![2, -1, -1]]

def raw9267step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw9268 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -2, 0, 1], ![-2, 0, 2, 0], ![1, 2, 1, -4]]

def raw9268step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 2, 0, -1], ![2, 0, -2, 0], ![-1, -2, -1, 4]]

def raw9268step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, -1, 0, -1]]

def raw9269 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -2, 0, 1], ![-2, 1, 1, 0], ![1, 1, 2, -4]]

def raw9269step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def raw9270 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -2, 0, 1], ![-2, 2, 0, 0], ![1, 0, 3, -4]]

def raw9270step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![2, -2, 0, 0]]

def raw9271 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-2, -1, 2, 1], ![1, 2, 1, -4]]

def raw9271step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![2, 1, -2, -1], ![-1, -2, -1, 4]]

def raw9271step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 2, -2, -1]]

def raw9272 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-2, 0, 1, 1], ![1, 1, 2, -4]]

def raw9272step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![2, 0, -1, -1], ![-1, -1, -2, 4]]

def raw9272step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def raw9273 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-2, 0, 2, 0], ![1, 1, 1, -3]]

def raw9273step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![2, 0, -2, 0], ![-1, -1, -1, 3]]

def raw9273step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw9274 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-2, 1, 0, 1], ![1, 0, 3, -4]]

def raw9274step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw9275 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-2, 1, 1, 0], ![1, 0, 2, -3]]

def raw9275step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw9276 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-2, 2, 0, 0], ![1, -1, 3, -3]]

def raw9276step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw9277 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-1, -1, 2, 0], ![0, 2, 1, -3]]

def raw9277step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, -1, 0, 0]]

def raw9278 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, 3, -2]]

def raw9278step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -2, 3, -2]]

def raw9279 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 0, 1, -1], ![-2, 2, 0, 0], ![2, -2, 1, -1]]

def raw9279step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![-2, 2, 0, 0], ![2, -2, 1, -1]]

def raw9279step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw928 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, 4, -1], ![3, -4, 1]]

def raw928step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![4, -4], ![-1, 1]]

def raw928step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]

def raw929 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, 5, -2], ![3, -5, 2]]

def raw929step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![5, -5], ![-2, 2]]

def raw929step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![2, -2], ![3, -3]]

def raw930 : Matrix (Fin 2) (Fin 4) ℤ := ![![-2, -3, 3, 2], ![2, 3, -3, -2]]

def raw930step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-3, 3], ![3, -3], ![2, -2]]

def raw930step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![2, -2], ![3, -3]]

def raw931 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw932 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def raw933 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw934 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw935 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1]]

def raw935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw936 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]

def raw937 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 2, -2], ![0, 1, -1], ![2, -1, -1]]

def raw937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def raw938 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def raw939 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw940 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

def raw941 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw942 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 3, -3], ![2, -1, -1]]

def raw943 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![1, -1, 0], ![1, 3, -4]]

def raw944 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

def raw945 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

def raw946 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![2, 2, -4]]

def raw946step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 1, 2], ![5, -1, -4]]

def raw946step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 2, -2], ![1, 2, -3]]

def raw947 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def raw948 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical290
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9280 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -2, 2, -2]]

def raw9280step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![0, -1, 0, 1], ![2, -1, 0, -1], ![-2, 2, -2, 2]]

def raw9280step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, 0, 1], ![2, -1, 0, -1], ![-2, 2, -2, 2]]

def raw9280step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw9281 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 1, 2, -1]]

def raw9281step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 1, 2, -1]]

def raw9281step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw9282 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![-2, 2, 0, 0], ![1, -1, 2, -2]]

def raw9282step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-2, 2, 0, 0], ![1, -1, 2, -2]]

def raw9282step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9283 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 2, 2, -2]]

def raw9283step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 2, 2, -2]]

def raw9283step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9284 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, -1, 1, -1], ![-2, 2, 1, -1]]

def raw9284step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 1, -1], ![-2, 2, 1, -1]]

def raw9284step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw9285 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, 2, -1]]

def raw9285step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![2, -1, -2, 1]]

def raw9285step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![2, -1, -2, 1]]

def raw9285step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw9286 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 0, 0], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![1, -1, 2, -2]]

def raw9286step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![-1, 0, 0, 1], ![2, -1, 0, -1], ![-1, 1, -2, 2]]

def raw9286step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 0, 0, 1], ![2, -1, 0, -1], ![-1, 1, -2, 2]]

def raw9286step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -1, 2]]

def raw9287 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![-2, -1, 1, 2], ![2, 1, 0, -3]]

def raw9287step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, -1, 1], ![0, 0, 0, 0], ![2, 1, -1, -2], ![-2, -1, 0, 3]]

def raw9287step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, -1, 1], ![2, 1, -1, -2], ![-2, -1, 0, 3]]

def raw9287step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 2, -1, -2]]

def raw9288 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![-2, 1, 0, 1], ![2, -1, 1, -2]]

def raw9288step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, -1, 1], ![0, 0, 0, 0], ![2, -1, 0, -1], ![-2, 1, -1, 2]]

def raw9288step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, -1, 1], ![2, -1, 0, -1], ![-2, 1, -1, 2]]

def raw9288step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw9289 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![-2, 2, 0, 0], ![2, -2, 1, -1]]

def raw9289step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![-2, 2, 0, 0], ![2, -2, 1, -1]]

def raw9289step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw9290 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-2, 2, -1, 1], ![2, -2, 1, -1]]

def raw9290step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, -2, 1, -1]]

def raw9291 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-2, 2, 0, 0], ![2, -2, 0, 0]]

def raw9291step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw9292 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![-2, 1, 0, 1], ![2, -2, 2, -2]]

def raw9292step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def raw9293 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 0, 0], ![-2, 1, 2, -1]]

def raw9293step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw9294 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, -2, 1, 3], ![2, 1, 0, -3]]

def raw9294step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, 0, -3]]

def raw9295 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, -1, 1, 2], ![2, 0, 0, -2]]

def raw9295step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw9296 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 0, 0, 2], ![2, -1, 1, -2]]

def raw9296step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, -1, 1], ![0, -1, 0, 1], ![2, 0, 0, -2], ![-2, 1, -1, 2]]

def raw9296step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw9297 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, -1, 2], ![2, -2, 2, -2]]

def raw9297step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw9298 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -2, 1, -1]]

def raw9298step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, -1, 1], ![0, -1, 0, 1], ![2, -1, 0, -1], ![-2, 2, -1, 1]]

def raw9298step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw9299 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, -1, 1], ![-2, 1, 2, -1]]

def raw9299step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def raw9300 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 1, 1, 0]]

def raw9300step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, -1, 1], ![0, -1, 0, 1], ![-2, 2, 0, 0], ![2, -1, -1, 0]]

def raw9300step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw9301 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -2, 0, 1], ![1, 0, 0, -1], ![-2, 2, 1, -1]]

def raw9301step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 2, 0, -1], ![-1, 0, 0, 1], ![2, -2, -1, 1]]

def raw9301step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw9302 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![-2, 2, 0, 0], ![1, -1, 2, -2]]

def raw9302step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, -1, 2, -2]]

def raw9303 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, -1, 0, 0], ![-2, 2, 2, -2]]

def raw9303step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw9304 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, -1, 1, -1], ![-2, 2, 1, -1]]

def raw9304step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, -1, 1, -1]]

def raw9305 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![-2, 2, -1, 1], ![1, -1, 2, -2]]

def raw9305step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw9306 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![-2, 2, 0, 0], ![1, -1, 1, -1]]

def raw9306step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw9307 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, -1, 1], ![-2, 2, 2, -2]]

def raw9307step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw9308 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 2, 1, -1]]

def raw9308step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9309 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1], ![-2, 2, 0, 0]]

def raw9309step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw9310 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, 1, 0]]

def raw9310step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![2, -1, -1, 0]]

def raw9310step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw9311 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-1, 1, 2, -2], ![1, -2, 1, 0]]

def raw9311step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical291
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9312 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-1, 1, 3, -3], ![1, -2, 0, 1]]

def raw9312step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw9313 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, -1, 0, 1], ![-1, -1, 1, 1], ![1, 1, 2, -4]]

def raw9313step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 1, -1, -1], ![-1, -1, -2, 4]]

def raw9313step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def raw9314 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 0, 3, -1]]

def raw9314step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw9315 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![0, -2, 1, 1]]

def raw9315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![-2, 1, 1]]

def raw9315step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]

def raw9316 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![0, -2, 0, 2]]

def raw9316step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4], ![-2, 0, 2]]

def raw9316step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def raw9317 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 0, 1], ![-2, 0, 1, 1], ![1, 1, 2, -4]]

def raw9317step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 1, 2, -4]]

def raw9318 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 0, 1], ![-2, 1, 0, 1], ![1, 0, 3, -4]]

def raw9318step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def raw9319 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 0, -1], ![-2, 1, 3, -2]]

def raw9319step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def raw9320 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, -1, 1, 2], ![1, 1, 2, -4]]

def raw9320step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw9321 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![1, 0, 3, -4]]

def raw9321step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![2, 0, 0, -2], ![-1, 0, -3, 4]]

def raw9321step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw9322 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, 0, 1, 1], ![1, 0, 2, -3]]

def raw9322step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![2, 0, -1, -1], ![-1, 0, -2, 3]]

def raw9322step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 3, -2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def raw9323 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, 1, 0, 1], ![1, -1, 3, -3]]

def raw9323step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw9324 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, 1, 1, 0], ![1, -1, 2, -2]]

def raw9324step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9325 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-1, -1, 1, 1], ![0, 1, 2, -3]]

def raw9325step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw9326 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, 3, -2]]

def raw9326step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9327 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 0, 3, -1]]

def raw9327step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![2, 0, -3, 1]]

def raw9327step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw9328 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![-2, 1, 1, 0], ![1, -2, 2, -1]]

def raw9328step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def raw9329 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, -1, 2, -1]]

def raw9329step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![-1, 2, -1]]

def raw9329step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw9330 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![2, -2, 0, 0], ![-2, 0, 3, -1]]

def raw9330step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw9331 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -2, -1, 1], ![-2, 0, 3, -1]]

def raw9331step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def raw9332 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 0, 2, 0]]

def raw9332step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw9333 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -2, 0, 1], ![1, 0, 0, -1], ![-2, 1, 2, -1]]

def raw9333step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 2, 0, -1], ![-1, 0, 0, 1], ![2, -1, -2, 1]]

def raw9333step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9334 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![-2, 1, 1, 0], ![1, -1, 2, -2]]

def raw9334step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -2, 2], ![1, -1, 1, -1]]

def raw9335 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 0, 0], ![-2, 1, 3, -2]]

def raw9335step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw9336 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 1, 0, 1], ![1, -1, 2, -2]]

def raw9336step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![2, -1, 0, -1], ![-1, 1, -2, 2]]

def raw9336step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9337 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 1, 1, 0], ![1, -1, 1, -1]]

def raw9337step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw9338 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, -1, 1], ![-2, 1, 3, -2]]

def raw9338step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw9339 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, 2, -1]]

def raw9339step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw9340 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 0, 2, 0]]

def raw9340step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![2, 0, -2, 0]]

def raw9340step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw9341 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![-2, 1, 1, 0], ![1, -2, 2, -1]]

def raw9341step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw9342 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 0, 0, 2], ![1, -1, 2, -2]]

def raw9342step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 0, 0, 1], ![2, 0, 0, -2], ![-1, 1, -2, 2]]

def raw9342step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw9343 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![1, -2, 2, -1]]

def raw9343step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 0, 0, 1], ![2, -1, 0, -1], ![-1, 2, -2, 1]]

def raw9343step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical292
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9344 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 1, 1, 0], ![1, -2, 1, 0]]

def raw9344step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw9345 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![0, -1, -1, 2]]

def raw9345step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, -3, 4], ![0, 1, 1, -2]]

def raw9345step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![-1, -3, 4], ![1, 1, -2]]

def raw9345step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]

def raw9346 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![0, -2, 3, -1]]

def raw9346step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![-2, 3, -1]]

def raw9346step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw9347 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![0, -2, 1, 1]]

def raw9347step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -2, -1, 3], ![0, 2, -1, -1]]

def raw9347step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![-2, -1, 3], ![2, -1, -1]]

def raw9347step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw9348 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![0, -2, 0, 2]]

def raw9348step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -2, -2, 4], ![0, 2, 0, -2]]

def raw9348step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![-2, -2, 4], ![2, 0, -2]]

def raw9348step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw9349 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -2, 0, 1], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![0, 2, 2, -4]]

def raw9349step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 2, 0, -1], ![-1, 0, 1, 0], ![2, 0, -1, -1], ![0, -2, -2, 4]]

def raw9349step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -1, 0, -1]]

def raw9350 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -2, 0, 1], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![0, 1, 3, -4]]

def raw9350step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def raw9351 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, -1, 0, 0], ![-2, 0, 1, 1], ![0, 2, 2, -4]]

def raw9351step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![-1, 1, 0, 0], ![2, 0, -1, -1], ![0, -2, -2, 4]]

def raw9351step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw9352 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, -1, 0, 0], ![-2, 0, 2, 0], ![0, 2, 1, -3]]

def raw9352step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![-1, 1, 0, 0], ![2, 0, -2, 0], ![0, -2, -1, 3]]

def raw9352step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw9353 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, -1, 0, 0], ![-2, 1, 0, 1], ![0, 1, 3, -4]]

def raw9353step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw9354 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, -1, 0, 0], ![-1, 0, 2, -1], ![-1, 2, 1, -2]]

def raw9354step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![-1, 1, 0, 0], ![1, 0, -2, 1], ![1, -2, -1, 2]]

def raw9354step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw9355 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, -1, 0, 0], ![-1, 1, 1, -1], ![-1, 1, 2, -2]]

def raw9355step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw9356 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, -1, 0, 0], ![0, 0, 2, -2], ![-2, 2, 1, -1]]

def raw9356step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw9357 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 0, 0, -1], ![-1, -1, 1, 1], ![-1, 2, 2, -3]]

def raw9357step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![-1, 0, 0, 1], ![1, 1, -1, -1], ![1, -2, -2, 3]]

def raw9357step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw9358 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![0, -1, 0, 1], ![-1, 1, -1, 1], ![0, 1, 3, -4]]

def raw9358step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw9359 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![0, 0, -1, 1], ![-1, -1, 1, 1], ![0, 2, 2, -4]]

def raw9359step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, 0, 0]]

def raw9360 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, -1, 1], ![-2, 0, 1, 1], ![0, 2, 2, -4]]

def raw9360step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 1, 1, -1], ![2, 0, -1, -1], ![0, -2, -2, 4]]

def raw9360step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw9361 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, -1, 1], ![-2, 0, 2, 0], ![0, 2, 1, -3]]

def raw9361step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 1, 1, -1], ![2, 0, -2, 0], ![0, -2, -1, 3]]

def raw9361step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw9362 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, -1, 1], ![-2, 1, 0, 1], ![0, 1, 3, -4]]

def raw9362step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw9363 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, -1, 1], ![-1, 0, 2, -1], ![-1, 2, 1, -2]]

def raw9363step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 1, 1, -1], ![1, 0, -2, 1], ![1, -2, -1, 2]]

def raw9363step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw9364 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, -1, 1], ![-1, 1, 1, -1], ![-1, 1, 2, -2]]

def raw9364step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw9365 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, -1, 1], ![0, 0, 2, -2], ![-2, 2, 1, -1]]

def raw9365step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw9366 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![0, 2, 2, -4]]

def raw9366step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![2, 0, 0, -2], ![0, -2, -2, 4]]

def raw9366step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9367 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 1, 1], ![0, 2, 1, -3]]

def raw9367step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![2, 0, -1, -1], ![0, -2, -1, 3]]

def raw9367step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw9368 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 2, 0], ![0, 2, 0, -2]]

def raw9368step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw9369 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, -1, 2], ![0, 1, 3, -4]]

def raw9369step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw9370 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, 0, 1], ![0, 1, 2, -3]]

def raw9370step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![2, -1, 0, -1], ![0, -1, -2, 3]]

def raw9370step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9371 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 0, 1, 0], ![-1, 2, 1, -2]]

def raw9371step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw9372 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 0, 2, -1], ![-1, 2, 0, -1]]

def raw9372step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![1, 0, -2, 1], ![1, -2, 0, 1]]

def raw9372step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9373 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 1, -1, 1], ![-1, 1, 3, -3]]

def raw9373step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![-1, 1, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw9374 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 1, 0, 0], ![-1, 1, 2, -2]]

def raw9374step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9375 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 1, 1, -1], ![-1, 1, 1, -1]]

def raw9375step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, -1, 1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical293
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9376 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![0, 0, 1, -1], ![-2, 2, 1, -1]]

def raw9376step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9377 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![0, 0, 2, -2], ![-2, 2, 0, 0]]

def raw9377step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9378 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 1, 2], ![0, 2, 2, -4]]

def raw9378step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw9379 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 1, 3, -4]]

def raw9379step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![2, 0, 0, -2], ![0, -1, -3, 4]]

def raw9379step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw9380 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![0, 1, 2, -3]]

def raw9380step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![2, 0, -1, -1], ![0, -1, -2, 3]]

def raw9380step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def raw9381 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![0, 0, 3, -3]]

def raw9381step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -3, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw9382 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 1, 1], ![-1, 2, 2, -3]]

def raw9382step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, 1, -1, -1], ![1, -2, -2, 3]]

def raw9382step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw9383 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, 0, 2], ![-1, 2, 2, -3]]

def raw9383step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![1, 1, 0, -2], ![1, -2, -2, 3]]

def raw9383step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9384 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, 1, 1], ![-1, 2, 1, -2]]

def raw9384step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![1, 1, -1, -1], ![1, -2, -1, 2]]

def raw9384step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw9385 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -2, 0, 0]]

def raw9385step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -2, 0, 0]]

def raw9385step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw9386 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 1, 0], ![2, -2, -1, 1]]

def raw9386step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 0, -1, 1], ![0, -1, 0, 1], ![2, -1, -1, 0], ![-2, 2, 1, -1]]

def raw9386step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![0, -1, 0, 1], ![2, -1, -1, 0], ![-2, 2, 1, -1]]

def raw9386step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw9387 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 0, 1, -1], ![1, -1, 0, 0], ![-2, -1, 0, 3], ![1, 2, 0, -3]]

def raw9387step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![-2, -1, 0, 3], ![1, 2, 0, -3]]

def raw9387step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, -1, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def raw9388 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 2, 0, 0]]

def raw9388step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 2, 0, 0]]

def raw9388step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0]]

def raw9389 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![-2, 0, 0, 2], ![2, -2, 2, -2]]

def raw9389step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, -1, 1, 0], ![0, -1, 0, 1], ![2, 0, 0, -2], ![-2, 2, -2, 2]]

def raw9389step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![2, 0, 0, -2], ![-2, 2, -2, 2]]

def raw9389step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw9390 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![-2, 0, 1, 1], ![2, -2, 1, -1]]

def raw9390step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, -1, 1, 0], ![0, -1, 0, 1], ![2, 0, -1, -1], ![-2, 2, -1, 1]]

def raw9390step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![2, 0, -1, -1], ![-2, 2, -1, 1]]

def raw9390step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw9391 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 0, -1], ![-2, -1, 2, 1]]

def raw9391step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 0, -1], ![-2, -1, 2, 1]]

def raw9391step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw9392 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, -1, 1, 2], ![1, 1, 1, -3]]

def raw9392step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, -1, 1, 2], ![1, 1, 1, -3]]

def raw9392step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw9393 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 0, -2], ![-2, -1, 2, 1]]

def raw9393step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 0, -2], ![-2, -1, 2, 1]]

def raw9393step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw9394 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, -1, 0, 3], ![2, -1, 1, -2]]

def raw9394step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, -1, 0, 1], ![0, -1, 0, 1], ![2, 1, 0, -3], ![-2, 1, -1, 2]]

def raw9394step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![2, 1, 0, -3], ![-2, 1, -1, 2]]

def raw9394step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw9395 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, 0, 2], ![2, -2, 1, -1]]

def raw9395step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, -1, 0, 1], ![0, -1, 0, 1], ![2, 0, 0, -2], ![-2, 2, -1, 1]]

def raw9395step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![2, 0, 0, -2], ![-2, 2, -1, 1]]

def raw9395step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw9396 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, 1, 1], ![2, -2, 0, 0]]

def raw9396step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, -1, 0, 1], ![0, -1, 0, 1], ![2, 0, -1, -1], ![-2, 2, 0, 0]]

def raw9396step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![2, 0, -1, -1], ![-2, 2, 0, 0]]

def raw9396step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw9397 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, 2, 0], ![2, -2, -1, 1]]

def raw9397step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, -1, 0, 1], ![0, -1, 0, 1], ![2, 0, -2, 0], ![-2, 2, 1, -1]]

def raw9397step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![2, 0, -2, 0], ![-2, 2, 1, -1]]

def raw9397step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw9398 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0], ![-2, -1, 2, 1]]

def raw9398step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0], ![-2, -1, 2, 1]]

def raw9398step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def raw9399 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, 0, -1], ![-2, -1, 1, 2]]

def raw9399step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, 0, -1], ![-2, -1, 1, 2]]

def raw9399step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw9400 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1], ![-2, -2, 2, 2]]

def raw9400step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1], ![-2, -2, 2, 2]]

def raw9400step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw9401 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, 0, -2], ![-2, -2, 1, 3]]

def raw9401step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, 0, -2], ![-2, -2, 1, 3]]

def raw9401step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -2, -2, 3]]

def raw9402 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 1, 0, 1], ![1, -1, 1, -1]]

def raw9402step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![2, -1, 0, -1], ![-1, 1, -1, 1]]

def raw9402step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![2, -1, 0, -1], ![-1, 1, -1, 1]]

def raw9402step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw9403 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, 1, 0]]

def raw9403step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![2, -1, -1, 0]]

def raw9403step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![2, -1, -1, 0]]

def raw9403step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw9404 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![1, -2, 2, -1]]

def raw9404step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![1, -2, 2, -1]]

def raw9404step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw9405 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 1, -1, 2], ![1, -2, 2, -1]]

def raw9405step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 1, -1, 2], ![1, -2, 2, -1]]

def raw9405step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -2, -1]]

def raw9406 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![1, -2, 1, 0]]

def raw9406step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, -1, 0, 1], ![-1, 0, 0, 1], ![2, -1, 0, -1], ![-1, 2, -1, 0]]

def raw9406step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 0, 0, 1], ![2, -1, 0, -1], ![-1, 2, -1, 0]]

def raw9406step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw9407 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![0, 2, 1, -3]]

def raw9407step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![2, 0, 0, -2], ![0, -2, -1, 3]]

def raw9407step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![2, 0, 0, -2], ![0, -2, -1, 3]]

def raw9407step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical294
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9408 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 0, -1, 2], ![-1, 2, 2, -3]]

def raw9408step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![1, 0, 1, -2], ![1, -2, -2, 3]]

def raw9408step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![1, 0, 1, -2], ![1, -2, -2, 3]]

def raw9408step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw9409 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 1, 2], ![0, 2, 1, -3]]

def raw9409step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![2, 1, -1, -2], ![0, -2, -1, 3]]

def raw9409step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![2, 1, -1, -2], ![0, -2, -1, 3]]

def raw9409step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw9410 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 0, 2], ![-1, 2, 2, -3]]

def raw9410step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, 1, 0, -2], ![1, -2, -2, 3]]

def raw9410step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, 1, 0, -2], ![1, -2, -2, 3]]

def raw9410step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw9411 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 1, 1], ![-1, 2, 1, -2]]

def raw9411step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 1, 1], ![-1, 2, 1, -2]]

def raw9411step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw9412 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, 0, -2], ![-2, -1, 2, 1]]

def raw9412step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, 0, -2], ![-2, -1, 2, 1]]

def raw9412step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw9413 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, 0, 2], ![-1, 2, 1, -2]]

def raw9413step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![1, 1, 0, -2], ![1, -2, -1, 2]]

def raw9413step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![1, 1, 0, -2], ![1, -2, -1, 2]]

def raw9413step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw9414 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, -1, -1, 2], ![-2, 2, 2, -2]]

def raw9414step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![0, 1, 1, -2], ![2, -2, -2, 2]]

def raw9414step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![0, 1, 1, -2], ![2, -2, -2, 2]]

def raw9414step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw9415 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, 2, 0, -2], ![-2, -1, 1, 2]]

def raw9415step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, 2, 0, -2], ![-2, -1, 1, 2]]

def raw9415step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw9416 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw9416step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw9417 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![-1, 1, -1, 1], ![1, -1, 1, -1]]

def raw9417step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1]]

def raw9418 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![-1, 2, 1, -2], ![1, -2, -1, 2]]

def raw9418step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 2, -2], ![-1, 1, 1, -1], ![1, -1, -2, 2]]

def raw9418step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -1, 1, -1]]

def raw9419 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![-1, 2, 2, -3], ![1, -2, -2, 3]]

def raw9419step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 2, -2], ![-1, 1, 2, -2], ![1, -1, -3, 3]]

def raw9419step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -1, 2, -2]]

def raw9420 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![-2, -1, 0, 3], ![2, 1, 0, -3]]

def raw9420step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, 0, -3]]

def raw9421 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 2, 0, 0]]

def raw9421step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw9422 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, 1, 0]]

def raw9422step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![2, -1, -1, 0]]

def raw9422step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw9423 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -2, 0, 0]]

def raw9423step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -2, 0, 0]]

def raw9423step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw9424 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![-2, 1, 1, 0], ![2, -2, -1, 1]]

def raw9424step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![0, 0, 0, 0], ![0, -1, 0, 1], ![2, -1, -1, 0], ![-2, 2, 1, -1]]

def raw9424step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![0, -1, 0, 1], ![2, -1, -1, 0], ![-2, 2, 1, -1]]

def raw9424step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw9425 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![-2, -1, 0, 3], ![1, 2, 0, -3]]

def raw9425step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![-2, -1, 0, 3], ![1, 2, 0, -3]]

def raw9425step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, -1, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def raw9426 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 2, 0, 0]]

def raw9426step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 2, 0, 0]]

def raw9426step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0]]

def raw9427 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 1, 1, 0]]

def raw9427step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![0, 0, 0, 0], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![2, -1, -1, 0]]

def raw9427step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![2, -1, -1, 0]]

def raw9427step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw9428 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, -1, 1], ![1, -1, 0, 0]]

def raw9428step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0]]

def raw9429 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, -1, 1], ![-2, -1, 0, 3], ![2, 1, 0, -3]]

def raw9429step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 2, 0, -3]]

def raw9430 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![-2, -2, 0, 4], ![2, 1, 0, -3]]

def raw9430step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, 0, -3]]

def raw9431 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![-2, -1, 0, 3], ![2, 0, 0, -2]]

def raw9431step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw9432 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![-2, 1, 0, 1], ![2, -2, 0, 0]]

def raw9432step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -1, 1, 0], ![2, -1, 0, -1], ![-2, 2, 0, 0]]

def raw9432step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw9433 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![-2, 1, 1, 0], ![2, -2, -1, 1]]

def raw9433step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -1, 1, 0], ![2, -1, -1, 0], ![-2, 2, 1, -1]]

def raw9433step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw9434 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, -1, 0, 1]]

def raw9434step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1]]

def raw9434step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw9435 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, -1, 2], ![2, -2, 0, 0]]

def raw9435step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw9436 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -2, -1, 1]]

def raw9436step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def raw9437 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 1, 0], ![2, -2, -2, 2]]

def raw9437step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def raw9438 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -2, 0, 1], ![1, 0, -1, 0], ![-2, 2, 0, 0]]

def raw9438step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 2, 0, -1], ![-1, 0, 1, 0], ![2, -2, 0, 0]]

def raw9438step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw9439 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![-2, -1, 0, 3], ![1, 2, 0, -3]]

def raw9439step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 1, 1, -1], ![2, 1, 0, -3], ![-1, -2, 0, 3]]

def raw9439step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 2, 0, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical295
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9440 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, -1, 0, 0], ![-2, 2, 0, 0]]

def raw9440step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw9441 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![-2, -1, -1, 4], ![1, 2, 0, -3]]

def raw9441step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 0, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 2, -3]]

def raw9442 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![-2, -1, 0, 3], ![1, 2, -1, -2]]

def raw9442step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 2, -1, -2]]

def raw9443 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, -1, 1], ![-2, 2, 0, 0]]

def raw9443step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw9444 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 2, -1, 1]]

def raw9444step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9445 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1]]

def raw9445step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![2, -1, 0, -1]]

def raw9445step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw9446 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![-2, 0, 0, 2], ![2, -2, 2, -2]]

def raw9446step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw9447 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![-2, 0, 1, 1], ![2, -2, 1, -1]]

def raw9447step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def raw9448 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -1, 0, -1], ![-2, -1, 2, 1]]

def raw9448step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -1, -1, 0]]

def raw9449 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![-2, -1, 1, 2], ![1, 1, 1, -3]]

def raw9449step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw9450 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 0, -2], ![-2, -1, 2, 1]]

def raw9450step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw9451 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, -1, 1, 0]]

def raw9451step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0]]

def raw9451step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]

def raw9452 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, 0, 0, 2], ![2, -2, 2, -2]]

def raw9452step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def raw9453 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, 0, 1, 1], ![2, -2, 1, -1]]

def raw9453step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9454 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 0, -1], ![-2, -1, 2, 1]]

def raw9454step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw9455 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![-2, -1, 0, 3], ![2, -1, 1, -2]]

def raw9455step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 1, -2]]

def raw9456 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![-2, 0, -1, 3], ![2, -2, 2, -2]]

def raw9456step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw9457 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![-2, 0, 0, 2], ![2, -2, 1, -1]]

def raw9457step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![2, 0, 0, -2], ![-2, 2, -1, 1]]

def raw9457step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw9458 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![-2, 0, 1, 1], ![2, -2, 0, 0]]

def raw9458step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![2, 0, -1, -1], ![-2, 2, 0, 0]]

def raw9458step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw9459 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![-2, 0, 2, 0], ![2, -2, -1, 1]]

def raw9459step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![2, 0, -2, 0], ![-2, 2, 1, -1]]

def raw9459step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw9460 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0], ![-2, -1, 2, 1]]

def raw9460step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def raw9461 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 0, -1], ![-2, -1, 1, 2]]

def raw9461step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def raw9462 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1], ![-2, -2, 2, 2]]

def raw9462step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw9463 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2], ![-2, -2, 1, 3]]

def raw9463step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw9464 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 0, -1], ![-2, 1, 1, 0]]

def raw9464step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw9465 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![-2, -1, 1, 2], ![1, 1, 1, -3]]

def raw9465step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def raw9466 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 0, -2], ![-2, -1, 2, 1]]

def raw9466step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw9467 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, -1, 0, 3], ![1, 1, 1, -3]]

def raw9467step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw9468 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, -1, 1, 2], ![1, 1, 0, -2]]

def raw9468step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw9469 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, 1, 0, 1], ![1, -1, 1, -1]]

def raw9469step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw9470 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, 1, 0]]

def raw9470step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw9471 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 0, 1, 1]]

def raw9471step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical296
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9472 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, -1, -1], ![-2, -1, 2, 1]]

def raw9472step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw9473 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 0, -2], ![-2, -1, 1, 2]]

def raw9473step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw9474 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![1, -2, 2, -1]]

def raw9474step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw9475 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![-2, 1, -1, 2], ![1, -2, 2, -1]]

def raw9475step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw9476 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![1, -2, 1, 0]]

def raw9476step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw9477 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![-2, -1, 0, 3], ![2, -1, 1, -2]]

def raw9477step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 1, -2]]

def raw9478 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![-2, 0, 0, 2], ![2, -2, 1, -1]]

def raw9478step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![2, 0, 0, -2], ![-2, 2, -1, 1]]

def raw9478step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw9479 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![-2, 0, 1, 1], ![2, -2, 0, 0]]

def raw9479step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![2, 0, -1, -1], ![-2, 2, 0, 0]]

def raw9479step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw9480 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![-2, 0, 2, 0], ![2, -2, -1, 1]]

def raw9480step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![2, 0, -2, 0], ![-2, 2, 1, -1]]

def raw9480step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw9481 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![2, -1, -1, 0], ![-2, -1, 2, 1]]

def raw9481step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def raw9482 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![2, -1, 0, -1], ![-2, -1, 1, 2]]

def raw9482step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def raw9483 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![2, 0, -1, -1], ![-2, -2, 2, 2]]

def raw9483step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw9484 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![2, 0, 0, -2], ![-2, -2, 1, 3]]

end MUB6.Certificate.PairSemantics

end OAI
end


