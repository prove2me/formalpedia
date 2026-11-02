-- Prove2me | Definitions.Def_OAIQ106D048
-- name    : OAIQ106D048
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T12:24:40.512199+00:00
-- url     : https://prove2.me/theorems/9adebb29-aef6-495f-9d0f-83d724365348
-- title:
--   Definitions bundle OAIQ106D048 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 895 declarations of OpenAI's Lean: 895 definitions. The definitions and types are `OAI.MUB6.Certificate.PairSemantics.pivotMatrix3360`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix3361`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix3362`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix3363`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix3364`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix3365`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix3366`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix3367`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix3368`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix3369`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix337`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix3370`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix3371`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix3372`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix3373`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix3374`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix3375`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix3376`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix3377`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix3378`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix3379`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix338`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix3380`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix3381`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix3382`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix3383`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix3384`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix3385`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix3386`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix3387`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix3388`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix3389`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix339`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix3390`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix3391`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix3392`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix3393`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix3394`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix3395`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix3396` and 855 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_PairSemantics_Canonical0`, `MutuallyUnbiased_PairSemantics_Canonical6`, `MutuallyUnbiased_PairSemantics_Sound0`, `MutuallyUnbiased_PairSemantics_Sound1`, `MutuallyUnbiased_PairSemantics_Sound10`, `MutuallyUnbiased_PairSemantics_Sound11`, `MutuallyUnbiased_PairSemantics_Sound12`, `MutuallyUnbiased_PairSemantics_Sound13`, `MutuallyUnbiased_PairSemantics_Sound14`, `MutuallyUnbiased_PairSemantics_Sound15`, `MutuallyUnbiased_PairSemantics_Sound16`, `MutuallyUnbiased_PairSemantics_Sound17`, `MutuallyUnbiased_PairSemantics_Sound18`, `MutuallyUnbiased_PairSemantics_Sound19`, `MutuallyUnbiased_PairSemantics_Sound5`, `MutuallyUnbiased_PairSemantics_Sound52`, `MutuallyUnbiased_PairSemantics_Sound53`, `MutuallyUnbiased_PairSemantics_Sound54`, `MutuallyUnbiased_PairSemantics_Sound6`, `MutuallyUnbiased_PairSemantics_Sound8`, `MutuallyUnbiased_PairSemantics_Sound9`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1161`, `OAI.MUB6.Certificate.MixedSemantics.sound1162`, `OAI.MUB6.Certificate.MixedSemantics.sound1163`, `OAI.MUB6.Certificate.MixedSemantics.sound1164`, `OAI.MUB6.Certificate.MixedSemantics.sound1165`, `OAI.MUB6.Certificate.MixedSemantics.sound1166`, `OAI.MUB6.Certificate.MixedSemantics.sound1168`, `OAI.MUB6.Certificate.MixedSemantics.sound1170`, `OAI.MUB6.Certificate.MixedSemantics.sound1172`, `OAI.MUB6.Certificate.MixedSemantics.sound1173`, `OAI.MUB6.Certificate.MixedSemantics.sound1175`, `OAI.MUB6.Certificate.MixedSemantics.sound1265`, `OAI.MUB6.Certificate.MixedSemantics.sound1266`, `OAI.MUB6.Certificate.MixedSemantics.sound1267`, `OAI.MUB6.Certificate.MixedSemantics.sound1271`, `OAI.MUB6.Certificate.MixedSemantics.sound1298`, `OAI.MUB6.Certificate.MixedSemantics.sound1299`, `OAI.MUB6.Certificate.MixedSemantics.sound1301`, `OAI.MUB6.Certificate.MixedSemantics.sound1339`, `OAI.MUB6.Certificate.MixedSemantics.sound1340`, `OAI.MUB6.Certificate.MixedSemantics.sound1341`, `OAI.MUB6.Certificate.MixedSemantics.sound1342`, `OAI.MUB6.Certificate.MixedSemantics.sound1343`, `OAI.MUB6.Certificate.MixedSemantics.sound1344`, `OAI.MUB6.Certificate.MixedSemantics.sound1346`, `OAI.MUB6.Certificate.MixedSemantics.sound1395`, `OAI.MUB6.Certificate.MixedSemantics.sound1396`, `OAI.MUB6.Certificate.MixedSemantics.sound1397`, `OAI.MUB6.Certificate.MixedSemantics.sound1399`, `OAI.MUB6.Certificate.MixedSemantics.sound1401`, `OAI.MUB6.Certificate.MixedSemantics.sound1409`, `OAI.MUB6.Certificate.MixedSemantics.sound1410`, `OAI.MUB6.Certificate.MixedSemantics.sound1411`, `OAI.MUB6.Certificate.MixedSemantics.sound1412`, `OAI.MUB6.Certificate.MixedSemantics.sound1413`, `OAI.MUB6.Certificate.MixedSemantics.sound1414`, `OAI.MUB6.Certificate.MixedSemantics.sound1416`, `OAI.MUB6.Certificate.MixedSemantics.sound1417`, `OAI.MUB6.Certificate.MixedSemantics.sound1427`, `OAI.MUB6.Certificate.MixedSemantics.sound1441`, `OAI.MUB6.Certificate.MixedSemantics.sound1443`, `OAI.MUB6.Certificate.MixedSemantics.sound1451`, `OAI.MUB6.Certificate.MixedSemantics.sound1475`, `OAI.MUB6.Certificate.MixedSemantics.sound1477`, `OAI.MUB6.Certificate.MixedSemantics.sound1478`, `OAI.MUB6.Certificate.MixedSemantics.sound1479`, `OAI.MUB6.Certificate.MixedSemantics.sound1480`, `OAI.MUB6.Certificate.MixedSemantics.sound171`, `OAI.MUB6.Certificate.MixedSemantics.sound174`, `OAI.MUB6.Certificate.MixedSemantics.sound206`, `OAI.MUB6.Certificate.MixedSemantics.sound207`, `OAI.MUB6.Certificate.MixedSemantics.sound2357`, `OAI.MUB6.Certificate.MixedSemantics.sound2358`, `OAI.MUB6.Certificate.MixedSemantics.sound2359`, `OAI.MUB6.Certificate.MixedSemantics.sound2527`, `OAI.MUB6.Certificate.MixedSemantics.sound2530`, `OAI.MUB6.Certificate.MixedSemantics.sound2531`, `OAI.MUB6.Certificate.MixedSemantics.sound2532`, `OAI.MUB6.Certificate.MixedSemantics.sound2570`, `OAI.MUB6.Certificate.MixedSemantics.sound2572`, `OAI.MUB6.Certificate.MixedSemantics.sound2574`, `OAI.MUB6.Certificate.MixedSemantics.sound2576`, `OAI.MUB6.Certificate.MixedSemantics.sound2593`, `OAI.MUB6.Certificate.MixedSemantics.sound2594`, `OAI.MUB6.Certificate.MixedSemantics.sound2595`, `OAI.MUB6.Certificate.MixedSemantics.sound2596`, `OAI.MUB6.Certificate.MixedSemantics.sound2598`, `OAI.MUB6.Certificate.MixedSemantics.sound2599`, `OAI.MUB6.Certificate.MixedSemantics.sound2601`, `OAI.MUB6.Certificate.MixedSemantics.sound2636`, `OAI.MUB6.Certificate.MixedSemantics.sound2637`, `OAI.MUB6.Certificate.MixedSemantics.sound2638`, `OAI.MUB6.Certificate.MixedSemantics.sound2640`, `OAI.MUB6.Certificate.MixedSemantics.sound2753`, `OAI.MUB6.Certificate.MixedSemantics.sound2766`, `OAI.MUB6.Certificate.MixedSemantics.sound2828`, `OAI.MUB6.Certificate.MixedSemantics.sound2904`, `OAI.MUB6.Certificate.MixedSemantics.sound293`, `OAI.MUB6.Certificate.MixedSemantics.sound2936`, `OAI.MUB6.Certificate.MixedSemantics.sound2937`, `OAI.MUB6.Certificate.MixedSemantics.sound2939`, `OAI.MUB6.Certificate.MixedSemantics.sound294`, `OAI.MUB6.Certificate.MixedSemantics.sound2941`, `OAI.MUB6.Certificate.MixedSemantics.sound2943`, `OAI.MUB6.Certificate.MixedSemantics.sound2957`, `OAI.MUB6.Certificate.MixedSemantics.sound2958`, `OAI.MUB6.Certificate.MixedSemantics.sound2959`, `OAI.MUB6.Certificate.MixedSemantics.sound2960`, `OAI.MUB6.Certificate.MixedSemantics.sound2961`, `OAI.MUB6.Certificate.MixedSemantics.sound2963`, `OAI.MUB6.Certificate.MixedSemantics.sound2965`, `OAI.MUB6.Certificate.MixedSemantics.sound2966`, `OAI.MUB6.Certificate.MixedSemantics.sound2968`, `OAI.MUB6.Certificate.MixedSemantics.sound2969`, `OAI.MUB6.Certificate.MixedSemantics.sound2986`, `OAI.MUB6.Certificate.MixedSemantics.sound2987`, `OAI.MUB6.Certificate.MixedSemantics.sound2988`, `OAI.MUB6.Certificate.MixedSemantics.sound2990`, `OAI.MUB6.Certificate.MixedSemantics.sound2996`, `OAI.MUB6.Certificate.MixedSemantics.sound2997`, `OAI.MUB6.Certificate.MixedSemantics.sound2998`, `OAI.MUB6.Certificate.MixedSemantics.sound3003`, `OAI.MUB6.Certificate.MixedSemantics.sound3005`, `OAI.MUB6.Certificate.MixedSemantics.sound3082`, `OAI.MUB6.Certificate.MixedSemantics.sound3087`, `OAI.MUB6.Certificate.MixedSemantics.sound3088`, `OAI.MUB6.Certificate.MixedSemantics.sound3089`, `OAI.MUB6.Certificate.MixedSemantics.sound3090`, `OAI.MUB6.Certificate.MixedSemantics.sound3093`, `OAI.MUB6.Certificate.MixedSemantics.sound3094`, `OAI.MUB6.Certificate.MixedSemantics.sound3099`, `OAI.MUB6.Certificate.MixedSemantics.sound3100`, `OAI.MUB6.Certificate.MixedSemantics.sound3101`, `OAI.MUB6.Certificate.MixedSemantics.sound3102`, `OAI.MUB6.Certificate.MixedSemantics.sound3106`, `OAI.MUB6.Certificate.MixedSemantics.sound3109`, `OAI.MUB6.Certificate.MixedSemantics.sound3110`, `OAI.MUB6.Certificate.MixedSemantics.sound3116`, `OAI.MUB6.Certificate.MixedSemantics.sound3120`, `OAI.MUB6.Certificate.MixedSemantics.sound3143`, `OAI.MUB6.Certificate.MixedSemantics.sound3144`, `OAI.MUB6.Certificate.MixedSemantics.sound3178`, `OAI.MUB6.Certificate.MixedSemantics.sound3184`, `OAI.MUB6.Certificate.MixedSemantics.sound3185`, `OAI.MUB6.Certificate.MixedSemantics.sound3190`, `OAI.MUB6.Certificate.MixedSemantics.sound3191`, `OAI.MUB6.Certificate.MixedSemantics.sound3203`, `OAI.MUB6.Certificate.MixedSemantics.sound3204`, `OAI.MUB6.Certificate.MixedSemantics.sound3205`, `OAI.MUB6.Certificate.MixedSemantics.sound3206`, `OAI.MUB6.Certificate.MixedSemantics.sound3207`, `OAI.MUB6.Certificate.MixedSemantics.sound3209`, `OAI.MUB6.Certificate.MixedSemantics.sound3210`, `OAI.MUB6.Certificate.MixedSemantics.sound3211`, `OAI.MUB6.Certificate.MixedSemantics.sound3223`, `OAI.MUB6.Certificate.MixedSemantics.sound3226`, `OAI.MUB6.Certificate.MixedSemantics.sound3227`, `OAI.MUB6.Certificate.MixedSemantics.sound370`, `OAI.MUB6.Certificate.MixedSemantics.sound371`, `OAI.MUB6.Certificate.MixedSemantics.sound3711`, `OAI.MUB6.Certificate.MixedSemantics.sound3726`, `OAI.MUB6.Certificate.MixedSemantics.sound3727`, `OAI.MUB6.Certificate.MixedSemantics.sound3734`, `OAI.MUB6.Certificate.MixedSemantics.sound3735`, `OAI.MUB6.Certificate.MixedSemantics.sound3736`, `OAI.MUB6.Certificate.MixedSemantics.sound3737`, `OAI.MUB6.Certificate.MixedSemantics.sound3738`, `OAI.MUB6.Certificate.MixedSemantics.sound3739`, `OAI.MUB6.Certificate.MixedSemantics.sound3818`, `OAI.MUB6.Certificate.MixedSemantics.sound3821`, `OAI.MUB6.Certificate.MixedSemantics.sound3822`, `OAI.MUB6.Certificate.MixedSemantics.sound3823`, `OAI.MUB6.Certificate.MixedSemantics.sound3824`, `OAI.MUB6.Certificate.MixedSemantics.sound3829`, `OAI.MUB6.Certificate.MixedSemantics.sound3831`, `OAI.MUB6.Certificate.MixedSemantics.sound3847`, `OAI.MUB6.Certificate.MixedSemantics.sound3851`, `OAI.MUB6.Certificate.MixedSemantics.sound3853`, `OAI.MUB6.Certificate.MixedSemantics.sound3855`, `OAI.MUB6.Certificate.MixedSemantics.sound3856`, `OAI.MUB6.Certificate.MixedSemantics.sound3858`, `OAI.MUB6.Certificate.MixedSemantics.sound3882`, `OAI.MUB6.Certificate.MixedSemantics.sound3883`, `OAI.MUB6.Certificate.MixedSemantics.sound3887`, `OAI.MUB6.Certificate.MixedSemantics.sound3888`, `OAI.MUB6.Certificate.MixedSemantics.sound3925`, `OAI.MUB6.Certificate.MixedSemantics.sound3931`, `OAI.MUB6.Certificate.MixedSemantics.sound3933`, `OAI.MUB6.Certificate.MixedSemantics.sound3936`, `OAI.MUB6.Certificate.MixedSemantics.sound3937`, `OAI.MUB6.Certificate.MixedSemantics.sound3965`, `OAI.MUB6.Certificate.MixedSemantics.sound3966`, `OAI.MUB6.Certificate.MixedSemantics.sound3967`, `OAI.MUB6.Certificate.MixedSemantics.sound3977`, `OAI.MUB6.Certificate.MixedSemantics.sound3980`, `OAI.MUB6.Certificate.MixedSemantics.sound3984`, `OAI.MUB6.Certificate.MixedSemantics.sound3987`, `OAI.MUB6.Certificate.MixedSemantics.sound3992`, `OAI.MUB6.Certificate.MixedSemantics.sound3993`, `OAI.MUB6.Certificate.MixedSemantics.sound3994`, `OAI.MUB6.Certificate.MixedSemantics.sound3997`, `OAI.MUB6.Certificate.MixedSemantics.sound3998`, `OAI.MUB6.Certificate.MixedSemantics.sound4002`, `OAI.MUB6.Certificate.MixedSemantics.sound4003`, `OAI.MUB6.Certificate.MixedSemantics.sound4012`, `OAI.MUB6.Certificate.MixedSemantics.sound4014`, `OAI.MUB6.Certificate.MixedSemantics.sound4023`, `OAI.MUB6.Certificate.MixedSemantics.sound4026`, `OAI.MUB6.Certificate.MixedSemantics.sound4027`, `OAI.MUB6.Certificate.MixedSemantics.sound4029`, `OAI.MUB6.Certificate.MixedSemantics.sound4031`, `OAI.MUB6.Certificate.MixedSemantics.sound4032`, `OAI.MUB6.Certificate.MixedSemantics.sound4033`, `OAI.MUB6.Certificate.MixedSemantics.sound4039`, `OAI.MUB6.Certificate.MixedSemantics.sound4053`, `OAI.MUB6.Certificate.MixedSemantics.sound436`, `OAI.MUB6.Certificate.MixedSemantics.sound454`, `OAI.MUB6.Certificate.MixedSemantics.sound455`, `OAI.MUB6.Certificate.MixedSemantics.sound4623`, `OAI.MUB6.Certificate.MixedSemantics.sound4625`, `OAI.MUB6.Certificate.MixedSemantics.sound511`, `OAI.MUB6.Certificate.MixedSemantics.sound5176`, `OAI.MUB6.Certificate.MixedSemantics.sound5177`, `OAI.MUB6.Certificate.MixedSemantics.sound521`, `OAI.MUB6.Certificate.MixedSemantics.sound5293`, `OAI.MUB6.Certificate.MixedSemantics.sound5294`, `OAI.MUB6.Certificate.MixedSemantics.sound5296`, `OAI.MUB6.Certificate.MixedSemantics.sound5306`, `OAI.MUB6.Certificate.MixedSemantics.sound5310`, `OAI.MUB6.Certificate.MixedSemantics.sound5415`, `OAI.MUB6.Certificate.MixedSemantics.sound5443`, `OAI.MUB6.Certificate.MixedSemantics.sound5452`, `OAI.MUB6.Certificate.MixedSemantics.sound5453`, `OAI.MUB6.Certificate.MixedSemantics.sound5464`, `OAI.MUB6.Certificate.MixedSemantics.sound5492`, `OAI.MUB6.Certificate.MixedSemantics.sound5498`, `OAI.MUB6.Certificate.MixedSemantics.sound644`, `OAI.MUB6.Certificate.MixedSemantics.sound645`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound135`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound136`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound137`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound138`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound139`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound140`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound141`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound142`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound143`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound145`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound146`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound147`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound148`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound149`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound150`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound151`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1098`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1423`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero539`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero925`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound100`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1008`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound101`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1010`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1013`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1021`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1033`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1093`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1094`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1096`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound110`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1103`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1109`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound111`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1110`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1111`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1115`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1121`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1124`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1131`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound114`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1159`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound116`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1167`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound117`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1170`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1178`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1179`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound126`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1262`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1264`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1267`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1269`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound127`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1272`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1279`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1294`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound13`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound130`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1301`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1303`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1311`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1312`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1318`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound138`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound140`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound141`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1410`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1414`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1418`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1421`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1429`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound143`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1435`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1437`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1442`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1470`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1472`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1480`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1484`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1493`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1517`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1521`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound153`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1560`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1568`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound16`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1649`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1651`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1653`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1656`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1662`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1669`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1674`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1703`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1709`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1717`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1781`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1783`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1785`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1789`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1796`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1816`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1840`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1845`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1846`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1847`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1849`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1856`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1859`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1866`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1874`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound188`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound19`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1905`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1911`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1915`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1917`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1964`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1972`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound198`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound199`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2034`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2037`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2040`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2046`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2049`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound207`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2166`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2168`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2169`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2170`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2171`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2172`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2174`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2175`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2176`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2178`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2179`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2180`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2181`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2182`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2183`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2184`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2185`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2187`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2188`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2189`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2190`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2191`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2192`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2197`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2199`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2200`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2201`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2203`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2204`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2205`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2206`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2207`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2208`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2211`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2212`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2214`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2216`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2217`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2218`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2219`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2221`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2222`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2223`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2224`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2225`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2226`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2227`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2228`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2229`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2230`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2231`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2232`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2233`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2235`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2238`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2240`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2242`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2244`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2245`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2246`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2247`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2248`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2249`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2250`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2251`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2252`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2254`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2255`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2257`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2258`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2259`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2260`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2261`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2263`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2264`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2266`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2267`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2268`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2269`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2270`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2271`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2272`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2273`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2274`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2275`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2276`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2279`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2280`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2282`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2283`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2284`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2286`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2287`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2288`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2291`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2292`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2293`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2294`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2296`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2297`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2298`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2299`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2300`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2301`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2302`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2303`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2304`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2306`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2307`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2308`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2309`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2313`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2315`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2317`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2318`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2320`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2321`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2322`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2323`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2324`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2325`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2326`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2327`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2329`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2330`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2331`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2332`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2333`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2334`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2335`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2336`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2337`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2338`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2340`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2341`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2344`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2345`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2346`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2347`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2348`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2350`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2351`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2352`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2354`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2355`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2356`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2357`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound236`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2360`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2361`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2362`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2363`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2364`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2365`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2366`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2367`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2368`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2369`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2371`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2372`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2374`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2375`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2377`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2378`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2379`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2380`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2381`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2383`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2384`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2386`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2388`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2389`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2391`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2393`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2394`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2395`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2396`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2397`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2398`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2399`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2400`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2401`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2402`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2403`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2404`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2405`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2406`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2407`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2408`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2409`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2410`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2411`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2413`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2414`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2415`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2418`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2419`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2420`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2423`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2424`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound244`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound245`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound255`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound268`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound269`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound286`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound287`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound296`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound310`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound340`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound342`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound344`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound345`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound349`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound35`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound354`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound356`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound358`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound359`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound366`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound368`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound370`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound371`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound372`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound380`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound388`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound391`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound392`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound395`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound404`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound412`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound413`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound418`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound428`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound438`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound445`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound453`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound456`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound462`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound463`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound474`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound482`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound484`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound485`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound488`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound498`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound5`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound500`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound501`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound504`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound515`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound516`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound521`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound522`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound525`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound526`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound532`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound534`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound543`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound547`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound548`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound552`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound554`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound555`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound558`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound565`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound567`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound568`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound571`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound572`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound579`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound58`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound581`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound582`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound585`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound59`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound6`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound600`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound613`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound621`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound629`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound631`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound633`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound635`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound649`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound659`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound663`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound664`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound667`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound675`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound711`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound718`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound731`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound732`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound734`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound736`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound741`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound743`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound779`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound780`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound788`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound790`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound792`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound794`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound796`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound8`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound800`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound802`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound864`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound866`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound872`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound877`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound881`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound885`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound888`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound899`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound909`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound911`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound92`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound927`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound933`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound94`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound971`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound98`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval106`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1074`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval109`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval116`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval117`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1192`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval12`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval120`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1210`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval124`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1254`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval130`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval133`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval134`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval141`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval143`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval145`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval146`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval147`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval149`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval155`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1553`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval159`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval164`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval165`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval167`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval173`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval174`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval18`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval181`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval182`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval185`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval202`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval203`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval207`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval21`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval214`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval215`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval218`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval220`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval224`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval225`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval226`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval229`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval231`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval234`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval235`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval242`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval243`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval245`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval249`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval255`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval257`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval258`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval263`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval270`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval271`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval273`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval278`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval280`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval285`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval286`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval287`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval292`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval296`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval301`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval308`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval310`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval323`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval325`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval331`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval332`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval334`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval335`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval343`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval344`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval348`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval353`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval358`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval359`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval366`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval368`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval37`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval370`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval371`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval372`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval373`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval377`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval380`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval383`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval389`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval39`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval391`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval394`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval401`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval403`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval408`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval41`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval413`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval414`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval444`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval46`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval475`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval476`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval477`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval52`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval54`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval56`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval6`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval63`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval69`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval73`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval74`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval77`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval79`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval8`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval83`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval86`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval91`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval99`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval113`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval119`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval147`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval150`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval208`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval21`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval215`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval216`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval220`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval222`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval271`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval359`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval360`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval362`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval373`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval375`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval384`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval44`, `OAI.MUB6.Certificate.PairSemantics.boundarySound165`, `OAI.MUB6.Certificate.PairSemantics.boundarySound243`, `OAI.MUB6.Certificate.PairSemantics.boundarySound248`, `OAI.MUB6.Certificate.PairSemantics.boundarySound249`, `OAI.MUB6.Certificate.PairSemantics.boundarySound250`, `OAI.MUB6.Certificate.PairSemantics.boundarySound252`, `OAI.MUB6.Certificate.PairSemantics.boundarySound261`, `OAI.MUB6.Certificate.PairSemantics.boundarySound264`, `OAI.MUB6.Certificate.PairSemantics.boundarySound305`, `OAI.MUB6.Certificate.PairSemantics.boundarySound347`, `OAI.MUB6.Certificate.PairSemantics.boundarySound445`, `OAI.MUB6.Certificate.PairSemantics.boundarySound454`, `OAI.MUB6.Certificate.PairSemantics.boundarySound49`, `OAI.MUB6.Certificate.PairSemantics.boundarySound51`, `OAI.MUB6.Certificate.PairSemantics.boundarySound56`, `OAI.MUB6.Certificate.PairSemantics.boundarySound7`, `OAI.MUB6.Certificate.PairSemantics.boundarySound73`, `OAI.MUB6.Certificate.PairSemantics.boundarySound75`, `OAI.MUB6.Certificate.PairSemantics.boundarySound83`, `OAI.MUB6.Certificate.PairSemantics.boundarySound97`, `OAI.MUB6.Certificate.PairSemantics.sound11`, `OAI.MUB6.Certificate.PairSemantics.sound1141`, `OAI.MUB6.Certificate.PairSemantics.sound1151`, `OAI.MUB6.Certificate.PairSemantics.sound1152`, `OAI.MUB6.Certificate.PairSemantics.sound117`, `OAI.MUB6.Certificate.PairSemantics.sound1294`, `OAI.MUB6.Certificate.PairSemantics.sound1381`, `OAI.MUB6.Certificate.PairSemantics.sound1383`, `OAI.MUB6.Certificate.PairSemantics.sound1384`, `OAI.MUB6.Certificate.PairSemantics.sound1387`, `OAI.MUB6.Certificate.PairSemantics.sound1390`, `OAI.MUB6.Certificate.PairSemantics.sound1391`, `OAI.MUB6.Certificate.PairSemantics.sound1392`, `OAI.MUB6.Certificate.PairSemantics.sound1395`, `OAI.MUB6.Certificate.PairSemantics.sound1399`, `OAI.MUB6.Certificate.PairSemantics.sound1414`, `OAI.MUB6.Certificate.PairSemantics.sound1419`, `OAI.MUB6.Certificate.PairSemantics.sound1423`, `OAI.MUB6.Certificate.PairSemantics.sound1424`, `OAI.MUB6.Certificate.PairSemantics.sound1425`, `OAI.MUB6.Certificate.PairSemantics.sound1432`, `OAI.MUB6.Certificate.PairSemantics.sound1434`, `OAI.MUB6.Certificate.PairSemantics.sound1437`, `OAI.MUB6.Certificate.PairSemantics.sound1443`, `OAI.MUB6.Certificate.PairSemantics.sound1458`, `OAI.MUB6.Certificate.PairSemantics.sound1486`, `OAI.MUB6.Certificate.PairSemantics.sound1500`, `OAI.MUB6.Certificate.PairSemantics.sound1504`, `OAI.MUB6.Certificate.PairSemantics.sound1506`, `OAI.MUB6.Certificate.PairSemantics.sound1512`, `OAI.MUB6.Certificate.PairSemantics.sound1518`, `OAI.MUB6.Certificate.PairSemantics.sound1520`, `OAI.MUB6.Certificate.PairSemantics.sound1523`, `OAI.MUB6.Certificate.PairSemantics.sound1530`, `OAI.MUB6.Certificate.PairSemantics.sound1531`, `OAI.MUB6.Certificate.PairSemantics.sound1533`, `OAI.MUB6.Certificate.PairSemantics.sound1535`, `OAI.MUB6.Certificate.PairSemantics.sound1540`, `OAI.MUB6.Certificate.PairSemantics.sound1548`, `OAI.MUB6.Certificate.PairSemantics.sound1552`, `OAI.MUB6.Certificate.PairSemantics.sound1563`, `OAI.MUB6.Certificate.PairSemantics.sound1585`, `OAI.MUB6.Certificate.PairSemantics.sound1605`, `OAI.MUB6.Certificate.PairSemantics.sound1614`, `OAI.MUB6.Certificate.PairSemantics.sound1617`, `OAI.MUB6.Certificate.PairSemantics.sound1624`, `OAI.MUB6.Certificate.PairSemantics.sound1625`, `OAI.MUB6.Certificate.PairSemantics.sound1627`, `OAI.MUB6.Certificate.PairSemantics.sound1628`, `OAI.MUB6.Certificate.PairSemantics.sound1631`, `OAI.MUB6.Certificate.PairSemantics.sound1634`, `OAI.MUB6.Certificate.PairSemantics.sound1635`, `OAI.MUB6.Certificate.PairSemantics.sound1637`, `OAI.MUB6.Certificate.PairSemantics.sound1638`, `OAI.MUB6.Certificate.PairSemantics.sound1643`, `OAI.MUB6.Certificate.PairSemantics.sound1646`, `OAI.MUB6.Certificate.PairSemantics.sound1648`, `OAI.MUB6.Certificate.PairSemantics.sound1652`, `OAI.MUB6.Certificate.PairSemantics.sound1668`, `OAI.MUB6.Certificate.PairSemantics.sound1669`, `OAI.MUB6.Certificate.PairSemantics.sound1682`, `OAI.MUB6.Certificate.PairSemantics.sound1685`, `OAI.MUB6.Certificate.PairSemantics.sound1686`, `OAI.MUB6.Certificate.PairSemantics.sound1707`, `OAI.MUB6.Certificate.PairSemantics.sound1716`, `OAI.MUB6.Certificate.PairSemantics.sound1718`, `OAI.MUB6.Certificate.PairSemantics.sound1736`, `OAI.MUB6.Certificate.PairSemantics.sound1739`, `OAI.MUB6.Certificate.PairSemantics.sound1768`, `OAI.MUB6.Certificate.PairSemantics.sound1769`, `OAI.MUB6.Certificate.PairSemantics.sound1770`, `OAI.MUB6.Certificate.PairSemantics.sound1774`, `OAI.MUB6.Certificate.PairSemantics.sound1784`, `OAI.MUB6.Certificate.PairSemantics.sound1793`, `OAI.MUB6.Certificate.PairSemantics.sound1800`, `OAI.MUB6.Certificate.PairSemantics.sound1803`, `OAI.MUB6.Certificate.PairSemantics.sound1826`, `OAI.MUB6.Certificate.PairSemantics.sound1828`, `OAI.MUB6.Certificate.PairSemantics.sound1830`, `OAI.MUB6.Certificate.PairSemantics.sound1849`, `OAI.MUB6.Certificate.PairSemantics.sound1858`, `OAI.MUB6.Certificate.PairSemantics.sound1860`, `OAI.MUB6.Certificate.PairSemantics.sound1865`, `OAI.MUB6.Certificate.PairSemantics.sound1866`, `OAI.MUB6.Certificate.PairSemantics.sound1867`, `OAI.MUB6.Certificate.PairSemantics.sound1869`, `OAI.MUB6.Certificate.PairSemantics.sound1870`, `OAI.MUB6.Certificate.PairSemantics.sound1872`, `OAI.MUB6.Certificate.PairSemantics.sound1873`, `OAI.MUB6.Certificate.PairSemantics.sound1879`, `OAI.MUB6.Certificate.PairSemantics.sound1885`, `OAI.MUB6.Certificate.PairSemantics.sound1890`, `OAI.MUB6.Certificate.PairSemantics.sound1938`, `OAI.MUB6.Certificate.PairSemantics.sound1968`, `OAI.MUB6.Certificate.PairSemantics.sound1977`, `OAI.MUB6.Certificate.PairSemantics.sound1978`, `OAI.MUB6.Certificate.PairSemantics.sound1980`, `OAI.MUB6.Certificate.PairSemantics.sound1986`, `OAI.MUB6.Certificate.PairSemantics.sound1987`, `OAI.MUB6.Certificate.PairSemantics.sound2041`, `OAI.MUB6.Certificate.PairSemantics.sound2058`, `OAI.MUB6.Certificate.PairSemantics.sound2106`, `OAI.MUB6.Certificate.PairSemantics.sound2108`, `OAI.MUB6.Certificate.PairSemantics.sound2113`, `OAI.MUB6.Certificate.PairSemantics.sound2117`, `OAI.MUB6.Certificate.PairSemantics.sound2122`, `OAI.MUB6.Certificate.PairSemantics.sound2123`, `OAI.MUB6.Certificate.PairSemantics.sound2128`, `OAI.MUB6.Certificate.PairSemantics.sound2132`, `OAI.MUB6.Certificate.PairSemantics.sound2152`, `OAI.MUB6.Certificate.PairSemantics.sound2168`, `OAI.MUB6.Certificate.PairSemantics.sound2175`, `OAI.MUB6.Certificate.PairSemantics.sound2177`, `OAI.MUB6.Certificate.PairSemantics.sound2183`, `OAI.MUB6.Certificate.PairSemantics.sound2190`, `OAI.MUB6.Certificate.PairSemantics.sound2192`, `OAI.MUB6.Certificate.PairSemantics.sound2197`, `OAI.MUB6.Certificate.PairSemantics.sound2201`, `OAI.MUB6.Certificate.PairSemantics.sound2202`, `OAI.MUB6.Certificate.PairSemantics.sound2204`, `OAI.MUB6.Certificate.PairSemantics.sound2213`, `OAI.MUB6.Certificate.PairSemantics.sound2216`, `OAI.MUB6.Certificate.PairSemantics.sound2228`, `OAI.MUB6.Certificate.PairSemantics.sound2243`, `OAI.MUB6.Certificate.PairSemantics.sound2244`, `OAI.MUB6.Certificate.PairSemantics.sound2262`, `OAI.MUB6.Certificate.PairSemantics.sound2284`, `OAI.MUB6.Certificate.PairSemantics.sound2285`, `OAI.MUB6.Certificate.PairSemantics.sound2286`, `OAI.MUB6.Certificate.PairSemantics.sound2293`, `OAI.MUB6.Certificate.PairSemantics.sound2294`, `OAI.MUB6.Certificate.PairSemantics.sound2295`, `OAI.MUB6.Certificate.PairSemantics.sound2296`, `OAI.MUB6.Certificate.PairSemantics.sound2298`, `OAI.MUB6.Certificate.PairSemantics.sound2304`, `OAI.MUB6.Certificate.PairSemantics.sound2307`, `OAI.MUB6.Certificate.PairSemantics.sound2312`, `OAI.MUB6.Certificate.PairSemantics.sound2315`, `OAI.MUB6.Certificate.PairSemantics.sound232`, `OAI.MUB6.Certificate.PairSemantics.sound2324`, `OAI.MUB6.Certificate.PairSemantics.sound2325`, `OAI.MUB6.Certificate.PairSemantics.sound2327`, `OAI.MUB6.Certificate.PairSemantics.sound2338`, `OAI.MUB6.Certificate.PairSemantics.sound2349`, `OAI.MUB6.Certificate.PairSemantics.sound2357`, `OAI.MUB6.Certificate.PairSemantics.sound2375`, `OAI.MUB6.Certificate.PairSemantics.sound2382`, `OAI.MUB6.Certificate.PairSemantics.sound2389`, `OAI.MUB6.Certificate.PairSemantics.sound2390`, `OAI.MUB6.Certificate.PairSemantics.sound2391`, `OAI.MUB6.Certificate.PairSemantics.sound2399`, `OAI.MUB6.Certificate.PairSemantics.sound2400`, `OAI.MUB6.Certificate.PairSemantics.sound2403`, `OAI.MUB6.Certificate.PairSemantics.sound2411`, `OAI.MUB6.Certificate.PairSemantics.sound2413`, `OAI.MUB6.Certificate.PairSemantics.sound2414`, `OAI.MUB6.Certificate.PairSemantics.sound2415`, `OAI.MUB6.Certificate.PairSemantics.sound2416`, `OAI.MUB6.Certificate.PairSemantics.sound2417`, `OAI.MUB6.Certificate.PairSemantics.sound2420`, `OAI.MUB6.Certificate.PairSemantics.sound2428`, `OAI.MUB6.Certificate.PairSemantics.sound2433`, `OAI.MUB6.Certificate.PairSemantics.sound2434`, `OAI.MUB6.Certificate.PairSemantics.sound2435`, `OAI.MUB6.Certificate.PairSemantics.sound2436`, `OAI.MUB6.Certificate.PairSemantics.sound2440`, `OAI.MUB6.Certificate.PairSemantics.sound2441`, `OAI.MUB6.Certificate.PairSemantics.sound2442`, `OAI.MUB6.Certificate.PairSemantics.sound2443`, `OAI.MUB6.Certificate.PairSemantics.sound2444`, `OAI.MUB6.Certificate.PairSemantics.sound2445`, `OAI.MUB6.Certificate.PairSemantics.sound2455`, `OAI.MUB6.Certificate.PairSemantics.sound2456`, `OAI.MUB6.Certificate.PairSemantics.sound2457`, `OAI.MUB6.Certificate.PairSemantics.sound2462`, `OAI.MUB6.Certificate.PairSemantics.sound2463`, `OAI.MUB6.Certificate.PairSemantics.sound2464`, `OAI.MUB6.Certificate.PairSemantics.sound2465`, `OAI.MUB6.Certificate.PairSemantics.sound2466`, `OAI.MUB6.Certificate.PairSemantics.sound2470`, `OAI.MUB6.Certificate.PairSemantics.sound2472`, `OAI.MUB6.Certificate.PairSemantics.sound2473`, `OAI.MUB6.Certificate.PairSemantics.sound2477`, `OAI.MUB6.Certificate.PairSemantics.sound2479`, `OAI.MUB6.Certificate.PairSemantics.sound2486`, `OAI.MUB6.Certificate.PairSemantics.sound2489`, `OAI.MUB6.Certificate.PairSemantics.sound2490`, `OAI.MUB6.Certificate.PairSemantics.sound2491`, `OAI.MUB6.Certificate.PairSemantics.sound2492`, `OAI.MUB6.Certificate.PairSemantics.sound2507`, `OAI.MUB6.Certificate.PairSemantics.sound2520`, `OAI.MUB6.Certificate.PairSemantics.sound2521`, `OAI.MUB6.Certificate.PairSemantics.sound2524`, `OAI.MUB6.Certificate.PairSemantics.sound2525`, `OAI.MUB6.Certificate.PairSemantics.sound2533`, `OAI.MUB6.Certificate.PairSemantics.sound2540`, `OAI.MUB6.Certificate.PairSemantics.sound2546`, `OAI.MUB6.Certificate.PairSemantics.sound2547`, `OAI.MUB6.Certificate.PairSemantics.sound2548`, `OAI.MUB6.Certificate.PairSemantics.sound2557`, `OAI.MUB6.Certificate.PairSemantics.sound2558`, `OAI.MUB6.Certificate.PairSemantics.sound2559`, `OAI.MUB6.Certificate.PairSemantics.sound2564`, `OAI.MUB6.Certificate.PairSemantics.sound2565`, `OAI.MUB6.Certificate.PairSemantics.sound2566`, `OAI.MUB6.Certificate.PairSemantics.sound2573`, `OAI.MUB6.Certificate.PairSemantics.sound2578`, `OAI.MUB6.Certificate.PairSemantics.sound2579`, `OAI.MUB6.Certificate.PairSemantics.sound2580`, `OAI.MUB6.Certificate.PairSemantics.sound2602`, `OAI.MUB6.Certificate.PairSemantics.sound2604`, `OAI.MUB6.Certificate.PairSemantics.sound2606`, `OAI.MUB6.Certificate.PairSemantics.sound2619`, `OAI.MUB6.Certificate.PairSemantics.sound2626`, `OAI.MUB6.Certificate.PairSemantics.sound2627`, `OAI.MUB6.Certificate.PairSemantics.sound2641`, `OAI.MUB6.Certificate.PairSemantics.sound2657`, `OAI.MUB6.Certificate.PairSemantics.sound2658`, `OAI.MUB6.Certificate.PairSemantics.sound2661`, `OAI.MUB6.Certificate.PairSemantics.sound2666`, `OAI.MUB6.Certificate.PairSemantics.sound2670`, `OAI.MUB6.Certificate.PairSemantics.sound2671`, `OAI.MUB6.Certificate.PairSemantics.sound2674`, `OAI.MUB6.Certificate.PairSemantics.sound2683`, `OAI.MUB6.Certificate.PairSemantics.sound2686`, `OAI.MUB6.Certificate.PairSemantics.sound2690`, `OAI.MUB6.Certificate.PairSemantics.sound2693`, `OAI.MUB6.Certificate.PairSemantics.sound2709`, `OAI.MUB6.Certificate.PairSemantics.sound2710`, `OAI.MUB6.Certificate.PairSemantics.sound2711`, `OAI.MUB6.Certificate.PairSemantics.sound2714`, `OAI.MUB6.Certificate.PairSemantics.sound2717`, `OAI.MUB6.Certificate.PairSemantics.sound2723`, `OAI.MUB6.Certificate.PairSemantics.sound2732`, `OAI.MUB6.Certificate.PairSemantics.sound2733`, `OAI.MUB6.Certificate.PairSemantics.sound2754`, `OAI.MUB6.Certificate.PairSemantics.sound2757`, `OAI.MUB6.Certificate.PairSemantics.sound2765`, `OAI.MUB6.Certificate.PairSemantics.sound2788`, `OAI.MUB6.Certificate.PairSemantics.sound2790`, `OAI.MUB6.Certificate.PairSemantics.sound2793`, `OAI.MUB6.Certificate.PairSemantics.sound2827`, `OAI.MUB6.Certificate.PairSemantics.sound2829`, `OAI.MUB6.Certificate.PairSemantics.sound2836`, `OAI.MUB6.Certificate.PairSemantics.sound2839`, `OAI.MUB6.Certificate.PairSemantics.sound284`, `OAI.MUB6.Certificate.PairSemantics.sound2845`, `OAI.MUB6.Certificate.PairSemantics.sound2850`, `OAI.MUB6.Certificate.PairSemantics.sound2852`, `OAI.MUB6.Certificate.PairSemantics.sound2854`, `OAI.MUB6.Certificate.PairSemantics.sound2855`, `OAI.MUB6.Certificate.PairSemantics.sound2863`, `OAI.MUB6.Certificate.PairSemantics.sound2864`, `OAI.MUB6.Certificate.PairSemantics.sound2865`, `OAI.MUB6.Certificate.PairSemantics.sound2866`, `OAI.MUB6.Certificate.PairSemantics.sound2867`, `OAI.MUB6.Certificate.PairSemantics.sound2868`, `OAI.MUB6.Certificate.PairSemantics.sound2872`, `OAI.MUB6.Certificate.PairSemantics.sound2873`, `OAI.MUB6.Certificate.PairSemantics.sound2874`, `OAI.MUB6.Certificate.PairSemantics.sound2875`, `OAI.MUB6.Certificate.PairSemantics.sound2878`, `OAI.MUB6.Certificate.PairSemantics.sound2879`, `OAI.MUB6.Certificate.PairSemantics.sound2880`, `OAI.MUB6.Certificate.PairSemantics.sound2881`, `OAI.MUB6.Certificate.PairSemantics.sound2882`, `OAI.MUB6.Certificate.PairSemantics.sound2883`, `OAI.MUB6.Certificate.PairSemantics.sound2884`, `OAI.MUB6.Certificate.PairSemantics.sound2886`, `OAI.MUB6.Certificate.PairSemantics.sound2887`, `OAI.MUB6.Certificate.PairSemantics.sound2888`, `OAI.MUB6.Certificate.PairSemantics.sound2889`, `OAI.MUB6.Certificate.PairSemantics.sound2890`, `OAI.MUB6.Certificate.PairSemantics.sound2891`, `OAI.MUB6.Certificate.PairSemantics.sound2892`, `OAI.MUB6.Certificate.PairSemantics.sound2894`, `OAI.MUB6.Certificate.PairSemantics.sound2895`, `OAI.MUB6.Certificate.PairSemantics.sound2896`, `OAI.MUB6.Certificate.PairSemantics.sound2897`, `OAI.MUB6.Certificate.PairSemantics.sound2898`, `OAI.MUB6.Certificate.PairSemantics.sound2899`, `OAI.MUB6.Certificate.PairSemantics.sound2900`, `OAI.MUB6.Certificate.PairSemantics.sound2901`, `OAI.MUB6.Certificate.PairSemantics.sound2902`, `OAI.MUB6.Certificate.PairSemantics.sound2903`, `OAI.MUB6.Certificate.PairSemantics.sound2906`, `OAI.MUB6.Certificate.PairSemantics.sound2909`, `OAI.MUB6.Certificate.PairSemantics.sound2910`, `OAI.MUB6.Certificate.PairSemantics.sound2912`, `OAI.MUB6.Certificate.PairSemantics.sound2913`, `OAI.MUB6.Certificate.PairSemantics.sound2914`, `OAI.MUB6.Certificate.PairSemantics.sound2915`, `OAI.MUB6.Certificate.PairSemantics.sound2916`, `OAI.MUB6.Certificate.PairSemantics.sound2917`, `OAI.MUB6.Certificate.PairSemantics.sound2918`, `OAI.MUB6.Certificate.PairSemantics.sound2919`, `OAI.MUB6.Certificate.PairSemantics.sound2920`, `OAI.MUB6.Certificate.PairSemantics.sound2922`, `OAI.MUB6.Certificate.PairSemantics.sound2924`, `OAI.MUB6.Certificate.PairSemantics.sound2927`, `OAI.MUB6.Certificate.PairSemantics.sound2928`, `OAI.MUB6.Certificate.PairSemantics.sound2929`, `OAI.MUB6.Certificate.PairSemantics.sound2930`, `OAI.MUB6.Certificate.PairSemantics.sound2931`, `OAI.MUB6.Certificate.PairSemantics.sound2933`, `OAI.MUB6.Certificate.PairSemantics.sound2934`, `OAI.MUB6.Certificate.PairSemantics.sound2935`, `OAI.MUB6.Certificate.PairSemantics.sound2936`, `OAI.MUB6.Certificate.PairSemantics.sound2939`, `OAI.MUB6.Certificate.PairSemantics.sound2940`, `OAI.MUB6.Certificate.PairSemantics.sound2941`, `OAI.MUB6.Certificate.PairSemantics.sound2943`, `OAI.MUB6.Certificate.PairSemantics.sound2944`, `OAI.MUB6.Certificate.PairSemantics.sound2947`, `OAI.MUB6.Certificate.PairSemantics.sound2948`, `OAI.MUB6.Certificate.PairSemantics.sound2949`, `OAI.MUB6.Certificate.PairSemantics.sound2950`, `OAI.MUB6.Certificate.PairSemantics.sound2952`, `OAI.MUB6.Certificate.PairSemantics.sound2953`, `OAI.MUB6.Certificate.PairSemantics.sound2954`, `OAI.MUB6.Certificate.PairSemantics.sound2955`, `OAI.MUB6.Certificate.PairSemantics.sound2956`, `OAI.MUB6.Certificate.PairSemantics.sound2957`, `OAI.MUB6.Certificate.PairSemantics.sound2958`, `OAI.MUB6.Certificate.PairSemantics.sound2959`, `OAI.MUB6.Certificate.PairSemantics.sound2960`, `OAI.MUB6.Certificate.PairSemantics.sound2962`, `OAI.MUB6.Certificate.PairSemantics.sound2964`, `OAI.MUB6.Certificate.PairSemantics.sound2965`, `OAI.MUB6.Certificate.PairSemantics.sound2966`, `OAI.MUB6.Certificate.PairSemantics.sound2967`, `OAI.MUB6.Certificate.PairSemantics.sound2968`, `OAI.MUB6.Certificate.PairSemantics.sound2969`, `OAI.MUB6.Certificate.PairSemantics.sound2970`, `OAI.MUB6.Certificate.PairSemantics.sound2972`, `OAI.MUB6.Certificate.PairSemantics.sound2973`, `OAI.MUB6.Certificate.PairSemantics.sound2974`, `OAI.MUB6.Certificate.PairSemantics.sound2975`, `OAI.MUB6.Certificate.PairSemantics.sound2976`, `OAI.MUB6.Certificate.PairSemantics.sound2977`, `OAI.MUB6.Certificate.PairSemantics.sound2979`, `OAI.MUB6.Certificate.PairSemantics.sound2980`, `OAI.MUB6.Certificate.PairSemantics.sound2982`, `OAI.MUB6.Certificate.PairSemantics.sound2985`, `OAI.MUB6.Certificate.PairSemantics.sound2986`, `OAI.MUB6.Certificate.PairSemantics.sound2987`, `OAI.MUB6.Certificate.PairSemantics.sound2988`, `OAI.MUB6.Certificate.PairSemantics.sound2989`, `OAI.MUB6.Certificate.PairSemantics.sound2990`, `OAI.MUB6.Certificate.PairSemantics.sound2991`, `OAI.MUB6.Certificate.PairSemantics.sound2993`, `OAI.MUB6.Certificate.PairSemantics.sound2994`, `OAI.MUB6.Certificate.PairSemantics.sound2996`, `OAI.MUB6.Certificate.PairSemantics.sound2997`, `OAI.MUB6.Certificate.PairSemantics.sound2998`, `OAI.MUB6.Certificate.PairSemantics.sound2999`, `OAI.MUB6.Certificate.PairSemantics.sound3000`, `OAI.MUB6.Certificate.PairSemantics.sound3001`, `OAI.MUB6.Certificate.PairSemantics.sound3002`, `OAI.MUB6.Certificate.PairSemantics.sound3004`, `OAI.MUB6.Certificate.PairSemantics.sound3006`, `OAI.MUB6.Certificate.PairSemantics.sound3009`, `OAI.MUB6.Certificate.PairSemantics.sound3010`, `OAI.MUB6.Certificate.PairSemantics.sound3011`, `OAI.MUB6.Certificate.PairSemantics.sound3012`, `OAI.MUB6.Certificate.PairSemantics.sound3013`, `OAI.MUB6.Certificate.PairSemantics.sound3014`, `OAI.MUB6.Certificate.PairSemantics.sound3015`, `OAI.MUB6.Certificate.PairSemantics.sound3016`, `OAI.MUB6.Certificate.PairSemantics.sound3017`, `OAI.MUB6.Certificate.PairSemantics.sound3018`, `OAI.MUB6.Certificate.PairSemantics.sound3019`, `OAI.MUB6.Certificate.PairSemantics.sound3020`, `OAI.MUB6.Certificate.PairSemantics.sound3021`, `OAI.MUB6.Certificate.PairSemantics.sound3022`, `OAI.MUB6.Certificate.PairSemantics.sound3023`, `OAI.MUB6.Certificate.PairSemantics.sound3024`, `OAI.MUB6.Certificate.PairSemantics.sound3025`, `OAI.MUB6.Certificate.PairSemantics.sound3026`, `OAI.MUB6.Certificate.PairSemantics.sound3027`, `OAI.MUB6.Certificate.PairSemantics.sound3028`, `OAI.MUB6.Certificate.PairSemantics.sound3029`, `OAI.MUB6.Certificate.PairSemantics.sound3030`, `OAI.MUB6.Certificate.PairSemantics.sound3031`, `OAI.MUB6.Certificate.PairSemantics.sound3032`, `OAI.MUB6.Certificate.PairSemantics.sound3033`, `OAI.MUB6.Certificate.PairSemantics.sound3034`, `OAI.MUB6.Certificate.PairSemantics.sound3035`, `OAI.MUB6.Certificate.PairSemantics.sound3036`, `OAI.MUB6.Certificate.PairSemantics.sound3038`, `OAI.MUB6.Certificate.PairSemantics.sound3039`, `OAI.MUB6.Certificate.PairSemantics.sound3040`, `OAI.MUB6.Certificate.PairSemantics.sound3041`, `OAI.MUB6.Certificate.PairSemantics.sound3042`, `OAI.MUB6.Certificate.PairSemantics.sound3043`, `OAI.MUB6.Certificate.PairSemantics.sound3044`, `OAI.MUB6.Certificate.PairSemantics.sound3045`, `OAI.MUB6.Certificate.PairSemantics.sound3047`, `OAI.MUB6.Certificate.PairSemantics.sound3048`, `OAI.MUB6.Certificate.PairSemantics.sound3049`, `OAI.MUB6.Certificate.PairSemantics.sound3050`, `OAI.MUB6.Certificate.PairSemantics.sound3051`, `OAI.MUB6.Certificate.PairSemantics.sound3053`, `OAI.MUB6.Certificate.PairSemantics.sound3054`, `OAI.MUB6.Certificate.PairSemantics.sound3056`, `OAI.MUB6.Certificate.PairSemantics.sound3058`, `OAI.MUB6.Certificate.PairSemantics.sound3059`, `OAI.MUB6.Certificate.PairSemantics.sound3060`, `OAI.MUB6.Certificate.PairSemantics.sound3061`, `OAI.MUB6.Certificate.PairSemantics.sound3062`, `OAI.MUB6.Certificate.PairSemantics.sound3063`, `OAI.MUB6.Certificate.PairSemantics.sound3065`, `OAI.MUB6.Certificate.PairSemantics.sound3066`, `OAI.MUB6.Certificate.PairSemantics.sound3067`, `OAI.MUB6.Certificate.PairSemantics.sound3068`, `OAI.MUB6.Certificate.PairSemantics.sound3069`, `OAI.MUB6.Certificate.PairSemantics.sound3071`, `OAI.MUB6.Certificate.PairSemantics.sound3072`, `OAI.MUB6.Certificate.PairSemantics.sound3073`, `OAI.MUB6.Certificate.PairSemantics.sound3074`, `OAI.MUB6.Certificate.PairSemantics.sound3075`, `OAI.MUB6.Certificate.PairSemantics.sound3076`, `OAI.MUB6.Certificate.PairSemantics.sound3077`, `OAI.MUB6.Certificate.PairSemantics.sound3078`, `OAI.MUB6.Certificate.PairSemantics.sound3079`, `OAI.MUB6.Certificate.PairSemantics.sound3080`, `OAI.MUB6.Certificate.PairSemantics.sound3081`, `OAI.MUB6.Certificate.PairSemantics.sound3082`, `OAI.MUB6.Certificate.PairSemantics.sound3083`, `OAI.MUB6.Certificate.PairSemantics.sound3084`, `OAI.MUB6.Certificate.PairSemantics.sound3085`, `OAI.MUB6.Certificate.PairSemantics.sound3086`, `OAI.MUB6.Certificate.PairSemantics.sound3090`, `OAI.MUB6.Certificate.PairSemantics.sound3091`, `OAI.MUB6.Certificate.PairSemantics.sound3092`, `OAI.MUB6.Certificate.PairSemantics.sound3093`, `OAI.MUB6.Certificate.PairSemantics.sound3094`, `OAI.MUB6.Certificate.PairSemantics.sound3095`, `OAI.MUB6.Certificate.PairSemantics.sound3096`, `OAI.MUB6.Certificate.PairSemantics.sound3097`, `OAI.MUB6.Certificate.PairSemantics.sound3098`, `OAI.MUB6.Certificate.PairSemantics.sound3099`, `OAI.MUB6.Certificate.PairSemantics.sound3100`, `OAI.MUB6.Certificate.PairSemantics.sound3101`, `OAI.MUB6.Certificate.PairSemantics.sound3102`, `OAI.MUB6.Certificate.PairSemantics.sound3105`, `OAI.MUB6.Certificate.PairSemantics.sound3106`, `OAI.MUB6.Certificate.PairSemantics.sound3107`, `OAI.MUB6.Certificate.PairSemantics.sound3108`, `OAI.MUB6.Certificate.PairSemantics.sound3109`, `OAI.MUB6.Certificate.PairSemantics.sound3110`, `OAI.MUB6.Certificate.PairSemantics.sound3111`, `OAI.MUB6.Certificate.PairSemantics.sound3112`, `OAI.MUB6.Certificate.PairSemantics.sound3113`, `OAI.MUB6.Certificate.PairSemantics.sound3114`, `OAI.MUB6.Certificate.PairSemantics.sound3115`, `OAI.MUB6.Certificate.PairSemantics.sound3116`, `OAI.MUB6.Certificate.PairSemantics.sound3118`, `OAI.MUB6.Certificate.PairSemantics.sound3119`, `OAI.MUB6.Certificate.PairSemantics.sound3120`, `OAI.MUB6.Certificate.PairSemantics.sound3121`, `OAI.MUB6.Certificate.PairSemantics.sound3122`, `OAI.MUB6.Certificate.PairSemantics.sound3123`, `OAI.MUB6.Certificate.PairSemantics.sound3124`, `OAI.MUB6.Certificate.PairSemantics.sound3125`, `OAI.MUB6.Certificate.PairSemantics.sound3128`, `OAI.MUB6.Certificate.PairSemantics.sound3129`, `OAI.MUB6.Certificate.PairSemantics.sound3130`, `OAI.MUB6.Certificate.PairSemantics.sound3131`, `OAI.MUB6.Certificate.PairSemantics.sound3133`, `OAI.MUB6.Certificate.PairSemantics.sound3135`, `OAI.MUB6.Certificate.PairSemantics.sound3136`, `OAI.MUB6.Certificate.PairSemantics.sound3138`, `OAI.MUB6.Certificate.PairSemantics.sound3139`, `OAI.MUB6.Certificate.PairSemantics.sound3140`, `OAI.MUB6.Certificate.PairSemantics.sound3141`, `OAI.MUB6.Certificate.PairSemantics.sound3142`, `OAI.MUB6.Certificate.PairSemantics.sound3144`, `OAI.MUB6.Certificate.PairSemantics.sound3145`, `OAI.MUB6.Certificate.PairSemantics.sound3146`, `OAI.MUB6.Certificate.PairSemantics.sound3150`, `OAI.MUB6.Certificate.PairSemantics.sound3151`, `OAI.MUB6.Certificate.PairSemantics.sound3152`, `OAI.MUB6.Certificate.PairSemantics.sound3153`, `OAI.MUB6.Certificate.PairSemantics.sound3155`, `OAI.MUB6.Certificate.PairSemantics.sound3158`, `OAI.MUB6.Certificate.PairSemantics.sound3159`, `OAI.MUB6.Certificate.PairSemantics.sound3160`, `OAI.MUB6.Certificate.PairSemantics.sound3161`, `OAI.MUB6.Certificate.PairSemantics.sound3162`, `OAI.MUB6.Certificate.PairSemantics.sound3163`, `OAI.MUB6.Certificate.PairSemantics.sound3164`, `OAI.MUB6.Certificate.PairSemantics.sound3166`, `OAI.MUB6.Certificate.PairSemantics.sound3167`, `OAI.MUB6.Certificate.PairSemantics.sound3168`, `OAI.MUB6.Certificate.PairSemantics.sound3169`, `OAI.MUB6.Certificate.PairSemantics.sound3170`, `OAI.MUB6.Certificate.PairSemantics.sound3171`, `OAI.MUB6.Certificate.PairSemantics.sound3172`, `OAI.MUB6.Certificate.PairSemantics.sound3173`, `OAI.MUB6.Certificate.PairSemantics.sound3174`, `OAI.MUB6.Certificate.PairSemantics.sound3176`, `OAI.MUB6.Certificate.PairSemantics.sound3178`, `OAI.MUB6.Certificate.PairSemantics.sound3179`, `OAI.MUB6.Certificate.PairSemantics.sound3180`, `OAI.MUB6.Certificate.PairSemantics.sound3181`, `OAI.MUB6.Certificate.PairSemantics.sound3183`, `OAI.MUB6.Certificate.PairSemantics.sound3184`, `OAI.MUB6.Certificate.PairSemantics.sound3185`, `OAI.MUB6.Certificate.PairSemantics.sound3186`, `OAI.MUB6.Certificate.PairSemantics.sound3187`, `OAI.MUB6.Certificate.PairSemantics.sound3188`, `OAI.MUB6.Certificate.PairSemantics.sound3189`, `OAI.MUB6.Certificate.PairSemantics.sound3191`, `OAI.MUB6.Certificate.PairSemantics.sound3192`, `OAI.MUB6.Certificate.PairSemantics.sound3193`, `OAI.MUB6.Certificate.PairSemantics.sound3194`, `OAI.MUB6.Certificate.PairSemantics.sound3195`, `OAI.MUB6.Certificate.PairSemantics.sound3196`, `OAI.MUB6.Certificate.PairSemantics.sound3197`, `OAI.MUB6.Certificate.PairSemantics.sound3198`, `OAI.MUB6.Certificate.PairSemantics.sound3199`, `OAI.MUB6.Certificate.PairSemantics.sound3200`, `OAI.MUB6.Certificate.PairSemantics.sound3201`, `OAI.MUB6.Certificate.PairSemantics.sound3202`, `OAI.MUB6.Certificate.PairSemantics.sound3203`, `OAI.MUB6.Certificate.PairSemantics.sound3204`, `OAI.MUB6.Certificate.PairSemantics.sound3205`, `OAI.MUB6.Certificate.PairSemantics.sound3206`, `OAI.MUB6.Certificate.PairSemantics.sound3208`, `OAI.MUB6.Certificate.PairSemantics.sound3211`, `OAI.MUB6.Certificate.PairSemantics.sound3212`, `OAI.MUB6.Certificate.PairSemantics.sound3213`, `OAI.MUB6.Certificate.PairSemantics.sound3214`, `OAI.MUB6.Certificate.PairSemantics.sound3215`, `OAI.MUB6.Certificate.PairSemantics.sound3216`, `OAI.MUB6.Certificate.PairSemantics.sound3217`, `OAI.MUB6.Certificate.PairSemantics.sound3218`, `OAI.MUB6.Certificate.PairSemantics.sound3219`, `OAI.MUB6.Certificate.PairSemantics.sound3221`, `OAI.MUB6.Certificate.PairSemantics.sound3222`, `OAI.MUB6.Certificate.PairSemantics.sound3223`, `OAI.MUB6.Certificate.PairSemantics.sound3224`, `OAI.MUB6.Certificate.PairSemantics.sound3226`, `OAI.MUB6.Certificate.PairSemantics.sound3227`, `OAI.MUB6.Certificate.PairSemantics.sound3228`, `OAI.MUB6.Certificate.PairSemantics.sound3230`, `OAI.MUB6.Certificate.PairSemantics.sound3231`, `OAI.MUB6.Certificate.PairSemantics.sound3233`, `OAI.MUB6.Certificate.PairSemantics.sound3234`, `OAI.MUB6.Certificate.PairSemantics.sound3235`, `OAI.MUB6.Certificate.PairSemantics.sound3237`, `OAI.MUB6.Certificate.PairSemantics.sound3238`, `OAI.MUB6.Certificate.PairSemantics.sound3239`, `OAI.MUB6.Certificate.PairSemantics.sound3240`, `OAI.MUB6.Certificate.PairSemantics.sound3241`, `OAI.MUB6.Certificate.PairSemantics.sound3242`, `OAI.MUB6.Certificate.PairSemantics.sound3243`, `OAI.MUB6.Certificate.PairSemantics.sound3244`, `OAI.MUB6.Certificate.PairSemantics.sound3246`, `OAI.MUB6.Certificate.PairSemantics.sound3247`, `OAI.MUB6.Certificate.PairSemantics.sound3248`, `OAI.MUB6.Certificate.PairSemantics.sound3249`, `OAI.MUB6.Certificate.PairSemantics.sound3250`, `OAI.MUB6.Certificate.PairSemantics.sound3251`, `OAI.MUB6.Certificate.PairSemantics.sound3253`, `OAI.MUB6.Certificate.PairSemantics.sound3254`, `OAI.MUB6.Certificate.PairSemantics.sound3255`, `OAI.MUB6.Certificate.PairSemantics.sound3256`, `OAI.MUB6.Certificate.PairSemantics.sound3258`, `OAI.MUB6.Certificate.PairSemantics.sound3259`, `OAI.MUB6.Certificate.PairSemantics.sound3261`, `OAI.MUB6.Certificate.PairSemantics.sound3262`, `OAI.MUB6.Certificate.PairSemantics.sound3263`, `OAI.MUB6.Certificate.PairSemantics.sound3266`, `OAI.MUB6.Certificate.PairSemantics.sound3267`, `OAI.MUB6.Certificate.PairSemantics.sound3268`, `OAI.MUB6.Certificate.PairSemantics.sound3269`, `OAI.MUB6.Certificate.PairSemantics.sound3270`, `OAI.MUB6.Certificate.PairSemantics.sound3271`, `OAI.MUB6.Certificate.PairSemantics.sound3273`, `OAI.MUB6.Certificate.PairSemantics.sound3275`, `OAI.MUB6.Certificate.PairSemantics.sound3276`, `OAI.MUB6.Certificate.PairSemantics.sound3277`, `OAI.MUB6.Certificate.PairSemantics.sound3279`, `OAI.MUB6.Certificate.PairSemantics.sound3280`, `OAI.MUB6.Certificate.PairSemantics.sound3281`, `OAI.MUB6.Certificate.PairSemantics.sound3282`, `OAI.MUB6.Certificate.PairSemantics.sound3283`, `OAI.MUB6.Certificate.PairSemantics.sound3284`, `OAI.MUB6.Certificate.PairSemantics.sound3288`, `OAI.MUB6.Certificate.PairSemantics.sound3289`, `OAI.MUB6.Certificate.PairSemantics.sound3290`, `OAI.MUB6.Certificate.PairSemantics.sound3291`, `OAI.MUB6.Certificate.PairSemantics.sound3292`, `OAI.MUB6.Certificate.PairSemantics.sound3293`, `OAI.MUB6.Certificate.PairSemantics.sound3294`, `OAI.MUB6.Certificate.PairSemantics.sound3295`, `OAI.MUB6.Certificate.PairSemantics.sound3296`, `OAI.MUB6.Certificate.PairSemantics.sound3297`, `OAI.MUB6.Certificate.PairSemantics.sound3298`, `OAI.MUB6.Certificate.PairSemantics.sound3299`, `OAI.MUB6.Certificate.PairSemantics.sound3300`, `OAI.MUB6.Certificate.PairSemantics.sound3301`, `OAI.MUB6.Certificate.PairSemantics.sound3302`, `OAI.MUB6.Certificate.PairSemantics.sound3304`, `OAI.MUB6.Certificate.PairSemantics.sound3305`, `OAI.MUB6.Certificate.PairSemantics.sound3307`, `OAI.MUB6.Certificate.PairSemantics.sound3308`, `OAI.MUB6.Certificate.PairSemantics.sound3310`, `OAI.MUB6.Certificate.PairSemantics.sound3311`, `OAI.MUB6.Certificate.PairSemantics.sound3312`, `OAI.MUB6.Certificate.PairSemantics.sound3313`, `OAI.MUB6.Certificate.PairSemantics.sound3314`, `OAI.MUB6.Certificate.PairSemantics.sound3315`, `OAI.MUB6.Certificate.PairSemantics.sound3316`, `OAI.MUB6.Certificate.PairSemantics.sound3317`, `OAI.MUB6.Certificate.PairSemantics.sound3319`, `OAI.MUB6.Certificate.PairSemantics.sound3322`, `OAI.MUB6.Certificate.PairSemantics.sound3323`, `OAI.MUB6.Certificate.PairSemantics.sound3324`, `OAI.MUB6.Certificate.PairSemantics.sound3325`, `OAI.MUB6.Certificate.PairSemantics.sound3327`, `OAI.MUB6.Certificate.PairSemantics.sound3328`, `OAI.MUB6.Certificate.PairSemantics.sound3332`, `OAI.MUB6.Certificate.PairSemantics.sound3333`, `OAI.MUB6.Certificate.PairSemantics.sound3334`, `OAI.MUB6.Certificate.PairSemantics.sound3335`, `OAI.MUB6.Certificate.PairSemantics.sound3336`, `OAI.MUB6.Certificate.PairSemantics.sound3338`, `OAI.MUB6.Certificate.PairSemantics.sound3340`, `OAI.MUB6.Certificate.PairSemantics.sound3341`, `OAI.MUB6.Certificate.PairSemantics.sound3342`, `OAI.MUB6.Certificate.PairSemantics.sound3343`, `OAI.MUB6.Certificate.PairSemantics.sound3344`, `OAI.MUB6.Certificate.PairSemantics.sound3345`, `OAI.MUB6.Certificate.PairSemantics.sound3346`, `OAI.MUB6.Certificate.PairSemantics.sound3347`, `OAI.MUB6.Certificate.PairSemantics.sound3348`, `OAI.MUB6.Certificate.PairSemantics.sound3349`, `OAI.MUB6.Certificate.PairSemantics.sound3350`, `OAI.MUB6.Certificate.PairSemantics.sound3351`, `OAI.MUB6.Certificate.PairSemantics.sound3352`, `OAI.MUB6.Certificate.PairSemantics.sound3353`, `OAI.MUB6.Certificate.PairSemantics.sound3354`, `OAI.MUB6.Certificate.PairSemantics.sound3355`, `OAI.MUB6.Certificate.PairSemantics.sound3356`, `OAI.MUB6.Certificate.PairSemantics.sound3357`, `OAI.MUB6.Certificate.PairSemantics.sound3359`, `OAI.MUB6.Certificate.PairSemantics.sound3360`, `OAI.MUB6.Certificate.PairSemantics.sound3361`, `OAI.MUB6.Certificate.PairSemantics.sound3362`, `OAI.MUB6.Certificate.PairSemantics.sound3364`, `OAI.MUB6.Certificate.PairSemantics.sound3365`, `OAI.MUB6.Certificate.PairSemantics.sound3366`, `OAI.MUB6.Certificate.PairSemantics.sound3367`, `OAI.MUB6.Certificate.PairSemantics.sound3369`, `OAI.MUB6.Certificate.PairSemantics.sound3370`, `OAI.MUB6.Certificate.PairSemantics.sound3371`, `OAI.MUB6.Certificate.PairSemantics.sound3372`, `OAI.MUB6.Certificate.PairSemantics.sound3373`, `OAI.MUB6.Certificate.PairSemantics.sound3375`, `OAI.MUB6.Certificate.PairSemantics.sound3376`, `OAI.MUB6.Certificate.PairSemantics.sound3377`, `OAI.MUB6.Certificate.PairSemantics.sound3378`, `OAI.MUB6.Certificate.PairSemantics.sound3380`, `OAI.MUB6.Certificate.PairSemantics.sound3381`, `OAI.MUB6.Certificate.PairSemantics.sound3382`, `OAI.MUB6.Certificate.PairSemantics.sound3383`, `OAI.MUB6.Certificate.PairSemantics.sound3384`, `OAI.MUB6.Certificate.PairSemantics.sound3385`, `OAI.MUB6.Certificate.PairSemantics.sound3388`, `OAI.MUB6.Certificate.PairSemantics.sound3390`, `OAI.MUB6.Certificate.PairSemantics.sound3391`, `OAI.MUB6.Certificate.PairSemantics.sound3392`, `OAI.MUB6.Certificate.PairSemantics.sound3393`, `OAI.MUB6.Certificate.PairSemantics.sound3394`, `OAI.MUB6.Certificate.PairSemantics.sound3395`, `OAI.MUB6.Certificate.PairSemantics.sound3396`, `OAI.MUB6.Certificate.PairSemantics.sound3399`, `OAI.MUB6.Certificate.PairSemantics.sound3400`, `OAI.MUB6.Certificate.PairSemantics.sound3401`, `OAI.MUB6.Certificate.PairSemantics.sound3402`, `OAI.MUB6.Certificate.PairSemantics.sound3405`, `OAI.MUB6.Certificate.PairSemantics.sound3407`, `OAI.MUB6.Certificate.PairSemantics.sound3408`, `OAI.MUB6.Certificate.PairSemantics.sound3411`, `OAI.MUB6.Certificate.PairSemantics.sound3412`, `OAI.MUB6.Certificate.PairSemantics.sound3413`, `OAI.MUB6.Certificate.PairSemantics.sound3414`, `OAI.MUB6.Certificate.PairSemantics.sound3415`, `OAI.MUB6.Certificate.PairSemantics.sound3416`, `OAI.MUB6.Certificate.PairSemantics.sound3417`, `OAI.MUB6.Certificate.PairSemantics.sound3418`, `OAI.MUB6.Certificate.PairSemantics.sound3420`, `OAI.MUB6.Certificate.PairSemantics.sound3421`, `OAI.MUB6.Certificate.PairSemantics.sound3422`, `OAI.MUB6.Certificate.PairSemantics.sound3423`, `OAI.MUB6.Certificate.PairSemantics.sound3424`, `OAI.MUB6.Certificate.PairSemantics.sound3425`, `OAI.MUB6.Certificate.PairSemantics.sound3426`, `OAI.MUB6.Certificate.PairSemantics.sound3428`, `OAI.MUB6.Certificate.PairSemantics.sound3431`, `OAI.MUB6.Certificate.PairSemantics.sound3433`, `OAI.MUB6.Certificate.PairSemantics.sound3434`, `OAI.MUB6.Certificate.PairSemantics.sound3435`, `OAI.MUB6.Certificate.PairSemantics.sound3436`, `OAI.MUB6.Certificate.PairSemantics.sound3437`, `OAI.MUB6.Certificate.PairSemantics.sound3438`, `OAI.MUB6.Certificate.PairSemantics.sound3439`, `OAI.MUB6.Certificate.PairSemantics.sound3440`, `OAI.MUB6.Certificate.PairSemantics.sound3441`, `OAI.MUB6.Certificate.PairSemantics.sound3445`, `OAI.MUB6.Certificate.PairSemantics.sound3447`, `OAI.MUB6.Certificate.PairSemantics.sound3449`, `OAI.MUB6.Certificate.PairSemantics.sound3454`, `OAI.MUB6.Certificate.PairSemantics.sound3456`, `OAI.MUB6.Certificate.PairSemantics.sound3457`, `OAI.MUB6.Certificate.PairSemantics.sound3458`, `OAI.MUB6.Certificate.PairSemantics.sound3459`, `OAI.MUB6.Certificate.PairSemantics.sound3460`, `OAI.MUB6.Certificate.PairSemantics.sound3461`, `OAI.MUB6.Certificate.PairSemantics.sound3462`, `OAI.MUB6.Certificate.PairSemantics.sound3463`, `OAI.MUB6.Certificate.PairSemantics.sound3467`, `OAI.MUB6.Certificate.PairSemantics.sound3468`, `OAI.MUB6.Certificate.PairSemantics.sound381`, `OAI.MUB6.Certificate.PairSemantics.sound46`, `OAI.MUB6.Certificate.PairSemantics.sound545`, `OAI.MUB6.Certificate.PairSemantics.sound65`, `OAI.MUB6.Certificate.PairSemantics.sound659`, `OAI.MUB6.Certificate.PairSemantics.sound711`, `OAI.MUB6.Certificate.PairSemantics.sound856`, `OAI.MUB6.Certificate.PairSemantics.sound858`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound0`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound1`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound10`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound100`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound101`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound102`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound103`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound104`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound105`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound106`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound107`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound108`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound111`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound112`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound113`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound114`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound115`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound116`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound117`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound118`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound119`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound12`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound120`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound121`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound124`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound125`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound126`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound127`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound128`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound129`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound13`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound130`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound131`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound132`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound133`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound134`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound135`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound136`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound137`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound139`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound14`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound140`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound141`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound142`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound146`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound148`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound15`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound150`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound151`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound153`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound154`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound155`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound156`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound157`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound158`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound159`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound16`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound160`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound161`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound162`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound163`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound164`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound165`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound166`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound167`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound168`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound17`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound170`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound171`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound174`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound175`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound176`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound177`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound178`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound179`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound18`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound180`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound181`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound182`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound184`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound185`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound186`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound187`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound188`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound19`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound190`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound191`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound192`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound193`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound194`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound195`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound196`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound197`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound198`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound199`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound2`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound20`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound200`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound201`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound202`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound204`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound205`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound207`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound208`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound209`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound21`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound210`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound211`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound213`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound214`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound216`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound218`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound219`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound22`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound221`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound222`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound223`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound224`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound225`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound226`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound227`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound228`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound229`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound23`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound230`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound231`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound232`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound233`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound234`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound235`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound236`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound237`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound238`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound239`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound24`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound240`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound241`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound242`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound243`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound244`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound245`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound246`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound248`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound249`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound25`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound250`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound253`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound254`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound26`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound27`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound28`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound3`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound30`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound31`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound32`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound34`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound35`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound36`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound38`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound39`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound4`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound40`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound41`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound42`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound43`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound44`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound45`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound46`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound47`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound49`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound5`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound51`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound52`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound53`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound54`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound56`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound57`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound58`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound59`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound6`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound60`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound61`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound62`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound63`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound64`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound65`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound66`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound67`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound69`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound70`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound72`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound74`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound76`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound77`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound78`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound79`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound8`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound80`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound81`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound82`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound83`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound84`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound85`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound86`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound87`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound89`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound9`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound90`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound91`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound92`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound93`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound94`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound95`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound96`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound97`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound98`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound99`, `OAI.MUB6.Certificate.PairTargetSemantics.partition12`, `OAI.MUB6.Certificate.PairTargetSemantics.partition16`, `OAI.MUB6.Certificate.PairTargetSemantics.partition19`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm11`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm21`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm23`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm26`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm6`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm7`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm8` and `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm9`.
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

def raw0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw215 : Matrix (Fin 2) (Fin 2) ℤ := ![![-4, 4], ![4, -4]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix6 : Matrix (Fin 3) (Fin 2) ℤ := ![![1, -1], ![-5, 5], ![4, -4]]

def pivotMatrix8 : Matrix (Fin 3) (Fin 2) ℤ := ![![1, -1], ![-4, 4], ![3, -3]]

def pivotPermutation10 : Equiv.Perm (Fin 3) where
  toFun := ![1, 0, 2]
  invFun := ![1, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation11 : Equiv.Perm (Fin 3) where
  toFun := ![1, 0, 2]
  invFun := ![1, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation12 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix46 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]

def pivotMatrix47 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -4, 5], ![1, 3, -4]]

def pivotMatrix48 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![-4, 2, 2], ![5, -2, -3]]

def pivotMatrix49 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![-4, 3, 1], ![5, -3, -2]]

def pivotMatrix50 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 0, -1], ![-1, -4, 5], ![0, 4, -4]]

def pivotMatrix51 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -3, 4], ![1, 2, -3]]

def pivotMatrix52 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![4, -2, -2]]

def pivotMatrix53 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 0, -1], ![-1, -3, 4], ![0, 3, -3]]

def pivotMatrix54 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -1, 0], ![-1, -3, 4], ![0, 4, -4]]

def pivotMatrix55 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 5, -2], ![4, -5, 1]]

def pivotMatrix56 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -2, 3], ![1, 1, -2]]

def pivotMatrix57 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 0, -1], ![-1, -2, 3], ![0, 2, -2]]

def pivotMatrix58 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -1, 0], ![-1, -2, 3], ![0, 3, -3]]

def pivotMatrix59 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 4, -2], ![3, -4, 1]]

def pivotMatrix60 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 5, -3], ![3, -5, 2]]

def pivotMatrix61 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -1, 2], ![1, 0, -1]]

def pivotMatrix62 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -1, 0], ![-1, -1, 2], ![0, 2, -2]]

def pivotMatrix63 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 3, -2], ![2, -3, 1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix64 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![1, -1, 0]]

def pivotMatrix65 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def pivotMatrix66 : Matrix (Fin 5) (Fin 2) ℤ := ![![1, -1], ![-5, 5], ![1, -1], ![1, -1], ![2, -2]]

def pivotMatrix67 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-4, 4], ![1, -1], ![1, -1], ![3, -3]]

def pivotMatrix68 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-4, 4], ![1, -1], ![2, -2], ![2, -2]]

def pivotMatrix69 : Matrix (Fin 5) (Fin 2) ℤ := ![![1, -1], ![-4, 4], ![1, -1], ![1, -1], ![1, -1]]

def pivotMatrix70 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -2, 5], ![0, 2, -2], ![3, -1, -2]]

def pivotMatrix71 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -2, 5], ![1, -1, 0], ![2, 2, -4]]

def pivotMatrix72 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -2, 5], ![1, 2, -3], ![2, -1, -1]]

def pivotMatrix73 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-3, -2, 5], ![0, 2, -2], ![2, 1, -3]]

def pivotMatrix75 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-3, -2, 5], ![0, 3, -3], ![2, 0, -2]]

def pivotMatrix76 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-3, -2, 5], ![0, 3, -3], ![2, -1, -1]]

def pivotMatrix77 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-3, -2, 5], ![1, 0, -1], ![1, 3, -4]]

def pivotMatrix78 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-3, -2, 5], ![1, 1, -2], ![1, 2, -3]]

def pivotMatrix79 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-3, -1, 4], ![0, 3, -3], ![3, -1, -2]]

def pivotMatrix80 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-3, -1, 4], ![1, 3, -4], ![2, -1, -1]]

def pivotMatrix81 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -1, 4], ![0, 2, -2], ![3, -2, -1]]

def pivotMatrix82 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -1, 4], ![1, -2, 1], ![2, 2, -4]]

def pivotMatrix83 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -1, 4], ![1, 2, -3], ![2, -2, 0]]

def pivotMatrix87 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-3, -1, 4], ![0, 3, -3], ![2, -1, -1]]

def pivotMatrix88 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-3, -1, 4], ![0, 3, -3], ![2, -2, 0]]

def pivotMatrix90 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-3, -1, 4], ![1, -1, 0], ![1, 3, -4]]

def pivotMatrix92 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 0, 3], ![0, 3, -3], ![3, -2, -1]]

def pivotMatrix93 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 0, 3], ![0, 2, -2], ![3, -3, 0]]

def pivotMatrix94 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 0, 3], ![1, -3, 2], ![2, 2, -4]]

def pivotMatrix95 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 0, 3], ![1, 2, -3], ![2, -3, 1]]

def pivotPermutation102 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation105 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation106 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation107 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation108 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation109 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation113 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation116 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation117 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation118 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation119 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation120 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation121 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation122 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation123 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation124 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix640 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, -2, 2], ![1, 1, -2], ![1, 2, -3]]

def pivotMatrix641 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]

def pivotMatrix642 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]

def pivotMatrix644 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![0, -2, 2], ![1, -2, 1], ![1, 3, -4]]

def pivotMatrix645 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

def pivotMatrix646 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]

def pivotMatrix647 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

def pivotMatrix648 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

def pivotMatrix649 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![-2, 0, 2], ![0, -2, 2], ![0, 4, -4], ![1, -2, 1]]

def pivotMatrix650 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-2, 0, 2], ![0, -2, 2], ![0, 4, -4], ![1, -1, 0]]

def pivotMatrix651 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![2, -1, -1]]

def pivotMatrix652 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, -1, 1], ![1, -2, 1], ![1, 4, -5]]

def pivotMatrix653 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def pivotMatrix654 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]

def pivotMatrix655 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def pivotMatrix656 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def pivotMatrix657 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -3, 2], ![1, 3, -4]]

def pivotMatrix658 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

def pivotMatrix659 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def pivotMatrix660 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def pivotMatrix661 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix662 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def pivotMatrix663 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def pivotMatrix664 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, 4, -4], ![1, -3, 2], ![1, 0, -1]]

def pivotMatrix665 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, 4, -4], ![1, -2, 1], ![1, -1, 0]]

def pivotMatrix666 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2]]

def pivotMatrix667 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

def pivotMatrix668 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]

def pivotMatrix669 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1]]

def pivotMatrix670 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]

def pivotMatrix671 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![0, 3, -3], ![1, -3, 2], ![1, -1, 0]]

def pivotMatrix672 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![0, 3, -3], ![1, -2, 1], ![1, -2, 1]]

def pivotMatrix694 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 3, -4]]

def pivotMatrix695 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 3, -4]]

def pivotMatrix696 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 1, 1], ![0, -3, 3], ![1, -1, 0], ![1, 2, -3]]

def pivotMatrix697 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 1, 1], ![0, -3, 3], ![1, 0, -1], ![1, 1, -2]]

def pivotMatrix698 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-2, 1, 1], ![0, -3, 3], ![0, 2, -2], ![1, 1, -2]]

def pivotMatrix699 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![-2, 1, 1], ![0, -3, 3], ![0, 2, -2], ![1, 0, -1]]

def pivotMatrix700 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-2, 1, 1], ![0, -3, 3], ![0, 3, -3], ![1, 0, -1]]

def pivotMatrix701 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

def pivotMatrix702 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix704 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1]]

def pivotMatrix705 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2]]

def pivotMatrix706 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

def pivotMatrix707 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 3, -4]]

def pivotMatrix708 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]

def pivotMatrix709 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]

def pivotMatrix710 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def pivotMatrix711 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix715 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![-2, 2], ![1, -1], ![2, -2], ![2, -2]]

def pivotMatrix716 : Matrix (Fin 6) (Fin 2) ℤ := ![![1, -1], ![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]

def pivotMatrix717 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]

def pivotMatrix721 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -4, 5], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2]]

def pivotMatrix722 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -4, 5], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix723 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -4, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]

def pivotMatrix724 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -4, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

def pivotMatrix725 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-3, 0, 1, 2], ![1, 2, -2, -1], ![3, -2, 1, -2]]

def pivotMatrix726 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-3, 0, 2, 1], ![1, 2, -2, -1], ![3, -2, 0, -1]]

def pivotMatrix727 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-3, 0, 3, 0], ![1, 2, -1, -2], ![3, -2, -2, 1]]

def pivotMatrix728 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-3, 0, 1, 2], ![2, -2, 1, -1], ![2, 2, -2, -2]]

def pivotMatrix729 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-3, 0, 3, 0], ![2, -2, -1, 1], ![2, 2, -2, -2]]

def pivotMatrix730 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-3, 1, 1, 1], ![2, -2, 1, -1], ![2, 1, -2, -1]]

def pivotMatrix731 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-3, 1, 2, 0], ![2, -2, -1, 1], ![2, 1, -1, -2]]

def pivotMatrix732 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

def pivotMatrix733 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

def pivotMatrix734 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix735 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![0, -1, 1], ![1, 1, -2], ![1, 2, -3]]

def pivotMatrix736 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def pivotMatrix737 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def pivotMatrix738 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def pivotMatrix739 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix740 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix741 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -3, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

def pivotMatrix742 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -3, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix743 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-1, -3, 4], ![-1, 2, -1], ![0, 2, -2], ![1, 0, -1]]

def pivotMatrix744 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -3, 4], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix745 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -3, 4], ![-1, 4, -3], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix746 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![1, 2, -3]]

def pivotMatrix747 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -3, 4], ![0, 1, -1], ![0, 3, -3], ![1, 0, -1]]

def pivotMatrix748 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def pivotMatrix749 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -3, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def pivotMatrix750 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, -2, 5], ![0, 1, 1, -2], ![1, 1, 0, -2]]

def pivotMatrix751 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, -2, 5], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def pivotMatrix752 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![-2, 2, 1, -1], ![5, -2, -2, -1]]

def pivotMatrix753 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 2, 0], ![-2, 2, -1, 1], ![5, -2, -1, -2]]

def pivotMatrix754 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, -2, -2, 5], ![0, 0, 2, -2], ![0, 2, 0, -2]]

def pivotMatrix755 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, -2, -2, 5], ![0, 1, 1, -2], ![0, 1, 1, -2]]

def pivotMatrix756 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, -1, 1, 2], ![-1, 2, 1, -2], ![4, -1, -2, -1]]

def pivotMatrix757 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, -1, 2, 1], ![-1, 2, -2, 1], ![4, -1, 0, -3]]

def pivotMatrix758 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, -1, 2, 1], ![-1, 2, 1, -2], ![4, -1, -3, 0]]

def pivotMatrix759 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, -1, 3, 0], ![-1, 2, -2, 1], ![4, -1, -1, -2]]

def pivotMatrix760 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, -1, 4], ![0, 0, 2, -2], ![1, 2, 0, -3]]

def pivotMatrix761 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, -1, 4], ![0, 1, 1, -2], ![1, 1, 1, -3]]

def pivotMatrix762 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, -1, 4], ![0, 1, 2, -3], ![1, 1, 0, -2]]

def pivotMatrix763 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, -1, 4], ![0, 2, 0, -2], ![1, 0, 2, -3]]

def pivotMatrix764 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, -1, 4], ![0, 2, 1, -3], ![1, 0, 1, -2]]

def pivotMatrix765 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, -1, 4], ![0, 0, 2, -2], ![1, 2, -2, -1]]

def pivotMatrix766 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, -1, 4], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def pivotMatrix767 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, -1, 4], ![0, 1, 2, -3], ![1, 1, -2, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix768 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, -1, 4], ![0, 2, -2, 0], ![1, 0, 2, -3]]

def pivotMatrix769 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, -1, 4], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def pivotMatrix770 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![-1, 2, -2, 1], ![4, -2, 1, -3]]

def pivotMatrix771 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -2, -1, 4], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def pivotMatrix772 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![-1, 2, 1, -2], ![4, -2, -2, 0]]

def pivotMatrix773 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 2, 0], ![-1, 2, -2, 1], ![4, -2, 0, -2]]

def pivotMatrix774 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, -1, -1]]

def pivotMatrix775 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, 0, -2]]

def pivotMatrix776 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 2, 0], ![-1, 2, 1, -2], ![4, -2, -3, 1]]

def pivotMatrix777 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 3, -1], ![-1, 2, -2, 1], ![4, -2, -1, -1]]

def pivotMatrix778 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![-1, 3, -2, 0], ![4, -3, 1, -2]]

def pivotMatrix779 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -2, -1, 4], ![0, 0, 3, -3], ![1, 1, -1, -1]]

def pivotMatrix780 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -2, -1, 4], ![0, 0, 3, -3], ![1, 1, -2, 0]]

def pivotMatrix781 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, -2, -1, 4], ![0, 0, 3, -3], ![0, 2, -2, 0]]

def pivotMatrix782 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-1, -2, -1, 4], ![0, 0, 3, -3], ![0, 2, -1, -1]]

def pivotMatrix783 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 2, 0], ![-1, 3, 0, -2], ![4, -3, -2, 1]]

def pivotMatrix784 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![-1, -2, 1, 2], ![4, 1, -2, -3]]

def pivotMatrix785 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![-1, -2, 2, 1], ![4, 1, -3, -2]]

def pivotMatrix786 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -2, -1, 4], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def pivotMatrix787 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-1, -2, -1, 4], ![0, 1, 1, -2], ![0, 1, 1, -2]]

def pivotMatrix788 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![-1, 1, 2, -2], ![4, -2, -3, 1]]

def pivotMatrix789 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 0, 2], ![0, -2, 2, 0], ![3, 2, -2, -3]]

def pivotMatrix790 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![0, -2, 1, 1], ![3, 2, -2, -3]]

def pivotMatrix791 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![0, -2, 2, 0], ![3, 2, -3, -2]]

def pivotMatrix792 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![0, -2, 3, -1], ![3, 2, -4, -1]]

def pivotMatrix793 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 2, 0], ![0, -2, 0, 2], ![3, 2, -2, -3]]

def pivotMatrix794 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 2, 0], ![0, -2, 1, 1], ![3, 2, -3, -2]]

def pivotMatrix795 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 2, 2, -4]]

def pivotMatrix796 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 0, 3], ![0, 0, 2, -2], ![1, 2, -1, -2]]

def pivotMatrix797 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 0, 3], ![0, 1, 2, -3], ![1, 1, -1, -1]]

def pivotMatrix798 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 0, 3], ![0, 1, 3, -4], ![1, 1, -2, 0]]

def pivotMatrix799 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 0, 3], ![0, 2, -1, -1], ![1, 0, 2, -3]]

def pivotMatrix800 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, 0, 3], ![0, 1, -2, 1], ![1, 1, 1, -3]]

def pivotMatrix801 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, 0, 3], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def pivotMatrix802 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, 0, 3], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def pivotMatrix803 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, 0, 3], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def pivotMatrix804 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![0, 2, -2, 0], ![3, -2, 1, -2]]

def pivotMatrix805 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -2, 0, 3], ![0, 0, 2, -2], ![1, 1, -1, -1]]

def pivotMatrix806 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, -2, 0]]

def pivotMatrix807 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, -1, -1]]

def pivotMatrix808 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 2, 0], ![0, 2, 0, -2], ![3, -2, -2, 1]]

def pivotMatrix809 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![0, 3, -2, -1], ![3, -3, 1, -1]]

def pivotMatrix810 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -2, 0, 3], ![0, 0, 3, -3], ![1, 1, -2, 0]]

def pivotMatrix811 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-1, -2, 0, 3], ![0, 0, 3, -3], ![0, 2, -2, 0]]

def pivotMatrix812 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 2, 0], ![0, 3, -1, -2], ![3, -3, -1, 1]]

def pivotMatrix813 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![0, 4, -2, -2], ![3, -4, 1, 0]]

def pivotMatrix814 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 2, 0], ![0, 4, -2, -2], ![3, -4, 0, 1]]

def pivotMatrix815 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![0, -2, 1, 1], ![3, 1, -2, -2]]

def pivotMatrix816 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, -2, 0, 3], ![0, 1, -2, 1], ![0, 1, 2, -3]]

def pivotMatrix817 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-1, -2, 0, 3], ![0, 1, -2, 1], ![0, 1, 3, -4]]

def pivotMatrix818 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -2, 0, 3], ![0, 1, 3, -4], ![1, 0, -2, 1]]

def pivotMatrix819 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -2, 0, 3], ![0, 1, 2, -3], ![1, 0, -2, 1]]

def pivotMatrix820 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![0, 1, 1, -2], ![3, -2, -2, 1]]

def pivotMatrix821 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, -1, 2, 1], ![1, -1, 2, -2], ![2, 2, -4, 0]]

def pivotMatrix822 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, -1, 1, 2], ![1, 2, -2, -1], ![2, -1, 1, -2]]

def pivotMatrix823 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, -1, 2, 1], ![1, 2, -3, 0], ![2, -1, 1, -2]]

def pivotMatrix824 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, -1, 3, 0], ![1, 2, -1, -2], ![2, -1, -2, 1]]

def pivotMatrix825 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 0, 2], ![1, -2, 2, -1], ![2, 2, -2, -2]]

def pivotMatrix826 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -2, 1, 2], ![0, 0, -2, 2], ![1, 1, 2, -4]]

def pivotMatrix827 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -2, 1, 2], ![0, 0, -2, 2], ![1, 1, 1, -3]]

def pivotMatrix828 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![1, -2, 1, 0], ![2, 2, -2, -2]]

def pivotMatrix829 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![1, -2, 2, -1], ![2, 2, -3, -1]]

def pivotMatrix830 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![1, -2, 3, -2], ![2, 2, -4, 0]]

def pivotMatrix831 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 2, 0], ![1, -2, 0, 1], ![2, 2, -2, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix832 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 2, 1, -3]]

def pivotMatrix833 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 2, 2, -4]]

def pivotMatrix834 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 1, 2], ![0, 1, -2, 1], ![1, 1, 2, -4]]

def pivotMatrix835 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 1, 2], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def pivotMatrix836 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 1, 2], ![0, 1, 2, -3], ![1, 1, -2, 0]]

def pivotMatrix837 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 1, 2], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def pivotMatrix838 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, 1, 2], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def pivotMatrix839 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, 1, 2], ![0, 2, -3, 1], ![1, 0, 1, -2]]

def pivotMatrix840 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, 1, 2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def pivotMatrix841 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![1, 2, -3, 0], ![2, -2, 2, -2]]

def pivotMatrix842 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![1, 2, -2, -1], ![2, -2, 1, -1]]

def pivotMatrix843 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, -2, 1, 2], ![0, 0, 2, -2], ![0, 2, -3, 1]]

def pivotMatrix844 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 2, 0], ![1, 2, -1, -2], ![2, -2, -1, 1]]

def pivotMatrix845 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -2, 1, 2], ![0, 1, -2, 1], ![1, 0, 1, -2]]

def pivotMatrix846 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, -2, 1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2]]

def pivotMatrix847 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-1, -2, 1, 2], ![0, 1, -2, 1], ![0, 1, 2, -3]]

def pivotMatrix848 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![1, -2, 3, -2], ![2, 1, -4, 1]]

def pivotMatrix849 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 2, -1], ![1, -2, 2, -1], ![2, 1, -4, 1]]

def pivotMatrix850 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -2, 1, 2], ![0, 1, 2, -3], ![1, 0, -2, 1]]

def pivotMatrix851 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 2, -1], ![1, 1, -3, 1], ![2, -2, 1, -1]]

def pivotMatrix852 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 2, -1], ![1, 2, -2, -1], ![2, -3, 0, 1]]

def pivotMatrix853 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -2, 2, 1], ![0, 0, -2, 2], ![1, 1, 0, -2]]

def pivotMatrix854 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, -2, 2, 1], ![0, 0, -2, 2], ![0, 2, 0, -2]]

def pivotMatrix855 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -2, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 2, -3]]

def pivotMatrix856 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -2, 3], ![-1, -1, 2], ![1, 1, -2], ![1, 1, -2]]

def pivotMatrix857 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-1, -2, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 2, -3]]

def pivotMatrix858 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![-1, -2, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2]]

def pivotMatrix859 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-1, -2, 3], ![-1, -1, 2], ![0, 3, -3], ![1, 1, -2]]

def pivotMatrix860 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![-1, -2, 3], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1]]

def pivotMatrix861 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-1, -2, 3], ![-1, -1, 2], ![0, 4, -4], ![1, 0, -1]]

def pivotMatrix862 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def pivotMatrix863 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def pivotMatrix864 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix865 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

def pivotMatrix866 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]

def pivotMatrix867 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

def pivotMatrix868 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def pivotMatrix869 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix870 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -2, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2]]

def pivotMatrix871 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -2, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2]]

def pivotMatrix872 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix873 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![-1, -2, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -2, 1]]

def pivotMatrix874 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![-1, -2, 3], ![-1, 3, -2], ![0, -2, 2], ![1, 1, -2]]

def pivotMatrix875 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -2, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 1, -2]]

def pivotMatrix876 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -2, 3], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix877 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![-1, -2, 3], ![-1, 4, -3], ![0, -2, 2], ![1, 0, -1]]

def pivotMatrix878 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -2, 3], ![0, -2, 2], ![0, 1, -1], ![1, 2, -3]]

def pivotMatrix879 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -2, 3], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

def pivotMatrix880 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -2, 3], ![0, -1, 1], ![0, 4, -4], ![1, 0, -1]]

def pivotMatrix881 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]

def pivotMatrix882 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

def pivotMatrix883 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0]]

def pivotMatrix884 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def pivotMatrix885 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1]]

def pivotMatrix886 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 1, 1], ![-3, 2, 1, 0], ![5, -1, -2, -2]]

def pivotMatrix887 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![-3, 2, 0, 1], ![5, -1, -2, -2]]

def pivotMatrix888 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -3, 5], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def pivotMatrix889 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -3, 5], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def pivotMatrix890 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, -3, 5], ![0, 0, 2, -2], ![1, 0, 1, -2]]

def pivotMatrix892 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, -2, 4], ![0, 2, -1, -1], ![1, 0, 2, -3]]

def pivotMatrix893 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -2, 4], ![0, -1, 2, -1], ![1, 1, 1, -3]]

def pivotMatrix894 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 1, 1], ![-2, 2, 1, -1], ![4, -1, -2, -1]]

def pivotMatrix895 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![-2, 2, -2, 2], ![4, -1, 0, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix896 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![-2, 2, -1, 1], ![4, -1, -1, -2]]

def pivotMatrix897 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 2, 1, -3]]

def pivotMatrix898 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -2, 4], ![0, -1, 3, -2], ![1, 1, 0, -2]]

def pivotMatrix899 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, -2, 4], ![0, -1, 3, -2], ![1, 1, -1, -1]]

def pivotMatrix900 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 1, 1], ![-2, 3, 1, -2], ![4, -2, -2, 0]]

def pivotMatrix901 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![-2, 3, -2, 1], ![4, -2, 0, -2]]

def pivotMatrix902 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, -1, -2, 4], ![0, -1, 3, -2], ![0, 2, -1, -1]]

def pivotMatrix903 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-1, -1, -2, 4], ![0, -1, 3, -2], ![0, 2, 0, -2]]

def pivotMatrix904 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, -2, 4], ![0, 0, 2, -2], ![1, 1, 1, -3]]

def pivotMatrix905 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, -2, 4], ![0, 0, 3, -3], ![1, 1, 0, -2]]

def pivotMatrix906 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -2, 4], ![0, 0, 1, -1], ![1, 1, 0, -2]]

def pivotMatrix907 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -2, 4], ![0, 0, 2, -2], ![1, 1, -1, -1]]

def pivotMatrix908 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -2, 4], ![0, 0, 3, -3], ![1, 1, -2, 0]]

def pivotMatrix909 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -2, 4], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def pivotMatrix910 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -2, 4], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def pivotMatrix911 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -2, 4], ![0, 2, -1, -1], ![1, -1, 2, -2]]

def pivotMatrix912 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![-2, 2, 2, -2], ![4, -2, -2, 0]]

def pivotMatrix913 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 1, 0], ![-2, 2, -2, 2], ![4, -2, 1, -3]]

def pivotMatrix914 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -2, 4], ![0, 0, 2, -2], ![1, 0, 1, -2]]

def pivotMatrix915 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, -2, 4], ![0, 0, 2, -2], ![1, 0, 0, -1]]

def pivotMatrix916 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![-2, 2, -2, 2], ![4, -2, 0, -2]]

def pivotMatrix917 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![-2, 2, -1, 1], ![4, -2, -1, -1]]

def pivotMatrix918 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 1, 0], ![-2, 3, -2, 1], ![4, -3, 1, -2]]

def pivotMatrix919 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -2, 4], ![0, 0, 3, -3], ![1, 0, 0, -1]]

def pivotMatrix920 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, -1, -2, 4], ![0, 0, 3, -3], ![0, 2, -1, -1]]

def pivotMatrix921 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -2, 4], ![0, 1, 1, -2], ![1, -1, 2, -2]]

def pivotMatrix922 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -2, 4], ![0, 1, 2, -3], ![1, -1, 1, -1]]

def pivotMatrix923 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![-2, 1, 2, -1], ![4, -2, -3, 1]]

def pivotMatrix927 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -2, 2, 1], ![-1, 1, 2, -2], ![3, 1, -4, 0]]

def pivotMatrix928 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -2, 2, 1], ![-1, 2, 1, -2], ![3, 0, -3, 0]]

def pivotMatrix929 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -2, 3, 0], ![-1, 2, 1, -2], ![3, 0, -4, 1]]

def pivotMatrix930 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 1, 1], ![-1, -1, 1, 1], ![3, 2, -2, -3]]

def pivotMatrix931 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 1, 1], ![-1, -1, 2, 0], ![3, 2, -3, -2]]

def pivotMatrix932 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![-1, -1, -1, 3], ![3, 2, -1, -4]]

def pivotMatrix933 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, -1, 3], ![0, 1, 2, -3], ![1, 1, -1, -1]]

def pivotMatrix934 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, -1, 3], ![0, 1, 3, -4], ![1, 1, -2, 0]]

def pivotMatrix935 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, -1, 3], ![0, 2, -2, 0], ![1, 0, 3, -4]]

def pivotMatrix936 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, -1, 3], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def pivotMatrix937 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, -1, 3], ![0, 1, 2, -3], ![1, 1, -2, 0]]

def pivotMatrix938 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, -1, 3], ![0, 2, -2, 0], ![1, 0, 2, -3]]

def pivotMatrix939 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, -1, 3], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def pivotMatrix940 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, -1, 3], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def pivotMatrix941 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 1, 1], ![-1, 2, -2, 1], ![3, -1, 1, -3]]

def pivotMatrix942 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, -1, 3], ![0, -1, 2, -1], ![1, 1, -1, -1]]

def pivotMatrix943 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 1, 1], ![-1, 2, 1, -2], ![3, -1, -2, 0]]

def pivotMatrix944 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![-1, 2, -2, 1], ![3, -1, 0, -2]]

def pivotMatrix945 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, -1, -1]]

def pivotMatrix946 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, 0, -2]]

def pivotMatrix947 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![-1, 2, 1, -2], ![3, -1, -3, 1]]

def pivotMatrix948 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 1, 1], ![-1, 3, -2, 0], ![3, -2, 1, -2]]

def pivotMatrix949 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -1, 3], ![0, -1, 3, -2], ![1, 1, -1, -1]]

def pivotMatrix950 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, -1, 3], ![0, -1, 3, -2], ![1, 1, -2, 0]]

def pivotMatrix951 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 2, -2, 0]]

def pivotMatrix952 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 2, -1, -1]]

def pivotMatrix953 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![-1, 3, 0, -2], ![3, -2, -2, 1]]

def pivotMatrix954 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![-1, 4, -1, -2], ![3, -3, -1, 1]]

def pivotMatrix955 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![-1, -2, 2, 1], ![3, 2, -2, -3]]

def pivotMatrix956 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![-1, -2, 3, 0], ![3, 2, -3, -2]]

def pivotMatrix957 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![-1, -2, 4, -1], ![3, 2, -4, -1]]

def pivotMatrix958 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 1, 0], ![-1, -2, 1, 2], ![3, 2, -2, -3]]

def pivotMatrix959 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, -1, 3], ![0, 0, 2, -2], ![1, 1, 0, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix960 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, -1, 3], ![0, 0, 3, -3], ![1, 1, -1, -1]]

def pivotMatrix961 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, -1, 3], ![0, 0, 4, -4], ![1, 1, -2, 0]]

def pivotMatrix962 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, -1, 3], ![0, 1, -1, 0], ![1, 0, 3, -4]]

def pivotMatrix963 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, -1, 3], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def pivotMatrix964 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, -1, 3], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def pivotMatrix965 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, -1, 3], ![0, 2, -1, -1], ![1, -1, 3, -3]]

def pivotMatrix966 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -1, 3], ![0, 0, 1, -1], ![1, 1, -1, -1]]

def pivotMatrix967 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -1, 3], ![0, 0, 2, -2], ![1, 1, -2, 0]]

def pivotMatrix968 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -1, 3], ![0, 1, -2, 1], ![1, 0, 2, -3]]

def pivotMatrix969 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -1, 3], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def pivotMatrix970 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -1, 3], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def pivotMatrix971 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -1, 3], ![0, 2, -2, 0], ![1, -1, 2, -2]]

def pivotMatrix972 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -1, 3], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def pivotMatrix973 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 1, 0], ![-1, 2, -2, 1], ![3, -2, 1, -2]]

def pivotMatrix974 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -1, 3], ![0, 0, 2, -2], ![1, 0, 0, -1]]

def pivotMatrix975 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![-1, 2, -2, 1], ![3, -2, 0, -1]]

def pivotMatrix976 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![-1, 2, 0, -1], ![3, -2, -2, 1]]

def pivotMatrix977 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 1, -2, 1]]

def pivotMatrix978 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -1, 3], ![0, 0, 3, -3], ![1, 0, -1, 0]]

def pivotMatrix979 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 2, -2, 0]]

def pivotMatrix980 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![-1, 3, -1, -1], ![3, -3, -1, 1]]

def pivotMatrix981 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-1, -1, -1, 3], ![0, 0, 4, -4], ![0, 1, -2, 1]]

def pivotMatrix982 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, -1, 3], ![0, 1, -2, 1], ![1, -1, 3, -3]]

def pivotMatrix983 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![-1, -2, 1, 2], ![3, 1, -2, -2]]

def pivotMatrix984 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![-1, -2, 2, 1], ![3, 1, -3, -1]]

def pivotMatrix985 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, -1, -1, 3], ![0, 1, -2, 1], ![0, 1, 3, -4]]

def pivotMatrix986 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -1, 3], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def pivotMatrix987 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![-1, 1, 1, -1], ![3, -2, -2, 1]]

def pivotMatrix988 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -2, 2, 1], ![0, 1, 2, -3], ![2, 1, -4, 1]]

def pivotMatrix989 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -2, 2, 1], ![0, 3, -3, 0], ![2, -1, 1, -2]]

def pivotMatrix990 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -2, 3, 0], ![0, 3, -1, -2], ![2, -1, -2, 1]]

def pivotMatrix991 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 1, 1], ![0, -2, 2, 0], ![2, 3, -3, -2]]

def pivotMatrix992 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 1, 1], ![0, -2, 3, -1], ![2, 3, -4, -1]]

def pivotMatrix993 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![0, -2, 1, 1], ![2, 3, -3, -2]]

def pivotMatrix994 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, -1, 0, 2], ![0, -1, -2, 3], ![0, 2, 2, -4]]

def pivotMatrix995 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 1, 1], ![0, -1, 2, -1], ![2, 2, -3, -1]]

def pivotMatrix996 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 1, 1], ![0, -1, 3, -2], ![2, 2, -4, 0]]

def pivotMatrix997 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![0, -1, -2, 3], ![2, 2, 0, -4]]

def pivotMatrix998 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 2, 2, -4]]

def pivotMatrix999 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![0, -1, 3, -2], ![2, 2, -5, 1]]

def pivotPermutation1000 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1001 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1002 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1003 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1004 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1005 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1006 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1007 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1008 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1009 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1010 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1011 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1012 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1013 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1014 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1015 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1016 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1017 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1018 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1019 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1020 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1021 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1022 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1023 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotPermutation1024 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1025 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1026 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1027 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1028 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1029 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1030 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1031 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1032 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1033 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1034 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1035 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1036 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1037 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1038 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1039 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1040 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1041 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1042 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1043 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1044 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1045 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1046 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1047 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1048 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1049 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1050 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1051 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1052 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1053 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1054 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1055 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1056 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1057 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1058 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1059 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1060 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1061 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1062 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1063 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1064 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1065 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1066 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1067 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1068 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1069 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1070 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1071 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1072 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1073 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1074 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1075 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1076 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1077 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1078 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1079 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1080 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1081 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1082 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1083 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1084 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1085 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1086 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1087 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotPermutation1089 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1090 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1091 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1092 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1093 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1094 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1095 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1096 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1097 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1098 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1099 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1100 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1101 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1102 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1103 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1104 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1105 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1106 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1107 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1108 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1109 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1110 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1111 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1112 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1113 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1114 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1115 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1116 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1117 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1118 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1119 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1120 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1121 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1122 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1123 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1124 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1125 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1126 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1127 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1128 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1129 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1130 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1131 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1132 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1133 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1134 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1135 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1136 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1137 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1138 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1139 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1140 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1141 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1142 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1143 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1144 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1145 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1146 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1147 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1149 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1150 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1151 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotPermutation1152 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1153 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1154 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1155 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1156 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1157 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1158 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1159 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1160 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1161 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1162 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1163 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1164 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1165 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1166 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1167 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1168 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1169 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1170 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1171 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1172 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1173 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1174 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1175 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1176 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1177 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1178 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1179 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1180 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1181 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1182 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1183 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1184 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1185 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1186 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1187 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1188 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1189 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1190 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1191 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1192 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1193 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1194 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1195 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1196 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1197 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1198 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1199 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1200 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1201 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1202 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1203 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1204 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1205 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1206 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1207 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1208 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1209 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1210 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1211 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1212 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1213 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1214 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1215 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotPermutation1216 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1217 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1218 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1219 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1220 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1221 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1222 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1223 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1224 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1225 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1226 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1227 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1228 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1229 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1230 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1231 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1232 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1233 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1234 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1235 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1236 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1237 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1238 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1239 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1240 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1241 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix337 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]

def pivotMatrix338 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

def pivotMatrix339 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]

def pivotMatrix340 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 0, 3], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]

def pivotMatrix341 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]

def pivotMatrix342 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]

def pivotMatrix343 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

def pivotMatrix344 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]

def pivotMatrix345 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

def pivotMatrix346 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]

def pivotMatrix347 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]

def pivotMatrix348 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 0, 3], ![1, -3, 2], ![1, 0, -1], ![1, 2, -3]]

def pivotMatrix349 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 0, 3], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]

def pivotMatrix350 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

def pivotMatrix351 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def pivotMatrix352 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 2, -4]]

def pivotMatrix353 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]

def pivotMatrix354 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![3, -1, -2]]

def pivotMatrix355 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]

def pivotMatrix356 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]

def pivotMatrix357 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![2, 0, -2]]

def pivotMatrix358 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]

def pivotMatrix359 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

def pivotMatrix360 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 2, -3]]

def pivotMatrix361 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]

def pivotMatrix362 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]

def pivotMatrix363 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]

def pivotMatrix364 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]

def pivotMatrix365 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]

def pivotMatrix366 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]

def pivotMatrix367 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]

def pivotMatrix368 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]

def pivotMatrix369 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

def pivotMatrix370 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 3, -4]]

def pivotMatrix371 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]

def pivotMatrix372 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

def pivotMatrix373 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]

def pivotMatrix374 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]

def pivotMatrix375 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 1, 2], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]

def pivotMatrix376 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]

def pivotMatrix377 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

def pivotMatrix378 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]

def pivotMatrix379 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]

def pivotMatrix380 : Matrix (Fin 6) (Fin 2) ℤ := ![![1, -1], ![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]

def pivotMatrix381 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![3, -3]]

def pivotMatrix382 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-3, 3], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]

def pivotMatrix383 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-3, 3], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix384 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def pivotMatrix385 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -3, 5], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def pivotMatrix386 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -3, 5], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def pivotMatrix387 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -3, 5], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def pivotMatrix388 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -3, 5], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def pivotMatrix389 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -3, 5], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix390 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -3, 5], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix414 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, -2, 4], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]

def pivotMatrix415 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, -2, 4], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]

def pivotMatrix416 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]

def pivotMatrix417 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, -2, 4], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

def pivotMatrix418 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, -2, 4], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]

def pivotMatrix419 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -2, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]

def pivotMatrix420 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

def pivotMatrix421 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -2, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

def pivotMatrix422 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]

def pivotMatrix423 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-2, -2, 4], ![-1, 2, -1], ![0, 2, -2], ![2, -1, -1]]

def pivotMatrix424 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![-2, -2, 4], ![-1, 2, -1], ![0, 2, -2], ![2, -2, 0]]

def pivotMatrix425 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-2, -2, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 2, -3]]

def pivotMatrix426 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -2, 4], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]

def pivotMatrix427 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-2, -2, 4], ![-1, 3, -2], ![1, -1, 0], ![1, 1, -2]]

def pivotMatrix428 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-2, -2, 4], ![-1, 4, -3], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix429 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]

def pivotMatrix430 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

def pivotMatrix431 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -2, 4], ![0, 1, -1], ![1, -1, 0], ![1, 3, -4]]

def pivotMatrix432 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -2, 4], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

def pivotMatrix433 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -2, 4], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

def pivotMatrix434 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -2, 4], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def pivotMatrix435 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -2, 4], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix436 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -2, 4], ![0, 4, -4], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix437 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def pivotMatrix438 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def pivotMatrix439 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -2, 4], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

def pivotMatrix440 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -2, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def pivotMatrix441 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -2, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix442 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -2, 4], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def pivotMatrix443 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix444 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -2, 4], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def pivotMatrix445 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -2, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def pivotMatrix446 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-2, -2, 4], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix524 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![-1, -1, 2], ![1, 2, -3], ![2, -1, -1]]

def pivotMatrix525 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![2, 1, -3]]

def pivotMatrix527 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, -1, 3], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]

def pivotMatrix528 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]

def pivotMatrix529 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, -1, 3], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

def pivotMatrix530 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]

def pivotMatrix531 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]

def pivotMatrix532 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]

def pivotMatrix533 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]

def pivotMatrix535 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]

def pivotMatrix536 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]

def pivotMatrix537 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]

def pivotMatrix538 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 2, -3]]

def pivotMatrix539 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2]]

def pivotMatrix540 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-2, -1, 3], ![-1, 4, -3], ![1, -2, 1], ![1, 0, -1]]

def pivotMatrix541 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![2, 1, -3]]

def pivotMatrix542 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![2, 0, -2]]

def pivotMatrix543 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

def pivotMatrix544 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 2, -3]]

def pivotMatrix545 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]

def pivotMatrix546 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, 2, -3]]

def pivotMatrix547 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

def pivotMatrix548 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![1, 1, -2]]

def pivotMatrix549 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

def pivotMatrix550 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-2, -1, 3], ![0, -2, 2], ![0, 4, -4], ![1, 0, -1]]

def pivotMatrix551 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![2, 0, -2]]

def pivotMatrix552 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 4, -5]]

def pivotMatrix553 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 3, -4]]

def pivotMatrix554 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 2, -3]]

def pivotMatrix555 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def pivotMatrix556 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def pivotMatrix558 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 3, -4]]

def pivotMatrix559 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def pivotMatrix560 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def pivotMatrix561 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def pivotMatrix562 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix563 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix564 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, 4, -4], ![1, -2, 1], ![1, 0, -1]]

def pivotMatrix565 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

def pivotMatrix566 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

def pivotMatrix567 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]

def pivotMatrix568 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![0, 1, -1], ![1, -3, 2], ![1, 2, -3]]

def pivotMatrix569 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def pivotMatrix570 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix571 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

def pivotMatrix572 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

def pivotMatrix573 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

def pivotMatrix574 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

def pivotMatrix575 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix623 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2], ![1, 3, -4], ![2, -2, 0]]

def pivotMatrix624 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

def pivotMatrix626 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]

def pivotMatrix627 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-2, 0, 2], ![-1, 3, -2], ![1, -3, 2], ![1, 1, -2]]

def pivotMatrix628 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-2, 0, 2], ![-1, 4, -3], ![0, -2, 2], ![2, -1, -1]]

def pivotMatrix629 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-2, 0, 2], ![-1, 4, -3], ![1, -3, 2], ![1, 0, -1]]

def pivotMatrix630 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![-2, 0, 2], ![-1, 4, -3], ![1, -2, 1], ![1, -2, 1]]

def pivotMatrix631 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![0, -3, 3], ![0, 2, -2], ![2, 0, -2]]

def pivotMatrix632 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![0, -3, 3], ![1, -1, 0], ![1, 3, -4]]

def pivotMatrix633 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![0, -3, 3], ![1, 0, -1], ![1, 2, -3]]

def pivotMatrix634 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]

def pivotMatrix635 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![-2, 0, 2], ![0, -3, 3], ![0, 2, -2], ![1, 1, -2]]

def pivotMatrix636 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![-2, 0, 2], ![0, -3, 3], ![0, 3, -3], ![1, 0, -1]]

def pivotMatrix637 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-2, 0, 2], ![0, -3, 3], ![0, 4, -4], ![1, 0, -1]]

def pivotMatrix638 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 4, -5]]

def pivotMatrix639 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, -2, 2], ![1, 0, -1], ![1, 3, -4]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix3360 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def pivotMatrix3361 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def pivotMatrix3362 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def pivotMatrix3363 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def pivotMatrix3364 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def pivotMatrix3365 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -1, 3], ![-1, 1, -1, 1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def pivotMatrix3366 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def pivotMatrix3367 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def pivotMatrix3368 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def pivotMatrix3369 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -2, 1]]

def pivotMatrix3370 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def pivotMatrix3371 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def pivotMatrix3372 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def pivotMatrix3373 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def pivotMatrix3374 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def pivotMatrix3375 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def pivotMatrix3376 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 0, 2], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def pivotMatrix3377 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 0, 2], ![-1, 0, -1, 2], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def pivotMatrix3378 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def pivotMatrix3379 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def pivotMatrix3380 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 1, 0, -1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def pivotMatrix3381 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def pivotMatrix3382 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def pivotMatrix3383 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def pivotMatrix3384 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def pivotMatrix3385 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def pivotMatrix3386 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 3, -3], ![1, 0, -2, 1]]

def pivotMatrix3387 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 3, -4]]

def pivotMatrix3388 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def pivotMatrix3389 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def pivotMatrix3390 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def pivotMatrix3391 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix3392 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def pivotMatrix3393 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def pivotMatrix3394 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def pivotMatrix3395 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def pivotMatrix3396 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, -1, 0, 0]]

def pivotMatrix3397 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def pivotMatrix3398 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 1, 1], ![-1, -1, 1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def pivotMatrix3399 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 1, 1], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def pivotMatrix3400 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def pivotMatrix3401 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def pivotMatrix3402 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def pivotMatrix3403 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def pivotMatrix3404 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def pivotMatrix3405 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def pivotMatrix3406 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, 0, 0]]

def pivotMatrix3407 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def pivotMatrix3408 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, 3, -1], ![-1, 0, -3, 4], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def pivotMatrix3409 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, 3, -1], ![-1, 0, -2, 3], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def pivotMatrix3410 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-1, 0, -3, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def pivotMatrix3411 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 0, -3, 4], ![-1, 1, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def pivotMatrix3412 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def pivotMatrix3413 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def pivotMatrix3414 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def pivotMatrix3415 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def pivotMatrix3416 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def pivotMatrix3417 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def pivotMatrix3418 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, -1, 2], ![-1, 1, 3, -3], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def pivotMatrix3419 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def pivotMatrix3420 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def pivotMatrix3421 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def pivotMatrix3422 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def pivotMatrix3423 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def pivotMatrix3424 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def pivotMatrix3425 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def pivotMatrix3426 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def pivotMatrix3427 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def pivotMatrix3428 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def pivotMatrix3429 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def pivotMatrix3430 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def pivotMatrix3431 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, 0, 0, -1]]

def pivotMatrix3432 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def pivotMatrix3433 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def pivotMatrix3434 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def pivotMatrix3435 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def pivotMatrix3436 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def pivotMatrix3437 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def pivotMatrix3438 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 0, 1, -1], ![0, 1, -3, 2], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def pivotMatrix3439 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def pivotMatrix3440 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def pivotMatrix3441 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def pivotMatrix3442 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def pivotMatrix3443 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def pivotMatrix3444 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def pivotMatrix3445 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def pivotMatrix3446 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def pivotMatrix3447 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 3, -2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def pivotMatrix3448 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def pivotMatrix3449 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def pivotMatrix3450 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def pivotMatrix3451 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 0, 1]]

def pivotMatrix3452 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -3, 2], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def pivotMatrix3453 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

def pivotMatrix3454 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def pivotMatrix3455 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, -1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix3456 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def pivotMatrix3457 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -2, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0]]

def pivotMatrix3458 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def pivotMatrix3459 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -2, 0, 1]]

def pivotMatrix3460 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

def pivotMatrix3461 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 1, -3, 3], ![-1, 1, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def pivotMatrix3462 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def pivotMatrix3463 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def pivotMatrix3464 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def pivotMatrix3465 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -3, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def pivotMatrix3466 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -2, 3, -2]]

def pivotMatrix3467 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def pivotMatrix3468 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -2, 0, 1]]

end MUB6.Certificate.PairSemantics

end OAI
end


