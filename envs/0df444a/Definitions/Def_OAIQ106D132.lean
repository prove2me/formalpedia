-- Prove2me | Definitions.Def_OAIQ106D132
-- name    : OAIQ106D132
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T13:25:13.449708+00:00
-- url     : https://prove2.me/theorems/3188bfa1-3314-46d1-9cea-5dcfb249f14e
-- title:
--   Definitions bundle OAIQ106D132 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3009 declarations of OpenAI's Lean: 3009 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.nodeValue1133`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue1134`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue1135`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue1136`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue1137`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue1138`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue1139`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue114`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue1140`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue1141`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue1142`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue1143`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue1144`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue1145`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue1146`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue1147`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue1148`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue1149`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue1150`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue1151`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue116`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue1161`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue1162`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue1163`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue1164`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue1166`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue1167`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue1168`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue117`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue1170`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue1172`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue1173`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue1175`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue1176`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue1177`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue118`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue119`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue1191`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue1192`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue1193` and 2969 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedSemantics_Values0`, `MutuallyUnbiased_MixedSemantics_Values1`, `MutuallyUnbiased_MixedSemantics_Values17`, `MutuallyUnbiased_MixedSemantics_Values18`, `MutuallyUnbiased_MixedSemantics_Values19`, `MutuallyUnbiased_MixedSemantics_Values2`, `MutuallyUnbiased_MixedSemantics_Values20`, `MutuallyUnbiased_MixedSemantics_Values21`, `MutuallyUnbiased_MixedSemantics_Values22`, `MutuallyUnbiased_MixedSemantics_Values23`, `MutuallyUnbiased_MixedSemantics_Values24`, `MutuallyUnbiased_MixedSemantics_Values25`, `MutuallyUnbiased_MixedSemantics_Values26`, `MutuallyUnbiased_MixedSemantics_Values27`, `MutuallyUnbiased_MixedSemantics_Values28`, `MutuallyUnbiased_MixedSemantics_Values29`, `MutuallyUnbiased_MixedSemantics_Values3`, `MutuallyUnbiased_MixedSemantics_Values30`, `MutuallyUnbiased_MixedSemantics_Values31`, `MutuallyUnbiased_MixedSemantics_Values32`, `MutuallyUnbiased_MixedSemantics_Values33`, `MutuallyUnbiased_MixedSemantics_Values34`, `MutuallyUnbiased_MixedSemantics_Values35`, `MutuallyUnbiased_MixedSemantics_Values36`, `MutuallyUnbiased_MixedSemantics_Values37`, `MutuallyUnbiased_MixedSemantics_Values38`, `MutuallyUnbiased_MixedSemantics_Values39`, `MutuallyUnbiased_MixedSemantics_Values4`, `MutuallyUnbiased_MixedSemantics_Values40`, `MutuallyUnbiased_MixedSemantics_Values41`, `MutuallyUnbiased_MixedSemantics_Values42`, `MutuallyUnbiased_MixedSemantics_Values43`, `MutuallyUnbiased_MixedSemantics_Values44`, `MutuallyUnbiased_MixedSemantics_Values45`, `MutuallyUnbiased_MixedSemantics_Values46`, `MutuallyUnbiased_MixedSemantics_Values47`, `MutuallyUnbiased_MixedSemantics_Values48`, `MutuallyUnbiased_MixedSemantics_Values49`, `MutuallyUnbiased_MixedSemantics_Values5`, `MutuallyUnbiased_MixedSemantics_Values50`, `MutuallyUnbiased_MixedSemantics_Values51`, `MutuallyUnbiased_MixedSemantics_Values52`, `MutuallyUnbiased_MixedSemantics_Values53`, `MutuallyUnbiased_MixedSemantics_Values54`, `MutuallyUnbiased_MixedSemantics_Values55`, `MutuallyUnbiased_MixedSemantics_Values56`, `MutuallyUnbiased_MixedSemantics_Values57`, `MutuallyUnbiased_MixedSemantics_Values58`, `MutuallyUnbiased_MixedSemantics_Values59`, `MutuallyUnbiased_MixedSemantics_Values6`, `MutuallyUnbiased_MixedSemantics_Values60`, `MutuallyUnbiased_MixedSemantics_Values61`, `MutuallyUnbiased_MixedSemantics_Values62`, `MutuallyUnbiased_MixedSemantics_Values63`, `MutuallyUnbiased_MixedSemantics_Values64`, `MutuallyUnbiased_MixedSemantics_Values65`, `MutuallyUnbiased_MixedSemantics_Values66`, `MutuallyUnbiased_MixedSemantics_Values68`.
--
--   **Imports.** It imports the bundle `OAIQ106D002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ106D209`, `OAIQ106D210`, `OAIQ106D211`, `OAIQ106D212`, `OAIQ106D213`, `OAIQ106D214`, `OAIQ106D215`, `OAIQ106D216`, `OAIQ106D217`, `OAIQ106D218`, `OAIQ106D219`, `OAIQ106D220`, `OAIQ106D221` and `OAIQ106D222`; the statements `OAI.MUB6.Certificate.MixedSemantics.sound1161`, `OAI.MUB6.Certificate.MixedSemantics.sound1162`, `OAI.MUB6.Certificate.MixedSemantics.sound1163`, `OAI.MUB6.Certificate.MixedSemantics.sound1164`, `OAI.MUB6.Certificate.MixedSemantics.sound1166`, `OAI.MUB6.Certificate.MixedSemantics.sound1168`, `OAI.MUB6.Certificate.MixedSemantics.sound1170`, `OAI.MUB6.Certificate.MixedSemantics.sound1172`, `OAI.MUB6.Certificate.MixedSemantics.sound1173`, `OAI.MUB6.Certificate.MixedSemantics.sound1175`, `OAI.MUB6.Certificate.MixedSemantics.sound1265`, `OAI.MUB6.Certificate.MixedSemantics.sound1266`, `OAI.MUB6.Certificate.MixedSemantics.sound1267`, `OAI.MUB6.Certificate.MixedSemantics.sound1271`, `OAI.MUB6.Certificate.MixedSemantics.sound1298`, `OAI.MUB6.Certificate.MixedSemantics.sound1299`, `OAI.MUB6.Certificate.MixedSemantics.sound1301`, `OAI.MUB6.Certificate.MixedSemantics.sound1339`, `OAI.MUB6.Certificate.MixedSemantics.sound1340`, `OAI.MUB6.Certificate.MixedSemantics.sound1341`, `OAI.MUB6.Certificate.MixedSemantics.sound1342`, `OAI.MUB6.Certificate.MixedSemantics.sound1343`, `OAI.MUB6.Certificate.MixedSemantics.sound1344`, `OAI.MUB6.Certificate.MixedSemantics.sound1346`, `OAI.MUB6.Certificate.MixedSemantics.sound1395`, `OAI.MUB6.Certificate.MixedSemantics.sound1396`, `OAI.MUB6.Certificate.MixedSemantics.sound1397`, `OAI.MUB6.Certificate.MixedSemantics.sound1399`, `OAI.MUB6.Certificate.MixedSemantics.sound1401`, `OAI.MUB6.Certificate.MixedSemantics.sound1409`, `OAI.MUB6.Certificate.MixedSemantics.sound1410`, `OAI.MUB6.Certificate.MixedSemantics.sound1411`, `OAI.MUB6.Certificate.MixedSemantics.sound1412`, `OAI.MUB6.Certificate.MixedSemantics.sound1413`, `OAI.MUB6.Certificate.MixedSemantics.sound1414`, `OAI.MUB6.Certificate.MixedSemantics.sound1416`, `OAI.MUB6.Certificate.MixedSemantics.sound1417`, `OAI.MUB6.Certificate.MixedSemantics.sound1427`, `OAI.MUB6.Certificate.MixedSemantics.sound1441`, `OAI.MUB6.Certificate.MixedSemantics.sound1443`, `OAI.MUB6.Certificate.MixedSemantics.sound1451`, `OAI.MUB6.Certificate.MixedSemantics.sound1475`, `OAI.MUB6.Certificate.MixedSemantics.sound1477`, `OAI.MUB6.Certificate.MixedSemantics.sound1478`, `OAI.MUB6.Certificate.MixedSemantics.sound1479`, `OAI.MUB6.Certificate.MixedSemantics.sound1480`, `OAI.MUB6.Certificate.MixedSemantics.sound171`, `OAI.MUB6.Certificate.MixedSemantics.sound174`, `OAI.MUB6.Certificate.MixedSemantics.sound206`, `OAI.MUB6.Certificate.MixedSemantics.sound207`, `OAI.MUB6.Certificate.MixedSemantics.sound2357`, `OAI.MUB6.Certificate.MixedSemantics.sound2358`, `OAI.MUB6.Certificate.MixedSemantics.sound2359`, `OAI.MUB6.Certificate.MixedSemantics.sound2527`, `OAI.MUB6.Certificate.MixedSemantics.sound2530`, `OAI.MUB6.Certificate.MixedSemantics.sound2531`, `OAI.MUB6.Certificate.MixedSemantics.sound2532`, `OAI.MUB6.Certificate.MixedSemantics.sound2570`, `OAI.MUB6.Certificate.MixedSemantics.sound2572`, `OAI.MUB6.Certificate.MixedSemantics.sound2574`, `OAI.MUB6.Certificate.MixedSemantics.sound2576`, `OAI.MUB6.Certificate.MixedSemantics.sound2593`, `OAI.MUB6.Certificate.MixedSemantics.sound2594`, `OAI.MUB6.Certificate.MixedSemantics.sound2595`, `OAI.MUB6.Certificate.MixedSemantics.sound2596`, `OAI.MUB6.Certificate.MixedSemantics.sound2598`, `OAI.MUB6.Certificate.MixedSemantics.sound2599`, `OAI.MUB6.Certificate.MixedSemantics.sound2601`, `OAI.MUB6.Certificate.MixedSemantics.sound2636`, `OAI.MUB6.Certificate.MixedSemantics.sound2637`, `OAI.MUB6.Certificate.MixedSemantics.sound2638`, `OAI.MUB6.Certificate.MixedSemantics.sound2640`, `OAI.MUB6.Certificate.MixedSemantics.sound2753`, `OAI.MUB6.Certificate.MixedSemantics.sound2766`, `OAI.MUB6.Certificate.MixedSemantics.sound2828`, `OAI.MUB6.Certificate.MixedSemantics.sound2904`, `OAI.MUB6.Certificate.MixedSemantics.sound293`, `OAI.MUB6.Certificate.MixedSemantics.sound2936`, `OAI.MUB6.Certificate.MixedSemantics.sound2937`, `OAI.MUB6.Certificate.MixedSemantics.sound2939`, `OAI.MUB6.Certificate.MixedSemantics.sound294`, `OAI.MUB6.Certificate.MixedSemantics.sound2941`, `OAI.MUB6.Certificate.MixedSemantics.sound2943`, `OAI.MUB6.Certificate.MixedSemantics.sound2957`, `OAI.MUB6.Certificate.MixedSemantics.sound2958`, `OAI.MUB6.Certificate.MixedSemantics.sound2959`, `OAI.MUB6.Certificate.MixedSemantics.sound2960`, `OAI.MUB6.Certificate.MixedSemantics.sound2961`, `OAI.MUB6.Certificate.MixedSemantics.sound2963`, `OAI.MUB6.Certificate.MixedSemantics.sound2965`, `OAI.MUB6.Certificate.MixedSemantics.sound2966`, `OAI.MUB6.Certificate.MixedSemantics.sound2968`, `OAI.MUB6.Certificate.MixedSemantics.sound2969`, `OAI.MUB6.Certificate.MixedSemantics.sound2986`, `OAI.MUB6.Certificate.MixedSemantics.sound2987`, `OAI.MUB6.Certificate.MixedSemantics.sound2988`, `OAI.MUB6.Certificate.MixedSemantics.sound2990`, `OAI.MUB6.Certificate.MixedSemantics.sound2996`, `OAI.MUB6.Certificate.MixedSemantics.sound2997`, `OAI.MUB6.Certificate.MixedSemantics.sound2998`, `OAI.MUB6.Certificate.MixedSemantics.sound3003`, `OAI.MUB6.Certificate.MixedSemantics.sound3005`, `OAI.MUB6.Certificate.MixedSemantics.sound3082`, `OAI.MUB6.Certificate.MixedSemantics.sound3087`, `OAI.MUB6.Certificate.MixedSemantics.sound3088`, `OAI.MUB6.Certificate.MixedSemantics.sound3089`, `OAI.MUB6.Certificate.MixedSemantics.sound3090`, `OAI.MUB6.Certificate.MixedSemantics.sound3093`, `OAI.MUB6.Certificate.MixedSemantics.sound3094`, `OAI.MUB6.Certificate.MixedSemantics.sound3099`, `OAI.MUB6.Certificate.MixedSemantics.sound3100`, `OAI.MUB6.Certificate.MixedSemantics.sound3101`, `OAI.MUB6.Certificate.MixedSemantics.sound3102`, `OAI.MUB6.Certificate.MixedSemantics.sound3106`, `OAI.MUB6.Certificate.MixedSemantics.sound3109`, `OAI.MUB6.Certificate.MixedSemantics.sound3110`, `OAI.MUB6.Certificate.MixedSemantics.sound3116`, `OAI.MUB6.Certificate.MixedSemantics.sound3120`, `OAI.MUB6.Certificate.MixedSemantics.sound3143`, `OAI.MUB6.Certificate.MixedSemantics.sound3144`, `OAI.MUB6.Certificate.MixedSemantics.sound3178`, `OAI.MUB6.Certificate.MixedSemantics.sound3184`, `OAI.MUB6.Certificate.MixedSemantics.sound3185`, `OAI.MUB6.Certificate.MixedSemantics.sound3190`, `OAI.MUB6.Certificate.MixedSemantics.sound3191`, `OAI.MUB6.Certificate.MixedSemantics.sound3203`, `OAI.MUB6.Certificate.MixedSemantics.sound3204`, `OAI.MUB6.Certificate.MixedSemantics.sound3205`, `OAI.MUB6.Certificate.MixedSemantics.sound3206`, `OAI.MUB6.Certificate.MixedSemantics.sound3207`, `OAI.MUB6.Certificate.MixedSemantics.sound3209`, `OAI.MUB6.Certificate.MixedSemantics.sound3210`, `OAI.MUB6.Certificate.MixedSemantics.sound3211`, `OAI.MUB6.Certificate.MixedSemantics.sound3223`, `OAI.MUB6.Certificate.MixedSemantics.sound3226`, `OAI.MUB6.Certificate.MixedSemantics.sound3227`, `OAI.MUB6.Certificate.MixedSemantics.sound370`, `OAI.MUB6.Certificate.MixedSemantics.sound371`, `OAI.MUB6.Certificate.MixedSemantics.sound3711`, `OAI.MUB6.Certificate.MixedSemantics.sound3726`, `OAI.MUB6.Certificate.MixedSemantics.sound3727`, `OAI.MUB6.Certificate.MixedSemantics.sound3734`, `OAI.MUB6.Certificate.MixedSemantics.sound3735`, `OAI.MUB6.Certificate.MixedSemantics.sound3736`, `OAI.MUB6.Certificate.MixedSemantics.sound3737`, `OAI.MUB6.Certificate.MixedSemantics.sound3738`, `OAI.MUB6.Certificate.MixedSemantics.sound3739`, `OAI.MUB6.Certificate.MixedSemantics.sound3818`, `OAI.MUB6.Certificate.MixedSemantics.sound3821`, `OAI.MUB6.Certificate.MixedSemantics.sound3822`, `OAI.MUB6.Certificate.MixedSemantics.sound3823`, `OAI.MUB6.Certificate.MixedSemantics.sound3824`, `OAI.MUB6.Certificate.MixedSemantics.sound3829`, `OAI.MUB6.Certificate.MixedSemantics.sound3831`, `OAI.MUB6.Certificate.MixedSemantics.sound3847`, `OAI.MUB6.Certificate.MixedSemantics.sound3851`, `OAI.MUB6.Certificate.MixedSemantics.sound3852`, `OAI.MUB6.Certificate.MixedSemantics.sound3853`, `OAI.MUB6.Certificate.MixedSemantics.sound3855`, `OAI.MUB6.Certificate.MixedSemantics.sound3856`, `OAI.MUB6.Certificate.MixedSemantics.sound3858`, `OAI.MUB6.Certificate.MixedSemantics.sound3882`, `OAI.MUB6.Certificate.MixedSemantics.sound3883`, `OAI.MUB6.Certificate.MixedSemantics.sound3887`, `OAI.MUB6.Certificate.MixedSemantics.sound3888`, `OAI.MUB6.Certificate.MixedSemantics.sound3925`, `OAI.MUB6.Certificate.MixedSemantics.sound3931`, `OAI.MUB6.Certificate.MixedSemantics.sound3933`, `OAI.MUB6.Certificate.MixedSemantics.sound3936`, `OAI.MUB6.Certificate.MixedSemantics.sound3937`, `OAI.MUB6.Certificate.MixedSemantics.sound3965`, `OAI.MUB6.Certificate.MixedSemantics.sound3966`, `OAI.MUB6.Certificate.MixedSemantics.sound3967`, `OAI.MUB6.Certificate.MixedSemantics.sound3977`, `OAI.MUB6.Certificate.MixedSemantics.sound3980`, `OAI.MUB6.Certificate.MixedSemantics.sound3981`, `OAI.MUB6.Certificate.MixedSemantics.sound3982`, `OAI.MUB6.Certificate.MixedSemantics.sound3984`, `OAI.MUB6.Certificate.MixedSemantics.sound3987`, `OAI.MUB6.Certificate.MixedSemantics.sound3992`, `OAI.MUB6.Certificate.MixedSemantics.sound3993`, `OAI.MUB6.Certificate.MixedSemantics.sound3994`, `OAI.MUB6.Certificate.MixedSemantics.sound3995`, `OAI.MUB6.Certificate.MixedSemantics.sound3997`, `OAI.MUB6.Certificate.MixedSemantics.sound3998`, `OAI.MUB6.Certificate.MixedSemantics.sound4002`, `OAI.MUB6.Certificate.MixedSemantics.sound4003`, `OAI.MUB6.Certificate.MixedSemantics.sound4012`, `OAI.MUB6.Certificate.MixedSemantics.sound4013`, `OAI.MUB6.Certificate.MixedSemantics.sound4014`, `OAI.MUB6.Certificate.MixedSemantics.sound4023`, `OAI.MUB6.Certificate.MixedSemantics.sound4026`, `OAI.MUB6.Certificate.MixedSemantics.sound4027`, `OAI.MUB6.Certificate.MixedSemantics.sound4029`, `OAI.MUB6.Certificate.MixedSemantics.sound4031`, `OAI.MUB6.Certificate.MixedSemantics.sound4032`, `OAI.MUB6.Certificate.MixedSemantics.sound4033`, `OAI.MUB6.Certificate.MixedSemantics.sound4039`, `OAI.MUB6.Certificate.MixedSemantics.sound4050` and `OAI.MUB6.Certificate.MixedSemantics.sound4053`; the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1161`, `OAI.MUB6.Certificate.MixedSemantics.sound1162`, `OAI.MUB6.Certificate.MixedSemantics.sound1163`, `OAI.MUB6.Certificate.MixedSemantics.sound1164`, `OAI.MUB6.Certificate.MixedSemantics.sound1165`, `OAI.MUB6.Certificate.MixedSemantics.sound1166`, `OAI.MUB6.Certificate.MixedSemantics.sound1168`, `OAI.MUB6.Certificate.MixedSemantics.sound1170`, `OAI.MUB6.Certificate.MixedSemantics.sound1172`, `OAI.MUB6.Certificate.MixedSemantics.sound1173`, `OAI.MUB6.Certificate.MixedSemantics.sound1175`, `OAI.MUB6.Certificate.MixedSemantics.sound1265`, `OAI.MUB6.Certificate.MixedSemantics.sound1266`, `OAI.MUB6.Certificate.MixedSemantics.sound1267`, `OAI.MUB6.Certificate.MixedSemantics.sound1271`, `OAI.MUB6.Certificate.MixedSemantics.sound1298`, `OAI.MUB6.Certificate.MixedSemantics.sound1299`, `OAI.MUB6.Certificate.MixedSemantics.sound1301`, `OAI.MUB6.Certificate.MixedSemantics.sound1339`, `OAI.MUB6.Certificate.MixedSemantics.sound1340`, `OAI.MUB6.Certificate.MixedSemantics.sound1341`, `OAI.MUB6.Certificate.MixedSemantics.sound1342`, `OAI.MUB6.Certificate.MixedSemantics.sound1343`, `OAI.MUB6.Certificate.MixedSemantics.sound1344`, `OAI.MUB6.Certificate.MixedSemantics.sound1346`, `OAI.MUB6.Certificate.MixedSemantics.sound1395`, `OAI.MUB6.Certificate.MixedSemantics.sound1396`, `OAI.MUB6.Certificate.MixedSemantics.sound1397`, `OAI.MUB6.Certificate.MixedSemantics.sound1399`, `OAI.MUB6.Certificate.MixedSemantics.sound1401`, `OAI.MUB6.Certificate.MixedSemantics.sound1409`, `OAI.MUB6.Certificate.MixedSemantics.sound1410`, `OAI.MUB6.Certificate.MixedSemantics.sound1411`, `OAI.MUB6.Certificate.MixedSemantics.sound1412`, `OAI.MUB6.Certificate.MixedSemantics.sound1413`, `OAI.MUB6.Certificate.MixedSemantics.sound1414`, `OAI.MUB6.Certificate.MixedSemantics.sound1416`, `OAI.MUB6.Certificate.MixedSemantics.sound1417`, `OAI.MUB6.Certificate.MixedSemantics.sound1427`, `OAI.MUB6.Certificate.MixedSemantics.sound1441`, `OAI.MUB6.Certificate.MixedSemantics.sound1443`, `OAI.MUB6.Certificate.MixedSemantics.sound1451`, `OAI.MUB6.Certificate.MixedSemantics.sound1475`, `OAI.MUB6.Certificate.MixedSemantics.sound1477`, `OAI.MUB6.Certificate.MixedSemantics.sound1478`, `OAI.MUB6.Certificate.MixedSemantics.sound1479`, `OAI.MUB6.Certificate.MixedSemantics.sound1480`, `OAI.MUB6.Certificate.MixedSemantics.sound171`, `OAI.MUB6.Certificate.MixedSemantics.sound174`, `OAI.MUB6.Certificate.MixedSemantics.sound206`, `OAI.MUB6.Certificate.MixedSemantics.sound207`, `OAI.MUB6.Certificate.MixedSemantics.sound2357`, `OAI.MUB6.Certificate.MixedSemantics.sound2358`, `OAI.MUB6.Certificate.MixedSemantics.sound2359`, `OAI.MUB6.Certificate.MixedSemantics.sound2527`, `OAI.MUB6.Certificate.MixedSemantics.sound2530`, `OAI.MUB6.Certificate.MixedSemantics.sound2531`, `OAI.MUB6.Certificate.MixedSemantics.sound2532`, `OAI.MUB6.Certificate.MixedSemantics.sound2570`, `OAI.MUB6.Certificate.MixedSemantics.sound2572`, `OAI.MUB6.Certificate.MixedSemantics.sound2574`, `OAI.MUB6.Certificate.MixedSemantics.sound2576`, `OAI.MUB6.Certificate.MixedSemantics.sound2593`, `OAI.MUB6.Certificate.MixedSemantics.sound2594`, `OAI.MUB6.Certificate.MixedSemantics.sound2595`, `OAI.MUB6.Certificate.MixedSemantics.sound2596`, `OAI.MUB6.Certificate.MixedSemantics.sound2598`, `OAI.MUB6.Certificate.MixedSemantics.sound2599`, `OAI.MUB6.Certificate.MixedSemantics.sound2601`, `OAI.MUB6.Certificate.MixedSemantics.sound2636`, `OAI.MUB6.Certificate.MixedSemantics.sound2637`, `OAI.MUB6.Certificate.MixedSemantics.sound2638`, `OAI.MUB6.Certificate.MixedSemantics.sound2640`, `OAI.MUB6.Certificate.MixedSemantics.sound2753`, `OAI.MUB6.Certificate.MixedSemantics.sound2766`, `OAI.MUB6.Certificate.MixedSemantics.sound2828`, `OAI.MUB6.Certificate.MixedSemantics.sound2904`, `OAI.MUB6.Certificate.MixedSemantics.sound293`, `OAI.MUB6.Certificate.MixedSemantics.sound2936`, `OAI.MUB6.Certificate.MixedSemantics.sound2937`, `OAI.MUB6.Certificate.MixedSemantics.sound2939`, `OAI.MUB6.Certificate.MixedSemantics.sound294`, `OAI.MUB6.Certificate.MixedSemantics.sound2941`, `OAI.MUB6.Certificate.MixedSemantics.sound2943`, `OAI.MUB6.Certificate.MixedSemantics.sound2957`, `OAI.MUB6.Certificate.MixedSemantics.sound2958`, `OAI.MUB6.Certificate.MixedSemantics.sound2959`, `OAI.MUB6.Certificate.MixedSemantics.sound2960`, `OAI.MUB6.Certificate.MixedSemantics.sound2961`, `OAI.MUB6.Certificate.MixedSemantics.sound2963`, `OAI.MUB6.Certificate.MixedSemantics.sound2965`, `OAI.MUB6.Certificate.MixedSemantics.sound2966`, `OAI.MUB6.Certificate.MixedSemantics.sound2968`, `OAI.MUB6.Certificate.MixedSemantics.sound2969`, `OAI.MUB6.Certificate.MixedSemantics.sound2986`, `OAI.MUB6.Certificate.MixedSemantics.sound2987`, `OAI.MUB6.Certificate.MixedSemantics.sound2988`, `OAI.MUB6.Certificate.MixedSemantics.sound2990`, `OAI.MUB6.Certificate.MixedSemantics.sound2996`, `OAI.MUB6.Certificate.MixedSemantics.sound2997`, `OAI.MUB6.Certificate.MixedSemantics.sound2998`, `OAI.MUB6.Certificate.MixedSemantics.sound3003`, `OAI.MUB6.Certificate.MixedSemantics.sound3005`, `OAI.MUB6.Certificate.MixedSemantics.sound3082`, `OAI.MUB6.Certificate.MixedSemantics.sound3087`, `OAI.MUB6.Certificate.MixedSemantics.sound3088`, `OAI.MUB6.Certificate.MixedSemantics.sound3089`, `OAI.MUB6.Certificate.MixedSemantics.sound3090`, `OAI.MUB6.Certificate.MixedSemantics.sound3093`, `OAI.MUB6.Certificate.MixedSemantics.sound3094`, `OAI.MUB6.Certificate.MixedSemantics.sound3099`, `OAI.MUB6.Certificate.MixedSemantics.sound3100`, `OAI.MUB6.Certificate.MixedSemantics.sound3101`, `OAI.MUB6.Certificate.MixedSemantics.sound3102`, `OAI.MUB6.Certificate.MixedSemantics.sound3106`, `OAI.MUB6.Certificate.MixedSemantics.sound3109`, `OAI.MUB6.Certificate.MixedSemantics.sound3110`, `OAI.MUB6.Certificate.MixedSemantics.sound3116`, `OAI.MUB6.Certificate.MixedSemantics.sound3120`, `OAI.MUB6.Certificate.MixedSemantics.sound3143`, `OAI.MUB6.Certificate.MixedSemantics.sound3144`, `OAI.MUB6.Certificate.MixedSemantics.sound3178`, `OAI.MUB6.Certificate.MixedSemantics.sound3184`, `OAI.MUB6.Certificate.MixedSemantics.sound3185`, `OAI.MUB6.Certificate.MixedSemantics.sound3190`, `OAI.MUB6.Certificate.MixedSemantics.sound3191`, `OAI.MUB6.Certificate.MixedSemantics.sound3203`, `OAI.MUB6.Certificate.MixedSemantics.sound3204`, `OAI.MUB6.Certificate.MixedSemantics.sound3205`, `OAI.MUB6.Certificate.MixedSemantics.sound3206`, `OAI.MUB6.Certificate.MixedSemantics.sound3207`, `OAI.MUB6.Certificate.MixedSemantics.sound3209`, `OAI.MUB6.Certificate.MixedSemantics.sound3210`, `OAI.MUB6.Certificate.MixedSemantics.sound3211`, `OAI.MUB6.Certificate.MixedSemantics.sound3223`, `OAI.MUB6.Certificate.MixedSemantics.sound3226`, `OAI.MUB6.Certificate.MixedSemantics.sound3227`, `OAI.MUB6.Certificate.MixedSemantics.sound370`, `OAI.MUB6.Certificate.MixedSemantics.sound371`, `OAI.MUB6.Certificate.MixedSemantics.sound3711`, `OAI.MUB6.Certificate.MixedSemantics.sound3726`, `OAI.MUB6.Certificate.MixedSemantics.sound3727`, `OAI.MUB6.Certificate.MixedSemantics.sound3734`, `OAI.MUB6.Certificate.MixedSemantics.sound3735`, `OAI.MUB6.Certificate.MixedSemantics.sound3736`, `OAI.MUB6.Certificate.MixedSemantics.sound3737`, `OAI.MUB6.Certificate.MixedSemantics.sound3738`, `OAI.MUB6.Certificate.MixedSemantics.sound3739`, `OAI.MUB6.Certificate.MixedSemantics.sound3818`, `OAI.MUB6.Certificate.MixedSemantics.sound3821`, `OAI.MUB6.Certificate.MixedSemantics.sound3822`, `OAI.MUB6.Certificate.MixedSemantics.sound3823`, `OAI.MUB6.Certificate.MixedSemantics.sound3824`, `OAI.MUB6.Certificate.MixedSemantics.sound3829`, `OAI.MUB6.Certificate.MixedSemantics.sound3831`, `OAI.MUB6.Certificate.MixedSemantics.sound3847`, `OAI.MUB6.Certificate.MixedSemantics.sound3851`, `OAI.MUB6.Certificate.MixedSemantics.sound3852`, `OAI.MUB6.Certificate.MixedSemantics.sound3853`, `OAI.MUB6.Certificate.MixedSemantics.sound3855`, `OAI.MUB6.Certificate.MixedSemantics.sound3856`, `OAI.MUB6.Certificate.MixedSemantics.sound3858`, `OAI.MUB6.Certificate.MixedSemantics.sound3882`, `OAI.MUB6.Certificate.MixedSemantics.sound3883`, `OAI.MUB6.Certificate.MixedSemantics.sound3887`, `OAI.MUB6.Certificate.MixedSemantics.sound3888`, `OAI.MUB6.Certificate.MixedSemantics.sound3925`, `OAI.MUB6.Certificate.MixedSemantics.sound3931`, `OAI.MUB6.Certificate.MixedSemantics.sound3933`, `OAI.MUB6.Certificate.MixedSemantics.sound3936`, `OAI.MUB6.Certificate.MixedSemantics.sound3937`, `OAI.MUB6.Certificate.MixedSemantics.sound3965`, `OAI.MUB6.Certificate.MixedSemantics.sound3966`, `OAI.MUB6.Certificate.MixedSemantics.sound3967`, `OAI.MUB6.Certificate.MixedSemantics.sound3977`, `OAI.MUB6.Certificate.MixedSemantics.sound3980`, `OAI.MUB6.Certificate.MixedSemantics.sound3981`, `OAI.MUB6.Certificate.MixedSemantics.sound3982`, `OAI.MUB6.Certificate.MixedSemantics.sound3984`, `OAI.MUB6.Certificate.MixedSemantics.sound3987`, `OAI.MUB6.Certificate.MixedSemantics.sound3992`, `OAI.MUB6.Certificate.MixedSemantics.sound3993`, `OAI.MUB6.Certificate.MixedSemantics.sound3994`, `OAI.MUB6.Certificate.MixedSemantics.sound3995`, `OAI.MUB6.Certificate.MixedSemantics.sound3997`, `OAI.MUB6.Certificate.MixedSemantics.sound3998`, `OAI.MUB6.Certificate.MixedSemantics.sound4002`, `OAI.MUB6.Certificate.MixedSemantics.sound4003`, `OAI.MUB6.Certificate.MixedSemantics.sound4012`, `OAI.MUB6.Certificate.MixedSemantics.sound4013`, `OAI.MUB6.Certificate.MixedSemantics.sound4014`, `OAI.MUB6.Certificate.MixedSemantics.sound4023`, `OAI.MUB6.Certificate.MixedSemantics.sound4026`, `OAI.MUB6.Certificate.MixedSemantics.sound4027`, `OAI.MUB6.Certificate.MixedSemantics.sound4029`, `OAI.MUB6.Certificate.MixedSemantics.sound4031`, `OAI.MUB6.Certificate.MixedSemantics.sound4032`, `OAI.MUB6.Certificate.MixedSemantics.sound4033`, `OAI.MUB6.Certificate.MixedSemantics.sound4039`, `OAI.MUB6.Certificate.MixedSemantics.sound4050`, `OAI.MUB6.Certificate.MixedSemantics.sound4053`, `OAI.MUB6.Certificate.MixedSemantics.sound4622`, `OAI.MUB6.Certificate.MixedSemantics.sound4623`, `OAI.MUB6.Certificate.MixedSemantics.sound4625`, `OAI.MUB6.Certificate.MixedSemantics.sound5167`, `OAI.MUB6.Certificate.MixedSemantics.sound5168`, `OAI.MUB6.Certificate.MixedSemantics.sound5169`, `OAI.MUB6.Certificate.MixedSemantics.sound5171`, `OAI.MUB6.Certificate.MixedSemantics.sound5172`, `OAI.MUB6.Certificate.MixedSemantics.sound5174`, `OAI.MUB6.Certificate.MixedSemantics.sound5176`, `OAI.MUB6.Certificate.MixedSemantics.sound5177`, `OAI.MUB6.Certificate.MixedSemantics.sound5292`, `OAI.MUB6.Certificate.MixedSemantics.sound5293`, `OAI.MUB6.Certificate.MixedSemantics.sound5294`, `OAI.MUB6.Certificate.MixedSemantics.sound5296`, `OAI.MUB6.Certificate.MixedSemantics.sound5306`, `OAI.MUB6.Certificate.MixedSemantics.sound5310`, `OAI.MUB6.Certificate.MixedSemantics.sound5386`, `OAI.MUB6.Certificate.MixedSemantics.sound5387`, `OAI.MUB6.Certificate.MixedSemantics.sound5388`, `OAI.MUB6.Certificate.MixedSemantics.sound5415`, `OAI.MUB6.Certificate.MixedSemantics.sound5416`, `OAI.MUB6.Certificate.MixedSemantics.sound5418`, `OAI.MUB6.Certificate.MixedSemantics.sound5433`, `OAI.MUB6.Certificate.MixedSemantics.sound5434`, `OAI.MUB6.Certificate.MixedSemantics.sound5435`, `OAI.MUB6.Certificate.MixedSemantics.sound5439`, `OAI.MUB6.Certificate.MixedSemantics.sound5443`, `OAI.MUB6.Certificate.MixedSemantics.sound5450`, `OAI.MUB6.Certificate.MixedSemantics.sound5451`, `OAI.MUB6.Certificate.MixedSemantics.sound5452`, `OAI.MUB6.Certificate.MixedSemantics.sound5453`, `OAI.MUB6.Certificate.MixedSemantics.sound5464`, `OAI.MUB6.Certificate.MixedSemantics.sound5465`, `OAI.MUB6.Certificate.MixedSemantics.sound5476`, `OAI.MUB6.Certificate.MixedSemantics.sound5482`, `OAI.MUB6.Certificate.MixedSemantics.sound5483`, `OAI.MUB6.Certificate.MixedSemantics.sound5485`, `OAI.MUB6.Certificate.MixedSemantics.sound5490`, `OAI.MUB6.Certificate.MixedSemantics.sound5491`, `OAI.MUB6.Certificate.MixedSemantics.sound5492`, `OAI.MUB6.Certificate.MixedSemantics.sound5498`, `OAI.MUB6.Certificate.MixedSemantics.sound5500`, `OAI.MUB6.Certificate.MixedSemantics.sound644`, `OAI.MUB6.Certificate.MixedSemantics.sound645`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1009`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval106`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1074`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval109`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1105`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval116`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval117`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1192`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1194`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval12`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval120`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1210`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval124`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1254`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval130`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1315`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval133`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval134`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval141`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval143`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1435`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval145`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval146`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval147`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval149`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval155`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1553`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1554`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval159`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval164`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval165`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval167`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1674`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval173`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval174`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval18`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval181`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval182`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval185`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1852`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1853`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1882`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1913`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1914`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval202`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval203`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval207`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval21`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval214`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval215`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval218`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval220`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval224`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval225`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval226`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval229`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval231`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval234`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval235`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval242`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval243`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval245`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval249`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval255`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval257`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval258`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval263`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval270`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval271`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval273`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval278`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval280`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval285`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval286`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval287`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval292`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval296`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval301`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval308`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval310`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval323`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval325`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval331`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval332`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval41`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval477`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval69`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval715`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval73`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval74`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval77`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval79`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval83`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval835`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval86`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval91`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval953`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval955`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval957`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval99`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval113`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval119`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval147`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval150`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval208`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval21`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval215`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval216`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval220`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval222` and `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval271`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ106D002

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue2 : Sparse Master := [(Sum.inl 0, (1 / 6)), (Sum.inl 2, (5 / 6))]

def nodeValue3 : Sparse Master := [(Sum.inl 0, (1 / 9)), (Sum.inl 2, (-5 / 72)), (Sum.inl 1, (5 / 24))]

def nodeValue4 : Sparse Master := [(Sum.inl 0, (11 / 72)), (Sum.inl 2, (5 / 72)), (Sum.inl 1, (-5 / 36))]

def nodeValue12 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 9, (-5 / 54)), (Sum.inl 5, (-5 / 72)), (Sum.inl 257, (5 / 54)), (Sum.inl 2, (-5 / 288)), (Sum.inl 69, (5 / 18)), (Sum.inl 70, (5 / 18)), (Sum.inl 71, (5 / 54)), (Sum.inl 7, (5 / 27)), (Sum.inl 35, (5 / 54)), (Sum.inl 1, (-5 / 96))]

def nodeValue13 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 9, (5 / 36)), (Sum.inl 58, (-5 / 144)), (Sum.inl 5, (5 / 54)), (Sum.inl 6, (-5 / 108)), (Sum.inl 2, (-5 / 144)), (Sum.inl 1, (-25 / 432))]

def nodeValue14 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 9, (-5 / 54)), (Sum.inl 58, (5 / 432)), (Sum.inl 5, (-5 / 108)), (Sum.inl 6, (5 / 144)), (Sum.inl 257, (5 / 27)), (Sum.inl 2, (-5 / 864)), (Sum.inl 69, (5 / 54)), (Sum.inl 70, (5 / 54)), (Sum.inl 35, (5 / 27)), (Sum.inl 495, (5 / 27)), (Sum.inl 1, (5 / 864))]

def nodeValue15 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 9, (-5 / 54)), (Sum.inl 5, (-5 / 72)), (Sum.inl 256, (-5 / 18)), (Sum.inl 2, (35 / 864)), (Sum.inl 69, (5 / 27)), (Sum.inl 70, (5 / 54)), (Sum.inl 71, (5 / 18)), (Sum.inl 7, (5 / 54)), (Sum.inl 8, (5 / 54)), (Sum.inl 1, (5 / 288))]

def nodeValue16 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 9, (5 / 54)), (Sum.inl 58, (-5 / 144)), (Sum.inl 5, (5 / 108)), (Sum.inl 6, (-5 / 108)), (Sum.inl 2, (-5 / 216)), (Sum.inl 495, (-5 / 27))]

def nodeValue17 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 9, (5 / 36)), (Sum.inl 2, (-5 / 216)), (Sum.inl 69, (-5 / 27)), (Sum.inl 70, (-5 / 27)), (Sum.inl 71, (-5 / 27)), (Sum.inl 1, (-25 / 432))]

def nodeValue18 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 9, (5 / 36)), (Sum.inl 2, (5 / 144)), (Sum.inl 69, (-5 / 27)), (Sum.inl 71, (-10 / 27)), (Sum.inl 1, (5 / 432))]

def nodeValue19 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 9, (5 / 36)), (Sum.inl 257, (-5 / 27)), (Sum.inl 2, (-5 / 72)), (Sum.inl 69, (-5 / 27)), (Sum.inl 70, (-5 / 27)), (Sum.inl 1, (-5 / 72))]

def nodeValue20 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 9, (-5 / 18)), (Sum.inl 58, (5 / 36)), (Sum.inl 2, (-5 / 72)), (Sum.inl 1, (-5 / 72))]

def nodeValue21 : Sparse Master := [(Sum.inl 0, (1 / 54)), (Sum.inl 9, (-95 / 216)), (Sum.inl 58, (5 / 216)), (Sum.inl 5, (-5 / 27)), (Sum.inl 6, (5 / 72)), (Sum.inl 256, (5 / 6)), (Sum.inl 257, (-5 / 27)), (Sum.inl 2, (25 / 864)), (Sum.inl 69, (-5 / 9)), (Sum.inl 70, (-5 / 18)), (Sum.inl 71, (-5 / 18)), (Sum.inl 7, (-5 / 18)), (Sum.inl 35, (-25 / 54)), (Sum.inl 3, (-5 / 18)), (Sum.inl 495, (-5 / 18)), (Sum.inl 52, (-5 / 9)), (Sum.inl 1, (25 / 864))]

def nodeValue22 : Sparse Master := [(Sum.inl 0, (29 / 864)), (Sum.inl 9, (-10 / 27)), (Sum.inl 58, (5 / 216)), (Sum.inl 6, (5 / 96)), (Sum.inl 2, (5 / 432)), (Sum.inl 69, (-5 / 9)), (Sum.inl 70, (-5 / 27)), (Sum.inl 71, (-10 / 9)), (Sum.inl 7, (-5 / 18)), (Sum.inl 8, (-5 / 9)), (Sum.inl 1, (-5 / 216))]

def nodeValue23 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 9, (5 / 54)), (Sum.inl 58, (-5 / 864)), (Sum.inl 6, (-5 / 864)), (Sum.inl 2, (-35 / 864)), (Sum.inl 69, (5 / 27)), (Sum.inl 70, (5 / 54)), (Sum.inl 71, (5 / 27)), (Sum.inl 7, (5 / 54)), (Sum.inl 1, (-65 / 864))]

def nodeValue24 : Sparse Master := [(Sum.inl 0, (1 / 54)), (Sum.inl 9, (25 / 216)), (Sum.inl 58, (-5 / 864)), (Sum.inl 5, (5 / 216)), (Sum.inl 6, (-5 / 288)), (Sum.inl 256, (-5 / 18)), (Sum.inl 2, (-35 / 864)), (Sum.inl 69, (5 / 27)), (Sum.inl 71, (5 / 54)), (Sum.inl 495, (5 / 54)), (Sum.inl 52, (5 / 27)), (Sum.inl 1, (5 / 288))]

def nodeValue25 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 58, (5 / 432)), (Sum.inl 2, (25 / 144)), (Sum.inl 70, (-5 / 27)), (Sum.inl 1, (-5 / 144))]

def nodeValue26 : Sparse Master := [(Sum.inl 0, (1 / 32)), (Sum.inl 9, (5 / 54)), (Sum.inl 58, (-5 / 864)), (Sum.inl 6, (-5 / 432)), (Sum.inl 2, (5 / 144)), (Sum.inl 69, (5 / 54)), (Sum.inl 71, (10 / 27)), (Sum.inl 8, (5 / 27)), (Sum.inl 1, (5 / 216))]

def nodeValue27 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 9, (25 / 216)), (Sum.inl 58, (-5 / 864)), (Sum.inl 5, (5 / 72)), (Sum.inl 6, (-5 / 288)), (Sum.inl 256, (-5 / 18)), (Sum.inl 257, (5 / 54)), (Sum.inl 2, (-35 / 864)), (Sum.inl 69, (5 / 54)), (Sum.inl 70, (5 / 54)), (Sum.inl 7, (5 / 54)), (Sum.inl 35, (5 / 27)), (Sum.inl 3, (5 / 54)), (Sum.inl 495, (5 / 54)), (Sum.inl 52, (5 / 54)), (Sum.inl 1, (-55 / 864))]

def nodeValue28 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 58, (5 / 432)), (Sum.inl 5, (5 / 108)), (Sum.inl 6, (5 / 432)), (Sum.inl 2, (-5 / 108)), (Sum.inl 71, (-5 / 27)), (Sum.inl 1, (-35 / 432))]

def nodeValue29 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 9, (-5 / 54)), (Sum.inl 5, (-5 / 108)), (Sum.inl 257, (-5 / 27)), (Sum.inl 2, (65 / 432)), (Sum.inl 70, (-5 / 27)), (Sum.inl 35, (-5 / 27)), (Sum.inl 1, (-5 / 216))]

def nodeValue30 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 9, (-5 / 54)), (Sum.inl 2, (-5 / 108)), (Sum.inl 69, (-5 / 27)), (Sum.inl 71, (-5 / 27)), (Sum.inl 1, (-35 / 432))]

def nodeValue31 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 58, (5 / 432)), (Sum.inl 5, (5 / 54)), (Sum.inl 6, (5 / 216)), (Sum.inl 2, (5 / 216)), (Sum.inl 69, (-5 / 27)), (Sum.inl 1, (35 / 216))]

def nodeValue32 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 9, (-5 / 108)), (Sum.inl 58, (5 / 432)), (Sum.inl 6, (5 / 216)), (Sum.inl 257, (-5 / 27)), (Sum.inl 2, (-25 / 432)), (Sum.inl 35, (-5 / 27)), (Sum.inl 495, (-5 / 27)), (Sum.inl 1, (-5 / 72))]

def nodeValue33 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 9, (-5 / 54)), (Sum.inl 5, (-5 / 108)), (Sum.inl 2, (-5 / 144)), (Sum.inl 69, (-5 / 27)), (Sum.inl 70, (-5 / 27)), (Sum.inl 7, (-5 / 27)), (Sum.inl 1, (5 / 48))]

def nodeValue34 : Sparse Master := [(Sum.inl 0, (7 / 216)), (Sum.inl 9, (-5 / 54)), (Sum.inl 5, (-5 / 108)), (Sum.inl 2, (5 / 216)), (Sum.inl 71, (-10 / 27)), (Sum.inl 8, (-5 / 27))]

def nodeValue35 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 9, (-5 / 36)), (Sum.inl 58, (-5 / 144)), (Sum.inl 5, (-5 / 36)), (Sum.inl 6, (-5 / 144)), (Sum.inl 2, (-5 / 144)), (Sum.inl 1, (5 / 48))]

def nodeValue36 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 9, (-5 / 54)), (Sum.inl 5, (-5 / 108)), (Sum.inl 256, (5 / 9)), (Sum.inl 2, (-5 / 216)), (Sum.inl 1, (-25 / 432))]

def nodeValue37 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 58, (-5 / 144)), (Sum.inl 6, (-5 / 144)), (Sum.inl 2, (-5 / 72)), (Sum.inl 495, (5 / 9)), (Sum.inl 1, (-5 / 72))]

def nodeValue38 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 9, (5 / 36)), (Sum.inl 2, (5 / 36)), (Sum.inl 70, (5 / 9)), (Sum.inl 1, (5 / 36))]

def nodeValue39 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 9, (5 / 36)), (Sum.inl 2, (-5 / 144)), (Sum.inl 71, (5 / 9)), (Sum.inl 1, (-5 / 72))]

def nodeValue40 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 9, (5 / 36)), (Sum.inl 2, (-5 / 144)), (Sum.inl 69, (5 / 9)), (Sum.inl 1, (5 / 48))]

def nodeValue41 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 9, (5 / 36)), (Sum.inl 257, (5 / 9)), (Sum.inl 2, (5 / 48)), (Sum.inl 1, (-5 / 144))]

def nodeValue42 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 9, (5 / 9)), (Sum.inl 58, (5 / 36)), (Sum.inl 2, (5 / 36)), (Sum.inl 1, (5 / 36))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue114 : Sparse Master := [(Sum.inl 0, (7 / 288)), (Sum.inl 9, (5 / 108)), (Sum.inl 5, (5 / 27)), (Sum.inl 6, (-5 / 288)), (Sum.inl 257, (-5 / 54)), (Sum.inl 67, (-5 / 27)), (Sum.inl 2, (-25 / 432)), (Sum.inl 69, (-10 / 27)), (Sum.inl 70, (-10 / 27)), (Sum.inl 71, (-5 / 54)), (Sum.inl 7, (-5 / 9)), (Sum.inl 35, (-20 / 27)), (Sum.inl 8, (-5 / 27)), (Sum.inl 3, (-10 / 27)), (Sum.inl 52, (-5 / 54)), (Sum.inl 26, (-5 / 54)), (Sum.inl 1, (-5 / 108))]

def nodeValue116 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 9, (-5 / 108)), (Sum.inl 5, (-25 / 216)), (Sum.inl 6, (5 / 432)), (Sum.inl 2, (5 / 96)), (Sum.inl 69, (5 / 27)), (Sum.inl 70, (5 / 54)), (Sum.inl 71, (5 / 54)), (Sum.inl 7, (5 / 27)), (Sum.inl 35, (5 / 54)), (Sum.inl 8, (5 / 54)), (Sum.inl 52, (5 / 54)), (Sum.inl 1, (-25 / 864))]

def nodeValue117 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 9, (-5 / 108)), (Sum.inl 5, (-5 / 72)), (Sum.inl 6, (5 / 288)), (Sum.inl 257, (5 / 54)), (Sum.inl 67, (5 / 54)), (Sum.inl 2, (-5 / 216)), (Sum.inl 69, (5 / 54)), (Sum.inl 70, (5 / 27)), (Sum.inl 7, (5 / 27)), (Sum.inl 35, (5 / 18)), (Sum.inl 1, (-5 / 96))]

def nodeValue118 : Sparse Master := [(Sum.inl 0, (29 / 864)), (Sum.inl 9, (-5 / 54)), (Sum.inl 58, (5 / 864)), (Sum.inl 5, (25 / 108)), (Sum.inl 6, (-5 / 216)), (Sum.inl 2, (-55 / 864)), (Sum.inl 69, (-5 / 27)), (Sum.inl 70, (-5 / 54)), (Sum.inl 71, (-5 / 27)), (Sum.inl 7, (-10 / 27)), (Sum.inl 35, (-5 / 27)), (Sum.inl 8, (-10 / 27)), (Sum.inl 3, (-5 / 27)), (Sum.inl 1, (-25 / 288))]

def nodeValue119 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 58, (-5 / 864)), (Sum.inl 5, (-5 / 108)), (Sum.inl 6, (35 / 864)), (Sum.inl 2, (-35 / 864)), (Sum.inl 70, (5 / 54)), (Sum.inl 7, (5 / 54)), (Sum.inl 35, (5 / 27)), (Sum.inl 1, (-65 / 864))]

def nodeValue120 : Sparse Master := [(Sum.inl 0, (7 / 288)), (Sum.inl 9, (-5 / 54)), (Sum.inl 58, (5 / 864)), (Sum.inl 5, (5 / 36)), (Sum.inl 6, (-5 / 432)), (Sum.inl 2, (-5 / 48)), (Sum.inl 69, (-5 / 54)), (Sum.inl 71, (-10 / 27)), (Sum.inl 7, (-5 / 27)), (Sum.inl 8, (-5 / 27)), (Sum.inl 1, (-5 / 216))]

def nodeValue121 : Sparse Master := [(Sum.inl 0, (1 / 32)), (Sum.inl 58, (-5 / 864)), (Sum.inl 6, (25 / 864)), (Sum.inl 2, (25 / 432)), (Sum.inl 71, (5 / 54)), (Sum.inl 8, (5 / 54)), (Sum.inl 1, (-35 / 864))]

def nodeValue122 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 9, (5 / 216)), (Sum.inl 58, (-5 / 864)), (Sum.inl 5, (-5 / 108)), (Sum.inl 6, (5 / 216)), (Sum.inl 2, (5 / 72)), (Sum.inl 69, (5 / 54)), (Sum.inl 7, (5 / 54)), (Sum.inl 35, (5 / 27)), (Sum.inl 3, (5 / 54)), (Sum.inl 495, (5 / 54)), (Sum.inl 52, (5 / 27)), (Sum.inl 1, (-25 / 864))]

def nodeValue123 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 9, (5 / 108)), (Sum.inl 6, (-5 / 432)), (Sum.inl 257, (5 / 54)), (Sum.inl 67, (5 / 27)), (Sum.inl 2, (-5 / 108)), (Sum.inl 70, (5 / 54)), (Sum.inl 7, (5 / 27)), (Sum.inl 35, (10 / 27)), (Sum.inl 3, (5 / 54)), (Sum.inl 26, (5 / 54)), (Sum.inl 1, (-5 / 72))]

def nodeValue124 : Sparse Master := [(Sum.inl 0, (1 / 32)), (Sum.inl 9, (5 / 108)), (Sum.inl 5, (-5 / 54)), (Sum.inl 6, (-5 / 432)), (Sum.inl 2, (5 / 216)), (Sum.inl 69, (5 / 54)), (Sum.inl 71, (5 / 54)), (Sum.inl 7, (5 / 27)), (Sum.inl 8, (5 / 27)), (Sum.inl 1, (-5 / 96))]

def nodeValue125 : Sparse Master := [(Sum.inl 0, (1 / 54)), (Sum.inl 9, (-5 / 54)), (Sum.inl 58, (5 / 864)), (Sum.inl 5, (-5 / 108)), (Sum.inl 2, (5 / 288)), (Sum.inl 69, (-5 / 18)), (Sum.inl 70, (-5 / 27)), (Sum.inl 35, (-5 / 27)), (Sum.inl 3, (-5 / 18)), (Sum.inl 1, (35 / 216))]

def nodeValue126 : Sparse Master := [(Sum.inl 0, (1 / 54)), (Sum.inl 58, (-5 / 864)), (Sum.inl 5, (5 / 54)), (Sum.inl 6, (5 / 288)), (Sum.inl 2, (-5 / 432)), (Sum.inl 69, (5 / 54)), (Sum.inl 7, (5 / 54)), (Sum.inl 1, (55 / 432))]

def nodeValue127 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 9, (5 / 108)), (Sum.inl 5, (-5 / 216)), (Sum.inl 6, (-5 / 432)), (Sum.inl 69, (5 / 54)), (Sum.inl 70, (5 / 54)), (Sum.inl 35, (5 / 54)), (Sum.inl 3, (5 / 54)), (Sum.inl 1, (5 / 54))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue1133 : Sparse Master := [(Sum.inr 1133, (1 / 1))]

def nodeValue1134 : Sparse Master := [(Sum.inr 1134, (1 / 1))]

def nodeValue1135 : Sparse Master := [(Sum.inr 1135, (1 / 1))]

def nodeValue1136 : Sparse Master := [(Sum.inr 1136, (1 / 1))]

def nodeValue1137 : Sparse Master := [(Sum.inr 1137, (1 / 1))]

def nodeValue1138 : Sparse Master := [(Sum.inr 1138, (1 / 1))]

def nodeValue1139 : Sparse Master := [(Sum.inr 1139, (1 / 1))]

def nodeValue1140 : Sparse Master := [(Sum.inr 1140, (1 / 1))]

def nodeValue1141 : Sparse Master := [(Sum.inr 1141, (1 / 1))]

def nodeValue1142 : Sparse Master := [(Sum.inr 1142, (1 / 1))]

def nodeValue1143 : Sparse Master := [(Sum.inr 1143, (1 / 1))]

def nodeValue1144 : Sparse Master := [(Sum.inr 1144, (1 / 1))]

def nodeValue1145 : Sparse Master := [(Sum.inr 1145, (1 / 1))]

def nodeValue1146 : Sparse Master := [(Sum.inr 1146, (1 / 1))]

def nodeValue1147 : Sparse Master := [(Sum.inr 1147, (1 / 1))]

def nodeValue1148 : Sparse Master := [(Sum.inr 1148, (1 / 1))]

def nodeValue1149 : Sparse Master := [(Sum.inr 1149, (1 / 1))]

def nodeValue1150 : Sparse Master := [(Sum.inr 1150, (1 / 1))]

def nodeValue1151 : Sparse Master := [(Sum.inr 1151, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue1161 : Sparse Master := [(Sum.inl 0, (-1 / 270)), (Sum.inl 9, (1 / 54)), (Sum.inl 58, (-1 / 864)), (Sum.inl 5, (1 / 108)), (Sum.inl 2, (-1 / 288)), (Sum.inl 69, (1 / 18)), (Sum.inl 70, (1 / 27)), (Sum.inl 35, (1 / 27)), (Sum.inl 3, (1 / 18)), (Sum.inl 1, (-7 / 216))]

def nodeValue1162 : Sparse Master := [(Sum.inl 0, (-7 / 1440)), (Sum.inl 9, (1 / 54)), (Sum.inl 58, (-1 / 864)), (Sum.inl 5, (-1 / 36)), (Sum.inl 6, (1 / 432)), (Sum.inl 2, (1 / 48)), (Sum.inl 69, (1 / 54)), (Sum.inl 71, (2 / 27)), (Sum.inl 7, (1 / 27)), (Sum.inl 8, (1 / 27)), (Sum.inl 1, (1 / 216))]

def nodeValue1163 : Sparse Master := [(Sum.inl 0, (-1 / 270)), (Sum.inl 58, (1 / 864)), (Sum.inl 5, (-1 / 54)), (Sum.inl 6, (-1 / 288)), (Sum.inl 2, (1 / 432)), (Sum.inl 69, (-1 / 54)), (Sum.inl 7, (-1 / 54)), (Sum.inl 1, (-11 / 432))]

def nodeValue1164 : Sparse Master := [(Sum.inl 0, (-29 / 4320)), (Sum.inl 9, (1 / 54)), (Sum.inl 58, (-1 / 864)), (Sum.inl 5, (-5 / 108)), (Sum.inl 6, (1 / 216)), (Sum.inl 2, (11 / 864)), (Sum.inl 69, (1 / 27)), (Sum.inl 70, (1 / 54)), (Sum.inl 71, (1 / 27)), (Sum.inl 7, (2 / 27)), (Sum.inl 35, (1 / 27)), (Sum.inl 8, (2 / 27)), (Sum.inl 3, (1 / 27)), (Sum.inl 1, (5 / 288))]

def nodeValue1166 : Sparse Master := [(Sum.inl 0, (-11 / 2160)), (Sum.inl 9, (-1 / 108)), (Sum.inl 5, (1 / 216)), (Sum.inl 6, (1 / 432)), (Sum.inl 69, (-1 / 54)), (Sum.inl 70, (-1 / 54)), (Sum.inl 35, (-1 / 54)), (Sum.inl 3, (-1 / 54)), (Sum.inl 1, (-1 / 54))]

def nodeValue1167 : Sparse Master := [(Sum.inl 0, (-1 / 216)), (Sum.inl 9, (-1 / 108)), (Sum.inl 5, (1 / 108)), (Sum.inl 6, (1 / 432)), (Sum.inl 2, (1 / 432)), (Sum.inl 71, (-1 / 27)), (Sum.inl 1, (-1 / 216))]

def nodeValue1168 : Sparse Master := [(Sum.inl 0, (-11 / 2160)), (Sum.inl 9, (-1 / 108)), (Sum.inl 58, (-1 / 432)), (Sum.inl 5, (1 / 54)), (Sum.inl 6, (1 / 216)), (Sum.inl 2, (-1 / 432)), (Sum.inl 1, (-1 / 48))]

def nodeValue1170 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 58, (1 / 864)), (Sum.inl 5, (1 / 108)), (Sum.inl 6, (-7 / 864)), (Sum.inl 2, (7 / 864)), (Sum.inl 70, (-1 / 54)), (Sum.inl 7, (-1 / 54)), (Sum.inl 35, (-1 / 27)), (Sum.inl 1, (13 / 864))]

def nodeValue1172 : Sparse Master := [(Sum.inl 0, (-1 / 160)), (Sum.inl 9, (-1 / 108)), (Sum.inl 5, (1 / 54)), (Sum.inl 6, (1 / 432)), (Sum.inl 2, (-1 / 216)), (Sum.inl 69, (-1 / 54)), (Sum.inl 71, (-1 / 54)), (Sum.inl 7, (-1 / 27)), (Sum.inl 8, (-1 / 27)), (Sum.inl 1, (1 / 96))]

def nodeValue1173 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 9, (-1 / 108)), (Sum.inl 58, (-1 / 432)), (Sum.inl 5, (-1 / 54)), (Sum.inl 6, (1 / 108)), (Sum.inl 2, (5 / 432)), (Sum.inl 1, (7 / 432))]

def nodeValue1175 : Sparse Master := [(Sum.inl 0, (-11 / 2160)), (Sum.inl 9, (1 / 108)), (Sum.inl 6, (-1 / 432)), (Sum.inl 2, (-1 / 432)), (Sum.inl 69, (1 / 27)), (Sum.inl 7, (1 / 27)), (Sum.inl 1, (-1 / 48))]

def nodeValue1176 : Sparse Master := [(Sum.inl 0, (-7 / 1080)), (Sum.inl 9, (1 / 108)), (Sum.inl 6, (-1 / 432)), (Sum.inl 2, (-1 / 432)), (Sum.inl 71, (1 / 27)), (Sum.inl 8, (1 / 27)), (Sum.inl 1, (1 / 72))]

def nodeValue1177 : Sparse Master := [(Sum.inl 0, (-1 / 180)), (Sum.inl 9, (1 / 108)), (Sum.inl 5, (1 / 108)), (Sum.inl 6, (-1 / 432)), (Sum.inl 2, (1 / 216)), (Sum.inl 70, (1 / 27)), (Sum.inl 7, (1 / 27)), (Sum.inl 35, (1 / 27)), (Sum.inl 1, (-1 / 48))]

def nodeValue1191 : Sparse Master := [(Sum.inr 1191, (1 / 1))]

def nodeValue1192 : Sparse Master := [(Sum.inr 1192, (1 / 1))]

def nodeValue1193 : Sparse Master := [(Sum.inr 1193, (1 / 1))]

def nodeValue1194 : Sparse Master := [(Sum.inr 1194, (1 / 1))]

def nodeValue1195 : Sparse Master := [(Sum.inr 1195, (1 / 1))]

def nodeValue1196 : Sparse Master := [(Sum.inr 1196, (1 / 1))]

def nodeValue1197 : Sparse Master := [(Sum.inr 1197, (1 / 1))]

def nodeValue1198 : Sparse Master := [(Sum.inr 1198, (1 / 1))]

def nodeValue1199 : Sparse Master := [(Sum.inr 1199, (1 / 1))]

def nodeValue1200 : Sparse Master := [(Sum.inr 1200, (1 / 1))]

def nodeValue1201 : Sparse Master := [(Sum.inr 1201, (1 / 1))]

def nodeValue1202 : Sparse Master := [(Sum.inr 1202, (1 / 1))]

def nodeValue1203 : Sparse Master := [(Sum.inr 1203, (1 / 1))]

def nodeValue1204 : Sparse Master := [(Sum.inr 1204, (1 / 1))]

def nodeValue1205 : Sparse Master := [(Sum.inr 1205, (1 / 1))]

def nodeValue1206 : Sparse Master := [(Sum.inr 1206, (1 / 1))]

def nodeValue1208 : Sparse Master := [(Sum.inr 1208, (1 / 1))]

def nodeValue1209 : Sparse Master := [(Sum.inr 1209, (1 / 1))]

def nodeValue1210 : Sparse Master := [(Sum.inr 1210, (1 / 1))]

def nodeValue1211 : Sparse Master := [(Sum.inr 1211, (1 / 1))]

def nodeValue1212 : Sparse Master := [(Sum.inr 1212, (1 / 1))]

def nodeValue1213 : Sparse Master := [(Sum.inr 1213, (1 / 1))]

def nodeValue1214 : Sparse Master := [(Sum.inr 1214, (1 / 1))]

def nodeValue1215 : Sparse Master := [(Sum.inr 1215, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue1239 : Sparse Master := [(Sum.inr 1239, (1 / 1))]

def nodeValue1240 : Sparse Master := [(Sum.inr 1240, (1 / 1))]

def nodeValue1241 : Sparse Master := [(Sum.inr 1241, (1 / 1))]

def nodeValue1242 : Sparse Master := [(Sum.inr 1242, (1 / 1))]

def nodeValue1243 : Sparse Master := [(Sum.inr 1243, (1 / 1))]

def nodeValue1244 : Sparse Master := [(Sum.inr 1244, (1 / 1))]

def nodeValue1245 : Sparse Master := [(Sum.inr 1245, (1 / 1))]

def nodeValue1246 : Sparse Master := [(Sum.inr 1246, (1 / 1))]

def nodeValue1247 : Sparse Master := [(Sum.inr 1247, (1 / 1))]

def nodeValue1248 : Sparse Master := [(Sum.inr 1248, (1 / 1))]

def nodeValue1249 : Sparse Master := [(Sum.inr 1249, (1 / 1))]

def nodeValue1250 : Sparse Master := [(Sum.inr 1250, (1 / 1))]

def nodeValue1252 : Sparse Master := [(Sum.inr 1252, (1 / 1))]

def nodeValue1253 : Sparse Master := [(Sum.inr 1253, (1 / 1))]

def nodeValue1255 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 6, (-5 / 144)), (Sum.inl 82, (1 / 27)), (Sum.inl 1, (1 / 216))]

def nodeValue1256 : Sparse Master := [(Sum.inr 1256, (1 / 1))]

def nodeValue1257 : Sparse Master := [(Sum.inr 1257, (1 / 1))]

def nodeValue1258 : Sparse Master := [(Sum.inr 1258, (1 / 1))]

def nodeValue1259 : Sparse Master := [(Sum.inr 1259, (1 / 1))]

def nodeValue1260 : Sparse Master := [(Sum.inr 1260, (1 / 1))]

def nodeValue1261 : Sparse Master := [(Sum.inr 1261, (1 / 1))]

def nodeValue1262 : Sparse Master := [(Sum.inr 1262, (1 / 1))]

def nodeValue1263 : Sparse Master := [(Sum.inr 1263, (1 / 1))]

def nodeValue1264 : Sparse Master := [(Sum.inr 1264, (1 / 1))]

def nodeValue1265 : Sparse Master := [(Sum.inl 0, (-23 / 4320)), (Sum.inl 5, (-2 / 27)), (Sum.inl 6, (1 / 144)), (Sum.inl 2, (41 / 864)), (Sum.inl 7, (1 / 9)), (Sum.inl 35, (1 / 27)), (Sum.inl 8, (1 / 9)), (Sum.inl 3, (1 / 18)), (Sum.inl 1, (5 / 432))]

def nodeValue1266 : Sparse Master := [(Sum.inl 0, (-19 / 4320)), (Sum.inl 5, (1 / 36)), (Sum.inl 6, (-1 / 288)), (Sum.inl 2, (-1 / 72)), (Sum.inl 7, (-1 / 54)), (Sum.inl 8, (-1 / 27)), (Sum.inl 1, (-5 / 432))]

def nodeValue1267 : Sparse Master := [(Sum.inl 0, (-1 / 160)), (Sum.inl 5, (5 / 216)), (Sum.inl 6, (-1 / 288)), (Sum.inl 2, (-1 / 96)), (Sum.inl 7, (-1 / 27)), (Sum.inl 35, (-1 / 54)), (Sum.inl 8, (-1 / 54)), (Sum.inl 3, (-1 / 54)), (Sum.inl 1, (1 / 96))]

def nodeValue1268 : Sparse Master := [(Sum.inr 1268, (1 / 1))]

def nodeValue1269 : Sparse Master := [(Sum.inl 0, (-7 / 1080)), (Sum.inl 5, (-1 / 54)), (Sum.inl 6, (1 / 108)), (Sum.inl 2, (1 / 72)), (Sum.inl 1, (1 / 54))]

def nodeValue1270 : Sparse Master := [(Sum.inr 1270, (1 / 1))]

def nodeValue1271 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 5, (-1 / 108)), (Sum.inl 6, (1 / 108)), (Sum.inl 2, (1 / 108)), (Sum.inl 35, (1 / 27)), (Sum.inl 1, (7 / 432))]

def nodeValue1272 : Sparse Master := [(Sum.inr 1272, (1 / 1))]

def nodeValue1273 : Sparse Master := [(Sum.inr 1273, (1 / 1))]

def nodeValue1274 : Sparse Master := [(Sum.inl 0, (-7 / 1080)), (Sum.inl 5, (-1 / 27)), (Sum.inl 7, (1 / 27)), (Sum.inl 8, (1 / 27)), (Sum.inl 1, (1 / 72))]

def nodeValue1275 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 5, (1 / 36)), (Sum.inl 6, (-5 / 144)), (Sum.inl 1, (1 / 72))]

def nodeValue1276 : Sparse Master := [(Sum.inr 1276, (1 / 1))]

def nodeValue1277 : Sparse Master := [(Sum.inr 1277, (1 / 1))]

def nodeValue1278 : Sparse Master := [(Sum.inr 1278, (1 / 1))]

def nodeValue1279 : Sparse Master := [(Sum.inr 1279, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue128 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 9, (5 / 108)), (Sum.inl 5, (-5 / 108)), (Sum.inl 6, (-5 / 432)), (Sum.inl 2, (-5 / 432)), (Sum.inl 71, (5 / 27)), (Sum.inl 1, (5 / 216))]

def nodeValue129 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 9, (5 / 108)), (Sum.inl 58, (5 / 432)), (Sum.inl 5, (-5 / 54)), (Sum.inl 6, (-5 / 216)), (Sum.inl 2, (5 / 432)), (Sum.inl 1, (5 / 48))]

def nodeValue130 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 9, (5 / 108)), (Sum.inl 5, (-5 / 216)), (Sum.inl 6, (-5 / 432)), (Sum.inl 256, (-5 / 18)), (Sum.inl 2, (5 / 864)), (Sum.inl 81, (-5 / 18)), (Sum.inl 7, (5 / 27)), (Sum.inl 35, (5 / 54)), (Sum.inl 8, (5 / 54)), (Sum.inl 3, (5 / 54)), (Sum.inl 1, (-5 / 96))]

def nodeValue131 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 9, (-5 / 108)), (Sum.inl 5, (-5 / 108)), (Sum.inl 6, (5 / 432)), (Sum.inl 2, (-5 / 216)), (Sum.inl 70, (-5 / 27)), (Sum.inl 7, (-5 / 27)), (Sum.inl 35, (-5 / 27)), (Sum.inl 1, (5 / 48))]

def nodeValue132 : Sparse Master := [(Sum.inl 0, (7 / 216)), (Sum.inl 9, (-5 / 108)), (Sum.inl 6, (5 / 432)), (Sum.inl 2, (5 / 432)), (Sum.inl 71, (-5 / 27)), (Sum.inl 8, (-5 / 27)), (Sum.inl 1, (-5 / 72))]

def nodeValue133 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 9, (-5 / 108)), (Sum.inl 6, (5 / 432)), (Sum.inl 2, (5 / 432)), (Sum.inl 69, (-5 / 27)), (Sum.inl 7, (-5 / 27)), (Sum.inl 1, (5 / 48))]

def nodeValue134 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 9, (-5 / 108)), (Sum.inl 5, (-5 / 108)), (Sum.inl 6, (5 / 432)), (Sum.inl 257, (-5 / 27)), (Sum.inl 67, (-5 / 27)), (Sum.inl 2, (-25 / 432)), (Sum.inl 35, (-5 / 27)), (Sum.inl 1, (-5 / 72))]

def nodeValue139 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 5, (5 / 54)), (Sum.inl 67, (5 / 54)), (Sum.inl 2, (5 / 144)), (Sum.inl 35, (5 / 27)), (Sum.inl 8, (5 / 54)), (Sum.inl 1, (-5 / 144))]

def nodeValue140 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 5, (-5 / 54)), (Sum.inl 6, (25 / 216)), (Sum.inl 1, (-5 / 108))]

def nodeValue141 : Sparse Master := [(Sum.inl 0, (23 / 864)), (Sum.inl 5, (10 / 27)), (Sum.inl 6, (-5 / 144)), (Sum.inl 2, (-205 / 864)), (Sum.inl 7, (-5 / 9)), (Sum.inl 35, (-5 / 27)), (Sum.inl 8, (-5 / 9)), (Sum.inl 3, (-5 / 18)), (Sum.inl 1, (-25 / 432))]

def nodeValue142 : Sparse Master := [(Sum.inl 0, (1 / 32)), (Sum.inl 5, (-25 / 216)), (Sum.inl 6, (5 / 288)), (Sum.inl 2, (5 / 96)), (Sum.inl 7, (5 / 27)), (Sum.inl 35, (5 / 54)), (Sum.inl 8, (5 / 54)), (Sum.inl 3, (5 / 54)), (Sum.inl 1, (-5 / 96))]

def nodeValue143 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 5, (5 / 108)), (Sum.inl 6, (-5 / 108)), (Sum.inl 2, (-5 / 108)), (Sum.inl 35, (-5 / 27)), (Sum.inl 1, (-35 / 432))]

def nodeValue144 : Sparse Master := [(Sum.inl 0, (19 / 864)), (Sum.inl 5, (-5 / 36)), (Sum.inl 6, (5 / 288)), (Sum.inl 2, (5 / 72)), (Sum.inl 7, (5 / 54)), (Sum.inl 8, (5 / 27)), (Sum.inl 1, (25 / 432))]

def nodeValue145 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 5, (-5 / 72)), (Sum.inl 6, (5 / 432)), (Sum.inl 67, (5 / 54)), (Sum.inl 2, (25 / 432)), (Sum.inl 7, (5 / 27)), (Sum.inl 35, (5 / 18)), (Sum.inl 3, (5 / 27)), (Sum.inl 52, (5 / 54)), (Sum.inl 26, (5 / 54)), (Sum.inl 1, (-5 / 108))]

def nodeValue146 : Sparse Master := [(Sum.inl 0, (7 / 216)), (Sum.inl 5, (5 / 54)), (Sum.inl 6, (-5 / 108)), (Sum.inl 2, (-5 / 72)), (Sum.inl 1, (-5 / 54))]

def nodeValue147 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 5, (5 / 108)), (Sum.inl 6, (-5 / 144)), (Sum.inl 2, (-5 / 216)), (Sum.inl 35, (-5 / 27)), (Sum.inl 52, (-5 / 27)), (Sum.inl 1, (-25 / 432))]

def nodeValue148 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 5, (5 / 36)), (Sum.inl 67, (-5 / 27)), (Sum.inl 2, (-5 / 216)), (Sum.inl 7, (-5 / 27)), (Sum.inl 35, (-5 / 27)), (Sum.inl 1, (-25 / 432))]

def nodeValue149 : Sparse Master := [(Sum.inl 0, (7 / 216)), (Sum.inl 5, (5 / 27)), (Sum.inl 7, (-5 / 27)), (Sum.inl 8, (-5 / 27)), (Sum.inl 1, (-5 / 72))]

def nodeValue150 : Sparse Master := [(Sum.inl 0, (7 / 288)), (Sum.inl 5, (5 / 72)), (Sum.inl 6, (-5 / 288)), (Sum.inl 67, (5 / 54)), (Sum.inl 2, (-5 / 216)), (Sum.inl 81, (-5 / 18)), (Sum.inl 7, (5 / 54)), (Sum.inl 35, (5 / 27)), (Sum.inl 3, (5 / 27)), (Sum.inl 26, (5 / 27)), (Sum.inl 4, (5 / 54)), (Sum.inl 1, (-35 / 432))]

def nodeValue151 : Sparse Master := [(Sum.inl 0, (1 / 54)), (Sum.inl 5, (5 / 108)), (Sum.inl 6, (-5 / 288)), (Sum.inl 2, (-35 / 864)), (Sum.inl 7, (5 / 18)), (Sum.inl 35, (5 / 27)), (Sum.inl 3, (5 / 18)), (Sum.inl 1, (5 / 54))]

def nodeValue152 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 5, (-5 / 108)), (Sum.inl 6, (5 / 432)), (Sum.inl 2, (5 / 144)), (Sum.inl 7, (-5 / 27)), (Sum.inl 35, (-5 / 27)), (Sum.inl 3, (-5 / 27)), (Sum.inl 1, (55 / 432))]

def nodeValue153 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 5, (-5 / 108)), (Sum.inl 6, (5 / 432)), (Sum.inl 2, (5 / 108)), (Sum.inl 81, (5 / 9)), (Sum.inl 1, (-5 / 144))]

def nodeValue154 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 6, (-5 / 144)), (Sum.inl 2, (-5 / 72)), (Sum.inl 35, (5 / 9)), (Sum.inl 1, (5 / 48))]

def nodeValue155 : Sparse Master := [(Sum.inl 0, (37 / 864)), (Sum.inl 6, (-5 / 288)), (Sum.inl 7, (5 / 54)), (Sum.inl 8, (5 / 27)), (Sum.inl 1, (-35 / 432))]

def nodeValue156 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 6, (5 / 432)), (Sum.inl 7, (-5 / 27)), (Sum.inl 1, (5 / 36))]

def nodeValue157 : Sparse Master := [(Sum.inl 0, (19 / 432)), (Sum.inl 6, (5 / 432)), (Sum.inl 8, (-5 / 27)), (Sum.inl 1, (-5 / 54))]

def nodeValue158 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 5, (-5 / 36)), (Sum.inl 6, (-5 / 144)), (Sum.inl 1, (5 / 36))]

def nodeValue159 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 5, (5 / 36)), (Sum.inl 67, (5 / 9)), (Sum.inl 2, (-5 / 72)), (Sum.inl 1, (-5 / 72))]

def nodeValue160 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 5, (5 / 36)), (Sum.inl 7, (5 / 9)), (Sum.inl 1, (5 / 18))]

def nodeValue161 : Sparse Master := [(Sum.inl 0, (1 / 24)), (Sum.inl 5, (5 / 36)), (Sum.inl 8, (5 / 9)), (Sum.inl 1, (-5 / 72))]

def nodeValue162 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 5, (5 / 9)), (Sum.inl 6, (5 / 36)), (Sum.inl 1, (5 / 18))]

def nodeValue163 : Sparse Master := [(Sum.inl 0, (1 / 54)), (Sum.inl 9, (5 / 216)), (Sum.inl 5, (5 / 54)), (Sum.inl 6, (-5 / 144)), (Sum.inl 257, (-5 / 54)), (Sum.inl 266, (5 / 18)), (Sum.inl 67, (-5 / 27)), (Sum.inl 34, (-5 / 54)), (Sum.inl 68, (-5 / 72)), (Sum.inl 69, (-5 / 54)), (Sum.inl 70, (-5 / 18)), (Sum.inl 7, (-10 / 27)), (Sum.inl 35, (-20 / 27)), (Sum.inl 124, (5 / 18)), (Sum.inl 3, (-5 / 18)), (Sum.inl 13, (-5 / 54)), (Sum.inl 196, (5 / 18)), (Sum.inl 197, (5 / 9)), (Sum.inl 26, (-10 / 27)), (Sum.inl 1, (5 / 144))]

def nodeValue164 : Sparse Master := [(Sum.inl 0, (7 / 288)), (Sum.inl 9, (5 / 216)), (Sum.inl 5, (5 / 54)), (Sum.inl 6, (-5 / 288)), (Sum.inl 257, (-5 / 54)), (Sum.inl 260, (5 / 18)), (Sum.inl 60, (-5 / 54)), (Sum.inl 268, (5 / 18)), (Sum.inl 64, (5 / 18)), (Sum.inl 67, (-5 / 54)), (Sum.inl 34, (-5 / 54)), (Sum.inl 68, (-5 / 72)), (Sum.inl 2, (5 / 864)), (Sum.inl 69, (-5 / 54)), (Sum.inl 70, (-5 / 27)), (Sum.inl 7, (-10 / 27)), (Sum.inl 35, (-5 / 9)), (Sum.inl 125, (5 / 9)), (Sum.inl 126, (5 / 18)), (Sum.inl 3, (-25 / 54)), (Sum.inl 13, (-5 / 18)), (Sum.inl 52, (-5 / 27)), (Sum.inl 197, (5 / 18)), (Sum.inl 26, (-5 / 27)), (Sum.inl 1, (-5 / 864))]

def nodeValue165 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 5, (5 / 108)), (Sum.inl 264, (5 / 9)), (Sum.inl 266, (5 / 18)), (Sum.inl 63, (5 / 18)), (Sum.inl 65, (5 / 18)), (Sum.inl 68, (-5 / 36)), (Sum.inl 2, (-5 / 288)), (Sum.inl 7, (-5 / 54)), (Sum.inl 35, (-5 / 54)), (Sum.inl 124, (5 / 18)), (Sum.inl 125, (5 / 6)), (Sum.inl 3, (-5 / 54)), (Sum.inl 13, (-5 / 54)), (Sum.inl 196, (5 / 9)), (Sum.inl 197, (5 / 18)), (Sum.inl 23, (5 / 9)), (Sum.inl 54, (5 / 9)), (Sum.inl 55, (5 / 18)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (-5 / 96))]

def nodeValue166 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 9, (5 / 216)), (Sum.inl 5, (5 / 54)), (Sum.inl 6, (-5 / 432)), (Sum.inl 257, (-5 / 54)), (Sum.inl 260, (5 / 9)), (Sum.inl 60, (-5 / 27)), (Sum.inl 264, (5 / 6)), (Sum.inl 62, (5 / 9)), (Sum.inl 32, (-5 / 54)), (Sum.inl 68, (-5 / 72)), (Sum.inl 2, (-5 / 288)), (Sum.inl 69, (-5 / 54)), (Sum.inl 70, (-5 / 54)), (Sum.inl 7, (-5 / 27)), (Sum.inl 35, (-10 / 27)), (Sum.inl 125, (5 / 9)), (Sum.inl 3, (-5 / 27)), (Sum.inl 13, (-10 / 27)), (Sum.inl 52, (-5 / 27)), (Sum.inl 54, (5 / 9)), (Sum.inl 1, (-5 / 288))]

def nodeValue167 : Sparse Master := [(Sum.inl 0, (7 / 288)), (Sum.inl 5, (5 / 216)), (Sum.inl 263, (-5 / 9)), (Sum.inl 266, (5 / 18)), (Sum.inl 61, (5 / 18)), (Sum.inl 268, (5 / 18)), (Sum.inl 68, (-5 / 36)), (Sum.inl 2, (5 / 288)), (Sum.inl 124, (5 / 18)), (Sum.inl 125, (5 / 18)), (Sum.inl 126, (5 / 18)), (Sum.inl 51, (5 / 18)), (Sum.inl 196, (5 / 18)), (Sum.inl 197, (5 / 9)), (Sum.inl 23, (5 / 18)), (Sum.inl 54, (5 / 18)), (Sum.inl 24, (5 / 18)), (Sum.inl 55, (5 / 18)), (Sum.inl 56, (5 / 18)), (Sum.inl 27, (-5 / 36)), (Sum.inl 1, (5 / 432))]

def nodeValue168 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 266, (-5 / 18)), (Sum.inl 68, (5 / 36)), (Sum.inl 2, (-5 / 216)), (Sum.inl 124, (-5 / 18)), (Sum.inl 196, (-5 / 18)), (Sum.inl 197, (-5 / 18)), (Sum.inl 1, (-25 / 432))]

def nodeValue169 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 268, (-5 / 18)), (Sum.inl 68, (5 / 36)), (Sum.inl 2, (5 / 144)), (Sum.inl 125, (-5 / 18)), (Sum.inl 126, (-5 / 18)), (Sum.inl 197, (-5 / 18)), (Sum.inl 1, (5 / 432))]

def nodeValue170 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 264, (-5 / 9)), (Sum.inl 68, (5 / 36)), (Sum.inl 2, (-5 / 72)), (Sum.inl 125, (-5 / 9)), (Sum.inl 1, (-5 / 72))]

def nodeValue171 : Sparse Master := [(Sum.inl 0, (29 / 864)), (Sum.inl 9, (-5 / 216)), (Sum.inl 5, (-5 / 54)), (Sum.inl 6, (5 / 864)), (Sum.inl 68, (25 / 72)), (Sum.inl 2, (25 / 864)), (Sum.inl 70, (-5 / 54)), (Sum.inl 7, (-5 / 54)), (Sum.inl 35, (-5 / 18)), (Sum.inl 125, (5 / 9)), (Sum.inl 3, (-5 / 18)), (Sum.inl 13, (-5 / 54)), (Sum.inl 196, (5 / 18)), (Sum.inl 197, (5 / 9)), (Sum.inl 23, (5 / 18)), (Sum.inl 54, (5 / 18)), (Sum.inl 55, (5 / 9)), (Sum.inl 12, (-5 / 54)), (Sum.inl 26, (-5 / 27)), (Sum.inl 27, (5 / 24)), (Sum.inl 1, (-25 / 864))]

def nodeValue172 : Sparse Master := [(Sum.inl 0, (5 / 288)), (Sum.inl 9, (-5 / 216)), (Sum.inl 5, (-5 / 54)), (Sum.inl 6, (5 / 288)), (Sum.inl 260, (5 / 18)), (Sum.inl 263, (-5 / 9)), (Sum.inl 64, (5 / 9)), (Sum.inl 33, (5 / 18)), (Sum.inl 68, (25 / 72)), (Sum.inl 2, (-5 / 288)), (Sum.inl 125, (5 / 9)), (Sum.inl 3, (-5 / 27)), (Sum.inl 13, (-5 / 27)), (Sum.inl 52, (-5 / 27)), (Sum.inl 197, (5 / 18)), (Sum.inl 55, (5 / 9)), (Sum.inl 27, (5 / 24)), (Sum.inl 1, (-5 / 864))]

def nodeValue173 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 9, (5 / 216)), (Sum.inl 5, (5 / 108)), (Sum.inl 68, (-5 / 72)), (Sum.inl 2, (5 / 32)), (Sum.inl 70, (5 / 54)), (Sum.inl 35, (5 / 27)), (Sum.inl 13, (5 / 54)), (Sum.inl 196, (-5 / 18)), (Sum.inl 1, (-35 / 864))]

def nodeValue174 : Sparse Master := [(Sum.inl 0, (25 / 864)), (Sum.inl 9, (-5 / 216)), (Sum.inl 5, (-25 / 216)), (Sum.inl 6, (5 / 432)), (Sum.inl 68, (25 / 72)), (Sum.inl 2, (5 / 54)), (Sum.inl 70, (-5 / 54)), (Sum.inl 7, (-5 / 27)), (Sum.inl 35, (-5 / 18)), (Sum.inl 125, (5 / 18)), (Sum.inl 3, (-25 / 54)), (Sum.inl 13, (-5 / 54)), (Sum.inl 197, (10 / 9)), (Sum.inl 24, (5 / 9)), (Sum.inl 55, (5 / 18)), (Sum.inl 56, (5 / 9)), (Sum.inl 26, (-5 / 27)), (Sum.inl 4, (-5 / 27)), (Sum.inl 27, (5 / 24)), (Sum.inl 1, (85 / 864))]

def nodeValue175 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 9, (5 / 216)), (Sum.inl 5, (5 / 108)), (Sum.inl 6, (-5 / 864)), (Sum.inl 68, (-5 / 72)), (Sum.inl 2, (-5 / 72)), (Sum.inl 70, (5 / 54)), (Sum.inl 7, (5 / 54)), (Sum.inl 35, (5 / 27)), (Sum.inl 3, (5 / 54)), (Sum.inl 197, (-5 / 18)), (Sum.inl 26, (5 / 54)), (Sum.inl 1, (-85 / 864))]

def nodeValue176 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 9, (5 / 216)), (Sum.inl 5, (5 / 108)), (Sum.inl 6, (-5 / 432)), (Sum.inl 260, (-5 / 18)), (Sum.inl 64, (-5 / 18)), (Sum.inl 68, (-5 / 72)), (Sum.inl 2, (-5 / 288)), (Sum.inl 125, (-5 / 18)), (Sum.inl 13, (5 / 54)), (Sum.inl 52, (5 / 54)), (Sum.inl 1, (-55 / 864))]

def nodeValue177 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 5, (5 / 216)), (Sum.inl 264, (-5 / 18)), (Sum.inl 63, (-5 / 18)), (Sum.inl 68, (-5 / 36)), (Sum.inl 2, (35 / 288)), (Sum.inl 35, (5 / 54)), (Sum.inl 13, (5 / 54)), (Sum.inl 196, (-5 / 18)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (-25 / 864))]

def nodeValue178 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 68, (-5 / 36)), (Sum.inl 2, (-5 / 96)), (Sum.inl 125, (-5 / 18)), (Sum.inl 197, (-5 / 18)), (Sum.inl 55, (-5 / 18)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (-25 / 288))]

def nodeValue179 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 9, (-5 / 216)), (Sum.inl 5, (-5 / 36)), (Sum.inl 6, (5 / 288)), (Sum.inl 68, (25 / 72)), (Sum.inl 2, (5 / 108)), (Sum.inl 70, (-5 / 54)), (Sum.inl 7, (-5 / 18)), (Sum.inl 35, (-5 / 18)), (Sum.inl 125, (5 / 6)), (Sum.inl 3, (-5 / 9)), (Sum.inl 13, (-10 / 27)), (Sum.inl 196, (5 / 9)), (Sum.inl 23, (5 / 6)), (Sum.inl 54, (5 / 6)), (Sum.inl 12, (-5 / 18)), (Sum.inl 27, (5 / 24)), (Sum.inl 1, (175 / 864))]

def nodeValue180 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 9, (5 / 216)), (Sum.inl 5, (5 / 108)), (Sum.inl 6, (-5 / 432)), (Sum.inl 68, (-5 / 72)), (Sum.inl 2, (5 / 216)), (Sum.inl 70, (5 / 54)), (Sum.inl 7, (5 / 27)), (Sum.inl 35, (5 / 27)), (Sum.inl 125, (-5 / 18)), (Sum.inl 3, (5 / 27)), (Sum.inl 13, (5 / 54)), (Sum.inl 1, (5 / 36))]

def nodeValue181 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 9, (5 / 216)), (Sum.inl 5, (5 / 108)), (Sum.inl 6, (-5 / 432)), (Sum.inl 260, (-5 / 18)), (Sum.inl 264, (-5 / 18)), (Sum.inl 62, (-5 / 18)), (Sum.inl 68, (-5 / 72)), (Sum.inl 2, (-65 / 864)), (Sum.inl 54, (-5 / 18)), (Sum.inl 1, (-25 / 288))]

def nodeValue182 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 5, (5 / 216)), (Sum.inl 68, (-5 / 36)), (Sum.inl 2, (-5 / 108)), (Sum.inl 125, (-5 / 18)), (Sum.inl 196, (-5 / 18)), (Sum.inl 23, (-5 / 18)), (Sum.inl 54, (-5 / 18)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (5 / 54))]

def nodeValue183 : Sparse Master := [(Sum.inl 0, (7 / 216)), (Sum.inl 5, (5 / 216)), (Sum.inl 68, (-5 / 36)), (Sum.inl 2, (5 / 432)), (Sum.inl 197, (-5 / 9)), (Sum.inl 24, (-5 / 18)), (Sum.inl 56, (-5 / 18)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (-5 / 432))]

def nodeValue184 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 5, (5 / 216)), (Sum.inl 263, (5 / 9)), (Sum.inl 68, (-5 / 36)), (Sum.inl 2, (-5 / 144)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (-5 / 72))]

def nodeValue185 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 68, (5 / 36)), (Sum.inl 2, (5 / 36)), (Sum.inl 196, (5 / 9)), (Sum.inl 1, (5 / 36))]

def nodeValue186 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 68, (5 / 36)), (Sum.inl 2, (-5 / 144)), (Sum.inl 197, (5 / 9)), (Sum.inl 1, (-5 / 72))]

def nodeValue187 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 68, (5 / 36)), (Sum.inl 2, (-5 / 144)), (Sum.inl 125, (5 / 9)), (Sum.inl 1, (5 / 48))]

def nodeValue188 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 264, (5 / 9)), (Sum.inl 68, (5 / 36)), (Sum.inl 2, (5 / 48)), (Sum.inl 1, (-5 / 144))]

def nodeValue189 : Sparse Master := [(Sum.inl 0, (19 / 864)), (Sum.inl 9, (-5 / 216)), (Sum.inl 5, (-5 / 36)), (Sum.inl 6, (5 / 288)), (Sum.inl 257, (-5 / 54)), (Sum.inl 264, (5 / 9)), (Sum.inl 266, (5 / 6)), (Sum.inl 65, (5 / 6)), (Sum.inl 67, (-5 / 18)), (Sum.inl 34, (-5 / 18)), (Sum.inl 68, (25 / 72)), (Sum.inl 2, (25 / 288)), (Sum.inl 35, (-5 / 18)), (Sum.inl 3, (-5 / 18)), (Sum.inl 13, (-5 / 54)), (Sum.inl 54, (5 / 6)), (Sum.inl 26, (-5 / 9)), (Sum.inl 27, (5 / 24)), (Sum.inl 1, (65 / 864))]

def nodeValue190 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 9, (5 / 216)), (Sum.inl 5, (5 / 108)), (Sum.inl 6, (-5 / 432)), (Sum.inl 257, (5 / 54)), (Sum.inl 266, (-5 / 18)), (Sum.inl 67, (5 / 27)), (Sum.inl 34, (5 / 54)), (Sum.inl 68, (-5 / 72)), (Sum.inl 2, (-5 / 144)), (Sum.inl 35, (5 / 27)), (Sum.inl 26, (5 / 27)), (Sum.inl 1, (-5 / 432))]

def nodeValue191 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 9, (-5 / 216)), (Sum.inl 5, (-5 / 36)), (Sum.inl 6, (5 / 288)), (Sum.inl 257, (-5 / 54)), (Sum.inl 60, (-5 / 27)), (Sum.inl 264, (5 / 18)), (Sum.inl 266, (5 / 9)), (Sum.inl 61, (5 / 9)), (Sum.inl 32, (-5 / 54)), (Sum.inl 268, (5 / 9)), (Sum.inl 65, (5 / 18)), (Sum.inl 67, (-5 / 54)), (Sum.inl 34, (-5 / 27)), (Sum.inl 68, (25 / 72)), (Sum.inl 2, (35 / 864)), (Sum.inl 35, (-5 / 18)), (Sum.inl 3, (-10 / 27)), (Sum.inl 13, (-5 / 9)), (Sum.inl 54, (5 / 18)), (Sum.inl 55, (5 / 9)), (Sum.inl 12, (-5 / 27)), (Sum.inl 26, (-5 / 27)), (Sum.inl 27, (5 / 24)), (Sum.inl 1, (5 / 108))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue1280 : Sparse Master := [(Sum.inr 1280, (1 / 1))]

def nodeValue1282 : Sparse Master := [(Sum.inr 1282, (1 / 1))]

def nodeValue1283 : Sparse Master := [(Sum.inr 1283, (1 / 1))]

def nodeValue1286 : Sparse Master := [(Sum.inr 1286, (1 / 1))]

def nodeValue1287 : Sparse Master := [(Sum.inr 1287, (1 / 1))]

def nodeValue1288 : Sparse Master := [(Sum.inr 1288, (1 / 1))]

def nodeValue1289 : Sparse Master := [(Sum.inr 1289, (1 / 1))]

def nodeValue1291 : Sparse Master := [(Sum.inr 1291, (1 / 1))]

def nodeValue1292 : Sparse Master := [(Sum.inr 1292, (1 / 1))]

def nodeValue1293 : Sparse Master := [(Sum.inr 1293, (1 / 1))]

def nodeValue1294 : Sparse Master := [(Sum.inr 1294, (1 / 1))]

def nodeValue1295 : Sparse Master := [(Sum.inr 1295, (1 / 1))]

def nodeValue1296 : Sparse Master := [(Sum.inr 1296, (1 / 1))]

def nodeValue1297 : Sparse Master := [(Sum.inr 1297, (1 / 1))]

def nodeValue1298 : Sparse Master := [(Sum.inl 0, (-1 / 270)), (Sum.inl 5, (-1 / 108)), (Sum.inl 6, (1 / 288)), (Sum.inl 2, (7 / 864)), (Sum.inl 7, (-1 / 18)), (Sum.inl 35, (-1 / 27)), (Sum.inl 3, (-1 / 18)), (Sum.inl 1, (-1 / 54))]

def nodeValue1299 : Sparse Master := [(Sum.inl 0, (-37 / 4320)), (Sum.inl 6, (1 / 288)), (Sum.inl 7, (-1 / 54)), (Sum.inl 8, (-1 / 27)), (Sum.inl 1, (7 / 432))]

def nodeValue1300 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 6, (-1 / 432)), (Sum.inl 7, (1 / 27)), (Sum.inl 1, (-1 / 36))]

def nodeValue1301 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 6, (-1 / 432)), (Sum.inl 8, (1 / 27)), (Sum.inl 1, (1 / 54))]

def nodeValue1302 : Sparse Master := [(Sum.inl 0, (-11 / 2160)), (Sum.inl 5, (1 / 108)), (Sum.inl 6, (-1 / 432)), (Sum.inl 2, (-1 / 144)), (Sum.inl 7, (1 / 27)), (Sum.inl 35, (1 / 27)), (Sum.inl 3, (1 / 27)), (Sum.inl 1, (-11 / 432))]

def nodeValue1303 : Sparse Master := [(Sum.inr 1303, (1 / 1))]

def nodeValue1304 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 5, (1 / 36)), (Sum.inl 6, (1 / 144)), (Sum.inl 1, (-1 / 36))]

def nodeValue1305 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 6, (-1 / 432)), (Sum.inl 7, (1 / 27)), (Sum.inl 1, (-1 / 36))]

def nodeValue1306 : Sparse Master := [(Sum.inr 1306, (1 / 1))]

def nodeValue1307 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 5, (1 / 36)), (Sum.inl 6, (1 / 144)), (Sum.inl 1, (-1 / 36))]

def nodeValue1308 : Sparse Master := [(Sum.inl 0, (-1 / 180)), (Sum.inl 6, (1 / 144)), (Sum.inl 2, (1 / 72)), (Sum.inl 35, (-1 / 9)), (Sum.inl 1, (-1 / 48))]

def nodeValue1309 : Sparse Master := [(Sum.inr 1309, (1 / 1))]

def nodeValue1310 : Sparse Master := [(Sum.inr 1310, (1 / 1))]

def nodeValue1311 : Sparse Master := [(Sum.inl 0, (-1 / 180)), (Sum.inl 5, (-1 / 36)), (Sum.inl 7, (-1 / 9)), (Sum.inl 1, (-1 / 18))]

def nodeValue1312 : Sparse Master := [(Sum.inl 0, (-1 / 120)), (Sum.inl 5, (-1 / 36)), (Sum.inl 8, (-1 / 9)), (Sum.inl 1, (1 / 72))]

def nodeValue1313 : Sparse Master := [(Sum.inl 0, (-1 / 180)), (Sum.inl 5, (-1 / 9)), (Sum.inl 6, (-1 / 36)), (Sum.inl 1, (-1 / 18))]

def nodeValue1314 : Sparse Master := [(Sum.inr 1314, (1 / 1))]

def nodeValue1315 : Sparse Master := [(Sum.inr 1315, (1 / 1))]

def nodeValue1316 : Sparse Master := [(Sum.inr 1316, (1 / 1))]

def nodeValue1317 : Sparse Master := [(Sum.inr 1317, (1 / 1))]

def nodeValue1318 : Sparse Master := [(Sum.inr 1318, (1 / 1))]

def nodeValue1319 : Sparse Master := [(Sum.inr 1319, (1 / 1))]

def nodeValue1320 : Sparse Master := [(Sum.inr 1320, (1 / 1))]

def nodeValue1321 : Sparse Master := [(Sum.inr 1321, (1 / 1))]

def nodeValue1322 : Sparse Master := [(Sum.inr 1322, (1 / 1))]

def nodeValue1323 : Sparse Master := [(Sum.inr 1323, (1 / 1))]

def nodeValue1324 : Sparse Master := [(Sum.inr 1324, (1 / 1))]

def nodeValue1325 : Sparse Master := [(Sum.inr 1325, (1 / 1))]

def nodeValue1326 : Sparse Master := [(Sum.inr 1326, (1 / 1))]

def nodeValue1327 : Sparse Master := [(Sum.inr 1327, (1 / 1))]

def nodeValue1328 : Sparse Master := [(Sum.inr 1328, (1 / 1))]

def nodeValue1329 : Sparse Master := []

def nodeValue1330 : Sparse Master := [(Sum.inr 1330, (1 / 1))]

def nodeValue1331 : Sparse Master := []

def nodeValue1332 : Sparse Master := [(Sum.inr 1332, (1 / 1))]

def nodeValue1333 : Sparse Master := [(Sum.inr 1333, (1 / 1))]

def nodeValue1334 : Sparse Master := [(Sum.inr 1334, (1 / 1))]

def nodeValue1335 : Sparse Master := [(Sum.inr 1335, (1 / 1))]

def nodeValue1336 : Sparse Master := [(Sum.inr 1336, (1 / 1))]

def nodeValue1337 : Sparse Master := [(Sum.inr 1337, (1 / 1))]

def nodeValue1338 : Sparse Master := [(Sum.inr 1338, (1 / 1))]

def nodeValue1339 : Sparse Master := [(Sum.inl 0, (-37 / 4320)), (Sum.inl 9, (1 / 54)), (Sum.inl 58, (-1 / 864)), (Sum.inl 5, (-1 / 18)), (Sum.inl 6, (1 / 144)), (Sum.inl 2, (7 / 432)), (Sum.inl 69, (1 / 54)), (Sum.inl 71, (2 / 27)), (Sum.inl 8, (2 / 27)), (Sum.inl 52, (1 / 27)), (Sum.inl 1, (1 / 216))]

def nodeValue1340 : Sparse Master := [(Sum.inl 0, (-1 / 160)), (Sum.inl 58, (1 / 864)), (Sum.inl 5, (1 / 54)), (Sum.inl 6, (-1 / 144)), (Sum.inl 2, (-1 / 48)), (Sum.inl 69, (-1 / 54)), (Sum.inl 52, (-1 / 27)), (Sum.inl 1, (-1 / 108))]

def nodeValue1341 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 9, (1 / 54)), (Sum.inl 58, (-1 / 864)), (Sum.inl 5, (-1 / 54)), (Sum.inl 6, (1 / 432)), (Sum.inl 2, (1 / 108)), (Sum.inl 69, (1 / 27)), (Sum.inl 70, (1 / 54)), (Sum.inl 71, (1 / 27)), (Sum.inl 7, (1 / 27)), (Sum.inl 35, (1 / 27)), (Sum.inl 3, (1 / 54)), (Sum.inl 52, (1 / 27)), (Sum.inl 1, (7 / 864))]

def nodeValue1342 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 58, (1 / 864)), (Sum.inl 5, (1 / 108)), (Sum.inl 6, (-1 / 216)), (Sum.inl 2, (1 / 108)), (Sum.inl 71, (-1 / 54)), (Sum.inl 1, (7 / 864))]

def nodeValue1343 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 9, (-1 / 108)), (Sum.inl 5, (1 / 108)), (Sum.inl 6, (1 / 864)), (Sum.inl 2, (5 / 432)), (Sum.inl 69, (-1 / 54)), (Sum.inl 70, (-1 / 54)), (Sum.inl 7, (-1 / 27)), (Sum.inl 35, (-1 / 27)), (Sum.inl 3, (-1 / 54)), (Sum.inl 52, (-1 / 54)), (Sum.inl 1, (5 / 288))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue1344 : Sparse Master := [(Sum.inl 0, (-17 / 2160)), (Sum.inl 9, (-1 / 108)), (Sum.inl 5, (1 / 54)), (Sum.inl 2, (-5 / 432)), (Sum.inl 71, (-1 / 27)), (Sum.inl 8, (-1 / 27)), (Sum.inl 1, (-1 / 54))]

def nodeValue1345 : Sparse Master := []

def nodeValue1346 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 58, (1 / 864)), (Sum.inl 5, (-1 / 216)), (Sum.inl 2, (-37 / 864)), (Sum.inl 70, (-1 / 54)), (Sum.inl 35, (-1 / 54)), (Sum.inl 1, (-1 / 432))]

def nodeValue1347 : Sparse Master := [(Sum.inr 1347, (1 / 1))]

def nodeValue1348 : Sparse Master := [(Sum.inr 1348, (1 / 1))]

def nodeValue1349 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 9, (1 / 108)), (Sum.inl 5, (1 / 108)), (Sum.inl 2, (-1 / 27)), (Sum.inl 70, (1 / 27)), (Sum.inl 35, (1 / 27)), (Sum.inl 1, (1 / 144))]

def nodeValue1354 : Sparse Master := [(Sum.inr 1354, (1 / 1))]

def nodeValue1355 : Sparse Master := [(Sum.inr 1355, (1 / 1))]

def nodeValue1356 : Sparse Master := [(Sum.inr 1356, (1 / 1))]

def nodeValue1357 : Sparse Master := [(Sum.inr 1357, (1 / 1))]

def nodeValue1358 : Sparse Master := [(Sum.inr 1358, (1 / 1))]

def nodeValue1359 : Sparse Master := [(Sum.inr 1359, (1 / 1))]

def nodeValue1360 : Sparse Master := [(Sum.inr 1360, (1 / 1))]

def nodeValue1361 : Sparse Master := [(Sum.inr 1361, (1 / 1))]

def nodeValue1362 : Sparse Master := [(Sum.inr 1362, (1 / 1))]

def nodeValue1363 : Sparse Master := [(Sum.inr 1363, (1 / 1))]

def nodeValue1364 : Sparse Master := [(Sum.inr 1364, (1 / 1))]

def nodeValue1366 : Sparse Master := [(Sum.inr 1366, (1 / 1))]

def nodeValue1367 : Sparse Master := [(Sum.inr 1367, (1 / 1))]

def nodeValue1368 : Sparse Master := [(Sum.inr 1368, (1 / 1))]

def nodeValue1369 : Sparse Master := [(Sum.inr 1369, (1 / 1))]

def nodeValue1370 : Sparse Master := [(Sum.inr 1370, (1 / 1))]

def nodeValue1371 : Sparse Master := [(Sum.inr 1371, (1 / 1))]

def nodeValue1372 : Sparse Master := [(Sum.inr 1372, (1 / 1))]

def nodeValue1373 : Sparse Master := [(Sum.inr 1373, (1 / 1))]

def nodeValue1374 : Sparse Master := [(Sum.inr 1374, (1 / 1))]

def nodeValue1375 : Sparse Master := [(Sum.inr 1375, (1 / 1))]

def nodeValue1378 : Sparse Master := [(Sum.inr 1378, (1 / 1))]

def nodeValue1379 : Sparse Master := []

def nodeValue1380 : Sparse Master := [(Sum.inr 1380, (1 / 1))]

def nodeValue1381 : Sparse Master := []

def nodeValue1382 : Sparse Master := [(Sum.inr 1382, (1 / 1))]

def nodeValue1383 : Sparse Master := [(Sum.inr 1383, (1 / 1))]

def nodeValue1384 : Sparse Master := [(Sum.inr 1384, (1 / 1))]

def nodeValue1385 : Sparse Master := [(Sum.inr 1385, (1 / 1))]

def nodeValue1386 : Sparse Master := []

def nodeValue1387 : Sparse Master := [(Sum.inr 1387, (1 / 1))]

def nodeValue1388 : Sparse Master := [(Sum.inr 1388, (1 / 1))]

def nodeValue1389 : Sparse Master := [(Sum.inr 1389, (1 / 1))]

def nodeValue1390 : Sparse Master := [(Sum.inr 1390, (1 / 1))]

def nodeValue1391 : Sparse Master := [(Sum.inr 1391, (1 / 1))]

def nodeValue1392 : Sparse Master := [(Sum.inr 1392, (1 / 1))]

def nodeValue1393 : Sparse Master := []

def nodeValue1394 : Sparse Master := [(Sum.inr 1394, (1 / 1))]

def nodeValue1395 : Sparse Master := [(Sum.inl 0, (-49 / 4320)), (Sum.inl 5, (-1 / 54)), (Sum.inl 6, (-1 / 864)), (Sum.inl 2, (11 / 432)), (Sum.inl 7, (1 / 54)), (Sum.inl 35, (1 / 27)), (Sum.inl 8, (1 / 27)), (Sum.inl 3, (1 / 27)), (Sum.inl 52, (2 / 27)), (Sum.inl 1, (7 / 216))]

def nodeValue1396 : Sparse Master := [(Sum.inl 0, (-41 / 4320)), (Sum.inl 5, (-1 / 216)), (Sum.inl 6, (-1 / 864)), (Sum.inl 2, (-11 / 864)), (Sum.inl 7, (1 / 27)), (Sum.inl 35, (1 / 18)), (Sum.inl 8, (1 / 54)), (Sum.inl 3, (1 / 54)), (Sum.inl 52, (1 / 54)), (Sum.inl 228, (-1 / 18)), (Sum.inl 11, (1 / 54)), (Sum.inl 26, (1 / 54)), (Sum.inl 1, (-5 / 864))]

def nodeValue1397 : Sparse Master := [(Sum.inl 0, (-13 / 1440)), (Sum.inl 5, (1 / 108)), (Sum.inl 6, (1 / 96)), (Sum.inl 2, (1 / 108)), (Sum.inl 52, (-1 / 54)), (Sum.inl 1, (-1 / 144))]

def nodeValue1398 : Sparse Master := []

def nodeValue1399 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 5, (1 / 216)), (Sum.inl 6, (5 / 432)), (Sum.inl 2, (5 / 432)), (Sum.inl 35, (-1 / 54)), (Sum.inl 11, (-1 / 54)), (Sum.inl 1, (-1 / 144))]

def nodeValue1400 : Sparse Master := [(Sum.inr 1400, (1 / 1))]

def nodeValue1401 : Sparse Master := [(Sum.inl 0, (-13 / 1440)), (Sum.inl 5, (-1 / 24)), (Sum.inl 2, (-1 / 216)), (Sum.inl 7, (-1 / 54)), (Sum.inl 35, (-1 / 54)), (Sum.inl 8, (-1 / 54)), (Sum.inl 1, (-5 / 864))]

def nodeValue1403 : Sparse Master := [(Sum.inr 1403, (1 / 1))]

def nodeValue1404 : Sparse Master := [(Sum.inr 1404, (1 / 1))]

def nodeValue1405 : Sparse Master := []

def nodeValue1406 : Sparse Master := [(Sum.inr 1406, (1 / 1))]

def nodeValue1407 : Sparse Master := [(Sum.inr 1407, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue1408 : Sparse Master := [(Sum.inr 1408, (1 / 1))]

def nodeValue1409 : Sparse Master := [(Sum.inl 0, (-37 / 4320)), (Sum.inl 5, (-2 / 27)), (Sum.inl 6, (11 / 864)), (Sum.inl 2, (11 / 432)), (Sum.inl 7, (1 / 54)), (Sum.inl 35, (1 / 27)), (Sum.inl 8, (1 / 27)), (Sum.inl 3, (1 / 27)), (Sum.inl 52, (2 / 27)), (Sum.inl 1, (1 / 216))]

def nodeValue1410 : Sparse Master := [(Sum.inl 0, (-1 / 160)), (Sum.inl 5, (1 / 54)), (Sum.inl 6, (-1 / 288)), (Sum.inl 2, (-7 / 432)), (Sum.inl 7, (-1 / 54)), (Sum.inl 35, (-1 / 27)), (Sum.inl 3, (-1 / 27)), (Sum.inl 52, (-1 / 27)), (Sum.inl 1, (-1 / 216))]

def nodeValue1411 : Sparse Master := [(Sum.inl 0, (-17 / 2160)), (Sum.inl 5, (1 / 36)), (Sum.inl 6, (-1 / 216)), (Sum.inl 2, (-1 / 54)), (Sum.inl 8, (-1 / 54)), (Sum.inl 52, (-1 / 54)), (Sum.inl 1, (-1 / 48))]

def nodeValue1412 : Sparse Master := [(Sum.inl 0, (-31 / 4320)), (Sum.inl 5, (1 / 108)), (Sum.inl 6, (-1 / 432)), (Sum.inl 2, (-5 / 864)), (Sum.inl 7, (-1 / 54)), (Sum.inl 35, (-1 / 27)), (Sum.inl 3, (-1 / 54)), (Sum.inl 228, (1 / 18)), (Sum.inl 11, (-1 / 54)), (Sum.inl 26, (-1 / 54)), (Sum.inl 1, (1 / 216))]

def nodeValue1413 : Sparse Master := [(Sum.inl 0, (-7 / 1080)), (Sum.inl 5, (-1 / 108)), (Sum.inl 6, (1 / 108)), (Sum.inl 2, (1 / 108)), (Sum.inl 52, (1 / 27)), (Sum.inl 1, (1 / 216))]

def nodeValue1414 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 5, (5 / 216)), (Sum.inl 6, (-5 / 864)), (Sum.inl 2, (1 / 108)), (Sum.inl 7, (-1 / 54)), (Sum.inl 35, (-1 / 54)), (Sum.inl 1, (7 / 864))]

def nodeValue1415 : Sparse Master := [(Sum.inr 1415, (1 / 1))]

def nodeValue1416 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 5, (-1 / 108)), (Sum.inl 6, (5 / 432)), (Sum.inl 2, (1 / 72)), (Sum.inl 1, (1 / 108))]

def nodeValue1417 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 6, (1 / 144)), (Sum.inl 2, (1 / 216)), (Sum.inl 35, (1 / 27)), (Sum.inl 11, (1 / 27)), (Sum.inl 1, (1 / 216))]

def nodeValue1418 : Sparse Master := [(Sum.inr 1418, (1 / 1))]

def nodeValue1419 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 5, (-1 / 27)), (Sum.inl 2, (1 / 108)), (Sum.inl 7, (1 / 27)), (Sum.inl 35, (1 / 27)), (Sum.inl 1, (7 / 432))]

def nodeValue1420 : Sparse Master := [(Sum.inl 0, (-1 / 120)), (Sum.inl 5, (-5 / 108)), (Sum.inl 8, (1 / 27)), (Sum.inl 1, (-1 / 216))]

def nodeValue1421 : Sparse Master := [(Sum.inr 1421, (1 / 1))]

def nodeValue1422 : Sparse Master := [(Sum.inr 1422, (1 / 1))]

def nodeValue1423 : Sparse Master := [(Sum.inr 1423, (1 / 1))]

def nodeValue1424 : Sparse Master := [(Sum.inr 1424, (1 / 1))]

def nodeValue1425 : Sparse Master := [(Sum.inr 1425, (1 / 1))]

def nodeValue1427 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 5, (1 / 54)), (Sum.inl 6, (-1 / 216)), (Sum.inl 2, (1 / 108)), (Sum.inl 35, (-1 / 27)), (Sum.inl 11, (-1 / 54)), (Sum.inl 26, (-1 / 54)), (Sum.inl 1, (-1 / 144))]

def nodeValue1433 : Sparse Master := [(Sum.inr 1433, (1 / 1))]

def nodeValue1435 : Sparse Master := [(Sum.inr 1435, (1 / 1))]

def nodeValue1436 : Sparse Master := [(Sum.inr 1436, (1 / 1))]

def nodeValue1437 : Sparse Master := [(Sum.inr 1437, (1 / 1))]

def nodeValue1438 : Sparse Master := [(Sum.inr 1438, (1 / 1))]

def nodeValue1440 : Sparse Master := [(Sum.inr 1440, (1 / 1))]

def nodeValue1441 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 5, (-1 / 216)), (Sum.inl 6, (1 / 432)), (Sum.inl 2, (13 / 864)), (Sum.inl 35, (-1 / 54)), (Sum.inl 3, (-1 / 54)), (Sum.inl 52, (-1 / 27)), (Sum.inl 1, (1 / 96))]

def nodeValue1442 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 5, (1 / 108)), (Sum.inl 6, (-1 / 432)), (Sum.inl 2, (1 / 432)), (Sum.inl 35, (1 / 27)), (Sum.inl 3, (1 / 27)), (Sum.inl 52, (1 / 27)), (Sum.inl 1, (5 / 432))]

def nodeValue1443 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 6, (-1 / 432)), (Sum.inl 2, (1 / 108)), (Sum.inl 52, (1 / 27)), (Sum.inl 1, (1 / 108))]

def nodeValue1444 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 5, (1 / 54)), (Sum.inl 6, (-1 / 432)), (Sum.inl 2, (-1 / 108)), (Sum.inl 228, (-1 / 9))]

def nodeValue1445 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 6, (1 / 144)), (Sum.inl 2, (1 / 72)), (Sum.inl 52, (-1 / 9)), (Sum.inl 1, (1 / 72))]

def nodeValue1446 : Sparse Master := []

def nodeValue1447 : Sparse Master := []

def nodeValue1448 : Sparse Master := []

def nodeValue1449 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 5, (1 / 108)), (Sum.inl 6, (-1 / 216)), (Sum.inl 35, (1 / 27)), (Sum.inl 11, (1 / 27)), (Sum.inl 26, (1 / 27)), (Sum.inl 1, (1 / 432))]

def nodeValue1450 : Sparse Master := []

def nodeValue1451 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 5, (1 / 108)), (Sum.inl 2, (-5 / 108)), (Sum.inl 35, (1 / 27)), (Sum.inl 1, (-1 / 432))]

def nodeValue1452 : Sparse Master := []

def nodeValue1453 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 6, (1 / 72)), (Sum.inl 2, (1 / 72)), (Sum.inl 11, (-1 / 9)), (Sum.inl 1, (1 / 144))]

def nodeValue1454 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 5, (-1 / 36)), (Sum.inl 2, (-1 / 36)), (Sum.inl 35, (-1 / 9)), (Sum.inl 1, (1 / 144))]

def nodeValue1455 : Sparse Master := []

def nodeValue1456 : Sparse Master := []

def nodeValue1457 : Sparse Master := [(Sum.inr 1457, (1 / 1))]

def nodeValue1458 : Sparse Master := [(Sum.inr 1458, (1 / 1))]

def nodeValue1459 : Sparse Master := [(Sum.inr 1459, (1 / 1))]

def nodeValue1460 : Sparse Master := [(Sum.inr 1460, (1 / 1))]

def nodeValue1461 : Sparse Master := [(Sum.inr 1461, (1 / 1))]

def nodeValue1462 : Sparse Master := [(Sum.inr 1462, (1 / 1))]

def nodeValue1463 : Sparse Master := [(Sum.inr 1463, (1 / 1))]

def nodeValue1464 : Sparse Master := [(Sum.inr 1464, (1 / 1))]

def nodeValue1465 : Sparse Master := [(Sum.inr 1465, (1 / 1))]

def nodeValue1466 : Sparse Master := [(Sum.inr 1466, (1 / 1))]

def nodeValue1467 : Sparse Master := [(Sum.inr 1467, (1 / 1))]

def nodeValue1468 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 5, (1 / 36)), (Sum.inl 6, (-1 / 144)), (Sum.inl 2, (-1 / 72)), (Sum.inl 35, (-1 / 54)), (Sum.inl 82, (-1 / 54)), (Sum.inl 3, (-1 / 54)), (Sum.inl 13, (-1 / 54)), (Sum.inl 128, (-1 / 54)), (Sum.inl 52, (-1 / 54)), (Sum.inl 201, (1 / 18))]

def nodeValue1470 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 5, (-1 / 54)), (Sum.inl 6, (-1 / 216)), (Sum.inl 2, (-1 / 108)), (Sum.inl 7, (-1 / 54)), (Sum.inl 35, (-1 / 27)), (Sum.inl 82, (-1 / 54)), (Sum.inl 199, (1 / 18)), (Sum.inl 1, (1 / 432))]

def nodeValue1471 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 5, (-1 / 27)), (Sum.inl 6, (1 / 108)), (Sum.inl 2, (1 / 108)), (Sum.inl 35, (1 / 27)), (Sum.inl 82, (1 / 27)), (Sum.inl 1, (1 / 144))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue1473 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 5, (-1 / 54)), (Sum.inl 6, (-1 / 432)), (Sum.inl 2, (-1 / 216)), (Sum.inl 201, (-1 / 9)), (Sum.inl 1, (1 / 216))]

def nodeValue1474 : Sparse Master := [(Sum.inr 1474, (1 / 1))]

def nodeValue1475 : Sparse Master := [(Sum.inl 0, (-7 / 720)), (Sum.inl 5, (-1 / 36)), (Sum.inl 6, (1 / 144)), (Sum.inl 2, (11 / 432)), (Sum.inl 35, (1 / 54)), (Sum.inl 82, (1 / 54)), (Sum.inl 8, (1 / 54)), (Sum.inl 3, (1 / 54)), (Sum.inl 13, (1 / 54)), (Sum.inl 128, (1 / 27)), (Sum.inl 52, (2 / 27)), (Sum.inl 201, (-1 / 18)), (Sum.inl 1, (1 / 48))]

def nodeValue1477 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 5, (1 / 36)), (Sum.inl 6, (-1 / 72)), (Sum.inl 2, (-1 / 27)), (Sum.inl 7, (1 / 27)), (Sum.inl 35, (2 / 27)), (Sum.inl 82, (1 / 27)), (Sum.inl 199, (-1 / 18)), (Sum.inl 1, (-7 / 432))]

def nodeValue1478 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 5, (5 / 216)), (Sum.inl 6, (1 / 96)), (Sum.inl 2, (1 / 108)), (Sum.inl 35, (-1 / 54)), (Sum.inl 82, (-1 / 54)), (Sum.inl 1, (-7 / 864))]

def nodeValue1479 : Sparse Master := [(Sum.inl 0, (-13 / 1440)), (Sum.inl 5, (-11 / 216)), (Sum.inl 6, (1 / 864)), (Sum.inl 2, (1 / 432)), (Sum.inl 8, (-1 / 54)), (Sum.inl 201, (1 / 18))]

def nodeValue1480 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 5, (1 / 36)), (Sum.inl 6, (-1 / 108)), (Sum.inl 2, (-1 / 48)), (Sum.inl 128, (-1 / 54)), (Sum.inl 52, (-1 / 27)), (Sum.inl 1, (-1 / 72))]

def nodeValue1482 : Sparse Master := []

def nodeValue1483 : Sparse Master := []

def nodeValue1484 : Sparse Master := []

def nodeValue1485 : Sparse Master := []

def nodeValue1486 : Sparse Master := []

def nodeValue1488 : Sparse Master := [(Sum.inr 1488, (1 / 1))]

def nodeValue1489 : Sparse Master := [(Sum.inr 1489, (1 / 1))]

def nodeValue1490 : Sparse Master := [(Sum.inr 1490, (1 / 1))]

def nodeValue1491 : Sparse Master := [(Sum.inr 1491, (1 / 1))]

def nodeValue1492 : Sparse Master := [(Sum.inr 1492, (1 / 1))]

def nodeValue1493 : Sparse Master := [(Sum.inr 1493, (1 / 1))]

def nodeValue1494 : Sparse Master := [(Sum.inr 1494, (1 / 1))]

def nodeValue1495 : Sparse Master := [(Sum.inr 1495, (1 / 1))]

def nodeValue1496 : Sparse Master := [(Sum.inr 1496, (1 / 1))]

def nodeValue1497 : Sparse Master := [(Sum.inr 1497, (1 / 1))]

def nodeValue1498 : Sparse Master := [(Sum.inr 1498, (1 / 1))]

def nodeValue1499 : Sparse Master := [(Sum.inr 1499, (1 / 1))]

def nodeValue1500 : Sparse Master := [(Sum.inr 1500, (1 / 1))]

def nodeValue1501 : Sparse Master := [(Sum.inr 1501, (1 / 1))]

def nodeValue1502 : Sparse Master := [(Sum.inr 1502, (1 / 1))]

def nodeValue1503 : Sparse Master := [(Sum.inr 1503, (1 / 1))]

def nodeValue1504 : Sparse Master := [(Sum.inr 1504, (1 / 1))]

def nodeValue1505 : Sparse Master := [(Sum.inr 1505, (1 / 1))]

def nodeValue1506 : Sparse Master := [(Sum.inr 1506, (1 / 1))]

def nodeValue1507 : Sparse Master := [(Sum.inr 1507, (1 / 1))]

def nodeValue1508 : Sparse Master := [(Sum.inr 1508, (1 / 1))]

def nodeValue1509 : Sparse Master := [(Sum.inr 1509, (1 / 1))]

def nodeValue1510 : Sparse Master := [(Sum.inr 1510, (1 / 1))]

def nodeValue1511 : Sparse Master := [(Sum.inr 1511, (1 / 1))]

def nodeValue1512 : Sparse Master := [(Sum.inr 1512, (1 / 1))]

def nodeValue1513 : Sparse Master := [(Sum.inr 1513, (1 / 1))]

def nodeValue1514 : Sparse Master := [(Sum.inr 1514, (1 / 1))]

def nodeValue1515 : Sparse Master := [(Sum.inr 1515, (1 / 1))]

def nodeValue1516 : Sparse Master := [(Sum.inr 1516, (1 / 1))]

def nodeValue1517 : Sparse Master := [(Sum.inr 1517, (1 / 1))]

def nodeValue1518 : Sparse Master := [(Sum.inr 1518, (1 / 1))]

def nodeValue1519 : Sparse Master := [(Sum.inr 1519, (1 / 1))]

def nodeValue1520 : Sparse Master := [(Sum.inr 1520, (1 / 1))]

def nodeValue1521 : Sparse Master := [(Sum.inr 1521, (1 / 1))]

def nodeValue1522 : Sparse Master := [(Sum.inr 1522, (1 / 1))]

def nodeValue1523 : Sparse Master := [(Sum.inr 1523, (1 / 1))]

def nodeValue1524 : Sparse Master := [(Sum.inr 1524, (1 / 1))]

def nodeValue1525 : Sparse Master := [(Sum.inr 1525, (1 / 1))]

def nodeValue1526 : Sparse Master := [(Sum.inr 1526, (1 / 1))]

def nodeValue1527 : Sparse Master := [(Sum.inr 1527, (1 / 1))]

def nodeValue1528 : Sparse Master := [(Sum.inr 1528, (1 / 1))]

def nodeValue1529 : Sparse Master := [(Sum.inr 1529, (1 / 1))]

def nodeValue1530 : Sparse Master := [(Sum.inr 1530, (1 / 1))]

def nodeValue1531 : Sparse Master := [(Sum.inr 1531, (1 / 1))]

def nodeValue1532 : Sparse Master := [(Sum.inr 1532, (1 / 1))]

def nodeValue1533 : Sparse Master := [(Sum.inr 1533, (1 / 1))]

def nodeValue1534 : Sparse Master := [(Sum.inr 1534, (1 / 1))]

def nodeValue1535 : Sparse Master := [(Sum.inr 1535, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue1536 : Sparse Master := [(Sum.inr 1536, (1 / 1))]

def nodeValue1537 : Sparse Master := [(Sum.inr 1537, (1 / 1))]

def nodeValue1538 : Sparse Master := [(Sum.inr 1538, (1 / 1))]

def nodeValue1539 : Sparse Master := [(Sum.inr 1539, (1 / 1))]

def nodeValue1540 : Sparse Master := [(Sum.inr 1540, (1 / 1))]

def nodeValue1541 : Sparse Master := [(Sum.inr 1541, (1 / 1))]

def nodeValue1550 : Sparse Master := [(Sum.inr 1550, (1 / 1))]

def nodeValue1552 : Sparse Master := [(Sum.inr 1552, (1 / 1))]

def nodeValue1553 : Sparse Master := [(Sum.inr 1553, (1 / 1))]

def nodeValue1554 : Sparse Master := [(Sum.inr 1554, (1 / 1))]

def nodeValue1555 : Sparse Master := [(Sum.inr 1555, (1 / 1))]

def nodeValue1556 : Sparse Master := [(Sum.inr 1556, (1 / 1))]

def nodeValue1557 : Sparse Master := []

def nodeValue1558 : Sparse Master := [(Sum.inr 1558, (1 / 1))]

def nodeValue1559 : Sparse Master := [(Sum.inr 1559, (1 / 1))]

def nodeValue1561 : Sparse Master := [(Sum.inr 1561, (1 / 1))]

def nodeValue1562 : Sparse Master := [(Sum.inr 1562, (1 / 1))]

def nodeValue1563 : Sparse Master := [(Sum.inr 1563, (1 / 1))]

def nodeValue1565 : Sparse Master := [(Sum.inr 1565, (1 / 1))]

def nodeValue1566 : Sparse Master := [(Sum.inr 1566, (1 / 1))]

def nodeValue1567 : Sparse Master := [(Sum.inr 1567, (1 / 1))]

def nodeValue1568 : Sparse Master := [(Sum.inr 1568, (1 / 1))]

def nodeValue1569 : Sparse Master := [(Sum.inr 1569, (1 / 1))]

def nodeValue1570 : Sparse Master := [(Sum.inr 1570, (1 / 1))]

def nodeValue1573 : Sparse Master := [(Sum.inr 1573, (1 / 1))]

def nodeValue1574 : Sparse Master := []

def nodeValue1575 : Sparse Master := [(Sum.inr 1575, (1 / 1))]

def nodeValue1576 : Sparse Master := []

def nodeValue1577 : Sparse Master := [(Sum.inr 1577, (1 / 1))]

def nodeValue1578 : Sparse Master := [(Sum.inr 1578, (1 / 1))]

def nodeValue1579 : Sparse Master := []

def nodeValue1586 : Sparse Master := [(Sum.inr 1586, (1 / 1))]

def nodeValue1587 : Sparse Master := [(Sum.inr 1587, (1 / 1))]

def nodeValue1588 : Sparse Master := [(Sum.inr 1588, (1 / 1))]

def nodeValue1589 : Sparse Master := [(Sum.inr 1589, (1 / 1))]

def nodeValue1590 : Sparse Master := [(Sum.inr 1590, (1 / 1))]

def nodeValue1591 : Sparse Master := [(Sum.inr 1591, (1 / 1))]

def nodeValue1592 : Sparse Master := []

def nodeValue1593 : Sparse Master := [(Sum.inr 1593, (1 / 1))]

def nodeValue1594 : Sparse Master := [(Sum.inr 1594, (1 / 1))]

def nodeValue1595 : Sparse Master := []

def nodeValue1596 : Sparse Master := []

def nodeValue1597 : Sparse Master := [(Sum.inr 1597, (1 / 1))]

def nodeValue1598 : Sparse Master := []

def nodeValue1599 : Sparse Master := [(Sum.inr 1599, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue1600 : Sparse Master := [(Sum.inr 1600, (1 / 1))]

def nodeValue1601 : Sparse Master := [(Sum.inr 1601, (1 / 1))]

def nodeValue1602 : Sparse Master := [(Sum.inr 1602, (1 / 1))]

def nodeValue1603 : Sparse Master := [(Sum.inr 1603, (1 / 1))]

def nodeValue1604 : Sparse Master := [(Sum.inr 1604, (1 / 1))]

def nodeValue1605 : Sparse Master := [(Sum.inr 1605, (1 / 1))]

def nodeValue1606 : Sparse Master := [(Sum.inr 1606, (1 / 1))]

def nodeValue1607 : Sparse Master := [(Sum.inr 1607, (1 / 1))]

def nodeValue1608 : Sparse Master := [(Sum.inr 1608, (1 / 1))]

def nodeValue1609 : Sparse Master := [(Sum.inr 1609, (1 / 1))]

def nodeValue1610 : Sparse Master := [(Sum.inr 1610, (1 / 1))]

def nodeValue1611 : Sparse Master := [(Sum.inr 1611, (1 / 1))]

def nodeValue1612 : Sparse Master := [(Sum.inr 1612, (1 / 1))]

def nodeValue1613 : Sparse Master := [(Sum.inr 1613, (1 / 1))]

def nodeValue1615 : Sparse Master := [(Sum.inr 1615, (1 / 1))]

def nodeValue1616 : Sparse Master := [(Sum.inr 1616, (1 / 1))]

def nodeValue1617 : Sparse Master := [(Sum.inr 1617, (1 / 1))]

def nodeValue1618 : Sparse Master := [(Sum.inr 1618, (1 / 1))]

def nodeValue1619 : Sparse Master := [(Sum.inr 1619, (1 / 1))]

def nodeValue1620 : Sparse Master := [(Sum.inr 1620, (1 / 1))]

def nodeValue1623 : Sparse Master := [(Sum.inr 1623, (1 / 1))]

def nodeValue1624 : Sparse Master := [(Sum.inr 1624, (1 / 1))]

def nodeValue1626 : Sparse Master := [(Sum.inr 1626, (1 / 1))]

def nodeValue1627 : Sparse Master := [(Sum.inr 1627, (1 / 1))]

def nodeValue1628 : Sparse Master := [(Sum.inr 1628, (1 / 1))]

def nodeValue1629 : Sparse Master := [(Sum.inr 1629, (1 / 1))]

def nodeValue1630 : Sparse Master := [(Sum.inr 1630, (1 / 1))]

def nodeValue1632 : Sparse Master := [(Sum.inr 1632, (1 / 1))]

def nodeValue1633 : Sparse Master := [(Sum.inr 1633, (1 / 1))]

def nodeValue1634 : Sparse Master := [(Sum.inr 1634, (1 / 1))]

def nodeValue1635 : Sparse Master := [(Sum.inr 1635, (1 / 1))]

def nodeValue1636 : Sparse Master := [(Sum.inr 1636, (1 / 1))]

def nodeValue1637 : Sparse Master := [(Sum.inr 1637, (1 / 1))]

def nodeValue1638 : Sparse Master := [(Sum.inr 1638, (1 / 1))]

def nodeValue1639 : Sparse Master := [(Sum.inr 1639, (1 / 1))]

def nodeValue1640 : Sparse Master := [(Sum.inr 1640, (1 / 1))]

def nodeValue1641 : Sparse Master := [(Sum.inr 1641, (1 / 1))]

def nodeValue1642 : Sparse Master := [(Sum.inr 1642, (1 / 1))]

def nodeValue1643 : Sparse Master := [(Sum.inr 1643, (1 / 1))]

def nodeValue1644 : Sparse Master := [(Sum.inr 1644, (1 / 1))]

def nodeValue1645 : Sparse Master := [(Sum.inr 1645, (1 / 1))]

def nodeValue1646 : Sparse Master := [(Sum.inr 1646, (1 / 1))]

def nodeValue1647 : Sparse Master := [(Sum.inr 1647, (1 / 1))]

def nodeValue1648 : Sparse Master := [(Sum.inr 1648, (1 / 1))]

def nodeValue1649 : Sparse Master := [(Sum.inr 1649, (1 / 1))]

def nodeValue1650 : Sparse Master := [(Sum.inr 1650, (1 / 1))]

def nodeValue1651 : Sparse Master := [(Sum.inr 1651, (1 / 1))]

def nodeValue1652 : Sparse Master := [(Sum.inr 1652, (1 / 1))]

def nodeValue1653 : Sparse Master := [(Sum.inr 1653, (1 / 1))]

def nodeValue1654 : Sparse Master := [(Sum.inr 1654, (1 / 1))]

def nodeValue1655 : Sparse Master := [(Sum.inr 1655, (1 / 1))]

def nodeValue1656 : Sparse Master := [(Sum.inr 1656, (1 / 1))]

def nodeValue1657 : Sparse Master := [(Sum.inr 1657, (1 / 1))]

def nodeValue1658 : Sparse Master := [(Sum.inr 1658, (1 / 1))]

def nodeValue1659 : Sparse Master := [(Sum.inr 1659, (1 / 1))]

def nodeValue1660 : Sparse Master := [(Sum.inr 1660, (1 / 1))]

def nodeValue1661 : Sparse Master := [(Sum.inr 1661, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue1664 : Sparse Master := [(Sum.inr 1664, (1 / 1))]

def nodeValue1666 : Sparse Master := [(Sum.inr 1666, (1 / 1))]

def nodeValue1667 : Sparse Master := [(Sum.inr 1667, (1 / 1))]

def nodeValue1668 : Sparse Master := [(Sum.inr 1668, (1 / 1))]

def nodeValue1669 : Sparse Master := [(Sum.inr 1669, (1 / 1))]

def nodeValue1670 : Sparse Master := [(Sum.inr 1670, (1 / 1))]

def nodeValue1672 : Sparse Master := [(Sum.inr 1672, (1 / 1))]

def nodeValue1673 : Sparse Master := [(Sum.inr 1673, (1 / 1))]

def nodeValue1674 : Sparse Master := [(Sum.inr 1674, (1 / 1))]

def nodeValue1675 : Sparse Master := [(Sum.inr 1675, (1 / 1))]

def nodeValue1676 : Sparse Master := [(Sum.inr 1676, (1 / 1))]

def nodeValue1677 : Sparse Master := [(Sum.inr 1677, (1 / 1))]

def nodeValue1678 : Sparse Master := [(Sum.inr 1678, (1 / 1))]

def nodeValue1679 : Sparse Master := [(Sum.inr 1679, (1 / 1))]

def nodeValue1680 : Sparse Master := [(Sum.inr 1680, (1 / 1))]

def nodeValue1681 : Sparse Master := [(Sum.inr 1681, (1 / 1))]

def nodeValue1682 : Sparse Master := [(Sum.inr 1682, (1 / 1))]

def nodeValue1683 : Sparse Master := [(Sum.inr 1683, (1 / 1))]

def nodeValue1684 : Sparse Master := [(Sum.inr 1684, (1 / 1))]

def nodeValue1685 : Sparse Master := [(Sum.inr 1685, (1 / 1))]

def nodeValue1686 : Sparse Master := [(Sum.inr 1686, (1 / 1))]

def nodeValue1687 : Sparse Master := [(Sum.inr 1687, (1 / 1))]

def nodeValue1688 : Sparse Master := [(Sum.inr 1688, (1 / 1))]

def nodeValue1689 : Sparse Master := [(Sum.inr 1689, (1 / 1))]

def nodeValue1690 : Sparse Master := [(Sum.inr 1690, (1 / 1))]

def nodeValue1691 : Sparse Master := [(Sum.inr 1691, (1 / 1))]

def nodeValue1692 : Sparse Master := [(Sum.inr 1692, (1 / 1))]

def nodeValue1693 : Sparse Master := [(Sum.inr 1693, (1 / 1))]

def nodeValue1694 : Sparse Master := [(Sum.inr 1694, (1 / 1))]

def nodeValue1695 : Sparse Master := [(Sum.inr 1695, (1 / 1))]

def nodeValue1697 : Sparse Master := [(Sum.inr 1697, (1 / 1))]

def nodeValue1698 : Sparse Master := []

def nodeValue1699 : Sparse Master := [(Sum.inr 1699, (1 / 1))]

def nodeValue1700 : Sparse Master := [(Sum.inr 1700, (1 / 1))]

def nodeValue1703 : Sparse Master := [(Sum.inr 1703, (1 / 1))]

def nodeValue1704 : Sparse Master := [(Sum.inr 1704, (1 / 1))]

def nodeValue1705 : Sparse Master := []

def nodeValue1706 : Sparse Master := [(Sum.inr 1706, (1 / 1))]

def nodeValue1707 : Sparse Master := [(Sum.inr 1707, (1 / 1))]

def nodeValue1708 : Sparse Master := [(Sum.inr 1708, (1 / 1))]

def nodeValue1709 : Sparse Master := [(Sum.inr 1709, (1 / 1))]

def nodeValue1710 : Sparse Master := [(Sum.inr 1710, (1 / 1))]

def nodeValue1711 : Sparse Master := [(Sum.inr 1711, (1 / 1))]

def nodeValue1712 : Sparse Master := [(Sum.inr 1712, (1 / 1))]

def nodeValue1713 : Sparse Master := [(Sum.inr 1713, (1 / 1))]

def nodeValue1714 : Sparse Master := [(Sum.inr 1714, (1 / 1))]

def nodeValue1715 : Sparse Master := [(Sum.inr 1715, (1 / 1))]

def nodeValue1716 : Sparse Master := [(Sum.inr 1716, (1 / 1))]

def nodeValue1720 : Sparse Master := [(Sum.inr 1720, (1 / 1))]

def nodeValue1721 : Sparse Master := [(Sum.inr 1721, (1 / 1))]

def nodeValue1722 : Sparse Master := [(Sum.inr 1722, (1 / 1))]

def nodeValue1723 : Sparse Master := [(Sum.inr 1723, (1 / 1))]

def nodeValue1724 : Sparse Master := [(Sum.inr 1724, (1 / 1))]

def nodeValue1725 : Sparse Master := [(Sum.inr 1725, (1 / 1))]

def nodeValue1726 : Sparse Master := []

def nodeValue1727 : Sparse Master := []

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue1728 : Sparse Master := [(Sum.inr 1728, (1 / 1))]

def nodeValue1729 : Sparse Master := [(Sum.inr 1729, (1 / 1))]

def nodeValue1730 : Sparse Master := []

def nodeValue1734 : Sparse Master := [(Sum.inr 1734, (1 / 1))]

def nodeValue1735 : Sparse Master := [(Sum.inr 1735, (1 / 1))]

def nodeValue1736 : Sparse Master := [(Sum.inr 1736, (1 / 1))]

def nodeValue1737 : Sparse Master := [(Sum.inr 1737, (1 / 1))]

def nodeValue1738 : Sparse Master := [(Sum.inr 1738, (1 / 1))]

def nodeValue1739 : Sparse Master := [(Sum.inr 1739, (1 / 1))]

def nodeValue1740 : Sparse Master := [(Sum.inr 1740, (1 / 1))]

def nodeValue1741 : Sparse Master := [(Sum.inr 1741, (1 / 1))]

def nodeValue1742 : Sparse Master := [(Sum.inr 1742, (1 / 1))]

def nodeValue1743 : Sparse Master := [(Sum.inr 1743, (1 / 1))]

def nodeValue1744 : Sparse Master := [(Sum.inr 1744, (1 / 1))]

def nodeValue1745 : Sparse Master := [(Sum.inr 1745, (1 / 1))]

def nodeValue1746 : Sparse Master := [(Sum.inr 1746, (1 / 1))]

def nodeValue1747 : Sparse Master := [(Sum.inr 1747, (1 / 1))]

def nodeValue1748 : Sparse Master := [(Sum.inr 1748, (1 / 1))]

def nodeValue1749 : Sparse Master := [(Sum.inr 1749, (1 / 1))]

def nodeValue1750 : Sparse Master := [(Sum.inr 1750, (1 / 1))]

def nodeValue1751 : Sparse Master := [(Sum.inr 1751, (1 / 1))]

def nodeValue1752 : Sparse Master := [(Sum.inr 1752, (1 / 1))]

def nodeValue1753 : Sparse Master := []

def nodeValue1754 : Sparse Master := []

def nodeValue1755 : Sparse Master := []

def nodeValue1756 : Sparse Master := [(Sum.inr 1756, (1 / 1))]

def nodeValue1757 : Sparse Master := [(Sum.inr 1757, (1 / 1))]

def nodeValue1758 : Sparse Master := []

def nodeValue1759 : Sparse Master := [(Sum.inr 1759, (1 / 1))]

def nodeValue1760 : Sparse Master := [(Sum.inr 1760, (1 / 1))]

def nodeValue1761 : Sparse Master := [(Sum.inr 1761, (1 / 1))]

def nodeValue1762 : Sparse Master := [(Sum.inr 1762, (1 / 1))]

def nodeValue1763 : Sparse Master := [(Sum.inr 1763, (1 / 1))]

def nodeValue1764 : Sparse Master := [(Sum.inr 1764, (1 / 1))]

def nodeValue1765 : Sparse Master := [(Sum.inr 1765, (1 / 1))]

def nodeValue1766 : Sparse Master := [(Sum.inr 1766, (1 / 1))]

def nodeValue1767 : Sparse Master := [(Sum.inr 1767, (1 / 1))]

def nodeValue1769 : Sparse Master := [(Sum.inr 1769, (1 / 1))]

def nodeValue1771 : Sparse Master := [(Sum.inr 1771, (1 / 1))]

def nodeValue1773 : Sparse Master := [(Sum.inr 1773, (1 / 1))]

def nodeValue1774 : Sparse Master := [(Sum.inr 1774, (1 / 1))]

def nodeValue1776 : Sparse Master := [(Sum.inr 1776, (1 / 1))]

def nodeValue1778 : Sparse Master := [(Sum.inr 1778, (1 / 1))]

def nodeValue1781 : Sparse Master := [(Sum.inr 1781, (1 / 1))]

def nodeValue1782 : Sparse Master := [(Sum.inr 1782, (1 / 1))]

def nodeValue1783 : Sparse Master := [(Sum.inr 1783, (1 / 1))]

def nodeValue1784 : Sparse Master := [(Sum.inr 1784, (1 / 1))]

def nodeValue1786 : Sparse Master := [(Sum.inr 1786, (1 / 1))]

def nodeValue1787 : Sparse Master := [(Sum.inr 1787, (1 / 1))]

def nodeValue1789 : Sparse Master := [(Sum.inr 1789, (1 / 1))]

def nodeValue1790 : Sparse Master := [(Sum.inr 1790, (1 / 1))]

def nodeValue1791 : Sparse Master := [(Sum.inr 1791, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue1792 : Sparse Master := [(Sum.inr 1792, (1 / 1))]

def nodeValue1793 : Sparse Master := [(Sum.inr 1793, (1 / 1))]

def nodeValue1794 : Sparse Master := [(Sum.inr 1794, (1 / 1))]

def nodeValue1795 : Sparse Master := [(Sum.inr 1795, (1 / 1))]

def nodeValue1796 : Sparse Master := [(Sum.inr 1796, (1 / 1))]

def nodeValue1797 : Sparse Master := [(Sum.inr 1797, (1 / 1))]

def nodeValue1798 : Sparse Master := [(Sum.inr 1798, (1 / 1))]

def nodeValue1799 : Sparse Master := [(Sum.inr 1799, (1 / 1))]

def nodeValue1801 : Sparse Master := [(Sum.inr 1801, (1 / 1))]

def nodeValue1802 : Sparse Master := [(Sum.inr 1802, (1 / 1))]

def nodeValue1803 : Sparse Master := [(Sum.inr 1803, (1 / 1))]

def nodeValue1804 : Sparse Master := [(Sum.inr 1804, (1 / 1))]

def nodeValue1805 : Sparse Master := [(Sum.inr 1805, (1 / 1))]

def nodeValue1806 : Sparse Master := [(Sum.inr 1806, (1 / 1))]

def nodeValue1807 : Sparse Master := [(Sum.inr 1807, (1 / 1))]

def nodeValue1808 : Sparse Master := [(Sum.inr 1808, (1 / 1))]

def nodeValue1809 : Sparse Master := [(Sum.inr 1809, (1 / 1))]

def nodeValue1810 : Sparse Master := [(Sum.inr 1810, (1 / 1))]

def nodeValue1811 : Sparse Master := [(Sum.inr 1811, (1 / 1))]

def nodeValue1812 : Sparse Master := [(Sum.inr 1812, (1 / 1))]

def nodeValue1813 : Sparse Master := [(Sum.inr 1813, (1 / 1))]

def nodeValue1814 : Sparse Master := [(Sum.inr 1814, (1 / 1))]

def nodeValue1815 : Sparse Master := [(Sum.inr 1815, (1 / 1))]

def nodeValue1816 : Sparse Master := [(Sum.inr 1816, (1 / 1))]

def nodeValue1817 : Sparse Master := [(Sum.inr 1817, (1 / 1))]

def nodeValue1818 : Sparse Master := [(Sum.inr 1818, (1 / 1))]

def nodeValue1819 : Sparse Master := [(Sum.inr 1819, (1 / 1))]

def nodeValue1820 : Sparse Master := [(Sum.inr 1820, (1 / 1))]

def nodeValue1821 : Sparse Master := [(Sum.inr 1821, (1 / 1))]

def nodeValue1822 : Sparse Master := [(Sum.inr 1822, (1 / 1))]

def nodeValue1823 : Sparse Master := [(Sum.inr 1823, (1 / 1))]

def nodeValue1824 : Sparse Master := [(Sum.inr 1824, (1 / 1))]

def nodeValue1825 : Sparse Master := [(Sum.inr 1825, (1 / 1))]

def nodeValue1826 : Sparse Master := [(Sum.inr 1826, (1 / 1))]

def nodeValue1827 : Sparse Master := [(Sum.inr 1827, (1 / 1))]

def nodeValue1828 : Sparse Master := [(Sum.inr 1828, (1 / 1))]

def nodeValue1829 : Sparse Master := [(Sum.inr 1829, (1 / 1))]

def nodeValue1830 : Sparse Master := [(Sum.inr 1830, (1 / 1))]

def nodeValue1831 : Sparse Master := [(Sum.inr 1831, (1 / 1))]

def nodeValue1832 : Sparse Master := [(Sum.inr 1832, (1 / 1))]

def nodeValue1833 : Sparse Master := [(Sum.inr 1833, (1 / 1))]

def nodeValue1835 : Sparse Master := [(Sum.inr 1835, (1 / 1))]

def nodeValue1836 : Sparse Master := [(Sum.inr 1836, (1 / 1))]

def nodeValue1837 : Sparse Master := [(Sum.inr 1837, (1 / 1))]

def nodeValue1838 : Sparse Master := [(Sum.inr 1838, (1 / 1))]

def nodeValue1840 : Sparse Master := [(Sum.inr 1840, (1 / 1))]

def nodeValue1841 : Sparse Master := [(Sum.inr 1841, (1 / 1))]

def nodeValue1842 : Sparse Master := [(Sum.inr 1842, (1 / 1))]

def nodeValue1843 : Sparse Master := [(Sum.inr 1843, (1 / 1))]

def nodeValue1844 : Sparse Master := [(Sum.inr 1844, (1 / 1))]

def nodeValue1846 : Sparse Master := [(Sum.inr 1846, (1 / 1))]

def nodeValue1847 : Sparse Master := [(Sum.inr 1847, (1 / 1))]

def nodeValue1848 : Sparse Master := [(Sum.inr 1848, (1 / 1))]

def nodeValue1849 : Sparse Master := [(Sum.inr 1849, (1 / 1))]

def nodeValue1850 : Sparse Master := [(Sum.inr 1850, (1 / 1))]

def nodeValue1851 : Sparse Master := [(Sum.inr 1851, (1 / 1))]

def nodeValue1854 : Sparse Master := [(Sum.inr 1854, (1 / 1))]

def nodeValue1855 : Sparse Master := [(Sum.inr 1855, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue1857 : Sparse Master := [(Sum.inr 1857, (1 / 1))]

def nodeValue1858 : Sparse Master := [(Sum.inr 1858, (1 / 1))]

def nodeValue1860 : Sparse Master := [(Sum.inr 1860, (1 / 1))]

def nodeValue1861 : Sparse Master := [(Sum.inr 1861, (1 / 1))]

def nodeValue1863 : Sparse Master := [(Sum.inr 1863, (1 / 1))]

def nodeValue1864 : Sparse Master := [(Sum.inr 1864, (1 / 1))]

def nodeValue1867 : Sparse Master := [(Sum.inr 1867, (1 / 1))]

def nodeValue1870 : Sparse Master := [(Sum.inr 1870, (1 / 1))]

def nodeValue1871 : Sparse Master := [(Sum.inr 1871, (1 / 1))]

def nodeValue1873 : Sparse Master := [(Sum.inr 1873, (1 / 1))]

def nodeValue1874 : Sparse Master := [(Sum.inr 1874, (1 / 1))]

def nodeValue1875 : Sparse Master := [(Sum.inr 1875, (1 / 1))]

def nodeValue1876 : Sparse Master := [(Sum.inr 1876, (1 / 1))]

def nodeValue1877 : Sparse Master := [(Sum.inr 1877, (1 / 1))]

def nodeValue1878 : Sparse Master := [(Sum.inr 1878, (1 / 1))]

def nodeValue1879 : Sparse Master := [(Sum.inr 1879, (1 / 1))]

def nodeValue1880 : Sparse Master := [(Sum.inr 1880, (1 / 1))]

def nodeValue1881 : Sparse Master := [(Sum.inr 1881, (1 / 1))]

def nodeValue1882 : Sparse Master := [(Sum.inr 1882, (1 / 1))]

def nodeValue1883 : Sparse Master := [(Sum.inr 1883, (1 / 1))]

def nodeValue1884 : Sparse Master := [(Sum.inr 1884, (1 / 1))]

def nodeValue1886 : Sparse Master := [(Sum.inr 1886, (1 / 1))]

def nodeValue1887 : Sparse Master := [(Sum.inr 1887, (1 / 1))]

def nodeValue1888 : Sparse Master := [(Sum.inr 1888, (1 / 1))]

def nodeValue1889 : Sparse Master := [(Sum.inr 1889, (1 / 1))]

def nodeValue1891 : Sparse Master := [(Sum.inr 1891, (1 / 1))]

def nodeValue1892 : Sparse Master := [(Sum.inr 1892, (1 / 1))]

def nodeValue1893 : Sparse Master := [(Sum.inr 1893, (1 / 1))]

def nodeValue1894 : Sparse Master := [(Sum.inr 1894, (1 / 1))]

def nodeValue1896 : Sparse Master := [(Sum.inr 1896, (1 / 1))]

def nodeValue1897 : Sparse Master := [(Sum.inr 1897, (1 / 1))]

def nodeValue1898 : Sparse Master := [(Sum.inr 1898, (1 / 1))]

def nodeValue1900 : Sparse Master := [(Sum.inr 1900, (1 / 1))]

def nodeValue1901 : Sparse Master := [(Sum.inr 1901, (1 / 1))]

def nodeValue1902 : Sparse Master := [(Sum.inr 1902, (1 / 1))]

def nodeValue1903 : Sparse Master := [(Sum.inr 1903, (1 / 1))]

def nodeValue1904 : Sparse Master := [(Sum.inr 1904, (1 / 1))]

def nodeValue1905 : Sparse Master := [(Sum.inr 1905, (1 / 1))]

def nodeValue1906 : Sparse Master := [(Sum.inr 1906, (1 / 1))]

def nodeValue1907 : Sparse Master := [(Sum.inr 1907, (1 / 1))]

def nodeValue1908 : Sparse Master := []

def nodeValue1909 : Sparse Master := [(Sum.inr 1909, (1 / 1))]

def nodeValue1910 : Sparse Master := [(Sum.inr 1910, (1 / 1))]

def nodeValue1911 : Sparse Master := []

def nodeValue1912 : Sparse Master := []

def nodeValue1913 : Sparse Master := [(Sum.inr 1913, (1 / 1))]

def nodeValue1914 : Sparse Master := []

def nodeValue1915 : Sparse Master := [(Sum.inr 1915, (1 / 1))]

def nodeValue1916 : Sparse Master := [(Sum.inr 1916, (1 / 1))]

def nodeValue1917 : Sparse Master := [(Sum.inr 1917, (1 / 1))]

def nodeValue1918 : Sparse Master := []

def nodeValue1919 : Sparse Master := [(Sum.inr 1919, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue192 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 9, (5 / 216)), (Sum.inl 5, (5 / 108)), (Sum.inl 6, (-5 / 432)), (Sum.inl 257, (5 / 54)), (Sum.inl 60, (5 / 54)), (Sum.inl 268, (-5 / 18)), (Sum.inl 67, (5 / 54)), (Sum.inl 34, (5 / 54)), (Sum.inl 68, (-5 / 72)), (Sum.inl 2, (-5 / 288)), (Sum.inl 35, (5 / 27)), (Sum.inl 3, (5 / 54)), (Sum.inl 13, (5 / 54)), (Sum.inl 26, (5 / 54)), (Sum.inl 1, (-5 / 288))]

def nodeValue193 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 5, (5 / 216)), (Sum.inl 264, (-5 / 18)), (Sum.inl 266, (-5 / 18)), (Sum.inl 65, (-5 / 18)), (Sum.inl 68, (-5 / 36)), (Sum.inl 2, (-35 / 432)), (Sum.inl 54, (-5 / 18)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (-35 / 432))]

def nodeValue194 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 9, (5 / 216)), (Sum.inl 5, (5 / 108)), (Sum.inl 6, (-5 / 432)), (Sum.inl 257, (5 / 54)), (Sum.inl 60, (5 / 27)), (Sum.inl 264, (-5 / 18)), (Sum.inl 32, (5 / 54)), (Sum.inl 68, (-5 / 72)), (Sum.inl 2, (5 / 36)), (Sum.inl 35, (5 / 27)), (Sum.inl 13, (5 / 27)), (Sum.inl 1, (5 / 216))]

def nodeValue195 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 5, (5 / 216)), (Sum.inl 266, (-5 / 18)), (Sum.inl 61, (-5 / 18)), (Sum.inl 268, (-5 / 18)), (Sum.inl 68, (-5 / 36)), (Sum.inl 2, (-5 / 216)), (Sum.inl 55, (-5 / 18)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (-5 / 432))]

def nodeValue196 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 266, (5 / 9)), (Sum.inl 68, (5 / 36)), (Sum.inl 2, (-5 / 72)), (Sum.inl 1, (-5 / 72))]

def nodeValue197 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 268, (5 / 9)), (Sum.inl 68, (5 / 36)), (Sum.inl 2, (-5 / 432))]

def nodeValue206 : Sparse Master := [(Sum.inl 0, (19 / 432)), (Sum.inl 9, (-5 / 216)), (Sum.inl 58, (5 / 864)), (Sum.inl 5, (5 / 216)), (Sum.inl 6, (-35 / 864)), (Sum.inl 68, (5 / 72)), (Sum.inl 2, (-5 / 144)), (Sum.inl 70, (-5 / 54)), (Sum.inl 71, (-5 / 54)), (Sum.inl 7, (-5 / 54)), (Sum.inl 35, (-5 / 18)), (Sum.inl 3, (-5 / 54)), (Sum.inl 197, (5 / 18)), (Sum.inl 26, (-5 / 27)), (Sum.inl 1, (-5 / 216))]

def nodeValue207 : Sparse Master := [(Sum.inl 0, (29 / 864)), (Sum.inl 9, (-5 / 216)), (Sum.inl 58, (5 / 864)), (Sum.inl 5, (5 / 54)), (Sum.inl 6, (-25 / 432)), (Sum.inl 68, (5 / 72)), (Sum.inl 69, (-5 / 54)), (Sum.inl 70, (-5 / 54)), (Sum.inl 7, (-5 / 27)), (Sum.inl 35, (-10 / 27)), (Sum.inl 125, (5 / 18)), (Sum.inl 3, (-10 / 27)), (Sum.inl 13, (-25 / 54)), (Sum.inl 52, (-10 / 27)), (Sum.inl 1, (-25 / 432))]

def nodeValue208 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 9, (-5 / 108)), (Sum.inl 58, (5 / 864)), (Sum.inl 5, (-5 / 54)), (Sum.inl 6, (-5 / 216)), (Sum.inl 257, (-5 / 54)), (Sum.inl 260, (5 / 18)), (Sum.inl 60, (-25 / 54)), (Sum.inl 264, (5 / 18)), (Sum.inl 62, (5 / 9)), (Sum.inl 32, (-5 / 18)), (Sum.inl 68, (5 / 72)), (Sum.inl 2, (-5 / 864)), (Sum.inl 35, (-25 / 54)), (Sum.inl 3, (-10 / 27)), (Sum.inl 13, (-65 / 54)), (Sum.inl 128, (-5 / 27)), (Sum.inl 495, (-5 / 54)), (Sum.inl 52, (-10 / 27)), (Sum.inl 54, (5 / 18)), (Sum.inl 12, (-5 / 27)), (Sum.inl 1, (-5 / 144))]

def nodeValue209 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 9, (-5 / 108)), (Sum.inl 5, (5 / 72)), (Sum.inl 6, (5 / 432)), (Sum.inl 68, (5 / 36)), (Sum.inl 2, (-25 / 432)), (Sum.inl 69, (-5 / 54)), (Sum.inl 70, (-5 / 54)), (Sum.inl 7, (-5 / 18)), (Sum.inl 35, (-10 / 27)), (Sum.inl 125, (5 / 18)), (Sum.inl 3, (-10 / 27)), (Sum.inl 13, (-10 / 27)), (Sum.inl 52, (-5 / 27)), (Sum.inl 196, (5 / 18)), (Sum.inl 23, (5 / 18)), (Sum.inl 54, (5 / 9)), (Sum.inl 12, (-5 / 54)), (Sum.inl 27, (5 / 72)), (Sum.inl 1, (-5 / 48))]

def nodeValue210 : Sparse Master := [(Sum.inl 0, (1 / 24)), (Sum.inl 9, (-5 / 108)), (Sum.inl 5, (35 / 216)), (Sum.inl 68, (5 / 36)), (Sum.inl 2, (5 / 216)), (Sum.inl 71, (-5 / 27)), (Sum.inl 8, (-5 / 18)), (Sum.inl 197, (5 / 9)), (Sum.inl 24, (5 / 18)), (Sum.inl 56, (5 / 9)), (Sum.inl 27, (5 / 72)), (Sum.inl 1, (5 / 108))]

def nodeValue211 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 9, (5 / 216)), (Sum.inl 6, (-5 / 432)), (Sum.inl 68, (-5 / 72)), (Sum.inl 2, (-25 / 864)), (Sum.inl 69, (5 / 54)), (Sum.inl 125, (-5 / 18)), (Sum.inl 13, (5 / 54)), (Sum.inl 52, (5 / 27)), (Sum.inl 1, (-65 / 864))]

def nodeValue212 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 9, (-5 / 108)), (Sum.inl 58, (5 / 864)), (Sum.inl 5, (-5 / 72)), (Sum.inl 6, (-25 / 864)), (Sum.inl 257, (-5 / 54)), (Sum.inl 60, (-5 / 27)), (Sum.inl 262, (5 / 18)), (Sum.inl 268, (5 / 18)), (Sum.inl 67, (-5 / 54)), (Sum.inl 34, (-5 / 27)), (Sum.inl 68, (5 / 72)), (Sum.inl 2, (5 / 96)), (Sum.inl 35, (-10 / 27)), (Sum.inl 3, (-10 / 27)), (Sum.inl 13, (-5 / 18)), (Sum.inl 128, (-5 / 54)), (Sum.inl 495, (-5 / 54)), (Sum.inl 52, (-5 / 18)), (Sum.inl 56, (5 / 18)), (Sum.inl 26, (-5 / 18)), (Sum.inl 4, (-5 / 54)), (Sum.inl 1, (-25 / 864))]

def nodeValue213 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 9, (-5 / 108)), (Sum.inl 5, (-5 / 216)), (Sum.inl 6, (5 / 216)), (Sum.inl 259, (5 / 18)), (Sum.inl 59, (5 / 18)), (Sum.inl 262, (5 / 18)), (Sum.inl 266, (5 / 18)), (Sum.inl 61, (5 / 9)), (Sum.inl 268, (5 / 18)), (Sum.inl 68, (5 / 36)), (Sum.inl 2, (25 / 864)), (Sum.inl 35, (-5 / 27)), (Sum.inl 51, (5 / 9)), (Sum.inl 3, (-10 / 27)), (Sum.inl 13, (-10 / 27)), (Sum.inl 54, (5 / 9)), (Sum.inl 55, (5 / 18)), (Sum.inl 12, (-5 / 27)), (Sum.inl 56, (5 / 9)), (Sum.inl 26, (-5 / 54)), (Sum.inl 4, (-5 / 54)), (Sum.inl 27, (5 / 72)), (Sum.inl 1, (5 / 864))]

def nodeValue214 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 9, (5 / 216)), (Sum.inl 5, (5 / 108)), (Sum.inl 6, (-5 / 432)), (Sum.inl 259, (-5 / 18)), (Sum.inl 266, (-5 / 18)), (Sum.inl 68, (-5 / 72)), (Sum.inl 2, (-5 / 108)), (Sum.inl 35, (5 / 54)), (Sum.inl 54, (-5 / 18)), (Sum.inl 26, (5 / 54)), (Sum.inl 1, (-5 / 72))]

def nodeValue218 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 5, (5 / 108)), (Sum.inl 60, (-10 / 27)), (Sum.inl 62, (5 / 9)), (Sum.inl 32, (-10 / 27)), (Sum.inl 2, (-5 / 432)), (Sum.inl 35, (-10 / 27)), (Sum.inl 3, (-10 / 27)), (Sum.inl 13, (-40 / 27)), (Sum.inl 128, (-5 / 54)), (Sum.inl 52, (-10 / 27)), (Sum.inl 12, (-5 / 54))]

def nodeValue220 : Sparse Master := [(Sum.inl 0, (7 / 144)), (Sum.inl 5, (5 / 54)), (Sum.inl 6, (-5 / 216)), (Sum.inl 2, (-5 / 72)), (Sum.inl 7, (-5 / 54)), (Sum.inl 35, (-5 / 27)), (Sum.inl 3, (-5 / 27)), (Sum.inl 13, (-5 / 54)), (Sum.inl 54, (5 / 18)), (Sum.inl 26, (-5 / 27)), (Sum.inl 1, (-25 / 432))]

def nodeValue221 : Sparse Master := [(Sum.inl 0, (37 / 864)), (Sum.inl 5, (25 / 216)), (Sum.inl 6, (-5 / 288)), (Sum.inl 2, (35 / 864)), (Sum.inl 35, (-5 / 54)), (Sum.inl 8, (-5 / 54)), (Sum.inl 3, (-5 / 18)), (Sum.inl 13, (-5 / 27)), (Sum.inl 52, (-5 / 54)), (Sum.inl 56, (5 / 18)), (Sum.inl 26, (-5 / 54)), (Sum.inl 4, (-5 / 54)), (Sum.inl 1, (85 / 864))]

def nodeValue222 : Sparse Master := [(Sum.inl 0, (19 / 432)), (Sum.inl 5, (-5 / 216)), (Sum.inl 6, (5 / 216)), (Sum.inl 2, (-25 / 432)), (Sum.inl 35, (5 / 54)), (Sum.inl 26, (5 / 54)), (Sum.inl 1, (-5 / 108))]

def nodeValue223 : Sparse Master := [(Sum.inl 0, (31 / 864)), (Sum.inl 5, (5 / 72)), (Sum.inl 6, (-5 / 432)), (Sum.inl 2, (5 / 432)), (Sum.inl 7, (-5 / 54)), (Sum.inl 35, (-5 / 18)), (Sum.inl 3, (-20 / 27)), (Sum.inl 13, (-5 / 6)), (Sum.inl 52, (-5 / 27)), (Sum.inl 54, (5 / 18)), (Sum.inl 12, (-10 / 27)), (Sum.inl 1, (65 / 864))]

def nodeValue224 : Sparse Master := [(Sum.inl 0, (1 / 32)), (Sum.inl 5, (-5 / 216)), (Sum.inl 6, (5 / 288)), (Sum.inl 2, (5 / 864)), (Sum.inl 35, (5 / 54)), (Sum.inl 3, (5 / 54)), (Sum.inl 13, (5 / 27)), (Sum.inl 52, (5 / 54)), (Sum.inl 1, (35 / 864))]

def nodeValue225 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 6, (5 / 432)), (Sum.inl 60, (5 / 54)), (Sum.inl 62, (-5 / 18)), (Sum.inl 32, (5 / 54)), (Sum.inl 2, (-5 / 216)), (Sum.inl 35, (5 / 54)), (Sum.inl 3, (5 / 54)), (Sum.inl 13, (5 / 18)), (Sum.inl 52, (5 / 54)), (Sum.inl 1, (5 / 216))]

def nodeValue226 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 5, (-5 / 72)), (Sum.inl 2, (-25 / 864)), (Sum.inl 7, (5 / 54)), (Sum.inl 35, (5 / 54)), (Sum.inl 3, (5 / 54)), (Sum.inl 13, (5 / 54)), (Sum.inl 54, (-5 / 18)), (Sum.inl 1, (-55 / 864))]

def nodeValue227 : Sparse Master := [(Sum.inl 0, (17 / 432)), (Sum.inl 5, (-5 / 54)), (Sum.inl 2, (5 / 108)), (Sum.inl 8, (5 / 54)), (Sum.inl 56, (-5 / 18)), (Sum.inl 1, (35 / 432))]

def nodeValue228 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 6, (5 / 432)), (Sum.inl 60, (5 / 27)), (Sum.inl 32, (5 / 27)), (Sum.inl 2, (-5 / 54)), (Sum.inl 13, (5 / 9)), (Sum.inl 128, (5 / 54)), (Sum.inl 12, (5 / 54)), (Sum.inl 1, (-25 / 432))]

def nodeValue229 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 5, (-5 / 108)), (Sum.inl 59, (-5 / 18)), (Sum.inl 61, (-5 / 18)), (Sum.inl 2, (5 / 432)), (Sum.inl 3, (5 / 54)), (Sum.inl 13, (5 / 18)), (Sum.inl 12, (5 / 54)), (Sum.inl 1, (-5 / 216))]

def nodeValue231 : Sparse Master := [(Sum.inl 0, (31 / 864)), (Sum.inl 5, (-5 / 108)), (Sum.inl 6, (-5 / 864)), (Sum.inl 2, (25 / 864)), (Sum.inl 54, (-5 / 18)), (Sum.inl 56, (-5 / 18)), (Sum.inl 228, (-5 / 18)), (Sum.inl 1, (-5 / 864))]

def nodeValue232 : Sparse Master := [(Sum.inl 0, (47 / 864)), (Sum.inl 5, (-5 / 216)), (Sum.inl 6, (5 / 432)), (Sum.inl 2, (-25 / 216)), (Sum.inl 35, (-5 / 54)), (Sum.inl 3, (-10 / 27)), (Sum.inl 13, (-10 / 27)), (Sum.inl 52, (-5 / 27)), (Sum.inl 12, (-5 / 54)), (Sum.inl 1, (-35 / 288))]

def nodeValue233 : Sparse Master := [(Sum.inl 0, (13 / 288)), (Sum.inl 5, (5 / 216)), (Sum.inl 2, (185 / 864)), (Sum.inl 35, (5 / 54)), (Sum.inl 13, (5 / 54)), (Sum.inl 1, (5 / 432))]

def nodeValue234 : Sparse Master := [(Sum.inl 0, (19 / 432)), (Sum.inl 6, (-5 / 864)), (Sum.inl 2, (-5 / 144)), (Sum.inl 3, (5 / 54)), (Sum.inl 13, (5 / 54)), (Sum.inl 52, (5 / 54)), (Sum.inl 1, (-5 / 288))]

def nodeValue235 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 5, (5 / 216)), (Sum.inl 6, (-5 / 864)), (Sum.inl 2, (-5 / 288)), (Sum.inl 35, (5 / 54)), (Sum.inl 3, (5 / 27)), (Sum.inl 13, (5 / 18)), (Sum.inl 52, (5 / 54)), (Sum.inl 12, (5 / 54)), (Sum.inl 1, (-5 / 108))]

def nodeValue236 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 6, (5 / 432)), (Sum.inl 2, (-35 / 432)), (Sum.inl 13, (-5 / 27)), (Sum.inl 52, (-5 / 27)), (Sum.inl 1, (-35 / 432))]

def nodeValue237 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 5, (-5 / 108)), (Sum.inl 2, (85 / 432)), (Sum.inl 35, (-5 / 27)), (Sum.inl 13, (-5 / 27)), (Sum.inl 1, (-5 / 216))]

def nodeValue238 : Sparse Master := [(Sum.inl 0, (25 / 864)), (Sum.inl 5, (5 / 216)), (Sum.inl 6, (-5 / 864)), (Sum.inl 60, (-5 / 54)), (Sum.inl 61, (5 / 18)), (Sum.inl 62, (5 / 18)), (Sum.inl 32, (-5 / 54)), (Sum.inl 33, (5 / 18)), (Sum.inl 34, (-5 / 54)), (Sum.inl 2, (5 / 288)), (Sum.inl 35, (-5 / 27)), (Sum.inl 51, (5 / 18)), (Sum.inl 3, (-20 / 27)), (Sum.inl 13, (-25 / 27)), (Sum.inl 52, (-5 / 54)), (Sum.inl 54, (5 / 9)), (Sum.inl 12, (-10 / 27)), (Sum.inl 56, (5 / 18)), (Sum.inl 26, (-5 / 54)), (Sum.inl 4, (-5 / 54)), (Sum.inl 1, (35 / 864))]

def nodeValue239 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 6, (5 / 432)), (Sum.inl 60, (5 / 54)), (Sum.inl 34, (5 / 54)), (Sum.inl 2, (5 / 864)), (Sum.inl 35, (5 / 27)), (Sum.inl 3, (5 / 27)), (Sum.inl 13, (5 / 27)), (Sum.inl 52, (5 / 54)), (Sum.inl 26, (5 / 54)), (Sum.inl 1, (35 / 864))]

def nodeValue240 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 5, (-5 / 108)), (Sum.inl 61, (-5 / 18)), (Sum.inl 2, (25 / 432)), (Sum.inl 51, (-5 / 18)), (Sum.inl 54, (-5 / 18)), (Sum.inl 56, (-5 / 18)), (Sum.inl 1, (5 / 144))]

def nodeValue242 : Sparse Master := [(Sum.inl 0, (29 / 864)), (Sum.inl 5, (-5 / 72)), (Sum.inl 6, (5 / 288)), (Sum.inl 62, (5 / 9)), (Sum.inl 33, (5 / 6)), (Sum.inl 2, (-85 / 864)), (Sum.inl 35, (-5 / 54)), (Sum.inl 3, (-5 / 9)), (Sum.inl 13, (-5 / 18)), (Sum.inl 54, (5 / 6)), (Sum.inl 26, (-5 / 18)), (Sum.inl 1, (-65 / 864))]

def nodeValue243 : Sparse Master := [(Sum.inl 0, (11 / 288)), (Sum.inl 5, (-5 / 72)), (Sum.inl 6, (5 / 288)), (Sum.inl 2, (5 / 288)), (Sum.inl 35, (-5 / 18)), (Sum.inl 3, (-5 / 6)), (Sum.inl 13, (-25 / 54)), (Sum.inl 54, (5 / 18)), (Sum.inl 12, (-5 / 27)), (Sum.inl 56, (5 / 9)), (Sum.inl 26, (-10 / 27)), (Sum.inl 4, (-10 / 27)), (Sum.inl 1, (5 / 288))]

def nodeValue244 : Sparse Master := [(Sum.inl 0, (31 / 864)), (Sum.inl 5, (5 / 216)), (Sum.inl 6, (-5 / 864)), (Sum.inl 2, (-5 / 72)), (Sum.inl 35, (5 / 54)), (Sum.inl 3, (5 / 54)), (Sum.inl 54, (-5 / 18)), (Sum.inl 26, (5 / 27)), (Sum.inl 1, (-5 / 48))]

def nodeValue245 : Sparse Master := [(Sum.inl 0, (7 / 216)), (Sum.inl 5, (5 / 216)), (Sum.inl 6, (-5 / 864)), (Sum.inl 2, (25 / 864)), (Sum.inl 35, (5 / 54)), (Sum.inl 3, (5 / 27)), (Sum.inl 13, (5 / 54)), (Sum.inl 56, (-5 / 18)), (Sum.inl 26, (5 / 54)), (Sum.inl 4, (5 / 54)), (Sum.inl 1, (5 / 432))]

def nodeValue246 : Sparse Master := [(Sum.inl 0, (23 / 864)), (Sum.inl 5, (5 / 216)), (Sum.inl 6, (-5 / 864)), (Sum.inl 62, (-5 / 18)), (Sum.inl 33, (-5 / 18)), (Sum.inl 3, (5 / 54)), (Sum.inl 13, (5 / 54)), (Sum.inl 54, (-5 / 18)), (Sum.inl 1, (-5 / 144))]

def nodeValue247 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 6, (5 / 432)), (Sum.inl 2, (-5 / 216)), (Sum.inl 35, (-5 / 27)), (Sum.inl 26, (-5 / 27)), (Sum.inl 1, (-5 / 72))]

def nodeValue248 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 5, (5 / 216)), (Sum.inl 6, (-5 / 864)), (Sum.inl 2, (5 / 144)), (Sum.inl 35, (5 / 54)), (Sum.inl 3, (5 / 27)), (Sum.inl 13, (5 / 18)), (Sum.inl 54, (-5 / 18)), (Sum.inl 12, (5 / 27)), (Sum.inl 1, (145 / 864))]

def nodeValue249 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 6, (5 / 432)), (Sum.inl 35, (-5 / 27)), (Sum.inl 3, (-5 / 27)), (Sum.inl 13, (-5 / 27)), (Sum.inl 1, (5 / 27))]

def nodeValue250 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 6, (5 / 432)), (Sum.inl 62, (5 / 9)), (Sum.inl 2, (-5 / 54)), (Sum.inl 1, (-25 / 432))]

def nodeValue251 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 5, (-5 / 108)), (Sum.inl 2, (-5 / 432)), (Sum.inl 54, (5 / 9)), (Sum.inl 1, (55 / 432))]

def nodeValue252 : Sparse Master := [(Sum.inl 0, (7 / 216)), (Sum.inl 5, (-5 / 108)), (Sum.inl 2, (5 / 108)), (Sum.inl 56, (5 / 9)), (Sum.inl 1, (5 / 216))]

def nodeValue253 : Sparse Master := [(Sum.inl 0, (1 / 27)), (Sum.inl 5, (-5 / 72)), (Sum.inl 6, (5 / 288)), (Sum.inl 60, (-5 / 18)), (Sum.inl 61, (5 / 6)), (Sum.inl 32, (-5 / 27)), (Sum.inl 34, (-5 / 9)), (Sum.inl 2, (-25 / 288)), (Sum.inl 3, (-5 / 6)), (Sum.inl 13, (-35 / 27)), (Sum.inl 12, (-5 / 18)), (Sum.inl 26, (-5 / 18)), (Sum.inl 1, (-5 / 48))]

def nodeValue254 : Sparse Master := [(Sum.inl 0, (23 / 864)), (Sum.inl 5, (5 / 216)), (Sum.inl 6, (-5 / 864)), (Sum.inl 60, (5 / 54)), (Sum.inl 61, (-5 / 18)), (Sum.inl 34, (5 / 27)), (Sum.inl 2, (5 / 432)), (Sum.inl 3, (5 / 27)), (Sum.inl 13, (5 / 27)), (Sum.inl 26, (5 / 54)), (Sum.inl 1, (5 / 216))]

def nodeValue255 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 6, (5 / 432)), (Sum.inl 60, (-5 / 27)), (Sum.inl 34, (-5 / 27)), (Sum.inl 2, (-5 / 54)), (Sum.inl 13, (-5 / 27)), (Sum.inl 1, (-25 / 432))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue1920 : Sparse Master := [(Sum.inr 1920, (1 / 1))]

def nodeValue1921 : Sparse Master := [(Sum.inr 1921, (1 / 1))]

def nodeValue1922 : Sparse Master := [(Sum.inr 1922, (1 / 1))]

def nodeValue1923 : Sparse Master := [(Sum.inr 1923, (1 / 1))]

def nodeValue1924 : Sparse Master := [(Sum.inr 1924, (1 / 1))]

def nodeValue1925 : Sparse Master := [(Sum.inr 1925, (1 / 1))]

def nodeValue1926 : Sparse Master := [(Sum.inr 1926, (1 / 1))]

def nodeValue1927 : Sparse Master := [(Sum.inr 1927, (1 / 1))]

def nodeValue1928 : Sparse Master := [(Sum.inr 1928, (1 / 1))]

def nodeValue1929 : Sparse Master := [(Sum.inr 1929, (1 / 1))]

def nodeValue1935 : Sparse Master := [(Sum.inr 1935, (1 / 1))]

def nodeValue1936 : Sparse Master := [(Sum.inr 1936, (1 / 1))]

def nodeValue1937 : Sparse Master := [(Sum.inr 1937, (1 / 1))]

def nodeValue1938 : Sparse Master := [(Sum.inr 1938, (1 / 1))]

def nodeValue1939 : Sparse Master := [(Sum.inr 1939, (1 / 1))]

def nodeValue1940 : Sparse Master := [(Sum.inr 1940, (1 / 1))]

def nodeValue1941 : Sparse Master := [(Sum.inr 1941, (1 / 1))]

def nodeValue1942 : Sparse Master := [(Sum.inr 1942, (1 / 1))]

def nodeValue1944 : Sparse Master := []

def nodeValue1945 : Sparse Master := []

def nodeValue1946 : Sparse Master := [(Sum.inr 1946, (1 / 1))]

def nodeValue1947 : Sparse Master := []

def nodeValue1948 : Sparse Master := [(Sum.inr 1948, (1 / 1))]

def nodeValue1949 : Sparse Master := [(Sum.inr 1949, (1 / 1))]

def nodeValue1950 : Sparse Master := []

def nodeValue1951 : Sparse Master := [(Sum.inr 1951, (1 / 1))]

def nodeValue1952 : Sparse Master := [(Sum.inr 1952, (1 / 1))]

def nodeValue1953 : Sparse Master := []

def nodeValue1955 : Sparse Master := [(Sum.inr 1955, (1 / 1))]

def nodeValue1956 : Sparse Master := [(Sum.inr 1956, (1 / 1))]

def nodeValue1957 : Sparse Master := [(Sum.inr 1957, (1 / 1))]

def nodeValue1959 : Sparse Master := [(Sum.inr 1959, (1 / 1))]

def nodeValue1960 : Sparse Master := [(Sum.inr 1960, (1 / 1))]

def nodeValue1961 : Sparse Master := [(Sum.inr 1961, (1 / 1))]

def nodeValue1963 : Sparse Master := [(Sum.inr 1963, (1 / 1))]

def nodeValue1964 : Sparse Master := [(Sum.inr 1964, (1 / 1))]

def nodeValue1965 : Sparse Master := [(Sum.inr 1965, (1 / 1))]

def nodeValue1966 : Sparse Master := [(Sum.inr 1966, (1 / 1))]

def nodeValue1967 : Sparse Master := [(Sum.inr 1967, (1 / 1))]

def nodeValue1969 : Sparse Master := [(Sum.inr 1969, (1 / 1))]

def nodeValue1970 : Sparse Master := [(Sum.inr 1970, (1 / 1))]

def nodeValue1971 : Sparse Master := [(Sum.inr 1971, (1 / 1))]

def nodeValue1972 : Sparse Master := [(Sum.inr 1972, (1 / 1))]

def nodeValue1973 : Sparse Master := [(Sum.inr 1973, (1 / 1))]

def nodeValue1974 : Sparse Master := [(Sum.inr 1974, (1 / 1))]

def nodeValue1975 : Sparse Master := [(Sum.inr 1975, (1 / 1))]

def nodeValue1976 : Sparse Master := [(Sum.inr 1976, (1 / 1))]

def nodeValue1977 : Sparse Master := [(Sum.inr 1977, (1 / 1))]

def nodeValue1978 : Sparse Master := [(Sum.inr 1978, (1 / 1))]

def nodeValue1979 : Sparse Master := [(Sum.inr 1979, (1 / 1))]

def nodeValue1980 : Sparse Master := [(Sum.inr 1980, (1 / 1))]

def nodeValue1982 : Sparse Master := [(Sum.inr 1982, (1 / 1))]

def nodeValue1983 : Sparse Master := [(Sum.inr 1983, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue1986 : Sparse Master := [(Sum.inr 1986, (1 / 1))]

def nodeValue1987 : Sparse Master := [(Sum.inr 1987, (1 / 1))]

def nodeValue1989 : Sparse Master := [(Sum.inr 1989, (1 / 1))]

def nodeValue1990 : Sparse Master := [(Sum.inr 1990, (1 / 1))]

def nodeValue1991 : Sparse Master := [(Sum.inr 1991, (1 / 1))]

def nodeValue1992 : Sparse Master := [(Sum.inr 1992, (1 / 1))]

def nodeValue1993 : Sparse Master := [(Sum.inr 1993, (1 / 1))]

def nodeValue1994 : Sparse Master := [(Sum.inr 1994, (1 / 1))]

def nodeValue1995 : Sparse Master := [(Sum.inr 1995, (1 / 1))]

def nodeValue1996 : Sparse Master := [(Sum.inr 1996, (1 / 1))]

def nodeValue1997 : Sparse Master := [(Sum.inr 1997, (1 / 1))]

def nodeValue1998 : Sparse Master := [(Sum.inr 1998, (1 / 1))]

def nodeValue2000 : Sparse Master := [(Sum.inr 2000, (1 / 1))]

def nodeValue2001 : Sparse Master := [(Sum.inr 2001, (1 / 1))]

def nodeValue2002 : Sparse Master := [(Sum.inr 2002, (1 / 1))]

def nodeValue2003 : Sparse Master := [(Sum.inr 2003, (1 / 1))]

def nodeValue2004 : Sparse Master := [(Sum.inr 2004, (1 / 1))]

def nodeValue2005 : Sparse Master := [(Sum.inr 2005, (1 / 1))]

def nodeValue2006 : Sparse Master := [(Sum.inr 2006, (1 / 1))]

def nodeValue2008 : Sparse Master := [(Sum.inr 2008, (1 / 1))]

def nodeValue2009 : Sparse Master := [(Sum.inr 2009, (1 / 1))]

def nodeValue2010 : Sparse Master := [(Sum.inr 2010, (1 / 1))]

def nodeValue2011 : Sparse Master := [(Sum.inr 2011, (1 / 1))]

def nodeValue2012 : Sparse Master := [(Sum.inr 2012, (1 / 1))]

def nodeValue2013 : Sparse Master := [(Sum.inr 2013, (1 / 1))]

def nodeValue2014 : Sparse Master := [(Sum.inr 2014, (1 / 1))]

def nodeValue2015 : Sparse Master := [(Sum.inr 2015, (1 / 1))]

def nodeValue2016 : Sparse Master := [(Sum.inr 2016, (1 / 1))]

def nodeValue2017 : Sparse Master := [(Sum.inr 2017, (1 / 1))]

def nodeValue2018 : Sparse Master := [(Sum.inr 2018, (1 / 1))]

def nodeValue2019 : Sparse Master := [(Sum.inr 2019, (1 / 1))]

def nodeValue2020 : Sparse Master := [(Sum.inr 2020, (1 / 1))]

def nodeValue2021 : Sparse Master := [(Sum.inr 2021, (1 / 1))]

def nodeValue2022 : Sparse Master := [(Sum.inr 2022, (1 / 1))]

def nodeValue2023 : Sparse Master := [(Sum.inr 2023, (1 / 1))]

def nodeValue2024 : Sparse Master := [(Sum.inr 2024, (1 / 1))]

def nodeValue2025 : Sparse Master := [(Sum.inr 2025, (1 / 1))]

def nodeValue2026 : Sparse Master := [(Sum.inr 2026, (1 / 1))]

def nodeValue2027 : Sparse Master := [(Sum.inr 2027, (1 / 1))]

def nodeValue2028 : Sparse Master := [(Sum.inr 2028, (1 / 1))]

def nodeValue2029 : Sparse Master := [(Sum.inr 2029, (1 / 1))]

def nodeValue2030 : Sparse Master := [(Sum.inr 2030, (1 / 1))]

def nodeValue2031 : Sparse Master := [(Sum.inr 2031, (1 / 1))]

def nodeValue2032 : Sparse Master := [(Sum.inr 2032, (1 / 1))]

def nodeValue2033 : Sparse Master := [(Sum.inr 2033, (1 / 1))]

def nodeValue2034 : Sparse Master := [(Sum.inr 2034, (1 / 1))]

def nodeValue2035 : Sparse Master := [(Sum.inr 2035, (1 / 1))]

def nodeValue2036 : Sparse Master := [(Sum.inr 2036, (1 / 1))]

def nodeValue2037 : Sparse Master := [(Sum.inr 2037, (1 / 1))]

def nodeValue2038 : Sparse Master := [(Sum.inr 2038, (1 / 1))]

def nodeValue2039 : Sparse Master := [(Sum.inr 2039, (1 / 1))]

def nodeValue2040 : Sparse Master := [(Sum.inr 2040, (1 / 1))]

def nodeValue2041 : Sparse Master := [(Sum.inr 2041, (1 / 1))]

def nodeValue2042 : Sparse Master := [(Sum.inr 2042, (1 / 1))]

def nodeValue2043 : Sparse Master := [(Sum.inr 2043, (1 / 1))]

def nodeValue2044 : Sparse Master := [(Sum.inr 2044, (1 / 1))]

def nodeValue2045 : Sparse Master := [(Sum.inr 2045, (1 / 1))]

def nodeValue2046 : Sparse Master := [(Sum.inr 2046, (1 / 1))]

def nodeValue2047 : Sparse Master := [(Sum.inr 2047, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue2048 : Sparse Master := [(Sum.inr 2048, (1 / 1))]

def nodeValue2049 : Sparse Master := [(Sum.inr 2049, (1 / 1))]

def nodeValue2050 : Sparse Master := [(Sum.inr 2050, (1 / 1))]

def nodeValue2051 : Sparse Master := [(Sum.inr 2051, (1 / 1))]

def nodeValue2052 : Sparse Master := [(Sum.inr 2052, (1 / 1))]

def nodeValue2053 : Sparse Master := []

def nodeValue2054 : Sparse Master := [(Sum.inr 2054, (1 / 1))]

def nodeValue2055 : Sparse Master := [(Sum.inr 2055, (1 / 1))]

def nodeValue2056 : Sparse Master := []

def nodeValue2057 : Sparse Master := []

def nodeValue2058 : Sparse Master := [(Sum.inr 2058, (1 / 1))]

def nodeValue2059 : Sparse Master := [(Sum.inr 2059, (1 / 1))]

def nodeValue2060 : Sparse Master := []

def nodeValue2062 : Sparse Master := [(Sum.inr 2062, (1 / 1))]

def nodeValue2063 : Sparse Master := [(Sum.inr 2063, (1 / 1))]

def nodeValue2064 : Sparse Master := [(Sum.inr 2064, (1 / 1))]

def nodeValue2065 : Sparse Master := [(Sum.inr 2065, (1 / 1))]

def nodeValue2066 : Sparse Master := []

def nodeValue2067 : Sparse Master := [(Sum.inr 2067, (1 / 1))]

def nodeValue2070 : Sparse Master := [(Sum.inr 2070, (1 / 1))]

def nodeValue2071 : Sparse Master := [(Sum.inr 2071, (1 / 1))]

def nodeValue2072 : Sparse Master := [(Sum.inr 2072, (1 / 1))]

def nodeValue2073 : Sparse Master := [(Sum.inr 2073, (1 / 1))]

def nodeValue2074 : Sparse Master := [(Sum.inr 2074, (1 / 1))]

def nodeValue2075 : Sparse Master := [(Sum.inr 2075, (1 / 1))]

def nodeValue2076 : Sparse Master := [(Sum.inr 2076, (1 / 1))]

def nodeValue2077 : Sparse Master := [(Sum.inr 2077, (1 / 1))]

def nodeValue2078 : Sparse Master := [(Sum.inr 2078, (1 / 1))]

def nodeValue2079 : Sparse Master := [(Sum.inr 2079, (1 / 1))]

def nodeValue2080 : Sparse Master := [(Sum.inr 2080, (1 / 1))]

def nodeValue2081 : Sparse Master := [(Sum.inr 2081, (1 / 1))]

def nodeValue2082 : Sparse Master := [(Sum.inr 2082, (1 / 1))]

def nodeValue2083 : Sparse Master := [(Sum.inr 2083, (1 / 1))]

def nodeValue2084 : Sparse Master := [(Sum.inr 2084, (1 / 1))]

def nodeValue2085 : Sparse Master := [(Sum.inr 2085, (1 / 1))]

def nodeValue2086 : Sparse Master := [(Sum.inr 2086, (1 / 1))]

def nodeValue2087 : Sparse Master := [(Sum.inr 2087, (1 / 1))]

def nodeValue2088 : Sparse Master := [(Sum.inr 2088, (1 / 1))]

def nodeValue2089 : Sparse Master := [(Sum.inr 2089, (1 / 1))]

def nodeValue2090 : Sparse Master := [(Sum.inr 2090, (1 / 1))]

def nodeValue2091 : Sparse Master := [(Sum.inr 2091, (1 / 1))]

def nodeValue2092 : Sparse Master := [(Sum.inr 2092, (1 / 1))]

def nodeValue2093 : Sparse Master := [(Sum.inr 2093, (1 / 1))]

def nodeValue2094 : Sparse Master := [(Sum.inr 2094, (1 / 1))]

def nodeValue2095 : Sparse Master := [(Sum.inr 2095, (1 / 1))]

def nodeValue2096 : Sparse Master := [(Sum.inr 2096, (1 / 1))]

def nodeValue2097 : Sparse Master := [(Sum.inr 2097, (1 / 1))]

def nodeValue2098 : Sparse Master := [(Sum.inr 2098, (1 / 1))]

def nodeValue2099 : Sparse Master := [(Sum.inr 2099, (1 / 1))]

def nodeValue2100 : Sparse Master := [(Sum.inr 2100, (1 / 1))]

def nodeValue2101 : Sparse Master := [(Sum.inr 2101, (1 / 1))]

def nodeValue2102 : Sparse Master := [(Sum.inr 2102, (1 / 1))]

def nodeValue2103 : Sparse Master := [(Sum.inr 2103, (1 / 1))]

def nodeValue2104 : Sparse Master := [(Sum.inr 2104, (1 / 1))]

def nodeValue2105 : Sparse Master := [(Sum.inr 2105, (1 / 1))]

def nodeValue2106 : Sparse Master := [(Sum.inr 2106, (1 / 1))]

def nodeValue2107 : Sparse Master := [(Sum.inr 2107, (1 / 1))]

def nodeValue2108 : Sparse Master := [(Sum.inr 2108, (1 / 1))]

def nodeValue2109 : Sparse Master := [(Sum.inr 2109, (1 / 1))]

def nodeValue2110 : Sparse Master := [(Sum.inr 2110, (1 / 1))]

def nodeValue2111 : Sparse Master := [(Sum.inr 2111, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue2112 : Sparse Master := [(Sum.inr 2112, (1 / 1))]

def nodeValue2113 : Sparse Master := [(Sum.inr 2113, (1 / 1))]

def nodeValue2114 : Sparse Master := [(Sum.inr 2114, (1 / 1))]

def nodeValue2115 : Sparse Master := [(Sum.inr 2115, (1 / 1))]

def nodeValue2116 : Sparse Master := [(Sum.inr 2116, (1 / 1))]

def nodeValue2117 : Sparse Master := [(Sum.inr 2117, (1 / 1))]

def nodeValue2118 : Sparse Master := [(Sum.inr 2118, (1 / 1))]

def nodeValue2119 : Sparse Master := [(Sum.inr 2119, (1 / 1))]

def nodeValue2121 : Sparse Master := [(Sum.inr 2121, (1 / 1))]

def nodeValue2122 : Sparse Master := [(Sum.inr 2122, (1 / 1))]

def nodeValue2123 : Sparse Master := [(Sum.inr 2123, (1 / 1))]

def nodeValue2124 : Sparse Master := [(Sum.inr 2124, (1 / 1))]

def nodeValue2125 : Sparse Master := [(Sum.inr 2125, (1 / 1))]

def nodeValue2126 : Sparse Master := [(Sum.inr 2126, (1 / 1))]

def nodeValue2127 : Sparse Master := [(Sum.inr 2127, (1 / 1))]

def nodeValue2128 : Sparse Master := [(Sum.inr 2128, (1 / 1))]

def nodeValue2129 : Sparse Master := [(Sum.inr 2129, (1 / 1))]

def nodeValue2130 : Sparse Master := [(Sum.inr 2130, (1 / 1))]

def nodeValue2131 : Sparse Master := [(Sum.inr 2131, (1 / 1))]

def nodeValue2132 : Sparse Master := [(Sum.inr 2132, (1 / 1))]

def nodeValue2133 : Sparse Master := [(Sum.inr 2133, (1 / 1))]

def nodeValue2134 : Sparse Master := [(Sum.inr 2134, (1 / 1))]

def nodeValue2136 : Sparse Master := [(Sum.inr 2136, (1 / 1))]

def nodeValue2137 : Sparse Master := [(Sum.inr 2137, (1 / 1))]

def nodeValue2138 : Sparse Master := [(Sum.inr 2138, (1 / 1))]

def nodeValue2139 : Sparse Master := [(Sum.inr 2139, (1 / 1))]

def nodeValue2140 : Sparse Master := [(Sum.inr 2140, (1 / 1))]

def nodeValue2141 : Sparse Master := [(Sum.inr 2141, (1 / 1))]

def nodeValue2142 : Sparse Master := [(Sum.inr 2142, (1 / 1))]

def nodeValue2143 : Sparse Master := [(Sum.inr 2143, (1 / 1))]

def nodeValue2144 : Sparse Master := [(Sum.inr 2144, (1 / 1))]

def nodeValue2145 : Sparse Master := [(Sum.inr 2145, (1 / 1))]

def nodeValue2146 : Sparse Master := [(Sum.inr 2146, (1 / 1))]

def nodeValue2147 : Sparse Master := [(Sum.inr 2147, (1 / 1))]

def nodeValue2148 : Sparse Master := [(Sum.inr 2148, (1 / 1))]

def nodeValue2149 : Sparse Master := [(Sum.inr 2149, (1 / 1))]

def nodeValue2150 : Sparse Master := [(Sum.inr 2150, (1 / 1))]

def nodeValue2151 : Sparse Master := [(Sum.inr 2151, (1 / 1))]

def nodeValue2152 : Sparse Master := [(Sum.inr 2152, (1 / 1))]

def nodeValue2153 : Sparse Master := [(Sum.inr 2153, (1 / 1))]

def nodeValue2154 : Sparse Master := [(Sum.inr 2154, (1 / 1))]

def nodeValue2155 : Sparse Master := [(Sum.inr 2155, (1 / 1))]

def nodeValue2156 : Sparse Master := [(Sum.inr 2156, (1 / 1))]

def nodeValue2157 : Sparse Master := [(Sum.inr 2157, (1 / 1))]

def nodeValue2158 : Sparse Master := [(Sum.inr 2158, (1 / 1))]

def nodeValue2159 : Sparse Master := [(Sum.inr 2159, (1 / 1))]

def nodeValue2160 : Sparse Master := [(Sum.inr 2160, (1 / 1))]

def nodeValue2161 : Sparse Master := [(Sum.inr 2161, (1 / 1))]

def nodeValue2162 : Sparse Master := [(Sum.inr 2162, (1 / 1))]

def nodeValue2163 : Sparse Master := [(Sum.inr 2163, (1 / 1))]

def nodeValue2164 : Sparse Master := [(Sum.inr 2164, (1 / 1))]

def nodeValue2165 : Sparse Master := [(Sum.inr 2165, (1 / 1))]

def nodeValue2166 : Sparse Master := [(Sum.inr 2166, (1 / 1))]

def nodeValue2167 : Sparse Master := [(Sum.inr 2167, (1 / 1))]

def nodeValue2168 : Sparse Master := [(Sum.inr 2168, (1 / 1))]

def nodeValue2169 : Sparse Master := [(Sum.inr 2169, (1 / 1))]

def nodeValue2170 : Sparse Master := [(Sum.inr 2170, (1 / 1))]

def nodeValue2171 : Sparse Master := [(Sum.inr 2171, (1 / 1))]

def nodeValue2172 : Sparse Master := [(Sum.inr 2172, (1 / 1))]

def nodeValue2173 : Sparse Master := [(Sum.inr 2173, (1 / 1))]

def nodeValue2174 : Sparse Master := [(Sum.inr 2174, (1 / 1))]

def nodeValue2175 : Sparse Master := [(Sum.inr 2175, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue2176 : Sparse Master := [(Sum.inr 2176, (1 / 1))]

def nodeValue2177 : Sparse Master := [(Sum.inr 2177, (1 / 1))]

def nodeValue2178 : Sparse Master := [(Sum.inr 2178, (1 / 1))]

def nodeValue2179 : Sparse Master := [(Sum.inr 2179, (1 / 1))]

def nodeValue2180 : Sparse Master := [(Sum.inr 2180, (1 / 1))]

def nodeValue2181 : Sparse Master := [(Sum.inr 2181, (1 / 1))]

def nodeValue2182 : Sparse Master := [(Sum.inr 2182, (1 / 1))]

def nodeValue2183 : Sparse Master := [(Sum.inr 2183, (1 / 1))]

def nodeValue2184 : Sparse Master := [(Sum.inr 2184, (1 / 1))]

def nodeValue2185 : Sparse Master := [(Sum.inr 2185, (1 / 1))]

def nodeValue2186 : Sparse Master := [(Sum.inr 2186, (1 / 1))]

def nodeValue2187 : Sparse Master := [(Sum.inr 2187, (1 / 1))]

def nodeValue2189 : Sparse Master := [(Sum.inr 2189, (1 / 1))]

def nodeValue2190 : Sparse Master := [(Sum.inr 2190, (1 / 1))]

def nodeValue2191 : Sparse Master := [(Sum.inr 2191, (1 / 1))]

def nodeValue2192 : Sparse Master := [(Sum.inr 2192, (1 / 1))]

def nodeValue2193 : Sparse Master := [(Sum.inr 2193, (1 / 1))]

def nodeValue2194 : Sparse Master := [(Sum.inr 2194, (1 / 1))]

def nodeValue2195 : Sparse Master := [(Sum.inr 2195, (1 / 1))]

def nodeValue2196 : Sparse Master := [(Sum.inr 2196, (1 / 1))]

def nodeValue2197 : Sparse Master := [(Sum.inr 2197, (1 / 1))]

def nodeValue2198 : Sparse Master := [(Sum.inr 2198, (1 / 1))]

def nodeValue2199 : Sparse Master := [(Sum.inr 2199, (1 / 1))]

def nodeValue2200 : Sparse Master := [(Sum.inr 2200, (1 / 1))]

def nodeValue2201 : Sparse Master := [(Sum.inr 2201, (1 / 1))]

def nodeValue2202 : Sparse Master := [(Sum.inr 2202, (1 / 1))]

def nodeValue2203 : Sparse Master := [(Sum.inr 2203, (1 / 1))]

def nodeValue2204 : Sparse Master := []

def nodeValue2205 : Sparse Master := []

def nodeValue2206 : Sparse Master := [(Sum.inr 2206, (1 / 1))]

def nodeValue2207 : Sparse Master := [(Sum.inr 2207, (1 / 1))]

def nodeValue2208 : Sparse Master := []

def nodeValue2211 : Sparse Master := [(Sum.inr 2211, (1 / 1))]

def nodeValue2212 : Sparse Master := [(Sum.inr 2212, (1 / 1))]

def nodeValue2213 : Sparse Master := [(Sum.inr 2213, (1 / 1))]

def nodeValue2214 : Sparse Master := [(Sum.inr 2214, (1 / 1))]

def nodeValue2215 : Sparse Master := [(Sum.inr 2215, (1 / 1))]

def nodeValue2216 : Sparse Master := [(Sum.inr 2216, (1 / 1))]

def nodeValue2217 : Sparse Master := [(Sum.inr 2217, (1 / 1))]

def nodeValue2218 : Sparse Master := [(Sum.inr 2218, (1 / 1))]

def nodeValue2219 : Sparse Master := [(Sum.inr 2219, (1 / 1))]

def nodeValue2220 : Sparse Master := [(Sum.inr 2220, (1 / 1))]

def nodeValue2221 : Sparse Master := [(Sum.inr 2221, (1 / 1))]

def nodeValue2222 : Sparse Master := [(Sum.inr 2222, (1 / 1))]

def nodeValue2223 : Sparse Master := [(Sum.inr 2223, (1 / 1))]

def nodeValue2224 : Sparse Master := [(Sum.inr 2224, (1 / 1))]

def nodeValue2225 : Sparse Master := [(Sum.inr 2225, (1 / 1))]

def nodeValue2226 : Sparse Master := [(Sum.inr 2226, (1 / 1))]

def nodeValue2227 : Sparse Master := []

def nodeValue2228 : Sparse Master := []

def nodeValue2229 : Sparse Master := []

def nodeValue2230 : Sparse Master := [(Sum.inr 2230, (1 / 1))]

def nodeValue2231 : Sparse Master := [(Sum.inr 2231, (1 / 1))]

def nodeValue2232 : Sparse Master := [(Sum.inr 2232, (1 / 1))]

def nodeValue2233 : Sparse Master := [(Sum.inr 2233, (1 / 1))]

def nodeValue2234 : Sparse Master := [(Sum.inr 2234, (1 / 1))]

def nodeValue2235 : Sparse Master := [(Sum.inr 2235, (1 / 1))]

def nodeValue2238 : Sparse Master := [(Sum.inr 2238, (1 / 1))]

def nodeValue2239 : Sparse Master := [(Sum.inr 2239, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue2240 : Sparse Master := [(Sum.inr 2240, (1 / 1))]

def nodeValue2241 : Sparse Master := [(Sum.inr 2241, (1 / 1))]

def nodeValue2242 : Sparse Master := [(Sum.inr 2242, (1 / 1))]

def nodeValue2243 : Sparse Master := [(Sum.inr 2243, (1 / 1))]

def nodeValue2244 : Sparse Master := [(Sum.inr 2244, (1 / 1))]

def nodeValue2245 : Sparse Master := [(Sum.inr 2245, (1 / 1))]

def nodeValue2246 : Sparse Master := [(Sum.inr 2246, (1 / 1))]

def nodeValue2247 : Sparse Master := [(Sum.inr 2247, (1 / 1))]

def nodeValue2248 : Sparse Master := [(Sum.inr 2248, (1 / 1))]

def nodeValue2249 : Sparse Master := [(Sum.inr 2249, (1 / 1))]

def nodeValue2250 : Sparse Master := [(Sum.inr 2250, (1 / 1))]

def nodeValue2251 : Sparse Master := [(Sum.inr 2251, (1 / 1))]

def nodeValue2252 : Sparse Master := [(Sum.inr 2252, (1 / 1))]

def nodeValue2253 : Sparse Master := [(Sum.inr 2253, (1 / 1))]

def nodeValue2254 : Sparse Master := [(Sum.inr 2254, (1 / 1))]

def nodeValue2255 : Sparse Master := [(Sum.inr 2255, (1 / 1))]

def nodeValue2256 : Sparse Master := [(Sum.inr 2256, (1 / 1))]

def nodeValue2257 : Sparse Master := [(Sum.inr 2257, (1 / 1))]

def nodeValue2258 : Sparse Master := [(Sum.inr 2258, (1 / 1))]

def nodeValue2259 : Sparse Master := [(Sum.inr 2259, (1 / 1))]

def nodeValue2260 : Sparse Master := [(Sum.inr 2260, (1 / 1))]

def nodeValue2261 : Sparse Master := [(Sum.inr 2261, (1 / 1))]

def nodeValue2262 : Sparse Master := [(Sum.inr 2262, (1 / 1))]

def nodeValue2263 : Sparse Master := []

def nodeValue2264 : Sparse Master := []

def nodeValue2265 : Sparse Master := []

def nodeValue2266 : Sparse Master := [(Sum.inr 2266, (1 / 1))]

def nodeValue2267 : Sparse Master := [(Sum.inr 2267, (1 / 1))]

def nodeValue2268 : Sparse Master := []

def nodeValue2272 : Sparse Master := [(Sum.inr 2272, (1 / 1))]

def nodeValue2273 : Sparse Master := [(Sum.inr 2273, (1 / 1))]

def nodeValue2274 : Sparse Master := [(Sum.inr 2274, (1 / 1))]

def nodeValue2275 : Sparse Master := [(Sum.inr 2275, (1 / 1))]

def nodeValue2276 : Sparse Master := [(Sum.inr 2276, (1 / 1))]

def nodeValue2277 : Sparse Master := [(Sum.inr 2277, (1 / 1))]

def nodeValue2278 : Sparse Master := [(Sum.inr 2278, (1 / 1))]

def nodeValue2279 : Sparse Master := [(Sum.inr 2279, (1 / 1))]

def nodeValue2280 : Sparse Master := [(Sum.inr 2280, (1 / 1))]

def nodeValue2281 : Sparse Master := [(Sum.inr 2281, (1 / 1))]

def nodeValue2282 : Sparse Master := [(Sum.inr 2282, (1 / 1))]

def nodeValue2283 : Sparse Master := [(Sum.inr 2283, (1 / 1))]

def nodeValue2284 : Sparse Master := [(Sum.inr 2284, (1 / 1))]

def nodeValue2285 : Sparse Master := [(Sum.inr 2285, (1 / 1))]

def nodeValue2286 : Sparse Master := [(Sum.inr 2286, (1 / 1))]

def nodeValue2287 : Sparse Master := [(Sum.inr 2287, (1 / 1))]

def nodeValue2288 : Sparse Master := [(Sum.inr 2288, (1 / 1))]

def nodeValue2289 : Sparse Master := [(Sum.inr 2289, (1 / 1))]

def nodeValue2290 : Sparse Master := [(Sum.inr 2290, (1 / 1))]

def nodeValue2291 : Sparse Master := []

def nodeValue2292 : Sparse Master := []

def nodeValue2293 : Sparse Master := []

def nodeValue2294 : Sparse Master := [(Sum.inr 2294, (1 / 1))]

def nodeValue2295 : Sparse Master := [(Sum.inr 2295, (1 / 1))]

def nodeValue2300 : Sparse Master := [(Sum.inr 2300, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue2306 : Sparse Master := [(Sum.inr 2306, (1 / 1))]

def nodeValue2316 : Sparse Master := [(Sum.inr 2316, (1 / 1))]

def nodeValue2317 : Sparse Master := [(Sum.inr 2317, (1 / 1))]

def nodeValue2318 : Sparse Master := [(Sum.inr 2318, (1 / 1))]

def nodeValue2319 : Sparse Master := []

def nodeValue2320 : Sparse Master := [(Sum.inr 2320, (1 / 1))]

def nodeValue2321 : Sparse Master := [(Sum.inr 2321, (1 / 1))]

def nodeValue2322 : Sparse Master := []

def nodeValue2323 : Sparse Master := [(Sum.inr 2323, (1 / 1))]

def nodeValue2324 : Sparse Master := [(Sum.inr 2324, (1 / 1))]

def nodeValue2325 : Sparse Master := [(Sum.inr 2325, (1 / 1))]

def nodeValue2326 : Sparse Master := [(Sum.inr 2326, (1 / 1))]

def nodeValue2327 : Sparse Master := [(Sum.inr 2327, (1 / 1))]

def nodeValue2328 : Sparse Master := [(Sum.inr 2328, (1 / 1))]

def nodeValue2329 : Sparse Master := [(Sum.inr 2329, (1 / 1))]

def nodeValue2330 : Sparse Master := [(Sum.inr 2330, (1 / 1))]

def nodeValue2331 : Sparse Master := []

def nodeValue2332 : Sparse Master := [(Sum.inr 2332, (1 / 1))]

def nodeValue2333 : Sparse Master := [(Sum.inr 2333, (1 / 1))]

def nodeValue2334 : Sparse Master := [(Sum.inr 2334, (1 / 1))]

def nodeValue2335 : Sparse Master := [(Sum.inr 2335, (1 / 1))]

def nodeValue2337 : Sparse Master := [(Sum.inr 2337, (1 / 1))]

def nodeValue2338 : Sparse Master := [(Sum.inr 2338, (1 / 1))]

def nodeValue2339 : Sparse Master := [(Sum.inr 2339, (1 / 1))]

def nodeValue2340 : Sparse Master := [(Sum.inr 2340, (1 / 1))]

def nodeValue2341 : Sparse Master := [(Sum.inr 2341, (1 / 1))]

def nodeValue2342 : Sparse Master := [(Sum.inr 2342, (1 / 1))]

def nodeValue2343 : Sparse Master := [(Sum.inr 2343, (1 / 1))]

def nodeValue2344 : Sparse Master := [(Sum.inr 2344, (1 / 1))]

def nodeValue2345 : Sparse Master := [(Sum.inr 2345, (1 / 1))]

def nodeValue2346 : Sparse Master := [(Sum.inr 2346, (1 / 1))]

def nodeValue2347 : Sparse Master := [(Sum.inr 2347, (1 / 1))]

def nodeValue2348 : Sparse Master := [(Sum.inr 2348, (1 / 1))]

def nodeValue2349 : Sparse Master := [(Sum.inr 2349, (1 / 1))]

def nodeValue2350 : Sparse Master := [(Sum.inr 2350, (1 / 1))]

def nodeValue2351 : Sparse Master := [(Sum.inr 2351, (1 / 1))]

def nodeValue2352 : Sparse Master := [(Sum.inr 2352, (1 / 1))]

def nodeValue2353 : Sparse Master := [(Sum.inr 2353, (1 / 1))]

def nodeValue2354 : Sparse Master := [(Sum.inr 2354, (1 / 1))]

def nodeValue2355 : Sparse Master := [(Sum.inr 2355, (1 / 1))]

def nodeValue2356 : Sparse Master := [(Sum.inr 2356, (1 / 1))]

def nodeValue2357 : Sparse Master := [(Sum.inl 0, (-1 / 270)), (Sum.inl 9, (-1 / 216)), (Sum.inl 6, (1 / 432)), (Sum.inl 68, (1 / 72)), (Sum.inl 2, (1 / 288)), (Sum.inl 69, (-1 / 54)), (Sum.inl 7, (-1 / 27)), (Sum.inl 124, (1 / 18)), (Sum.inl 3, (-1 / 54)), (Sum.inl 1, (-19 / 864))]

def nodeValue2358 : Sparse Master := [(Sum.inl 0, (-1 / 160)), (Sum.inl 9, (-1 / 216)), (Sum.inl 6, (1 / 432)), (Sum.inl 68, (1 / 72)), (Sum.inl 2, (-7 / 864)), (Sum.inl 69, (-1 / 54)), (Sum.inl 7, (-1 / 54)), (Sum.inl 126, (1 / 18)), (Sum.inl 3, (-1 / 54)), (Sum.inl 52, (-1 / 54)), (Sum.inl 1, (5 / 432))]

def nodeValue2359 : Sparse Master := [(Sum.inl 0, (-11 / 2160)), (Sum.inl 5, (-1 / 216)), (Sum.inl 68, (1 / 36)), (Sum.inl 2, (-1 / 864)), (Sum.inl 7, (-1 / 54)), (Sum.inl 124, (1 / 18)), (Sum.inl 125, (1 / 18)), (Sum.inl 3, (-1 / 54)), (Sum.inl 23, (1 / 18)), (Sum.inl 27, (1 / 72)), (Sum.inl 1, (-5 / 288))]

def nodeValue2361 : Sparse Master := [(Sum.inr 2361, (1 / 1))]

def nodeValue2362 : Sparse Master := [(Sum.inr 2362, (1 / 1))]

def nodeValue2363 : Sparse Master := [(Sum.inl 0, (-1 / 180)), (Sum.inl 68, (-1 / 36)), (Sum.inl 2, (1 / 144)), (Sum.inl 125, (-1 / 9)), (Sum.inl 1, (-1 / 48))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue2370 : Sparse Master := [(Sum.inr 2370, (1 / 1))]

def nodeValue2371 : Sparse Master := [(Sum.inr 2371, (1 / 1))]

def nodeValue2372 : Sparse Master := [(Sum.inr 2372, (1 / 1))]

def nodeValue2377 : Sparse Master := []

def nodeValue2378 : Sparse Master := [(Sum.inr 2378, (1 / 1))]

def nodeValue2379 : Sparse Master := [(Sum.inr 2379, (1 / 1))]

def nodeValue2382 : Sparse Master := [(Sum.inr 2382, (1 / 1))]

def nodeValue2383 : Sparse Master := [(Sum.inr 2383, (1 / 1))]

def nodeValue2384 : Sparse Master := [(Sum.inr 2384, (1 / 1))]

def nodeValue2385 : Sparse Master := [(Sum.inr 2385, (1 / 1))]

def nodeValue2388 : Sparse Master := [(Sum.inr 2388, (1 / 1))]

def nodeValue2389 : Sparse Master := [(Sum.inr 2389, (1 / 1))]

def nodeValue2390 : Sparse Master := [(Sum.inr 2390, (1 / 1))]

def nodeValue2391 : Sparse Master := [(Sum.inr 2391, (1 / 1))]

def nodeValue2392 : Sparse Master := [(Sum.inr 2392, (1 / 1))]

def nodeValue2393 : Sparse Master := [(Sum.inr 2393, (1 / 1))]

def nodeValue2394 : Sparse Master := [(Sum.inr 2394, (1 / 1))]

def nodeValue2395 : Sparse Master := [(Sum.inr 2395, (1 / 1))]

def nodeValue2396 : Sparse Master := [(Sum.inr 2396, (1 / 1))]

def nodeValue2397 : Sparse Master := [(Sum.inr 2397, (1 / 1))]

def nodeValue2398 : Sparse Master := [(Sum.inr 2398, (1 / 1))]

def nodeValue2399 : Sparse Master := [(Sum.inr 2399, (1 / 1))]

def nodeValue2400 : Sparse Master := [(Sum.inr 2400, (1 / 1))]

def nodeValue2401 : Sparse Master := [(Sum.inr 2401, (1 / 1))]

def nodeValue2402 : Sparse Master := []

def nodeValue2403 : Sparse Master := []

def nodeValue2404 : Sparse Master := [(Sum.inr 2404, (1 / 1))]

def nodeValue2405 : Sparse Master := [(Sum.inr 2405, (1 / 1))]

def nodeValue2407 : Sparse Master := [(Sum.inr 2407, (1 / 1))]

def nodeValue2408 : Sparse Master := [(Sum.inr 2408, (1 / 1))]

def nodeValue2409 : Sparse Master := [(Sum.inr 2409, (1 / 1))]

def nodeValue2410 : Sparse Master := [(Sum.inr 2410, (1 / 1))]

def nodeValue2411 : Sparse Master := []

def nodeValue2412 : Sparse Master := [(Sum.inr 2412, (1 / 1))]

def nodeValue2419 : Sparse Master := [(Sum.inr 2419, (1 / 1))]

def nodeValue2422 : Sparse Master := [(Sum.inr 2422, (1 / 1))]

def nodeValue2423 : Sparse Master := [(Sum.inr 2423, (1 / 1))]

def nodeValue2424 : Sparse Master := [(Sum.inr 2424, (1 / 1))]

def nodeValue2425 : Sparse Master := [(Sum.inr 2425, (1 / 1))]

def nodeValue2426 : Sparse Master := [(Sum.inr 2426, (1 / 1))]

def nodeValue2427 : Sparse Master := [(Sum.inr 2427, (1 / 1))]

def nodeValue2428 : Sparse Master := [(Sum.inr 2428, (1 / 1))]

def nodeValue2429 : Sparse Master := [(Sum.inr 2429, (1 / 1))]

def nodeValue2430 : Sparse Master := [(Sum.inr 2430, (1 / 1))]

def nodeValue2431 : Sparse Master := [(Sum.inr 2431, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue2432 : Sparse Master := [(Sum.inr 2432, (1 / 1))]

def nodeValue2433 : Sparse Master := [(Sum.inr 2433, (1 / 1))]

def nodeValue2434 : Sparse Master := [(Sum.inr 2434, (1 / 1))]

def nodeValue2435 : Sparse Master := [(Sum.inr 2435, (1 / 1))]

def nodeValue2436 : Sparse Master := [(Sum.inr 2436, (1 / 1))]

def nodeValue2437 : Sparse Master := [(Sum.inr 2437, (1 / 1))]

def nodeValue2438 : Sparse Master := [(Sum.inr 2438, (1 / 1))]

def nodeValue2440 : Sparse Master := [(Sum.inr 2440, (1 / 1))]

def nodeValue2441 : Sparse Master := [(Sum.inr 2441, (1 / 1))]

def nodeValue2442 : Sparse Master := [(Sum.inr 2442, (1 / 1))]

def nodeValue2443 : Sparse Master := [(Sum.inr 2443, (1 / 1))]

def nodeValue2449 : Sparse Master := [(Sum.inr 2449, (1 / 1))]

def nodeValue2452 : Sparse Master := [(Sum.inr 2452, (1 / 1))]

def nodeValue2453 : Sparse Master := [(Sum.inr 2453, (1 / 1))]

def nodeValue2454 : Sparse Master := [(Sum.inr 2454, (1 / 1))]

def nodeValue2455 : Sparse Master := [(Sum.inr 2455, (1 / 1))]

def nodeValue2456 : Sparse Master := [(Sum.inr 2456, (1 / 1))]

def nodeValue2457 : Sparse Master := [(Sum.inr 2457, (1 / 1))]

def nodeValue2458 : Sparse Master := [(Sum.inr 2458, (1 / 1))]

def nodeValue2459 : Sparse Master := [(Sum.inr 2459, (1 / 1))]

def nodeValue2460 : Sparse Master := [(Sum.inr 2460, (1 / 1))]

def nodeValue2461 : Sparse Master := []

def nodeValue2462 : Sparse Master := [(Sum.inr 2462, (1 / 1))]

def nodeValue2463 : Sparse Master := [(Sum.inr 2463, (1 / 1))]

def nodeValue2465 : Sparse Master := [(Sum.inr 2465, (1 / 1))]

def nodeValue2466 : Sparse Master := [(Sum.inr 2466, (1 / 1))]

def nodeValue2467 : Sparse Master := [(Sum.inr 2467, (1 / 1))]

def nodeValue2468 : Sparse Master := []

def nodeValue2469 : Sparse Master := [(Sum.inr 2469, (1 / 1))]

def nodeValue2470 : Sparse Master := [(Sum.inr 2470, (1 / 1))]

def nodeValue2471 : Sparse Master := [(Sum.inr 2471, (1 / 1))]

def nodeValue2472 : Sparse Master := [(Sum.inr 2472, (1 / 1))]

def nodeValue2473 : Sparse Master := [(Sum.inr 2473, (1 / 1))]

def nodeValue2474 : Sparse Master := [(Sum.inr 2474, (1 / 1))]

def nodeValue2475 : Sparse Master := [(Sum.inr 2475, (1 / 1))]

def nodeValue2476 : Sparse Master := [(Sum.inr 2476, (1 / 1))]

def nodeValue2477 : Sparse Master := [(Sum.inr 2477, (1 / 1))]

def nodeValue2478 : Sparse Master := [(Sum.inr 2478, (1 / 1))]

def nodeValue2479 : Sparse Master := [(Sum.inr 2479, (1 / 1))]

def nodeValue2480 : Sparse Master := [(Sum.inr 2480, (1 / 1))]

def nodeValue2481 : Sparse Master := [(Sum.inr 2481, (1 / 1))]

def nodeValue2482 : Sparse Master := [(Sum.inr 2482, (1 / 1))]

def nodeValue2483 : Sparse Master := [(Sum.inr 2483, (1 / 1))]

def nodeValue2484 : Sparse Master := [(Sum.inr 2484, (1 / 1))]

def nodeValue2485 : Sparse Master := [(Sum.inr 2485, (1 / 1))]

def nodeValue2486 : Sparse Master := [(Sum.inr 2486, (1 / 1))]

def nodeValue2488 : Sparse Master := [(Sum.inr 2488, (1 / 1))]

def nodeValue2489 : Sparse Master := [(Sum.inr 2489, (1 / 1))]

def nodeValue2490 : Sparse Master := [(Sum.inr 2490, (1 / 1))]

def nodeValue2491 : Sparse Master := [(Sum.inr 2491, (1 / 1))]

def nodeValue2492 : Sparse Master := [(Sum.inr 2492, (1 / 1))]

def nodeValue2493 : Sparse Master := [(Sum.inr 2493, (1 / 1))]

def nodeValue2494 : Sparse Master := [(Sum.inr 2494, (1 / 1))]

def nodeValue2495 : Sparse Master := [(Sum.inr 2495, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue2496 : Sparse Master := [(Sum.inr 2496, (1 / 1))]

def nodeValue2497 : Sparse Master := [(Sum.inr 2497, (1 / 1))]

def nodeValue2498 : Sparse Master := [(Sum.inr 2498, (1 / 1))]

def nodeValue2499 : Sparse Master := [(Sum.inr 2499, (1 / 1))]

def nodeValue2500 : Sparse Master := [(Sum.inr 2500, (1 / 1))]

def nodeValue2501 : Sparse Master := [(Sum.inr 2501, (1 / 1))]

def nodeValue2502 : Sparse Master := [(Sum.inr 2502, (1 / 1))]

def nodeValue2503 : Sparse Master := [(Sum.inr 2503, (1 / 1))]

def nodeValue2504 : Sparse Master := [(Sum.inr 2504, (1 / 1))]

def nodeValue2505 : Sparse Master := [(Sum.inr 2505, (1 / 1))]

def nodeValue2506 : Sparse Master := [(Sum.inr 2506, (1 / 1))]

def nodeValue2507 : Sparse Master := [(Sum.inr 2507, (1 / 1))]

def nodeValue2508 : Sparse Master := [(Sum.inr 2508, (1 / 1))]

def nodeValue2509 : Sparse Master := [(Sum.inr 2509, (1 / 1))]

def nodeValue2510 : Sparse Master := []

def nodeValue2511 : Sparse Master := []

def nodeValue2512 : Sparse Master := [(Sum.inr 2512, (1 / 1))]

def nodeValue2513 : Sparse Master := [(Sum.inr 2513, (1 / 1))]

def nodeValue2514 : Sparse Master := []

def nodeValue2515 : Sparse Master := [(Sum.inr 2515, (1 / 1))]

def nodeValue2516 : Sparse Master := [(Sum.inr 2516, (1 / 1))]

def nodeValue2517 : Sparse Master := []

def nodeValue2519 : Sparse Master := [(Sum.inr 2519, (1 / 1))]

def nodeValue2520 : Sparse Master := [(Sum.inr 2520, (1 / 1))]

def nodeValue2521 : Sparse Master := [(Sum.inr 2521, (1 / 1))]

def nodeValue2522 : Sparse Master := [(Sum.inr 2522, (1 / 1))]

def nodeValue2523 : Sparse Master := []

def nodeValue2524 : Sparse Master := [(Sum.inr 2524, (1 / 1))]

def nodeValue2525 : Sparse Master := [(Sum.inr 2525, (1 / 1))]

def nodeValue2526 : Sparse Master := [(Sum.inl 0, (-7 / 1440)), (Sum.inl 9, (1 / 216)), (Sum.inl 58, (-1 / 864)), (Sum.inl 6, (7 / 864)), (Sum.inl 68, (-1 / 72)), (Sum.inl 2, (1 / 108)), (Sum.inl 69, (1 / 54)), (Sum.inl 71, (1 / 54)), (Sum.inl 7, (1 / 54)), (Sum.inl 8, (1 / 27)), (Sum.inl 126, (-1 / 18)), (Sum.inl 3, (1 / 27)), (Sum.inl 52, (1 / 27)), (Sum.inl 1, (-1 / 288))]

def nodeValue2527 : Sparse Master := [(Sum.inl 0, (-1 / 270)), (Sum.inl 9, (1 / 108)), (Sum.inl 5, (-1 / 216)), (Sum.inl 6, (-1 / 216)), (Sum.inl 68, (-1 / 36)), (Sum.inl 2, (1 / 288)), (Sum.inl 69, (1 / 54)), (Sum.inl 70, (1 / 54)), (Sum.inl 7, (1 / 54)), (Sum.inl 35, (1 / 27)), (Sum.inl 124, (-1 / 18)), (Sum.inl 125, (-1 / 18)), (Sum.inl 3, (1 / 54)), (Sum.inl 13, (1 / 54)), (Sum.inl 23, (-1 / 18)), (Sum.inl 12, (1 / 54)), (Sum.inl 27, (-1 / 72)), (Sum.inl 1, (-7 / 288))]

def nodeValue2528 : Sparse Master := [(Sum.inl 0, (-29 / 4320)), (Sum.inl 9, (1 / 216)), (Sum.inl 58, (-1 / 864)), (Sum.inl 5, (-1 / 54)), (Sum.inl 6, (5 / 432)), (Sum.inl 68, (-1 / 72)), (Sum.inl 69, (1 / 54)), (Sum.inl 70, (1 / 54)), (Sum.inl 7, (1 / 27)), (Sum.inl 35, (2 / 27)), (Sum.inl 125, (-1 / 18)), (Sum.inl 3, (2 / 27)), (Sum.inl 13, (5 / 54)), (Sum.inl 52, (2 / 27)), (Sum.inl 1, (5 / 432))]

def nodeValue2529 : Sparse Master := [(Sum.inr 2529, (1 / 1))]

def nodeValue2530 : Sparse Master := [(Sum.inl 0, (-23 / 4320)), (Sum.inl 9, (1 / 108)), (Sum.inl 5, (-1 / 36)), (Sum.inl 6, (-1 / 216)), (Sum.inl 68, (-1 / 36)), (Sum.inl 2, (29 / 864)), (Sum.inl 69, (1 / 54)), (Sum.inl 71, (1 / 54)), (Sum.inl 7, (2 / 27)), (Sum.inl 8, (2 / 27)), (Sum.inl 124, (-1 / 18)), (Sum.inl 126, (-1 / 18)), (Sum.inl 51, (-1 / 9)), (Sum.inl 3, (1 / 18))]

def nodeValue2531 : Sparse Master := [(Sum.inl 0, (-19 / 4320)), (Sum.inl 9, (-1 / 216)), (Sum.inl 6, (1 / 432)), (Sum.inl 68, (1 / 72)), (Sum.inl 2, (-1 / 216)), (Sum.inl 71, (-1 / 54)), (Sum.inl 8, (-1 / 27)), (Sum.inl 126, (1 / 18)), (Sum.inl 1, (-7 / 864))]

def nodeValue2532 : Sparse Master := [(Sum.inl 0, (-11 / 2160)), (Sum.inl 9, (-1 / 216)), (Sum.inl 5, (-1 / 108)), (Sum.inl 6, (1 / 432)), (Sum.inl 68, (1 / 72)), (Sum.inl 2, (-1 / 216)), (Sum.inl 70, (-1 / 54)), (Sum.inl 7, (-1 / 27)), (Sum.inl 35, (-1 / 27)), (Sum.inl 125, (1 / 18)), (Sum.inl 3, (-1 / 27)), (Sum.inl 13, (-1 / 54)), (Sum.inl 1, (-1 / 36))]

def nodeValue2533 : Sparse Master := [(Sum.inr 2533, (1 / 1))]

def nodeValue2534 : Sparse Master := [(Sum.inr 2534, (1 / 1))]

def nodeValue2535 : Sparse Master := [(Sum.inr 2535, (1 / 1))]

def nodeValue2536 : Sparse Master := [(Sum.inr 2536, (1 / 1))]

def nodeValue2537 : Sparse Master := [(Sum.inr 2537, (1 / 1))]

def nodeValue2538 : Sparse Master := [(Sum.inr 2538, (1 / 1))]

def nodeValue2539 : Sparse Master := [(Sum.inr 2539, (1 / 1))]

def nodeValue2540 : Sparse Master := []

def nodeValue2541 : Sparse Master := [(Sum.inr 2541, (1 / 1))]

def nodeValue2542 : Sparse Master := []

def nodeValue2543 : Sparse Master := [(Sum.inr 2543, (1 / 1))]

def nodeValue2544 : Sparse Master := [(Sum.inr 2544, (1 / 1))]

def nodeValue2545 : Sparse Master := [(Sum.inr 2545, (1 / 1))]

def nodeValue2546 : Sparse Master := []

def nodeValue2547 : Sparse Master := [(Sum.inr 2547, (1 / 1))]

def nodeValue2549 : Sparse Master := [(Sum.inr 2549, (1 / 1))]

def nodeValue2550 : Sparse Master := [(Sum.inr 2550, (1 / 1))]

def nodeValue2551 : Sparse Master := [(Sum.inr 2551, (1 / 1))]

def nodeValue2552 : Sparse Master := []

def nodeValue2553 : Sparse Master := [(Sum.inr 2553, (1 / 1))]

def nodeValue2554 : Sparse Master := []

def nodeValue2555 : Sparse Master := [(Sum.inr 2555, (1 / 1))]

def nodeValue2556 : Sparse Master := [(Sum.inr 2556, (1 / 1))]

def nodeValue2557 : Sparse Master := [(Sum.inr 2557, (1 / 1))]

def nodeValue2558 : Sparse Master := [(Sum.inr 2558, (1 / 1))]

def nodeValue2559 : Sparse Master := [(Sum.inr 2559, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue256 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 5, (-5 / 108)), (Sum.inl 61, (5 / 9)), (Sum.inl 2, (-5 / 108)), (Sum.inl 1, (-5 / 108))]

def nodeValue257 : Sparse Master := [(Sum.inl 0, (23 / 864)), (Sum.inl 32, (-5 / 27)), (Sum.inl 2, (-5 / 72)), (Sum.inl 3, (-5 / 6)), (Sum.inl 13, (-85 / 54)), (Sum.inl 12, (-5 / 9)), (Sum.inl 1, (5 / 96))]

def nodeValue258 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 32, (5 / 27)), (Sum.inl 2, (25 / 144)), (Sum.inl 13, (5 / 9)), (Sum.inl 1, (5 / 48))]

def nodeValue259 : Sparse Master := [(Sum.inl 0, (13 / 432)), (Sum.inl 2, (5 / 54)), (Sum.inl 3, (-10 / 27)), (Sum.inl 13, (-10 / 27)), (Sum.inl 12, (-5 / 54)), (Sum.inl 1, (115 / 432))]

def nodeValue260 : Sparse Master := [(Sum.inl 0, (11 / 288)), (Sum.inl 2, (-5 / 216)), (Sum.inl 3, (5 / 54)), (Sum.inl 13, (5 / 54)), (Sum.inl 1, (-5 / 864))]

def nodeValue261 : Sparse Master := [(Sum.inl 0, (13 / 432)), (Sum.inl 2, (5 / 864)), (Sum.inl 3, (5 / 27)), (Sum.inl 13, (5 / 18)), (Sum.inl 12, (5 / 54)), (Sum.inl 1, (-25 / 864))]

def nodeValue262 : Sparse Master := [(Sum.inl 0, (7 / 216)), (Sum.inl 2, (25 / 144)), (Sum.inl 13, (-5 / 27)), (Sum.inl 1, (-5 / 144))]

def nodeValue263 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 32, (5 / 54)), (Sum.inl 2, (-5 / 108)), (Sum.inl 3, (5 / 27)), (Sum.inl 13, (5 / 9)), (Sum.inl 12, (5 / 27)), (Sum.inl 1, (-35 / 432))]

def nodeValue264 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 32, (-5 / 27)), (Sum.inl 2, (5 / 72)), (Sum.inl 13, (-10 / 27)), (Sum.inl 1, (-5 / 72))]

def nodeValue265 : Sparse Master := []

def nodeValue266 : Sparse Master := []

def nodeValue267 : Sparse Master := []

def nodeValue268 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 2, (-5 / 54)), (Sum.inl 3, (-5 / 27)), (Sum.inl 13, (-5 / 27)), (Sum.inl 1, (-55 / 432))]

def nodeValue269 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 2, (-5 / 72)), (Sum.inl 13, (-10 / 27)), (Sum.inl 12, (-5 / 27)), (Sum.inl 1, (5 / 72))]

def nodeValue270 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 2, (5 / 48)), (Sum.inl 13, (5 / 9)), (Sum.inl 1, (5 / 48))]

def nodeValue271 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 32, (5 / 9)), (Sum.inl 2, (5 / 12))]

def nodeValue272 : Sparse Master := []

def nodeValue273 : Sparse Master := [(Sum.inl 0, (17 / 432)), (Sum.inl 9, (5 / 216)), (Sum.inl 6, (-5 / 864)), (Sum.inl 68, (-5 / 72)), (Sum.inl 2, (5 / 216)), (Sum.inl 71, (5 / 54)), (Sum.inl 8, (5 / 54)), (Sum.inl 1, (-25 / 864)), (Sum.inl 236, (-5 / 18))]

def nodeValue274 : Sparse Master := [(Sum.inl 0, (19 / 864)), (Sum.inl 9, (5 / 216)), (Sum.inl 6, (-5 / 432)), (Sum.inl 68, (-5 / 72)), (Sum.inl 2, (5 / 216)), (Sum.inl 71, (5 / 54)), (Sum.inl 8, (5 / 27)), (Sum.inl 126, (-5 / 18)), (Sum.inl 1, (35 / 864))]

def nodeValue275 : Sparse Master := [(Sum.inl 0, (7 / 216)), (Sum.inl 5, (5 / 216)), (Sum.inl 68, (-5 / 36)), (Sum.inl 2, (5 / 864)), (Sum.inl 7, (5 / 54)), (Sum.inl 126, (-5 / 18)), (Sum.inl 3, (5 / 54)), (Sum.inl 197, (-5 / 18)), (Sum.inl 24, (-5 / 18)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (-25 / 288))]

def nodeValue277 : Sparse Master := [(Sum.inl 0, (7 / 216)), (Sum.inl 68, (5 / 36)), (Sum.inl 2, (5 / 432)), (Sum.inl 126, (5 / 9)), (Sum.inl 1, (-25 / 432))]

def nodeValue278 : Sparse Master := [(Sum.inl 0, (7 / 288)), (Sum.inl 5, (5 / 216)), (Sum.inl 266, (5 / 18)), (Sum.inl 64, (5 / 18)), (Sum.inl 68, (-5 / 36)), (Sum.inl 2, (-5 / 864)), (Sum.inl 7, (-5 / 27)), (Sum.inl 124, (5 / 9)), (Sum.inl 125, (5 / 6)), (Sum.inl 126, (5 / 9)), (Sum.inl 51, (5 / 18)), (Sum.inl 3, (-5 / 27)), (Sum.inl 196, (5 / 18)), (Sum.inl 197, (5 / 18)), (Sum.inl 23, (5 / 9)), (Sum.inl 54, (5 / 18)), (Sum.inl 24, (5 / 18)), (Sum.inl 55, (5 / 18)), (Sum.inl 27, (-5 / 36)), (Sum.inl 1, (-5 / 432))]

def nodeValue279 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 68, (5 / 36)), (Sum.inl 2, (5 / 216)), (Sum.inl 125, (-5 / 9)), (Sum.inl 126, (-5 / 9)), (Sum.inl 1, (-5 / 108))]

def nodeValue280 : Sparse Master := [(Sum.inl 0, (19 / 864)), (Sum.inl 9, (-5 / 216)), (Sum.inl 5, (-5 / 36)), (Sum.inl 6, (5 / 288)), (Sum.inl 259, (5 / 18)), (Sum.inl 266, (5 / 18)), (Sum.inl 64, (5 / 18)), (Sum.inl 68, (25 / 72)), (Sum.inl 2, (5 / 72)), (Sum.inl 7, (-5 / 54)), (Sum.inl 35, (-5 / 54)), (Sum.inl 487, (-5 / 9)), (Sum.inl 123, (5 / 18)), (Sum.inl 124, (5 / 18)), (Sum.inl 125, (5 / 18)), (Sum.inl 51, (5 / 18)), (Sum.inl 3, (-10 / 27)), (Sum.inl 23, (5 / 18)), (Sum.inl 54, (5 / 18)), (Sum.inl 55, (5 / 18)), (Sum.inl 12, (-5 / 54)), (Sum.inl 25, (5 / 18)), (Sum.inl 26, (-5 / 27)), (Sum.inl 4, (-5 / 54)), (Sum.inl 27, (5 / 24)), (Sum.inl 1, (5 / 144))]

def nodeValue281 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 9, (5 / 216)), (Sum.inl 5, (5 / 108)), (Sum.inl 6, (-5 / 432)), (Sum.inl 259, (-5 / 18)), (Sum.inl 68, (-5 / 72)), (Sum.inl 2, (5 / 288)), (Sum.inl 123, (-5 / 18)), (Sum.inl 124, (-5 / 18)), (Sum.inl 51, (-5 / 18)), (Sum.inl 1, (-55 / 864))]

def nodeValue282 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 5, (5 / 216)), (Sum.inl 68, (-5 / 36)), (Sum.inl 2, (5 / 432)), (Sum.inl 487, (5 / 9)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (-25 / 432))]

def nodeValue283 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 9, (-5 / 216)), (Sum.inl 5, (-5 / 72)), (Sum.inl 6, (5 / 288)), (Sum.inl 68, (25 / 72)), (Sum.inl 2, (-25 / 432)), (Sum.inl 69, (-5 / 54)), (Sum.inl 7, (-5 / 27)), (Sum.inl 8, (-5 / 27)), (Sum.inl 124, (5 / 18)), (Sum.inl 126, (10 / 9)), (Sum.inl 51, (5 / 18)), (Sum.inl 3, (-5 / 18)), (Sum.inl 52, (-5 / 54)), (Sum.inl 24, (5 / 9)), (Sum.inl 4, (-5 / 54)), (Sum.inl 27, (5 / 36)), (Sum.inl 1, (55 / 864))]

def nodeValue284 : Sparse Master := [(Sum.inl 0, (1 / 54)), (Sum.inl 9, (5 / 216)), (Sum.inl 6, (-5 / 432)), (Sum.inl 68, (-5 / 72)), (Sum.inl 2, (-5 / 288)), (Sum.inl 69, (5 / 54)), (Sum.inl 7, (5 / 27)), (Sum.inl 124, (-5 / 18)), (Sum.inl 3, (5 / 54)), (Sum.inl 1, (95 / 864))]

def nodeValue285 : Sparse Master := [(Sum.inl 0, (1 / 32)), (Sum.inl 9, (5 / 216)), (Sum.inl 6, (-5 / 432)), (Sum.inl 68, (-5 / 72)), (Sum.inl 2, (35 / 864)), (Sum.inl 69, (5 / 54)), (Sum.inl 7, (5 / 54)), (Sum.inl 126, (-5 / 18)), (Sum.inl 3, (5 / 54)), (Sum.inl 52, (5 / 54)), (Sum.inl 1, (-25 / 432))]

def nodeValue286 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 5, (5 / 216)), (Sum.inl 68, (-5 / 36)), (Sum.inl 2, (5 / 864)), (Sum.inl 7, (5 / 54)), (Sum.inl 124, (-5 / 18)), (Sum.inl 125, (-5 / 18)), (Sum.inl 3, (5 / 54)), (Sum.inl 23, (-5 / 18)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (25 / 288))]

def nodeValue287 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 5, (5 / 216)), (Sum.inl 68, (-5 / 36)), (Sum.inl 2, (-5 / 432)), (Sum.inl 8, (5 / 54)), (Sum.inl 126, (-5 / 9)), (Sum.inl 24, (-5 / 18)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (5 / 432))]

def nodeValue288 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 5, (5 / 216)), (Sum.inl 266, (-5 / 18)), (Sum.inl 64, (-5 / 18)), (Sum.inl 68, (-5 / 36)), (Sum.inl 2, (-5 / 144)), (Sum.inl 125, (-5 / 18)), (Sum.inl 55, (-5 / 18)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (-5 / 72))]

def nodeValue289 : Sparse Master := [(Sum.inl 0, (1 / 32)), (Sum.inl 5, (5 / 216)), (Sum.inl 68, (-5 / 36)), (Sum.inl 2, (5 / 864)), (Sum.inl 124, (-5 / 18)), (Sum.inl 126, (-5 / 18)), (Sum.inl 51, (-5 / 18)), (Sum.inl 1, (-35 / 432))]

def nodeValue290 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 68, (5 / 36)), (Sum.inl 2, (5 / 432)), (Sum.inl 124, (5 / 9)), (Sum.inl 1, (25 / 216))]

def nodeValue291 : Sparse Master := [(Sum.inl 0, (37 / 864)), (Sum.inl 9, (-5 / 216)), (Sum.inl 58, (5 / 864)), (Sum.inl 5, (5 / 108)), (Sum.inl 6, (-5 / 108)), (Sum.inl 68, (5 / 72)), (Sum.inl 2, (5 / 216)), (Sum.inl 71, (-5 / 27)), (Sum.inl 8, (-5 / 27)), (Sum.inl 1, (-5 / 108)), (Sum.inl 236, (5 / 18))]

def nodeValue292 : Sparse Master := [(Sum.inl 0, (17 / 864)), (Sum.inl 9, (-5 / 108)), (Sum.inl 58, (5 / 864)), (Sum.inl 6, (-25 / 864)), (Sum.inl 262, (5 / 18)), (Sum.inl 68, (5 / 72)), (Sum.inl 2, (-65 / 864)), (Sum.inl 69, (-5 / 54)), (Sum.inl 7, (-5 / 54)), (Sum.inl 35, (-5 / 27)), (Sum.inl 126, (5 / 18)), (Sum.inl 51, (5 / 18)), (Sum.inl 3, (-10 / 27)), (Sum.inl 13, (-10 / 27)), (Sum.inl 128, (-5 / 54)), (Sum.inl 495, (-5 / 54)), (Sum.inl 52, (-10 / 27)), (Sum.inl 12, (-5 / 54)), (Sum.inl 1, (-5 / 108))]

def nodeValue293 : Sparse Master := [(Sum.inl 0, (19 / 432)), (Sum.inl 9, (-5 / 108)), (Sum.inl 5, (5 / 54)), (Sum.inl 6, (5 / 288)), (Sum.inl 68, (5 / 36)), (Sum.inl 2, (-25 / 432)), (Sum.inl 69, (-5 / 54)), (Sum.inl 71, (-5 / 54)), (Sum.inl 7, (-5 / 27)), (Sum.inl 8, (-5 / 27)), (Sum.inl 126, (5 / 18)), (Sum.inl 3, (-5 / 27)), (Sum.inl 52, (-5 / 54)), (Sum.inl 1, (-55 / 864)), (Sum.inl 236, (5 / 18))]

def nodeValue294 : Sparse Master := [(Sum.inl 0, (7 / 288)), (Sum.inl 9, (-5 / 216)), (Sum.inl 58, (5 / 864)), (Sum.inl 6, (-35 / 864)), (Sum.inl 68, (5 / 72)), (Sum.inl 2, (-5 / 108)), (Sum.inl 69, (-5 / 54)), (Sum.inl 71, (-5 / 54)), (Sum.inl 7, (-5 / 54)), (Sum.inl 8, (-5 / 27)), (Sum.inl 126, (5 / 18)), (Sum.inl 3, (-5 / 27)), (Sum.inl 52, (-5 / 27)), (Sum.inl 1, (5 / 288))]

def nodeValue295 : Sparse Master := [(Sum.inl 0, (1 / 32)), (Sum.inl 9, (-5 / 108)), (Sum.inl 5, (5 / 108)), (Sum.inl 6, (5 / 288)), (Sum.inl 68, (5 / 36)), (Sum.inl 2, (-5 / 144)), (Sum.inl 69, (-5 / 54)), (Sum.inl 70, (-5 / 54)), (Sum.inl 7, (-5 / 18)), (Sum.inl 35, (-5 / 18)), (Sum.inl 126, (5 / 18)), (Sum.inl 3, (-25 / 54)), (Sum.inl 52, (-5 / 54)), (Sum.inl 197, (5 / 18)), (Sum.inl 24, (5 / 18)), (Sum.inl 26, (-5 / 27)), (Sum.inl 4, (-5 / 54)), (Sum.inl 27, (5 / 72)), (Sum.inl 1, (-5 / 216))]

def nodeValue296 : Sparse Master := [(Sum.inl 0, (17 / 864)), (Sum.inl 9, (-5 / 108)), (Sum.inl 5, (5 / 216)), (Sum.inl 6, (5 / 216)), (Sum.inl 256, (5 / 18)), (Sum.inl 59, (5 / 18)), (Sum.inl 33, (5 / 18)), (Sum.inl 68, (5 / 36)), (Sum.inl 2, (-25 / 288)), (Sum.inl 81, (5 / 18)), (Sum.inl 7, (-5 / 27)), (Sum.inl 35, (-5 / 27)), (Sum.inl 8, (-5 / 54)), (Sum.inl 486, (-5 / 9)), (Sum.inl 51, (5 / 18)), (Sum.inl 3, (-10 / 27)), (Sum.inl 13, (-5 / 54)), (Sum.inl 52, (-5 / 27)), (Sum.inl 12, (-5 / 54)), (Sum.inl 26, (-5 / 54)), (Sum.inl 4, (-5 / 54)), (Sum.inl 27, (5 / 72)), (Sum.inl 1, (-5 / 216))]

def nodeValue297 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 9, (-5 / 108)), (Sum.inl 6, (5 / 216)), (Sum.inl 259, (5 / 18)), (Sum.inl 260, (5 / 18)), (Sum.inl 64, (5 / 9)), (Sum.inl 68, (5 / 36)), (Sum.inl 2, (-5 / 144)), (Sum.inl 7, (-5 / 18)), (Sum.inl 35, (-5 / 54)), (Sum.inl 123, (5 / 18)), (Sum.inl 124, (5 / 18)), (Sum.inl 125, (5 / 18)), (Sum.inl 51, (5 / 9)), (Sum.inl 3, (-25 / 54)), (Sum.inl 13, (-5 / 54)), (Sum.inl 52, (-5 / 54)), (Sum.inl 23, (5 / 18)), (Sum.inl 54, (5 / 9)), (Sum.inl 12, (-5 / 54)), (Sum.inl 25, (5 / 18)), (Sum.inl 26, (-5 / 54)), (Sum.inl 27, (5 / 72)), (Sum.inl 1, (-5 / 432))]

def nodeValue298 : Sparse Master := [(Sum.inl 0, (5 / 288)), (Sum.inl 9, (-5 / 108)), (Sum.inl 5, (-5 / 216)), (Sum.inl 6, (5 / 216)), (Sum.inl 259, (5 / 18)), (Sum.inl 59, (5 / 18)), (Sum.inl 262, (5 / 18)), (Sum.inl 33, (5 / 18)), (Sum.inl 68, (5 / 36)), (Sum.inl 2, (-35 / 864)), (Sum.inl 123, (5 / 18)), (Sum.inl 124, (5 / 18)), (Sum.inl 126, (5 / 18)), (Sum.inl 51, (5 / 9)), (Sum.inl 3, (-5 / 27)), (Sum.inl 13, (-5 / 54)), (Sum.inl 52, (-5 / 54)), (Sum.inl 12, (-5 / 54)), (Sum.inl 1, (5 / 432)), (Sum.inl 31, (5 / 18))]

def nodeValue299 : Sparse Master := [(Sum.inl 0, (1 / 54)), (Sum.inl 5, (5 / 27)), (Sum.inl 6, (-5 / 216)), (Sum.inl 2, (-25 / 432)), (Sum.inl 3, (-10 / 27)), (Sum.inl 13, (-10 / 27)), (Sum.inl 128, (-5 / 54)), (Sum.inl 52, (-10 / 27)), (Sum.inl 12, (-5 / 54)), (Sum.inl 1, (5 / 48))]

def nodeValue300 : Sparse Master := [(Sum.inl 0, (7 / 288)), (Sum.inl 5, (5 / 54)), (Sum.inl 59, (5 / 18)), (Sum.inl 33, (5 / 18)), (Sum.inl 2, (-65 / 432)), (Sum.inl 7, (-10 / 27)), (Sum.inl 35, (-5 / 54)), (Sum.inl 8, (-10 / 27)), (Sum.inl 51, (5 / 9)), (Sum.inl 3, (-5 / 9)), (Sum.inl 13, (-5 / 54)), (Sum.inl 12, (-5 / 54)), (Sum.inl 26, (-5 / 54)), (Sum.inl 1, (65 / 864))]

def nodeValue301 : Sparse Master := [(Sum.inl 0, (37 / 864)), (Sum.inl 5, (25 / 216)), (Sum.inl 6, (-5 / 216)), (Sum.inl 2, (5 / 54)), (Sum.inl 7, (-5 / 27)), (Sum.inl 35, (-5 / 54)), (Sum.inl 3, (-10 / 27)), (Sum.inl 26, (-5 / 27)), (Sum.inl 1, (-5 / 864))]

def nodeValue302 : Sparse Master := [(Sum.inl 0, (23 / 864)), (Sum.inl 5, (5 / 36)), (Sum.inl 6, (-5 / 288)), (Sum.inl 2, (-35 / 432)), (Sum.inl 8, (-5 / 27)), (Sum.inl 3, (-5 / 27)), (Sum.inl 52, (-5 / 54)), (Sum.inl 1, (5 / 48))]

def nodeValue303 : Sparse Master := [(Sum.inl 0, (17 / 432)), (Sum.inl 5, (-5 / 108)), (Sum.inl 6, (5 / 216)), (Sum.inl 2, (-5 / 144)), (Sum.inl 1, (-5 / 216))]

def nodeValue304 : Sparse Master := [(Sum.inl 0, (19 / 864)), (Sum.inl 5, (5 / 54)), (Sum.inl 6, (-5 / 432)), (Sum.inl 2, (-5 / 96)), (Sum.inl 7, (-5 / 27)), (Sum.inl 35, (-5 / 27)), (Sum.inl 3, (-5 / 18)), (Sum.inl 52, (-5 / 27)), (Sum.inl 26, (-5 / 27)), (Sum.inl 4, (-5 / 27)), (Sum.inl 1, (5 / 144))]

def nodeValue305 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 5, (-5 / 108)), (Sum.inl 6, (5 / 288)), (Sum.inl 2, (-5 / 288)), (Sum.inl 3, (5 / 54)), (Sum.inl 52, (5 / 54)), (Sum.inl 1, (5 / 432))]

def nodeValue306 : Sparse Master := [(Sum.inl 0, (1 / 32)), (Sum.inl 5, (-5 / 72)), (Sum.inl 2, (55 / 864)), (Sum.inl 7, (5 / 27)), (Sum.inl 35, (5 / 54)), (Sum.inl 3, (5 / 18)), (Sum.inl 26, (5 / 54)), (Sum.inl 1, (-5 / 72))]

def nodeValue307 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 5, (-5 / 54)), (Sum.inl 2, (5 / 72)), (Sum.inl 8, (5 / 27)), (Sum.inl 1, (25 / 216))]

def nodeValue308 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 6, (5 / 432)), (Sum.inl 2, (5 / 216)), (Sum.inl 3, (5 / 27)), (Sum.inl 13, (10 / 27)), (Sum.inl 128, (5 / 54)), (Sum.inl 52, (5 / 27)), (Sum.inl 12, (5 / 54)), (Sum.inl 1, (-5 / 432))]

def nodeValue309 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 5, (-5 / 108)), (Sum.inl 59, (-5 / 18)), (Sum.inl 33, (-5 / 18)), (Sum.inl 2, (5 / 108)), (Sum.inl 51, (-5 / 18)), (Sum.inl 3, (5 / 54)), (Sum.inl 13, (5 / 54)), (Sum.inl 12, (5 / 54)), (Sum.inl 1, (-5 / 216))]

def nodeValue310 : Sparse Master := [(Sum.inl 0, (37 / 864)), (Sum.inl 5, (-5 / 216)), (Sum.inl 6, (5 / 432)), (Sum.inl 2, (-5 / 54)), (Sum.inl 35, (-5 / 54)), (Sum.inl 3, (-10 / 27)), (Sum.inl 52, (-5 / 27)), (Sum.inl 26, (-5 / 27)), (Sum.inl 4, (-5 / 27)), (Sum.inl 1, (-25 / 288))]

def nodeValue311 : Sparse Master := [(Sum.inl 0, (19 / 432)), (Sum.inl 5, (5 / 216)), (Sum.inl 2, (-65 / 864)), (Sum.inl 35, (5 / 54)), (Sum.inl 3, (5 / 54)), (Sum.inl 26, (5 / 27)), (Sum.inl 1, (-55 / 864))]

def nodeValue312 : Sparse Master := [(Sum.inl 0, (11 / 288)), (Sum.inl 6, (-5 / 864)), (Sum.inl 2, (35 / 432)), (Sum.inl 3, (5 / 27)), (Sum.inl 52, (5 / 54)), (Sum.inl 1, (5 / 432))]

def nodeValue313 : Sparse Master := [(Sum.inl 0, (23 / 864)), (Sum.inl 5, (5 / 216)), (Sum.inl 6, (-5 / 864)), (Sum.inl 60, (5 / 54)), (Sum.inl 34, (5 / 27)), (Sum.inl 2, (-5 / 432)), (Sum.inl 35, (5 / 54)), (Sum.inl 3, (5 / 18)), (Sum.inl 13, (5 / 18)), (Sum.inl 12, (5 / 54)), (Sum.inl 26, (5 / 54)), (Sum.inl 1, (-5 / 108))]

def nodeValue314 : Sparse Master := [(Sum.inl 0, (7 / 216)), (Sum.inl 5, (5 / 216)), (Sum.inl 6, (-5 / 864)), (Sum.inl 2, (5 / 144)), (Sum.inl 35, (5 / 54)), (Sum.inl 52, (5 / 54)), (Sum.inl 26, (5 / 54)), (Sum.inl 4, (5 / 54)), (Sum.inl 1, (-5 / 96))]

def nodeValue315 : Sparse Master := [(Sum.inl 0, (7 / 216)), (Sum.inl 6, (5 / 432)), (Sum.inl 2, (-5 / 144)), (Sum.inl 3, (-5 / 27)), (Sum.inl 52, (-5 / 27)), (Sum.inl 1, (-5 / 72))]

def nodeValue316 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 5, (-5 / 108)), (Sum.inl 2, (-5 / 432)), (Sum.inl 35, (-5 / 27)), (Sum.inl 3, (-5 / 27)), (Sum.inl 26, (-5 / 27)), (Sum.inl 1, (-5 / 108))]

def nodeValue317 : Sparse Master := [(Sum.inl 0, (1 / 54)), (Sum.inl 9, (-5 / 108)), (Sum.inl 5, (5 / 216)), (Sum.inl 6, (5 / 216)), (Sum.inl 68, (5 / 36)), (Sum.inl 2, (-5 / 288)), (Sum.inl 69, (-5 / 54)), (Sum.inl 70, (-5 / 54)), (Sum.inl 7, (-5 / 54)), (Sum.inl 35, (-5 / 27)), (Sum.inl 124, (5 / 18)), (Sum.inl 125, (5 / 18)), (Sum.inl 3, (-5 / 54)), (Sum.inl 13, (-5 / 54)), (Sum.inl 23, (5 / 18)), (Sum.inl 12, (-5 / 54)), (Sum.inl 27, (5 / 72)), (Sum.inl 1, (35 / 288))]

def nodeValue318 : Sparse Master := [(Sum.inl 0, (23 / 864)), (Sum.inl 9, (-5 / 108)), (Sum.inl 5, (5 / 36)), (Sum.inl 6, (5 / 216)), (Sum.inl 68, (5 / 36)), (Sum.inl 2, (-145 / 864)), (Sum.inl 69, (-5 / 54)), (Sum.inl 71, (-5 / 54)), (Sum.inl 7, (-10 / 27)), (Sum.inl 8, (-10 / 27)), (Sum.inl 124, (5 / 18)), (Sum.inl 126, (5 / 18)), (Sum.inl 51, (5 / 9)), (Sum.inl 3, (-5 / 18))]

def nodeValue319 : Sparse Master := [(Sum.inl 0, (1 / 72)), (Sum.inl 5, (5 / 54)), (Sum.inl 6, (-5 / 432)), (Sum.inl 2, (-5 / 108)), (Sum.inl 35, (-5 / 27)), (Sum.inl 3, (-10 / 27)), (Sum.inl 13, (-10 / 27)), (Sum.inl 52, (-10 / 27)), (Sum.inl 1, (35 / 432))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue2560 : Sparse Master := [(Sum.inr 2560, (1 / 1))]

def nodeValue2561 : Sparse Master := [(Sum.inr 2561, (1 / 1))]

def nodeValue2562 : Sparse Master := [(Sum.inr 2562, (1 / 1))]

def nodeValue2564 : Sparse Master := [(Sum.inr 2564, (1 / 1))]

def nodeValue2565 : Sparse Master := [(Sum.inr 2565, (1 / 1))]

def nodeValue2566 : Sparse Master := [(Sum.inr 2566, (1 / 1))]

def nodeValue2567 : Sparse Master := [(Sum.inr 2567, (1 / 1))]

def nodeValue2568 : Sparse Master := [(Sum.inr 2568, (1 / 1))]

def nodeValue2569 : Sparse Master := [(Sum.inr 2569, (1 / 1))]

def nodeValue2570 : Sparse Master := [(Sum.inl 0, (-23 / 4320)), (Sum.inl 5, (-1 / 54)), (Sum.inl 6, (1 / 432)), (Sum.inl 2, (13 / 864)), (Sum.inl 7, (1 / 27)), (Sum.inl 35, (1 / 54)), (Sum.inl 8, (1 / 54)), (Sum.inl 51, (-1 / 18)), (Sum.inl 3, (2 / 27)), (Sum.inl 13, (1 / 27)), (Sum.inl 52, (1 / 54)), (Sum.inl 12, (1 / 27)), (Sum.inl 1, (-7 / 432))]

def nodeValue2571 : Sparse Master := [(Sum.inr 2571, (1 / 1))]

def nodeValue2572 : Sparse Master := [(Sum.inl 0, (-1 / 216)), (Sum.inl 5, (1 / 108)), (Sum.inl 6, (-1 / 288)), (Sum.inl 2, (1 / 288)), (Sum.inl 3, (-1 / 54)), (Sum.inl 52, (-1 / 54)), (Sum.inl 1, (-1 / 432))]

def nodeValue2573 : Sparse Master := [(Sum.inr 2573, (1 / 1))]

def nodeValue2574 : Sparse Master := [(Sum.inl 0, (-1 / 160)), (Sum.inl 5, (1 / 216)), (Sum.inl 6, (-1 / 288)), (Sum.inl 2, (-1 / 864)), (Sum.inl 35, (-1 / 54)), (Sum.inl 3, (-1 / 54)), (Sum.inl 13, (-1 / 27)), (Sum.inl 52, (-1 / 54)), (Sum.inl 1, (-7 / 864))]

def nodeValue2575 : Sparse Master := [(Sum.inr 2575, (1 / 1))]

def nodeValue2576 : Sparse Master := [(Sum.inl 0, (-19 / 4320)), (Sum.inl 5, (1 / 72)), (Sum.inl 2, (-1 / 108)), (Sum.inl 7, (-1 / 54)), (Sum.inl 8, (-1 / 54)), (Sum.inl 51, (1 / 18)), (Sum.inl 3, (-1 / 54)), (Sum.inl 1, (-5 / 864))]

def nodeValue2577 : Sparse Master := [(Sum.inr 2577, (1 / 1))]

def nodeValue2578 : Sparse Master := [(Sum.inr 2578, (1 / 1))]

def nodeValue2579 : Sparse Master := [(Sum.inr 2579, (1 / 1))]

def nodeValue2580 : Sparse Master := [(Sum.inr 2580, (1 / 1))]

def nodeValue2582 : Sparse Master := [(Sum.inr 2582, (1 / 1))]

def nodeValue2583 : Sparse Master := [(Sum.inr 2583, (1 / 1))]

def nodeValue2584 : Sparse Master := [(Sum.inr 2584, (1 / 1))]

def nodeValue2585 : Sparse Master := [(Sum.inr 2585, (1 / 1))]

def nodeValue2587 : Sparse Master := [(Sum.inr 2587, (1 / 1))]

def nodeValue2588 : Sparse Master := [(Sum.inr 2588, (1 / 1))]

def nodeValue2589 : Sparse Master := [(Sum.inr 2589, (1 / 1))]

def nodeValue2590 : Sparse Master := [(Sum.inr 2590, (1 / 1))]

def nodeValue2591 : Sparse Master := [(Sum.inr 2591, (1 / 1))]

def nodeValue2592 : Sparse Master := [(Sum.inr 2592, (1 / 1))]

def nodeValue2593 : Sparse Master := [(Sum.inl 0, (-49 / 4320)), (Sum.inl 6, (-1 / 288)), (Sum.inl 2, (11 / 432)), (Sum.inl 7, (1 / 54)), (Sum.inl 8, (1 / 27)), (Sum.inl 3, (1 / 27)), (Sum.inl 1, (7 / 432))]

def nodeValue2594 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 6, (1 / 864)), (Sum.inl 2, (1 / 864)), (Sum.inl 7, (-1 / 54)), (Sum.inl 3, (-1 / 54)), (Sum.inl 1, (-19 / 432))]

def nodeValue2595 : Sparse Master := [(Sum.inl 0, (-47 / 4320)), (Sum.inl 6, (1 / 864)), (Sum.inl 2, (-1 / 144)), (Sum.inl 8, (-1 / 54)), (Sum.inl 1, (1 / 216))]

def nodeValue2596 : Sparse Master := [(Sum.inl 0, (-1 / 270)), (Sum.inl 5, (-1 / 216)), (Sum.inl 6, (1 / 864)), (Sum.inl 2, (-1 / 864)), (Sum.inl 7, (-1 / 54)), (Sum.inl 35, (-1 / 54)), (Sum.inl 13, (-1 / 54)), (Sum.inl 12, (-1 / 54)), (Sum.inl 1, (-13 / 432))]

def nodeValue2597 : Sparse Master := [(Sum.inr 2597, (1 / 1))]

def nodeValue2598 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 5, (-1 / 108)), (Sum.inl 6, (-1 / 432)), (Sum.inl 1, (-5 / 108))]

def nodeValue2599 : Sparse Master := [(Sum.inl 0, (-37 / 4320)), (Sum.inl 6, (1 / 864)), (Sum.inl 2, (-5 / 432)), (Sum.inl 7, (-1 / 54)), (Sum.inl 3, (-1 / 27)), (Sum.inl 1, (7 / 432))]

def nodeValue2600 : Sparse Master := [(Sum.inr 2600, (1 / 1))]

def nodeValue2601 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 5, (-1 / 108)), (Sum.inl 6, (-1 / 432)), (Sum.inl 2, (1 / 72)), (Sum.inl 1, (5 / 216))]

def nodeValue2602 : Sparse Master := [(Sum.inl 0, (-11 / 2160)), (Sum.inl 6, (-1 / 432)), (Sum.inl 35, (1 / 27)), (Sum.inl 3, (1 / 27)), (Sum.inl 13, (1 / 27)), (Sum.inl 1, (-1 / 27))]

def nodeValue2603 : Sparse Master := [(Sum.inr 2603, (1 / 1))]

def nodeValue2604 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 5, (1 / 108)), (Sum.inl 2, (-1 / 432)), (Sum.inl 7, (1 / 27)), (Sum.inl 3, (1 / 27)), (Sum.inl 1, (-7 / 216))]

def nodeValue2605 : Sparse Master := [(Sum.inl 0, (-1 / 90)), (Sum.inl 5, (1 / 108)), (Sum.inl 8, (1 / 27)), (Sum.inl 1, (1 / 108))]

def nodeValue2606 : Sparse Master := [(Sum.inr 2606, (1 / 1))]

def nodeValue2607 : Sparse Master := [(Sum.inr 2607, (1 / 1))]

def nodeValue2608 : Sparse Master := [(Sum.inr 2608, (1 / 1))]

def nodeValue2609 : Sparse Master := [(Sum.inr 2609, (1 / 1))]

def nodeValue2610 : Sparse Master := [(Sum.inr 2610, (1 / 1))]

def nodeValue2611 : Sparse Master := [(Sum.inr 2611, (1 / 1))]

def nodeValue2612 : Sparse Master := [(Sum.inr 2612, (1 / 1))]

def nodeValue2613 : Sparse Master := [(Sum.inr 2613, (1 / 1))]

def nodeValue2614 : Sparse Master := [(Sum.inr 2614, (1 / 1))]

def nodeValue2615 : Sparse Master := [(Sum.inr 2615, (1 / 1))]

def nodeValue2616 : Sparse Master := [(Sum.inr 2616, (1 / 1))]

def nodeValue2617 : Sparse Master := [(Sum.inr 2617, (1 / 1))]

def nodeValue2618 : Sparse Master := [(Sum.inr 2618, (1 / 1))]

def nodeValue2619 : Sparse Master := [(Sum.inr 2619, (1 / 1))]

def nodeValue2620 : Sparse Master := [(Sum.inr 2620, (1 / 1))]

def nodeValue2621 : Sparse Master := [(Sum.inr 2621, (1 / 1))]

def nodeValue2622 : Sparse Master := [(Sum.inr 2622, (1 / 1))]

def nodeValue2623 : Sparse Master := [(Sum.inr 2623, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue2624 : Sparse Master := [(Sum.inr 2624, (1 / 1))]

def nodeValue2625 : Sparse Master := [(Sum.inr 2625, (1 / 1))]

def nodeValue2627 : Sparse Master := [(Sum.inr 2627, (1 / 1))]

def nodeValue2628 : Sparse Master := [(Sum.inr 2628, (1 / 1))]

def nodeValue2629 : Sparse Master := [(Sum.inr 2629, (1 / 1))]

def nodeValue2630 : Sparse Master := [(Sum.inr 2630, (1 / 1))]

def nodeValue2631 : Sparse Master := [(Sum.inr 2631, (1 / 1))]

def nodeValue2632 : Sparse Master := [(Sum.inr 2632, (1 / 1))]

def nodeValue2633 : Sparse Master := [(Sum.inr 2633, (1 / 1))]

def nodeValue2634 : Sparse Master := [(Sum.inr 2634, (1 / 1))]

def nodeValue2635 : Sparse Master := [(Sum.inr 2635, (1 / 1))]

def nodeValue2636 : Sparse Master := [(Sum.inl 0, (-5 / 864)), (Sum.inl 5, (1 / 72)), (Sum.inl 6, (-1 / 288)), (Sum.inl 2, (5 / 144)), (Sum.inl 51, (-1 / 6)), (Sum.inl 3, (1 / 6)), (Sum.inl 13, (1 / 27)), (Sum.inl 52, (1 / 18)), (Sum.inl 12, (1 / 18)), (Sum.inl 4, (1 / 18)), (Sum.inl 1, (-1 / 144))]

def nodeValue2637 : Sparse Master := [(Sum.inl 0, (-1 / 216)), (Sum.inl 5, (-1 / 216)), (Sum.inl 6, (1 / 864)), (Sum.inl 2, (-5 / 864)), (Sum.inl 51, (1 / 18)), (Sum.inl 3, (-1 / 27)), (Sum.inl 52, (-1 / 54)), (Sum.inl 4, (-1 / 54)), (Sum.inl 1, (-1 / 432))]

def nodeValue2638 : Sparse Master := [(Sum.inl 0, (-1 / 160)), (Sum.inl 5, (-1 / 216)), (Sum.inl 6, (1 / 864)), (Sum.inl 2, (-1 / 108)), (Sum.inl 51, (1 / 18)), (Sum.inl 3, (-1 / 27)), (Sum.inl 13, (-1 / 54)), (Sum.inl 52, (-1 / 54)), (Sum.inl 12, (-1 / 54)), (Sum.inl 1, (5 / 432))]

def nodeValue2639 : Sparse Master := [(Sum.inr 2639, (1 / 1))]

def nodeValue2640 : Sparse Master := [(Sum.inl 0, (-7 / 1080)), (Sum.inl 6, (-1 / 432)), (Sum.inl 2, (1 / 144)), (Sum.inl 3, (1 / 27)), (Sum.inl 52, (1 / 27)), (Sum.inl 1, (1 / 72))]

def nodeValue2641 : Sparse Master := [(Sum.inr 2641, (1 / 1))]

def nodeValue2642 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 6, (-1 / 432)), (Sum.inl 2, (7 / 432)), (Sum.inl 13, (1 / 27)), (Sum.inl 52, (1 / 27)), (Sum.inl 1, (7 / 432))]

def nodeValue2643 : Sparse Master := [(Sum.inr 2643, (1 / 1))]

def nodeValue2644 : Sparse Master := [(Sum.inl 0, (-7 / 1080)), (Sum.inl 5, (1 / 108)), (Sum.inl 2, (-1 / 144)), (Sum.inl 51, (-1 / 9)), (Sum.inl 1, (1 / 144))]

def nodeValue2645 : Sparse Master := [(Sum.inr 2645, (1 / 1))]

def nodeValue2647 : Sparse Master := [(Sum.inr 2647, (1 / 1))]

def nodeValue2649 : Sparse Master := [(Sum.inr 2649, (1 / 1))]

def nodeValue2650 : Sparse Master := [(Sum.inr 2650, (1 / 1))]

def nodeValue2651 : Sparse Master := [(Sum.inr 2651, (1 / 1))]

def nodeValue2652 : Sparse Master := [(Sum.inr 2652, (1 / 1))]

def nodeValue2653 : Sparse Master := [(Sum.inr 2653, (1 / 1))]

def nodeValue2654 : Sparse Master := [(Sum.inr 2654, (1 / 1))]

def nodeValue2655 : Sparse Master := [(Sum.inr 2655, (1 / 1))]

def nodeValue2656 : Sparse Master := [(Sum.inr 2656, (1 / 1))]

def nodeValue2657 : Sparse Master := [(Sum.inr 2657, (1 / 1))]

def nodeValue2658 : Sparse Master := [(Sum.inr 2658, (1 / 1))]

def nodeValue2659 : Sparse Master := [(Sum.inr 2659, (1 / 1))]

def nodeValue2661 : Sparse Master := [(Sum.inr 2661, (1 / 1))]

def nodeValue2662 : Sparse Master := [(Sum.inr 2662, (1 / 1))]

def nodeValue2664 : Sparse Master := [(Sum.inr 2664, (1 / 1))]

def nodeValue2665 : Sparse Master := [(Sum.inr 2665, (1 / 1))]

def nodeValue2668 : Sparse Master := [(Sum.inr 2668, (1 / 1))]

def nodeValue2669 : Sparse Master := [(Sum.inr 2669, (1 / 1))]

def nodeValue2670 : Sparse Master := [(Sum.inr 2670, (1 / 1))]

def nodeValue2671 : Sparse Master := [(Sum.inr 2671, (1 / 1))]

def nodeValue2672 : Sparse Master := [(Sum.inr 2672, (1 / 1))]

def nodeValue2673 : Sparse Master := [(Sum.inr 2673, (1 / 1))]

def nodeValue2674 : Sparse Master := [(Sum.inr 2674, (1 / 1))]

def nodeValue2675 : Sparse Master := [(Sum.inr 2675, (1 / 1))]

def nodeValue2676 : Sparse Master := [(Sum.inr 2676, (1 / 1))]

def nodeValue2677 : Sparse Master := [(Sum.inr 2677, (1 / 1))]

def nodeValue2678 : Sparse Master := [(Sum.inr 2678, (1 / 1))]

def nodeValue2680 : Sparse Master := [(Sum.inr 2680, (1 / 1))]

def nodeValue2681 : Sparse Master := [(Sum.inr 2681, (1 / 1))]

def nodeValue2682 : Sparse Master := [(Sum.inr 2682, (1 / 1))]

def nodeValue2683 : Sparse Master := [(Sum.inr 2683, (1 / 1))]

def nodeValue2684 : Sparse Master := [(Sum.inr 2684, (1 / 1))]

def nodeValue2685 : Sparse Master := [(Sum.inr 2685, (1 / 1))]

def nodeValue2686 : Sparse Master := [(Sum.inr 2686, (1 / 1))]

def nodeValue2687 : Sparse Master := [(Sum.inr 2687, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue2688 : Sparse Master := [(Sum.inr 2688, (1 / 1))]

def nodeValue2689 : Sparse Master := []

def nodeValue2690 : Sparse Master := [(Sum.inr 2690, (1 / 1))]

def nodeValue2691 : Sparse Master := []

def nodeValue2693 : Sparse Master := []

def nodeValue2694 : Sparse Master := [(Sum.inr 2694, (1 / 1))]

def nodeValue2695 : Sparse Master := []

def nodeValue2697 : Sparse Master := [(Sum.inr 2697, (1 / 1))]

def nodeValue2698 : Sparse Master := [(Sum.inr 2698, (1 / 1))]

def nodeValue2700 : Sparse Master := [(Sum.inr 2700, (1 / 1))]

def nodeValue2701 : Sparse Master := []

def nodeValue2702 : Sparse Master := [(Sum.inr 2702, (1 / 1))]

def nodeValue2703 : Sparse Master := [(Sum.inr 2703, (1 / 1))]

def nodeValue2704 : Sparse Master := [(Sum.inr 2704, (1 / 1))]

def nodeValue2705 : Sparse Master := [(Sum.inr 2705, (1 / 1))]

def nodeValue2706 : Sparse Master := [(Sum.inr 2706, (1 / 1))]

def nodeValue2707 : Sparse Master := [(Sum.inr 2707, (1 / 1))]

def nodeValue2708 : Sparse Master := [(Sum.inr 2708, (1 / 1))]

def nodeValue2709 : Sparse Master := []

def nodeValue2710 : Sparse Master := [(Sum.inr 2710, (1 / 1))]

def nodeValue2712 : Sparse Master := [(Sum.inr 2712, (1 / 1))]

def nodeValue2713 : Sparse Master := [(Sum.inr 2713, (1 / 1))]

def nodeValue2714 : Sparse Master := [(Sum.inr 2714, (1 / 1))]

def nodeValue2716 : Sparse Master := [(Sum.inr 2716, (1 / 1))]

def nodeValue2717 : Sparse Master := [(Sum.inr 2717, (1 / 1))]

def nodeValue2718 : Sparse Master := [(Sum.inr 2718, (1 / 1))]

def nodeValue2719 : Sparse Master := [(Sum.inr 2719, (1 / 1))]

def nodeValue2720 : Sparse Master := []

def nodeValue2721 : Sparse Master := [(Sum.inr 2721, (1 / 1))]

def nodeValue2722 : Sparse Master := [(Sum.inr 2722, (1 / 1))]

def nodeValue2723 : Sparse Master := [(Sum.inr 2723, (1 / 1))]

def nodeValue2724 : Sparse Master := [(Sum.inr 2724, (1 / 1))]

def nodeValue2726 : Sparse Master := [(Sum.inr 2726, (1 / 1))]

def nodeValue2727 : Sparse Master := [(Sum.inr 2727, (1 / 1))]

def nodeValue2728 : Sparse Master := [(Sum.inr 2728, (1 / 1))]

def nodeValue2729 : Sparse Master := [(Sum.inr 2729, (1 / 1))]

def nodeValue2730 : Sparse Master := [(Sum.inr 2730, (1 / 1))]

def nodeValue2731 : Sparse Master := [(Sum.inr 2731, (1 / 1))]

def nodeValue2732 : Sparse Master := [(Sum.inr 2732, (1 / 1))]

def nodeValue2734 : Sparse Master := [(Sum.inr 2734, (1 / 1))]

def nodeValue2735 : Sparse Master := [(Sum.inr 2735, (1 / 1))]

def nodeValue2736 : Sparse Master := [(Sum.inr 2736, (1 / 1))]

def nodeValue2737 : Sparse Master := [(Sum.inr 2737, (1 / 1))]

def nodeValue2738 : Sparse Master := [(Sum.inr 2738, (1 / 1))]

def nodeValue2739 : Sparse Master := [(Sum.inr 2739, (1 / 1))]

def nodeValue2740 : Sparse Master := [(Sum.inr 2740, (1 / 1))]

def nodeValue2741 : Sparse Master := []

def nodeValue2742 : Sparse Master := []

def nodeValue2743 : Sparse Master := [(Sum.inr 2743, (1 / 1))]

def nodeValue2744 : Sparse Master := [(Sum.inr 2744, (1 / 1))]

def nodeValue2745 : Sparse Master := [(Sum.inr 2745, (1 / 1))]

def nodeValue2746 : Sparse Master := [(Sum.inr 2746, (1 / 1))]

def nodeValue2747 : Sparse Master := [(Sum.inr 2747, (1 / 1))]

def nodeValue2748 : Sparse Master := [(Sum.inr 2748, (1 / 1))]

def nodeValue2749 : Sparse Master := [(Sum.inr 2749, (1 / 1))]

def nodeValue2750 : Sparse Master := [(Sum.inr 2750, (1 / 1))]

def nodeValue2751 : Sparse Master := [(Sum.inr 2751, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue2752 : Sparse Master := []

def nodeValue2753 : Sparse Master := [(Sum.inl 0, (-1 / 240)), (Sum.inl 2, (5 / 864)), (Sum.inl 3, (-1 / 27)), (Sum.inl 13, (-1 / 54)), (Sum.inl 12, (-1 / 54)), (Sum.inl 1, (11 / 864))]

def nodeValue2754 : Sparse Master := [(Sum.inr 2754, (1 / 1))]

def nodeValue2755 : Sparse Master := [(Sum.inl 0, (-7 / 1080)), (Sum.inl 2, (-5 / 144)), (Sum.inl 13, (1 / 27)), (Sum.inl 1, (1 / 144))]

def nodeValue2756 : Sparse Master := [(Sum.inr 2756, (1 / 1))]

def nodeValue2757 : Sparse Master := [(Sum.inr 2757, (1 / 1))]

def nodeValue2758 : Sparse Master := [(Sum.inr 2758, (1 / 1))]

def nodeValue2759 : Sparse Master := [(Sum.inr 2759, (1 / 1))]

def nodeValue2760 : Sparse Master := [(Sum.inr 2760, (1 / 1))]

def nodeValue2761 : Sparse Master := [(Sum.inr 2761, (1 / 1))]

def nodeValue2762 : Sparse Master := [(Sum.inr 2762, (1 / 1))]

def nodeValue2763 : Sparse Master := [(Sum.inr 2763, (1 / 1))]

def nodeValue2764 : Sparse Master := [(Sum.inr 2764, (1 / 1))]

def nodeValue2765 : Sparse Master := [(Sum.inr 2765, (1 / 1))]

def nodeValue2766 : Sparse Master := [(Sum.inl 0, (-47 / 4320)), (Sum.inl 2, (-11 / 864)), (Sum.inl 3, (-1 / 54)), (Sum.inl 1, (1 / 216))]

def nodeValue2767 : Sparse Master := [(Sum.inl 0, (-1 / 90)), (Sum.inl 2, (1 / 72)), (Sum.inl 1, (1 / 72))]

def nodeValue2768 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 2, (5 / 432)), (Sum.inl 3, (1 / 27)), (Sum.inl 1, (1 / 54))]

def nodeValue2769 : Sparse Master := [(Sum.inr 2769, (1 / 1))]

def nodeValue2770 : Sparse Master := [(Sum.inl 0, (-1 / 120)), (Sum.inl 2, (-1 / 24))]

def nodeValue2771 : Sparse Master := [(Sum.inr 2771, (1 / 1))]

def nodeValue2772 : Sparse Master := [(Sum.inr 2772, (1 / 1))]

def nodeValue2773 : Sparse Master := [(Sum.inr 2773, (1 / 1))]

def nodeValue2774 : Sparse Master := [(Sum.inr 2774, (1 / 1))]

def nodeValue2775 : Sparse Master := [(Sum.inl 0, (-11 / 4320)), (Sum.inl 2, (-1 / 288)), (Sum.inl 3, (-1 / 18)), (Sum.inl 13, (-1 / 27)), (Sum.inl 12, (-1 / 18)), (Sum.inl 1, (-1 / 36))]

def nodeValue2776 : Sparse Master := [(Sum.inl 0, (-11 / 2160)), (Sum.inl 2, (1 / 216)), (Sum.inl 3, (1 / 27)), (Sum.inl 13, (1 / 27)), (Sum.inl 12, (1 / 27)), (Sum.inl 1, (-7 / 432))]

def nodeValue2777 : Sparse Master := [(Sum.inr 2777, (1 / 1))]

def nodeValue2778 : Sparse Master := [(Sum.inl 0, (-1 / 180)), (Sum.inl 2, (-1 / 48)), (Sum.inl 13, (-1 / 9)), (Sum.inl 1, (-1 / 48))]

def nodeValue2779 : Sparse Master := [(Sum.inr 2779, (1 / 1))]

def nodeValue2780 : Sparse Master := [(Sum.inr 2780, (1 / 1))]

def nodeValue2781 : Sparse Master := [(Sum.inr 2781, (1 / 1))]

def nodeValue2782 : Sparse Master := [(Sum.inr 2782, (1 / 1))]

def nodeValue2783 : Sparse Master := [(Sum.inr 2783, (1 / 1))]

def nodeValue2784 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 2, (-1 / 432)), (Sum.inl 3, (1 / 27)), (Sum.inl 1, (-11 / 216))]

def nodeValue2785 : Sparse Master := []

def nodeValue2786 : Sparse Master := []

def nodeValue2787 : Sparse Master := []

def nodeValue2788 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 2, (1 / 144)), (Sum.inl 3, (-1 / 9)), (Sum.inl 1, (-1 / 72))]

def nodeValue2789 : Sparse Master := [(Sum.inr 2789, (1 / 1))]

def nodeValue2790 : Sparse Master := []

def nodeValue2796 : Sparse Master := [(Sum.inr 2796, (1 / 1))]

def nodeValue2797 : Sparse Master := [(Sum.inr 2797, (1 / 1))]

def nodeValue2798 : Sparse Master := [(Sum.inr 2798, (1 / 1))]

def nodeValue2799 : Sparse Master := [(Sum.inr 2799, (1 / 1))]

def nodeValue2800 : Sparse Master := [(Sum.inr 2800, (1 / 1))]

def nodeValue2801 : Sparse Master := [(Sum.inr 2801, (1 / 1))]

def nodeValue2802 : Sparse Master := [(Sum.inr 2802, (1 / 1))]

def nodeValue2803 : Sparse Master := [(Sum.inr 2803, (1 / 1))]

def nodeValue2804 : Sparse Master := [(Sum.inr 2804, (1 / 1))]

def nodeValue2806 : Sparse Master := [(Sum.inr 2806, (1 / 1))]

def nodeValue2807 : Sparse Master := [(Sum.inr 2807, (1 / 1))]

def nodeValue2809 : Sparse Master := [(Sum.inr 2809, (1 / 1))]

def nodeValue2810 : Sparse Master := [(Sum.inr 2810, (1 / 1))]

def nodeValue2811 : Sparse Master := [(Sum.inr 2811, (1 / 1))]

def nodeValue2812 : Sparse Master := [(Sum.inr 2812, (1 / 1))]

def nodeValue2813 : Sparse Master := [(Sum.inr 2813, (1 / 1))]

def nodeValue2814 : Sparse Master := [(Sum.inr 2814, (1 / 1))]

def nodeValue2815 : Sparse Master := [(Sum.inr 2815, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue2816 : Sparse Master := [(Sum.inr 2816, (1 / 1))]

def nodeValue2817 : Sparse Master := [(Sum.inr 2817, (1 / 1))]

def nodeValue2818 : Sparse Master := [(Sum.inr 2818, (1 / 1))]

def nodeValue2819 : Sparse Master := [(Sum.inr 2819, (1 / 1))]

def nodeValue2820 : Sparse Master := [(Sum.inr 2820, (1 / 1))]

def nodeValue2821 : Sparse Master := [(Sum.inr 2821, (1 / 1))]

def nodeValue2822 : Sparse Master := [(Sum.inr 2822, (1 / 1))]

def nodeValue2824 : Sparse Master := [(Sum.inr 2824, (1 / 1))]

def nodeValue2826 : Sparse Master := [(Sum.inr 2826, (1 / 1))]

def nodeValue2827 : Sparse Master := [(Sum.inr 2827, (1 / 1))]

def nodeValue2828 : Sparse Master := [(Sum.inl 0, (-17 / 2160)), (Sum.inl 9, (-1 / 216)), (Sum.inl 6, (1 / 864)), (Sum.inl 68, (1 / 72)), (Sum.inl 2, (-1 / 216)), (Sum.inl 71, (-1 / 54)), (Sum.inl 8, (-1 / 54)), (Sum.inl 1, (5 / 864)), (Sum.inl 236, (1 / 18))]

def nodeValue2829 : Sparse Master := [(Sum.inl 0, (-7 / 1080)), (Sum.inl 5, (-1 / 216)), (Sum.inl 68, (1 / 36)), (Sum.inl 2, (-1 / 864)), (Sum.inl 7, (-1 / 54)), (Sum.inl 126, (1 / 18)), (Sum.inl 3, (-1 / 54)), (Sum.inl 197, (1 / 18)), (Sum.inl 24, (1 / 18)), (Sum.inl 27, (1 / 72)), (Sum.inl 1, (5 / 288))]

def nodeValue2831 : Sparse Master := [(Sum.inr 2831, (1 / 1))]

def nodeValue2832 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 68, (-1 / 36)), (Sum.inl 2, (1 / 144)), (Sum.inl 197, (-1 / 9)), (Sum.inl 1, (1 / 72))]

def nodeValue2833 : Sparse Master := [(Sum.inr 2833, (1 / 1))]

def nodeValue2834 : Sparse Master := [(Sum.inr 2834, (1 / 1))]

def nodeValue2835 : Sparse Master := [(Sum.inr 2835, (1 / 1))]

def nodeValue2836 : Sparse Master := [(Sum.inr 2836, (1 / 1))]

def nodeValue2837 : Sparse Master := [(Sum.inr 2837, (1 / 1))]

def nodeValue2838 : Sparse Master := [(Sum.inr 2838, (1 / 1))]

def nodeValue2841 : Sparse Master := [(Sum.inr 2841, (1 / 1))]

def nodeValue2842 : Sparse Master := [(Sum.inr 2842, (1 / 1))]

def nodeValue2846 : Sparse Master := [(Sum.inr 2846, (1 / 1))]

def nodeValue2847 : Sparse Master := [(Sum.inr 2847, (1 / 1))]

def nodeValue2848 : Sparse Master := [(Sum.inr 2848, (1 / 1))]

def nodeValue2849 : Sparse Master := [(Sum.inr 2849, (1 / 1))]

def nodeValue2853 : Sparse Master := [(Sum.inr 2853, (1 / 1))]

def nodeValue2856 : Sparse Master := [(Sum.inr 2856, (1 / 1))]

def nodeValue2857 : Sparse Master := [(Sum.inr 2857, (1 / 1))]

def nodeValue2858 : Sparse Master := [(Sum.inr 2858, (1 / 1))]

def nodeValue2859 : Sparse Master := [(Sum.inr 2859, (1 / 1))]

def nodeValue2860 : Sparse Master := [(Sum.inr 2860, (1 / 1))]

def nodeValue2861 : Sparse Master := [(Sum.inr 2861, (1 / 1))]

def nodeValue2862 : Sparse Master := [(Sum.inr 2862, (1 / 1))]

def nodeValue2864 : Sparse Master := [(Sum.inr 2864, (1 / 1))]

def nodeValue2865 : Sparse Master := [(Sum.inr 2865, (1 / 1))]

def nodeValue2867 : Sparse Master := [(Sum.inr 2867, (1 / 1))]

def nodeValue2868 : Sparse Master := [(Sum.inr 2868, (1 / 1))]

def nodeValue2869 : Sparse Master := [(Sum.inr 2869, (1 / 1))]

def nodeValue2870 : Sparse Master := [(Sum.inr 2870, (1 / 1))]

def nodeValue2871 : Sparse Master := [(Sum.inr 2871, (1 / 1))]

def nodeValue2872 : Sparse Master := [(Sum.inr 2872, (1 / 1))]

def nodeValue2873 : Sparse Master := [(Sum.inr 2873, (1 / 1))]

def nodeValue2874 : Sparse Master := [(Sum.inr 2874, (1 / 1))]

def nodeValue2875 : Sparse Master := [(Sum.inr 2875, (1 / 1))]

def nodeValue2876 : Sparse Master := [(Sum.inr 2876, (1 / 1))]

def nodeValue2877 : Sparse Master := [(Sum.inr 2877, (1 / 1))]

def nodeValue2878 : Sparse Master := [(Sum.inr 2878, (1 / 1))]

def nodeValue2879 : Sparse Master := [(Sum.inr 2879, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue2880 : Sparse Master := [(Sum.inr 2880, (1 / 1))]

def nodeValue2881 : Sparse Master := [(Sum.inr 2881, (1 / 1))]

def nodeValue2882 : Sparse Master := [(Sum.inr 2882, (1 / 1))]

def nodeValue2883 : Sparse Master := [(Sum.inr 2883, (1 / 1))]

def nodeValue2884 : Sparse Master := [(Sum.inr 2884, (1 / 1))]

def nodeValue2885 : Sparse Master := [(Sum.inr 2885, (1 / 1))]

def nodeValue2886 : Sparse Master := [(Sum.inr 2886, (1 / 1))]

def nodeValue2887 : Sparse Master := [(Sum.inr 2887, (1 / 1))]

def nodeValue2888 : Sparse Master := [(Sum.inr 2888, (1 / 1))]

def nodeValue2889 : Sparse Master := [(Sum.inr 2889, (1 / 1))]

def nodeValue2890 : Sparse Master := [(Sum.inr 2890, (1 / 1))]

def nodeValue2892 : Sparse Master := [(Sum.inr 2892, (1 / 1))]

def nodeValue2893 : Sparse Master := [(Sum.inr 2893, (1 / 1))]

def nodeValue2894 : Sparse Master := []

def nodeValue2895 : Sparse Master := [(Sum.inr 2895, (1 / 1))]

def nodeValue2896 : Sparse Master := [(Sum.inr 2896, (1 / 1))]

def nodeValue2897 : Sparse Master := []

def nodeValue2898 : Sparse Master := [(Sum.inr 2898, (1 / 1))]

def nodeValue2899 : Sparse Master := [(Sum.inr 2899, (1 / 1))]

def nodeValue2900 : Sparse Master := [(Sum.inr 2900, (1 / 1))]

def nodeValue2901 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 9, (1 / 216)), (Sum.inl 58, (-1 / 864)), (Sum.inl 5, (-1 / 216)), (Sum.inl 6, (7 / 864)), (Sum.inl 68, (-1 / 72)), (Sum.inl 2, (1 / 144)), (Sum.inl 70, (1 / 54)), (Sum.inl 71, (1 / 54)), (Sum.inl 7, (1 / 54)), (Sum.inl 35, (1 / 18)), (Sum.inl 3, (1 / 54)), (Sum.inl 197, (-1 / 18)), (Sum.inl 26, (1 / 27)), (Sum.inl 1, (1 / 216))]

def nodeValue2902 : Sparse Master := [(Sum.inr 2902, (1 / 1))]

def nodeValue2903 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 9, (1 / 108)), (Sum.inl 5, (-1 / 54)), (Sum.inl 6, (-1 / 288)), (Sum.inl 68, (-1 / 36)), (Sum.inl 2, (5 / 432)), (Sum.inl 69, (1 / 54)), (Sum.inl 71, (1 / 54)), (Sum.inl 7, (1 / 27)), (Sum.inl 8, (1 / 27)), (Sum.inl 126, (-1 / 18)), (Sum.inl 3, (1 / 27)), (Sum.inl 52, (1 / 54)), (Sum.inl 1, (11 / 864)), (Sum.inl 236, (-1 / 18))]

def nodeValue2904 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 9, (-1 / 216)), (Sum.inl 5, (-1 / 108)), (Sum.inl 6, (1 / 864)), (Sum.inl 68, (1 / 72)), (Sum.inl 2, (1 / 72)), (Sum.inl 70, (-1 / 54)), (Sum.inl 7, (-1 / 54)), (Sum.inl 35, (-1 / 27)), (Sum.inl 3, (-1 / 54)), (Sum.inl 197, (1 / 18)), (Sum.inl 26, (-1 / 54)), (Sum.inl 1, (17 / 864))]

def nodeValue2905 : Sparse Master := [(Sum.inr 2905, (1 / 1))]

def nodeValue2906 : Sparse Master := [(Sum.inr 2906, (1 / 1))]

def nodeValue2907 : Sparse Master := [(Sum.inr 2907, (1 / 1))]

def nodeValue2908 : Sparse Master := [(Sum.inr 2908, (1 / 1))]

def nodeValue2909 : Sparse Master := [(Sum.inr 2909, (1 / 1))]

def nodeValue2910 : Sparse Master := [(Sum.inr 2910, (1 / 1))]

def nodeValue2911 : Sparse Master := [(Sum.inr 2911, (1 / 1))]

def nodeValue2912 : Sparse Master := [(Sum.inr 2912, (1 / 1))]

def nodeValue2913 : Sparse Master := [(Sum.inr 2913, (1 / 1))]

def nodeValue2914 : Sparse Master := []

def nodeValue2916 : Sparse Master := [(Sum.inr 2916, (1 / 1))]

def nodeValue2917 : Sparse Master := []

def nodeValue2918 : Sparse Master := [(Sum.inr 2918, (1 / 1))]

def nodeValue2919 : Sparse Master := [(Sum.inr 2919, (1 / 1))]

def nodeValue2920 : Sparse Master := [(Sum.inr 2920, (1 / 1))]

def nodeValue2921 : Sparse Master := [(Sum.inr 2921, (1 / 1))]

def nodeValue2922 : Sparse Master := [(Sum.inr 2922, (1 / 1))]

def nodeValue2923 : Sparse Master := [(Sum.inr 2923, (1 / 1))]

def nodeValue2924 : Sparse Master := [(Sum.inr 2924, (1 / 1))]

def nodeValue2925 : Sparse Master := [(Sum.inr 2925, (1 / 1))]

def nodeValue2926 : Sparse Master := [(Sum.inr 2926, (1 / 1))]

def nodeValue2927 : Sparse Master := []

def nodeValue2928 : Sparse Master := [(Sum.inr 2928, (1 / 1))]

def nodeValue2929 : Sparse Master := [(Sum.inr 2929, (1 / 1))]

def nodeValue2930 : Sparse Master := [(Sum.inr 2930, (1 / 1))]

def nodeValue2931 : Sparse Master := [(Sum.inr 2931, (1 / 1))]

def nodeValue2933 : Sparse Master := [(Sum.inr 2933, (1 / 1))]

def nodeValue2934 : Sparse Master := []

def nodeValue2936 : Sparse Master := [(Sum.inl 0, (-19 / 4320)), (Sum.inl 5, (-1 / 36)), (Sum.inl 6, (1 / 288)), (Sum.inl 2, (5 / 432)), (Sum.inl 7, (1 / 54)), (Sum.inl 8, (1 / 27)), (Sum.inl 3, (1 / 27)), (Sum.inl 1, (-17 / 432))]

def nodeValue2937 : Sparse Master := [(Sum.inl 0, (-37 / 4320)), (Sum.inl 5, (-5 / 216)), (Sum.inl 6, (1 / 288)), (Sum.inl 2, (-1 / 216)), (Sum.inl 7, (1 / 27)), (Sum.inl 35, (1 / 54)), (Sum.inl 8, (1 / 54)), (Sum.inl 3, (2 / 27)), (Sum.inl 26, (1 / 27)), (Sum.inl 4, (1 / 54)), (Sum.inl 1, (1 / 144))]

def nodeValue2939 : Sparse Master := [(Sum.inl 0, (-17 / 2160)), (Sum.inl 5, (1 / 108)), (Sum.inl 6, (-1 / 216)), (Sum.inl 2, (1 / 144)), (Sum.inl 1, (1 / 216))]

def nodeValue2940 : Sparse Master := []

def nodeValue2941 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 5, (1 / 216)), (Sum.inl 6, (-1 / 216)), (Sum.inl 2, (5 / 432)), (Sum.inl 35, (-1 / 54)), (Sum.inl 26, (-1 / 54)), (Sum.inl 1, (1 / 108))]

def nodeValue2942 : Sparse Master := [(Sum.inr 2942, (1 / 1))]

def nodeValue2943 : Sparse Master := [(Sum.inl 0, (-11 / 1440)), (Sum.inl 5, (1 / 54)), (Sum.inl 2, (-11 / 864)), (Sum.inl 7, (-1 / 54)), (Sum.inl 8, (-1 / 54)), (Sum.inl 3, (-1 / 54)), (Sum.inl 1, (-1 / 432))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue2945 : Sparse Master := [(Sum.inr 2945, (1 / 1))]

def nodeValue2946 : Sparse Master := [(Sum.inr 2946, (1 / 1))]

def nodeValue2947 : Sparse Master := [(Sum.inr 2947, (1 / 1))]

def nodeValue2949 : Sparse Master := [(Sum.inr 2949, (1 / 1))]

def nodeValue2950 : Sparse Master := [(Sum.inr 2950, (1 / 1))]

def nodeValue2951 : Sparse Master := [(Sum.inr 2951, (1 / 1))]

def nodeValue2952 : Sparse Master := [(Sum.inr 2952, (1 / 1))]

def nodeValue2953 : Sparse Master := []

def nodeValue2954 : Sparse Master := [(Sum.inr 2954, (1 / 1))]

def nodeValue2955 : Sparse Master := [(Sum.inr 2955, (1 / 1))]

def nodeValue2956 : Sparse Master := [(Sum.inr 2956, (1 / 1))]

def nodeValue2957 : Sparse Master := [(Sum.inl 0, (-17 / 4320)), (Sum.inl 5, (1 / 108)), (Sum.inl 6, (-1 / 288)), (Sum.inl 2, (5 / 216)), (Sum.inl 7, (1 / 18)), (Sum.inl 35, (1 / 27)), (Sum.inl 3, (2 / 9)), (Sum.inl 26, (1 / 9)), (Sum.inl 4, (1 / 9)), (Sum.inl 1, (-5 / 216))]

def nodeValue2958 : Sparse Master := [(Sum.inl 0, (-49 / 4320)), (Sum.inl 6, (-1 / 288)), (Sum.inl 2, (11 / 432)), (Sum.inl 7, (1 / 54)), (Sum.inl 8, (1 / 27)), (Sum.inl 3, (1 / 27)), (Sum.inl 1, (7 / 432))]

def nodeValue2959 : Sparse Master := [(Sum.inl 0, (-37 / 4320)), (Sum.inl 6, (1 / 864)), (Sum.inl 2, (-5 / 432)), (Sum.inl 7, (-1 / 54)), (Sum.inl 3, (-1 / 27)), (Sum.inl 1, (7 / 432))]

def nodeValue2960 : Sparse Master := [(Sum.inl 0, (-47 / 4320)), (Sum.inl 6, (1 / 864)), (Sum.inl 2, (-1 / 144)), (Sum.inl 8, (-1 / 54)), (Sum.inl 1, (1 / 216))]

def nodeValue2961 : Sparse Master := [(Sum.inl 0, (-7 / 1080)), (Sum.inl 5, (-1 / 216)), (Sum.inl 6, (1 / 864)), (Sum.inl 2, (-1 / 288)), (Sum.inl 7, (-1 / 54)), (Sum.inl 35, (-1 / 54)), (Sum.inl 3, (-1 / 18)), (Sum.inl 26, (-1 / 27)), (Sum.inl 4, (-1 / 54)), (Sum.inl 1, (1 / 54))]

def nodeValue2962 : Sparse Master := [(Sum.inr 2962, (1 / 1))]

def nodeValue2963 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 6, (1 / 864)), (Sum.inl 2, (1 / 864)), (Sum.inl 7, (-1 / 54)), (Sum.inl 3, (-1 / 54)), (Sum.inl 1, (-19 / 432))]

def nodeValue2964 : Sparse Master := [(Sum.inr 2964, (1 / 1))]

def nodeValue2965 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 5, (-1 / 108)), (Sum.inl 6, (-1 / 432)), (Sum.inl 1, (-5 / 108))]

def nodeValue2966 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 6, (-1 / 432)), (Sum.inl 2, (1 / 216)), (Sum.inl 35, (1 / 27)), (Sum.inl 26, (1 / 27)), (Sum.inl 1, (1 / 72))]

def nodeValue2967 : Sparse Master := [(Sum.inr 2967, (1 / 1))]

def nodeValue2968 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 5, (1 / 108)), (Sum.inl 2, (-1 / 432)), (Sum.inl 7, (1 / 27)), (Sum.inl 3, (1 / 27)), (Sum.inl 1, (-7 / 216))]

def nodeValue2969 : Sparse Master := [(Sum.inl 0, (-1 / 90)), (Sum.inl 5, (1 / 108)), (Sum.inl 8, (1 / 27)), (Sum.inl 1, (1 / 108))]

def nodeValue2970 : Sparse Master := [(Sum.inr 2970, (1 / 1))]

def nodeValue2971 : Sparse Master := [(Sum.inr 2971, (1 / 1))]

def nodeValue2972 : Sparse Master := [(Sum.inr 2972, (1 / 1))]

def nodeValue2973 : Sparse Master := [(Sum.inr 2973, (1 / 1))]

def nodeValue2974 : Sparse Master := [(Sum.inr 2974, (1 / 1))]

def nodeValue2975 : Sparse Master := [(Sum.inr 2975, (1 / 1))]

def nodeValue2976 : Sparse Master := [(Sum.inr 2976, (1 / 1))]

def nodeValue2977 : Sparse Master := [(Sum.inr 2977, (1 / 1))]

def nodeValue2978 : Sparse Master := [(Sum.inr 2978, (1 / 1))]

def nodeValue2979 : Sparse Master := [(Sum.inr 2979, (1 / 1))]

def nodeValue2980 : Sparse Master := [(Sum.inr 2980, (1 / 1))]

def nodeValue2981 : Sparse Master := [(Sum.inr 2981, (1 / 1))]

def nodeValue2983 : Sparse Master := [(Sum.inr 2983, (1 / 1))]

def nodeValue2984 : Sparse Master := [(Sum.inr 2984, (1 / 1))]

def nodeValue2985 : Sparse Master := [(Sum.inr 2985, (1 / 1))]

def nodeValue2986 : Sparse Master := [(Sum.inl 0, (-19 / 4320)), (Sum.inl 5, (-1 / 54)), (Sum.inl 6, (1 / 432)), (Sum.inl 2, (1 / 96)), (Sum.inl 7, (1 / 27)), (Sum.inl 35, (1 / 27)), (Sum.inl 3, (1 / 18)), (Sum.inl 52, (1 / 27)), (Sum.inl 26, (1 / 27)), (Sum.inl 4, (1 / 27)), (Sum.inl 1, (-1 / 144))]

def nodeValue2987 : Sparse Master := [(Sum.inl 0, (-23 / 4320)), (Sum.inl 5, (-1 / 36)), (Sum.inl 6, (1 / 288)), (Sum.inl 2, (7 / 432)), (Sum.inl 8, (1 / 27)), (Sum.inl 3, (1 / 27)), (Sum.inl 52, (1 / 54)), (Sum.inl 1, (-1 / 48))]

def nodeValue2988 : Sparse Master := [(Sum.inl 0, (-37 / 4320)), (Sum.inl 5, (-5 / 216)), (Sum.inl 6, (1 / 216)), (Sum.inl 2, (-1 / 54)), (Sum.inl 7, (1 / 27)), (Sum.inl 35, (1 / 54)), (Sum.inl 3, (2 / 27)), (Sum.inl 26, (1 / 27)), (Sum.inl 1, (1 / 864))]

def nodeValue2990 : Sparse Master := [(Sum.inl 0, (-1 / 160)), (Sum.inl 5, (1 / 72)), (Sum.inl 2, (-11 / 864)), (Sum.inl 7, (-1 / 27)), (Sum.inl 35, (-1 / 54)), (Sum.inl 3, (-1 / 18)), (Sum.inl 26, (-1 / 54)), (Sum.inl 1, (1 / 72))]

def nodeValue2991 : Sparse Master := [(Sum.inl 0, (-1 / 180)), (Sum.inl 5, (1 / 54)), (Sum.inl 2, (-1 / 72)), (Sum.inl 8, (-1 / 27)), (Sum.inl 1, (-5 / 216))]

def nodeValue2992 : Sparse Master := [(Sum.inr 2992, (1 / 1))]

def nodeValue2995 : Sparse Master := [(Sum.inr 2995, (1 / 1))]

def nodeValue2996 : Sparse Master := [(Sum.inl 0, (-37 / 4320)), (Sum.inl 5, (1 / 216)), (Sum.inl 6, (-1 / 432)), (Sum.inl 2, (1 / 54)), (Sum.inl 35, (1 / 54)), (Sum.inl 3, (2 / 27)), (Sum.inl 52, (1 / 27)), (Sum.inl 26, (1 / 27)), (Sum.inl 4, (1 / 27)), (Sum.inl 1, (5 / 288))]

def nodeValue2997 : Sparse Master := [(Sum.inl 0, (-7 / 1080)), (Sum.inl 5, (-1 / 216)), (Sum.inl 6, (1 / 864)), (Sum.inl 2, (-1 / 144)), (Sum.inl 35, (-1 / 54)), (Sum.inl 52, (-1 / 54)), (Sum.inl 26, (-1 / 54)), (Sum.inl 4, (-1 / 54)), (Sum.inl 1, (1 / 96))]

def nodeValue2998 : Sparse Master := [(Sum.inl 0, (-11 / 1440)), (Sum.inl 6, (1 / 864)), (Sum.inl 2, (-7 / 432)), (Sum.inl 3, (-1 / 27)), (Sum.inl 52, (-1 / 54)), (Sum.inl 1, (-1 / 432))]

def nodeValue2999 : Sparse Master := []

def nodeValue3000 : Sparse Master := []

def nodeValue3001 : Sparse Master := []

def nodeValue3002 : Sparse Master := []

def nodeValue3003 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 5, (-1 / 216)), (Sum.inl 2, (13 / 864)), (Sum.inl 35, (-1 / 54)), (Sum.inl 3, (-1 / 54)), (Sum.inl 26, (-1 / 27)), (Sum.inl 1, (11 / 864))]

def nodeValue3004 : Sparse Master := []

def nodeValue3005 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 5, (1 / 108)), (Sum.inl 2, (1 / 432)), (Sum.inl 35, (1 / 27)), (Sum.inl 3, (1 / 27)), (Sum.inl 26, (1 / 27)), (Sum.inl 1, (1 / 108))]

def nodeValue3006 : Sparse Master := []

def nodeValue3007 : Sparse Master := [(Sum.inr 3007, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue3008 : Sparse Master := [(Sum.inr 3008, (1 / 1))]

def nodeValue3010 : Sparse Master := [(Sum.inr 3010, (1 / 1))]

def nodeValue3011 : Sparse Master := [(Sum.inr 3011, (1 / 1))]

def nodeValue3012 : Sparse Master := [(Sum.inr 3012, (1 / 1))]

def nodeValue3013 : Sparse Master := [(Sum.inr 3013, (1 / 1))]

def nodeValue3014 : Sparse Master := [(Sum.inr 3014, (1 / 1))]

def nodeValue3015 : Sparse Master := [(Sum.inr 3015, (1 / 1))]

def nodeValue3016 : Sparse Master := [(Sum.inr 3016, (1 / 1))]

def nodeValue3017 : Sparse Master := [(Sum.inr 3017, (1 / 1))]

def nodeValue3018 : Sparse Master := [(Sum.inr 3018, (1 / 1))]

def nodeValue3019 : Sparse Master := [(Sum.inr 3019, (1 / 1))]

def nodeValue3022 : Sparse Master := [(Sum.inr 3022, (1 / 1))]

def nodeValue3023 : Sparse Master := [(Sum.inr 3023, (1 / 1))]

def nodeValue3024 : Sparse Master := [(Sum.inr 3024, (1 / 1))]

def nodeValue3025 : Sparse Master := [(Sum.inr 3025, (1 / 1))]

def nodeValue3028 : Sparse Master := [(Sum.inr 3028, (1 / 1))]

def nodeValue3029 : Sparse Master := [(Sum.inr 3029, (1 / 1))]

def nodeValue3030 : Sparse Master := [(Sum.inr 3030, (1 / 1))]

def nodeValue3031 : Sparse Master := [(Sum.inr 3031, (1 / 1))]

def nodeValue3032 : Sparse Master := [(Sum.inr 3032, (1 / 1))]

def nodeValue3033 : Sparse Master := [(Sum.inr 3033, (1 / 1))]

def nodeValue3034 : Sparse Master := [(Sum.inr 3034, (1 / 1))]

def nodeValue3035 : Sparse Master := [(Sum.inr 3035, (1 / 1))]

def nodeValue3036 : Sparse Master := [(Sum.inr 3036, (1 / 1))]

def nodeValue3037 : Sparse Master := [(Sum.inr 3037, (1 / 1))]

def nodeValue3038 : Sparse Master := [(Sum.inr 3038, (1 / 1))]

def nodeValue3039 : Sparse Master := [(Sum.inr 3039, (1 / 1))]

def nodeValue3040 : Sparse Master := [(Sum.inr 3040, (1 / 1))]

def nodeValue3041 : Sparse Master := [(Sum.inr 3041, (1 / 1))]

def nodeValue3042 : Sparse Master := [(Sum.inr 3042, (1 / 1))]

def nodeValue3043 : Sparse Master := [(Sum.inr 3043, (1 / 1))]

def nodeValue3044 : Sparse Master := [(Sum.inr 3044, (1 / 1))]

def nodeValue3045 : Sparse Master := [(Sum.inr 3045, (1 / 1))]

def nodeValue3046 : Sparse Master := [(Sum.inr 3046, (1 / 1))]

def nodeValue3049 : Sparse Master := [(Sum.inr 3049, (1 / 1))]

def nodeValue3050 : Sparse Master := [(Sum.inr 3050, (1 / 1))]

def nodeValue3051 : Sparse Master := [(Sum.inr 3051, (1 / 1))]

def nodeValue3052 : Sparse Master := [(Sum.inr 3052, (1 / 1))]

def nodeValue3053 : Sparse Master := [(Sum.inr 3053, (1 / 1))]

def nodeValue3054 : Sparse Master := [(Sum.inr 3054, (1 / 1))]

def nodeValue3055 : Sparse Master := [(Sum.inr 3055, (1 / 1))]

def nodeValue3056 : Sparse Master := [(Sum.inr 3056, (1 / 1))]

def nodeValue3057 : Sparse Master := [(Sum.inr 3057, (1 / 1))]

def nodeValue3058 : Sparse Master := [(Sum.inr 3058, (1 / 1))]

def nodeValue3059 : Sparse Master := [(Sum.inr 3059, (1 / 1))]

def nodeValue3061 : Sparse Master := []

def nodeValue3062 : Sparse Master := [(Sum.inr 3062, (1 / 1))]

def nodeValue3063 : Sparse Master := [(Sum.inr 3063, (1 / 1))]

def nodeValue3064 : Sparse Master := [(Sum.inr 3064, (1 / 1))]

def nodeValue3065 : Sparse Master := []

def nodeValue3066 : Sparse Master := [(Sum.inr 3066, (1 / 1))]

def nodeValue3067 : Sparse Master := [(Sum.inr 3067, (1 / 1))]

def nodeValue3068 : Sparse Master := [(Sum.inr 3068, (1 / 1))]

def nodeValue3069 : Sparse Master := [(Sum.inr 3069, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue3072 : Sparse Master := [(Sum.inr 3072, (1 / 1))]

def nodeValue3073 : Sparse Master := [(Sum.inr 3073, (1 / 1))]

def nodeValue3074 : Sparse Master := [(Sum.inr 3074, (1 / 1))]

def nodeValue3075 : Sparse Master := [(Sum.inr 3075, (1 / 1))]

def nodeValue3076 : Sparse Master := []

def nodeValue3077 : Sparse Master := [(Sum.inr 3077, (1 / 1))]

def nodeValue3078 : Sparse Master := [(Sum.inr 3078, (1 / 1))]

def nodeValue3079 : Sparse Master := [(Sum.inr 3079, (1 / 1))]

def nodeValue3080 : Sparse Master := []

def nodeValue3081 : Sparse Master := [(Sum.inl 0, (-5 / 432)), (Sum.inl 5, (1 / 216)), (Sum.inl 2, (1 / 108)), (Sum.inl 35, (1 / 54)), (Sum.inl 3, (2 / 27)), (Sum.inl 13, (1 / 54)), (Sum.inl 55, (-1 / 18)), (Sum.inl 12, (1 / 54)), (Sum.inl 26, (1 / 27)), (Sum.inl 27, (-1 / 72)), (Sum.inl 1, (5 / 432))]

def nodeValue3082 : Sparse Master := [(Sum.inl 0, (-13 / 1440)), (Sum.inl 5, (-1 / 216)), (Sum.inl 2, (-37 / 864)), (Sum.inl 35, (-1 / 54)), (Sum.inl 13, (-1 / 54)), (Sum.inl 1, (-1 / 432))]

def nodeValue3083 : Sparse Master := [(Sum.inr 3083, (1 / 1))]

def nodeValue3084 : Sparse Master := [(Sum.inr 3084, (1 / 1))]

def nodeValue3085 : Sparse Master := []

def nodeValue3086 : Sparse Master := [(Sum.inr 3086, (1 / 1))]

def nodeValue3087 : Sparse Master := [(Sum.inl 0, (-17 / 4320)), (Sum.inl 2, (1 / 288)), (Sum.inl 3, (5 / 54)), (Sum.inl 26, (1 / 27)), (Sum.inl 4, (1 / 27)), (Sum.inl 1, (-11 / 216))]

def nodeValue3088 : Sparse Master := [(Sum.inl 0, (-29 / 4320)), (Sum.inl 2, (7 / 864)), (Sum.inl 3, (-1 / 54)), (Sum.inl 1, (1 / 216))]

def nodeValue3089 : Sparse Master := [(Sum.inl 0, (-17 / 2160)), (Sum.inl 2, (1 / 96)), (Sum.inl 3, (-1 / 54)), (Sum.inl 26, (-1 / 54)), (Sum.inl 1, (7 / 864))]

def nodeValue3090 : Sparse Master := [(Sum.inl 0, (-1 / 120)), (Sum.inl 2, (-1 / 24))]

def nodeValue3091 : Sparse Master := [(Sum.inr 3091, (1 / 1))]

def nodeValue3092 : Sparse Master := [(Sum.inr 3092, (1 / 1))]

def nodeValue3093 : Sparse Master := [(Sum.inl 0, (-17 / 2160)), (Sum.inl 5, (1 / 72)), (Sum.inl 2, (-7 / 288)), (Sum.inl 35, (1 / 18)), (Sum.inl 3, (2 / 9)), (Sum.inl 13, (1 / 27)), (Sum.inl 55, (-1 / 6)), (Sum.inl 12, (1 / 18)), (Sum.inl 26, (1 / 9)), (Sum.inl 4, (1 / 9)), (Sum.inl 27, (-1 / 24)), (Sum.inl 1, (-5 / 288))]

def nodeValue3094 : Sparse Master := [(Sum.inl 0, (-31 / 4320)), (Sum.inl 5, (-1 / 216)), (Sum.inl 2, (1 / 72)), (Sum.inl 35, (-1 / 54)), (Sum.inl 3, (-1 / 27)), (Sum.inl 13, (-1 / 54)), (Sum.inl 55, (1 / 18)), (Sum.inl 12, (-1 / 54)), (Sum.inl 26, (-1 / 54)), (Sum.inl 27, (1 / 72)), (Sum.inl 1, (5 / 288))]

def nodeValue3095 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 5, (1 / 108)), (Sum.inl 2, (-17 / 432)), (Sum.inl 35, (1 / 27)), (Sum.inl 13, (1 / 27)), (Sum.inl 1, (1 / 216))]

def nodeValue3096 : Sparse Master := [(Sum.inr 3096, (1 / 1))]

def nodeValue3097 : Sparse Master := [(Sum.inr 3097, (1 / 1))]

def nodeValue3098 : Sparse Master := [(Sum.inr 3098, (1 / 1))]

def nodeValue3099 : Sparse Master := [(Sum.inl 0, (-7 / 1440)), (Sum.inl 2, (-5 / 864)), (Sum.inl 3, (-1 / 18)), (Sum.inl 26, (-1 / 27)), (Sum.inl 4, (-1 / 27))]

def nodeValue3100 : Sparse Master := [(Sum.inl 0, (-47 / 4320)), (Sum.inl 2, (-11 / 864)), (Sum.inl 3, (-1 / 54)), (Sum.inl 1, (1 / 216))]

def nodeValue3101 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 2, (5 / 432)), (Sum.inl 3, (1 / 27)), (Sum.inl 1, (1 / 54))]

def nodeValue3102 : Sparse Master := [(Sum.inl 0, (-1 / 90)), (Sum.inl 2, (1 / 72)), (Sum.inl 1, (1 / 72))]

def nodeValue3103 : Sparse Master := [(Sum.inl 0, (-7 / 1080)), (Sum.inl 2, (1 / 144)), (Sum.inl 3, (1 / 27)), (Sum.inl 26, (1 / 27)), (Sum.inl 1, (5 / 432))]

def nodeValue3104 : Sparse Master := []

def nodeValue3105 : Sparse Master := [(Sum.inl 0, (-7 / 864)), (Sum.inl 5, (1 / 216)), (Sum.inl 2, (-1 / 108)), (Sum.inl 35, (1 / 54)), (Sum.inl 3, (7 / 54)), (Sum.inl 55, (-1 / 18)), (Sum.inl 26, (2 / 27)), (Sum.inl 4, (2 / 27)), (Sum.inl 27, (-1 / 72)), (Sum.inl 1, (-41 / 864))]

def nodeValue3106 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 2, (5 / 432)), (Sum.inl 3, (-1 / 54)), (Sum.inl 55, (1 / 18)), (Sum.inl 27, (1 / 72)), (Sum.inl 1, (1 / 216))]

def nodeValue3108 : Sparse Master := [(Sum.inr 3108, (1 / 1))]

def nodeValue3109 : Sparse Master := [(Sum.inl 0, (-17 / 2160)), (Sum.inl 2, (-1 / 108)), (Sum.inl 3, (-1 / 27)), (Sum.inl 26, (-1 / 54)), (Sum.inl 4, (-1 / 54)), (Sum.inl 1, (1 / 432))]

def nodeValue3110 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 2, (5 / 432)), (Sum.inl 3, (1 / 27)), (Sum.inl 1, (1 / 54))]

def nodeValue3111 : Sparse Master := []

def nodeValue3112 : Sparse Master := []

def nodeValue3113 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 2, (1 / 108)), (Sum.inl 26, (1 / 27)), (Sum.inl 1, (1 / 144))]

def nodeValue3114 : Sparse Master := []

def nodeValue3115 : Sparse Master := [(Sum.inr 3115, (1 / 1))]

def nodeValue3116 : Sparse Master := [(Sum.inl 0, (-29 / 4320)), (Sum.inl 5, (-1 / 216)), (Sum.inl 35, (-1 / 54)), (Sum.inl 3, (-1 / 18)), (Sum.inl 55, (1 / 18)), (Sum.inl 26, (-1 / 27)), (Sum.inl 4, (-1 / 27)), (Sum.inl 27, (1 / 72)), (Sum.inl 1, (1 / 864))]

def nodeValue3117 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 2, (1 / 144)), (Sum.inl 55, (-1 / 9)), (Sum.inl 27, (-1 / 36)), (Sum.inl 1, (1 / 72))]

def nodeValue3118 : Sparse Master := [(Sum.inr 3118, (1 / 1))]

def nodeValue3119 : Sparse Master := [(Sum.inl 0, (-13 / 2160)), (Sum.inl 2, (-1 / 144)), (Sum.inl 3, (1 / 27)), (Sum.inl 26, (1 / 27)), (Sum.inl 4, (1 / 27)), (Sum.inl 1, (1 / 216))]

def nodeValue3120 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 2, (-1 / 432)), (Sum.inl 3, (1 / 27)), (Sum.inl 1, (-11 / 216))]

def nodeValue3121 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 2, (1 / 144)), (Sum.inl 3, (-1 / 9)), (Sum.inl 1, (-1 / 72))]

def nodeValue3122 : Sparse Master := []

def nodeValue3123 : Sparse Master := []

def nodeValue3124 : Sparse Master := []

def nodeValue3125 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 2, (1 / 72)), (Sum.inl 26, (-1 / 9)), (Sum.inl 1, (1 / 48))]

def nodeValue3126 : Sparse Master := []

def nodeValue3127 : Sparse Master := [(Sum.inr 3127, (1 / 1))]

def nodeValue3128 : Sparse Master := [(Sum.inr 3128, (1 / 1))]

def nodeValue3129 : Sparse Master := [(Sum.inr 3129, (1 / 1))]

def nodeValue3130 : Sparse Master := [(Sum.inr 3130, (1 / 1))]

def nodeValue3131 : Sparse Master := [(Sum.inr 3131, (1 / 1))]

def nodeValue3132 : Sparse Master := [(Sum.inr 3132, (1 / 1))]

def nodeValue3133 : Sparse Master := [(Sum.inr 3133, (1 / 1))]

def nodeValue3134 : Sparse Master := [(Sum.inr 3134, (1 / 1))]

def nodeValue3135 : Sparse Master := [(Sum.inr 3135, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue3136 : Sparse Master := [(Sum.inr 3136, (1 / 1))]

def nodeValue3137 : Sparse Master := [(Sum.inr 3137, (1 / 1))]

def nodeValue3138 : Sparse Master := [(Sum.inr 3138, (1 / 1))]

def nodeValue3139 : Sparse Master := [(Sum.inl 0, (-5 / 864)), (Sum.inl 9, (1 / 216)), (Sum.inl 5, (5 / 216)), (Sum.inl 6, (-1 / 432)), (Sum.inl 68, (-5 / 72)), (Sum.inl 2, (-1 / 54)), (Sum.inl 70, (1 / 54)), (Sum.inl 7, (1 / 27)), (Sum.inl 35, (1 / 18)), (Sum.inl 125, (-1 / 18)), (Sum.inl 3, (5 / 54)), (Sum.inl 13, (1 / 54)), (Sum.inl 197, (-2 / 9)), (Sum.inl 24, (-1 / 9)), (Sum.inl 55, (-1 / 18)), (Sum.inl 56, (-1 / 9)), (Sum.inl 26, (1 / 27)), (Sum.inl 4, (1 / 27)), (Sum.inl 27, (-1 / 24)), (Sum.inl 1, (-17 / 864))]

def nodeValue3140 : Sparse Master := [(Sum.inl 0, (-29 / 4320)), (Sum.inl 9, (1 / 216)), (Sum.inl 5, (1 / 54)), (Sum.inl 6, (-1 / 864)), (Sum.inl 68, (-5 / 72)), (Sum.inl 2, (-5 / 864)), (Sum.inl 70, (1 / 54)), (Sum.inl 7, (1 / 54)), (Sum.inl 35, (1 / 18)), (Sum.inl 125, (-1 / 9)), (Sum.inl 3, (1 / 18)), (Sum.inl 13, (1 / 54)), (Sum.inl 196, (-1 / 18)), (Sum.inl 197, (-1 / 9)), (Sum.inl 23, (-1 / 18)), (Sum.inl 54, (-1 / 18)), (Sum.inl 55, (-1 / 9)), (Sum.inl 12, (1 / 54)), (Sum.inl 26, (1 / 27)), (Sum.inl 27, (-1 / 24)), (Sum.inl 1, (5 / 864))]

def nodeValue3141 : Sparse Master := [(Sum.inl 0, (-1 / 180)), (Sum.inl 5, (-1 / 216)), (Sum.inl 68, (1 / 36)), (Sum.inl 2, (1 / 108)), (Sum.inl 125, (1 / 18)), (Sum.inl 196, (1 / 18)), (Sum.inl 23, (1 / 18)), (Sum.inl 54, (1 / 18)), (Sum.inl 27, (1 / 72)), (Sum.inl 1, (-1 / 54))]

def nodeValue3142 : Sparse Master := [(Sum.inl 0, (-7 / 1080)), (Sum.inl 5, (-1 / 216)), (Sum.inl 68, (1 / 36)), (Sum.inl 2, (-1 / 432)), (Sum.inl 197, (1 / 9)), (Sum.inl 24, (1 / 18)), (Sum.inl 56, (1 / 18)), (Sum.inl 27, (1 / 72)), (Sum.inl 1, (1 / 432))]

def nodeValue3143 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 9, (-1 / 216)), (Sum.inl 5, (-1 / 108)), (Sum.inl 68, (1 / 72)), (Sum.inl 2, (-1 / 32)), (Sum.inl 70, (-1 / 54)), (Sum.inl 35, (-1 / 27)), (Sum.inl 13, (-1 / 54)), (Sum.inl 196, (1 / 18)), (Sum.inl 1, (7 / 864))]

def nodeValue3144 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 68, (1 / 36)), (Sum.inl 2, (1 / 96)), (Sum.inl 125, (1 / 18)), (Sum.inl 197, (1 / 18)), (Sum.inl 55, (1 / 18)), (Sum.inl 27, (1 / 72)), (Sum.inl 1, (5 / 288))]

def nodeValue3145 : Sparse Master := [(Sum.inl 0, (-1 / 180)), (Sum.inl 68, (-1 / 36)), (Sum.inl 2, (-1 / 36)), (Sum.inl 196, (-1 / 9)), (Sum.inl 1, (-1 / 36))]

def nodeValue3146 : Sparse Master := [(Sum.inr 3146, (1 / 1))]

def nodeValue3147 : Sparse Master := [(Sum.inr 3147, (1 / 1))]

def nodeValue3149 : Sparse Master := [(Sum.inr 3149, (1 / 1))]

def nodeValue3150 : Sparse Master := [(Sum.inr 3150, (1 / 1))]

def nodeValue3151 : Sparse Master := [(Sum.inr 3151, (1 / 1))]

def nodeValue3152 : Sparse Master := [(Sum.inr 3152, (1 / 1))]

def nodeValue3153 : Sparse Master := [(Sum.inr 3153, (1 / 1))]

def nodeValue3154 : Sparse Master := [(Sum.inr 3154, (1 / 1))]

def nodeValue3155 : Sparse Master := [(Sum.inr 3155, (1 / 1))]

def nodeValue3156 : Sparse Master := [(Sum.inr 3156, (1 / 1))]

def nodeValue3157 : Sparse Master := [(Sum.inr 3157, (1 / 1))]

def nodeValue3158 : Sparse Master := [(Sum.inr 3158, (1 / 1))]

def nodeValue3159 : Sparse Master := [(Sum.inr 3159, (1 / 1))]

def nodeValue3160 : Sparse Master := [(Sum.inr 3160, (1 / 1))]

def nodeValue3161 : Sparse Master := [(Sum.inr 3161, (1 / 1))]

def nodeValue3162 : Sparse Master := [(Sum.inr 3162, (1 / 1))]

def nodeValue3163 : Sparse Master := [(Sum.inr 3163, (1 / 1))]

def nodeValue3164 : Sparse Master := [(Sum.inr 3164, (1 / 1))]

def nodeValue3165 : Sparse Master := [(Sum.inr 3165, (1 / 1))]

def nodeValue3166 : Sparse Master := [(Sum.inr 3166, (1 / 1))]

def nodeValue3168 : Sparse Master := [(Sum.inr 3168, (1 / 1))]

def nodeValue3170 : Sparse Master := [(Sum.inr 3170, (1 / 1))]

def nodeValue3172 : Sparse Master := [(Sum.inr 3172, (1 / 1))]

def nodeValue3174 : Sparse Master := [(Sum.inr 3174, (1 / 1))]

def nodeValue3175 : Sparse Master := [(Sum.inr 3175, (1 / 1))]

def nodeValue3176 : Sparse Master := [(Sum.inr 3176, (1 / 1))]

def nodeValue3178 : Sparse Master := [(Sum.inl 0, (-31 / 4320)), (Sum.inl 5, (1 / 108)), (Sum.inl 6, (1 / 864)), (Sum.inl 2, (-5 / 864)), (Sum.inl 54, (1 / 18)), (Sum.inl 56, (1 / 18)), (Sum.inl 228, (1 / 18)), (Sum.inl 1, (1 / 864))]

def nodeValue3179 : Sparse Master := [(Sum.inr 3179, (1 / 1))]

def nodeValue3180 : Sparse Master := [(Sum.inr 3180, (1 / 1))]

def nodeValue3184 : Sparse Master := [(Sum.inl 0, (-7 / 1080)), (Sum.inl 5, (-1 / 216)), (Sum.inl 6, (1 / 864)), (Sum.inl 2, (-5 / 864)), (Sum.inl 35, (-1 / 54)), (Sum.inl 3, (-1 / 27)), (Sum.inl 13, (-1 / 54)), (Sum.inl 56, (1 / 18)), (Sum.inl 26, (-1 / 54)), (Sum.inl 4, (-1 / 54)), (Sum.inl 1, (-1 / 432))]

def nodeValue3185 : Sparse Master := [(Sum.inl 0, (-31 / 4320)), (Sum.inl 5, (-1 / 216)), (Sum.inl 6, (1 / 864)), (Sum.inl 2, (1 / 72)), (Sum.inl 35, (-1 / 54)), (Sum.inl 3, (-1 / 54)), (Sum.inl 54, (1 / 18)), (Sum.inl 26, (-1 / 27)), (Sum.inl 1, (1 / 48))]

def nodeValue3187 : Sparse Master := [(Sum.inl 0, (-1 / 180)), (Sum.inl 5, (1 / 108)), (Sum.inl 2, (1 / 432)), (Sum.inl 54, (-1 / 9)), (Sum.inl 1, (-11 / 432))]

def nodeValue3188 : Sparse Master := [(Sum.inl 0, (-7 / 1080)), (Sum.inl 5, (1 / 108)), (Sum.inl 2, (-1 / 108)), (Sum.inl 56, (-1 / 9)), (Sum.inl 1, (-1 / 216))]

def nodeValue3189 : Sparse Master := [(Sum.inr 3189, (1 / 1))]

def nodeValue3190 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 9, (1 / 108)), (Sum.inl 5, (-1 / 72)), (Sum.inl 6, (-1 / 432)), (Sum.inl 68, (-1 / 36)), (Sum.inl 2, (5 / 432)), (Sum.inl 69, (1 / 54)), (Sum.inl 70, (1 / 54)), (Sum.inl 7, (1 / 18)), (Sum.inl 35, (2 / 27)), (Sum.inl 125, (-1 / 18)), (Sum.inl 3, (2 / 27)), (Sum.inl 13, (2 / 27)), (Sum.inl 52, (1 / 27)), (Sum.inl 196, (-1 / 18)), (Sum.inl 23, (-1 / 18)), (Sum.inl 54, (-1 / 9)), (Sum.inl 12, (1 / 54)), (Sum.inl 27, (-1 / 72)), (Sum.inl 1, (1 / 48))]

def nodeValue3191 : Sparse Master := [(Sum.inl 0, (-1 / 120)), (Sum.inl 9, (1 / 108)), (Sum.inl 5, (-7 / 216)), (Sum.inl 68, (-1 / 36)), (Sum.inl 2, (-1 / 216)), (Sum.inl 71, (1 / 27)), (Sum.inl 8, (1 / 18)), (Sum.inl 197, (-1 / 9)), (Sum.inl 24, (-1 / 18)), (Sum.inl 56, (-1 / 9)), (Sum.inl 27, (-1 / 72)), (Sum.inl 1, (-1 / 108))]

def nodeValue3193 : Sparse Master := [(Sum.inr 3193, (1 / 1))]

def nodeValue3195 : Sparse Master := [(Sum.inr 3195, (1 / 1))]

def nodeValue3196 : Sparse Master := [(Sum.inr 3196, (1 / 1))]

def nodeValue3197 : Sparse Master := [(Sum.inr 3197, (1 / 1))]

def nodeValue3198 : Sparse Master := [(Sum.inr 3198, (1 / 1))]

def nodeValue3199 : Sparse Master := [(Sum.inr 3199, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue320 : Sparse Master := [(Sum.inl 0, (37 / 864)), (Sum.inl 5, (25 / 216)), (Sum.inl 6, (-5 / 288)), (Sum.inl 2, (5 / 216)), (Sum.inl 7, (-5 / 27)), (Sum.inl 35, (-5 / 54)), (Sum.inl 8, (-5 / 54)), (Sum.inl 3, (-10 / 27)), (Sum.inl 26, (-5 / 27)), (Sum.inl 4, (-5 / 54)), (Sum.inl 1, (-5 / 144))]

def nodeValue321 : Sparse Master := [(Sum.inl 0, (19 / 864)), (Sum.inl 5, (5 / 36)), (Sum.inl 6, (-5 / 288)), (Sum.inl 2, (-25 / 432)), (Sum.inl 7, (-5 / 54)), (Sum.inl 8, (-5 / 27)), (Sum.inl 3, (-5 / 27)), (Sum.inl 1, (85 / 432))]

def nodeValue322 : Sparse Master := [(Sum.inl 0, (1 / 48)), (Sum.inl 5, (5 / 108)), (Sum.inl 6, (-5 / 864)), (Sum.inl 67, (-5 / 54)), (Sum.inl 34, (-5 / 27)), (Sum.inl 2, (-25 / 432)), (Sum.inl 7, (-5 / 27)), (Sum.inl 35, (-10 / 27)), (Sum.inl 3, (-35 / 54)), (Sum.inl 13, (-25 / 54)), (Sum.inl 52, (-5 / 27)), (Sum.inl 12, (-5 / 27)), (Sum.inl 26, (-10 / 27)), (Sum.inl 4, (-5 / 27)), (Sum.inl 1, (65 / 864))]

def nodeValue323 : Sparse Master := [(Sum.inl 0, (13 / 864)), (Sum.inl 5, (-5 / 216)), (Sum.inl 6, (5 / 432)), (Sum.inl 2, (5 / 216)), (Sum.inl 35, (5 / 54)), (Sum.inl 3, (5 / 27)), (Sum.inl 13, (5 / 27)), (Sum.inl 52, (5 / 27)), (Sum.inl 1, (65 / 864))]

def nodeValue324 : Sparse Master := [(Sum.inl 0, (1 / 54)), (Sum.inl 5, (-5 / 108)), (Sum.inl 67, (5 / 54)), (Sum.inl 34, (5 / 54)), (Sum.inl 2, (-5 / 144)), (Sum.inl 7, (5 / 54)), (Sum.inl 35, (5 / 27)), (Sum.inl 3, (5 / 27)), (Sum.inl 13, (5 / 54)), (Sum.inl 26, (5 / 27)), (Sum.inl 1, (5 / 432))]

def nodeValue325 : Sparse Master := [(Sum.inl 0, (11 / 288)), (Sum.inl 5, (-5 / 54)), (Sum.inl 2, (55 / 864)), (Sum.inl 7, (5 / 54)), (Sum.inl 8, (5 / 54)), (Sum.inl 3, (5 / 54)), (Sum.inl 1, (5 / 432))]

def nodeValue326 : Sparse Master := [(Sum.inl 0, (23 / 864)), (Sum.inl 5, (5 / 54)), (Sum.inl 6, (-5 / 432)), (Sum.inl 2, (-65 / 864)), (Sum.inl 7, (-5 / 27)), (Sum.inl 35, (-5 / 54)), (Sum.inl 8, (-5 / 54)), (Sum.inl 51, (5 / 18)), (Sum.inl 3, (-10 / 27)), (Sum.inl 13, (-5 / 27)), (Sum.inl 52, (-5 / 54)), (Sum.inl 12, (-5 / 27)), (Sum.inl 1, (35 / 432))]

def nodeValue327 : Sparse Master := [(Sum.inl 0, (17 / 864)), (Sum.inl 5, (5 / 108)), (Sum.inl 6, (-5 / 432)), (Sum.inl 64, (5 / 18)), (Sum.inl 67, (-5 / 27)), (Sum.inl 34, (-25 / 54)), (Sum.inl 7, (-5 / 54)), (Sum.inl 35, (-5 / 18)), (Sum.inl 3, (-55 / 54)), (Sum.inl 13, (-10 / 27)), (Sum.inl 52, (-5 / 54)), (Sum.inl 26, (-20 / 27)), (Sum.inl 4, (-5 / 27)), (Sum.inl 1, (35 / 288))]

def nodeValue328 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 5, (-5 / 108)), (Sum.inl 64, (-5 / 18)), (Sum.inl 67, (5 / 54)), (Sum.inl 34, (5 / 54)), (Sum.inl 2, (55 / 864)), (Sum.inl 7, (5 / 54)), (Sum.inl 35, (5 / 54)), (Sum.inl 3, (5 / 27)), (Sum.inl 26, (5 / 27)), (Sum.inl 1, (5 / 288))]

def nodeValue329 : Sparse Master := [(Sum.inl 0, (19 / 864)), (Sum.inl 5, (-5 / 72)), (Sum.inl 2, (5 / 108)), (Sum.inl 7, (5 / 54)), (Sum.inl 8, (5 / 54)), (Sum.inl 51, (-5 / 18)), (Sum.inl 3, (5 / 54)), (Sum.inl 1, (25 / 864))]

def nodeValue330 : Sparse Master := [(Sum.inl 0, (23 / 864)), (Sum.inl 5, (-5 / 72)), (Sum.inl 6, (5 / 288)), (Sum.inl 33, (5 / 18)), (Sum.inl 67, (-5 / 54)), (Sum.inl 34, (-5 / 27)), (Sum.inl 2, (-55 / 864)), (Sum.inl 81, (5 / 18)), (Sum.inl 7, (-5 / 54)), (Sum.inl 35, (-5 / 27)), (Sum.inl 3, (-5 / 6)), (Sum.inl 13, (-5 / 54)), (Sum.inl 12, (-5 / 54)), (Sum.inl 26, (-25 / 54)), (Sum.inl 4, (-5 / 18)), (Sum.inl 1, (-5 / 864))]

def nodeValue331 : Sparse Master := [(Sum.inl 0, (17 / 864)), (Sum.inl 5, (-5 / 108)), (Sum.inl 6, (5 / 288)), (Sum.inl 2, (-25 / 216)), (Sum.inl 7, (-5 / 18)), (Sum.inl 35, (-5 / 27)), (Sum.inl 3, (-10 / 9)), (Sum.inl 26, (-5 / 9)), (Sum.inl 4, (-5 / 9)), (Sum.inl 1, (25 / 216))]

def nodeValue332 : Sparse Master := [(Sum.inl 0, (7 / 216)), (Sum.inl 5, (5 / 216)), (Sum.inl 6, (-5 / 864)), (Sum.inl 2, (5 / 288)), (Sum.inl 7, (5 / 54)), (Sum.inl 35, (5 / 54)), (Sum.inl 3, (5 / 18)), (Sum.inl 26, (5 / 27)), (Sum.inl 4, (5 / 54)), (Sum.inl 1, (-5 / 54))]

def nodeValue333 : Sparse Master := [(Sum.inl 0, (7 / 432)), (Sum.inl 5, (5 / 216)), (Sum.inl 6, (-5 / 864)), (Sum.inl 33, (-5 / 18)), (Sum.inl 2, (25 / 864)), (Sum.inl 81, (-5 / 18)), (Sum.inl 3, (5 / 27)), (Sum.inl 26, (5 / 54)), (Sum.inl 4, (5 / 54)), (Sum.inl 1, (5 / 108))]

def nodeValue334 : Sparse Master := [(Sum.inl 0, (49 / 864)), (Sum.inl 6, (5 / 288)), (Sum.inl 2, (-55 / 432)), (Sum.inl 7, (-5 / 54)), (Sum.inl 8, (-5 / 27)), (Sum.inl 3, (-5 / 27)), (Sum.inl 1, (-35 / 432))]

def nodeValue335 : Sparse Master := [(Sum.inl 0, (19 / 432)), (Sum.inl 6, (-5 / 864)), (Sum.inl 2, (-5 / 864)), (Sum.inl 7, (5 / 54)), (Sum.inl 3, (5 / 54)), (Sum.inl 1, (95 / 432))]

def nodeValue336 : Sparse Master := [(Sum.inl 0, (47 / 864)), (Sum.inl 6, (-5 / 864)), (Sum.inl 2, (5 / 144)), (Sum.inl 8, (5 / 54)), (Sum.inl 1, (-5 / 216))]

def nodeValue337 : Sparse Master := [(Sum.inl 0, (1 / 54)), (Sum.inl 5, (5 / 216)), (Sum.inl 6, (-5 / 864)), (Sum.inl 2, (5 / 864)), (Sum.inl 7, (5 / 54)), (Sum.inl 35, (5 / 54)), (Sum.inl 13, (5 / 54)), (Sum.inl 12, (5 / 54)), (Sum.inl 1, (65 / 432))]

def nodeValue338 : Sparse Master := [(Sum.inl 0, (19 / 432)), (Sum.inl 5, (5 / 108)), (Sum.inl 6, (5 / 432)), (Sum.inl 1, (25 / 108))]

def nodeValue339 : Sparse Master := [(Sum.inl 0, (37 / 864)), (Sum.inl 6, (-5 / 864)), (Sum.inl 2, (25 / 432)), (Sum.inl 7, (5 / 54)), (Sum.inl 3, (5 / 27)), (Sum.inl 1, (-35 / 432))]

def nodeValue340 : Sparse Master := [(Sum.inl 0, (7 / 288)), (Sum.inl 5, (5 / 216)), (Sum.inl 6, (-5 / 864)), (Sum.inl 67, (5 / 54)), (Sum.inl 34, (5 / 27)), (Sum.inl 2, (5 / 108)), (Sum.inl 35, (5 / 54)), (Sum.inl 3, (5 / 18)), (Sum.inl 13, (5 / 54)), (Sum.inl 26, (5 / 18)), (Sum.inl 4, (5 / 54)), (Sum.inl 1, (5 / 216))]

def nodeValue341 : Sparse Master := [(Sum.inl 0, (19 / 432)), (Sum.inl 5, (5 / 108)), (Sum.inl 6, (5 / 432)), (Sum.inl 2, (-5 / 72)), (Sum.inl 1, (-25 / 216))]

def nodeValue342 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 5, (-5 / 108)), (Sum.inl 67, (-5 / 27)), (Sum.inl 34, (-5 / 27)), (Sum.inl 2, (5 / 432)), (Sum.inl 26, (-5 / 27)), (Sum.inl 1, (5 / 216))]

def nodeValue343 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 5, (-5 / 108)), (Sum.inl 2, (5 / 432)), (Sum.inl 7, (-5 / 27)), (Sum.inl 3, (-5 / 27)), (Sum.inl 1, (35 / 216))]

def nodeValue344 : Sparse Master := [(Sum.inl 0, (1 / 18)), (Sum.inl 5, (-5 / 108)), (Sum.inl 8, (-5 / 27)), (Sum.inl 1, (-5 / 108))]

def nodeValue345 : Sparse Master := [(Sum.inl 0, (7 / 288)), (Sum.inl 5, (5 / 108)), (Sum.inl 6, (-5 / 864)), (Sum.inl 64, (5 / 18)), (Sum.inl 34, (-5 / 54)), (Sum.inl 2, (-95 / 864)), (Sum.inl 7, (-5 / 54)), (Sum.inl 35, (-5 / 54)), (Sum.inl 51, (5 / 9)), (Sum.inl 3, (-25 / 27)), (Sum.inl 13, (-35 / 54)), (Sum.inl 52, (-5 / 18)), (Sum.inl 54, (5 / 18)), (Sum.inl 12, (-10 / 27)), (Sum.inl 1, (5 / 96))]

def nodeValue346 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 5, (-5 / 108)), (Sum.inl 64, (-5 / 18)), (Sum.inl 2, (5 / 96)), (Sum.inl 7, (5 / 54)), (Sum.inl 51, (-5 / 18)), (Sum.inl 3, (5 / 54)), (Sum.inl 54, (-5 / 18)), (Sum.inl 1, (-35 / 864))]

def nodeValue347 : Sparse Master := [(Sum.inl 0, (7 / 288)), (Sum.inl 5, (-5 / 72)), (Sum.inl 6, (5 / 288)), (Sum.inl 64, (5 / 18)), (Sum.inl 33, (5 / 9)), (Sum.inl 34, (-5 / 54)), (Sum.inl 2, (-5 / 54)), (Sum.inl 123, (5 / 9)), (Sum.inl 51, (5 / 9)), (Sum.inl 3, (-35 / 54)), (Sum.inl 13, (-5 / 27)), (Sum.inl 52, (-5 / 54)), (Sum.inl 12, (-5 / 27)), (Sum.inl 25, (5 / 18)), (Sum.inl 26, (-5 / 27)), (Sum.inl 4, (-5 / 27)), (Sum.inl 31, (5 / 9))]

def nodeValue348 : Sparse Master := [(Sum.inl 0, (7 / 288)), (Sum.inl 5, (5 / 216)), (Sum.inl 6, (-5 / 864)), (Sum.inl 64, (-5 / 18)), (Sum.inl 2, (35 / 864)), (Sum.inl 123, (-5 / 18)), (Sum.inl 3, (5 / 54)), (Sum.inl 25, (-5 / 18)), (Sum.inl 26, (5 / 54)), (Sum.inl 1, (-5 / 96))]

def nodeValue349 : Sparse Master := [(Sum.inl 0, (5 / 288)), (Sum.inl 5, (5 / 216)), (Sum.inl 6, (-5 / 864)), (Sum.inl 33, (-5 / 18)), (Sum.inl 2, (5 / 432)), (Sum.inl 123, (-5 / 18)), (Sum.inl 51, (-5 / 18)), (Sum.inl 1, (5 / 216)), (Sum.inl 31, (-5 / 18))]

def nodeValue350 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 6, (5 / 432)), (Sum.inl 123, (5 / 9)), (Sum.inl 1, (-5 / 144))]

def nodeValue351 : Sparse Master := [(Sum.inl 0, (25 / 864)), (Sum.inl 5, (-5 / 72)), (Sum.inl 6, (5 / 288)), (Sum.inl 2, (-25 / 144)), (Sum.inl 51, (5 / 6)), (Sum.inl 3, (-5 / 6)), (Sum.inl 13, (-5 / 27)), (Sum.inl 52, (-5 / 18)), (Sum.inl 12, (-5 / 18)), (Sum.inl 4, (-5 / 18)), (Sum.inl 1, (5 / 144))]

def nodeValue352 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 5, (5 / 216)), (Sum.inl 6, (-5 / 864)), (Sum.inl 2, (25 / 864)), (Sum.inl 51, (-5 / 18)), (Sum.inl 3, (5 / 27)), (Sum.inl 52, (5 / 54)), (Sum.inl 4, (5 / 54)), (Sum.inl 1, (5 / 432))]

def nodeValue353 : Sparse Master := [(Sum.inl 0, (1 / 32)), (Sum.inl 5, (5 / 216)), (Sum.inl 6, (-5 / 864)), (Sum.inl 2, (5 / 108)), (Sum.inl 51, (-5 / 18)), (Sum.inl 3, (5 / 27)), (Sum.inl 13, (5 / 54)), (Sum.inl 52, (5 / 54)), (Sum.inl 12, (5 / 54)), (Sum.inl 1, (-25 / 432))]

def nodeValue354 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 5, (-5 / 108)), (Sum.inl 64, (5 / 9)), (Sum.inl 1, (-5 / 144))]

def nodeValue355 : Sparse Master := [(Sum.inl 0, (7 / 216)), (Sum.inl 5, (-5 / 108)), (Sum.inl 2, (5 / 144)), (Sum.inl 51, (5 / 9)), (Sum.inl 1, (-5 / 144))]

def nodeValue356 : Sparse Master := [(Sum.inl 0, (19 / 864)), (Sum.inl 5, (-5 / 54)), (Sum.inl 264, (5 / 18)), (Sum.inl 266, (5 / 18)), (Sum.inl 63, (5 / 9)), (Sum.inl 64, (5 / 18)), (Sum.inl 65, (5 / 9)), (Sum.inl 33, (5 / 18)), (Sum.inl 68, (5 / 18)), (Sum.inl 2, (25 / 432)), (Sum.inl 35, (-5 / 54)), (Sum.inl 125, (5 / 18)), (Sum.inl 3, (-5 / 27)), (Sum.inl 13, (-5 / 54)), (Sum.inl 196, (5 / 18)), (Sum.inl 23, (5 / 9)), (Sum.inl 54, (5 / 9)), (Sum.inl 55, (5 / 9)), (Sum.inl 12, (-5 / 54)), (Sum.inl 25, (5 / 18)), (Sum.inl 26, (-5 / 54)), (Sum.inl 27, (5 / 36)), (Sum.inl 1, (-25 / 864))]

def nodeValue357 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 5, (5 / 216)), (Sum.inl 63, (5 / 18)), (Sum.inl 65, (5 / 18)), (Sum.inl 67, (-5 / 54)), (Sum.inl 34, (-5 / 27)), (Sum.inl 2, (-25 / 864)), (Sum.inl 7, (-5 / 54)), (Sum.inl 35, (-5 / 18)), (Sum.inl 3, (-20 / 27)), (Sum.inl 13, (-5 / 9)), (Sum.inl 23, (5 / 18)), (Sum.inl 55, (5 / 9)), (Sum.inl 12, (-5 / 18)), (Sum.inl 26, (-10 / 27)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (5 / 96))]

def nodeValue358 : Sparse Master := [(Sum.inl 0, (31 / 864)), (Sum.inl 5, (-5 / 72)), (Sum.inl 63, (5 / 18)), (Sum.inl 64, (5 / 9)), (Sum.inl 33, (5 / 6)), (Sum.inl 2, (5 / 864)), (Sum.inl 35, (-5 / 54)), (Sum.inl 3, (-5 / 9)), (Sum.inl 13, (-5 / 18)), (Sum.inl 55, (5 / 9)), (Sum.inl 12, (-5 / 27)), (Sum.inl 25, (5 / 18)), (Sum.inl 26, (-5 / 54)), (Sum.inl 27, (5 / 24)), (Sum.inl 1, (-35 / 432))]

def nodeValue359 : Sparse Master := [(Sum.inl 0, (1 / 48)), (Sum.inl 5, (5 / 216)), (Sum.inl 64, (5 / 18)), (Sum.inl 33, (5 / 18)), (Sum.inl 66, (5 / 18)), (Sum.inl 67, (-5 / 54)), (Sum.inl 34, (-5 / 27)), (Sum.inl 2, (-25 / 864)), (Sum.inl 7, (-5 / 54)), (Sum.inl 35, (-5 / 27)), (Sum.inl 3, (-25 / 27)), (Sum.inl 13, (-5 / 54)), (Sum.inl 24, (5 / 18)), (Sum.inl 55, (5 / 6)), (Sum.inl 12, (-5 / 54)), (Sum.inl 26, (-5 / 9)), (Sum.inl 4, (-10 / 27)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (145 / 864))]

def nodeValue360 : Sparse Master := [(Sum.inl 0, (17 / 432)), (Sum.inl 5, (-5 / 72)), (Sum.inl 2, (35 / 288)), (Sum.inl 35, (-5 / 18)), (Sum.inl 3, (-10 / 9)), (Sum.inl 13, (-5 / 27)), (Sum.inl 55, (5 / 6)), (Sum.inl 12, (-5 / 18)), (Sum.inl 26, (-5 / 9)), (Sum.inl 4, (-5 / 9)), (Sum.inl 27, (5 / 24)), (Sum.inl 1, (25 / 288))]

def nodeValue361 : Sparse Master := [(Sum.inl 0, (31 / 864)), (Sum.inl 5, (5 / 216)), (Sum.inl 2, (-5 / 72)), (Sum.inl 35, (5 / 54)), (Sum.inl 3, (5 / 27)), (Sum.inl 13, (5 / 54)), (Sum.inl 55, (-5 / 18)), (Sum.inl 12, (5 / 54)), (Sum.inl 26, (5 / 54)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (-25 / 288))]

def nodeValue362 : Sparse Master := [(Sum.inl 0, (17 / 864)), (Sum.inl 5, (5 / 216)), (Sum.inl 64, (-5 / 18)), (Sum.inl 33, (-5 / 18)), (Sum.inl 2, (-5 / 96)), (Sum.inl 3, (5 / 54)), (Sum.inl 55, (-5 / 18)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (5 / 144))]

def nodeValue363 : Sparse Master := [(Sum.inl 0, (25 / 864)), (Sum.inl 5, (5 / 216)), (Sum.inl 63, (5 / 9)), (Sum.inl 64, (5 / 9)), (Sum.inl 65, (5 / 18)), (Sum.inl 33, (5 / 9)), (Sum.inl 67, (-5 / 54)), (Sum.inl 34, (-5 / 27)), (Sum.inl 2, (-5 / 864)), (Sum.inl 7, (-5 / 54)), (Sum.inl 35, (-5 / 54)), (Sum.inl 3, (-35 / 54)), (Sum.inl 13, (-5 / 54)), (Sum.inl 23, (5 / 18)), (Sum.inl 55, (5 / 18)), (Sum.inl 12, (-5 / 54)), (Sum.inl 25, (5 / 9)), (Sum.inl 26, (-10 / 27)), (Sum.inl 4, (-5 / 27)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (5 / 144))]

def nodeValue364 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 63, (-5 / 18)), (Sum.inl 65, (-5 / 18)), (Sum.inl 2, (-5 / 216)), (Sum.inl 23, (-5 / 18)), (Sum.inl 55, (-5 / 18)), (Sum.inl 27, (5 / 36)), (Sum.inl 1, (-25 / 432))]

def nodeValue365 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 5, (5 / 216)), (Sum.inl 63, (-5 / 18)), (Sum.inl 64, (-5 / 18)), (Sum.inl 33, (-5 / 18)), (Sum.inl 2, (-5 / 108)), (Sum.inl 25, (-5 / 18)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (-5 / 108))]

def nodeValue366 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 63, (5 / 9)), (Sum.inl 2, (65 / 432)), (Sum.inl 27, (5 / 36)), (Sum.inl 1, (-5 / 216))]

def nodeValue367 : Sparse Master := [(Sum.inl 0, (7 / 432)), (Sum.inl 66, (-5 / 18)), (Sum.inl 2, (5 / 432)), (Sum.inl 24, (-5 / 18)), (Sum.inl 55, (-5 / 9)), (Sum.inl 27, (5 / 36)), (Sum.inl 1, (5 / 72))]

def nodeValue368 : Sparse Master := [(Sum.inl 0, (29 / 864)), (Sum.inl 5, (5 / 216)), (Sum.inl 35, (5 / 54)), (Sum.inl 3, (5 / 18)), (Sum.inl 55, (-5 / 18)), (Sum.inl 26, (5 / 27)), (Sum.inl 4, (5 / 27)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (-5 / 864))]

def nodeValue369 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 2, (-5 / 144)), (Sum.inl 55, (5 / 9)), (Sum.inl 27, (5 / 36)), (Sum.inl 1, (-5 / 72))]

def nodeValue370 : Sparse Master := [(Sum.inl 0, (25 / 432)), (Sum.inl 5, (-5 / 216)), (Sum.inl 2, (-5 / 108)), (Sum.inl 35, (-5 / 54)), (Sum.inl 3, (-10 / 27)), (Sum.inl 13, (-5 / 54)), (Sum.inl 55, (5 / 18)), (Sum.inl 12, (-5 / 54)), (Sum.inl 26, (-5 / 27)), (Sum.inl 27, (5 / 72)), (Sum.inl 1, (-25 / 432))]

def nodeValue371 : Sparse Master := [(Sum.inl 0, (35 / 864)), (Sum.inl 5, (-5 / 216)), (Sum.inl 2, (5 / 108)), (Sum.inl 35, (-5 / 54)), (Sum.inl 3, (-35 / 54)), (Sum.inl 55, (5 / 18)), (Sum.inl 26, (-10 / 27)), (Sum.inl 4, (-10 / 27)), (Sum.inl 27, (5 / 72)), (Sum.inl 1, (205 / 864))]

def nodeValue372 : Sparse Master := [(Sum.inl 0, (19 / 432)), (Sum.inl 2, (-25 / 432)), (Sum.inl 3, (5 / 54)), (Sum.inl 55, (-5 / 18)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (-5 / 216))]

def nodeValue373 : Sparse Master := [(Sum.inl 0, (11 / 864)), (Sum.inl 34, (-5 / 27)), (Sum.inl 2, (-5 / 108)), (Sum.inl 3, (-5 / 18)), (Sum.inl 13, (-25 / 54)), (Sum.inl 12, (-5 / 27)), (Sum.inl 26, (-5 / 27)), (Sum.inl 1, (5 / 96))]

def nodeValue374 : Sparse Master := [(Sum.inl 0, (1 / 108)), (Sum.inl 2, (5 / 144)), (Sum.inl 13, (5 / 27)), (Sum.inl 1, (5 / 144))]

def nodeValue375 : Sparse Master := []

def nodeValue376 : Sparse Master := [(Sum.inl 0, (17 / 864)), (Sum.inl 2, (-5 / 288)), (Sum.inl 3, (-25 / 54)), (Sum.inl 26, (-5 / 27)), (Sum.inl 4, (-5 / 27)), (Sum.inl 1, (55 / 216))]

def nodeValue377 : Sparse Master := [(Sum.inl 0, (17 / 432)), (Sum.inl 2, (-5 / 96)), (Sum.inl 3, (5 / 54)), (Sum.inl 26, (5 / 54)), (Sum.inl 1, (-35 / 864))]

def nodeValue378 : Sparse Master := [(Sum.inl 0, (29 / 864)), (Sum.inl 2, (-35 / 864)), (Sum.inl 3, (5 / 54)), (Sum.inl 1, (-5 / 216))]

def nodeValue379 : Sparse Master := [(Sum.inl 0, (1 / 24)), (Sum.inl 2, (5 / 24))]

def nodeValue380 : Sparse Master := [(Sum.inl 0, (31 / 864)), (Sum.inl 5, (-5 / 108)), (Sum.inl 6, (5 / 864)), (Sum.inl 65, (5 / 18)), (Sum.inl 33, (5 / 9)), (Sum.inl 67, (-5 / 54)), (Sum.inl 34, (-10 / 27)), (Sum.inl 2, (5 / 432)), (Sum.inl 35, (-5 / 54)), (Sum.inl 3, (-65 / 54)), (Sum.inl 13, (-5 / 9)), (Sum.inl 54, (5 / 18)), (Sum.inl 12, (-10 / 27)), (Sum.inl 26, (-5 / 9)), (Sum.inl 4, (-10 / 27)), (Sum.inl 27, (5 / 72)), (Sum.inl 1, (5 / 48))]

def nodeValue381 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 5, (5 / 216)), (Sum.inl 65, (-5 / 18)), (Sum.inl 33, (-5 / 18)), (Sum.inl 2, (-35 / 864)), (Sum.inl 3, (5 / 54)), (Sum.inl 54, (-5 / 18)), (Sum.inl 26, (5 / 54)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (-55 / 864))]

def nodeValue382 : Sparse Master := [(Sum.inl 0, (7 / 432)), (Sum.inl 33, (5 / 9)), (Sum.inl 34, (-5 / 27)), (Sum.inl 2, (-35 / 864)), (Sum.inl 3, (-10 / 9)), (Sum.inl 13, (-35 / 54)), (Sum.inl 12, (-5 / 9)), (Sum.inl 26, (-5 / 27)), (Sum.inl 4, (-5 / 27)), (Sum.inl 1, (155 / 864))]

def nodeValue383 : Sparse Master := [(Sum.inl 0, (1 / 72)), (Sum.inl 33, (-5 / 18)), (Sum.inl 2, (-5 / 864)), (Sum.inl 3, (5 / 27)), (Sum.inl 13, (5 / 27)), (Sum.inl 12, (5 / 54)), (Sum.inl 1, (-5 / 864))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue3202 : Sparse Master := [(Sum.inr 3202, (1 / 1))]

def nodeValue3203 : Sparse Master := [(Sum.inl 0, (-31 / 4320)), (Sum.inl 5, (-1 / 72)), (Sum.inl 6, (1 / 432)), (Sum.inl 2, (-1 / 432)), (Sum.inl 7, (1 / 54)), (Sum.inl 35, (1 / 18)), (Sum.inl 3, (4 / 27)), (Sum.inl 13, (1 / 6)), (Sum.inl 52, (1 / 27)), (Sum.inl 54, (-1 / 18)), (Sum.inl 12, (2 / 27)), (Sum.inl 1, (-13 / 864))]

def nodeValue3204 : Sparse Master := [(Sum.inl 0, (-37 / 4320)), (Sum.inl 5, (-5 / 216)), (Sum.inl 6, (1 / 288)), (Sum.inl 2, (-7 / 864)), (Sum.inl 35, (1 / 54)), (Sum.inl 8, (1 / 54)), (Sum.inl 3, (1 / 18)), (Sum.inl 13, (1 / 27)), (Sum.inl 52, (1 / 54)), (Sum.inl 56, (-1 / 18)), (Sum.inl 26, (1 / 54)), (Sum.inl 4, (1 / 54)), (Sum.inl 1, (-17 / 864))]

def nodeValue3205 : Sparse Master := [(Sum.inl 0, (-7 / 720)), (Sum.inl 5, (-1 / 54)), (Sum.inl 6, (1 / 216)), (Sum.inl 2, (1 / 72)), (Sum.inl 7, (1 / 54)), (Sum.inl 35, (1 / 27)), (Sum.inl 3, (1 / 27)), (Sum.inl 13, (1 / 54)), (Sum.inl 54, (-1 / 18)), (Sum.inl 26, (1 / 27)), (Sum.inl 1, (5 / 432))]

def nodeValue3206 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 5, (1 / 72)), (Sum.inl 2, (5 / 864)), (Sum.inl 7, (-1 / 54)), (Sum.inl 35, (-1 / 54)), (Sum.inl 3, (-1 / 54)), (Sum.inl 13, (-1 / 54)), (Sum.inl 54, (1 / 18)), (Sum.inl 1, (11 / 864))]

def nodeValue3207 : Sparse Master := [(Sum.inl 0, (-17 / 2160)), (Sum.inl 5, (1 / 54)), (Sum.inl 2, (-1 / 108)), (Sum.inl 8, (-1 / 54)), (Sum.inl 56, (1 / 18)), (Sum.inl 1, (-7 / 432))]

def nodeValue3209 : Sparse Master := [(Sum.inl 0, (-47 / 4320)), (Sum.inl 5, (1 / 216)), (Sum.inl 6, (-1 / 432)), (Sum.inl 2, (5 / 216)), (Sum.inl 35, (1 / 54)), (Sum.inl 3, (2 / 27)), (Sum.inl 13, (2 / 27)), (Sum.inl 52, (1 / 27)), (Sum.inl 12, (1 / 54)), (Sum.inl 1, (7 / 288))]

def nodeValue3210 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 5, (-1 / 216)), (Sum.inl 6, (1 / 864)), (Sum.inl 2, (1 / 288)), (Sum.inl 35, (-1 / 54)), (Sum.inl 3, (-1 / 27)), (Sum.inl 13, (-1 / 18)), (Sum.inl 52, (-1 / 54)), (Sum.inl 12, (-1 / 54)), (Sum.inl 1, (1 / 108))]

def nodeValue3211 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 6, (1 / 864)), (Sum.inl 2, (1 / 144)), (Sum.inl 3, (-1 / 54)), (Sum.inl 13, (-1 / 54)), (Sum.inl 52, (-1 / 54)), (Sum.inl 1, (1 / 288))]

def nodeValue3212 : Sparse Master := []

def nodeValue3213 : Sparse Master := []

def nodeValue3214 : Sparse Master := []

def nodeValue3215 : Sparse Master := []

def nodeValue3216 : Sparse Master := []

def nodeValue3217 : Sparse Master := [(Sum.inr 3217, (1 / 1))]

def nodeValue3221 : Sparse Master := [(Sum.inr 3221, (1 / 1))]

def nodeValue3222 : Sparse Master := [(Sum.inr 3222, (1 / 1))]

def nodeValue3223 : Sparse Master := [(Sum.inl 0, (-13 / 2160)), (Sum.inl 2, (-1 / 864)), (Sum.inl 3, (-1 / 27)), (Sum.inl 13, (-1 / 18)), (Sum.inl 12, (-1 / 54)), (Sum.inl 1, (5 / 864))]

def nodeValue3224 : Sparse Master := [(Sum.inl 0, (-1 / 180)), (Sum.inl 2, (1 / 72)), (Sum.inl 13, (2 / 27)), (Sum.inl 12, (1 / 27)), (Sum.inl 1, (-1 / 72))]

def nodeValue3225 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 2, (1 / 54)), (Sum.inl 3, (1 / 27)), (Sum.inl 13, (1 / 27)), (Sum.inl 1, (11 / 432))]

def nodeValue3226 : Sparse Master := [(Sum.inl 0, (-13 / 2160)), (Sum.inl 2, (-1 / 54)), (Sum.inl 3, (2 / 27)), (Sum.inl 13, (2 / 27)), (Sum.inl 12, (1 / 54)), (Sum.inl 1, (-23 / 432))]

def nodeValue3227 : Sparse Master := [(Sum.inl 0, (-11 / 1440)), (Sum.inl 2, (1 / 216)), (Sum.inl 3, (-1 / 54)), (Sum.inl 13, (-1 / 54)), (Sum.inl 1, (1 / 864))]

def nodeValue3228 : Sparse Master := []

def nodeValue3229 : Sparse Master := []

def nodeValue3230 : Sparse Master := []

def nodeValue3231 : Sparse Master := []

def nodeValue3232 : Sparse Master := [(Sum.inr 3232, (1 / 1))]

def nodeValue3233 : Sparse Master := [(Sum.inr 3233, (1 / 1))]

def nodeValue3234 : Sparse Master := [(Sum.inr 3234, (1 / 1))]

def nodeValue3235 : Sparse Master := [(Sum.inr 3235, (1 / 1))]

def nodeValue3236 : Sparse Master := [(Sum.inr 3236, (1 / 1))]

def nodeValue3237 : Sparse Master := [(Sum.inr 3237, (1 / 1))]

def nodeValue3238 : Sparse Master := [(Sum.inr 3238, (1 / 1))]

def nodeValue3239 : Sparse Master := [(Sum.inr 3239, (1 / 1))]

def nodeValue3240 : Sparse Master := [(Sum.inr 3240, (1 / 1))]

def nodeValue3241 : Sparse Master := [(Sum.inr 3241, (1 / 1))]

def nodeValue3242 : Sparse Master := [(Sum.inr 3242, (1 / 1))]

def nodeValue3243 : Sparse Master := [(Sum.inr 3243, (1 / 1))]

def nodeValue3244 : Sparse Master := [(Sum.inr 3244, (1 / 1))]

def nodeValue3245 : Sparse Master := [(Sum.inr 3245, (1 / 1))]

def nodeValue3246 : Sparse Master := [(Sum.inr 3246, (1 / 1))]

def nodeValue3247 : Sparse Master := [(Sum.inr 3247, (1 / 1))]

def nodeValue3248 : Sparse Master := [(Sum.inr 3248, (1 / 1))]

def nodeValue3249 : Sparse Master := [(Sum.inr 3249, (1 / 1))]

def nodeValue3250 : Sparse Master := [(Sum.inr 3250, (1 / 1))]

def nodeValue3251 : Sparse Master := [(Sum.inr 3251, (1 / 1))]

def nodeValue3252 : Sparse Master := [(Sum.inr 3252, (1 / 1))]

def nodeValue3253 : Sparse Master := [(Sum.inr 3253, (1 / 1))]

def nodeValue3254 : Sparse Master := [(Sum.inr 3254, (1 / 1))]

def nodeValue3255 : Sparse Master := [(Sum.inr 3255, (1 / 1))]

def nodeValue3256 : Sparse Master := [(Sum.inr 3256, (1 / 1))]

def nodeValue3257 : Sparse Master := [(Sum.inr 3257, (1 / 1))]

def nodeValue3258 : Sparse Master := [(Sum.inr 3258, (1 / 1))]

def nodeValue3259 : Sparse Master := [(Sum.inr 3259, (1 / 1))]

def nodeValue3260 : Sparse Master := [(Sum.inr 3260, (1 / 1))]

def nodeValue3261 : Sparse Master := [(Sum.inr 3261, (1 / 1))]

def nodeValue3262 : Sparse Master := [(Sum.inr 3262, (1 / 1))]

def nodeValue3263 : Sparse Master := [(Sum.inr 3263, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue3264 : Sparse Master := [(Sum.inr 3264, (1 / 1))]

def nodeValue3265 : Sparse Master := [(Sum.inr 3265, (1 / 1))]

def nodeValue3266 : Sparse Master := [(Sum.inr 3266, (1 / 1))]

def nodeValue3267 : Sparse Master := [(Sum.inr 3267, (1 / 1))]

def nodeValue3268 : Sparse Master := [(Sum.inr 3268, (1 / 1))]

def nodeValue3269 : Sparse Master := [(Sum.inr 3269, (1 / 1))]

def nodeValue3270 : Sparse Master := [(Sum.inr 3270, (1 / 1))]

def nodeValue3271 : Sparse Master := [(Sum.inr 3271, (1 / 1))]

def nodeValue3272 : Sparse Master := [(Sum.inr 3272, (1 / 1))]

def nodeValue3273 : Sparse Master := [(Sum.inr 3273, (1 / 1))]

def nodeValue3274 : Sparse Master := [(Sum.inr 3274, (1 / 1))]

def nodeValue3275 : Sparse Master := [(Sum.inr 3275, (1 / 1))]

def nodeValue3276 : Sparse Master := [(Sum.inr 3276, (1 / 1))]

def nodeValue3277 : Sparse Master := [(Sum.inr 3277, (1 / 1))]

def nodeValue3278 : Sparse Master := [(Sum.inr 3278, (1 / 1))]

def nodeValue3279 : Sparse Master := [(Sum.inr 3279, (1 / 1))]

def nodeValue3280 : Sparse Master := [(Sum.inr 3280, (1 / 1))]

def nodeValue3281 : Sparse Master := [(Sum.inr 3281, (1 / 1))]

def nodeValue3282 : Sparse Master := [(Sum.inr 3282, (1 / 1))]

def nodeValue3283 : Sparse Master := [(Sum.inr 3283, (1 / 1))]

def nodeValue3284 : Sparse Master := [(Sum.inr 3284, (1 / 1))]

def nodeValue3285 : Sparse Master := [(Sum.inr 3285, (1 / 1))]

def nodeValue3286 : Sparse Master := [(Sum.inr 3286, (1 / 1))]

def nodeValue3287 : Sparse Master := [(Sum.inr 3287, (1 / 1))]

def nodeValue3288 : Sparse Master := [(Sum.inr 3288, (1 / 1))]

def nodeValue3289 : Sparse Master := [(Sum.inr 3289, (1 / 1))]

def nodeValue3290 : Sparse Master := [(Sum.inr 3290, (1 / 1))]

def nodeValue3291 : Sparse Master := [(Sum.inr 3291, (1 / 1))]

def nodeValue3292 : Sparse Master := [(Sum.inr 3292, (1 / 1))]

def nodeValue3293 : Sparse Master := [(Sum.inr 3293, (1 / 1))]

def nodeValue3294 : Sparse Master := [(Sum.inr 3294, (1 / 1))]

def nodeValue3295 : Sparse Master := [(Sum.inr 3295, (1 / 1))]

def nodeValue3296 : Sparse Master := [(Sum.inr 3296, (1 / 1))]

def nodeValue3297 : Sparse Master := [(Sum.inr 3297, (1 / 1))]

def nodeValue3298 : Sparse Master := [(Sum.inr 3298, (1 / 1))]

def nodeValue3299 : Sparse Master := [(Sum.inr 3299, (1 / 1))]

def nodeValue3300 : Sparse Master := [(Sum.inr 3300, (1 / 1))]

def nodeValue3301 : Sparse Master := [(Sum.inr 3301, (1 / 1))]

def nodeValue3302 : Sparse Master := [(Sum.inr 3302, (1 / 1))]

def nodeValue3303 : Sparse Master := [(Sum.inr 3303, (1 / 1))]

def nodeValue3304 : Sparse Master := [(Sum.inr 3304, (1 / 1))]

def nodeValue3305 : Sparse Master := [(Sum.inr 3305, (1 / 1))]

def nodeValue3306 : Sparse Master := [(Sum.inr 3306, (1 / 1))]

def nodeValue3307 : Sparse Master := [(Sum.inr 3307, (1 / 1))]

def nodeValue3308 : Sparse Master := [(Sum.inr 3308, (1 / 1))]

def nodeValue3309 : Sparse Master := [(Sum.inr 3309, (1 / 1))]

def nodeValue3310 : Sparse Master := [(Sum.inr 3310, (1 / 1))]

def nodeValue3311 : Sparse Master := [(Sum.inr 3311, (1 / 1))]

def nodeValue3312 : Sparse Master := [(Sum.inr 3312, (1 / 1))]

def nodeValue3313 : Sparse Master := [(Sum.inr 3313, (1 / 1))]

def nodeValue3315 : Sparse Master := [(Sum.inr 3315, (1 / 1))]

def nodeValue3318 : Sparse Master := [(Sum.inr 3318, (1 / 1))]

def nodeValue3325 : Sparse Master := [(Sum.inr 3325, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue3334 : Sparse Master := [(Sum.inr 3334, (1 / 1))]

def nodeValue3335 : Sparse Master := [(Sum.inr 3335, (1 / 1))]

def nodeValue3336 : Sparse Master := [(Sum.inr 3336, (1 / 1))]

def nodeValue3337 : Sparse Master := [(Sum.inr 3337, (1 / 1))]

def nodeValue3339 : Sparse Master := []

def nodeValue3340 : Sparse Master := [(Sum.inr 3340, (1 / 1))]

def nodeValue3341 : Sparse Master := [(Sum.inr 3341, (1 / 1))]

def nodeValue3342 : Sparse Master := [(Sum.inr 3342, (1 / 1))]

def nodeValue3343 : Sparse Master := [(Sum.inr 3343, (1 / 1))]

def nodeValue3344 : Sparse Master := [(Sum.inr 3344, (1 / 1))]

def nodeValue3345 : Sparse Master := [(Sum.inr 3345, (1 / 1))]

def nodeValue3346 : Sparse Master := [(Sum.inr 3346, (1 / 1))]

def nodeValue3347 : Sparse Master := [(Sum.inr 3347, (1 / 1))]

def nodeValue3348 : Sparse Master := [(Sum.inr 3348, (1 / 1))]

def nodeValue3349 : Sparse Master := [(Sum.inr 3349, (1 / 1))]

def nodeValue3350 : Sparse Master := [(Sum.inr 3350, (1 / 1))]

def nodeValue3351 : Sparse Master := []

def nodeValue3352 : Sparse Master := [(Sum.inr 3352, (1 / 1))]

def nodeValue3353 : Sparse Master := [(Sum.inr 3353, (1 / 1))]

def nodeValue3354 : Sparse Master := [(Sum.inr 3354, (1 / 1))]

def nodeValue3355 : Sparse Master := [(Sum.inr 3355, (1 / 1))]

def nodeValue3357 : Sparse Master := [(Sum.inr 3357, (1 / 1))]

def nodeValue3358 : Sparse Master := [(Sum.inr 3358, (1 / 1))]

def nodeValue3360 : Sparse Master := [(Sum.inr 3360, (1 / 1))]

def nodeValue3365 : Sparse Master := [(Sum.inr 3365, (1 / 1))]

def nodeValue3368 : Sparse Master := [(Sum.inr 3368, (1 / 1))]

def nodeValue3370 : Sparse Master := [(Sum.inr 3370, (1 / 1))]

def nodeValue3372 : Sparse Master := [(Sum.inr 3372, (1 / 1))]

def nodeValue3373 : Sparse Master := [(Sum.inr 3373, (1 / 1))]

def nodeValue3374 : Sparse Master := [(Sum.inr 3374, (1 / 1))]

def nodeValue3375 : Sparse Master := [(Sum.inr 3375, (1 / 1))]

def nodeValue3376 : Sparse Master := [(Sum.inr 3376, (1 / 1))]

def nodeValue3377 : Sparse Master := [(Sum.inr 3377, (1 / 1))]

def nodeValue3378 : Sparse Master := [(Sum.inr 3378, (1 / 1))]

def nodeValue3379 : Sparse Master := [(Sum.inr 3379, (1 / 1))]

def nodeValue3380 : Sparse Master := [(Sum.inr 3380, (1 / 1))]

def nodeValue3382 : Sparse Master := [(Sum.inr 3382, (1 / 1))]

def nodeValue3383 : Sparse Master := [(Sum.inr 3383, (1 / 1))]

def nodeValue3384 : Sparse Master := [(Sum.inr 3384, (1 / 1))]

def nodeValue3385 : Sparse Master := [(Sum.inr 3385, (1 / 1))]

def nodeValue3386 : Sparse Master := [(Sum.inr 3386, (1 / 1))]

def nodeValue3387 : Sparse Master := [(Sum.inr 3387, (1 / 1))]

def nodeValue3388 : Sparse Master := [(Sum.inr 3388, (1 / 1))]

def nodeValue3389 : Sparse Master := [(Sum.inr 3389, (1 / 1))]

def nodeValue3390 : Sparse Master := [(Sum.inr 3390, (1 / 1))]

def nodeValue3391 : Sparse Master := [(Sum.inr 3391, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue3392 : Sparse Master := [(Sum.inr 3392, (1 / 1))]

def nodeValue3393 : Sparse Master := [(Sum.inr 3393, (1 / 1))]

def nodeValue3394 : Sparse Master := [(Sum.inr 3394, (1 / 1))]

def nodeValue3395 : Sparse Master := [(Sum.inr 3395, (1 / 1))]

def nodeValue3396 : Sparse Master := [(Sum.inr 3396, (1 / 1))]

def nodeValue3397 : Sparse Master := [(Sum.inr 3397, (1 / 1))]

def nodeValue3398 : Sparse Master := [(Sum.inr 3398, (1 / 1))]

def nodeValue3399 : Sparse Master := [(Sum.inr 3399, (1 / 1))]

def nodeValue3400 : Sparse Master := [(Sum.inr 3400, (1 / 1))]

def nodeValue3401 : Sparse Master := [(Sum.inr 3401, (1 / 1))]

def nodeValue3402 : Sparse Master := [(Sum.inr 3402, (1 / 1))]

def nodeValue3403 : Sparse Master := []

def nodeValue3404 : Sparse Master := [(Sum.inr 3404, (1 / 1))]

def nodeValue3405 : Sparse Master := []

def nodeValue3406 : Sparse Master := [(Sum.inr 3406, (1 / 1))]

def nodeValue3407 : Sparse Master := [(Sum.inr 3407, (1 / 1))]

def nodeValue3408 : Sparse Master := [(Sum.inr 3408, (1 / 1))]

def nodeValue3409 : Sparse Master := []

def nodeValue3410 : Sparse Master := [(Sum.inr 3410, (1 / 1))]

def nodeValue3411 : Sparse Master := [(Sum.inr 3411, (1 / 1))]

def nodeValue3412 : Sparse Master := [(Sum.inr 3412, (1 / 1))]

def nodeValue3413 : Sparse Master := [(Sum.inr 3413, (1 / 1))]

def nodeValue3414 : Sparse Master := [(Sum.inr 3414, (1 / 1))]

def nodeValue3415 : Sparse Master := [(Sum.inr 3415, (1 / 1))]

def nodeValue3416 : Sparse Master := [(Sum.inr 3416, (1 / 1))]

def nodeValue3417 : Sparse Master := [(Sum.inr 3417, (1 / 1))]

def nodeValue3418 : Sparse Master := [(Sum.inr 3418, (1 / 1))]

def nodeValue3419 : Sparse Master := [(Sum.inr 3419, (1 / 1))]

def nodeValue3420 : Sparse Master := [(Sum.inr 3420, (1 / 1))]

def nodeValue3421 : Sparse Master := [(Sum.inr 3421, (1 / 1))]

def nodeValue3422 : Sparse Master := [(Sum.inr 3422, (1 / 1))]

def nodeValue3423 : Sparse Master := [(Sum.inr 3423, (1 / 1))]

def nodeValue3425 : Sparse Master := [(Sum.inr 3425, (1 / 1))]

def nodeValue3426 : Sparse Master := [(Sum.inr 3426, (1 / 1))]

def nodeValue3429 : Sparse Master := [(Sum.inr 3429, (1 / 1))]

def nodeValue3430 : Sparse Master := [(Sum.inr 3430, (1 / 1))]

def nodeValue3431 : Sparse Master := [(Sum.inr 3431, (1 / 1))]

def nodeValue3432 : Sparse Master := [(Sum.inr 3432, (1 / 1))]

def nodeValue3433 : Sparse Master := [(Sum.inr 3433, (1 / 1))]

def nodeValue3434 : Sparse Master := [(Sum.inr 3434, (1 / 1))]

def nodeValue3436 : Sparse Master := [(Sum.inr 3436, (1 / 1))]

def nodeValue3437 : Sparse Master := [(Sum.inr 3437, (1 / 1))]

def nodeValue3439 : Sparse Master := []

def nodeValue3440 : Sparse Master := [(Sum.inr 3440, (1 / 1))]

def nodeValue3441 : Sparse Master := [(Sum.inr 3441, (1 / 1))]

def nodeValue3442 : Sparse Master := [(Sum.inr 3442, (1 / 1))]

def nodeValue3443 : Sparse Master := [(Sum.inr 3443, (1 / 1))]

def nodeValue3444 : Sparse Master := [(Sum.inr 3444, (1 / 1))]

def nodeValue3445 : Sparse Master := [(Sum.inr 3445, (1 / 1))]

def nodeValue3446 : Sparse Master := [(Sum.inr 3446, (1 / 1))]

def nodeValue3447 : Sparse Master := [(Sum.inr 3447, (1 / 1))]

def nodeValue3448 : Sparse Master := [(Sum.inr 3448, (1 / 1))]

def nodeValue3449 : Sparse Master := [(Sum.inr 3449, (1 / 1))]

def nodeValue3450 : Sparse Master := [(Sum.inr 3450, (1 / 1))]

def nodeValue3451 : Sparse Master := [(Sum.inr 3451, (1 / 1))]

def nodeValue3452 : Sparse Master := [(Sum.inr 3452, (1 / 1))]

def nodeValue3453 : Sparse Master := [(Sum.inr 3453, (1 / 1))]

def nodeValue3454 : Sparse Master := [(Sum.inr 3454, (1 / 1))]

def nodeValue3455 : Sparse Master := [(Sum.inr 3455, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue3456 : Sparse Master := [(Sum.inr 3456, (1 / 1))]

def nodeValue3457 : Sparse Master := [(Sum.inr 3457, (1 / 1))]

def nodeValue3458 : Sparse Master := [(Sum.inr 3458, (1 / 1))]

def nodeValue3459 : Sparse Master := [(Sum.inr 3459, (1 / 1))]

def nodeValue3460 : Sparse Master := [(Sum.inr 3460, (1 / 1))]

def nodeValue3461 : Sparse Master := [(Sum.inr 3461, (1 / 1))]

def nodeValue3462 : Sparse Master := [(Sum.inr 3462, (1 / 1))]

def nodeValue3463 : Sparse Master := [(Sum.inr 3463, (1 / 1))]

def nodeValue3464 : Sparse Master := [(Sum.inr 3464, (1 / 1))]

def nodeValue3465 : Sparse Master := [(Sum.inr 3465, (1 / 1))]

def nodeValue3466 : Sparse Master := [(Sum.inr 3466, (1 / 1))]

def nodeValue3467 : Sparse Master := [(Sum.inr 3467, (1 / 1))]

def nodeValue3468 : Sparse Master := [(Sum.inr 3468, (1 / 1))]

def nodeValue3469 : Sparse Master := []

def nodeValue3470 : Sparse Master := []

def nodeValue3471 : Sparse Master := [(Sum.inr 3471, (1 / 1))]

def nodeValue3472 : Sparse Master := [(Sum.inr 3472, (1 / 1))]

def nodeValue3473 : Sparse Master := [(Sum.inr 3473, (1 / 1))]

def nodeValue3474 : Sparse Master := [(Sum.inr 3474, (1 / 1))]

def nodeValue3475 : Sparse Master := [(Sum.inr 3475, (1 / 1))]

def nodeValue3476 : Sparse Master := [(Sum.inr 3476, (1 / 1))]

def nodeValue3477 : Sparse Master := [(Sum.inr 3477, (1 / 1))]

def nodeValue3478 : Sparse Master := [(Sum.inr 3478, (1 / 1))]

def nodeValue3479 : Sparse Master := [(Sum.inr 3479, (1 / 1))]

def nodeValue3480 : Sparse Master := [(Sum.inr 3480, (1 / 1))]

def nodeValue3481 : Sparse Master := [(Sum.inr 3481, (1 / 1))]

def nodeValue3482 : Sparse Master := [(Sum.inr 3482, (1 / 1))]

def nodeValue3483 : Sparse Master := []

def nodeValue3484 : Sparse Master := []

def nodeValue3485 : Sparse Master := []

def nodeValue3486 : Sparse Master := [(Sum.inr 3486, (1 / 1))]

def nodeValue3487 : Sparse Master := [(Sum.inr 3487, (1 / 1))]

def nodeValue3488 : Sparse Master := [(Sum.inr 3488, (1 / 1))]

def nodeValue3489 : Sparse Master := []

def nodeValue3490 : Sparse Master := [(Sum.inr 3490, (1 / 1))]

def nodeValue3491 : Sparse Master := [(Sum.inr 3491, (1 / 1))]

def nodeValue3492 : Sparse Master := []

def nodeValue3493 : Sparse Master := [(Sum.inr 3493, (1 / 1))]

def nodeValue3494 : Sparse Master := []

def nodeValue3495 : Sparse Master := [(Sum.inr 3495, (1 / 1))]

def nodeValue3496 : Sparse Master := [(Sum.inr 3496, (1 / 1))]

def nodeValue3497 : Sparse Master := [(Sum.inr 3497, (1 / 1))]

def nodeValue3498 : Sparse Master := [(Sum.inr 3498, (1 / 1))]

def nodeValue3499 : Sparse Master := [(Sum.inr 3499, (1 / 1))]

def nodeValue3500 : Sparse Master := [(Sum.inr 3500, (1 / 1))]

def nodeValue3501 : Sparse Master := [(Sum.inr 3501, (1 / 1))]

def nodeValue3502 : Sparse Master := [(Sum.inr 3502, (1 / 1))]

def nodeValue3503 : Sparse Master := [(Sum.inr 3503, (1 / 1))]

def nodeValue3504 : Sparse Master := [(Sum.inr 3504, (1 / 1))]

def nodeValue3505 : Sparse Master := [(Sum.inr 3505, (1 / 1))]

def nodeValue3506 : Sparse Master := [(Sum.inr 3506, (1 / 1))]

def nodeValue3507 : Sparse Master := [(Sum.inr 3507, (1 / 1))]

def nodeValue3508 : Sparse Master := [(Sum.inr 3508, (1 / 1))]

def nodeValue3509 : Sparse Master := [(Sum.inr 3509, (1 / 1))]

def nodeValue3510 : Sparse Master := [(Sum.inr 3510, (1 / 1))]

def nodeValue3511 : Sparse Master := [(Sum.inr 3511, (1 / 1))]

def nodeValue3512 : Sparse Master := [(Sum.inr 3512, (1 / 1))]

def nodeValue3513 : Sparse Master := []

def nodeValue3514 : Sparse Master := [(Sum.inr 3514, (1 / 1))]

def nodeValue3515 : Sparse Master := []

def nodeValue3516 : Sparse Master := [(Sum.inr 3516, (1 / 1))]

def nodeValue3517 : Sparse Master := [(Sum.inr 3517, (1 / 1))]

def nodeValue3518 : Sparse Master := [(Sum.inr 3518, (1 / 1))]

def nodeValue3519 : Sparse Master := [(Sum.inr 3519, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue3520 : Sparse Master := []

def nodeValue3521 : Sparse Master := [(Sum.inr 3521, (1 / 1))]

def nodeValue3522 : Sparse Master := [(Sum.inr 3522, (1 / 1))]

def nodeValue3523 : Sparse Master := [(Sum.inr 3523, (1 / 1))]

def nodeValue3524 : Sparse Master := [(Sum.inr 3524, (1 / 1))]

def nodeValue3525 : Sparse Master := []

def nodeValue3526 : Sparse Master := [(Sum.inr 3526, (1 / 1))]

def nodeValue3527 : Sparse Master := [(Sum.inr 3527, (1 / 1))]

def nodeValue3528 : Sparse Master := [(Sum.inr 3528, (1 / 1))]

def nodeValue3529 : Sparse Master := [(Sum.inr 3529, (1 / 1))]

def nodeValue3530 : Sparse Master := [(Sum.inr 3530, (1 / 1))]

def nodeValue3531 : Sparse Master := []

def nodeValue3532 : Sparse Master := [(Sum.inr 3532, (1 / 1))]

def nodeValue3533 : Sparse Master := [(Sum.inr 3533, (1 / 1))]

def nodeValue3534 : Sparse Master := [(Sum.inr 3534, (1 / 1))]

def nodeValue3535 : Sparse Master := [(Sum.inr 3535, (1 / 1))]

def nodeValue3536 : Sparse Master := [(Sum.inr 3536, (1 / 1))]

def nodeValue3537 : Sparse Master := [(Sum.inr 3537, (1 / 1))]

def nodeValue3538 : Sparse Master := [(Sum.inr 3538, (1 / 1))]

def nodeValue3539 : Sparse Master := [(Sum.inr 3539, (1 / 1))]

def nodeValue3540 : Sparse Master := [(Sum.inr 3540, (1 / 1))]

def nodeValue3541 : Sparse Master := [(Sum.inr 3541, (1 / 1))]

def nodeValue3542 : Sparse Master := [(Sum.inr 3542, (1 / 1))]

def nodeValue3543 : Sparse Master := [(Sum.inr 3543, (1 / 1))]

def nodeValue3544 : Sparse Master := [(Sum.inr 3544, (1 / 1))]

def nodeValue3545 : Sparse Master := [(Sum.inr 3545, (1 / 1))]

def nodeValue3546 : Sparse Master := []

def nodeValue3547 : Sparse Master := []

def nodeValue3548 : Sparse Master := [(Sum.inr 3548, (1 / 1))]

def nodeValue3549 : Sparse Master := [(Sum.inr 3549, (1 / 1))]

def nodeValue3550 : Sparse Master := [(Sum.inr 3550, (1 / 1))]

def nodeValue3551 : Sparse Master := [(Sum.inr 3551, (1 / 1))]

def nodeValue3552 : Sparse Master := [(Sum.inr 3552, (1 / 1))]

def nodeValue3553 : Sparse Master := [(Sum.inr 3553, (1 / 1))]

def nodeValue3554 : Sparse Master := [(Sum.inr 3554, (1 / 1))]

def nodeValue3555 : Sparse Master := [(Sum.inr 3555, (1 / 1))]

def nodeValue3556 : Sparse Master := [(Sum.inr 3556, (1 / 1))]

def nodeValue3557 : Sparse Master := [(Sum.inr 3557, (1 / 1))]

def nodeValue3558 : Sparse Master := [(Sum.inr 3558, (1 / 1))]

def nodeValue3559 : Sparse Master := [(Sum.inr 3559, (1 / 1))]

def nodeValue3560 : Sparse Master := [(Sum.inr 3560, (1 / 1))]

def nodeValue3561 : Sparse Master := [(Sum.inr 3561, (1 / 1))]

def nodeValue3562 : Sparse Master := [(Sum.inr 3562, (1 / 1))]

def nodeValue3563 : Sparse Master := [(Sum.inr 3563, (1 / 1))]

def nodeValue3564 : Sparse Master := [(Sum.inr 3564, (1 / 1))]

def nodeValue3565 : Sparse Master := [(Sum.inr 3565, (1 / 1))]

def nodeValue3566 : Sparse Master := [(Sum.inr 3566, (1 / 1))]

def nodeValue3567 : Sparse Master := [(Sum.inr 3567, (1 / 1))]

def nodeValue3568 : Sparse Master := [(Sum.inr 3568, (1 / 1))]

def nodeValue3569 : Sparse Master := [(Sum.inr 3569, (1 / 1))]

def nodeValue3570 : Sparse Master := [(Sum.inr 3570, (1 / 1))]

def nodeValue3571 : Sparse Master := [(Sum.inr 3571, (1 / 1))]

def nodeValue3572 : Sparse Master := [(Sum.inr 3572, (1 / 1))]

def nodeValue3573 : Sparse Master := [(Sum.inr 3573, (1 / 1))]

def nodeValue3574 : Sparse Master := [(Sum.inr 3574, (1 / 1))]

def nodeValue3575 : Sparse Master := [(Sum.inr 3575, (1 / 1))]

def nodeValue3576 : Sparse Master := [(Sum.inr 3576, (1 / 1))]

def nodeValue3577 : Sparse Master := [(Sum.inr 3577, (1 / 1))]

def nodeValue3578 : Sparse Master := [(Sum.inr 3578, (1 / 1))]

def nodeValue3579 : Sparse Master := [(Sum.inr 3579, (1 / 1))]

def nodeValue3580 : Sparse Master := [(Sum.inr 3580, (1 / 1))]

def nodeValue3581 : Sparse Master := [(Sum.inr 3581, (1 / 1))]

def nodeValue3582 : Sparse Master := [(Sum.inr 3582, (1 / 1))]

def nodeValue3583 : Sparse Master := [(Sum.inr 3583, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue3584 : Sparse Master := [(Sum.inr 3584, (1 / 1))]

def nodeValue3585 : Sparse Master := [(Sum.inr 3585, (1 / 1))]

def nodeValue3586 : Sparse Master := [(Sum.inr 3586, (1 / 1))]

def nodeValue3587 : Sparse Master := [(Sum.inr 3587, (1 / 1))]

def nodeValue3588 : Sparse Master := [(Sum.inr 3588, (1 / 1))]

def nodeValue3589 : Sparse Master := [(Sum.inr 3589, (1 / 1))]

def nodeValue3590 : Sparse Master := [(Sum.inr 3590, (1 / 1))]

def nodeValue3591 : Sparse Master := [(Sum.inr 3591, (1 / 1))]

def nodeValue3592 : Sparse Master := [(Sum.inr 3592, (1 / 1))]

def nodeValue3595 : Sparse Master := [(Sum.inr 3595, (1 / 1))]

def nodeValue3596 : Sparse Master := [(Sum.inr 3596, (1 / 1))]

def nodeValue3597 : Sparse Master := [(Sum.inr 3597, (1 / 1))]

def nodeValue3599 : Sparse Master := [(Sum.inr 3599, (1 / 1))]

def nodeValue3600 : Sparse Master := [(Sum.inr 3600, (1 / 1))]

def nodeValue3602 : Sparse Master := [(Sum.inr 3602, (1 / 1))]

def nodeValue3603 : Sparse Master := [(Sum.inr 3603, (1 / 1))]

def nodeValue3605 : Sparse Master := [(Sum.inr 3605, (1 / 1))]

def nodeValue3606 : Sparse Master := [(Sum.inr 3606, (1 / 1))]

def nodeValue3607 : Sparse Master := [(Sum.inr 3607, (1 / 1))]

def nodeValue3608 : Sparse Master := [(Sum.inr 3608, (1 / 1))]

def nodeValue3610 : Sparse Master := [(Sum.inr 3610, (1 / 1))]

def nodeValue3611 : Sparse Master := [(Sum.inr 3611, (1 / 1))]

def nodeValue3612 : Sparse Master := [(Sum.inr 3612, (1 / 1))]

def nodeValue3613 : Sparse Master := [(Sum.inr 3613, (1 / 1))]

def nodeValue3614 : Sparse Master := [(Sum.inr 3614, (1 / 1))]

def nodeValue3615 : Sparse Master := [(Sum.inr 3615, (1 / 1))]

def nodeValue3616 : Sparse Master := [(Sum.inr 3616, (1 / 1))]

def nodeValue3617 : Sparse Master := [(Sum.inr 3617, (1 / 1))]

def nodeValue3618 : Sparse Master := []

def nodeValue3619 : Sparse Master := [(Sum.inr 3619, (1 / 1))]

def nodeValue3620 : Sparse Master := [(Sum.inr 3620, (1 / 1))]

def nodeValue3621 : Sparse Master := [(Sum.inr 3621, (1 / 1))]

def nodeValue3622 : Sparse Master := [(Sum.inr 3622, (1 / 1))]

def nodeValue3623 : Sparse Master := [(Sum.inr 3623, (1 / 1))]

def nodeValue3624 : Sparse Master := [(Sum.inr 3624, (1 / 1))]

def nodeValue3625 : Sparse Master := [(Sum.inr 3625, (1 / 1))]

def nodeValue3626 : Sparse Master := [(Sum.inr 3626, (1 / 1))]

def nodeValue3627 : Sparse Master := [(Sum.inr 3627, (1 / 1))]

def nodeValue3628 : Sparse Master := []

def nodeValue3629 : Sparse Master := []

def nodeValue3630 : Sparse Master := [(Sum.inr 3630, (1 / 1))]

def nodeValue3631 : Sparse Master := [(Sum.inr 3631, (1 / 1))]

def nodeValue3632 : Sparse Master := [(Sum.inr 3632, (1 / 1))]

def nodeValue3633 : Sparse Master := [(Sum.inr 3633, (1 / 1))]

def nodeValue3634 : Sparse Master := [(Sum.inr 3634, (1 / 1))]

def nodeValue3635 : Sparse Master := []

def nodeValue3636 : Sparse Master := []

def nodeValue3646 : Sparse Master := [(Sum.inr 3646, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue3648 : Sparse Master := [(Sum.inr 3648, (1 / 1))]

def nodeValue3653 : Sparse Master := [(Sum.inr 3653, (1 / 1))]

def nodeValue3658 : Sparse Master := [(Sum.inr 3658, (1 / 1))]

def nodeValue3659 : Sparse Master := [(Sum.inr 3659, (1 / 1))]

def nodeValue3660 : Sparse Master := [(Sum.inr 3660, (1 / 1))]

def nodeValue3666 : Sparse Master := [(Sum.inr 3666, (1 / 1))]

def nodeValue3668 : Sparse Master := [(Sum.inr 3668, (1 / 1))]

def nodeValue3670 : Sparse Master := [(Sum.inr 3670, (1 / 1))]

def nodeValue3671 : Sparse Master := [(Sum.inr 3671, (1 / 1))]

def nodeValue3672 : Sparse Master := [(Sum.inr 3672, (1 / 1))]

def nodeValue3673 : Sparse Master := [(Sum.inr 3673, (1 / 1))]

def nodeValue3674 : Sparse Master := [(Sum.inr 3674, (1 / 1))]

def nodeValue3675 : Sparse Master := [(Sum.inr 3675, (1 / 1))]

def nodeValue3676 : Sparse Master := [(Sum.inr 3676, (1 / 1))]

def nodeValue3677 : Sparse Master := [(Sum.inr 3677, (1 / 1))]

def nodeValue3678 : Sparse Master := [(Sum.inr 3678, (1 / 1))]

def nodeValue3679 : Sparse Master := [(Sum.inr 3679, (1 / 1))]

def nodeValue3680 : Sparse Master := [(Sum.inr 3680, (1 / 1))]

def nodeValue3681 : Sparse Master := [(Sum.inr 3681, (1 / 1))]

def nodeValue3683 : Sparse Master := [(Sum.inr 3683, (1 / 1))]

def nodeValue3685 : Sparse Master := [(Sum.inr 3685, (1 / 1))]

def nodeValue3686 : Sparse Master := [(Sum.inr 3686, (1 / 1))]

def nodeValue3687 : Sparse Master := [(Sum.inr 3687, (1 / 1))]

def nodeValue3688 : Sparse Master := [(Sum.inr 3688, (1 / 1))]

def nodeValue3689 : Sparse Master := [(Sum.inr 3689, (1 / 1))]

def nodeValue3690 : Sparse Master := [(Sum.inr 3690, (1 / 1))]

def nodeValue3691 : Sparse Master := [(Sum.inr 3691, (1 / 1))]

def nodeValue3692 : Sparse Master := [(Sum.inr 3692, (1 / 1))]

def nodeValue3693 : Sparse Master := [(Sum.inr 3693, (1 / 1))]

def nodeValue3694 : Sparse Master := [(Sum.inr 3694, (1 / 1))]

def nodeValue3695 : Sparse Master := [(Sum.inr 3695, (1 / 1))]

def nodeValue3696 : Sparse Master := [(Sum.inr 3696, (1 / 1))]

def nodeValue3697 : Sparse Master := [(Sum.inr 3697, (1 / 1))]

def nodeValue3698 : Sparse Master := [(Sum.inr 3698, (1 / 1))]

def nodeValue3699 : Sparse Master := [(Sum.inr 3699, (1 / 1))]

def nodeValue3700 : Sparse Master := [(Sum.inr 3700, (1 / 1))]

def nodeValue3701 : Sparse Master := [(Sum.inr 3701, (1 / 1))]

def nodeValue3702 : Sparse Master := [(Sum.inr 3702, (1 / 1))]

def nodeValue3703 : Sparse Master := [(Sum.inr 3703, (1 / 1))]

def nodeValue3705 : Sparse Master := [(Sum.inr 3705, (1 / 1))]

def nodeValue3706 : Sparse Master := [(Sum.inr 3706, (1 / 1))]

def nodeValue3707 : Sparse Master := []

def nodeValue3708 : Sparse Master := [(Sum.inr 3708, (1 / 1))]

def nodeValue3709 : Sparse Master := [(Sum.inr 3709, (1 / 1))]

def nodeValue3710 : Sparse Master := [(Sum.inr 3710, (1 / 1))]

def nodeValue3711 : Sparse Master := [(Sum.inl 0, (-1 / 160)), (Sum.inl 5, (1 / 72)), (Sum.inl 68, (-1 / 18)), (Sum.inl 2, (-1 / 96)), (Sum.inl 7, (1 / 27)), (Sum.inl 124, (-1 / 18)), (Sum.inl 125, (-1 / 18)), (Sum.inl 126, (-1 / 18)), (Sum.inl 51, (-1 / 18)), (Sum.inl 3, (2 / 27)), (Sum.inl 197, (-1 / 18)), (Sum.inl 23, (-1 / 9)), (Sum.inl 24, (-1 / 9)), (Sum.inl 55, (-1 / 9)), (Sum.inl 12, (1 / 54)), (Sum.inl 4, (1 / 54)), (Sum.inl 1, (-1 / 432))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue3712 : Sparse Master := [(Sum.inr 3712, (1 / 1))]

def nodeValue3713 : Sparse Master := [(Sum.inr 3713, (1 / 1))]

def nodeValue3714 : Sparse Master := [(Sum.inr 3714, (1 / 1))]

def nodeValue3715 : Sparse Master := [(Sum.inr 3715, (1 / 1))]

def nodeValue3716 : Sparse Master := [(Sum.inr 3716, (1 / 1))]

def nodeValue3717 : Sparse Master := [(Sum.inr 3717, (1 / 1))]

def nodeValue3718 : Sparse Master := [(Sum.inr 3718, (1 / 1))]

def nodeValue3719 : Sparse Master := [(Sum.inr 3719, (1 / 1))]

def nodeValue3720 : Sparse Master := [(Sum.inr 3720, (1 / 1))]

def nodeValue3721 : Sparse Master := [(Sum.inr 3721, (1 / 1))]

def nodeValue3722 : Sparse Master := [(Sum.inr 3722, (1 / 1))]

def nodeValue3723 : Sparse Master := [(Sum.inr 3723, (1 / 1))]

def nodeValue3724 : Sparse Master := [(Sum.inr 3724, (1 / 1))]

def nodeValue3725 : Sparse Master := [(Sum.inr 3725, (1 / 1))]

def nodeValue3726 : Sparse Master := [(Sum.inl 0, (-19 / 4320)), (Sum.inl 5, (-1 / 108)), (Sum.inl 2, (1 / 48)), (Sum.inl 7, (1 / 18)), (Sum.inl 35, (1 / 54)), (Sum.inl 3, (1 / 6)), (Sum.inl 23, (-1 / 18)), (Sum.inl 24, (-1 / 9)), (Sum.inl 55, (-1 / 18)), (Sum.inl 12, (1 / 54)), (Sum.inl 26, (1 / 27)), (Sum.inl 4, (2 / 27)), (Sum.inl 27, (1 / 36)), (Sum.inl 1, (-31 / 864))]

def nodeValue3727 : Sparse Master := [(Sum.inl 0, (-11 / 1440)), (Sum.inl 5, (-1 / 108)), (Sum.inl 2, (1 / 144)), (Sum.inl 7, (1 / 27)), (Sum.inl 35, (1 / 54)), (Sum.inl 3, (7 / 54)), (Sum.inl 13, (1 / 54)), (Sum.inl 23, (-1 / 9)), (Sum.inl 54, (-1 / 18)), (Sum.inl 24, (-1 / 18)), (Sum.inl 55, (-1 / 18)), (Sum.inl 12, (1 / 18)), (Sum.inl 25, (-1 / 18)), (Sum.inl 26, (1 / 54)), (Sum.inl 4, (1 / 54)), (Sum.inl 27, (1 / 36)), (Sum.inl 1, (-5 / 864))]

def nodeValue3728 : Sparse Master := [(Sum.inl 0, (-1 / 160)), (Sum.inl 2, (-1 / 288)), (Sum.inl 23, (1 / 18)), (Sum.inl 24, (1 / 18)), (Sum.inl 55, (1 / 18)), (Sum.inl 27, (-1 / 24)), (Sum.inl 1, (1 / 72))]

def nodeValue3729 : Sparse Master := [(Sum.inr 3729, (1 / 1))]

def nodeValue3730 : Sparse Master := [(Sum.inr 3730, (1 / 1))]

def nodeValue3731 : Sparse Master := [(Sum.inr 3731, (1 / 1))]

def nodeValue3732 : Sparse Master := [(Sum.inr 3732, (1 / 1))]

def nodeValue3733 : Sparse Master := [(Sum.inr 3733, (1 / 1))]

def nodeValue3734 : Sparse Master := [(Sum.inl 0, (-1 / 160)), (Sum.inl 5, (1 / 72)), (Sum.inl 2, (-11 / 864)), (Sum.inl 7, (1 / 54)), (Sum.inl 3, (7 / 54)), (Sum.inl 23, (-1 / 6)), (Sum.inl 54, (-1 / 9)), (Sum.inl 12, (1 / 9)), (Sum.inl 25, (-1 / 6)), (Sum.inl 27, (-1 / 24)), (Sum.inl 1, (-1 / 36))]

def nodeValue3735 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 5, (1 / 72)), (Sum.inl 2, (-1 / 108)), (Sum.inl 7, (1 / 18)), (Sum.inl 3, (4 / 27)), (Sum.inl 23, (-1 / 18)), (Sum.inl 24, (-1 / 9)), (Sum.inl 12, (1 / 27)), (Sum.inl 4, (2 / 27)), (Sum.inl 27, (-1 / 24)), (Sum.inl 1, (-1 / 432))]

def nodeValue3736 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 5, (-1 / 216)), (Sum.inl 2, (1 / 432)), (Sum.inl 7, (-1 / 54)), (Sum.inl 3, (-1 / 27)), (Sum.inl 23, (1 / 18)), (Sum.inl 12, (-1 / 54)), (Sum.inl 27, (1 / 72)), (Sum.inl 1, (-1 / 36))]

def nodeValue3737 : Sparse Master := [(Sum.inl 0, (-13 / 1440)), (Sum.inl 5, (-1 / 216)), (Sum.inl 2, (1 / 432)), (Sum.inl 7, (-1 / 54)), (Sum.inl 3, (-1 / 27)), (Sum.inl 24, (1 / 18)), (Sum.inl 4, (-1 / 54)), (Sum.inl 27, (1 / 72)), (Sum.inl 1, (7 / 288))]

def nodeValue3738 : Sparse Master := [(Sum.inl 0, (-23 / 4320)), (Sum.inl 5, (-1 / 216)), (Sum.inl 2, (1 / 432)), (Sum.inl 3, (-1 / 54)), (Sum.inl 23, (1 / 18)), (Sum.inl 54, (1 / 18)), (Sum.inl 12, (-1 / 54)), (Sum.inl 25, (1 / 18)), (Sum.inl 27, (1 / 72)), (Sum.inl 1, (-19 / 864))]

def nodeValue3739 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 5, (-1 / 216)), (Sum.inl 2, (1 / 432)), (Sum.inl 7, (-1 / 54)), (Sum.inl 3, (-1 / 27)), (Sum.inl 23, (1 / 18)), (Sum.inl 12, (-1 / 54)), (Sum.inl 27, (1 / 72)), (Sum.inl 1, (-1 / 36))]

def nodeValue3740 : Sparse Master := [(Sum.inl 0, (-1 / 180)), (Sum.inl 23, (-1 / 9)), (Sum.inl 27, (-1 / 36)), (Sum.inl 1, (-1 / 18))]

def nodeValue3741 : Sparse Master := [(Sum.inl 0, (-1 / 120)), (Sum.inl 24, (-1 / 9)), (Sum.inl 27, (-1 / 36)), (Sum.inl 1, (1 / 72))]

def nodeValue3743 : Sparse Master := [(Sum.inr 3743, (1 / 1))]

def nodeValue3744 : Sparse Master := [(Sum.inr 3744, (1 / 1))]

def nodeValue3746 : Sparse Master := [(Sum.inr 3746, (1 / 1))]

def nodeValue3748 : Sparse Master := [(Sum.inr 3748, (1 / 1))]

def nodeValue3749 : Sparse Master := [(Sum.inr 3749, (1 / 1))]

def nodeValue3750 : Sparse Master := [(Sum.inr 3750, (1 / 1))]

def nodeValue3751 : Sparse Master := [(Sum.inr 3751, (1 / 1))]

def nodeValue3752 : Sparse Master := [(Sum.inr 3752, (1 / 1))]

def nodeValue3753 : Sparse Master := [(Sum.inr 3753, (1 / 1))]

def nodeValue3754 : Sparse Master := [(Sum.inr 3754, (1 / 1))]

def nodeValue3755 : Sparse Master := [(Sum.inr 3755, (1 / 1))]

def nodeValue3756 : Sparse Master := [(Sum.inr 3756, (1 / 1))]

def nodeValue3757 : Sparse Master := [(Sum.inr 3757, (1 / 1))]

def nodeValue3758 : Sparse Master := [(Sum.inr 3758, (1 / 1))]

def nodeValue3759 : Sparse Master := [(Sum.inr 3759, (1 / 1))]

def nodeValue3760 : Sparse Master := [(Sum.inr 3760, (1 / 1))]

def nodeValue3761 : Sparse Master := [(Sum.inr 3761, (1 / 1))]

def nodeValue3762 : Sparse Master := [(Sum.inr 3762, (1 / 1))]

def nodeValue3763 : Sparse Master := [(Sum.inr 3763, (1 / 1))]

def nodeValue3764 : Sparse Master := [(Sum.inr 3764, (1 / 1))]

def nodeValue3765 : Sparse Master := []

def nodeValue3766 : Sparse Master := []

def nodeValue3767 : Sparse Master := [(Sum.inr 3767, (1 / 1))]

def nodeValue3768 : Sparse Master := [(Sum.inr 3768, (1 / 1))]

def nodeValue3769 : Sparse Master := [(Sum.inr 3769, (1 / 1))]

def nodeValue3770 : Sparse Master := [(Sum.inr 3770, (1 / 1))]

def nodeValue3771 : Sparse Master := [(Sum.inr 3771, (1 / 1))]

def nodeValue3772 : Sparse Master := [(Sum.inr 3772, (1 / 1))]

def nodeValue3773 : Sparse Master := [(Sum.inr 3773, (1 / 1))]

def nodeValue3774 : Sparse Master := []

def nodeValue3775 : Sparse Master := []

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue3776 : Sparse Master := [(Sum.inr 3776, (1 / 1))]

def nodeValue3778 : Sparse Master := [(Sum.inr 3778, (1 / 1))]

def nodeValue3779 : Sparse Master := [(Sum.inr 3779, (1 / 1))]

def nodeValue3780 : Sparse Master := [(Sum.inr 3780, (1 / 1))]

def nodeValue3781 : Sparse Master := [(Sum.inr 3781, (1 / 1))]

def nodeValue3782 : Sparse Master := [(Sum.inr 3782, (1 / 1))]

def nodeValue3783 : Sparse Master := [(Sum.inr 3783, (1 / 1))]

def nodeValue3784 : Sparse Master := [(Sum.inr 3784, (1 / 1))]

def nodeValue3785 : Sparse Master := [(Sum.inr 3785, (1 / 1))]

def nodeValue3786 : Sparse Master := [(Sum.inr 3786, (1 / 1))]

def nodeValue3787 : Sparse Master := [(Sum.inr 3787, (1 / 1))]

def nodeValue3788 : Sparse Master := [(Sum.inr 3788, (1 / 1))]

def nodeValue3789 : Sparse Master := [(Sum.inr 3789, (1 / 1))]

def nodeValue3790 : Sparse Master := [(Sum.inr 3790, (1 / 1))]

def nodeValue3791 : Sparse Master := [(Sum.inr 3791, (1 / 1))]

def nodeValue3792 : Sparse Master := [(Sum.inr 3792, (1 / 1))]

def nodeValue3793 : Sparse Master := []

def nodeValue3794 : Sparse Master := [(Sum.inr 3794, (1 / 1))]

def nodeValue3795 : Sparse Master := [(Sum.inr 3795, (1 / 1))]

def nodeValue3796 : Sparse Master := [(Sum.inr 3796, (1 / 1))]

def nodeValue3797 : Sparse Master := [(Sum.inr 3797, (1 / 1))]

def nodeValue3798 : Sparse Master := []

def nodeValue3799 : Sparse Master := [(Sum.inr 3799, (1 / 1))]

def nodeValue3800 : Sparse Master := [(Sum.inr 3800, (1 / 1))]

def nodeValue3801 : Sparse Master := [(Sum.inr 3801, (1 / 1))]

def nodeValue3802 : Sparse Master := [(Sum.inr 3802, (1 / 1))]

def nodeValue3803 : Sparse Master := [(Sum.inr 3803, (1 / 1))]

def nodeValue3804 : Sparse Master := [(Sum.inr 3804, (1 / 1))]

def nodeValue3805 : Sparse Master := [(Sum.inr 3805, (1 / 1))]

def nodeValue3806 : Sparse Master := []

def nodeValue3807 : Sparse Master := []

def nodeValue3808 : Sparse Master := []

def nodeValue3809 : Sparse Master := [(Sum.inr 3809, (1 / 1))]

def nodeValue3810 : Sparse Master := [(Sum.inr 3810, (1 / 1))]

def nodeValue3811 : Sparse Master := [(Sum.inr 3811, (1 / 1))]

def nodeValue3812 : Sparse Master := [(Sum.inr 3812, (1 / 1))]

def nodeValue3813 : Sparse Master := [(Sum.inr 3813, (1 / 1))]

def nodeValue3814 : Sparse Master := [(Sum.inr 3814, (1 / 1))]

def nodeValue3815 : Sparse Master := [(Sum.inr 3815, (1 / 1))]

def nodeValue3816 : Sparse Master := []

def nodeValue3817 : Sparse Master := []

def nodeValue3818 : Sparse Master := [(Sum.inl 0, (-11 / 2160)), (Sum.inl 5, (-1 / 108)), (Sum.inl 2, (1 / 48)), (Sum.inl 7, (1 / 54)), (Sum.inl 8, (1 / 54)), (Sum.inl 51, (-1 / 9)), (Sum.inl 3, (1 / 9)), (Sum.inl 23, (-1 / 18)), (Sum.inl 24, (-1 / 18)), (Sum.inl 55, (-1 / 9)), (Sum.inl 12, (1 / 18)), (Sum.inl 4, (1 / 27)), (Sum.inl 27, (1 / 36)), (Sum.inl 1, (-1 / 36))]

def nodeValue3819 : Sparse Master := [(Sum.inr 3819, (1 / 1))]

def nodeValue3820 : Sparse Master := [(Sum.inl 0, (-43 / 4320)), (Sum.inl 5, (1 / 216)), (Sum.inl 6, (-1 / 864)), (Sum.inl 2, (-1 / 216)), (Sum.inl 7, (1 / 27)), (Sum.inl 3, (2 / 27)), (Sum.inl 23, (-1 / 18)), (Sum.inl 12, (1 / 27)), (Sum.inl 27, (-1 / 72)), (Sum.inl 1, (-11 / 216))]

def nodeValue3821 : Sparse Master := [(Sum.inl 0, (-23 / 2160)), (Sum.inl 5, (1 / 216)), (Sum.inl 6, (-1 / 864)), (Sum.inl 2, (1 / 96)), (Sum.inl 7, (1 / 54)), (Sum.inl 8, (1 / 54)), (Sum.inl 3, (1 / 18)), (Sum.inl 24, (-1 / 18)), (Sum.inl 4, (1 / 27)), (Sum.inl 27, (-1 / 72)), (Sum.inl 1, (1 / 216))]

def nodeValue3822 : Sparse Master := [(Sum.inl 0, (-1 / 180)), (Sum.inl 5, (1 / 108)), (Sum.inl 6, (-1 / 864)), (Sum.inl 2, (1 / 216)), (Sum.inl 7, (1 / 54)), (Sum.inl 35, (1 / 54)), (Sum.inl 3, (1 / 27)), (Sum.inl 13, (1 / 18)), (Sum.inl 23, (-1 / 18)), (Sum.inl 54, (-1 / 18)), (Sum.inl 12, (1 / 54)), (Sum.inl 25, (-1 / 18)), (Sum.inl 27, (-1 / 72)), (Sum.inl 1, (-31 / 864))]

def nodeValue3823 : Sparse Master := [(Sum.inl 0, (-41 / 4320)), (Sum.inl 5, (1 / 216)), (Sum.inl 6, (-1 / 864)), (Sum.inl 2, (1 / 54)), (Sum.inl 7, (1 / 27)), (Sum.inl 3, (4 / 27)), (Sum.inl 23, (-1 / 18)), (Sum.inl 12, (5 / 54)), (Sum.inl 27, (-1 / 72)), (Sum.inl 1, (-1 / 48))]

def nodeValue3824 : Sparse Master := [(Sum.inl 0, (-1 / 90)), (Sum.inl 5, (-1 / 216)), (Sum.inl 8, (-1 / 54)), (Sum.inl 24, (1 / 18)), (Sum.inl 27, (1 / 72)), (Sum.inl 1, (1 / 108))]

def nodeValue3825 : Sparse Master := [(Sum.inr 3825, (1 / 1))]

def nodeValue3826 : Sparse Master := [(Sum.inr 3826, (1 / 1))]

def nodeValue3827 : Sparse Master := [(Sum.inr 3827, (1 / 1))]

def nodeValue3828 : Sparse Master := [(Sum.inr 3828, (1 / 1))]

def nodeValue3829 : Sparse Master := [(Sum.inl 0, (-5 / 864)), (Sum.inl 5, (1 / 108)), (Sum.inl 6, (-1 / 864)), (Sum.inl 2, (7 / 864)), (Sum.inl 35, (1 / 54)), (Sum.inl 51, (-1 / 18)), (Sum.inl 3, (1 / 18)), (Sum.inl 52, (1 / 54)), (Sum.inl 55, (-1 / 18)), (Sum.inl 12, (1 / 54)), (Sum.inl 26, (1 / 27)), (Sum.inl 4, (1 / 54)), (Sum.inl 27, (-1 / 72)), (Sum.inl 1, (-1 / 288))]

def nodeValue3830 : Sparse Master := [(Sum.inl 0, (-1 / 120)), (Sum.inl 5, (1 / 108)), (Sum.inl 6, (-1 / 864)), (Sum.inl 2, (1 / 432)), (Sum.inl 35, (1 / 54)), (Sum.inl 51, (-1 / 18)), (Sum.inl 3, (7 / 54)), (Sum.inl 13, (1 / 18)), (Sum.inl 52, (1 / 54)), (Sum.inl 55, (-1 / 18)), (Sum.inl 12, (1 / 18)), (Sum.inl 26, (1 / 54)), (Sum.inl 4, (1 / 18)), (Sum.inl 27, (-1 / 72)), (Sum.inl 1, (-13 / 864))]

def nodeValue3831 : Sparse Master := [(Sum.inl 0, (-7 / 1080)), (Sum.inl 5, (-1 / 216)), (Sum.inl 2, (1 / 432)), (Sum.inl 51, (1 / 18)), (Sum.inl 3, (-1 / 27)), (Sum.inl 55, (1 / 18)), (Sum.inl 12, (-1 / 54)), (Sum.inl 4, (-1 / 54)), (Sum.inl 27, (1 / 72)), (Sum.inl 1, (7 / 432))]

def nodeValue3832 : Sparse Master := [(Sum.inr 3832, (1 / 1))]

def nodeValue3833 : Sparse Master := [(Sum.inr 3833, (1 / 1))]

def nodeValue3834 : Sparse Master := [(Sum.inr 3834, (1 / 1))]

def nodeValue3835 : Sparse Master := [(Sum.inr 3835, (1 / 1))]

def nodeValue3836 : Sparse Master := [(Sum.inr 3836, (1 / 1))]

def nodeValue3837 : Sparse Master := [(Sum.inr 3837, (1 / 1))]

def nodeValue3838 : Sparse Master := [(Sum.inr 3838, (1 / 1))]

def nodeValue3839 : Sparse Master := [(Sum.inr 3839, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue384 : Sparse Master := [(Sum.inl 0, (19 / 864)), (Sum.inl 34, (5 / 54)), (Sum.inl 3, (5 / 18)), (Sum.inl 13, (10 / 27)), (Sum.inl 12, (5 / 27)), (Sum.inl 1, (-25 / 288))]

def nodeValue385 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 2, (5 / 36)), (Sum.inl 13, (-10 / 27)), (Sum.inl 1, (-5 / 72))]

def nodeValue386 : Sparse Master := [(Sum.inl 0, (13 / 864)), (Sum.inl 34, (5 / 27)), (Sum.inl 2, (-5 / 216)), (Sum.inl 3, (5 / 18)), (Sum.inl 13, (5 / 54)), (Sum.inl 26, (5 / 27)), (Sum.inl 1, (5 / 288))]

def nodeValue387 : Sparse Master := [(Sum.inl 0, (17 / 432)), (Sum.inl 2, (5 / 108)), (Sum.inl 3, (5 / 27)), (Sum.inl 26, (5 / 54)), (Sum.inl 4, (5 / 54)), (Sum.inl 1, (-5 / 432))]

def nodeValue388 : Sparse Master := [(Sum.inl 0, (19 / 432)), (Sum.inl 2, (-5 / 108)), (Sum.inl 26, (-5 / 27)), (Sum.inl 1, (-5 / 144))]

def nodeValue389 : Sparse Master := []

def nodeValue390 : Sparse Master := [(Sum.inl 0, (19 / 432)), (Sum.inl 2, (-25 / 432)), (Sum.inl 3, (-5 / 27)), (Sum.inl 1, (-5 / 54))]

def nodeValue391 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 34, (-5 / 27)), (Sum.inl 2, (-25 / 432)), (Sum.inl 3, (-5 / 27)), (Sum.inl 13, (-5 / 27)), (Sum.inl 1, (-5 / 54))]

def nodeValue392 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 5, (-5 / 72)), (Sum.inl 65, (5 / 18)), (Sum.inl 66, (5 / 9)), (Sum.inl 67, (-5 / 18)), (Sum.inl 34, (-20 / 27)), (Sum.inl 2, (25 / 216)), (Sum.inl 3, (-10 / 9)), (Sum.inl 13, (-5 / 27)), (Sum.inl 26, (-10 / 9)), (Sum.inl 4, (-10 / 27)), (Sum.inl 27, (5 / 24)), (Sum.inl 1, (5 / 144))]

def nodeValue393 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 5, (5 / 216)), (Sum.inl 65, (-5 / 18)), (Sum.inl 67, (5 / 54)), (Sum.inl 34, (5 / 27)), (Sum.inl 2, (-25 / 864)), (Sum.inl 3, (5 / 27)), (Sum.inl 13, (5 / 54)), (Sum.inl 26, (5 / 27)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (-5 / 864))]

def nodeValue394 : Sparse Master := [(Sum.inl 0, (1 / 432)), (Sum.inl 33, (5 / 18)), (Sum.inl 34, (-5 / 27)), (Sum.inl 2, (-65 / 864)), (Sum.inl 3, (-65 / 54)), (Sum.inl 13, (-5 / 54)), (Sum.inl 12, (-5 / 54)), (Sum.inl 26, (-35 / 54)), (Sum.inl 4, (-5 / 9)), (Sum.inl 1, (25 / 96))]

def nodeValue395 : Sparse Master := [(Sum.inl 0, (5 / 864)), (Sum.inl 33, (-5 / 18)), (Sum.inl 2, (-5 / 288)), (Sum.inl 3, (5 / 27)), (Sum.inl 26, (5 / 54)), (Sum.inl 1, (5 / 108))]

def nodeValue396 : Sparse Master := []

def nodeValue397 : Sparse Master := [(Sum.inl 0, (1 / 48)), (Sum.inl 2, (-25 / 864)), (Sum.inl 3, (5 / 27)), (Sum.inl 13, (5 / 54)), (Sum.inl 12, (5 / 54)), (Sum.inl 1, (-55 / 864))]

def nodeValue398 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 5, (5 / 216)), (Sum.inl 61, (-5 / 18)), (Sum.inl 33, (-5 / 18)), (Sum.inl 2, (-5 / 108)), (Sum.inl 3, (5 / 54)), (Sum.inl 13, (5 / 54)), (Sum.inl 55, (-5 / 18)), (Sum.inl 12, (5 / 54)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (-5 / 108))]

def nodeValue399 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 5, (5 / 216)), (Sum.inl 66, (-5 / 18)), (Sum.inl 67, (5 / 54)), (Sum.inl 34, (5 / 27)), (Sum.inl 2, (5 / 216)), (Sum.inl 3, (5 / 27)), (Sum.inl 26, (5 / 18)), (Sum.inl 4, (5 / 54)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (35 / 432))]

def nodeValue400 : Sparse Master := [(Sum.inl 0, (11 / 864)), (Sum.inl 34, (5 / 54)), (Sum.inl 2, (25 / 864)), (Sum.inl 3, (10 / 27)), (Sum.inl 26, (5 / 18)), (Sum.inl 4, (5 / 27)), (Sum.inl 1, (5 / 432))]

def nodeValue401 : Sparse Master := [(Sum.inl 0, (7 / 288)), (Sum.inl 2, (25 / 864)), (Sum.inl 3, (5 / 18)), (Sum.inl 26, (5 / 27)), (Sum.inl 4, (5 / 27))]

def nodeValue402 : Sparse Master := [(Sum.inl 0, (7 / 216)), (Sum.inl 2, (-5 / 144)), (Sum.inl 3, (-5 / 27)), (Sum.inl 26, (-5 / 27)), (Sum.inl 1, (-25 / 432))]

def nodeValue403 : Sparse Master := [(Sum.inl 0, (47 / 864)), (Sum.inl 2, (55 / 864)), (Sum.inl 3, (5 / 54)), (Sum.inl 1, (-5 / 216))]

def nodeValue404 : Sparse Master := [(Sum.inl 0, (1 / 18)), (Sum.inl 2, (-5 / 72)), (Sum.inl 1, (-5 / 72))]

def nodeValue405 : Sparse Master := [(Sum.inl 0, (19 / 432)), (Sum.inl 2, (-25 / 432)), (Sum.inl 3, (-5 / 27)), (Sum.inl 1, (-5 / 54))]

def nodeValue406 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 34, (-5 / 27)), (Sum.inl 3, (-5 / 27)), (Sum.inl 26, (-5 / 27)), (Sum.inl 1, (-5 / 216))]

def nodeValue407 : Sparse Master := [(Sum.inl 0, (1 / 24)), (Sum.inl 2, (5 / 24))]

def nodeValue408 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 65, (5 / 9)), (Sum.inl 2, (-5 / 72)), (Sum.inl 27, (5 / 36)), (Sum.inl 1, (-5 / 72))]

def nodeValue409 : Sparse Master := [(Sum.inl 0, (17 / 864)), (Sum.inl 33, (-5 / 18)), (Sum.inl 34, (5 / 54)), (Sum.inl 2, (5 / 108)), (Sum.inl 3, (5 / 18)), (Sum.inl 13, (5 / 54)), (Sum.inl 12, (5 / 54)), (Sum.inl 26, (5 / 54)), (Sum.inl 4, (5 / 54)), (Sum.inl 1, (-25 / 864))]

def nodeValue410 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 33, (5 / 9)), (Sum.inl 2, (-5 / 432)), (Sum.inl 1, (-35 / 432))]

def nodeValue411 : Sparse Master := [(Sum.inl 0, (11 / 864)), (Sum.inl 2, (5 / 288)), (Sum.inl 3, (5 / 18)), (Sum.inl 13, (5 / 27)), (Sum.inl 12, (5 / 18)), (Sum.inl 1, (5 / 36))]

def nodeValue412 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 2, (-5 / 216)), (Sum.inl 3, (-5 / 27)), (Sum.inl 13, (-5 / 27)), (Sum.inl 12, (-5 / 27)), (Sum.inl 1, (35 / 432))]

def nodeValue413 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 66, (5 / 9)), (Sum.inl 2, (5 / 108)), (Sum.inl 27, (5 / 36)), (Sum.inl 1, (5 / 72))]

def nodeValue414 : Sparse Master := [(Sum.inl 0, (13 / 432)), (Sum.inl 2, (5 / 144)), (Sum.inl 3, (-5 / 27)), (Sum.inl 26, (-5 / 27)), (Sum.inl 4, (-5 / 27)), (Sum.inl 1, (-5 / 216))]

def nodeValue415 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 2, (-5 / 72)), (Sum.inl 26, (5 / 9)), (Sum.inl 1, (-5 / 48))]

def nodeValue416 : Sparse Master := [(Sum.inl 0, (19 / 432)), (Sum.inl 2, (5 / 432)), (Sum.inl 3, (-5 / 27)), (Sum.inl 1, (55 / 216))]

def nodeValue417 : Sparse Master := []

def nodeValue418 : Sparse Master := []

def nodeValue419 : Sparse Master := []

def nodeValue420 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 2, (-5 / 144)), (Sum.inl 3, (5 / 9)), (Sum.inl 1, (5 / 72))]

def nodeValue421 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 34, (5 / 9)), (Sum.inl 2, (-5 / 48)), (Sum.inl 1, (-5 / 48))]

def nodeValue422 : Sparse Master := []

def nodeValue423 : Sparse Master := [(Sum.inl 0, (1 / 24)), (Sum.inl 5, (-5 / 108)), (Sum.inl 68, (5 / 18)), (Sum.inl 2, (5 / 144)), (Sum.inl 124, (5 / 18)), (Sum.inl 126, (5 / 9)), (Sum.inl 51, (5 / 9)), (Sum.inl 1, (5 / 432)), (Sum.inl 236, (5 / 18)), (Sum.inl 31, (5 / 18))]

def nodeValue424 : Sparse Master := [(Sum.inl 0, (1 / 32)), (Sum.inl 5, (-5 / 72)), (Sum.inl 68, (5 / 18)), (Sum.inl 2, (5 / 96)), (Sum.inl 7, (-5 / 27)), (Sum.inl 124, (5 / 18)), (Sum.inl 125, (5 / 18)), (Sum.inl 126, (5 / 18)), (Sum.inl 51, (5 / 18)), (Sum.inl 3, (-10 / 27)), (Sum.inl 197, (5 / 18)), (Sum.inl 23, (5 / 9)), (Sum.inl 24, (5 / 9)), (Sum.inl 55, (5 / 9)), (Sum.inl 12, (-5 / 54)), (Sum.inl 4, (-5 / 54)), (Sum.inl 1, (5 / 432))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue3840 : Sparse Master := [(Sum.inr 3840, (1 / 1))]

def nodeValue3841 : Sparse Master := [(Sum.inr 3841, (1 / 1))]

def nodeValue3842 : Sparse Master := [(Sum.inr 3842, (1 / 1))]

def nodeValue3843 : Sparse Master := [(Sum.inr 3843, (1 / 1))]

def nodeValue3844 : Sparse Master := []

def nodeValue3845 : Sparse Master := [(Sum.inr 3845, (1 / 1))]

def nodeValue3846 : Sparse Master := [(Sum.inr 3846, (1 / 1))]

def nodeValue3847 : Sparse Master := [(Sum.inl 0, (-1 / 540)), (Sum.inl 2, (7 / 864)), (Sum.inl 3, (4 / 27)), (Sum.inl 13, (1 / 18)), (Sum.inl 12, (2 / 27)), (Sum.inl 4, (1 / 27)), (Sum.inl 1, (-29 / 864))]

def nodeValue3848 : Sparse Master := [(Sum.inr 3848, (1 / 1))]

def nodeValue3849 : Sparse Master := [(Sum.inr 3849, (1 / 1))]

def nodeValue3850 : Sparse Master := [(Sum.inr 3850, (1 / 1))]

def nodeValue3851 : Sparse Master := [(Sum.inl 0, (-29 / 4320)), (Sum.inl 2, (1 / 96)), (Sum.inl 3, (1 / 18)), (Sum.inl 12, (1 / 27)), (Sum.inl 4, (1 / 27)), (Sum.inl 1, (-1 / 48))]

def nodeValue3852 : Sparse Master := [(Sum.inl 0, (-1 / 90)), (Sum.inl 2, (-5 / 864)), (Sum.inl 3, (-1 / 54)), (Sum.inl 4, (-1 / 54)), (Sum.inl 1, (7 / 864))]

def nodeValue3853 : Sparse Master := [(Sum.inl 0, (-1 / 120)), (Sum.inl 2, (-1 / 216)), (Sum.inl 3, (-1 / 27)), (Sum.inl 12, (-1 / 27)), (Sum.inl 1, (1 / 27))]

def nodeValue3854 : Sparse Master := [(Sum.inr 3854, (1 / 1))]

def nodeValue3855 : Sparse Master := [(Sum.inl 0, (-1 / 2160)), (Sum.inl 2, (1 / 144)), (Sum.inl 3, (1 / 9)), (Sum.inl 13, (2 / 27)), (Sum.inl 1, (-1 / 36))]

def nodeValue3856 : Sparse Master := [(Sum.inl 0, (-1 / 240)), (Sum.inl 2, (-1 / 216)), (Sum.inl 3, (-1 / 27)), (Sum.inl 13, (-1 / 27)), (Sum.inl 1, (-5 / 432))]

def nodeValue3857 : Sparse Master := [(Sum.inr 3857, (1 / 1))]

def nodeValue3858 : Sparse Master := [(Sum.inl 0, (-11 / 1440)), (Sum.inl 2, (1 / 864)), (Sum.inl 3, (-1 / 54)), (Sum.inl 12, (-1 / 54)), (Sum.inl 1, (-19 / 432))]

def nodeValue3859 : Sparse Master := []

def nodeValue3860 : Sparse Master := []

def nodeValue3861 : Sparse Master := []

def nodeValue3862 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 2, (-1 / 432)), (Sum.inl 3, (1 / 27)), (Sum.inl 12, (1 / 27)), (Sum.inl 1, (-5 / 216))]

def nodeValue3863 : Sparse Master := [(Sum.inr 3863, (1 / 1))]

def nodeValue3865 : Sparse Master := [(Sum.inr 3865, (1 / 1))]

def nodeValue3866 : Sparse Master := [(Sum.inr 3866, (1 / 1))]

def nodeValue3867 : Sparse Master := [(Sum.inr 3867, (1 / 1))]

def nodeValue3868 : Sparse Master := [(Sum.inr 3868, (1 / 1))]

def nodeValue3869 : Sparse Master := [(Sum.inr 3869, (1 / 1))]

def nodeValue3870 : Sparse Master := [(Sum.inr 3870, (1 / 1))]

def nodeValue3871 : Sparse Master := [(Sum.inr 3871, (1 / 1))]

def nodeValue3872 : Sparse Master := [(Sum.inr 3872, (1 / 1))]

def nodeValue3873 : Sparse Master := [(Sum.inr 3873, (1 / 1))]

def nodeValue3874 : Sparse Master := [(Sum.inr 3874, (1 / 1))]

def nodeValue3875 : Sparse Master := [(Sum.inr 3875, (1 / 1))]

def nodeValue3876 : Sparse Master := [(Sum.inr 3876, (1 / 1))]

def nodeValue3877 : Sparse Master := [(Sum.inr 3877, (1 / 1))]

def nodeValue3878 : Sparse Master := [(Sum.inr 3878, (1 / 1))]

def nodeValue3879 : Sparse Master := [(Sum.inr 3879, (1 / 1))]

def nodeValue3880 : Sparse Master := [(Sum.inr 3880, (1 / 1))]

def nodeValue3881 : Sparse Master := [(Sum.inr 3881, (1 / 1))]

def nodeValue3882 : Sparse Master := [(Sum.inl 0, (17 / 4320)), (Sum.inl 2, (1 / 96)), (Sum.inl 3, (1 / 6)), (Sum.inl 13, (1 / 27)), (Sum.inl 12, (1 / 9)), (Sum.inl 4, (1 / 9)), (Sum.inl 1, (-1 / 12))]

def nodeValue3883 : Sparse Master := [(Sum.inl 0, (-11 / 2160)), (Sum.inl 2, (-1 / 144)), (Sum.inl 3, (-1 / 18)), (Sum.inl 13, (-1 / 54)), (Sum.inl 12, (-1 / 27)), (Sum.inl 4, (-1 / 54)), (Sum.inl 1, (1 / 36))]

def nodeValue3884 : Sparse Master := [(Sum.inr 3884, (1 / 1))]

def nodeValue3885 : Sparse Master := [(Sum.inr 3885, (1 / 1))]

def nodeValue3886 : Sparse Master := [(Sum.inr 3886, (1 / 1))]

def nodeValue3887 : Sparse Master := [(Sum.inl 0, (-17 / 2160)), (Sum.inl 2, (1 / 432)), (Sum.inl 3, (-1 / 27)), (Sum.inl 12, (-1 / 54)), (Sum.inl 4, (-1 / 27)), (Sum.inl 1, (5 / 216))]

def nodeValue3888 : Sparse Master := [(Sum.inl 0, (-1 / 120)), (Sum.inl 2, (-1 / 432)), (Sum.inl 3, (1 / 27)), (Sum.inl 4, (1 / 27)), (Sum.inl 1, (5 / 432))]

def nodeValue3889 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 2, (-1 / 432)), (Sum.inl 3, (1 / 27)), (Sum.inl 12, (1 / 27)), (Sum.inl 1, (-5 / 216))]

def nodeValue3890 : Sparse Master := [(Sum.inr 3890, (1 / 1))]

def nodeValue3891 : Sparse Master := [(Sum.inr 3891, (1 / 1))]

def nodeValue3892 : Sparse Master := [(Sum.inr 3892, (1 / 1))]

def nodeValue3893 : Sparse Master := [(Sum.inr 3893, (1 / 1))]

def nodeValue3894 : Sparse Master := [(Sum.inr 3894, (1 / 1))]

def nodeValue3895 : Sparse Master := [(Sum.inr 3895, (1 / 1))]

def nodeValue3896 : Sparse Master := [(Sum.inr 3896, (1 / 1))]

def nodeValue3897 : Sparse Master := [(Sum.inr 3897, (1 / 1))]

def nodeValue3898 : Sparse Master := [(Sum.inr 3898, (1 / 1))]

def nodeValue3899 : Sparse Master := [(Sum.inr 3899, (1 / 1))]

def nodeValue3900 : Sparse Master := [(Sum.inr 3900, (1 / 1))]

def nodeValue3901 : Sparse Master := [(Sum.inr 3901, (1 / 1))]

def nodeValue3902 : Sparse Master := [(Sum.inr 3902, (1 / 1))]

def nodeValue3903 : Sparse Master := [(Sum.inr 3903, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue3904 : Sparse Master := []

def nodeValue3905 : Sparse Master := []

def nodeValue3906 : Sparse Master := [(Sum.inr 3906, (1 / 1))]

def nodeValue3907 : Sparse Master := [(Sum.inr 3907, (1 / 1))]

def nodeValue3908 : Sparse Master := []

def nodeValue3909 : Sparse Master := [(Sum.inr 3909, (1 / 1))]

def nodeValue3910 : Sparse Master := [(Sum.inr 3910, (1 / 1))]

def nodeValue3911 : Sparse Master := [(Sum.inl 0, (-7 / 432)), (Sum.inl 12, (-1 / 54)), (Sum.inl 1, (5 / 144))]

def nodeValue3912 : Sparse Master := [(Sum.inl 0, (-1 / 108)), (Sum.inl 12, (1 / 27)), (Sum.inl 1, (-1 / 36))]

def nodeValue3913 : Sparse Master := [(Sum.inr 3913, (1 / 1))]

def nodeValue3914 : Sparse Master := []

def nodeValue3915 : Sparse Master := [(Sum.inl 0, (-1 / 108)), (Sum.inl 12, (1 / 27)), (Sum.inl 1, (-1 / 36))]

def nodeValue3916 : Sparse Master := [(Sum.inl 0, (-1 / 180)), (Sum.inl 12, (-1 / 9)), (Sum.inl 1, (-1 / 12))]

def nodeValue3917 : Sparse Master := []

def nodeValue3920 : Sparse Master := []

def nodeValue3921 : Sparse Master := []

def nodeValue3922 : Sparse Master := [(Sum.inr 3922, (1 / 1))]

def nodeValue3923 : Sparse Master := []

def nodeValue3925 : Sparse Master := [(Sum.inl 0, (-11 / 2160)), (Sum.inl 5, (-1 / 72)), (Sum.inl 2, (1 / 48)), (Sum.inl 8, (1 / 27)), (Sum.inl 3, (1 / 27)), (Sum.inl 24, (-1 / 9)), (Sum.inl 56, (-1 / 18)), (Sum.inl 4, (1 / 27)), (Sum.inl 27, (1 / 24)), (Sum.inl 1, (-1 / 54)), (Sum.inl 30, (-1 / 18))]

def nodeValue3926 : Sparse Master := [(Sum.inl 0, (-7 / 1080)), (Sum.inl 24, (1 / 18)), (Sum.inl 27, (-1 / 18)), (Sum.inl 1, (-1 / 216)), (Sum.inl 30, (1 / 18))]

def nodeValue3927 : Sparse Master := [(Sum.inr 3927, (1 / 1))]

def nodeValue3929 : Sparse Master := [(Sum.inr 3929, (1 / 1))]

def nodeValue3930 : Sparse Master := [(Sum.inl 0, (-13 / 1080)), (Sum.inl 5, (1 / 72)), (Sum.inl 8, (1 / 18)), (Sum.inl 24, (-1 / 18)), (Sum.inl 27, (-1 / 24)), (Sum.inl 1, (-1 / 216)), (Sum.inl 30, (-1 / 9))]

def nodeValue3931 : Sparse Master := [(Sum.inl 0, (-2 / 135)), (Sum.inl 5, (-1 / 216)), (Sum.inl 8, (-1 / 54)), (Sum.inl 27, (1 / 72)), (Sum.inl 1, (-1 / 108)), (Sum.inl 30, (1 / 18))]

def nodeValue3933 : Sparse Master := [(Sum.inl 0, (-1 / 90)), (Sum.inl 5, (-1 / 216)), (Sum.inl 8, (-1 / 54)), (Sum.inl 24, (1 / 18)), (Sum.inl 27, (1 / 72)), (Sum.inl 1, (1 / 108))]

def nodeValue3934 : Sparse Master := [(Sum.inl 0, (-13 / 1080)), (Sum.inl 27, (-1 / 36)), (Sum.inl 1, (-1 / 216)), (Sum.inl 30, (-1 / 9))]

def nodeValue3935 : Sparse Master := [(Sum.inr 3935, (1 / 1))]

def nodeValue3936 : Sparse Master := [(Sum.inl 0, (-1 / 240)), (Sum.inl 5, (-1 / 72)), (Sum.inl 2, (23 / 864)), (Sum.inl 7, (1 / 54)), (Sum.inl 8, (1 / 54)), (Sum.inl 51, (-1 / 18)), (Sum.inl 3, (1 / 27)), (Sum.inl 24, (-1 / 18)), (Sum.inl 4, (1 / 54)), (Sum.inl 27, (1 / 18)), (Sum.inl 1, (-31 / 864)), (Sum.inl 30, (-1 / 18)), (Sum.inl 31, (-1 / 18))]

def nodeValue3937 : Sparse Master := [(Sum.inl 0, (-1 / 108)), (Sum.inl 5, (-1 / 54)), (Sum.inl 2, (1 / 72)), (Sum.inl 7, (1 / 54)), (Sum.inl 8, (1 / 54)), (Sum.inl 3, (1 / 18)), (Sum.inl 23, (-1 / 18)), (Sum.inl 24, (-1 / 18)), (Sum.inl 55, (-1 / 18)), (Sum.inl 12, (1 / 54)), (Sum.inl 27, (1 / 24))]

def nodeValue3938 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 5, (1 / 108)), (Sum.inl 2, (-5 / 432)), (Sum.inl 51, (-1 / 9)), (Sum.inl 3, (1 / 18)), (Sum.inl 55, (-1 / 18)), (Sum.inl 12, (1 / 54)), (Sum.inl 4, (1 / 27)), (Sum.inl 27, (-1 / 72)), (Sum.inl 31, (-1 / 9))]

def nodeValue3939 : Sparse Master := [(Sum.inl 0, (-7 / 864)), (Sum.inl 5, (-1 / 216)), (Sum.inl 2, (-1 / 864)), (Sum.inl 51, (1 / 18)), (Sum.inl 1, (1 / 144)), (Sum.inl 31, (1 / 18))]

def nodeValue3940 : Sparse Master := []

def nodeValue3941 : Sparse Master := []

def nodeValue3942 : Sparse Master := [(Sum.inr 3942, (1 / 1))]

def nodeValue3944 : Sparse Master := []

def nodeValue3945 : Sparse Master := [(Sum.inr 3945, (1 / 1))]

def nodeValue3946 : Sparse Master := [(Sum.inr 3946, (1 / 1))]

def nodeValue3947 : Sparse Master := [(Sum.inr 3947, (1 / 1))]

def nodeValue3949 : Sparse Master := [(Sum.inr 3949, (1 / 1))]

def nodeValue3950 : Sparse Master := []

def nodeValue3951 : Sparse Master := []

def nodeValue3952 : Sparse Master := [(Sum.inr 3952, (1 / 1))]

def nodeValue3953 : Sparse Master := []

def nodeValue3954 : Sparse Master := [(Sum.inr 3954, (1 / 1))]

def nodeValue3955 : Sparse Master := [(Sum.inr 3955, (1 / 1))]

def nodeValue3956 : Sparse Master := []

def nodeValue3957 : Sparse Master := [(Sum.inr 3957, (1 / 1))]

def nodeValue3958 : Sparse Master := [(Sum.inr 3958, (1 / 1))]

def nodeValue3959 : Sparse Master := [(Sum.inr 3959, (1 / 1))]

def nodeValue3960 : Sparse Master := [(Sum.inr 3960, (1 / 1))]

def nodeValue3961 : Sparse Master := [(Sum.inr 3961, (1 / 1))]

def nodeValue3962 : Sparse Master := []

def nodeValue3963 : Sparse Master := [(Sum.inr 3963, (1 / 1))]

def nodeValue3964 : Sparse Master := [(Sum.inr 3964, (1 / 1))]

def nodeValue3965 : Sparse Master := [(Sum.inl 0, (-17 / 1440)), (Sum.inl 5, (1 / 216)), (Sum.inl 6, (-1 / 864)), (Sum.inl 2, (1 / 72)), (Sum.inl 8, (1 / 27)), (Sum.inl 27, (-1 / 72)), (Sum.inl 1, (-5 / 216)), (Sum.inl 30, (-1 / 18))]

def nodeValue3966 : Sparse Master := [(Sum.inl 0, (-23 / 4320)), (Sum.inl 5, (1 / 108)), (Sum.inl 6, (-1 / 864)), (Sum.inl 2, (1 / 216)), (Sum.inl 7, (1 / 54)), (Sum.inl 35, (1 / 54)), (Sum.inl 3, (7 / 54)), (Sum.inl 13, (1 / 54)), (Sum.inl 24, (-1 / 18)), (Sum.inl 12, (1 / 27)), (Sum.inl 56, (-1 / 18)), (Sum.inl 26, (1 / 27)), (Sum.inl 4, (2 / 27)), (Sum.inl 27, (-1 / 72)), (Sum.inl 1, (-7 / 216))]

def nodeValue3967 : Sparse Master := [(Sum.inl 0, (-23 / 2160)), (Sum.inl 5, (1 / 216)), (Sum.inl 6, (-1 / 864)), (Sum.inl 2, (1 / 96)), (Sum.inl 7, (1 / 54)), (Sum.inl 8, (1 / 54)), (Sum.inl 3, (1 / 18)), (Sum.inl 24, (-1 / 18)), (Sum.inl 4, (1 / 27)), (Sum.inl 27, (-1 / 72)), (Sum.inl 1, (1 / 216))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue3968 : Sparse Master := []

def nodeValue3969 : Sparse Master := [(Sum.inl 0, (-7 / 2160)), (Sum.inl 5, (1 / 216)), (Sum.inl 6, (-1 / 864)), (Sum.inl 2, (23 / 864)), (Sum.inl 51, (-1 / 18)), (Sum.inl 3, (2 / 27)), (Sum.inl 52, (1 / 54)), (Sum.inl 4, (1 / 18)), (Sum.inl 1, (-7 / 144)), (Sum.inl 31, (-1 / 9))]

def nodeValue3970 : Sparse Master := [(Sum.inl 0, (-7 / 720)), (Sum.inl 5, (1 / 216)), (Sum.inl 6, (-1 / 864)), (Sum.inl 2, (1 / 96)), (Sum.inl 51, (-1 / 18)), (Sum.inl 3, (5 / 54)), (Sum.inl 13, (1 / 54)), (Sum.inl 52, (1 / 54)), (Sum.inl 12, (1 / 27)), (Sum.inl 4, (1 / 54)), (Sum.inl 1, (-1 / 216)), (Sum.inl 31, (-1 / 18))]

def nodeValue3971 : Sparse Master := []

def nodeValue3972 : Sparse Master := [(Sum.inr 3972, (1 / 1))]

def nodeValue3973 : Sparse Master := [(Sum.inr 3973, (1 / 1))]

def nodeValue3974 : Sparse Master := [(Sum.inr 3974, (1 / 1))]

def nodeValue3975 : Sparse Master := []

def nodeValue3976 : Sparse Master := []

def nodeValue3977 : Sparse Master := [(Sum.inl 0, (1 / 1080)), (Sum.inl 2, (5 / 864)), (Sum.inl 3, (2 / 27)), (Sum.inl 13, (1 / 54)), (Sum.inl 12, (1 / 27)), (Sum.inl 4, (1 / 27)), (Sum.inl 1, (-19 / 864))]

def nodeValue3978 : Sparse Master := [(Sum.inr 3978, (1 / 1))]

def nodeValue3979 : Sparse Master := []

def nodeValue3980 : Sparse Master := [(Sum.inl 0, (-47 / 4320)), (Sum.inl 2, (11 / 864)), (Sum.inl 3, (1 / 54)), (Sum.inl 4, (1 / 27)), (Sum.inl 1, (-23 / 432))]

def nodeValue3981 : Sparse Master := [(Sum.inl 0, (-11 / 720)), (Sum.inl 2, (-1 / 144)), (Sum.inl 1, (1 / 72))]

def nodeValue3982 : Sparse Master := [(Sum.inl 0, (-1 / 90)), (Sum.inl 2, (-5 / 864)), (Sum.inl 3, (-1 / 54)), (Sum.inl 4, (-1 / 54)), (Sum.inl 1, (7 / 864))]

def nodeValue3983 : Sparse Master := [(Sum.inr 3983, (1 / 1))]

def nodeValue3984 : Sparse Master := [(Sum.inl 0, (-49 / 4320)), (Sum.inl 2, (1 / 864)), (Sum.inl 3, (-1 / 54)), (Sum.inl 4, (-1 / 27)), (Sum.inl 1, (5 / 432))]

def nodeValue3985 : Sparse Master := []

def nodeValue3986 : Sparse Master := []

def nodeValue3987 : Sparse Master := [(Sum.inl 0, (-1 / 120)), (Sum.inl 2, (-1 / 432)), (Sum.inl 3, (1 / 27)), (Sum.inl 4, (1 / 27)), (Sum.inl 1, (5 / 432))]

def nodeValue3988 : Sparse Master := []

def nodeValue3989 : Sparse Master := []

def nodeValue3990 : Sparse Master := [(Sum.inl 0, (-7 / 2160)), (Sum.inl 2, (5 / 864)), (Sum.inl 3, (5 / 54)), (Sum.inl 12, (1 / 27)), (Sum.inl 26, (1 / 54)), (Sum.inl 4, (1 / 27)), (Sum.inl 1, (-17 / 864))]

def nodeValue3991 : Sparse Master := []

def nodeValue3992 : Sparse Master := [(Sum.inl 0, (-47 / 4320)), (Sum.inl 2, (11 / 864)), (Sum.inl 3, (1 / 54)), (Sum.inl 4, (1 / 27)), (Sum.inl 1, (-23 / 432))]

def nodeValue3993 : Sparse Master := [(Sum.inl 0, (-1 / 216)), (Sum.inl 2, (-1 / 864)), (Sum.inl 3, (-1 / 18)), (Sum.inl 12, (-1 / 54)), (Sum.inl 26, (-1 / 54)), (Sum.inl 4, (-1 / 27)), (Sum.inl 1, (5 / 288))]

def nodeValue3994 : Sparse Master := [(Sum.inl 0, (-1 / 4320)), (Sum.inl 2, (5 / 432)), (Sum.inl 3, (2 / 27)), (Sum.inl 26, (1 / 54)), (Sum.inl 4, (1 / 18)), (Sum.inl 1, (-49 / 864)), (Sum.inl 31, (-1 / 18))]

def nodeValue3995 : Sparse Master := [(Sum.inl 0, (-31 / 4320)), (Sum.inl 2, (-1 / 288)), (Sum.inl 3, (-1 / 54)), (Sum.inl 4, (-1 / 54)), (Sum.inl 1, (1 / 216)), (Sum.inl 31, (1 / 18))]

def nodeValue3996 : Sparse Master := []

def nodeValue3997 : Sparse Master := [(Sum.inl 0, (-1 / 288)), (Sum.inl 2, (1 / 216)), (Sum.inl 3, (-1 / 27)), (Sum.inl 26, (-1 / 54)), (Sum.inl 1, (-1 / 864))]

def nodeValue3998 : Sparse Master := [(Sum.inl 0, (-49 / 4320)), (Sum.inl 2, (1 / 864)), (Sum.inl 3, (-1 / 54)), (Sum.inl 4, (-1 / 27)), (Sum.inl 1, (5 / 432))]

def nodeValue3999 : Sparse Master := []

def nodeValue4000 : Sparse Master := []

def nodeValue4001 : Sparse Master := []

def nodeValue4002 : Sparse Master := [(Sum.inl 2, (1 / 54)), (Sum.inl 3, (2 / 27)), (Sum.inl 12, (1 / 54)), (Sum.inl 4, (2 / 27)), (Sum.inl 1, (-2 / 27)), (Sum.inl 31, (-1 / 9))]

def nodeValue4003 : Sparse Master := [(Sum.inl 0, (-1 / 135)), (Sum.inl 2, (-5 / 432)), (Sum.inl 3, (-1 / 27)), (Sum.inl 12, (-1 / 54)), (Sum.inl 1, (7 / 432))]

def nodeValue4004 : Sparse Master := [(Sum.inl 0, (-17 / 2160)), (Sum.inl 2, (-1 / 216)), (Sum.inl 1, (1 / 144)), (Sum.inl 31, (-1 / 9))]

def nodeValue4005 : Sparse Master := []

def nodeValue4006 : Sparse Master := []

def nodeValue4007 : Sparse Master := []

def nodeValue4008 : Sparse Master := []

def nodeValue4009 : Sparse Master := []

def nodeValue4010 : Sparse Master := [(Sum.inr 4010, (1 / 1))]

def nodeValue4011 : Sparse Master := []

def nodeValue4012 : Sparse Master := [(Sum.inl 0, (-11 / 1440)), (Sum.inl 2, (1 / 864)), (Sum.inl 3, (-1 / 54)), (Sum.inl 12, (-1 / 54)), (Sum.inl 1, (-19 / 432))]

def nodeValue4013 : Sparse Master := [(Sum.inl 0, (-67 / 4320)), (Sum.inl 4, (-1 / 54)), (Sum.inl 1, (5 / 288))]

def nodeValue4014 : Sparse Master := [(Sum.inl 0, (-1 / 90)), (Sum.inl 1, (-1 / 18))]

def nodeValue4015 : Sparse Master := [(Sum.inl 0, (-23 / 2160)), (Sum.inl 4, (1 / 27)), (Sum.inl 1, (1 / 144))]

def nodeValue4016 : Sparse Master := []

def nodeValue4017 : Sparse Master := [(Sum.inl 0, (-23 / 2160)), (Sum.inl 4, (1 / 27)), (Sum.inl 1, (1 / 144))]

def nodeValue4018 : Sparse Master := []

def nodeValue4019 : Sparse Master := []

def nodeValue4020 : Sparse Master := [(Sum.inl 0, (-7 / 720)), (Sum.inl 4, (-1 / 9)), (Sum.inl 1, (1 / 48))]

def nodeValue4021 : Sparse Master := []

def nodeValue4022 : Sparse Master := [(Sum.inr 4022, (1 / 1))]

def nodeValue4023 : Sparse Master := [(Sum.inl 0, (-37 / 4320)), (Sum.inl 5, (1 / 108)), (Sum.inl 6, (-1 / 864)), (Sum.inl 2, (-1 / 216)), (Sum.inl 7, (1 / 54)), (Sum.inl 35, (1 / 54)), (Sum.inl 3, (1 / 6)), (Sum.inl 23, (-1 / 18)), (Sum.inl 54, (-1 / 18)), (Sum.inl 12, (1 / 27)), (Sum.inl 25, (-1 / 9)), (Sum.inl 26, (2 / 27)), (Sum.inl 4, (2 / 27)), (Sum.inl 27, (-1 / 72)), (Sum.inl 1, (1 / 432))]

def nodeValue4024 : Sparse Master := [(Sum.inr 4024, (1 / 1))]

def nodeValue4025 : Sparse Master := [(Sum.inr 4025, (1 / 1))]

def nodeValue4026 : Sparse Master := [(Sum.inl 0, (1 / 4320)), (Sum.inl 2, (1 / 96)), (Sum.inl 3, (1 / 6)), (Sum.inl 12, (2 / 27)), (Sum.inl 25, (-1 / 18)), (Sum.inl 26, (1 / 27)), (Sum.inl 4, (1 / 9)), (Sum.inl 1, (-7 / 108))]

def nodeValue4027 : Sparse Master := [(Sum.inl 0, (-1 / 180)), (Sum.inl 2, (-1 / 144)), (Sum.inl 3, (-1 / 27)), (Sum.inl 25, (1 / 18)), (Sum.inl 26, (-1 / 54)), (Sum.inl 4, (-1 / 54)), (Sum.inl 1, (5 / 432))]

def nodeValue4028 : Sparse Master := [(Sum.inl 0, (-1 / 540)), (Sum.inl 2, (1 / 216)), (Sum.inl 3, (-1 / 27)), (Sum.inl 12, (-1 / 27)), (Sum.inl 25, (1 / 18)), (Sum.inl 1, (-5 / 216))]

def nodeValue4029 : Sparse Master := [(Sum.inl 0, (-17 / 2160)), (Sum.inl 2, (1 / 432)), (Sum.inl 3, (-1 / 27)), (Sum.inl 12, (-1 / 54)), (Sum.inl 4, (-1 / 27)), (Sum.inl 1, (5 / 216))]

def nodeValue4030 : Sparse Master := [(Sum.inl 0, (-1 / 216)), (Sum.inl 2, (-1 / 216)), (Sum.inl 25, (-1 / 9)), (Sum.inl 1, (-1 / 54))]

def nodeValue4031 : Sparse Master := [(Sum.inl 0, (-43 / 4320)), (Sum.inl 5, (1 / 216)), (Sum.inl 6, (-1 / 864)), (Sum.inl 2, (-1 / 216)), (Sum.inl 7, (1 / 27)), (Sum.inl 3, (2 / 27)), (Sum.inl 23, (-1 / 18)), (Sum.inl 12, (1 / 27)), (Sum.inl 27, (-1 / 72)), (Sum.inl 1, (-11 / 216))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue4032 : Sparse Master := [(Sum.inl 0, (-13 / 2160)), (Sum.inl 2, (-5 / 432)), (Sum.inl 3, (2 / 27)), (Sum.inl 25, (-1 / 18)), (Sum.inl 26, (1 / 27)), (Sum.inl 4, (1 / 27))]

def nodeValue4033 : Sparse Master := [(Sum.inl 0, (-29 / 4320)), (Sum.inl 2, (1 / 96)), (Sum.inl 3, (1 / 18)), (Sum.inl 12, (1 / 27)), (Sum.inl 4, (1 / 27)), (Sum.inl 1, (-1 / 48))]

def nodeValue4034 : Sparse Master := []

def nodeValue4035 : Sparse Master := []

def nodeValue4036 : Sparse Master := []

def nodeValue4037 : Sparse Master := []

def nodeValue4038 : Sparse Master := []

def nodeValue4039 : Sparse Master := [(Sum.inl 0, (-7 / 432)), (Sum.inl 12, (-1 / 54)), (Sum.inl 1, (5 / 144))]

def nodeValue4040 : Sparse Master := []

def nodeValue4041 : Sparse Master := [(Sum.inr 4041, (1 / 1))]

def nodeValue4042 : Sparse Master := [(Sum.inr 4042, (1 / 1))]

def nodeValue4043 : Sparse Master := [(Sum.inr 4043, (1 / 1))]

def nodeValue4044 : Sparse Master := []

def nodeValue4045 : Sparse Master := [(Sum.inr 4045, (1 / 1))]

def nodeValue4046 : Sparse Master := [(Sum.inr 4046, (1 / 1))]

def nodeValue4047 : Sparse Master := [(Sum.inr 4047, (1 / 1))]

def nodeValue4048 : Sparse Master := []

def nodeValue4049 : Sparse Master := []

def nodeValue4050 : Sparse Master := [(Sum.inl 0, (-67 / 4320)), (Sum.inl 4, (-1 / 54)), (Sum.inl 1, (5 / 288))]

def nodeValue4051 : Sparse Master := [(Sum.inl 0, (-79 / 2160)), (Sum.inl 12, (1 / 54)), (Sum.inl 1, (-7 / 144))]

def nodeValue4052 : Sparse Master := []

def nodeValue4053 : Sparse Master := [(Sum.inl 0, (-47 / 2160)), (Sum.inl 4, (1 / 27)), (Sum.inl 1, (-7 / 144))]

def nodeValue4054 : Sparse Master := []

def nodeValue4055 : Sparse Master := []

def nodeValue4056 : Sparse Master := [(Sum.inr 4056, (1 / 1))]

def nodeValue4057 : Sparse Master := [(Sum.inr 4057, (1 / 1))]

def nodeValue4058 : Sparse Master := [(Sum.inr 4058, (1 / 1))]

def nodeValue4059 : Sparse Master := [(Sum.inr 4059, (1 / 1))]

def nodeValue4060 : Sparse Master := [(Sum.inr 4060, (1 / 1))]

def nodeValue4061 : Sparse Master := [(Sum.inr 4061, (1 / 1))]

def nodeValue4062 : Sparse Master := [(Sum.inr 4062, (1 / 1))]

def nodeValue4063 : Sparse Master := [(Sum.inr 4063, (1 / 1))]

def nodeValue4064 : Sparse Master := [(Sum.inr 4064, (1 / 1))]

def nodeValue4065 : Sparse Master := [(Sum.inr 4065, (1 / 1))]

def nodeValue4066 : Sparse Master := [(Sum.inr 4066, (1 / 1))]

def nodeValue4067 : Sparse Master := [(Sum.inr 4067, (1 / 1))]

def nodeValue4068 : Sparse Master := [(Sum.inr 4068, (1 / 1))]

def nodeValue4069 : Sparse Master := [(Sum.inr 4069, (1 / 1))]

def nodeValue4070 : Sparse Master := [(Sum.inr 4070, (1 / 1))]

def nodeValue4071 : Sparse Master := [(Sum.inr 4071, (1 / 1))]

def nodeValue4072 : Sparse Master := [(Sum.inr 4072, (1 / 1))]

def nodeValue4073 : Sparse Master := [(Sum.inr 4073, (1 / 1))]

def nodeValue4074 : Sparse Master := [(Sum.inr 4074, (1 / 1))]

def nodeValue4075 : Sparse Master := [(Sum.inr 4075, (1 / 1))]

def nodeValue4076 : Sparse Master := [(Sum.inr 4076, (1 / 1))]

def nodeValue4077 : Sparse Master := [(Sum.inr 4077, (1 / 1))]

def nodeValue4078 : Sparse Master := [(Sum.inr 4078, (1 / 1))]

def nodeValue4079 : Sparse Master := [(Sum.inr 4079, (1 / 1))]

def nodeValue4080 : Sparse Master := [(Sum.inr 4080, (1 / 1))]

def nodeValue4081 : Sparse Master := [(Sum.inr 4081, (1 / 1))]

def nodeValue4082 : Sparse Master := [(Sum.inr 4082, (1 / 1))]

def nodeValue4083 : Sparse Master := [(Sum.inr 4083, (1 / 1))]

def nodeValue4084 : Sparse Master := [(Sum.inr 4084, (1 / 1))]

def nodeValue4085 : Sparse Master := [(Sum.inr 4085, (1 / 1))]

def nodeValue4086 : Sparse Master := [(Sum.inr 4086, (1 / 1))]

def nodeValue4087 : Sparse Master := [(Sum.inr 4087, (1 / 1))]

def nodeValue4088 : Sparse Master := [(Sum.inr 4088, (1 / 1))]

def nodeValue4089 : Sparse Master := [(Sum.inr 4089, (1 / 1))]

def nodeValue4090 : Sparse Master := [(Sum.inr 4090, (1 / 1))]

def nodeValue4091 : Sparse Master := [(Sum.inr 4091, (1 / 1))]

def nodeValue4092 : Sparse Master := [(Sum.inr 4092, (1 / 1))]

def nodeValue4093 : Sparse Master := [(Sum.inl 0, (-1 / 24)), (Sum.inl 1, (1 / 24))]

def nodeValue4094 : Sparse Master := [(Sum.inl 0, (-1 / 30)), (Sum.inl 1, (-1 / 6))]

def nodeValue4095 : Sparse Master := []

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue4096 : Sparse Master := [(Sum.inl 0, (-19 / 360)), (Sum.inl 1, (-1 / 72))]

def nodeValue4097 : Sparse Master := []

def nodeValue4098 : Sparse Master := [(Sum.inr 535, (-1 / 4)), (Sum.inr 656, (-1 / 4))]

def nodeValue4099 : Sparse Master := [(Sum.inr 536, (-1 / 4)), (Sum.inr 657, (-1 / 4))]

def nodeValue4100 : Sparse Master := [(Sum.inr 537, (-1 / 4)), (Sum.inr 662, (-1 / 4))]

def nodeValue4101 : Sparse Master := [(Sum.inr 538, (-1 / 4)), (Sum.inr 663, (-1 / 4))]

def nodeValue4102 : Sparse Master := [(Sum.inr 539, (-1 / 4)), (Sum.inr 664, (-1 / 4))]

def nodeValue4103 : Sparse Master := [(Sum.inr 540, (-1 / 4)), (Sum.inr 665, (-1 / 4))]

def nodeValue4104 : Sparse Master := [(Sum.inr 541, (-1 / 4)), (Sum.inr 674, (-1 / 4))]

def nodeValue4105 : Sparse Master := [(Sum.inr 542, (-1 / 4)), (Sum.inr 681, (-1 / 4))]

def nodeValue4106 : Sparse Master := [(Sum.inr 543, (-1 / 4)), (Sum.inr 675, (-1 / 4))]

def nodeValue4107 : Sparse Master := [(Sum.inr 544, (-1 / 4)), (Sum.inr 682, (-1 / 4))]

def nodeValue4108 : Sparse Master := [(Sum.inr 545, (-1 / 4)), (Sum.inr 683, (-1 / 4))]

def nodeValue4109 : Sparse Master := [(Sum.inr 546, (-1 / 4)), (Sum.inr 676, (-1 / 4))]

def nodeValue4110 : Sparse Master := [(Sum.inr 547, (-1 / 4)), (Sum.inr 684, (-1 / 4))]

def nodeValue4111 : Sparse Master := [(Sum.inr 548, (-1 / 4)), (Sum.inr 685, (-1 / 4))]

def nodeValue4112 : Sparse Master := [(Sum.inr 549, (-1 / 4)), (Sum.inr 686, (-1 / 4))]

def nodeValue4113 : Sparse Master := [(Sum.inr 550, (-1 / 4)), (Sum.inr 658, (-1 / 4))]

def nodeValue4115 : Sparse Master := [(Sum.inr 552, (-1 / 4)), (Sum.inr 660, (-1 / 4))]

def nodeValue4117 : Sparse Master := []

def nodeValue4118 : Sparse Master := []

def nodeValue4119 : Sparse Master := [(Sum.inr 554, (-1 / 4)), (Sum.inr 668, (-1 / 4))]

def nodeValue4120 : Sparse Master := []

def nodeValue4121 : Sparse Master := [(Sum.inr 555, (-1 / 4)), (Sum.inr 671, (-1 / 4))]

def nodeValue4122 : Sparse Master := [(Sum.inr 556, (-1 / 4)), (Sum.inr 670, (-1 / 4))]

def nodeValue4123 : Sparse Master := []

def nodeValue4125 : Sparse Master := []

def nodeValue4126 : Sparse Master := [(Sum.inr 557, (-1 / 4)), (Sum.inr 677, (-1 / 4))]

def nodeValue4127 : Sparse Master := []

def nodeValue4128 : Sparse Master := [(Sum.inr 559, (-1 / 4)), (Sum.inr 690, (-1 / 4))]

def nodeValue4130 : Sparse Master := []

def nodeValue4131 : Sparse Master := []

def nodeValue4132 : Sparse Master := [(Sum.inr 562, (-1 / 4)), (Sum.inr 679, (-1 / 4))]

def nodeValue4133 : Sparse Master := [(Sum.inr 563, (-1 / 4)), (Sum.inr 692, (-1 / 4))]

def nodeValue4134 : Sparse Master := [(Sum.inr 564, (-1 / 4)), (Sum.inr 695, (-1 / 4))]

def nodeValue4136 : Sparse Master := []

def nodeValue4137 : Sparse Master := []

def nodeValue4138 : Sparse Master := [(Sum.inr 566, (-1 / 4)), (Sum.inr 694, (-1 / 4))]

def nodeValue4139 : Sparse Master := [(Sum.inr 567, (-1 / 4)), (Sum.inr 1488, (-1 / 4))]

def nodeValue4140 : Sparse Master := [(Sum.inr 568, (-1 / 4)), (Sum.inr 1489, (-1 / 4))]

def nodeValue4141 : Sparse Master := [(Sum.inr 569, (-1 / 4)), (Sum.inr 1490, (-1 / 4))]

def nodeValue4142 : Sparse Master := [(Sum.inr 570, (-1 / 4)), (Sum.inr 765, (-1 / 4))]

def nodeValue4143 : Sparse Master := [(Sum.inr 571, (-1 / 4)), (Sum.inr 1491, (-1 / 4))]

def nodeValue4144 : Sparse Master := [(Sum.inr 572, (-1 / 4)), (Sum.inr 1492, (-1 / 4))]

def nodeValue4145 : Sparse Master := [(Sum.inr 573, (-1 / 4)), (Sum.inr 1493, (-1 / 4))]

def nodeValue4146 : Sparse Master := [(Sum.inr 574, (-1 / 4)), (Sum.inr 1494, (-1 / 4))]

def nodeValue4147 : Sparse Master := [(Sum.inr 575, (-1 / 4)), (Sum.inr 1495, (-1 / 4))]

def nodeValue4148 : Sparse Master := [(Sum.inr 576, (-1 / 4)), (Sum.inr 1496, (-1 / 4))]

def nodeValue4149 : Sparse Master := [(Sum.inr 4149, (1 / 1))]

def nodeValue4150 : Sparse Master := [(Sum.inr 4150, (1 / 1))]

def nodeValue4151 : Sparse Master := [(Sum.inr 4151, (1 / 1))]

def nodeValue4152 : Sparse Master := [(Sum.inr 4152, (1 / 1))]

def nodeValue4153 : Sparse Master := [(Sum.inr 4153, (1 / 1))]

def nodeValue4154 : Sparse Master := [(Sum.inr 4154, (1 / 1))]

def nodeValue4155 : Sparse Master := [(Sum.inr 4155, (1 / 1))]

def nodeValue4156 : Sparse Master := [(Sum.inr 4156, (1 / 1))]

def nodeValue4157 : Sparse Master := [(Sum.inr 4157, (1 / 1))]

def nodeValue4158 : Sparse Master := [(Sum.inr 4158, (1 / 1))]

def nodeValue4159 : Sparse Master := [(Sum.inr 4159, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue4160 : Sparse Master := [(Sum.inr 4160, (1 / 1))]

def nodeValue4161 : Sparse Master := [(Sum.inr 4161, (1 / 1))]

def nodeValue4162 : Sparse Master := [(Sum.inr 4162, (1 / 1))]

def nodeValue4163 : Sparse Master := [(Sum.inr 4163, (1 / 1))]

def nodeValue4164 : Sparse Master := [(Sum.inr 592, (-1 / 4)), (Sum.inr 1497, (-1 / 4))]

def nodeValue4165 : Sparse Master := [(Sum.inr 593, (-1 / 4)), (Sum.inr 1498, (-1 / 4))]

def nodeValue4166 : Sparse Master := [(Sum.inr 594, (-1 / 4)), (Sum.inr 1499, (-1 / 4))]

def nodeValue4167 : Sparse Master := [(Sum.inr 595, (-1 / 4)), (Sum.inr 1500, (-1 / 4))]

def nodeValue4168 : Sparse Master := [(Sum.inr 596, (-1 / 4)), (Sum.inr 845, (-1 / 4))]

def nodeValue4169 : Sparse Master := [(Sum.inr 4169, (1 / 1))]

def nodeValue4170 : Sparse Master := [(Sum.inr 4170, (1 / 1))]

def nodeValue4171 : Sparse Master := [(Sum.inr 599, (-1 / 4)), (Sum.inr 1506, (-1 / 4))]

def nodeValue4172 : Sparse Master := [(Sum.inr 600, (-1 / 4)), (Sum.inr 1507, (-1 / 4))]

def nodeValue4173 : Sparse Master := [(Sum.inr 4173, (1 / 1))]

def nodeValue4174 : Sparse Master := [(Sum.inr 602, (-1 / 4)), (Sum.inr 1509, (-1 / 4))]

def nodeValue4175 : Sparse Master := [(Sum.inr 603, (-1 / 4)), (Sum.inr 1517, (-1 / 4))]

def nodeValue4176 : Sparse Master := [(Sum.inr 4176, (1 / 1))]

def nodeValue4178 : Sparse Master := [(Sum.inr 4178, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue4224 : Sparse Master := [(Sum.inr 725, (-1 / 4)), (Sum.inr 771, (-1 / 4))]

def nodeValue4225 : Sparse Master := [(Sum.inr 726, (-1 / 4)), (Sum.inr 774, (-1 / 4))]

def nodeValue4227 : Sparse Master := []

def nodeValue4228 : Sparse Master := []

def nodeValue4229 : Sparse Master := [(Sum.inr 729, (-1 / 4)), (Sum.inr 773, (-1 / 4))]

def nodeValue4230 : Sparse Master := [(Sum.inr 730, (-1 / 4)), (Sum.inr 780, (-1 / 4))]

def nodeValue4231 : Sparse Master := [(Sum.inr 731, (-1 / 4)), (Sum.inr 781, (-1 / 4))]

def nodeValue4232 : Sparse Master := [(Sum.inr 732, (-1 / 4)), (Sum.inr 798, (-1 / 4))]

def nodeValue4233 : Sparse Master := [(Sum.inr 733, (-1 / 4)), (Sum.inr 799, (-1 / 4))]

def nodeValue4234 : Sparse Master := [(Sum.inr 734, (-1 / 4)), (Sum.inr 800, (-1 / 4))]

def nodeValue4235 : Sparse Master := [(Sum.inr 735, (-1 / 4)), (Sum.inr 801, (-1 / 4))]

def nodeValue4236 : Sparse Master := [(Sum.inr 736, (-1 / 4)), (Sum.inr 818, (-1 / 4))]

def nodeValue4237 : Sparse Master := [(Sum.inr 737, (-1 / 4)), (Sum.inr 840, (-1 / 4))]

def nodeValue4238 : Sparse Master := [(Sum.inr 738, (-1 / 4)), (Sum.inr 819, (-1 / 4))]

def nodeValue4239 : Sparse Master := [(Sum.inr 739, (-1 / 4)), (Sum.inr 841, (-1 / 4))]

def nodeValue4240 : Sparse Master := [(Sum.inr 740, (-1 / 4)), (Sum.inr 842, (-1 / 4))]

def nodeValue4241 : Sparse Master := [(Sum.inr 741, (-1 / 4)), (Sum.inr 820, (-1 / 4))]

def nodeValue4242 : Sparse Master := [(Sum.inr 742, (-1 / 4)), (Sum.inr 843, (-1 / 4))]

def nodeValue4243 : Sparse Master := [(Sum.inr 743, (-1 / 4)), (Sum.inr 844, (-1 / 4))]

def nodeValue4248 : Sparse Master := [(Sum.inr 782, (-1 / 2))]

def nodeValue4249 : Sparse Master := [(Sum.inr 783, (-1 / 4)), (Sum.inr 803, (-1 / 4))]

def nodeValue4251 : Sparse Master := [(Sum.inr 785, (-1 / 4)), (Sum.inr 804, (-1 / 4))]

def nodeValue4252 : Sparse Master := [(Sum.inr 786, (-1 / 4)), (Sum.inr 822, (-1 / 4))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue4352 : Sparse Master := [(Sum.inr 930, (-1 / 4)), (Sum.inr 1690, (-1 / 4))]

def nodeValue4353 : Sparse Master := [(Sum.inr 4353, (1 / 1))]

def nodeValue4354 : Sparse Master := [(Sum.inr 932, (-1 / 4)), (Sum.inr 1681, (-1 / 4))]

def nodeValue4355 : Sparse Master := [(Sum.inr 933, (-1 / 4)), (Sum.inr 1691, (-1 / 4))]

def nodeValue4356 : Sparse Master := [(Sum.inr 934, (-1 / 4)), (Sum.inr 1692, (-1 / 4))]

def nodeValue4397 : Sparse Master := []

end MUB6.Certificate.MixedSemantics

end OAI
end


