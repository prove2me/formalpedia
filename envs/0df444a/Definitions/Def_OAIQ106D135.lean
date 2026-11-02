-- Prove2me | Definitions.Def_OAIQ106D135
-- name    : OAIQ106D135
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T13:31:44.980485+00:00
-- url     : https://prove2.me/theorems/102148ab-e384-403c-a387-0575e70c0c3c
-- title:
--   Definitions bundle OAIQ106D135 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 5268 declarations of OpenAI's Lean: 5268 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.sourceA2553`, `OAI.MUB6.Certificate.MixedSemantics.sourceA2555`, `OAI.MUB6.Certificate.MixedSemantics.sourceA2556`, `OAI.MUB6.Certificate.MixedSemantics.sourceA2557`, `OAI.MUB6.Certificate.MixedSemantics.sourceA2558`, `OAI.MUB6.Certificate.MixedSemantics.sourceA256`, `OAI.MUB6.Certificate.MixedSemantics.sourceA2565`, `OAI.MUB6.Certificate.MixedSemantics.sourceA2566`, `OAI.MUB6.Certificate.MixedSemantics.sourceA257`, `OAI.MUB6.Certificate.MixedSemantics.sourceA2571`, `OAI.MUB6.Certificate.MixedSemantics.sourceA2572`, `OAI.MUB6.Certificate.MixedSemantics.sourceA2573`, `OAI.MUB6.Certificate.MixedSemantics.sourceA2574`, `OAI.MUB6.Certificate.MixedSemantics.sourceA2575`, `OAI.MUB6.Certificate.MixedSemantics.sourceA2576`, `OAI.MUB6.Certificate.MixedSemantics.sourceA2579`, `OAI.MUB6.Certificate.MixedSemantics.sourceA258`, `OAI.MUB6.Certificate.MixedSemantics.sourceA2580`, `OAI.MUB6.Certificate.MixedSemantics.sourceA2582`, `OAI.MUB6.Certificate.MixedSemantics.sourceA2583`, `OAI.MUB6.Certificate.MixedSemantics.sourceA2584`, `OAI.MUB6.Certificate.MixedSemantics.sourceA2587`, `OAI.MUB6.Certificate.MixedSemantics.sourceA2588`, `OAI.MUB6.Certificate.MixedSemantics.sourceA259`, `OAI.MUB6.Certificate.MixedSemantics.sourceA2591`, `OAI.MUB6.Certificate.MixedSemantics.sourceA2592`, `OAI.MUB6.Certificate.MixedSemantics.sourceA2595`, `OAI.MUB6.Certificate.MixedSemantics.sourceA2596`, `OAI.MUB6.Certificate.MixedSemantics.sourceA2597`, `OAI.MUB6.Certificate.MixedSemantics.sourceA2598`, `OAI.MUB6.Certificate.MixedSemantics.sourceA2599`, `OAI.MUB6.Certificate.MixedSemantics.sourceA26`, `OAI.MUB6.Certificate.MixedSemantics.sourceA260`, `OAI.MUB6.Certificate.MixedSemantics.sourceA2602`, `OAI.MUB6.Certificate.MixedSemantics.sourceA2603`, `OAI.MUB6.Certificate.MixedSemantics.sourceA2607`, `OAI.MUB6.Certificate.MixedSemantics.sourceA2608`, `OAI.MUB6.Certificate.MixedSemantics.sourceA261`, `OAI.MUB6.Certificate.MixedSemantics.sourceA2611`, `OAI.MUB6.Certificate.MixedSemantics.sourceA2612` and 5228 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_Certificate_MixedTargetBasic`, `MutuallyUnbiased_MixedSemantics_Sources0`, `MutuallyUnbiased_MixedSemantics_Sources1`, `MutuallyUnbiased_MixedSemantics_Sources10`, `MutuallyUnbiased_MixedSemantics_Sources11`, `MutuallyUnbiased_MixedSemantics_Sources12`, `MutuallyUnbiased_MixedSemantics_Sources13`, `MutuallyUnbiased_MixedSemantics_Sources14`, `MutuallyUnbiased_MixedSemantics_Sources15`, `MutuallyUnbiased_MixedSemantics_Sources16`, `MutuallyUnbiased_MixedSemantics_Sources17`, `MutuallyUnbiased_MixedSemantics_Sources18`, `MutuallyUnbiased_MixedSemantics_Sources19`, `MutuallyUnbiased_MixedSemantics_Sources2`, `MutuallyUnbiased_MixedSemantics_Sources20`, `MutuallyUnbiased_MixedSemantics_Sources21`, `MutuallyUnbiased_MixedSemantics_Sources22`, `MutuallyUnbiased_MixedSemantics_Sources23`, `MutuallyUnbiased_MixedSemantics_Sources24`, `MutuallyUnbiased_MixedSemantics_Sources25`, `MutuallyUnbiased_MixedSemantics_Sources26`, `MutuallyUnbiased_MixedSemantics_Sources27`, `MutuallyUnbiased_MixedSemantics_Sources28`, `MutuallyUnbiased_MixedSemantics_Sources29`, `MutuallyUnbiased_MixedSemantics_Sources3`, `MutuallyUnbiased_MixedSemantics_Sources30`, `MutuallyUnbiased_MixedSemantics_Sources31`, `MutuallyUnbiased_MixedSemantics_Sources32`, `MutuallyUnbiased_MixedSemantics_Sources33`, `MutuallyUnbiased_MixedSemantics_Sources34`, `MutuallyUnbiased_MixedSemantics_Sources35`, `MutuallyUnbiased_MixedSemantics_Sources36`, `MutuallyUnbiased_MixedSemantics_Sources37`, `MutuallyUnbiased_MixedSemantics_Sources38`, `MutuallyUnbiased_MixedSemantics_Sources39`, `MutuallyUnbiased_MixedSemantics_Sources4`, `MutuallyUnbiased_MixedSemantics_Sources40`, `MutuallyUnbiased_MixedSemantics_Sources41`, `MutuallyUnbiased_MixedSemantics_Sources42`, `MutuallyUnbiased_MixedSemantics_Sources43`, `MutuallyUnbiased_MixedSemantics_Sources44`, `MutuallyUnbiased_MixedSemantics_Sources45`, `MutuallyUnbiased_MixedSemantics_Sources46`, `MutuallyUnbiased_MixedSemantics_Sources47`, `MutuallyUnbiased_MixedSemantics_Sources48`, `MutuallyUnbiased_MixedSemantics_Sources49`, `MutuallyUnbiased_MixedSemantics_Sources5`, `MutuallyUnbiased_MixedSemantics_Sources50`, `MutuallyUnbiased_MixedSemantics_Sources51`, `MutuallyUnbiased_MixedSemantics_Sources52`, `MutuallyUnbiased_MixedSemantics_Sources53`, `MutuallyUnbiased_MixedSemantics_Sources54`, `MutuallyUnbiased_MixedSemantics_Sources55`, `MutuallyUnbiased_MixedSemantics_Sources56`, `MutuallyUnbiased_MixedSemantics_Sources57`, `MutuallyUnbiased_MixedSemantics_Sources58`, `MutuallyUnbiased_MixedSemantics_Sources59`, `MutuallyUnbiased_MixedSemantics_Sources6`, `MutuallyUnbiased_MixedSemantics_Sources60`, `MutuallyUnbiased_MixedSemantics_Sources61`, `MutuallyUnbiased_MixedSemantics_Sources62`, `MutuallyUnbiased_MixedSemantics_Sources63`, `MutuallyUnbiased_MixedSemantics_Sources64`, `MutuallyUnbiased_MixedSemantics_Sources65`, `MutuallyUnbiased_MixedSemantics_Sources66`, `MutuallyUnbiased_MixedSemantics_Sources67`, `MutuallyUnbiased_MixedSemantics_Sources68`, `MutuallyUnbiased_MixedSemantics_Sources69`, `MutuallyUnbiased_MixedSemantics_Sources7`, `MutuallyUnbiased_MixedSemantics_Sources70`, `MutuallyUnbiased_MixedSemantics_Sources71`, `MutuallyUnbiased_MixedSemantics_Sources72`, `MutuallyUnbiased_MixedSemantics_Sources73`, `MutuallyUnbiased_MixedSemantics_Sources74`, `MutuallyUnbiased_MixedSemantics_Sources75`, `MutuallyUnbiased_MixedSemantics_Sources76`, `MutuallyUnbiased_MixedSemantics_Sources77`, `MutuallyUnbiased_MixedSemantics_Sources78`, `MutuallyUnbiased_MixedSemantics_Sources79`, `MutuallyUnbiased_MixedSemantics_Sources8`, `MutuallyUnbiased_MixedSemantics_Sources80`, `MutuallyUnbiased_MixedSemantics_Sources81`, `MutuallyUnbiased_MixedSemantics_Sources82`, `MutuallyUnbiased_MixedSemantics_Sources83`, `MutuallyUnbiased_MixedSemantics_Sources84`, `MutuallyUnbiased_MixedSemantics_Sources85`, `MutuallyUnbiased_MixedSemantics_Sources86`, `MutuallyUnbiased_MixedSemantics_Sources9`, `MutuallyUnbiased_PairMerge_Block0`, `MutuallyUnbiased_PairMerge_Block3`, `MutuallyUnbiased_PairMerge_Block4`, `MutuallyUnbiased_PairMerge_Block5`, `MutuallyUnbiased_PairMerge_Block6`, `MutuallyUnbiased_PairSemantics_Values0`.
--
--   **Imports.** It imports the published bundle `Def_MUBSix`; the bundles `OAIQ106D000`, `OAIQ106D002` and `OAIQ106D034` of this split.
--
--   **Imported by** (directly, in this split): the statement `OAI.MUB6.Certificate.PairSemantics.sound0`; the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1161`, `OAI.MUB6.Certificate.MixedSemantics.sound1162`, `OAI.MUB6.Certificate.MixedSemantics.sound1163`, `OAI.MUB6.Certificate.MixedSemantics.sound1164`, `OAI.MUB6.Certificate.MixedSemantics.sound1165`, `OAI.MUB6.Certificate.MixedSemantics.sound1166`, `OAI.MUB6.Certificate.MixedSemantics.sound1168`, `OAI.MUB6.Certificate.MixedSemantics.sound1170`, `OAI.MUB6.Certificate.MixedSemantics.sound1172`, `OAI.MUB6.Certificate.MixedSemantics.sound1173`, `OAI.MUB6.Certificate.MixedSemantics.sound1175`, `OAI.MUB6.Certificate.MixedSemantics.sound1265`, `OAI.MUB6.Certificate.MixedSemantics.sound1266`, `OAI.MUB6.Certificate.MixedSemantics.sound1267`, `OAI.MUB6.Certificate.MixedSemantics.sound1271`, `OAI.MUB6.Certificate.MixedSemantics.sound1298`, `OAI.MUB6.Certificate.MixedSemantics.sound1299`, `OAI.MUB6.Certificate.MixedSemantics.sound1301`, `OAI.MUB6.Certificate.MixedSemantics.sound1339`, `OAI.MUB6.Certificate.MixedSemantics.sound1340`, `OAI.MUB6.Certificate.MixedSemantics.sound1341`, `OAI.MUB6.Certificate.MixedSemantics.sound1342`, `OAI.MUB6.Certificate.MixedSemantics.sound1343`, `OAI.MUB6.Certificate.MixedSemantics.sound1344`, `OAI.MUB6.Certificate.MixedSemantics.sound1346`, `OAI.MUB6.Certificate.MixedSemantics.sound1395`, `OAI.MUB6.Certificate.MixedSemantics.sound1396`, `OAI.MUB6.Certificate.MixedSemantics.sound1397`, `OAI.MUB6.Certificate.MixedSemantics.sound1399`, `OAI.MUB6.Certificate.MixedSemantics.sound1401`, `OAI.MUB6.Certificate.MixedSemantics.sound1409`, `OAI.MUB6.Certificate.MixedSemantics.sound1410`, `OAI.MUB6.Certificate.MixedSemantics.sound1411`, `OAI.MUB6.Certificate.MixedSemantics.sound1412`, `OAI.MUB6.Certificate.MixedSemantics.sound1413`, `OAI.MUB6.Certificate.MixedSemantics.sound1414`, `OAI.MUB6.Certificate.MixedSemantics.sound1416`, `OAI.MUB6.Certificate.MixedSemantics.sound1417`, `OAI.MUB6.Certificate.MixedSemantics.sound1427`, `OAI.MUB6.Certificate.MixedSemantics.sound1441`, `OAI.MUB6.Certificate.MixedSemantics.sound1443`, `OAI.MUB6.Certificate.MixedSemantics.sound1451`, `OAI.MUB6.Certificate.MixedSemantics.sound1475`, `OAI.MUB6.Certificate.MixedSemantics.sound1477`, `OAI.MUB6.Certificate.MixedSemantics.sound1478`, `OAI.MUB6.Certificate.MixedSemantics.sound1479`, `OAI.MUB6.Certificate.MixedSemantics.sound1480`, `OAI.MUB6.Certificate.MixedSemantics.sound171`, `OAI.MUB6.Certificate.MixedSemantics.sound174`, `OAI.MUB6.Certificate.MixedSemantics.sound206`, `OAI.MUB6.Certificate.MixedSemantics.sound207`, `OAI.MUB6.Certificate.MixedSemantics.sound2357`, `OAI.MUB6.Certificate.MixedSemantics.sound2358`, `OAI.MUB6.Certificate.MixedSemantics.sound2359`, `OAI.MUB6.Certificate.MixedSemantics.sound2527`, `OAI.MUB6.Certificate.MixedSemantics.sound2530`, `OAI.MUB6.Certificate.MixedSemantics.sound2531`, `OAI.MUB6.Certificate.MixedSemantics.sound2532`, `OAI.MUB6.Certificate.MixedSemantics.sound2570`, `OAI.MUB6.Certificate.MixedSemantics.sound2572`, `OAI.MUB6.Certificate.MixedSemantics.sound2574`, `OAI.MUB6.Certificate.MixedSemantics.sound2576`, `OAI.MUB6.Certificate.MixedSemantics.sound2593`, `OAI.MUB6.Certificate.MixedSemantics.sound2594`, `OAI.MUB6.Certificate.MixedSemantics.sound2595`, `OAI.MUB6.Certificate.MixedSemantics.sound2596`, `OAI.MUB6.Certificate.MixedSemantics.sound2598`, `OAI.MUB6.Certificate.MixedSemantics.sound2599`, `OAI.MUB6.Certificate.MixedSemantics.sound2601`, `OAI.MUB6.Certificate.MixedSemantics.sound2636`, `OAI.MUB6.Certificate.MixedSemantics.sound2637`, `OAI.MUB6.Certificate.MixedSemantics.sound2638`, `OAI.MUB6.Certificate.MixedSemantics.sound2640`, `OAI.MUB6.Certificate.MixedSemantics.sound2753`, `OAI.MUB6.Certificate.MixedSemantics.sound2766`, `OAI.MUB6.Certificate.MixedSemantics.sound2828`, `OAI.MUB6.Certificate.MixedSemantics.sound2904`, `OAI.MUB6.Certificate.MixedSemantics.sound293`, `OAI.MUB6.Certificate.MixedSemantics.sound2936`, `OAI.MUB6.Certificate.MixedSemantics.sound2937`, `OAI.MUB6.Certificate.MixedSemantics.sound2939`, `OAI.MUB6.Certificate.MixedSemantics.sound294`, `OAI.MUB6.Certificate.MixedSemantics.sound2941`, `OAI.MUB6.Certificate.MixedSemantics.sound2943`, `OAI.MUB6.Certificate.MixedSemantics.sound2957`, `OAI.MUB6.Certificate.MixedSemantics.sound2958`, `OAI.MUB6.Certificate.MixedSemantics.sound2959`, `OAI.MUB6.Certificate.MixedSemantics.sound2960`, `OAI.MUB6.Certificate.MixedSemantics.sound2961`, `OAI.MUB6.Certificate.MixedSemantics.sound2963`, `OAI.MUB6.Certificate.MixedSemantics.sound2965`, `OAI.MUB6.Certificate.MixedSemantics.sound2966`, `OAI.MUB6.Certificate.MixedSemantics.sound2968`, `OAI.MUB6.Certificate.MixedSemantics.sound2969`, `OAI.MUB6.Certificate.MixedSemantics.sound2986`, `OAI.MUB6.Certificate.MixedSemantics.sound2987`, `OAI.MUB6.Certificate.MixedSemantics.sound2988`, `OAI.MUB6.Certificate.MixedSemantics.sound2990`, `OAI.MUB6.Certificate.MixedSemantics.sound2996`, `OAI.MUB6.Certificate.MixedSemantics.sound2997`, `OAI.MUB6.Certificate.MixedSemantics.sound2998`, `OAI.MUB6.Certificate.MixedSemantics.sound3003`, `OAI.MUB6.Certificate.MixedSemantics.sound3005`, `OAI.MUB6.Certificate.MixedSemantics.sound3082`, `OAI.MUB6.Certificate.MixedSemantics.sound3087`, `OAI.MUB6.Certificate.MixedSemantics.sound3088`, `OAI.MUB6.Certificate.MixedSemantics.sound3089`, `OAI.MUB6.Certificate.MixedSemantics.sound3090`, `OAI.MUB6.Certificate.MixedSemantics.sound3093`, `OAI.MUB6.Certificate.MixedSemantics.sound3094`, `OAI.MUB6.Certificate.MixedSemantics.sound3099`, `OAI.MUB6.Certificate.MixedSemantics.sound3100`, `OAI.MUB6.Certificate.MixedSemantics.sound3101`, `OAI.MUB6.Certificate.MixedSemantics.sound3102`, `OAI.MUB6.Certificate.MixedSemantics.sound3106`, `OAI.MUB6.Certificate.MixedSemantics.sound3109`, `OAI.MUB6.Certificate.MixedSemantics.sound3110`, `OAI.MUB6.Certificate.MixedSemantics.sound3116`, `OAI.MUB6.Certificate.MixedSemantics.sound3120`, `OAI.MUB6.Certificate.MixedSemantics.sound3143`, `OAI.MUB6.Certificate.MixedSemantics.sound3144`, `OAI.MUB6.Certificate.MixedSemantics.sound3178`, `OAI.MUB6.Certificate.MixedSemantics.sound3184`, `OAI.MUB6.Certificate.MixedSemantics.sound3185`, `OAI.MUB6.Certificate.MixedSemantics.sound3190`, `OAI.MUB6.Certificate.MixedSemantics.sound3191`, `OAI.MUB6.Certificate.MixedSemantics.sound3203`, `OAI.MUB6.Certificate.MixedSemantics.sound3204`, `OAI.MUB6.Certificate.MixedSemantics.sound3205`, `OAI.MUB6.Certificate.MixedSemantics.sound3206`, `OAI.MUB6.Certificate.MixedSemantics.sound3207`, `OAI.MUB6.Certificate.MixedSemantics.sound3209`, `OAI.MUB6.Certificate.MixedSemantics.sound3210`, `OAI.MUB6.Certificate.MixedSemantics.sound3211`, `OAI.MUB6.Certificate.MixedSemantics.sound3223`, `OAI.MUB6.Certificate.MixedSemantics.sound3226`, `OAI.MUB6.Certificate.MixedSemantics.sound3227`, `OAI.MUB6.Certificate.MixedSemantics.sound370`, `OAI.MUB6.Certificate.MixedSemantics.sound371`, `OAI.MUB6.Certificate.MixedSemantics.sound3711`, `OAI.MUB6.Certificate.MixedSemantics.sound3726`, `OAI.MUB6.Certificate.MixedSemantics.sound3727`, `OAI.MUB6.Certificate.MixedSemantics.sound3734`, `OAI.MUB6.Certificate.MixedSemantics.sound3735`, `OAI.MUB6.Certificate.MixedSemantics.sound3736`, `OAI.MUB6.Certificate.MixedSemantics.sound3737`, `OAI.MUB6.Certificate.MixedSemantics.sound3738`, `OAI.MUB6.Certificate.MixedSemantics.sound3739`, `OAI.MUB6.Certificate.MixedSemantics.sound3818`, `OAI.MUB6.Certificate.MixedSemantics.sound3821`, `OAI.MUB6.Certificate.MixedSemantics.sound3822`, `OAI.MUB6.Certificate.MixedSemantics.sound3823`, `OAI.MUB6.Certificate.MixedSemantics.sound3824`, `OAI.MUB6.Certificate.MixedSemantics.sound3829`, `OAI.MUB6.Certificate.MixedSemantics.sound3831`, `OAI.MUB6.Certificate.MixedSemantics.sound3847`, `OAI.MUB6.Certificate.MixedSemantics.sound3851`, `OAI.MUB6.Certificate.MixedSemantics.sound3852`, `OAI.MUB6.Certificate.MixedSemantics.sound3853`, `OAI.MUB6.Certificate.MixedSemantics.sound3855`, `OAI.MUB6.Certificate.MixedSemantics.sound3856`, `OAI.MUB6.Certificate.MixedSemantics.sound3858`, `OAI.MUB6.Certificate.MixedSemantics.sound3882`, `OAI.MUB6.Certificate.MixedSemantics.sound3883`, `OAI.MUB6.Certificate.MixedSemantics.sound3887`, `OAI.MUB6.Certificate.MixedSemantics.sound3888`, `OAI.MUB6.Certificate.MixedSemantics.sound3925`, `OAI.MUB6.Certificate.MixedSemantics.sound3931`, `OAI.MUB6.Certificate.MixedSemantics.sound3933`, `OAI.MUB6.Certificate.MixedSemantics.sound3936`, `OAI.MUB6.Certificate.MixedSemantics.sound3937`, `OAI.MUB6.Certificate.MixedSemantics.sound3965`, `OAI.MUB6.Certificate.MixedSemantics.sound3966`, `OAI.MUB6.Certificate.MixedSemantics.sound3967`, `OAI.MUB6.Certificate.MixedSemantics.sound3977`, `OAI.MUB6.Certificate.MixedSemantics.sound3980`, `OAI.MUB6.Certificate.MixedSemantics.sound3982`, `OAI.MUB6.Certificate.MixedSemantics.sound3984`, `OAI.MUB6.Certificate.MixedSemantics.sound3987`, `OAI.MUB6.Certificate.MixedSemantics.sound3992`, `OAI.MUB6.Certificate.MixedSemantics.sound3993`, `OAI.MUB6.Certificate.MixedSemantics.sound3994`, `OAI.MUB6.Certificate.MixedSemantics.sound3997`, `OAI.MUB6.Certificate.MixedSemantics.sound3998`, `OAI.MUB6.Certificate.MixedSemantics.sound4002`, `OAI.MUB6.Certificate.MixedSemantics.sound4003`, `OAI.MUB6.Certificate.MixedSemantics.sound4012`, `OAI.MUB6.Certificate.MixedSemantics.sound4013`, `OAI.MUB6.Certificate.MixedSemantics.sound4014`, `OAI.MUB6.Certificate.MixedSemantics.sound4023`, `OAI.MUB6.Certificate.MixedSemantics.sound4026`, `OAI.MUB6.Certificate.MixedSemantics.sound4027`, `OAI.MUB6.Certificate.MixedSemantics.sound4029`, `OAI.MUB6.Certificate.MixedSemantics.sound4031`, `OAI.MUB6.Certificate.MixedSemantics.sound4032`, `OAI.MUB6.Certificate.MixedSemantics.sound4033`, `OAI.MUB6.Certificate.MixedSemantics.sound4039`, `OAI.MUB6.Certificate.MixedSemantics.sound4050`, `OAI.MUB6.Certificate.MixedSemantics.sound4053`, `OAI.MUB6.Certificate.MixedSemantics.sound436`, `OAI.MUB6.Certificate.MixedSemantics.sound454`, `OAI.MUB6.Certificate.MixedSemantics.sound455`, `OAI.MUB6.Certificate.MixedSemantics.sound4623`, `OAI.MUB6.Certificate.MixedSemantics.sound4625`, `OAI.MUB6.Certificate.MixedSemantics.sound479`, `OAI.MUB6.Certificate.MixedSemantics.sound511`, `OAI.MUB6.Certificate.MixedSemantics.sound514`, `OAI.MUB6.Certificate.MixedSemantics.sound5176`, `OAI.MUB6.Certificate.MixedSemantics.sound5177`, `OAI.MUB6.Certificate.MixedSemantics.sound521`, `OAI.MUB6.Certificate.MixedSemantics.sound5293`, `OAI.MUB6.Certificate.MixedSemantics.sound5294`, `OAI.MUB6.Certificate.MixedSemantics.sound5296`, `OAI.MUB6.Certificate.MixedSemantics.sound5306`, `OAI.MUB6.Certificate.MixedSemantics.sound5310`, `OAI.MUB6.Certificate.MixedSemantics.sound5415`, `OAI.MUB6.Certificate.MixedSemantics.sound5443`, `OAI.MUB6.Certificate.MixedSemantics.sound5452`, `OAI.MUB6.Certificate.MixedSemantics.sound5453`, `OAI.MUB6.Certificate.MixedSemantics.sound5464`, `OAI.MUB6.Certificate.MixedSemantics.sound5492`, `OAI.MUB6.Certificate.MixedSemantics.sound5498`, `OAI.MUB6.Certificate.MixedSemantics.sound644`, `OAI.MUB6.Certificate.MixedSemantics.sound645`, `OAI.MUB6.Certificate.MixedSemantics.sourceEq1094`, `OAI.MUB6.Certificate.MixedSemantics.sourceEq1095`, `OAI.MUB6.Certificate.MixedSemantics.sourceEq1100`, `OAI.MUB6.Certificate.MixedSemantics.sourceEq1104`, `OAI.MUB6.Certificate.MixedSourceBridge.allRowsSound`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound0`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound1`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound10`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound100`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound101`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound102`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound103`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound104`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound105`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound106`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound107`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound108`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound109`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound11`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound110`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound111`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound112`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound113`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound114`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound115`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound116`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound117`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound118`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound119`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound12`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound120`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound121`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound122`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound123`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound124`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound125`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound126`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound127`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound128`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound129`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound13`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound130`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound131`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound132`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound133`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound134`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound135`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound14`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound15`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound16`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound17`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound18`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound19`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound2`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound20`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound21`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound22`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound23`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound24`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound25`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound26`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound27`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound28`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound29`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound3`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound30`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound31`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound32`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound33`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound34`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound35`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound36`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound37`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound38`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound39`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound4`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound40`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound41`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound42`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound43`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound44`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound45`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound46`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound47`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound48`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound49`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound50`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound51`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound52`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound53`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound54`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound55`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound56`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound57`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound58`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound59`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound6`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound60`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound61`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound62`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound63`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound64`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound65`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound66`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound67`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound68`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound69`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound7`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound70`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound71`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound72`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound73`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound74`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound75`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound76`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound77`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound78`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound79`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound8`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound80`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound81`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound82`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound83`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound84`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound85`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound86`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound87`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound88`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound89`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound9`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound90`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound91`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound92`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound93`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound94`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound95`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound96`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound97`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound98`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound99`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1098`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1423`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero15`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1780`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero539`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero733`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero769`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero863`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero925`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound0`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound10`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound100`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1000`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1001`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1003`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1004`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1005`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1006`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1007`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1008`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1009`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound101`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1010`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1012`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1013`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1014`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1019`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1020`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1021`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1022`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1023`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1030`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1031`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1033`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1034`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1035`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1071`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound109`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1093`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1094`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1095`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1096`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1097`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound11`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound110`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1103`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1108`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1109`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound111`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1110`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1111`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1114`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1115`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1120`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1121`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1123`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1124`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound113`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1130`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1131`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound114`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1158`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1159`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound116`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1165`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1166`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1167`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1169`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound117`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1170`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1177`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1178`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1179`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1191`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1194`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1195`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1197`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1198`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1205`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1227`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1231`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1232`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1233`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound126`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1261`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1262`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1263`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1264`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1266`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1267`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1268`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1269`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound127`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1271`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1272`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1278`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1279`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound129`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1293`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1294`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound13`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound130`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1300`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1301`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1303`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1309`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1310`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1311`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1312`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1317`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1318`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1321`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1324`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1326`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1335`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1340`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound137`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound138`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound14`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound140`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1409`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound141`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1410`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1411`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1412`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1414`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1417`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1418`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1420`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1421`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1422`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1428`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1429`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound143`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1430`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1433`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1435`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1436`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1437`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1438`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1441`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1442`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound145`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1465`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1469`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1470`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1471`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1472`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1477`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1478`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1480`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1483`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1484`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1490`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1493`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1505`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1507`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1508`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound151`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1510`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1511`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1513`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1514`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1516`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1517`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound152`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1521`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound153`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1536`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1539`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1559`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1560`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1561`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1567`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1568`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1569`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1571`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1575`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1584`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1587`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1589`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1593`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1595`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1598`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1599`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound16`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound163`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1648`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1649`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1650`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1651`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1652`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1653`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1655`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1656`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1657`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1662`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1668`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1669`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1672`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1673`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1674`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1679`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1684`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1685`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1686`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1687`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound17`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1702`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1703`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1708`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1709`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1710`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1715`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1716`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1717`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1723`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1734`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1738`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1739`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1740`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1741`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1743`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1744`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1781`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1782`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1783`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1785`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1786`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1787`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1788`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1789`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1795`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1796`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1797`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound18`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1811`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1815`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1816`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1817`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1822`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1825`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1826`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1828`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1829`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1831`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1833`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1835`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1838`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1839`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound184`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1840`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1844`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1845`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1846`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1847`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1848`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1849`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1853`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1854`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1856`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1858`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1859`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1864`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1865`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1866`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1871`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1872`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1873`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1874`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1877`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound188`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1880`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1881`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1882`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound19`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1904`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1905`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1906`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1907`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1908`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1909`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1910`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1911`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1912`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1914`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1915`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1916`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1917`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1924`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1925`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1935`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1937`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1938`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1941`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1942`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1944`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1945`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1948`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1949`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1950`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1952`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1953`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1954`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1956`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1957`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1958`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1960`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1963`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1964`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1965`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1968`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1969`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1970`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1971`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1972`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1976`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1977`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound198`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1980`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1983`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1984`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1985`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1988`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1989`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound199`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1990`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1991`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1993`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1994`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1995`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1998`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1999`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound20`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2002`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2003`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2004`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2005`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2006`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2010`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2011`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2014`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2015`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2016`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2017`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2018`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2019`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2021`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2022`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2023`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2033`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2034`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2035`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2036`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2037`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2038`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2039`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2040`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2041`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2045`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2046`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2047`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2048`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2049`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2050`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2051`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2052`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2056`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2059`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2060`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2061`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2062`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2063`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2064`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2065`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2066`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2067`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2068`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2069`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound207`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2070`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2071`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2073`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2075`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2076`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2077`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2078`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2080`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2082`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2084`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2085`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2086`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2087`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2088`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2089`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2090`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2091`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2092`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2093`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2094`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2096`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2097`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2099`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound21`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2100`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2102`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2103`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2105`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2107`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2108`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2109`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2110`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2126`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound213`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound214`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound22`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound226`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound23`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound236`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound24`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound244`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound245`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound25`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound255`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound267`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound268`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound269`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound28`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound281`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound282`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound286`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound287`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound29`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound296`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound3`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound301`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound310`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound311`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound319`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound327`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound328`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound335`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound339`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound340`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound341`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound342`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound344`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound345`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound349`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound35`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound353`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound354`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound356`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound357`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound358`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound359`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound365`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound366`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound367`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound368`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound369`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound370`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound371`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound372`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound380`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound388`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound391`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound392`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound395`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound396`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound4`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound404`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound411`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound412`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound413`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound417`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound418`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound419`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound426`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound428`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound438`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound444`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound445`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound446`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound448`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound452`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound453`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound454`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound456`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound462`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound463`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound470`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound473`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound474`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound482`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound483`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound484`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound485`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound487`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound488`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound489`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound497`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound498`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound499`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound5`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound500`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound501`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound503`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound504`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound512`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound514`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound515`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound516`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound518`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound519`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound520`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound521`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound522`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound523`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound525`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound526`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound531`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound532`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound533`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound534`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound536`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound537`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound538`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound540`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound542`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound543`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound545`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound546`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound547`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound548`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound551`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound552`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound553`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound554`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound555`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound558`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound564`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound565`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound566`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound567`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound568`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound571`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound572`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound579`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound58`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound580`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound581`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound582`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound584`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound585`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound587`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound588`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound589`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound59`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound590`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound599`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound6`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound600`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound601`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound612`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound613`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound620`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound621`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound628`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound629`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound630`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound631`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound632`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound633`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound635`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound642`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound644`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound649`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound656`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound657`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound658`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound659`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound660`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound663`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound664`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound666`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound667`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound675`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound682`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound686`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound688`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound693`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound700`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound708`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound710`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound711`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound712`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound717`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound718`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound719`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound721`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound723`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound726`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound728`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound730`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound731`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound732`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound734`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound735`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound736`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound737`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound738`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound739`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound740`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound741`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound742`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound743`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound744`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound745`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound746`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound749`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound750`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound751`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound757`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound758`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound759`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound76`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound770`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound774`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound779`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound780`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound783`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound786`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound787`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound788`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound790`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound791`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound792`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound793`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound794`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound795`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound796`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound797`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound798`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound799`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound8`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound800`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound801`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound802`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound804`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound805`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound813`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound814`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound815`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound816`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound817`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound818`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound821`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound823`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound833`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound834`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound840`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound841`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound842`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound843`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound844`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound845`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound847`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound848`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound849`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound851`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound852`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound853`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound854`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound855`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound856`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound857`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound858`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound859`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound864`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound865`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound866`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound867`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound868`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound871`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound872`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound877`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound878`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound881`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound882`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound883`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound884`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound885`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound886`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound888`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound890`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound892`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound894`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound896`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound897`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound898`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound899`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound9`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound900`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound901`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound903`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound905`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound906`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound908`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound909`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound91`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound910`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound911`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound912`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound914`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound915`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound916`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound918`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound92`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound920`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound921`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound922`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound923`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound924`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound926`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound927`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound928`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound93`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound930`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound931`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound932`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound933`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound934`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound935`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound936`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound938`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound939`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound94`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound940`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound941`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound942`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound943`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound944`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound945`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound946`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound947`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound949`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound950`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound951`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound952`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound954`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound955`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound956`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound958`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound960`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound961`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound963`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound964`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound965`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound966`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound967`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound968`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound969`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound97`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound970`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound971`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound972`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound973`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound974`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound975`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound976`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound977`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound978`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound979`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound98`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound980`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound982`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound983`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound984`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound986`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound988`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound989`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound990`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound991`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound992`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound993`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound994`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound995`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound997`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound998`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound999`, `OAI.MUB6.Certificate.MixedTargetSemantics.originalReductionEval`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval106`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1074`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1076`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval109`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1105`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval116`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval117`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1192`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1194`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval12`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval120`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1210`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval124`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1254`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval130`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1315`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval133`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval134`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval141`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval143`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1435`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1436`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval145`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval146`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval147`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval149`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval155`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1553`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1554`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval159`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval164`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval165`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval167`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1674`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval173`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval174`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1777`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1793`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval18`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval181`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval182`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval185`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1852`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1853`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1882`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1913`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1914`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1917`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval202`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval203`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval207`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval21`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval214`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval215`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval218`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval220`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval224`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval225`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval226`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval229`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval231`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval234`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval235`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval242`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval243`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval245`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval249`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval255`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval257`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval258`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval263`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval270`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval271`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval273`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval278`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval280`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval285`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval286`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval287`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval292`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval296`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval301`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval308`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval310`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval323`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval325`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval331`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval332`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval334`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval335`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval343`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval344`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval348`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval353`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval358`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval359`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval366`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval368`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval37`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval370`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval371`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval372`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval373`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval377`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval380`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval383`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval389`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval39`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval391`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval394`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval401`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval403`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval408`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval41`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval413`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval414`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval444`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval46`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval475`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval476`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval477`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval52`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval54`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval56`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval6`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval63`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval69`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval715`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval73`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval74`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval77`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval79`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval8`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval83`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval835`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval86`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval91`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval953`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval955`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval957`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval99`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval113`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval119`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval147`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval150`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval208`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval21`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval215`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval216`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval220`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval222`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval271`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval359`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval360`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval362`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval373`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval375`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval384`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval44`, `OAI.MUB6.Certificate.PairSemantics.sound0`, `OAI.MUB6.Certificate.PairSemantics.sound5`, `OAI.MUB6.Certificate.PairTargetSemantics.certificate_zero1`, `OAI.MUB6.Certificate.PairTargetSemantics.expandedIdentity0`, `OAI.MUB6.Certificate.PairTargetSemantics.partition12`, `OAI.MUB6.Certificate.PairTargetSemantics.partition14`, `OAI.MUB6.Certificate.PairTargetSemantics.partition16`, `OAI.MUB6.Certificate.PairTargetSemantics.partition19`, `OAI.MUB6.Certificate.PairTargetSemantics.partition24`, `OAI.MUB6.Certificate.PairTargetSemantics.partition25`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm1`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm10`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm11`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm13`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm15`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm17`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm18`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm20`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm21`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm23`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm26`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm6`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm7`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm8`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm9`, `OAI.MUB6.exact_dichotomy`, `OAI.MUB6.family_size_le_five` and `OAI.MUB6.fourier_and_family_bound`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106D000
import Definitions.Def_OAIQ106D002
import Definitions.Def_OAIQ106D034

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_MixedTargetBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalLess (a b : OriginalKey) : Bool :=
  match a, b with
  | .inl i, .inl j => decide (i < j)
  | .inl _, .inr _ => true
  | .inr _, .inl _ => false
  | .inr i, .inr j => decide (i < j)

def masterLess (a b : Master) : Bool :=
  match a, b with
  | .inl i, .inl j => decide (i < j)
  | .inl _, .inr _ => true
  | .inr _, .inl _ => false
  | .inr i, .inr j => decide (i < j)

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB0 : Charge := ![0, 0, 0, 0, 2, -2]
def sourceC0 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceB1 : Charge := ![0, 0, 0, 1, 1, -2]
def sourceC1 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceB2 : Charge := ![0, 0, 0, 1, 1, -2]
def sourceC2 : Charge := ![2, 0, 0, -1, -1, 0]

def sourceA3 : Charge := ![0, 0, 0, 1, 1, -2]
def sourceB3 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC3 : Charge := ![-2, 0, 0, 0, 0, 2]

def sourceA4 : Charge := ![-2, 0, 0, 0, 0, 2]
def sourceB4 : Charge := ![1, -1, 0, 0, 1, -1]
def sourceC4 : Charge := ![1, 1, 0, 0, -1, -1]

def sourceA5 : Charge := ![-2, 0, 0, 0, 0, 2]
def sourceB5 : Charge := ![1, -1, 0, 0, 1, -1]
def sourceC5 : Charge := ![1, 1, 0, 0, -1, -1]

def sourceA6 : Charge := ![-2, 0, 0, 0, 0, 2]
def sourceB6 : Charge := ![1, -1, 0, 0, 1, -1]
def sourceC6 : Charge := ![1, 1, 0, 0, -1, -1]

def sourceA7 : Charge := ![1, -1, 0, 0, 1, -1]
def sourceB7 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC7 : Charge := ![-2, 0, 0, 0, 0, 2]

def sourceA8 : Charge := ![1, -1, 0, 0, 1, -1]
def sourceB8 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC8 : Charge := ![-2, 0, 0, 0, 0, 2]

def sourceA9 : Charge := ![-2, 0, 0, 0, 0, 2]
def sourceB9 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC9 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceB10 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceC10 : Charge := ![-2, 0, 0, 0, 0, 2]
def sourceB11 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC11 : Charge := ![0, 0, 0, 0, 0, 0]
def sourceB12 : Charge := ![0, 0, 1, 1, -1, -1]
def sourceC12 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceB13 : Charge := ![0, 0, 1, 1, -1, -1]
def sourceC13 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceB14 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC14 : Charge := ![0, 0, 1, 1, -1, -1]
def sourceB15 : Charge := ![1, -1, 0, 0, -1, 1]
def sourceC15 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceB16 : Charge := ![1, -1, 0, 0, -1, 1]
def sourceC16 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceB17 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC17 : Charge := ![1, -1, 0, 0, -1, 1]
def sourceB18 : Charge := ![1, -1, 0, 1, -1, 0]
def sourceC18 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceB19 : Charge := ![1, -1, 0, 1, -1, 0]
def sourceC19 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceB20 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC20 : Charge := ![-2, 0, 0, 0, 1, 1]
def sourceB21 : Charge := ![1, 0, 0, 0, -2, 1]
def sourceC21 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceB22 : Charge := ![1, 0, 0, -1, 0, 0]
def sourceC22 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceB23 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceC23 : Charge := ![-2, 0, 0, 0, 1, 1]
def sourceB24 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC24 : Charge := ![2, -1, 0, 0, -1, 0]
def sourceB25 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC25 : Charge := ![0, 0, 0, 0, 0, 0]

def sourceA26 : Charge := ![-1, -1, 0, 0, 1, 1]
def sourceB26 : Charge := ![0, 0, 1, 1, -1, -1]
def sourceC26 : Charge := ![1, 1, -1, -1, 0, 0]

def sourceA27 : Charge := ![-1, -1, 0, 0, 1, 1]
def sourceB27 : Charge := ![0, 1, -1, 1, -1, 0]
def sourceC27 : Charge := ![1, 0, 1, -1, 0, -1]

def sourceA28 : Charge := ![-1, -1, 0, 0, 1, 1]
def sourceB28 : Charge := ![1, 0, 0, -1, 0, 0]
def sourceC28 : Charge := ![0, 1, 0, 1, -1, -1]

def sourceA29 : Charge := ![-1, -1, 0, 0, 1, 1]
def sourceB29 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC29 : Charge := ![0, 0, 0, 0, 0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA32 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB32 : Charge := ![0, 0, 0, 0, 3, -3]
def sourceC32 : Charge := ![3, 0, 0, 0, -3, 0]

def sourceA33 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB33 : Charge := ![0, 0, 0, 0, 3, -3]
def sourceC33 : Charge := ![3, 0, 0, 0, -3, 0]

def sourceA34 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB34 : Charge := ![0, 0, 0, 0, 3, -3]
def sourceC34 : Charge := ![3, 0, 0, 0, -3, 0]

def sourceA35 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB35 : Charge := ![0, 0, 0, 0, 3, -3]
def sourceC35 : Charge := ![3, 0, 0, 0, -3, 0]

def sourceA36 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB36 : Charge := ![0, 0, 0, 0, 3, -3]
def sourceC36 : Charge := ![3, 0, 0, 0, -3, 0]

def sourceA38 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB38 : Charge := ![0, 0, 0, 1, 2, -3]
def sourceC38 : Charge := ![3, 0, 0, -1, -2, 0]

def sourceA40 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB40 : Charge := ![0, 0, 0, 1, 2, -3]
def sourceC40 : Charge := ![3, 0, 0, -1, -2, 0]

def sourceA41 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB41 : Charge := ![0, 0, 0, 1, 2, -3]
def sourceC41 : Charge := ![3, 0, 0, -1, -2, 0]

def sourceA42 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB42 : Charge := ![0, 0, 0, 1, 2, -3]
def sourceC42 : Charge := ![3, 0, 0, -1, -2, 0]

def sourceA43 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB43 : Charge := ![0, 0, 0, 1, 2, -3]
def sourceC43 : Charge := ![3, 0, 0, -1, -2, 0]

def sourceA44 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB44 : Charge := ![0, 0, 0, 1, 2, -3]
def sourceC44 : Charge := ![3, 0, 0, -1, -2, 0]

def sourceA45 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB45 : Charge := ![0, 0, 0, 1, 2, -3]
def sourceC45 : Charge := ![3, 0, 0, -1, -2, 0]

def sourceA46 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB46 : Charge := ![0, 0, 0, 1, 2, -3]
def sourceC46 : Charge := ![3, 0, 0, -1, -2, 0]

def sourceA47 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB47 : Charge := ![0, 0, 0, 1, 2, -3]
def sourceC47 : Charge := ![3, 0, 0, -1, -2, 0]

def sourceA48 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB48 : Charge := ![0, 0, 0, 1, 2, -3]
def sourceC48 : Charge := ![3, 0, 0, -1, -2, 0]

def sourceA51 : Charge := ![0, 0, 0, 1, 2, -3]
def sourceB51 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceC51 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA52 : Charge := ![0, 0, 0, 1, 2, -3]
def sourceB52 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceC52 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA53 : Charge := ![0, 0, 0, 1, 2, -3]
def sourceB53 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceC53 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA54 : Charge := ![0, 0, 0, 1, 2, -3]
def sourceB54 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceC54 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA55 : Charge := ![0, 0, 0, 1, 2, -3]
def sourceB55 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceC55 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA59 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB59 : Charge := ![0, 0, 1, 1, 1, -3]
def sourceC59 : Charge := ![3, 0, -1, -1, -1, 0]

def sourceA60 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB60 : Charge := ![0, 0, 1, 1, 1, -3]
def sourceC60 : Charge := ![3, 0, -1, -1, -1, 0]

def sourceA61 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB61 : Charge := ![0, 0, 1, 1, 1, -3]
def sourceC61 : Charge := ![3, 0, -1, -1, -1, 0]

def sourceA62 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB62 : Charge := ![0, 0, 1, 1, 1, -3]
def sourceC62 : Charge := ![3, 0, -1, -1, -1, 0]

def sourceA63 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB63 : Charge := ![0, 0, 1, 1, 1, -3]
def sourceC63 : Charge := ![3, 0, -1, -1, -1, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA320 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceB320 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC320 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA321 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceB321 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC321 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA322 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceB322 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC322 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA323 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceB323 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC323 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA324 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceB324 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC324 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA325 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceB325 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC325 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA326 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceB326 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC326 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA327 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceB327 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC327 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA328 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceB328 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC328 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA329 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceB329 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC329 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA331 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB331 : Charge := ![1, -1, 0, 2, 0, -2]
def sourceC331 : Charge := ![2, 1, 0, -2, -1, 0]

def sourceA332 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB332 : Charge := ![1, -1, 0, 2, 0, -2]
def sourceC332 : Charge := ![2, 1, 0, -2, -1, 0]

def sourceA333 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB333 : Charge := ![1, -1, 0, 2, 0, -2]
def sourceC333 : Charge := ![2, 1, 0, -2, -1, 0]

def sourceA335 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB335 : Charge := ![1, -1, 0, 2, 0, -2]
def sourceC335 : Charge := ![2, 1, 0, -2, -1, 0]

def sourceA336 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB336 : Charge := ![1, -1, 0, 2, 0, -2]
def sourceC336 : Charge := ![2, 1, 0, -2, -1, 0]

def sourceA341 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB341 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC341 : Charge := ![1, -1, 0, 2, 0, -2]

def sourceA342 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB342 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC342 : Charge := ![1, -1, 0, 2, 0, -2]

def sourceA343 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB343 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC343 : Charge := ![1, -1, 0, 2, 0, -2]

def sourceA344 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB344 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC344 : Charge := ![1, -1, 0, 2, 0, -2]

def sourceA345 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB345 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC345 : Charge := ![1, -1, 0, 2, 0, -2]

def sourceA346 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB346 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC346 : Charge := ![1, -1, 0, 2, 0, -2]

def sourceA347 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB347 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC347 : Charge := ![1, -1, 0, 2, 0, -2]

def sourceA348 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB348 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC348 : Charge := ![1, -1, 0, 2, 0, -2]

def sourceA349 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB349 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC349 : Charge := ![1, -1, 0, 2, 0, -2]

def sourceA350 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB350 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC350 : Charge := ![1, -1, 0, 2, 0, -2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA353 : Charge := ![1, -1, 0, 2, 0, -2]
def sourceB353 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC353 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA354 : Charge := ![1, -1, 0, 2, 0, -2]
def sourceB354 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC354 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA355 : Charge := ![1, -1, 0, 2, 0, -2]
def sourceB355 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC355 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA356 : Charge := ![1, -1, 0, 2, 0, -2]
def sourceB356 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC356 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA357 : Charge := ![1, -1, 0, 2, 0, -2]
def sourceB357 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC357 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA361 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB361 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceC361 : Charge := ![2, 1, -1, -1, 0, -1]

def sourceA362 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB362 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceC362 : Charge := ![2, 1, -1, -1, 0, -1]

def sourceA363 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB363 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceC363 : Charge := ![2, 1, -1, -1, 0, -1]

def sourceA364 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB364 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceC364 : Charge := ![2, 1, -1, -1, 0, -1]

def sourceA365 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB365 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceC365 : Charge := ![2, 1, -1, -1, 0, -1]

def sourceA366 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB366 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceC366 : Charge := ![2, 1, -1, -1, 0, -1]

def sourceA367 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB367 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceC367 : Charge := ![2, 1, -1, -1, 0, -1]

def sourceA368 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB368 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceC368 : Charge := ![2, 1, -1, -1, 0, -1]

def sourceA369 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceB369 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC369 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA370 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceB370 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC370 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA371 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceB371 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC371 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA372 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceB372 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC372 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA373 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceB373 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC373 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA374 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceB374 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC374 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA375 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceB375 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC375 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA376 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceB376 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC376 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA377 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceB377 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC377 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA378 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceB378 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC378 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA381 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB381 : Charge := ![1, -1, 1, 1, 0, -2]
def sourceC381 : Charge := ![2, 1, -1, -1, -1, 0]

def sourceA382 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB382 : Charge := ![1, -1, 1, 1, 0, -2]
def sourceC382 : Charge := ![2, 1, -1, -1, -1, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA384 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB384 : Charge := ![1, -1, 1, 1, 0, -2]
def sourceC384 : Charge := ![2, 1, -1, -1, -1, 0]

def sourceA385 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB385 : Charge := ![1, -1, 1, 1, 0, -2]
def sourceC385 : Charge := ![2, 1, -1, -1, -1, 0]

def sourceA386 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB386 : Charge := ![1, -1, 1, 1, 0, -2]
def sourceC386 : Charge := ![2, 1, -1, -1, -1, 0]

def sourceA387 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB387 : Charge := ![1, -1, 1, 1, 0, -2]
def sourceC387 : Charge := ![2, 1, -1, -1, -1, 0]

def sourceA388 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB388 : Charge := ![1, -1, 1, 1, 0, -2]
def sourceC388 : Charge := ![2, 1, -1, -1, -1, 0]

def sourceA389 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB389 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC389 : Charge := ![1, -1, 1, 1, 0, -2]

def sourceA390 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB390 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC390 : Charge := ![1, -1, 1, 1, 0, -2]

def sourceA391 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB391 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC391 : Charge := ![1, -1, 1, 1, 0, -2]

def sourceA392 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB392 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC392 : Charge := ![1, -1, 1, 1, 0, -2]

def sourceA393 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB393 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC393 : Charge := ![1, -1, 1, 1, 0, -2]

def sourceA394 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB394 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC394 : Charge := ![1, -1, 1, 1, 0, -2]

def sourceA395 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB395 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC395 : Charge := ![1, -1, 1, 1, 0, -2]

def sourceA396 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB396 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC396 : Charge := ![1, -1, 1, 1, 0, -2]

def sourceA397 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB397 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC397 : Charge := ![1, -1, 1, 1, 0, -2]

def sourceA400 : Charge := ![1, -1, 1, 1, 0, -2]
def sourceB400 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC400 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA401 : Charge := ![1, -1, 1, 1, 0, -2]
def sourceB401 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC401 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA402 : Charge := ![1, -1, 1, 1, 0, -2]
def sourceB402 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC402 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA403 : Charge := ![1, -1, 1, 1, 0, -2]
def sourceB403 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC403 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA405 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB405 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceC405 : Charge := ![2, 0, 0, 0, -2, 0]

def sourceA406 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB406 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceC406 : Charge := ![2, 0, 0, 0, -2, 0]

def sourceA407 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB407 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC407 : Charge := ![1, 0, 0, 0, 1, -2]

def sourceA408 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB408 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC408 : Charge := ![1, 0, 0, 0, 1, -2]

def sourceA409 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceB409 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC409 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA410 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceB410 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC410 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA411 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceB411 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC411 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA412 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceB412 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC412 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA413 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceB413 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC413 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA414 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceB414 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC414 : Charge := ![-3, 0, 0, 0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA417 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB417 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceC417 : Charge := ![2, 0, 0, 0, -3, 1]

def sourceA418 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB418 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceC418 : Charge := ![2, 0, 0, 0, -3, 1]

def sourceA419 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB419 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceC419 : Charge := ![2, 0, 0, 0, -3, 1]

def sourceA420 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB420 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceC420 : Charge := ![2, 0, 0, 0, -3, 1]

def sourceA421 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB421 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceC421 : Charge := ![2, 0, 0, -1, 0, -1]

def sourceA422 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB422 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceC422 : Charge := ![2, 0, 0, -1, 0, -1]

def sourceA423 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB423 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC423 : Charge := ![1, 0, 0, 1, -1, -1]

def sourceA424 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB424 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC424 : Charge := ![1, 0, 0, 1, -1, -1]

def sourceA425 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceB425 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC425 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA426 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceB426 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC426 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA427 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceB427 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC427 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA428 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceB428 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC428 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA429 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceB429 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC429 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA430 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceB430 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC430 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA431 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceB431 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC431 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA432 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceB432 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC432 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA433 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB433 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceC433 : Charge := ![2, 0, 0, -1, -1, 0]

def sourceA434 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB434 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceC434 : Charge := ![2, 0, 0, -1, -1, 0]

def sourceA435 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB435 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC435 : Charge := ![1, 0, 0, 1, 0, -2]

def sourceA436 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB436 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC436 : Charge := ![1, 0, 0, 1, 0, -2]

def sourceA437 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceB437 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC437 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA438 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceB438 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC438 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA440 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB440 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceC440 : Charge := ![2, 0, 0, -1, -2, 1]

def sourceA441 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB441 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceC441 : Charge := ![2, 0, 0, -1, -2, 1]

def sourceA442 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB442 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceC442 : Charge := ![2, 0, 0, -1, -2, 1]

def sourceA443 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB443 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceC443 : Charge := ![2, 0, 0, -1, -2, 1]

def sourceA444 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB444 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceC444 : Charge := ![2, 0, 0, -1, -2, 1]

def sourceA445 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB445 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceC445 : Charge := ![2, 0, 0, -1, -2, 1]

def sourceA446 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB446 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceC446 : Charge := ![2, 0, 0, -1, -2, 1]

def sourceA447 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB447 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceC447 : Charge := ![2, 0, 0, -1, -2, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA448 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB448 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceC448 : Charge := ![2, 0, 0, -1, -2, 1]

def sourceA451 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB451 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceC451 : Charge := ![1, 0, 0, 1, 1, -3]

def sourceA452 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB452 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceC452 : Charge := ![1, 0, 0, 1, 1, -3]

def sourceA453 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB453 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceC453 : Charge := ![1, 0, 0, 1, 1, -3]

def sourceA454 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB454 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceC454 : Charge := ![1, 0, 0, 1, 1, -3]

def sourceA455 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB455 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceC455 : Charge := ![1, 0, 0, 1, 1, -3]

def sourceA456 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB456 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceC456 : Charge := ![1, 0, 0, 1, 1, -3]

def sourceA457 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB457 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceC457 : Charge := ![1, 0, 0, 1, 1, -3]

def sourceA458 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB458 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceC458 : Charge := ![1, 0, 0, 1, 1, -3]

def sourceA461 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceB461 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceC461 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA462 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceB462 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceC462 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA463 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceB463 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceC463 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA466 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB466 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceC466 : Charge := ![2, 0, 0, -2, 1, -1]

def sourceA467 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB467 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceC467 : Charge := ![2, 0, 0, -2, 1, -1]

def sourceA468 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB468 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceC468 : Charge := ![2, 0, 0, -2, 1, -1]

def sourceA471 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB471 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceC471 : Charge := ![2, 0, 0, -2, 1, -1]

def sourceA473 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB473 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC473 : Charge := ![1, 0, 0, 2, -2, -1]

def sourceA474 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB474 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC474 : Charge := ![1, 0, 0, 2, -2, -1]

def sourceA475 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB475 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC475 : Charge := ![1, 0, 0, 2, -2, -1]

def sourceA476 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB476 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC476 : Charge := ![1, 0, 0, 2, -2, -1]

def sourceA477 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB477 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC477 : Charge := ![1, 0, 0, 2, -2, -1]

def sourceA478 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB478 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC478 : Charge := ![1, 0, 0, 2, -2, -1]

def sourceA479 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB479 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC479 : Charge := ![1, 0, 0, 2, -2, -1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA480 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB480 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC480 : Charge := ![1, 0, 0, 2, -2, -1]

def sourceA481 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB481 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC481 : Charge := ![1, 0, 0, 2, -2, -1]

def sourceA483 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceB483 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC483 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA485 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceB485 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC485 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA486 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceB486 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC486 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA487 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceB487 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC487 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA488 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceB488 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC488 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA489 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceB489 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC489 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA490 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceB490 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC490 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA493 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB493 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceC493 : Charge := ![1, 0, 0, 2, -1, -2]

def sourceA494 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB494 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceC494 : Charge := ![1, 0, 0, 2, -1, -2]

def sourceA495 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB495 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceC495 : Charge := ![1, 0, 0, 2, -1, -2]

def sourceA496 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB496 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceC496 : Charge := ![1, 0, 0, 2, -1, -2]

def sourceA497 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB497 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceC497 : Charge := ![1, 0, 0, 2, -1, -2]

def sourceA498 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB498 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceC498 : Charge := ![1, 0, 0, 2, -1, -2]

def sourceA499 : Charge := ![1, 0, 0, 2, -1, -2]
def sourceB499 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceC499 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA500 : Charge := ![1, 0, 0, 2, -1, -2]
def sourceB500 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceC500 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA503 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB503 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceC503 : Charge := ![2, 0, -1, -1, 1, -1]

def sourceA504 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB504 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceC504 : Charge := ![2, 0, -1, -1, 1, -1]

def sourceA505 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB505 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceC505 : Charge := ![2, 0, -1, -1, 1, -1]

def sourceA506 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB506 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceC506 : Charge := ![2, 0, -1, -1, 1, -1]

def sourceA507 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB507 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceC507 : Charge := ![2, 0, -1, -1, 1, -1]

def sourceA508 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB508 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceC508 : Charge := ![2, 0, -1, -1, 1, -1]

def sourceA509 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB509 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceC509 : Charge := ![2, 0, -1, -1, 1, -1]

def sourceA510 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB510 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC510 : Charge := ![1, 0, 1, 1, -2, -1]

def sourceA511 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB511 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC511 : Charge := ![1, 0, 1, 1, -2, -1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA512 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB512 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC512 : Charge := ![1, 0, 1, 1, -2, -1]

def sourceA513 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB513 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC513 : Charge := ![1, 0, 1, 1, -2, -1]

def sourceA514 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB514 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC514 : Charge := ![1, 0, 1, 1, -2, -1]

def sourceA515 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB515 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC515 : Charge := ![1, 0, 1, 1, -2, -1]

def sourceA516 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB516 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC516 : Charge := ![1, 0, 1, 1, -2, -1]

def sourceA517 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB517 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC517 : Charge := ![1, 0, 1, 1, -2, -1]

def sourceA518 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB518 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC518 : Charge := ![1, 0, 1, 1, -2, -1]

def sourceA519 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB519 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC519 : Charge := ![1, 0, 1, 1, -2, -1]

def sourceA520 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB520 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC520 : Charge := ![1, 0, 1, 1, -2, -1]

def sourceA521 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB521 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC521 : Charge := ![1, 0, 1, 1, -2, -1]

def sourceA523 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceB523 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC523 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA525 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceB525 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC525 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA526 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceB526 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC526 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA527 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceB527 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC527 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA528 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceB528 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC528 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA529 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceB529 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC529 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA530 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB530 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceC530 : Charge := ![2, 0, -1, -1, 0, 0]

def sourceA531 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB531 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceC531 : Charge := ![2, 0, -1, -1, 0, 0]

def sourceA532 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB532 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC532 : Charge := ![1, 0, 1, 1, -1, -2]

def sourceA533 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB533 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC533 : Charge := ![1, 0, 1, 1, -1, -2]

def sourceA534 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB534 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC534 : Charge := ![1, 0, 1, 1, -1, -2]

def sourceA535 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB535 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC535 : Charge := ![1, 0, 1, 1, -1, -2]

def sourceA536 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB536 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC536 : Charge := ![1, 0, 1, 1, -1, -2]

def sourceA537 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB537 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC537 : Charge := ![1, 0, 1, 1, -1, -2]

def sourceA538 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceB538 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC538 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA539 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceB539 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC539 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA540 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceB540 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC540 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA541 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceB541 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC541 : Charge := ![-3, 0, 0, 0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA544 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB544 : Charge := ![1, 0, 1, 1, 0, -3]
def sourceC544 : Charge := ![2, 0, -1, -1, -1, 1]

def sourceA545 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB545 : Charge := ![1, 0, 1, 1, 0, -3]
def sourceC545 : Charge := ![2, 0, -1, -1, -1, 1]

def sourceA546 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB546 : Charge := ![1, 0, 1, 1, 0, -3]
def sourceC546 : Charge := ![2, 0, -1, -1, -1, 1]

def sourceA547 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB547 : Charge := ![1, 0, 1, 1, 0, -3]
def sourceC547 : Charge := ![2, 0, -1, -1, -1, 1]

def sourceA548 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB548 : Charge := ![1, 0, 1, 1, 0, -3]
def sourceC548 : Charge := ![2, 0, -1, -1, -1, 1]

def sourceA549 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB549 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceC549 : Charge := ![1, 0, 1, 1, 0, -3]

def sourceA550 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB550 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceC550 : Charge := ![1, 0, 1, 1, 0, -3]

def sourceA551 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB551 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceC551 : Charge := ![1, 0, 1, 1, 0, -3]

def sourceA552 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB552 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceC552 : Charge := ![1, 0, 1, 1, 0, -3]

def sourceA553 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB553 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceC553 : Charge := ![1, 0, 1, 1, 0, -3]

def sourceA554 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB554 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceC554 : Charge := ![1, 0, 1, 1, 0, -3]

def sourceA555 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB555 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceC555 : Charge := ![1, 0, 1, 1, 0, -3]

def sourceA556 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB556 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceC556 : Charge := ![1, 0, 1, 1, 0, -3]

def sourceA557 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB557 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceC557 : Charge := ![1, 0, 1, 1, 0, -3]

def sourceA560 : Charge := ![1, 0, 1, 1, 0, -3]
def sourceB560 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceC560 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA561 : Charge := ![1, 0, 1, 1, 0, -3]
def sourceB561 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceC561 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA562 : Charge := ![1, 0, 1, 1, 0, -3]
def sourceB562 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceC562 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA564 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB564 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC564 : Charge := ![2, -1, 0, 0, 1, -2]

def sourceA565 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB565 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC565 : Charge := ![2, -1, 0, 0, 1, -2]

def sourceA566 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB566 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC566 : Charge := ![2, -1, 0, 0, 1, -2]

def sourceA567 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB567 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC567 : Charge := ![2, -1, 0, 0, 1, -2]

def sourceA568 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB568 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC568 : Charge := ![2, -1, 0, 0, 1, -2]

def sourceA569 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB569 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC569 : Charge := ![2, -1, 0, 0, 1, -2]

def sourceA570 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB570 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC570 : Charge := ![2, -1, 0, 0, 1, -2]

def sourceA571 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB571 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC571 : Charge := ![2, -1, 0, 0, 1, -2]

def sourceA572 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB572 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC572 : Charge := ![1, 1, 0, 0, -2, 0]

def sourceA573 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB573 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC573 : Charge := ![1, 1, 0, 0, -2, 0]

def sourceA574 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceB574 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC574 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA575 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceB575 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC575 : Charge := ![-3, 0, 0, 0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA576 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceB576 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC576 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA577 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceB577 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC577 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA578 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB578 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC578 : Charge := ![2, -1, 0, 1, -1, -1]

def sourceA579 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB579 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC579 : Charge := ![2, -1, 0, 1, -1, -1]

def sourceA580 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB580 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC580 : Charge := ![2, -1, 0, 1, -1, -1]

def sourceA581 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB581 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC581 : Charge := ![2, -1, 0, 1, -1, -1]

def sourceA582 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB582 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC582 : Charge := ![2, -1, 0, 1, -1, -1]

def sourceA583 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB583 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC583 : Charge := ![2, -1, 0, 1, -1, -1]

def sourceA584 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB584 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC584 : Charge := ![2, -1, 0, 1, -1, -1]

def sourceA585 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB585 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC585 : Charge := ![2, -1, 0, 1, -1, -1]

def sourceA586 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB586 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC586 : Charge := ![2, -1, 0, 1, -1, -1]

def sourceA587 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB587 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC587 : Charge := ![2, -1, 0, 1, -1, -1]

def sourceA588 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB588 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceC588 : Charge := ![1, 1, 0, -1, 0, -1]

def sourceA589 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB589 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceC589 : Charge := ![1, 1, 0, -1, 0, -1]

def sourceA590 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceB590 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceC590 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA591 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceB591 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceC591 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA592 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceB592 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceC592 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA593 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceB593 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceC593 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA594 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB594 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC594 : Charge := ![2, -1, 0, 1, 0, -2]

def sourceA595 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB595 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC595 : Charge := ![2, -1, 0, 1, 0, -2]

def sourceA596 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB596 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC596 : Charge := ![2, -1, 0, 1, 0, -2]

def sourceA597 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB597 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC597 : Charge := ![2, -1, 0, 1, 0, -2]

def sourceA598 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB598 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC598 : Charge := ![2, -1, 0, 1, 0, -2]

def sourceA599 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB599 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC599 : Charge := ![2, -1, 0, 1, 0, -2]

def sourceA600 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB600 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC600 : Charge := ![2, -1, 0, 1, 0, -2]

def sourceA601 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB601 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC601 : Charge := ![2, -1, 0, 1, 0, -2]

def sourceA602 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB602 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC602 : Charge := ![2, -1, 0, 1, 0, -2]

def sourceA603 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB603 : Charge := ![2, -1, 0, 1, 0, -2]
def sourceC603 : Charge := ![1, 1, 0, -1, -1, 0]

def sourceA604 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB604 : Charge := ![2, -1, 0, 1, 0, -2]
def sourceC604 : Charge := ![1, 1, 0, -1, -1, 0]

def sourceA605 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceB605 : Charge := ![2, -1, 0, 1, 0, -2]
def sourceC605 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA606 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceB606 : Charge := ![2, -1, 0, 1, 0, -2]
def sourceC606 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA607 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceB607 : Charge := ![2, -1, 0, 1, 0, -2]
def sourceC607 : Charge := ![-3, 0, 0, 0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA608 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceB608 : Charge := ![2, -1, 0, 1, 0, -2]
def sourceC608 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA609 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB609 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC609 : Charge := ![2, 0, 0, 0, -1, -1]

def sourceA610 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB610 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC610 : Charge := ![2, 0, 0, 0, 0, -2]

def sourceA611 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB611 : Charge := ![1, 0, 0, 0, -2, 1]
def sourceC611 : Charge := ![2, 0, 0, 0, 1, -3]

def sourceA612 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB612 : Charge := ![1, 0, 0, 0, -2, 1]
def sourceC612 : Charge := ![2, 0, 0, 0, 1, -3]

def sourceA613 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB613 : Charge := ![1, 0, 0, 0, -2, 1]
def sourceC613 : Charge := ![2, 0, 0, 0, 1, -3]

def sourceA614 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB614 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceC614 : Charge := ![1, 0, 0, 0, -2, 1]

def sourceA615 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB615 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceC615 : Charge := ![2, 0, 0, 1, -2, -1]

def sourceA616 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB616 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceC616 : Charge := ![2, 0, 0, 1, -2, -1]

def sourceA617 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB617 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceC617 : Charge := ![2, 0, 0, 1, -2, -1]

def sourceA618 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB618 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceC618 : Charge := ![2, 0, 0, 1, -2, -1]

def sourceA619 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB619 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceC619 : Charge := ![2, 0, 0, 1, -2, -1]

def sourceA620 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB620 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceC620 : Charge := ![2, 0, 0, 1, -2, -1]

def sourceA621 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB621 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceC621 : Charge := ![2, 0, 0, 1, -2, -1]

def sourceA622 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB622 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceC622 : Charge := ![1, 0, 0, -1, 1, -1]

def sourceA623 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB623 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceC623 : Charge := ![1, 0, 0, -1, 1, -1]

def sourceA624 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceB624 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceC624 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA625 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceB625 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceC625 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA626 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceB626 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceC626 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA627 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB627 : Charge := ![1, 0, 0, -1, 0, 0]
def sourceC627 : Charge := ![2, 0, 0, 1, -1, -2]

def sourceA628 : Charge := ![1, 0, 0, -1, 0, 0]
def sourceB628 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceC628 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA629 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB629 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceC629 : Charge := ![2, 0, 0, 1, 0, -3]

def sourceA630 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB630 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceC630 : Charge := ![2, 0, 0, 1, 0, -3]

def sourceA631 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB631 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceC631 : Charge := ![2, 0, 0, 1, 0, -3]

def sourceA632 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB632 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceC632 : Charge := ![1, 0, 0, -1, -1, 1]

def sourceA633 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB633 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceC633 : Charge := ![3, -2, 0, 0, -1, 0]

def sourceA634 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB634 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceC634 : Charge := ![3, -2, 0, 0, -1, 0]

def sourceA635 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB635 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceC635 : Charge := ![3, -2, 0, 0, -1, 0]

def sourceA636 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB636 : Charge := ![3, -2, 0, 0, -1, 0]
def sourceC636 : Charge := ![0, 2, 0, 0, 0, -2]

def sourceA637 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB637 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC637 : Charge := ![3, -2, 0, 0, 0, -1]

def sourceA638 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB638 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC638 : Charge := ![3, -2, 0, 0, 0, -1]

def sourceA639 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB639 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC639 : Charge := ![3, -2, 0, 0, 0, -1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA64 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB64 : Charge := ![0, 0, 1, 1, 1, -3]
def sourceC64 : Charge := ![3, 0, -1, -1, -1, 0]

def sourceA65 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB65 : Charge := ![0, 0, 1, 1, 1, -3]
def sourceC65 : Charge := ![3, 0, -1, -1, -1, 0]

def sourceA68 : Charge := ![0, 0, 1, 1, 1, -3]
def sourceB68 : Charge := ![3, 0, -1, -1, -1, 0]
def sourceC68 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA72 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB72 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC72 : Charge := ![2, 1, 0, 0, -2, -1]

def sourceA73 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB73 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC73 : Charge := ![2, 1, 0, 0, -2, -1]

def sourceA74 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB74 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC74 : Charge := ![2, 1, 0, 0, -2, -1]

def sourceA75 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB75 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC75 : Charge := ![2, 1, 0, 0, -2, -1]

def sourceA76 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB76 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC76 : Charge := ![2, 1, 0, 0, -2, -1]

def sourceA77 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB77 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC77 : Charge := ![2, 1, 0, 0, -2, -1]

def sourceA78 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB78 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC78 : Charge := ![2, 1, 0, 0, -2, -1]

def sourceA79 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB79 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC79 : Charge := ![2, 1, 0, 0, -2, -1]

def sourceA80 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB80 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC80 : Charge := ![2, 1, 0, 0, -2, -1]

def sourceA81 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB81 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC81 : Charge := ![2, 1, 0, 0, -2, -1]

def sourceA82 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB82 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC82 : Charge := ![2, 1, 0, 0, -2, -1]

def sourceA85 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceB85 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC85 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA86 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceB86 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC86 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA87 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceB87 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC87 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA88 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceB88 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC88 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA89 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceB89 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC89 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA90 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceB90 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC90 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA91 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceB91 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC91 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA94 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB94 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC94 : Charge := ![2, 1, 0, -1, -1, -1]

def sourceA95 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB95 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC95 : Charge := ![2, 1, 0, -1, -1, -1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA640 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB640 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC640 : Charge := ![3, -2, 0, 0, 0, -1]

def sourceA641 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB641 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC641 : Charge := ![3, -2, 0, 0, 0, -1]

def sourceA642 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB642 : Charge := ![3, -2, 0, 0, 0, -1]
def sourceC642 : Charge := ![0, 2, 0, 0, -1, -1]

def sourceA643 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB643 : Charge := ![3, -2, 0, 0, 0, -1]
def sourceC643 : Charge := ![0, 2, 0, 0, -1, -1]

def sourceA644 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceB644 : Charge := ![3, -2, 0, 0, 0, -1]
def sourceC644 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA645 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceB645 : Charge := ![3, -2, 0, 0, 0, -1]
def sourceC645 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA646 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceB646 : Charge := ![3, -2, 0, 0, 0, -1]
def sourceC646 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA647 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceB647 : Charge := ![3, -2, 0, 0, 0, -1]
def sourceC647 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA648 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB648 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC648 : Charge := ![3, -1, -1, 0, -1, 0]

def sourceA649 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB649 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC649 : Charge := ![3, -1, -1, 0, -1, 0]

def sourceA650 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB650 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC650 : Charge := ![3, -1, -1, 0, -1, 0]

def sourceA651 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB651 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC651 : Charge := ![3, -1, -1, 0, -1, 0]

def sourceA652 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB652 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC652 : Charge := ![3, -1, -1, 0, -1, 0]

def sourceA653 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB653 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC653 : Charge := ![3, -1, -1, 0, -1, 0]

def sourceA654 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB654 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC654 : Charge := ![3, -1, -1, 0, -1, 0]

def sourceA655 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB655 : Charge := ![3, -1, -1, 0, -1, 0]
def sourceC655 : Charge := ![0, 1, 1, 0, 0, -2]

def sourceA656 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB656 : Charge := ![3, -1, -1, 0, -1, 0]
def sourceC656 : Charge := ![0, 1, 1, 0, 0, -2]

def sourceA657 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceB657 : Charge := ![3, -1, -1, 0, -1, 0]
def sourceC657 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA658 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceB658 : Charge := ![3, -1, -1, 0, -1, 0]
def sourceC658 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA659 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceB659 : Charge := ![3, -1, -1, 0, -1, 0]
def sourceC659 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA660 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceB660 : Charge := ![3, -1, -1, 0, -1, 0]
def sourceC660 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA661 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB661 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC661 : Charge := ![3, -1, -1, 0, 0, -1]

def sourceA662 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB662 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC662 : Charge := ![3, -1, -1, 0, 0, -1]

def sourceA663 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB663 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC663 : Charge := ![3, -1, -1, 0, 0, -1]

def sourceA664 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB664 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC664 : Charge := ![3, -1, -1, 0, 0, -1]

def sourceA665 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB665 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC665 : Charge := ![3, -1, -1, 0, 0, -1]

def sourceA666 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB666 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC666 : Charge := ![3, -1, -1, 0, 0, -1]

def sourceA667 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB667 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC667 : Charge := ![3, -1, -1, 0, 0, -1]

def sourceA668 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB668 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC668 : Charge := ![3, -1, -1, 0, 0, -1]

def sourceA669 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB669 : Charge := ![3, -1, -1, 0, 0, -1]
def sourceC669 : Charge := ![0, 1, 1, 0, -1, -1]

def sourceA670 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB670 : Charge := ![3, -1, -1, 0, 0, -1]
def sourceC670 : Charge := ![0, 1, 1, 0, -1, -1]

def sourceA671 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceB671 : Charge := ![3, -1, -1, 0, 0, -1]
def sourceC671 : Charge := ![-3, 0, 0, 0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA672 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceB672 : Charge := ![3, -1, -1, 0, 0, -1]
def sourceC672 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA673 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceB673 : Charge := ![3, -1, -1, 0, 0, -1]
def sourceC673 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA674 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceB674 : Charge := ![3, -1, -1, 0, 0, -1]
def sourceC674 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA675 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB675 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC675 : Charge := ![3, -1, 0, 0, -1, -1]

def sourceA676 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB676 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC676 : Charge := ![3, -1, 0, 0, -1, -1]

def sourceA677 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB677 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC677 : Charge := ![3, -1, 0, 0, -1, -1]

def sourceA678 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceB678 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceC678 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA679 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB679 : Charge := ![0, 1, 0, 0, -1, 0]
def sourceC679 : Charge := ![3, -1, 0, 0, 0, -2]

def sourceA680 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB680 : Charge := ![0, 0, 0, 0, 1, -1]
def sourceC680 : Charge := ![3, 0, 0, 0, -2, -1]

def sourceA681 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB681 : Charge := ![3, 0, 0, 0, -1, -2]
def sourceC681 : Charge := ![0, 0, 0, 0, 0, 0]

def sourceA683 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB683 : Charge := ![1, -1, 1, -1, -1, 1]
def sourceC683 : Charge := ![2, 1, -1, 0, 0, -2]

def sourceA684 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB684 : Charge := ![1, -1, 1, -1, -1, 1]
def sourceC684 : Charge := ![2, 1, -1, 0, 0, -2]

def sourceA685 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB685 : Charge := ![1, -1, 1, -1, -1, 1]
def sourceC685 : Charge := ![2, 1, -1, 0, 0, -2]

def sourceA686 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB686 : Charge := ![1, -1, 1, -1, -1, 1]
def sourceC686 : Charge := ![2, 1, -1, 0, 0, -2]

def sourceA687 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB687 : Charge := ![1, -1, 1, -1, -1, 1]
def sourceC687 : Charge := ![2, 1, -1, 0, 0, -2]

def sourceA688 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB688 : Charge := ![1, -1, 1, -1, -1, 1]
def sourceC688 : Charge := ![2, 1, -1, 0, 0, -2]

def sourceA689 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB689 : Charge := ![1, -1, 1, -1, -1, 1]
def sourceC689 : Charge := ![2, 1, -1, 0, 0, -2]

def sourceA690 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB690 : Charge := ![1, -1, 1, -1, -1, 1]
def sourceC690 : Charge := ![2, 1, -1, 0, 0, -2]

def sourceA691 : Charge := ![1, -1, 1, -1, -1, 1]
def sourceB691 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceC691 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA692 : Charge := ![1, -1, 1, -1, -1, 1]
def sourceB692 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceC692 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA693 : Charge := ![1, -1, 1, -1, -1, 1]
def sourceB693 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceC693 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA694 : Charge := ![1, -1, 1, -1, -1, 1]
def sourceB694 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceC694 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA695 : Charge := ![1, -1, 1, -1, -1, 1]
def sourceB695 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceC695 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA696 : Charge := ![1, -1, 1, -1, -1, 1]
def sourceB696 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceC696 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA697 : Charge := ![1, -1, 1, -1, -1, 1]
def sourceB697 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceC697 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA698 : Charge := ![1, -1, 1, -1, -1, 1]
def sourceB698 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceC698 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA700 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB700 : Charge := ![1, -1, 2, -1, -1, 0]
def sourceC700 : Charge := ![2, 1, -2, 0, 0, -1]

def sourceA701 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB701 : Charge := ![1, -1, 2, -1, -1, 0]
def sourceC701 : Charge := ![2, 1, -2, 0, 0, -1]

def sourceA702 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB702 : Charge := ![1, -1, 2, -1, -1, 0]
def sourceC702 : Charge := ![2, 1, -2, 0, 0, -1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA704 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB704 : Charge := ![1, -1, 2, -1, -1, 0]
def sourceC704 : Charge := ![2, 1, -2, 0, 0, -1]

def sourceA705 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB705 : Charge := ![1, -1, 2, -1, -1, 0]
def sourceC705 : Charge := ![2, 1, -2, 0, 0, -1]

def sourceA706 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB706 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC706 : Charge := ![1, -1, 2, -1, -1, 0]

def sourceA707 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB707 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC707 : Charge := ![1, -1, 2, -1, -1, 0]

def sourceA708 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB708 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC708 : Charge := ![1, -1, 2, -1, -1, 0]

def sourceA709 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB709 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC709 : Charge := ![1, -1, 2, -1, -1, 0]

def sourceA710 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB710 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC710 : Charge := ![1, -1, 2, -1, -1, 0]

def sourceA711 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB711 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC711 : Charge := ![1, -1, 2, -1, -1, 0]

def sourceA713 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB713 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC713 : Charge := ![1, -1, 2, -1, -1, 0]

def sourceA714 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB714 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC714 : Charge := ![1, -1, 2, -1, -1, 0]

def sourceA715 : Charge := ![1, -1, 2, -1, -1, 0]
def sourceB715 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC715 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA716 : Charge := ![1, -1, 2, -1, -1, 0]
def sourceB716 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC716 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA717 : Charge := ![1, -1, 2, -1, -1, 0]
def sourceB717 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC717 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA718 : Charge := ![1, -1, 2, -1, -1, 0]
def sourceB718 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC718 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA719 : Charge := ![1, -1, 2, -1, -1, 0]
def sourceB719 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC719 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA720 : Charge := ![1, -1, 2, -1, -1, 0]
def sourceB720 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC720 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA721 : Charge := ![1, -1, 2, -1, -1, 0]
def sourceB721 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC721 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA722 : Charge := ![1, -1, 2, -1, -1, 0]
def sourceB722 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC722 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA723 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB723 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceC723 : Charge := ![2, 0, 0, 0, 0, -2]

def sourceA724 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB724 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceC724 : Charge := ![2, 0, 0, 0, 0, -2]

def sourceA725 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB725 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC725 : Charge := ![1, 0, 0, -1, -1, 1]

def sourceA726 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB726 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC726 : Charge := ![1, 0, 0, -1, -1, 1]

def sourceA727 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceB727 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC727 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA728 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceB728 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC728 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA729 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceB729 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC729 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA731 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB731 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceC731 : Charge := ![2, 0, -1, 1, 0, -2]

def sourceA732 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB732 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceC732 : Charge := ![2, 0, -1, 1, 0, -2]

def sourceA733 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB733 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceC733 : Charge := ![2, 0, -1, 1, 0, -2]

def sourceA734 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB734 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceC734 : Charge := ![2, 0, -1, 1, 0, -2]

def sourceA735 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB735 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceC735 : Charge := ![2, 0, -1, 1, 0, -2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA736 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB736 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceC736 : Charge := ![2, 0, -1, 1, 0, -2]

def sourceA737 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB737 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceC737 : Charge := ![2, 0, -1, 1, 0, -2]

def sourceA738 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB738 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceC738 : Charge := ![1, 0, 1, -2, -1, 1]

def sourceA739 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB739 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceC739 : Charge := ![1, 0, 1, -2, -1, 1]

def sourceA740 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB740 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceC740 : Charge := ![1, 0, 1, -2, -1, 1]

def sourceA741 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB741 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceC741 : Charge := ![1, 0, 1, -2, -1, 1]

def sourceA743 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB743 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceC743 : Charge := ![1, 0, 1, -2, -1, 1]

def sourceA746 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB746 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceC746 : Charge := ![1, 0, 1, -2, -1, 1]

def sourceA747 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB747 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceC747 : Charge := ![1, 0, 1, -2, -1, 1]

def sourceA749 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceB749 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceC749 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA751 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceB751 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceC751 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA752 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceB752 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceC752 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA753 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceB753 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceC753 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA754 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceB754 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceC754 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA755 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceB755 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceC755 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA756 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceB756 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceC756 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA757 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB757 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceC757 : Charge := ![2, 0, -1, 0, 0, -1]

def sourceA758 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB758 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceC758 : Charge := ![2, 0, -1, 0, 0, -1]

def sourceA759 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB759 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceC759 : Charge := ![1, 0, 1, -1, -1, 0]

def sourceA760 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB760 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceC760 : Charge := ![1, 0, 1, -1, -1, 0]

def sourceA761 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceB761 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceC761 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA762 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceB762 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceC762 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA763 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceB763 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceC763 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA765 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB765 : Charge := ![1, 0, 2, -2, -1, 0]
def sourceC765 : Charge := ![2, 0, -2, 1, 0, -1]

def sourceA766 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB766 : Charge := ![1, 0, 2, -2, -1, 0]
def sourceC766 : Charge := ![2, 0, -2, 1, 0, -1]

def sourceA767 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB767 : Charge := ![1, 0, 2, -2, -1, 0]
def sourceC767 : Charge := ![2, 0, -2, 1, 0, -1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA768 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB768 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC768 : Charge := ![1, 0, 2, -2, -1, 0]

def sourceA769 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB769 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC769 : Charge := ![1, 0, 2, -2, -1, 0]

def sourceA770 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB770 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC770 : Charge := ![1, 0, 2, -2, -1, 0]

def sourceA771 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB771 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC771 : Charge := ![1, 0, 2, -2, -1, 0]

def sourceA772 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB772 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC772 : Charge := ![1, 0, 2, -2, -1, 0]

def sourceA773 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB773 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC773 : Charge := ![1, 0, 2, -2, -1, 0]

def sourceA774 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB774 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC774 : Charge := ![1, 0, 2, -2, -1, 0]

def sourceA775 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB775 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC775 : Charge := ![1, 0, 2, -2, -1, 0]

def sourceA776 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB776 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC776 : Charge := ![1, 0, 2, -2, -1, 0]

def sourceA778 : Charge := ![1, 0, 2, -2, -1, 0]
def sourceB778 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC778 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA780 : Charge := ![1, 0, 2, -2, -1, 0]
def sourceB780 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC780 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA781 : Charge := ![1, 0, 2, -2, -1, 0]
def sourceB781 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC781 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA782 : Charge := ![1, 0, 2, -2, -1, 0]
def sourceB782 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC782 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA783 : Charge := ![1, 0, 2, -2, -1, 0]
def sourceB783 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC783 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA784 : Charge := ![1, 0, 2, -2, -1, 0]
def sourceB784 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC784 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA785 : Charge := ![1, 0, 2, -2, -1, 0]
def sourceB785 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC785 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA788 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB788 : Charge := ![2, 0, -2, 0, 0, 0]
def sourceC788 : Charge := ![1, 0, 2, -1, -1, -1]

def sourceA789 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB789 : Charge := ![2, 0, -2, 0, 0, 0]
def sourceC789 : Charge := ![1, 0, 2, -1, -1, -1]

def sourceA790 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB790 : Charge := ![2, 0, -2, 0, 0, 0]
def sourceC790 : Charge := ![1, 0, 2, -1, -1, -1]

def sourceA791 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB791 : Charge := ![2, 0, -2, 0, 0, 0]
def sourceC791 : Charge := ![1, 0, 2, -1, -1, -1]

def sourceA792 : Charge := ![1, 0, 2, -1, -1, -1]
def sourceB792 : Charge := ![2, 0, -2, 0, 0, 0]
def sourceC792 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA793 : Charge := ![1, 0, 2, -1, -1, -1]
def sourceB793 : Charge := ![2, 0, -2, 0, 0, 0]
def sourceC793 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA796 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB796 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceC796 : Charge := ![2, -1, -1, 1, 0, -1]

def sourceA797 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB797 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceC797 : Charge := ![2, -1, -1, 1, 0, -1]

def sourceA798 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB798 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceC798 : Charge := ![2, -1, -1, 1, 0, -1]

def sourceA799 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB799 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceC799 : Charge := ![2, -1, -1, 1, 0, -1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA800 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB800 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceC800 : Charge := ![2, -1, -1, 1, 0, -1]

def sourceA801 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB801 : Charge := ![2, -1, -1, 1, 0, -1]
def sourceC801 : Charge := ![1, 1, 1, -2, -1, 0]

def sourceA802 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB802 : Charge := ![2, -1, -1, 1, 0, -1]
def sourceC802 : Charge := ![1, 1, 1, -2, -1, 0]

def sourceA803 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB803 : Charge := ![2, -1, -1, 1, 0, -1]
def sourceC803 : Charge := ![1, 1, 1, -2, -1, 0]

def sourceA804 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB804 : Charge := ![2, -1, -1, 1, 0, -1]
def sourceC804 : Charge := ![1, 1, 1, -2, -1, 0]

def sourceA805 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB805 : Charge := ![2, -1, -1, 1, 0, -1]
def sourceC805 : Charge := ![1, 1, 1, -2, -1, 0]

def sourceA806 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB806 : Charge := ![2, -1, -1, 1, 0, -1]
def sourceC806 : Charge := ![1, 1, 1, -2, -1, 0]

def sourceA807 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB807 : Charge := ![2, -1, -1, 1, 0, -1]
def sourceC807 : Charge := ![1, 1, 1, -2, -1, 0]

def sourceA809 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceB809 : Charge := ![2, -1, -1, 1, 0, -1]
def sourceC809 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA811 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceB811 : Charge := ![2, -1, -1, 1, 0, -1]
def sourceC811 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA812 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceB812 : Charge := ![2, -1, -1, 1, 0, -1]
def sourceC812 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA813 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceB813 : Charge := ![2, -1, -1, 1, 0, -1]
def sourceC813 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA814 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceB814 : Charge := ![2, -1, -1, 1, 0, -1]
def sourceC814 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA815 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceB815 : Charge := ![2, -1, -1, 1, 0, -1]
def sourceC815 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA816 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB816 : Charge := ![1, 1, 1, -1, -1, -1]
def sourceC816 : Charge := ![2, -1, -1, 0, 0, 0]

def sourceA817 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB817 : Charge := ![1, 1, 1, -1, -1, -1]
def sourceC817 : Charge := ![2, -1, -1, 0, 0, 0]

def sourceA818 : Charge := ![1, 1, 1, -1, -1, -1]
def sourceB818 : Charge := ![2, -1, -1, 0, 0, 0]
def sourceC818 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA819 : Charge := ![1, 1, 1, -1, -1, -1]
def sourceB819 : Charge := ![2, -1, -1, 0, 0, 0]
def sourceC819 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA820 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB820 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC820 : Charge := ![2, -1, 0, -1, -1, 1]

def sourceA821 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB821 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC821 : Charge := ![2, -1, 0, -1, -1, 1]

def sourceA822 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB822 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC822 : Charge := ![2, -1, 0, -1, -1, 1]

def sourceA823 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB823 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC823 : Charge := ![2, -1, 0, -1, -1, 1]

def sourceA824 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB824 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC824 : Charge := ![2, -1, 0, -1, -1, 1]

def sourceA825 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB825 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC825 : Charge := ![2, -1, 0, -1, -1, 1]

def sourceA826 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB826 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC826 : Charge := ![2, -1, 0, -1, -1, 1]

def sourceA827 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB827 : Charge := ![2, -1, 0, -1, -1, 1]
def sourceC827 : Charge := ![1, 1, 0, 0, 0, -2]

def sourceA828 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB828 : Charge := ![2, -1, 0, -1, -1, 1]
def sourceC828 : Charge := ![1, 1, 0, 0, 0, -2]

def sourceA829 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceB829 : Charge := ![2, -1, 0, -1, -1, 1]
def sourceC829 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA830 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceB830 : Charge := ![2, -1, 0, -1, -1, 1]
def sourceC830 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA831 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB831 : Charge := ![1, 1, -1, 0, 0, -1]
def sourceC831 : Charge := ![2, -1, 1, -1, -1, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA832 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB832 : Charge := ![1, 1, -1, 0, 0, -1]
def sourceC832 : Charge := ![2, -1, 1, -1, -1, 0]

def sourceA833 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB833 : Charge := ![1, 1, -1, 0, 0, -1]
def sourceC833 : Charge := ![2, -1, 1, -1, -1, 0]

def sourceA834 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB834 : Charge := ![1, 1, -1, 0, 0, -1]
def sourceC834 : Charge := ![2, -1, 1, -1, -1, 0]

def sourceA835 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB835 : Charge := ![1, 1, -1, 0, 0, -1]
def sourceC835 : Charge := ![2, -1, 1, -1, -1, 0]

def sourceA836 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB836 : Charge := ![2, -1, 1, -1, -1, 0]
def sourceC836 : Charge := ![1, 1, -1, 0, 0, -1]

def sourceA837 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB837 : Charge := ![2, -1, 1, -1, -1, 0]
def sourceC837 : Charge := ![1, 1, -1, 0, 0, -1]

def sourceA838 : Charge := ![1, 1, -1, 0, 0, -1]
def sourceB838 : Charge := ![2, -1, 1, -1, -1, 0]
def sourceC838 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA839 : Charge := ![1, 1, -1, 0, 0, -1]
def sourceB839 : Charge := ![2, -1, 1, -1, -1, 0]
def sourceC839 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA840 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB840 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceC840 : Charge := ![2, 0, 0, -2, -1, 1]

def sourceA841 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB841 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceC841 : Charge := ![2, 0, 0, -2, -1, 1]

def sourceA842 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB842 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceC842 : Charge := ![2, 0, 0, -2, -1, 1]

def sourceA843 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB843 : Charge := ![2, 0, 0, -2, -1, 1]
def sourceC843 : Charge := ![1, 0, 0, 1, 0, -2]

def sourceA844 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB844 : Charge := ![2, 0, 0, -2, -1, 1]
def sourceC844 : Charge := ![1, 0, 0, 1, 0, -2]

def sourceA845 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceB845 : Charge := ![2, 0, 0, -2, -1, 1]
def sourceC845 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA846 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceB846 : Charge := ![2, 0, 0, -2, -1, 1]
def sourceC846 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA847 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB847 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC847 : Charge := ![2, 0, 0, -1, -1, 0]

def sourceA848 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB848 : Charge := ![1, 0, -1, 1, 0, -1]
def sourceC848 : Charge := ![2, 0, 1, -2, -1, 0]

def sourceA849 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB849 : Charge := ![1, 0, -1, 1, 0, -1]
def sourceC849 : Charge := ![2, 0, 1, -2, -1, 0]

def sourceA850 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB850 : Charge := ![2, 0, 1, -2, -1, 0]
def sourceC850 : Charge := ![1, 0, -1, 1, 0, -1]

def sourceA851 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB851 : Charge := ![2, 0, 1, -2, -1, 0]
def sourceC851 : Charge := ![1, 0, -1, 1, 0, -1]

def sourceA852 : Charge := ![1, 0, -1, 1, 0, -1]
def sourceB852 : Charge := ![2, 0, 1, -2, -1, 0]
def sourceC852 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA853 : Charge := ![1, 0, -1, 1, 0, -1]
def sourceB853 : Charge := ![2, 0, 1, -2, -1, 0]
def sourceC853 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA854 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB854 : Charge := ![1, 0, -1, 0, 0, 0]
def sourceC854 : Charge := ![2, 0, 1, -1, -1, -1]

def sourceA855 : Charge := ![1, 0, -1, 0, 0, 0]
def sourceB855 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceC855 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA856 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB856 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC856 : Charge := ![3, -1, -1, -1, 0, 0]

def sourceA857 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB857 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC857 : Charge := ![3, -1, -1, -1, 0, 0]

def sourceA858 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB858 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC858 : Charge := ![0, 1, 1, 0, -1, -1]

def sourceA859 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB859 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC859 : Charge := ![3, -1, 0, -1, -1, 0]

def sourceA860 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB860 : Charge := ![3, 0, 0, -1, -1, -1]
def sourceC860 : Charge := ![0, 0, 0, 0, 0, 0]

def sourceA862 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB862 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceC862 : Charge := ![2, 1, -1, -2, 0, 0]

def sourceA863 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB863 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceC863 : Charge := ![2, 1, -1, -2, 0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA864 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB864 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceC864 : Charge := ![2, 1, -1, -2, 0, 0]

def sourceA865 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB865 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceC865 : Charge := ![2, 1, -1, -2, 0, 0]

def sourceA866 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB866 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceC866 : Charge := ![2, 1, -1, -2, 0, 0]

def sourceA867 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB867 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceC867 : Charge := ![2, 1, -1, -2, 0, 0]

def sourceA868 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB868 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceC868 : Charge := ![2, 0, 1, -1, -2, 0]

def sourceA869 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB869 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceC869 : Charge := ![2, 0, 1, -1, -2, 0]

def sourceA870 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB870 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceC870 : Charge := ![2, 0, 1, -1, -2, 0]

def sourceA871 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB871 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceC871 : Charge := ![2, 0, 1, -1, -2, 0]

def sourceA872 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB872 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceC872 : Charge := ![2, 0, 1, -1, -2, 0]

def sourceA873 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB873 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceC873 : Charge := ![2, 0, 1, -1, -2, 0]

def sourceA874 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB874 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceC874 : Charge := ![2, 0, 1, -1, -2, 0]

def sourceA875 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB875 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceC875 : Charge := ![2, 0, 1, -1, -2, 0]

def sourceA876 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB876 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceC876 : Charge := ![2, 0, 1, -1, -2, 0]

def sourceA877 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB877 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceC877 : Charge := ![2, 0, 1, -1, -2, 0]

def sourceA878 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB878 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceC878 : Charge := ![2, 0, 1, -1, -2, 0]

def sourceA879 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB879 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceC879 : Charge := ![2, 0, 1, -1, -2, 0]

def sourceA882 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB882 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC882 : Charge := ![0, 1, -1, 1, 1, -2]

def sourceA883 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB883 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC883 : Charge := ![0, 1, -1, 1, 1, -2]

def sourceA884 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB884 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC884 : Charge := ![0, 1, -1, 1, 1, -2]

def sourceA885 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB885 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC885 : Charge := ![0, 1, -1, 1, 1, -2]

def sourceA886 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB886 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC886 : Charge := ![0, 1, -1, 1, 1, -2]

def sourceA887 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB887 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC887 : Charge := ![0, 1, -1, 1, 1, -2]

def sourceA888 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB888 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC888 : Charge := ![0, 1, -1, 1, 1, -2]

def sourceA889 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB889 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC889 : Charge := ![0, 1, -1, 1, 1, -2]

def sourceA890 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB890 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC890 : Charge := ![0, 1, -1, 1, 1, -2]

def sourceA891 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB891 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC891 : Charge := ![0, 1, -1, 1, 1, -2]

def sourceA893 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceB893 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC893 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA894 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceB894 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC894 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA895 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceB895 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC895 : Charge := ![-2, -1, 0, 0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA896 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceB896 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC896 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA897 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceB897 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC897 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA898 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceB898 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC898 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA899 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceB899 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC899 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA901 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB901 : Charge := ![0, 1, -1, 2, 0, -2]
def sourceC901 : Charge := ![2, 0, 1, -2, -1, 0]

def sourceA903 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB903 : Charge := ![0, 1, 0, 0, 1, -2]
def sourceC903 : Charge := ![2, 0, 0, 0, -2, 0]

def sourceA904 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB904 : Charge := ![0, 1, 0, 0, 1, -2]
def sourceC904 : Charge := ![2, 0, 0, 0, -2, 0]

def sourceA905 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB905 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC905 : Charge := ![0, 1, 0, 0, 1, -2]

def sourceA906 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB906 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC906 : Charge := ![0, 1, 0, 0, 1, -2]

def sourceA907 : Charge := ![0, 1, 0, 0, 1, -2]
def sourceB907 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC907 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA908 : Charge := ![0, 1, 0, 0, 1, -2]
def sourceB908 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC908 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA909 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB909 : Charge := ![0, 1, 0, 1, -1, -1]
def sourceC909 : Charge := ![2, 0, 0, -1, 0, -1]

def sourceA910 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB910 : Charge := ![0, 1, 0, 1, -1, -1]
def sourceC910 : Charge := ![2, 0, 0, -1, 0, -1]

def sourceA911 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB911 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC911 : Charge := ![0, 1, 0, 1, -1, -1]

def sourceA912 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB912 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC912 : Charge := ![0, 1, 0, 1, -1, -1]

def sourceA913 : Charge := ![0, 1, 0, 1, -1, -1]
def sourceB913 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC913 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA914 : Charge := ![0, 1, 0, 1, -1, -1]
def sourceB914 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC914 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA915 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB915 : Charge := ![0, 1, 0, 1, 0, -2]
def sourceC915 : Charge := ![2, 0, 0, -1, -1, 0]

def sourceA916 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB916 : Charge := ![0, 1, 0, 1, 0, -2]
def sourceC916 : Charge := ![2, 0, 0, -1, -1, 0]

def sourceA917 : Charge := ![0, 1, 0, 1, 0, -2]
def sourceB917 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC917 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA919 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB919 : Charge := ![0, 1, 0, 2, -2, -1]
def sourceC919 : Charge := ![2, 0, 0, -2, 1, -1]

def sourceA920 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB920 : Charge := ![0, 1, 0, 2, -2, -1]
def sourceC920 : Charge := ![2, 0, 0, -2, 1, -1]

def sourceA923 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB923 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC923 : Charge := ![0, 1, 0, 2, -2, -1]

def sourceA924 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB924 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC924 : Charge := ![0, 1, 0, 2, -2, -1]

def sourceA925 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB925 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC925 : Charge := ![0, 1, 0, 2, -2, -1]

def sourceA926 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB926 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC926 : Charge := ![0, 1, 0, 2, -2, -1]

def sourceA927 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB927 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC927 : Charge := ![0, 1, 0, 2, -2, -1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA928 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB928 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC928 : Charge := ![0, 1, 0, 2, -2, -1]

def sourceA929 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB929 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC929 : Charge := ![0, 1, 0, 2, -2, -1]

def sourceA930 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB930 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC930 : Charge := ![0, 1, 0, 2, -2, -1]

def sourceA931 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB931 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC931 : Charge := ![0, 1, 0, 2, -2, -1]

def sourceA932 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB932 : Charge := ![0, 1, 0, 2, -1, -2]
def sourceC932 : Charge := ![2, 0, 0, -2, 0, 0]

def sourceA933 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB933 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceC933 : Charge := ![0, 1, 0, 2, -1, -2]

def sourceA934 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB934 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceC934 : Charge := ![0, 1, 0, 2, -1, -2]

def sourceA935 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB935 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceC935 : Charge := ![2, 0, -1, -1, 1, -1]

def sourceA936 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB936 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceC936 : Charge := ![2, 0, -1, -1, 1, -1]

def sourceA937 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB937 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceC937 : Charge := ![2, 0, -1, -1, 1, -1]

def sourceA938 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB938 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceC938 : Charge := ![2, 0, -1, -1, 1, -1]

def sourceA940 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB940 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceC940 : Charge := ![2, 0, -1, -1, 1, -1]

def sourceA941 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB941 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC941 : Charge := ![0, 1, 1, 1, -2, -1]

def sourceA942 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB942 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC942 : Charge := ![0, 1, 1, 1, -2, -1]

def sourceA943 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB943 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC943 : Charge := ![0, 1, 1, 1, -2, -1]

def sourceA944 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB944 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC944 : Charge := ![0, 1, 1, 1, -2, -1]

def sourceA945 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB945 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC945 : Charge := ![0, 1, 1, 1, -2, -1]

def sourceA946 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB946 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC946 : Charge := ![0, 1, 1, 1, -2, -1]

def sourceA947 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB947 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC947 : Charge := ![0, 1, 1, 1, -2, -1]

def sourceA948 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB948 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC948 : Charge := ![0, 1, 1, 1, -2, -1]

def sourceA949 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB949 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC949 : Charge := ![0, 1, 1, 1, -2, -1]

def sourceA950 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB950 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC950 : Charge := ![0, 1, 1, 1, -2, -1]

def sourceA951 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB951 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC951 : Charge := ![0, 1, 1, 1, -2, -1]

def sourceA952 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB952 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC952 : Charge := ![0, 1, 1, 1, -2, -1]

def sourceA954 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceB954 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC954 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA955 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceB955 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC955 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA956 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceB956 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC956 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA957 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceB957 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC957 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA958 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceB958 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC958 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA959 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceB959 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC959 : Charge := ![-2, -1, 0, 0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA96 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB96 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC96 : Charge := ![2, 1, 0, -1, -1, -1]

def sourceA97 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB97 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC97 : Charge := ![2, 1, 0, -1, -1, -1]

def sourceA98 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB98 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC98 : Charge := ![2, 1, 0, -1, -1, -1]

def sourceA99 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB99 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC99 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceB100 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC100 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceB101 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC101 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceB102 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC102 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceB103 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC103 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceB106 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceC106 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB107 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceC107 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB108 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceC108 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB109 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceC109 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB110 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceC110 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB111 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceC111 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB112 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceC112 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB113 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC113 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB114 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC114 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB115 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC115 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB116 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC116 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB117 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceC117 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceB118 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceC118 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceB119 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC119 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceB120 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC120 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceB121 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC121 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceB122 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC122 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceB123 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC123 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceB124 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC124 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceB125 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC125 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceB126 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC126 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceB127 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC127 : Charge := ![1, 0, 0, 0, 2, -3]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA960 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceB960 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC960 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA963 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB963 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC963 : Charge := ![0, 1, 1, 1, -1, -2]

def sourceA964 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB964 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC964 : Charge := ![0, 1, 1, 1, -1, -2]

def sourceA965 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB965 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC965 : Charge := ![0, 1, 1, 1, -1, -2]

def sourceA966 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceB966 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC966 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA967 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceB967 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC967 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA968 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceB968 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC968 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA969 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceB969 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC969 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA972 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB972 : Charge := ![0, 2, -1, 1, -1, -1]
def sourceC972 : Charge := ![2, -1, 1, -1, 0, -1]

def sourceA973 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB973 : Charge := ![0, 2, -1, 1, -1, -1]
def sourceC973 : Charge := ![2, -1, 1, -1, 0, -1]

def sourceA976 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB976 : Charge := ![0, 2, -1, 1, -1, -1]
def sourceC976 : Charge := ![2, -1, 1, -1, 0, -1]

def sourceA977 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB977 : Charge := ![0, 2, -1, 1, -1, -1]
def sourceC977 : Charge := ![2, -1, 1, -1, 0, -1]

def sourceA978 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB978 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceC978 : Charge := ![0, 2, -1, 1, -1, -1]

def sourceA979 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB979 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceC979 : Charge := ![0, 2, -1, 1, -1, -1]

def sourceA980 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB980 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceC980 : Charge := ![0, 2, -1, 1, -1, -1]

def sourceA982 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB982 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceC982 : Charge := ![0, 2, -1, 1, -1, -1]

def sourceA983 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB983 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceC983 : Charge := ![0, 2, -1, 1, -1, -1]

def sourceA986 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB986 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceC986 : Charge := ![0, 2, -1, 1, -1, -1]

def sourceA987 : Charge := ![0, 2, -1, 1, -1, -1]
def sourceB987 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceC987 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA988 : Charge := ![0, 2, -1, 1, -1, -1]
def sourceB988 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceC988 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA989 : Charge := ![0, 2, -1, 1, -1, -1]
def sourceB989 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceC989 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA990 : Charge := ![0, 2, -1, 1, -1, -1]
def sourceB990 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceC990 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA991 : Charge := ![0, 2, -1, 1, -1, -1]
def sourceB991 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceC991 : Charge := ![-2, -1, 0, 0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA992 : Charge := ![0, 2, -1, 1, -1, -1]
def sourceB992 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceC992 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA993 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB993 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC993 : Charge := ![2, -1, 0, 0, 0, -1]

def sourceA994 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB994 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC994 : Charge := ![2, -1, 0, 0, 0, -1]

def sourceA995 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB995 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC995 : Charge := ![0, 2, 0, 0, -1, -1]

def sourceA996 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB996 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC996 : Charge := ![0, 2, 0, 0, -1, -1]

def sourceA997 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceB997 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC997 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1000 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceC1000 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceB1001 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceC1001 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceB1003 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceC1003 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceB1004 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceC1004 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceB1005 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceC1005 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceB1006 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceC1006 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceB1008 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceC1008 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceB1012 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceC1012 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceB1013 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceC1013 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceB1015 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceC1015 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1016 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceC1016 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1017 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceC1017 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1018 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceC1018 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1020 : Charge := ![0, 2, 0, 1, -1, -2]
def sourceC1020 : Charge := ![2, -1, 0, -1, 0, 0]
def sourceB1021 : Charge := ![2, -1, 0, -1, 0, 0]
def sourceC1021 : Charge := ![0, 2, 0, 1, -1, -2]
def sourceB1022 : Charge := ![2, -1, 0, -1, 0, 0]
def sourceC1022 : Charge := ![0, 2, 0, 1, -1, -2]
def sourceB1023 : Charge := ![2, -1, 0, -1, 0, 0]
def sourceC1023 : Charge := ![-2, -1, 0, 0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB1024 : Charge := ![2, -1, 0, -1, 0, 0]
def sourceC1024 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1025 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceC1025 : Charge := ![1, 2, -1, -1, 0, -1]
def sourceB1026 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceC1026 : Charge := ![1, 2, -1, -1, 0, -1]
def sourceB1027 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceC1027 : Charge := ![1, 2, -1, -1, 0, -1]
def sourceB1029 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceC1029 : Charge := ![1, 2, -1, -1, 0, -1]
def sourceB1030 : Charge := ![1, 2, -1, -1, 0, -1]
def sourceC1030 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1031 : Charge := ![1, 2, -1, -1, 0, -1]
def sourceC1031 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1032 : Charge := ![1, 2, -1, -1, 0, -1]
def sourceC1032 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1033 : Charge := ![1, 2, -1, -1, 0, -1]
def sourceC1033 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1036 : Charge := ![1, 0, -1, 2, -1, -1]
def sourceC1036 : Charge := ![1, 1, 1, -2, 0, -1]
def sourceB1039 : Charge := ![1, 0, -1, 2, -1, -1]
def sourceC1039 : Charge := ![1, 1, 1, -2, 0, -1]
def sourceB1040 : Charge := ![1, 1, 1, -2, 0, -1]
def sourceC1040 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1041 : Charge := ![1, 1, 1, -2, 0, -1]
def sourceC1041 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1043 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceC1043 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceB1044 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceC1044 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceB1045 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC1045 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1048 : Charge := ![1, 1, -1, -1, 0, 0]
def sourceC1048 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceB1049 : Charge := ![1, 1, -1, -1, 0, 0]
def sourceC1049 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceB1050 : Charge := ![1, 1, -1, -1, 0, 0]
def sourceC1050 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1051 : Charge := ![1, 1, -1, -1, 0, 0]
def sourceC1051 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1052 : Charge := ![1, 0, 1, 0, -2, 0]
def sourceC1052 : Charge := ![1, 1, -1, 0, 1, -2]
def sourceB1053 : Charge := ![1, 0, 1, 0, -2, 0]
def sourceC1053 : Charge := ![1, 1, -1, 0, 1, -2]
def sourceB1054 : Charge := ![1, 0, 1, 0, -2, 0]
def sourceC1054 : Charge := ![1, 1, -1, 0, 1, -2]
def sourceB1055 : Charge := ![1, 1, -1, 0, 1, -2]
def sourceC1055 : Charge := ![1, 0, 1, 0, -2, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB1056 : Charge := ![1, 1, -1, 0, 1, -2]
def sourceC1056 : Charge := ![1, 0, 1, 0, -2, 0]
def sourceB1057 : Charge := ![1, 1, -1, 0, 1, -2]
def sourceC1057 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1058 : Charge := ![1, 1, -1, 0, 1, -2]
def sourceC1058 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1059 : Charge := ![1, 1, -1, 1, -1, -1]
def sourceC1059 : Charge := ![1, 0, 1, -1, 0, -1]
def sourceB1060 : Charge := ![1, 1, -1, 1, -1, -1]
def sourceC1060 : Charge := ![1, 0, 1, -1, 0, -1]
def sourceB1061 : Charge := ![1, 1, -1, 1, -1, -1]
def sourceC1061 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1062 : Charge := ![1, 1, -1, 1, -1, -1]
def sourceC1062 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1063 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceC1063 : Charge := ![1, 1, -1, 1, 0, -2]
def sourceB1064 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceC1064 : Charge := ![1, 1, -1, 1, 0, -2]
def sourceB1065 : Charge := ![1, 1, -1, 1, 0, -2]
def sourceC1065 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceB1066 : Charge := ![1, 1, -1, 1, 0, -2]
def sourceC1066 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceB1067 : Charge := ![1, 1, -1, 1, 0, -2]
def sourceC1067 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1068 : Charge := ![1, 1, -1, 1, 0, -2]
def sourceC1068 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1069 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC1069 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceB1070 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC1070 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceB1071 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceC1071 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceB1072 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceC1072 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceB1073 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceC1073 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceB1074 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceC1074 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceB1075 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceC1075 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1076 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceC1076 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1077 : Charge := ![1, 0, 0, -1, 0, 0]
def sourceC1077 : Charge := ![1, 1, 0, 1, -1, -2]
def sourceB1078 : Charge := ![1, 1, 0, 1, -1, -2]
def sourceC1078 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1079 : Charge := ![1, -1, 1, 0, -1, 0]
def sourceC1079 : Charge := ![1, 2, -1, 0, 0, -2]
def sourceB1080 : Charge := ![1, -1, 1, 0, -1, 0]
def sourceC1080 : Charge := ![1, 2, -1, 0, 0, -2]
def sourceB1081 : Charge := ![1, 2, -1, 0, 0, -2]
def sourceC1081 : Charge := ![1, -1, 1, 0, -1, 0]
def sourceB1082 : Charge := ![1, -1, 0, 0, 1, -1]
def sourceC1082 : Charge := ![1, 2, 0, 0, -2, -1]
def sourceB1083 : Charge := ![1, -1, 0, 0, 1, -1]
def sourceC1083 : Charge := ![1, 2, 0, 0, -2, -1]
def sourceB1084 : Charge := ![1, 2, 0, 0, -2, -1]
def sourceC1084 : Charge := ![1, -1, 0, 0, 1, -1]
def sourceB1085 : Charge := ![0, 2, 0, 0, -2, 0]
def sourceC1085 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceB1086 : Charge := ![0, 2, 0, 0, -2, 0]
def sourceC1086 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceB1087 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC1087 : Charge := ![0, 2, 0, 0, -2, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB1088 : Charge := ![0, 2, 0, -1, -1, 0]
def sourceC1088 : Charge := ![2, -1, 0, 1, 0, -2]
def sourceB1089 : Charge := ![0, 2, 0, -1, -1, 0]
def sourceC1089 : Charge := ![2, -1, 0, 1, 0, -2]
def sourceB1090 : Charge := ![2, -1, 0, 1, 0, -2]
def sourceC1090 : Charge := ![0, 2, 0, -1, -1, 0]
def sourceB1091 : Charge := ![0, 1, 1, -1, -1, 0]
def sourceC1091 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceB1092 : Charge := ![0, 1, 1, -1, -1, 0]
def sourceC1092 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceB1093 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceC1093 : Charge := ![0, 1, 1, -1, -1, 0]
def sourceB1094 : Charge := ![0, 1, 0, 0, -1, 0]
def sourceC1094 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB1095 : Charge := ![0, 1, 0, -1, 0, 0]
def sourceC1095 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceB1096 : Charge := ![2, 1, 0, 0, -1, -2]
def sourceC1096 : Charge := ![0, 0, 0, 0, 0, 0]
def sourceB1097 : Charge := ![0, 1, 0, -1, -1, 1]
def sourceC1097 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB1098 : Charge := ![0, 1, 1, -1, -1, 0]
def sourceC1098 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceB1099 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceC1099 : Charge := ![0, 1, 1, -1, -1, 0]
def sourceB1100 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceC1100 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1101 : Charge := ![0, 1, 2, -1, -1, -1]
def sourceC1101 : Charge := ![2, 0, -2, 0, 0, 0]
def sourceB1102 : Charge := ![2, 0, -2, 0, 0, 0]
def sourceC1102 : Charge := ![0, 1, 2, -1, -1, -1]
def sourceB1103 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC1103 : Charge := ![0, 2, 0, -1, -1, 0]
def sourceB1104 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC1104 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1105 : Charge := ![0, 2, 1, -1, -1, -1]
def sourceC1105 : Charge := ![2, -1, -1, 0, 0, 0]
def sourceB1106 : Charge := ![0, 2, 1, -1, -1, -1]
def sourceC1106 : Charge := ![2, -1, -1, 0, 0, 0]
def sourceB1107 : Charge := ![2, -1, -1, 0, 0, 0]
def sourceC1107 : Charge := ![0, 2, 1, -1, -1, -1]
def sourceB1108 : Charge := ![2, -1, -1, 0, 0, 0]
def sourceC1108 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1109 : Charge := ![2, -1, -1, 0, 0, 0]
def sourceC1109 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1110 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceC1110 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceB1111 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1111 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceB1112 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceC1112 : Charge := ![1, 1, -1, 1, 0, -2]
def sourceB1113 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceC1113 : Charge := ![1, 1, -1, 1, 0, -2]
def sourceB1114 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceC1114 : Charge := ![1, 1, -1, 1, 0, -2]
def sourceB1116 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceC1116 : Charge := ![1, 1, -1, 0, 0, -1]
def sourceB1117 : Charge := ![1, 1, -1, 0, 0, -1]
def sourceC1117 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceB1118 : Charge := ![1, 1, -1, -1, -1, 1]
def sourceC1118 : Charge := ![1, 0, 1, 0, 0, -2]
def sourceB1119 : Charge := ![1, 1, -1, -1, -1, 1]
def sourceC1119 : Charge := ![1, 0, 1, 0, 0, -2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB1120 : Charge := ![1, 1, -1, -1, -1, 1]
def sourceC1120 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1121 : Charge := ![1, 1, -1, -1, -1, 1]
def sourceC1121 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1122 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceC1122 : Charge := ![1, 1, 0, -2, -1, 1]
def sourceB1123 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceC1123 : Charge := ![1, 1, 0, -2, -1, 1]
def sourceB1124 : Charge := ![1, 1, 0, -2, -1, 1]
def sourceC1124 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceB1125 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC1125 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceB1126 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceC1126 : Charge := ![1, 0, -1, 1, 0, -1]
def sourceB1127 : Charge := ![1, 1, 1, -1, -1, -1]
def sourceC1127 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1128 : Charge := ![1, -1, 1, 0, 0, -1]
def sourceC1128 : Charge := ![1, 2, -1, -1, -1, 0]
def sourceB1129 : Charge := ![1, -1, 1, 0, 0, -1]
def sourceC1129 : Charge := ![1, 2, -1, -1, -1, 0]
def sourceB1130 : Charge := ![1, 2, -1, -1, -1, 0]
def sourceC1130 : Charge := ![1, -1, 1, 0, 0, -1]
def sourceB1131 : Charge := ![2, -1, 0, -1, -1, 1]
def sourceC1131 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceB1132 : Charge := ![0, 2, -1, 0, 0, -1]
def sourceC1132 : Charge := ![2, -1, 1, -1, -1, 0]
def sourceB1133 : Charge := ![0, 2, -1, 0, 0, -1]
def sourceC1133 : Charge := ![2, -1, 1, -1, -1, 0]
def sourceB1134 : Charge := ![2, -1, 1, -1, -1, 0]
def sourceC1134 : Charge := ![0, 2, -1, 0, 0, -1]
def sourceB1135 : Charge := ![2, -1, 1, -1, -1, 0]
def sourceC1135 : Charge := ![0, 2, -1, 0, 0, -1]
def sourceB1136 : Charge := ![2, -1, 1, -1, -1, 0]
def sourceC1136 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1137 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC1137 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceB1138 : Charge := ![0, 1, -1, 0, 0, 0]
def sourceC1138 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceB1139 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceC1139 : Charge := ![0, 0, 0, 0, 0, 0]
def sourceB1140 : Charge := ![-1, 1, 1, -1, -1, 1]
def sourceC1140 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB1141 : Charge := ![1, 1, 1, -1, -1, -1]
def sourceC1141 : Charge := ![0, 0, 0, 0, 0, 0]
def sourceB1142 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceC1142 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceB1143 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceC1143 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1145 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceC1145 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1147 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceC1147 : Charge := ![3, 0, 0, -1, -1, -1]
def sourceB1148 : Charge := ![3, 0, 0, -1, -1, -1]
def sourceC1148 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1150 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceC1150 : Charge := ![1, 0, 0, 1, 2, -4]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB1152 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC1152 : Charge := ![2, 1, 0, 0, -1, -2]
def sourceB1153 : Charge := ![2, 1, 0, 0, -1, -2]
def sourceC1153 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1154 : Charge := ![2, 1, 0, 0, -1, -2]
def sourceC1154 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1155 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC1155 : Charge := ![2, -1, 0, 0, 2, -3]
def sourceB1156 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC1156 : Charge := ![2, -1, 0, 0, 2, -3]
def sourceB1157 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceC1157 : Charge := ![2, -1, 0, 1, 1, -3]
def sourceB1158 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceC1158 : Charge := ![2, -1, 0, 1, 1, -3]
def sourceB1159 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1159 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB1160 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1160 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB1161 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1161 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1162 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1162 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1163 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1163 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1164 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1164 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceB1165 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1165 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceB1166 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1166 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceB1167 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1167 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceB1168 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1168 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceB1169 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1169 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceB1170 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1170 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceB1171 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1171 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceB1172 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceC1172 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB1173 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceC1173 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB1177 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceC1177 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1178 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1178 : Charge := ![2, 0, 0, 0, 2, -4]
def sourceB1179 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1179 : Charge := ![2, 0, 0, 0, 2, -4]
def sourceB1180 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1180 : Charge := ![2, 0, 0, 0, 2, -4]
def sourceB1182 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1182 : Charge := ![2, 0, 0, 1, 1, -4]
def sourceB1183 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1183 : Charge := ![2, 0, 0, 1, 1, -4]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB1184 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1184 : Charge := ![2, 0, 0, 1, 1, -4]
def sourceB1186 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1186 : Charge := ![3, -1, 0, 0, 1, -3]
def sourceB1189 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC1189 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceB1190 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC1190 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceB1191 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC1191 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceB1192 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceC1192 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1193 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC1193 : Charge := ![3, 0, 0, 0, 1, -4]
def sourceB1194 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC1194 : Charge := ![3, 0, 0, 0, 1, -4]
def sourceB1195 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC1195 : Charge := ![3, 0, 0, 0, 1, -4]
def sourceB1197 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC1197 : Charge := ![3, 0, 0, 0, 1, -4]
def sourceB1198 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC1198 : Charge := ![3, 0, 0, 0, 1, -4]
def sourceB1200 : Charge := ![4, 0, 0, 0, 0, -4]
def sourceC1200 : Charge := ![0, 0, 0, 0, 0, 0]
def sourceB1201 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceC1201 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceB1202 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceC1202 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1203 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceC1203 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1204 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceC1204 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1205 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceC1205 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceB1206 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceC1206 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceB1207 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceC1207 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceB1208 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceC1208 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1210 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceC1210 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1211 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceC1211 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1212 : Charge := ![1, 0, 0, 2, -1, -2]
def sourceC1212 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceB1213 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC1213 : Charge := ![1, 0, 0, 2, -1, -2]
def sourceB1214 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC1214 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1215 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC1215 : Charge := ![-4, 0, 0, 0, 1, 3]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB1216 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC1216 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1217 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC1217 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1218 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC1218 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1220 : Charge := ![3, 0, 0, -2, -1, 0]
def sourceC1220 : Charge := ![1, 0, 0, 2, 0, -3]
def sourceB1221 : Charge := ![3, 0, 0, -2, -1, 0]
def sourceC1221 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1224 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceC1224 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceB1225 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceC1225 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceB1226 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceC1226 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1228 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceC1228 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1229 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceC1229 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1231 : Charge := ![1, 0, 1, 1, 0, -3]
def sourceC1231 : Charge := ![3, 0, -1, -1, -1, 0]
def sourceB1232 : Charge := ![3, 0, -1, -1, -1, 0]
def sourceC1232 : Charge := ![1, 0, 1, 1, 0, -3]
def sourceB1233 : Charge := ![3, 0, -1, -1, -1, 0]
def sourceC1233 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1235 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceC1235 : Charge := ![1, 0, 1, 2, -1, -3]
def sourceB1237 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC1237 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceB1238 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC1238 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceB1239 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC1239 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceB1240 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC1240 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1241 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC1241 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1242 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC1242 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1243 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC1243 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1244 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC1244 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1246 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC1246 : Charge := ![2, -1, 0, 0, 2, -3]
def sourceB1247 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceC1247 : Charge := ![2, 1, 0, -1, 0, -2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB1248 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceC1248 : Charge := ![2, 1, 0, -1, 0, -2]
def sourceB1249 : Charge := ![2, 1, 0, -1, 0, -2]
def sourceC1249 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceB1250 : Charge := ![2, 1, 0, -1, 0, -2]
def sourceC1250 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceB1251 : Charge := ![2, 1, 0, -1, 0, -2]
def sourceC1251 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1252 : Charge := ![2, 1, 0, -1, 0, -2]
def sourceC1252 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1253 : Charge := ![2, 1, 0, -1, 0, -2]
def sourceC1253 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1254 : Charge := ![2, 1, 0, -1, 0, -2]
def sourceC1254 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1255 : Charge := ![2, 1, 0, -1, 0, -2]
def sourceC1255 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1256 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC1256 : Charge := ![2, -1, 0, 1, 1, -3]
def sourceB1257 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC1257 : Charge := ![2, -1, 0, 2, -1, -2]
def sourceB1258 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC1258 : Charge := ![2, -1, 0, 2, -1, -2]
def sourceB1259 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC1259 : Charge := ![2, -1, 0, 2, 0, -3]
def sourceB1260 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC1260 : Charge := ![2, -1, 1, 1, -1, -2]
def sourceB1261 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC1261 : Charge := ![2, -1, 1, 1, -1, -2]
def sourceB1262 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC1262 : Charge := ![2, -1, 1, 1, 0, -3]
def sourceB1263 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1263 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB1264 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1264 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB1265 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1265 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB1266 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1266 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB1267 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1267 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1268 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1268 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1269 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1269 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1270 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1270 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1271 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1271 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1272 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1272 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceB1273 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1273 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceB1274 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1274 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceB1275 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1275 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceB1276 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1276 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceB1277 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1277 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceB1278 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceC1278 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceB1279 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceC1279 : Charge := ![2, 0, 0, 0, -2, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB128 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC128 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceB129 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC129 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB130 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC130 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB131 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC131 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB132 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC132 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB133 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceC133 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceB134 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceC134 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceB135 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC135 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceB136 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC136 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceB137 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC137 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceB138 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC138 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceB139 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC139 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceB140 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC140 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceB141 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC141 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceB142 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC142 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceB143 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC143 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceB144 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC144 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceB145 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC145 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB146 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC146 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB147 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC147 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB148 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC148 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB149 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC149 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceB150 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC150 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceB151 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC151 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceB152 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC152 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceB153 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC153 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceB154 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC154 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceB155 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC155 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceB156 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC156 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceB157 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC157 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceB158 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC158 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceB159 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC159 : Charge := ![-3, 0, 0, 0, 0, 3]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB1281 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceC1281 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1282 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceC1282 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1283 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceC1283 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1284 : Charge := ![2, 0, 0, 0, -3, 1]
def sourceC1284 : Charge := ![2, 0, 0, 0, 2, -4]
def sourceB1285 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1285 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceB1286 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1286 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceB1287 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1287 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceB1288 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1288 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceB1289 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1289 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceB1290 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1290 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceB1291 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceC1291 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceB1292 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceC1292 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceB1295 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceC1295 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1296 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1296 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceB1297 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1297 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceB1298 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1298 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceB1299 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1299 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceB1300 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1300 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceB1301 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1301 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceB1302 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1302 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceB1303 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceC1303 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceB1304 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceC1304 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceB1307 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceC1307 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1308 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceC1308 : Charge := ![2, 0, 0, 1, 1, -4]
def sourceB1309 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC1309 : Charge := ![2, 0, 0, 2, -2, -2]
def sourceB1310 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC1310 : Charge := ![2, 0, 0, 2, -2, -2]
def sourceB1311 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceC1311 : Charge := ![2, 0, 0, 2, -1, -3]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB1312 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceC1312 : Charge := ![2, 0, 0, 2, -1, -3]
def sourceB1313 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceC1313 : Charge := ![2, 0, 0, 2, -1, -3]
def sourceB1315 : Charge := ![2, 0, 0, -2, -1, 1]
def sourceC1315 : Charge := ![2, 0, 0, 2, 0, -4]
def sourceB1316 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC1316 : Charge := ![2, 0, 1, 1, -2, -2]
def sourceB1317 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC1317 : Charge := ![2, 0, 1, 1, -2, -2]
def sourceB1318 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC1318 : Charge := ![2, 0, 1, 1, -1, -3]
def sourceB1319 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC1319 : Charge := ![2, 0, 1, 1, -1, -3]
def sourceB1320 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC1320 : Charge := ![2, 0, 1, 1, -1, -3]
def sourceB1322 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceC1322 : Charge := ![2, 0, 1, 1, 0, -4]
def sourceB1323 : Charge := ![1, 2, 0, 0, -2, -1]
def sourceC1323 : Charge := ![3, -2, 0, 0, 1, -2]
def sourceB1324 : Charge := ![1, 2, 0, 0, -2, -1]
def sourceC1324 : Charge := ![3, -2, 0, 0, 1, -2]
def sourceB1325 : Charge := ![1, 2, 0, -1, 0, -2]
def sourceC1325 : Charge := ![3, -2, 0, 1, -1, -1]
def sourceB1326 : Charge := ![1, 2, 0, -1, 0, -2]
def sourceC1326 : Charge := ![3, -2, 0, 1, -1, -1]
def sourceB1327 : Charge := ![1, 2, 0, -1, -1, -1]
def sourceC1327 : Charge := ![3, -2, 0, 1, 0, -2]
def sourceB1328 : Charge := ![1, 2, 0, -1, -1, -1]
def sourceC1328 : Charge := ![3, -2, 0, 1, 0, -2]
def sourceB1329 : Charge := ![1, 1, 1, 0, -2, -1]
def sourceC1329 : Charge := ![3, -1, -1, 0, 1, -2]
def sourceB1330 : Charge := ![1, 1, 1, 0, -2, -1]
def sourceC1330 : Charge := ![3, -1, -1, 0, 1, -2]
def sourceB1331 : Charge := ![1, 1, 1, -1, 0, -2]
def sourceC1331 : Charge := ![3, -1, -1, 1, -1, -1]
def sourceB1332 : Charge := ![1, 1, 1, -1, 0, -2]
def sourceC1332 : Charge := ![3, -1, -1, 1, -1, -1]
def sourceB1333 : Charge := ![1, 1, 1, -1, -1, -1]
def sourceC1333 : Charge := ![3, -1, -1, 1, 0, -2]
def sourceB1334 : Charge := ![1, 1, 1, -1, -1, -1]
def sourceC1334 : Charge := ![3, -1, -1, 1, 0, -2]
def sourceB1335 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1335 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceB1336 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1336 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceB1337 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1337 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceB1338 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1338 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceB1339 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1339 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceB1340 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1340 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceB1341 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1341 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceB1342 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceC1342 : Charge := ![1, 1, 0, 0, 0, -2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB1344 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceC1344 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1345 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceC1345 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1347 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceC1347 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1348 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1348 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceB1349 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1349 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceB1350 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1350 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceB1351 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1351 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceB1352 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1352 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceB1353 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1353 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceB1354 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1354 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceB1355 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1355 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceB1356 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceC1356 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceB1357 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceC1357 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceB1360 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceC1360 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1361 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC1361 : Charge := ![3, -1, 0, 0, 1, -3]
def sourceB1362 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC1362 : Charge := ![3, -1, 0, 0, 1, -3]
def sourceB1363 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC1363 : Charge := ![3, -1, 0, 0, 1, -3]
def sourceB1364 : Charge := ![3, -1, 0, 0, 1, -3]
def sourceC1364 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1366 : Charge := ![1, 1, 0, -1, 1, -2]
def sourceC1366 : Charge := ![3, -1, 0, 1, -2, -1]
def sourceB1367 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC1367 : Charge := ![3, -1, 0, 1, -1, -2]
def sourceB1370 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC1370 : Charge := ![3, -1, 0, 1, -1, -2]
def sourceB1373 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC1373 : Charge := ![3, -1, 0, 1, 0, -3]
def sourceB1375 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC1375 : Charge := ![3, -1, 0, 1, 0, -3]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB1376 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC1376 : Charge := ![3, -1, 0, 1, 0, -3]
def sourceB1377 : Charge := ![3, -1, 0, 1, 0, -3]
def sourceC1377 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1378 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceC1378 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceB1379 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceC1379 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceB1380 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceC1380 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceB1381 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceC1381 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceB1385 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC1385 : Charge := ![3, 0, 0, 0, -1, -2]
def sourceB1386 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC1386 : Charge := ![3, 0, 0, 0, -1, -2]
def sourceB1387 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC1387 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceB1388 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC1388 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceB1389 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC1389 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceB1390 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC1390 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceB1391 : Charge := ![1, 0, 0, -1, 2, -2]
def sourceC1391 : Charge := ![3, 0, 0, 1, -3, -1]
def sourceB1392 : Charge := ![1, 0, 0, -1, 2, -2]
def sourceC1392 : Charge := ![3, 0, 0, 1, -3, -1]
def sourceB1393 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceC1393 : Charge := ![3, 0, 0, 1, -2, -2]
def sourceB1396 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceC1396 : Charge := ![3, 0, 0, 1, -2, -2]
def sourceB1399 : Charge := ![1, 0, 0, -1, 0, 0]
def sourceC1399 : Charge := ![3, 0, 0, 1, -1, -3]
def sourceB1400 : Charge := ![1, 0, 0, -1, 0, 0]
def sourceC1400 : Charge := ![3, 0, 0, 1, -1, -3]
def sourceB1401 : Charge := ![1, 0, 0, -1, 0, 0]
def sourceC1401 : Charge := ![3, 0, 0, 1, -1, -3]
def sourceB1403 : Charge := ![0, 2, 1, 0, 0, -3]
def sourceC1403 : Charge := ![4, -2, -1, 0, -1, 0]
def sourceB1405 : Charge := ![0, 2, 0, 0, 1, -3]
def sourceC1405 : Charge := ![4, -2, 0, 0, -2, 0]
def sourceB1406 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceC1406 : Charge := ![4, -2, 0, 0, -1, -1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB1408 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceC1408 : Charge := ![4, -2, 0, 0, -1, -1]
def sourceB1410 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC1410 : Charge := ![4, -2, 0, 0, 0, -2]
def sourceB1411 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC1411 : Charge := ![4, -2, 0, 0, 0, -2]
def sourceB1412 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC1412 : Charge := ![4, -2, 0, 0, 0, -2]
def sourceB1413 : Charge := ![4, -2, 0, 0, 0, -2]
def sourceC1413 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1415 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceC1415 : Charge := ![4, -1, -1, -1, 0, -1]
def sourceB1417 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC1417 : Charge := ![4, -1, -1, 0, -1, -1]
def sourceB1418 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC1418 : Charge := ![4, -1, -1, 0, -1, -1]
def sourceB1419 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC1419 : Charge := ![4, -1, -1, 0, -1, -1]
def sourceB1421 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC1421 : Charge := ![4, -1, -1, 0, 0, -2]
def sourceB1422 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC1422 : Charge := ![4, -1, -1, 0, 0, -2]
def sourceB1423 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC1423 : Charge := ![4, -1, -1, 0, 0, -2]
def sourceB1424 : Charge := ![4, -1, -1, 0, 0, -2]
def sourceC1424 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1425 : Charge := ![0, 1, 0, 0, 1, -2]
def sourceC1425 : Charge := ![4, -1, 0, 0, -2, -1]
def sourceB1426 : Charge := ![0, 1, 0, 0, 1, -2]
def sourceC1426 : Charge := ![4, -1, 0, 0, -2, -1]
def sourceB1427 : Charge := ![0, 1, 0, 0, 1, -2]
def sourceC1427 : Charge := ![4, -1, 0, 0, -2, -1]
def sourceB1429 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC1429 : Charge := ![4, -1, 0, 0, -1, -2]
def sourceB1430 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC1430 : Charge := ![4, -1, 0, 0, -1, -2]
def sourceB1431 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC1431 : Charge := ![4, -1, 0, 0, -1, -2]
def sourceB1433 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC1433 : Charge := ![4, -1, 0, 0, -1, -2]
def sourceB1435 : Charge := ![0, 1, 0, 0, -1, 0]
def sourceC1435 : Charge := ![4, -1, 0, 0, 0, -3]
def sourceB1437 : Charge := ![0, 0, 0, 0, 1, -1]
def sourceC1437 : Charge := ![4, 0, 0, 0, -2, -2]
def sourceB1438 : Charge := ![4, 0, 0, 0, -2, -2]
def sourceC1438 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1439 : Charge := ![4, 0, 0, 0, -1, -3]
def sourceC1439 : Charge := ![0, 0, 0, 0, 0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB1440 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceC1440 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceB1441 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC1441 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceB1443 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC1443 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1444 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC1444 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1445 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC1445 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1448 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceC1448 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceB1449 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceC1449 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceB1450 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceC1450 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1452 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceC1452 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1453 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceC1453 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1455 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceC1455 : Charge := ![1, 0, 1, 2, -2, -2]
def sourceB1457 : Charge := ![2, -1, 0, 0, -2, 1]
def sourceC1457 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceB1458 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceC1458 : Charge := ![2, -1, 0, 0, -2, 1]
def sourceB1459 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceC1459 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1460 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceC1460 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1461 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceC1461 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1462 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceC1462 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1463 : Charge := ![2, -1, 0, 1, -2, 0]
def sourceC1463 : Charge := ![2, 1, 0, -1, 0, -2]
def sourceB1464 : Charge := ![2, -1, 0, 1, -2, 0]
def sourceC1464 : Charge := ![2, 1, 0, -1, 0, -2]
def sourceB1465 : Charge := ![2, 1, 0, -1, 0, -2]
def sourceC1465 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1467 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceC1467 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceB1468 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceC1468 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceB1469 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceC1469 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1470 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceC1470 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1471 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC1471 : Charge := ![2, -1, 0, 2, -2, -1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB1472 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC1472 : Charge := ![2, -1, 1, 1, -2, -1]
def sourceB1473 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1473 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB1474 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1474 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB1475 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1475 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1476 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1476 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1477 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1477 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1478 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1478 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB1479 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1479 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB1480 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1480 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1481 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1481 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1482 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1482 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1483 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1483 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceB1484 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1484 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceB1485 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1485 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceB1486 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1486 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceB1487 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1487 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceB1488 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1488 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceB1489 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1489 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceB1490 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceC1490 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceB1491 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceC1491 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceB1495 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC1495 : Charge := ![2, 0, 0, 2, -3, -1]
def sourceB1496 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceC1496 : Charge := ![2, 0, 0, 2, -2, -2]
def sourceB1497 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceC1497 : Charge := ![2, 0, 0, 2, -2, -2]
def sourceB1499 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC1499 : Charge := ![2, 0, 1, 1, -3, -1]
def sourceB1500 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC1500 : Charge := ![2, 0, 1, 1, -2, -2]
def sourceB1501 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC1501 : Charge := ![2, 0, 1, 1, -2, -2]
def sourceB1503 : Charge := ![1, 2, 0, 0, 0, -3]
def sourceC1503 : Charge := ![3, -2, 0, 0, -2, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB1504 : Charge := ![1, 2, 0, -1, 0, -2]
def sourceC1504 : Charge := ![3, -2, 0, 1, -2, 0]
def sourceB1505 : Charge := ![1, 2, 0, -1, -1, -1]
def sourceC1505 : Charge := ![3, -2, 0, 1, -1, -1]
def sourceB1506 : Charge := ![1, 1, 1, 0, 0, -3]
def sourceC1506 : Charge := ![3, -1, -1, 0, -2, 1]
def sourceB1507 : Charge := ![1, 1, 1, -1, 0, -2]
def sourceC1507 : Charge := ![3, -1, -1, 1, -2, 0]
def sourceB1508 : Charge := ![1, 1, 1, -1, -1, -1]
def sourceC1508 : Charge := ![3, -1, -1, 1, -1, -1]
def sourceB1509 : Charge := ![1, 1, 0, 0, 1, -3]
def sourceC1509 : Charge := ![3, -1, 0, 0, -3, 1]
def sourceB1510 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1510 : Charge := ![3, -1, 0, 0, -2, 0]
def sourceB1511 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1511 : Charge := ![3, -1, 0, 0, -2, 0]
def sourceB1512 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1512 : Charge := ![3, -1, 0, 0, -2, 0]
def sourceB1513 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1513 : Charge := ![3, -1, 0, 0, -2, 0]
def sourceB1514 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1514 : Charge := ![3, -1, 0, 0, -2, 0]
def sourceB1515 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1515 : Charge := ![3, -1, 0, 0, -2, 0]
def sourceB1516 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1516 : Charge := ![3, -1, 0, 0, -2, 0]
def sourceB1517 : Charge := ![3, -1, 0, 0, -2, 0]
def sourceC1517 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceB1518 : Charge := ![3, -1, 0, 0, -2, 0]
def sourceC1518 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceB1522 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1522 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceB1523 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1523 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceB1524 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1524 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceB1525 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1525 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceB1526 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1526 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceB1527 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1527 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceB1528 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1528 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceB1529 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceC1529 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceB1531 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceC1531 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1532 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceC1532 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1533 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceC1533 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1534 : Charge := ![1, 1, 0, -1, 1, -2]
def sourceC1534 : Charge := ![3, -1, 0, 1, -3, 0]
def sourceB1535 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC1535 : Charge := ![3, -1, 0, 1, -2, -1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB1537 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC1537 : Charge := ![3, -1, 0, 1, -2, -1]
def sourceB1538 : Charge := ![3, -1, 0, 1, -2, -1]
def sourceC1538 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1540 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceC1540 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceB1541 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceC1541 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceB1542 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceC1542 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceB1543 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceC1543 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceB1550 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC1550 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceB1551 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC1551 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceB1552 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC1552 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceB1553 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceC1553 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1554 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceC1554 : Charge := ![3, 0, 0, 1, -3, -1]
def sourceB1556 : Charge := ![1, 0, 0, -1, 0, 0]
def sourceC1556 : Charge := ![3, 0, 0, 1, -2, -2]
def sourceB1558 : Charge := ![1, 0, 0, -1, 0, 0]
def sourceC1558 : Charge := ![3, 0, 0, 1, -2, -2]
def sourceB1561 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceC1561 : Charge := ![4, -2, 0, 0, -2, 0]
def sourceB1562 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC1562 : Charge := ![4, -2, 0, 0, -1, -1]
def sourceB1564 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC1564 : Charge := ![4, -1, -1, 0, -2, 0]
def sourceB1565 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC1565 : Charge := ![4, -1, -1, 0, -2, 0]
def sourceB1566 : Charge := ![4, -1, -1, 0, -2, 0]
def sourceC1566 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1567 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC1567 : Charge := ![4, -1, -1, 0, -1, -1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB1568 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC1568 : Charge := ![4, -1, -1, 0, -1, -1]
def sourceB1569 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC1569 : Charge := ![4, -1, 0, 0, -2, -1]
def sourceB1570 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC1570 : Charge := ![4, -1, 0, 0, -2, -1]
def sourceB1571 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC1571 : Charge := ![4, -1, 0, 0, -2, -1]
def sourceB1572 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC1572 : Charge := ![4, -1, 0, 0, -2, -1]
def sourceB1573 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC1573 : Charge := ![4, -1, 0, 0, -2, -1]
def sourceB1574 : Charge := ![4, -1, 0, 0, -2, -1]
def sourceC1574 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1575 : Charge := ![4, 0, 0, 0, -2, -2]
def sourceC1575 : Charge := ![0, 0, 0, 0, 0, 0]
def sourceB1576 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceC1576 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1577 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceC1577 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1578 : Charge := ![1, 0, 1, -1, 1, -2]
def sourceC1578 : Charge := ![3, 0, -1, 0, -2, 0]
def sourceB1579 : Charge := ![3, 0, -1, 0, -2, 0]
def sourceC1579 : Charge := ![1, 0, 1, -1, 1, -2]
def sourceB1580 : Charge := ![3, 0, -1, 0, -2, 0]
def sourceC1580 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1581 : Charge := ![3, 0, -1, 0, -2, 0]
def sourceC1581 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1582 : Charge := ![3, 0, -1, 0, -2, 0]
def sourceC1582 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1583 : Charge := ![3, 0, -1, 0, -2, 0]
def sourceC1583 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1584 : Charge := ![1, 0, 2, -1, -1, -1]
def sourceC1584 : Charge := ![3, 0, -2, 0, 0, -1]
def sourceB1585 : Charge := ![3, 0, -2, 0, 0, -1]
def sourceC1585 : Charge := ![1, 0, 2, -1, -1, -1]
def sourceB1586 : Charge := ![3, 0, -2, 0, 0, -1]
def sourceC1586 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1587 : Charge := ![3, 0, -2, 0, 0, -1]
def sourceC1587 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1588 : Charge := ![3, 0, -2, 0, 0, -1]
def sourceC1588 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1590 : Charge := ![3, 0, -2, 0, -1, 0]
def sourceC1590 : Charge := ![1, 0, 2, -1, 0, -2]
def sourceB1591 : Charge := ![3, 0, -2, 0, -1, 0]
def sourceC1591 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1592 : Charge := ![3, 0, -2, 0, -1, 0]
def sourceC1592 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1594 : Charge := ![1, 1, 1, -1, -1, -1]
def sourceC1594 : Charge := ![3, -1, -1, 0, 0, -1]
def sourceB1595 : Charge := ![3, -1, -1, 0, 0, -1]
def sourceC1595 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1596 : Charge := ![3, -1, -1, 0, 0, -1]
def sourceC1596 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1597 : Charge := ![3, -1, -1, 0, 0, -1]
def sourceC1597 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1598 : Charge := ![3, -1, -1, 0, 0, -1]
def sourceC1598 : Charge := ![-4, 0, 0, 1, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB160 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC160 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB161 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC161 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB162 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC162 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB163 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC163 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB164 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC164 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB165 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC165 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceB166 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC166 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceB167 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC167 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceB168 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC168 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceB169 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC169 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceB170 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC170 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceB171 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceC171 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB172 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceC172 : Charge := ![0, 0, 0, 0, 0, 0]
def sourceB174 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceC174 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceB176 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceC176 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceB177 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceC177 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceB178 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceC178 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceB179 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceC179 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceB180 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceC180 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceB181 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceC181 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceB182 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceC182 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceB183 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceC183 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceB184 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceC184 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceB186 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceC186 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceB187 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceC187 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceB188 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceC188 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceB189 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceC189 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceB190 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceC190 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceB191 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceC191 : Charge := ![0, 0, 1, 2, -1, -2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB1600 : Charge := ![1, 1, 1, -1, 0, -2]
def sourceC1600 : Charge := ![3, -1, -1, 0, -1, 0]
def sourceB1601 : Charge := ![3, -1, -1, 0, -1, 0]
def sourceC1601 : Charge := ![1, 1, 1, -1, 0, -2]
def sourceB1602 : Charge := ![3, -1, -1, 0, -1, 0]
def sourceC1602 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1604 : Charge := ![3, -1, -1, 0, -1, 0]
def sourceC1604 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1606 : Charge := ![2, -1, 0, -1, -1, 1]
def sourceC1606 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceB1607 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceC1607 : Charge := ![2, -1, 0, -1, -1, 1]
def sourceB1608 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceC1608 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1609 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceC1609 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1610 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceC1610 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1611 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceC1611 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1612 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceC1612 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceB1613 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC1613 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceB1614 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC1614 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1615 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC1615 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1616 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC1616 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1617 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC1617 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1618 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC1618 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1619 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC1619 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1620 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC1620 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1621 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC1621 : Charge := ![2, -1, 0, -1, 2, -2]
def sourceB1622 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC1622 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceB1623 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC1623 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceB1624 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC1624 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1625 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC1625 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1626 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC1626 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1627 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC1627 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1628 : Charge := ![2, -1, 1, -1, -1, 0]
def sourceC1628 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceB1629 : Charge := ![2, -1, 1, -1, -1, 0]
def sourceC1629 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceB1630 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceC1630 : Charge := ![2, -1, 1, -1, -1, 0]
def sourceB1631 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceC1631 : Charge := ![2, -1, 1, -1, -1, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB1632 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceC1632 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1633 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceC1633 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1634 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceC1634 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1635 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceC1635 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1636 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceC1636 : Charge := ![2, 1, -1, 0, -1, -1]
def sourceB1637 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceC1637 : Charge := ![2, 1, -1, 0, -1, -1]
def sourceB1638 : Charge := ![2, 1, -1, 0, -1, -1]
def sourceC1638 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1639 : Charge := ![2, 1, -1, 0, -2, 0]
def sourceC1639 : Charge := ![2, -1, 1, -1, 1, -2]
def sourceB1640 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC1640 : Charge := ![2, -1, 2, -1, -1, -1]
def sourceB1641 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC1641 : Charge := ![2, -1, 2, -1, -1, -1]
def sourceB1642 : Charge := ![2, 1, -2, 0, -1, 0]
def sourceC1642 : Charge := ![2, -1, 2, -1, 0, -2]
def sourceB1643 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceC1643 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1644 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceC1644 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1645 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceC1645 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1646 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceC1646 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1647 : Charge := ![2, 0, 0, 1, -3, 0]
def sourceC1647 : Charge := ![2, 0, 0, -2, 2, -2]
def sourceB1648 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1648 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB1649 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1649 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB1650 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1650 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceB1651 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1651 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceB1652 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1652 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1653 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1653 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1654 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1654 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1655 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1655 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1656 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1656 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB1657 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1657 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB1658 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1658 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1659 : Charge := ![2, 0, 0, -1, 1, -2]
def sourceC1659 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceB1660 : Charge := ![2, 0, 0, -1, 1, -2]
def sourceC1660 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceB1661 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1661 : Charge := ![2, 0, 0, -1, 1, -2]
def sourceB1662 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1662 : Charge := ![2, 0, 0, -1, 1, -2]
def sourceB1663 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1663 : Charge := ![2, 0, 0, -1, 1, -2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB1664 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1664 : Charge := ![2, 0, 0, -1, 1, -2]
def sourceB1667 : Charge := ![2, 0, 0, 0, -3, 1]
def sourceC1667 : Charge := ![2, 0, 0, -1, 2, -3]
def sourceB1668 : Charge := ![2, 0, -1, 1, -2, 0]
def sourceC1668 : Charge := ![2, 0, 1, -2, 1, -2]
def sourceB1669 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceC1669 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceB1670 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceC1670 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceB1671 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceC1671 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceB1672 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceC1672 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceB1673 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceC1673 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceB1674 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceC1674 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceB1675 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceC1675 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceB1677 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceC1677 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1678 : Charge := ![2, 0, -1, 0, -1, 0]
def sourceC1678 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceB1679 : Charge := ![2, 0, -1, 0, -1, 0]
def sourceC1679 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceB1680 : Charge := ![2, 0, -1, 0, -1, 0]
def sourceC1680 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceB1681 : Charge := ![2, 0, -1, 0, -1, 0]
def sourceC1681 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceB1682 : Charge := ![2, 0, -1, 0, -1, 0]
def sourceC1682 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceB1683 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceC1683 : Charge := ![2, 0, -1, 0, -1, 0]
def sourceB1684 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceC1684 : Charge := ![2, 0, -1, 0, -1, 0]
def sourceB1686 : Charge := ![2, 0, -1, 0, -2, 1]
def sourceC1686 : Charge := ![2, 0, 1, -1, 1, -3]
def sourceB1688 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC1688 : Charge := ![2, 0, 2, -2, -1, -1]
def sourceB1689 : Charge := ![2, 0, -2, 1, -1, 0]
def sourceC1689 : Charge := ![2, 0, 2, -2, 0, -2]
def sourceB1690 : Charge := ![2, 0, -2, 0, 0, 0]
def sourceC1690 : Charge := ![2, 0, 2, -1, -1, -2]
def sourceB1693 : Charge := ![2, 0, -2, 0, -1, 1]
def sourceC1693 : Charge := ![2, 0, 2, -1, 0, -3]
def sourceB1695 : Charge := ![2, -1, -1, 1, 0, -1]
def sourceC1695 : Charge := ![2, 1, 1, -2, -1, -1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB1696 : Charge := ![2, -1, -1, 1, -1, 0]
def sourceC1696 : Charge := ![2, 1, 1, -2, 0, -2]
def sourceB1697 : Charge := ![2, -1, -1, 0, 0, 0]
def sourceC1697 : Charge := ![2, 1, 1, -1, -1, -2]
def sourceB1700 : Charge := ![2, -1, -1, 0, -1, 1]
def sourceC1700 : Charge := ![2, 1, 1, -1, 0, -3]
def sourceB1702 : Charge := ![1, 2, 0, 0, 0, -3]
def sourceC1702 : Charge := ![3, -2, 0, -1, -1, 1]
def sourceB1703 : Charge := ![1, 2, 0, 0, -2, -1]
def sourceC1703 : Charge := ![3, -2, 0, -1, 1, -1]
def sourceB1704 : Charge := ![1, 2, 0, -1, -2, 0]
def sourceC1704 : Charge := ![3, -2, 0, 0, 1, -2]
def sourceB1706 : Charge := ![1, 2, -1, 0, 0, -2]
def sourceC1706 : Charge := ![3, -2, 1, -1, -1, 0]
def sourceB1707 : Charge := ![1, 2, -1, 0, -1, -1]
def sourceC1707 : Charge := ![3, -2, 1, -1, 0, -1]
def sourceB1708 : Charge := ![1, 2, -1, -1, -1, 0]
def sourceC1708 : Charge := ![3, -2, 1, 0, 0, -2]
def sourceB1709 : Charge := ![1, 1, 1, 0, 0, -3]
def sourceC1709 : Charge := ![3, -1, -1, -1, -1, 1]
def sourceB1710 : Charge := ![1, 1, 1, 0, 0, -3]
def sourceC1710 : Charge := ![3, -1, -1, -1, -1, 1]
def sourceB1711 : Charge := ![1, 1, 1, 0, -2, -1]
def sourceC1711 : Charge := ![3, -1, -1, -1, 1, -1]
def sourceB1712 : Charge := ![1, 1, 1, -1, -2, 0]
def sourceC1712 : Charge := ![3, -1, -1, 0, 1, -2]
def sourceB1713 : Charge := ![1, 1, 0, 1, 0, -3]
def sourceC1713 : Charge := ![3, -1, 0, -2, -1, 1]
def sourceB1714 : Charge := ![1, 1, 0, 1, 0, -3]
def sourceC1714 : Charge := ![3, -1, 0, -2, -1, 1]
def sourceB1715 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceC1715 : Charge := ![3, -1, 0, -2, 1, -1]
def sourceB1716 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1716 : Charge := ![3, -1, 0, -1, -1, 0]
def sourceB1717 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1717 : Charge := ![3, -1, 0, -1, -1, 0]
def sourceB1718 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1718 : Charge := ![3, -1, 0, -1, -1, 0]
def sourceB1719 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1719 : Charge := ![3, -1, 0, -1, -1, 0]
def sourceB1720 : Charge := ![3, -1, 0, -1, -1, 0]
def sourceC1720 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceB1723 : Charge := ![3, -1, 0, -1, -1, 0]
def sourceC1723 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1724 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1724 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceB1725 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1725 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceB1726 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1726 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceB1727 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1727 : Charge := ![3, -1, 0, -1, 0, -1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB1728 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1728 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceB1729 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1729 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceB1730 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceC1730 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceB1732 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceC1732 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1733 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceC1733 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1734 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceC1734 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1735 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC1735 : Charge := ![3, -1, 0, -1, 1, -2]
def sourceB1737 : Charge := ![3, -1, 0, -1, 1, -2]
def sourceC1737 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1738 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC1738 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceB1739 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC1739 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceB1740 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC1740 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceB1741 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC1741 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceB1742 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC1742 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceB1743 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC1743 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceB1744 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC1744 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceB1745 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceC1745 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceB1746 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceC1746 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceB1747 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceC1747 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1748 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceC1748 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1749 : Charge := ![1, 1, 0, -1, -2, 1]
def sourceC1749 : Charge := ![3, -1, 0, 0, 1, -3]
def sourceB1750 : Charge := ![1, 1, -1, 1, 0, -2]
def sourceC1750 : Charge := ![3, -1, 1, -2, -1, 0]
def sourceB1751 : Charge := ![1, 1, -1, 1, 0, -2]
def sourceC1751 : Charge := ![3, -1, 1, -2, -1, 0]
def sourceB1752 : Charge := ![1, 1, -1, 1, -1, -1]
def sourceC1752 : Charge := ![3, -1, 1, -2, 0, -1]
def sourceB1753 : Charge := ![1, 1, -1, 0, 0, -1]
def sourceC1753 : Charge := ![3, -1, 1, -1, -1, -1]
def sourceB1756 : Charge := ![1, 1, -1, 0, 0, -1]
def sourceC1756 : Charge := ![3, -1, 1, -1, -1, -1]
def sourceB1759 : Charge := ![1, 1, -1, 0, -1, 0]
def sourceC1759 : Charge := ![3, -1, 1, -1, 0, -2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB1761 : Charge := ![1, 1, -1, 0, -1, 0]
def sourceC1761 : Charge := ![3, -1, 1, -1, 0, -2]
def sourceB1762 : Charge := ![3, -1, 1, -1, 0, -2]
def sourceC1762 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1763 : Charge := ![1, 1, -1, -1, -1, 1]
def sourceC1763 : Charge := ![3, -1, 1, 0, 0, -3]
def sourceB1766 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceC1766 : Charge := ![3, 0, 0, -3, 1, -1]
def sourceB1769 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceC1769 : Charge := ![3, 0, 0, -2, -1, 0]
def sourceB1770 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceC1770 : Charge := ![3, 0, 0, -2, -1, 0]
def sourceB1773 : Charge := ![3, 0, 0, -2, -1, 0]
def sourceC1773 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1775 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceC1775 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceB1776 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceC1776 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceB1777 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC1777 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceB1779 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC1779 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1780 : Charge := ![1, 0, 0, 1, -2, 0]
def sourceC1780 : Charge := ![3, 0, 0, -2, 1, -2]
def sourceB1781 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC1781 : Charge := ![3, 0, 0, -1, -1, -1]
def sourceB1782 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC1782 : Charge := ![3, 0, 0, -1, 0, -2]
def sourceB1783 : Charge := ![1, 0, 0, 0, -2, 1]
def sourceC1783 : Charge := ![3, 0, 0, -1, 1, -3]
def sourceB1784 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceC1784 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceB1785 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceC1785 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceB1786 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceC1786 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceB1787 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceC1787 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceB1788 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceC1788 : Charge := ![3, 0, 0, 0, 0, -3]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB1792 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceC1792 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1793 : Charge := ![1, 0, -1, 2, 0, -2]
def sourceC1793 : Charge := ![3, 0, 1, -3, -1, 0]
def sourceB1795 : Charge := ![1, 0, -1, 2, -1, -1]
def sourceC1795 : Charge := ![3, 0, 1, -3, 0, -1]
def sourceB1796 : Charge := ![1, 0, -1, 1, 1, -2]
def sourceC1796 : Charge := ![3, 0, 1, -2, -2, 0]
def sourceB1797 : Charge := ![1, 0, -1, 1, 1, -2]
def sourceC1797 : Charge := ![3, 0, 1, -2, -2, 0]
def sourceB1798 : Charge := ![1, 0, -1, 1, 0, -1]
def sourceC1798 : Charge := ![3, 0, 1, -2, -1, -1]
def sourceB1800 : Charge := ![1, 0, -1, 1, 0, -1]
def sourceC1800 : Charge := ![3, 0, 1, -2, -1, -1]
def sourceB1803 : Charge := ![1, 0, -1, 1, -1, 0]
def sourceC1803 : Charge := ![3, 0, 1, -2, 0, -2]
def sourceB1804 : Charge := ![1, 0, -1, 1, -1, 0]
def sourceC1804 : Charge := ![3, 0, 1, -2, 0, -2]
def sourceB1807 : Charge := ![1, 0, -1, 0, -1, 1]
def sourceC1807 : Charge := ![3, 0, 1, -1, 0, -3]
def sourceB1809 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC1809 : Charge := ![4, -1, -1, -1, -1, 0]
def sourceB1811 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC1811 : Charge := ![4, -1, -1, -1, -1, 0]
def sourceB1812 : Charge := ![4, -1, -1, -1, -1, 0]
def sourceC1812 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1813 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC1813 : Charge := ![4, -1, -1, -1, 0, -1]
def sourceB1814 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC1814 : Charge := ![4, -1, -1, -1, 0, -1]
def sourceB1815 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC1815 : Charge := ![4, -1, 0, -1, -1, -1]
def sourceB1816 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC1816 : Charge := ![4, -1, 0, -1, -1, -1]
def sourceB1817 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC1817 : Charge := ![4, -1, 0, -1, -1, -1]
def sourceB1818 : Charge := ![4, -1, 0, -1, -1, -1]
def sourceC1818 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1821 : Charge := ![4, 0, 0, -1, -1, -2]
def sourceC1821 : Charge := ![0, 0, 0, 0, 0, 0]
def sourceB1822 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceC1822 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1823 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceC1823 : Charge := ![-4, 0, 1, 1, 1, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB1824 : Charge := ![1, 1, -1, -1, -1, 1]
def sourceC1824 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceB1825 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceC1825 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1826 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceC1826 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1827 : Charge := ![3, -2, 0, 0, 0, -1]
def sourceC1827 : Charge := ![1, 2, -1, -1, -1, 0]
def sourceB1828 : Charge := ![3, -2, 0, 0, 0, -1]
def sourceC1828 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1831 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceC1831 : Charge := ![2, -1, -1, -1, -1, 2]
def sourceB1832 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceC1832 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1833 : Charge := ![2, -1, -1, -1, 0, 1]
def sourceC1833 : Charge := ![2, 1, 0, 0, -1, -2]
def sourceB1834 : Charge := ![2, 1, 0, 0, -1, -2]
def sourceC1834 : Charge := ![2, -1, -1, -1, 0, 1]
def sourceB1835 : Charge := ![2, 1, 0, 0, -1, -2]
def sourceC1835 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1836 : Charge := ![2, 1, 0, 0, -1, -2]
def sourceC1836 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1837 : Charge := ![2, 1, 0, 0, -1, -2]
def sourceC1837 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1838 : Charge := ![2, 1, 0, 0, -1, -2]
def sourceC1838 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1839 : Charge := ![2, 1, 0, 0, -1, -2]
def sourceC1839 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1841 : Charge := ![2, 0, 1, 0, 0, -3]
def sourceC1841 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1842 : Charge := ![2, 0, 1, 0, -1, -2]
def sourceC1842 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1843 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceC1843 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB1844 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceC1844 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB1845 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1845 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceB1846 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1846 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceB1847 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1847 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceB1848 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1848 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceB1850 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1850 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1851 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1851 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1852 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC1852 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB1853 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC1853 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB1854 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1854 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1855 : Charge := ![2, -1, 1, 0, 0, -2]
def sourceC1855 : Charge := ![2, 1, -2, -1, -1, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB1856 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC1856 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceB1857 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC1857 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceB1858 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC1858 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceB1859 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC1859 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceB1860 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC1860 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceB1861 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC1861 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceB1863 : Charge := ![2, -2, 1, 0, 0, -1]
def sourceC1863 : Charge := ![2, 2, -2, -1, -1, 0]
def sourceB1864 : Charge := ![2, -2, 0, 0, 0, 0]
def sourceC1864 : Charge := ![2, 2, -1, -1, -1, -1]
def sourceB1865 : Charge := ![2, -2, 0, 0, 0, 0]
def sourceC1865 : Charge := ![2, 2, -1, -1, -1, -1]
def sourceB1867 : Charge := ![1, 2, 0, 0, -1, -2]
def sourceC1867 : Charge := ![3, -2, -1, -1, 0, 1]
def sourceB1868 : Charge := ![1, 1, 1, 0, -1, -2]
def sourceC1868 : Charge := ![3, -1, -2, -1, 0, 1]
def sourceB1869 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1869 : Charge := ![3, -1, -1, -1, -1, 1]
def sourceB1870 : Charge := ![3, -1, -1, -1, -1, 1]
def sourceC1870 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1871 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1871 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceB1872 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1872 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceB1873 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1873 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceB1874 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC1874 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceB1875 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC1875 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceB1876 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC1876 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1877 : Charge := ![1, 0, 2, 0, -1, -2]
def sourceC1877 : Charge := ![3, 0, -3, -1, 0, 1]
def sourceB1878 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceC1878 : Charge := ![3, 0, -2, -2, 0, 1]
def sourceB1879 : Charge := ![1, 0, 1, 0, 0, -2]
def sourceC1879 : Charge := ![3, 0, -2, -1, -1, 1]
def sourceB1880 : Charge := ![1, 0, 1, 0, -1, -1]
def sourceC1880 : Charge := ![3, 0, -2, -1, 0, 0]
def sourceB1881 : Charge := ![1, 0, 1, 0, -1, -1]
def sourceC1881 : Charge := ![3, 0, -2, -1, 0, 0]
def sourceB1884 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC1884 : Charge := ![3, 0, -1, -1, -1, 0]
def sourceB1885 : Charge := ![1, -1, 2, 0, -1, -1]
def sourceC1885 : Charge := ![3, 1, -3, -1, 0, 0]
def sourceB1886 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceC1886 : Charge := ![3, 1, -2, -2, 0, 0]
def sourceB1887 : Charge := ![1, -1, 0, 0, 0, 0]
def sourceC1887 : Charge := ![3, 1, -1, -1, -1, -1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB1889 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC1889 : Charge := ![4, -1, -1, -1, -1, 0]
def sourceB1890 : Charge := ![4, 0, -1, -1, -1, -1]
def sourceC1890 : Charge := ![0, 0, 0, 0, 0, 0]
def sourceB1891 : Charge := ![0, 1, 0, 0, 2, -3]
def sourceC1891 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceB1892 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceC1892 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1893 : Charge := ![0, 1, 0, 1, 1, -3]
def sourceC1893 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceB1894 : Charge := ![0, 1, 0, 1, 1, -3]
def sourceC1894 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceB1895 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceC1895 : Charge := ![0, 1, 0, 1, 1, -3]
def sourceB1897 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceC1897 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1898 : Charge := ![0, 1, 0, 2, -1, -2]
def sourceC1898 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceB1899 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC1899 : Charge := ![0, 1, 0, 2, -1, -2]
def sourceB1900 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC1900 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1901 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC1901 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1902 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC1902 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1903 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceC1903 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceB1904 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceC1904 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceB1905 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceC1905 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1907 : Charge := ![0, 1, 1, 1, 0, -3]
def sourceC1907 : Charge := ![3, 0, -1, -1, -1, 0]
def sourceB1908 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceC1908 : Charge := ![0, 1, 1, 2, -1, -3]
def sourceB1909 : Charge := ![0, 2, 0, 0, 1, -3]
def sourceC1909 : Charge := ![3, -1, 0, 0, -2, 0]
def sourceB1910 : Charge := ![0, 2, 0, 1, -1, -2]
def sourceC1910 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceB1911 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceC1911 : Charge := ![0, 2, 0, 1, -1, -2]
def sourceB1912 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceC1912 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1913 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceC1913 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1914 : Charge := ![3, -1, 0, -2, 0, 0]
def sourceC1914 : Charge := ![0, 2, 0, 2, -1, -3]
def sourceB1915 : Charge := ![3, -2, 0, 0, 0, -1]
def sourceC1915 : Charge := ![0, 3, 0, 0, -1, -2]
def sourceB1916 : Charge := ![3, -2, 0, 0, 0, -1]
def sourceC1916 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1917 : Charge := ![1, 0, 0, 2, -1, -2]
def sourceC1917 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceB1918 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC1918 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1919 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC1919 : Charge := ![-3, -1, 0, 0, 1, 3]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB192 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceC192 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceB193 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceC193 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceB197 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceC197 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceB198 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceC198 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceB199 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceC199 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceB200 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceC200 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceB201 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceC201 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceB203 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC203 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceB205 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC205 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceB206 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC206 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceB207 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC207 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceB208 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC208 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceB209 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC209 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceB210 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC210 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceB211 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC211 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceB214 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC214 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB215 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC215 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB217 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC217 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB219 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC219 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB222 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC222 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceB223 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC223 : Charge := ![2, 1, 0, 0, -3, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB1920 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceC1920 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceB1921 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC1921 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1923 : Charge := ![1, 1, -1, 0, 1, -2]
def sourceC1923 : Charge := ![2, 0, 1, 0, -2, -1]
def sourceB1924 : Charge := ![1, 1, -1, 0, 1, -2]
def sourceC1924 : Charge := ![2, 0, 1, 0, -2, -1]
def sourceB1925 : Charge := ![2, 0, 1, 0, -2, -1]
def sourceC1925 : Charge := ![1, 1, -1, 0, 1, -2]
def sourceB1926 : Charge := ![2, 0, 1, 0, -2, -1]
def sourceC1926 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1927 : Charge := ![2, 0, 1, 0, -2, -1]
def sourceC1927 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1929 : Charge := ![2, 0, 1, 0, -2, -1]
def sourceC1929 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1930 : Charge := ![2, 0, 1, 0, -2, -1]
def sourceC1930 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1931 : Charge := ![2, 0, 1, 0, -3, 0]
def sourceC1931 : Charge := ![1, 1, -1, 0, 2, -3]
def sourceB1932 : Charge := ![1, 1, -1, 1, -1, -1]
def sourceC1932 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceB1933 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceC1933 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1934 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceC1934 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1935 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceC1935 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1936 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceC1936 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1937 : Charge := ![1, 1, -1, 1, 0, -2]
def sourceC1937 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceB1938 : Charge := ![1, 1, -1, 1, 0, -2]
def sourceC1938 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceB1939 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC1939 : Charge := ![1, 1, -1, 1, 1, -3]
def sourceB1940 : Charge := ![2, 0, 1, -2, 0, -1]
def sourceC1940 : Charge := ![1, 1, -1, 2, -1, -2]
def sourceB1942 : Charge := ![2, 0, 1, -2, -1, 0]
def sourceC1942 : Charge := ![1, 1, -1, 2, 0, -3]
def sourceB1943 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1943 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB1944 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1944 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB1945 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1945 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceB1946 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1946 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceB1947 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1947 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB1948 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1948 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB1949 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1949 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1950 : Charge := ![1, 1, 0, 0, 1, -3]
def sourceC1950 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceB1951 : Charge := ![1, 1, 0, 0, 1, -3]
def sourceC1951 : Charge := ![2, 0, 0, 0, -2, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB1952 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1952 : Charge := ![1, 1, 0, 0, 1, -3]
def sourceB1953 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1953 : Charge := ![1, 1, 0, 0, 1, -3]
def sourceB1954 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1954 : Charge := ![1, 1, 0, 0, 1, -3]
def sourceB1955 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1955 : Charge := ![1, 1, 0, 0, 1, -3]
def sourceB1956 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1956 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1957 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1957 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1958 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceC1958 : Charge := ![2, 0, 0, -1, 1, -2]
def sourceB1959 : Charge := ![2, 0, 0, -1, 1, -2]
def sourceC1959 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceB1960 : Charge := ![2, 0, 0, -1, 1, -2]
def sourceC1960 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceB1961 : Charge := ![2, 0, 0, -1, 1, -2]
def sourceC1961 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1962 : Charge := ![2, 0, 0, -1, 1, -2]
def sourceC1962 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1965 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1965 : Charge := ![1, 1, 0, 1, -1, -2]
def sourceB1966 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1966 : Charge := ![1, 1, 0, 1, -1, -2]
def sourceB1967 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1967 : Charge := ![1, 1, 0, 1, -1, -2]
def sourceB1968 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1968 : Charge := ![1, 1, 0, 1, -1, -2]
def sourceB1971 : Charge := ![1, 1, 0, 1, 0, -3]
def sourceC1971 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceB1973 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1973 : Charge := ![1, 1, 0, 1, 0, -3]
def sourceB1974 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1974 : Charge := ![1, 1, 0, 1, 0, -3]
def sourceB1975 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1975 : Charge := ![1, 1, 0, 1, 0, -3]
def sourceB1976 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1976 : Charge := ![1, 1, 0, 1, 0, -3]
def sourceB1977 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1977 : Charge := ![1, 1, 0, 1, 0, -3]
def sourceB1978 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1978 : Charge := ![1, 1, 0, 1, 0, -3]
def sourceB1979 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1979 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1981 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC1981 : Charge := ![1, 1, 0, 2, -2, -2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB1987 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC1987 : Charge := ![1, 1, 1, 1, -1, -3]
def sourceB1991 : Charge := ![2, -1, 1, 0, -2, 0]
def sourceC1991 : Charge := ![1, 2, -1, 0, 1, -3]
def sourceB1993 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC1993 : Charge := ![1, 2, 0, 0, -2, -1]
def sourceB1996 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC1996 : Charge := ![1, 2, 0, 0, -1, -2]
def sourceB1997 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC1997 : Charge := ![1, 2, 0, 0, -1, -2]
def sourceB1998 : Charge := ![1, 2, 0, 0, 0, -3]
def sourceC1998 : Charge := ![2, -1, 0, 0, -1, 0]
def sourceB2000 : Charge := ![2, -1, 0, 0, -1, 0]
def sourceC2000 : Charge := ![1, 2, 0, 0, 0, -3]
def sourceB2001 : Charge := ![2, -1, 0, 0, -1, 0]
def sourceC2001 : Charge := ![1, 2, 0, 0, 0, -3]
def sourceB2002 : Charge := ![2, -1, 0, 0, -1, 0]
def sourceC2002 : Charge := ![1, 2, 0, 0, 0, -3]
def sourceB2003 : Charge := ![2, -1, 0, 0, -1, 0]
def sourceC2003 : Charge := ![1, 2, 0, 0, 0, -3]
def sourceB2008 : Charge := ![1, 2, 0, 0, -3, 0]
def sourceC2008 : Charge := ![2, -1, 0, 0, 2, -3]
def sourceB2009 : Charge := ![1, 2, 0, -1, -2, 0]
def sourceC2009 : Charge := ![2, -1, 0, 1, 1, -3]
def sourceB2011 : Charge := ![1, 2, 0, -2, 0, -1]
def sourceC2011 : Charge := ![2, -1, 0, 2, -1, -2]
def sourceB2012 : Charge := ![1, 2, 0, -2, -1, 0]
def sourceC2012 : Charge := ![2, -1, 0, 2, 0, -3]
def sourceB2014 : Charge := ![1, 2, -1, -1, 0, -1]
def sourceC2014 : Charge := ![2, -1, 1, 1, -1, -2]
def sourceB2015 : Charge := ![1, 2, -1, -1, -1, 0]
def sourceC2015 : Charge := ![2, -1, 1, 1, 0, -3]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB2016 : Charge := ![1, 1, 1, 0, -3, 0]
def sourceC2016 : Charge := ![2, 0, -1, 0, 2, -3]
def sourceB2017 : Charge := ![1, 1, 1, -1, -2, 0]
def sourceC2017 : Charge := ![2, 0, -1, 1, 1, -3]
def sourceB2018 : Charge := ![1, 1, 1, -2, 0, -1]
def sourceC2018 : Charge := ![2, 0, -1, 2, -1, -2]
def sourceB2019 : Charge := ![1, 1, 1, -2, 0, -1]
def sourceC2019 : Charge := ![2, 0, -1, 2, -1, -2]
def sourceB2020 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceC2020 : Charge := ![2, 0, -1, 2, 0, -3]
def sourceB2021 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC2021 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceB2022 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC2022 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceB2023 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC2023 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceB2024 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC2024 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceB2025 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC2025 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceB2026 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC2026 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceB2027 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceC2027 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceB2028 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceC2028 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceB2031 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2031 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceB2032 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2032 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceB2033 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2033 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceB2034 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2034 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceB2035 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2035 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceB2036 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceC2036 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceB2039 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC2039 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceB2040 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC2040 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceB2041 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC2041 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceB2042 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC2042 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceB2043 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC2043 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceB2044 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC2044 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceB2045 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC2045 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceB2046 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceC2046 : Charge := ![1, 1, 0, -1, -1, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB2051 : Charge := ![1, 1, 0, -2, 1, -1]
def sourceC2051 : Charge := ![2, 0, 0, 2, -2, -2]
def sourceB2052 : Charge := ![1, 1, 0, -2, 0, 0]
def sourceC2052 : Charge := ![2, 0, 0, 2, -1, -3]
def sourceB2054 : Charge := ![1, 1, 0, -2, 0, 0]
def sourceC2054 : Charge := ![2, 0, 0, 2, -1, -3]
def sourceB2056 : Charge := ![1, 1, -1, -1, 1, -1]
def sourceC2056 : Charge := ![2, 0, 1, 1, -2, -2]
def sourceB2057 : Charge := ![1, 1, -1, -1, 1, -1]
def sourceC2057 : Charge := ![2, 0, 1, 1, -2, -2]
def sourceB2059 : Charge := ![1, 1, -1, -1, 0, 0]
def sourceC2059 : Charge := ![2, 0, 1, 1, -1, -3]
def sourceB2061 : Charge := ![1, 0, 1, 0, -2, 0]
def sourceC2061 : Charge := ![2, 1, -1, 0, 1, -3]
def sourceB2062 : Charge := ![1, 0, 1, 0, -2, 0]
def sourceC2062 : Charge := ![2, 1, -1, 0, 1, -3]
def sourceB2064 : Charge := ![2, 1, -1, 0, 1, -3]
def sourceC2064 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2065 : Charge := ![1, 0, 1, -1, 0, -1]
def sourceC2065 : Charge := ![2, 1, -1, 1, -1, -2]
def sourceB2072 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC2072 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceB2073 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC2073 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceB2074 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceC2074 : Charge := ![2, 1, 0, 1, -2, -2]
def sourceB2077 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceC2077 : Charge := ![2, 1, 0, 1, -2, -2]
def sourceB2079 : Charge := ![1, 0, 0, -1, 0, 0]
def sourceC2079 : Charge := ![2, 1, 0, 1, -1, -3]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB2084 : Charge := ![2, 2, 0, 0, -1, -3]
def sourceC2084 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2085 : Charge := ![0, 1, 0, 0, -1, 0]
def sourceC2085 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceB2086 : Charge := ![0, 1, 0, 0, -1, 0]
def sourceC2086 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceB2087 : Charge := ![0, 1, 0, 0, -1, 0]
def sourceC2087 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceB2088 : Charge := ![0, 1, 0, -1, 0, 0]
def sourceC2088 : Charge := ![3, 0, 0, 1, -1, -3]
def sourceB2089 : Charge := ![3, 1, 0, 0, -1, -3]
def sourceC2089 : Charge := ![0, 0, 0, 0, 0, 0]
def sourceB2091 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC2091 : Charge := ![0, 1, 0, 2, -2, -1]
def sourceB2092 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC2092 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2093 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceC2093 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceB2094 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceC2094 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceB2095 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceC2095 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2097 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceC2097 : Charge := ![0, 1, 1, 2, -2, -2]
def sourceB2098 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceC2098 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceB2099 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceC2099 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceB2100 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceC2100 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2101 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceC2101 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2102 : Charge := ![3, -1, 0, -2, 0, 0]
def sourceC2102 : Charge := ![0, 2, 0, 2, -2, -2]
def sourceB2103 : Charge := ![3, -2, 0, 0, 0, -1]
def sourceC2103 : Charge := ![0, 3, 0, 0, -2, -1]
def sourceB2104 : Charge := ![3, -2, 0, -1, 0, 0]
def sourceC2104 : Charge := ![0, 3, 0, 1, -2, -2]
def sourceB2105 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceC2105 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceB2106 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC2106 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceB2108 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC2108 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2110 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC2110 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2111 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceC2111 : Charge := ![2, 1, -1, -1, 0, -1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB2112 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC2112 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceB2114 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC2114 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2115 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC2115 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2118 : Charge := ![1, 1, -1, 0, -2, 1]
def sourceC2118 : Charge := ![2, 0, 1, 0, 0, -3]
def sourceB2119 : Charge := ![2, 0, 1, 0, 0, -3]
def sourceC2119 : Charge := ![1, 1, -1, 0, -2, 1]
def sourceB2120 : Charge := ![2, 0, 1, 0, 0, -3]
def sourceC2120 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2121 : Charge := ![2, 0, 1, 0, 0, -3]
def sourceC2121 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2122 : Charge := ![1, 1, -1, 1, -2, 0]
def sourceC2122 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceB2123 : Charge := ![1, 1, -1, 1, -2, 0]
def sourceC2123 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceB2124 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceC2124 : Charge := ![1, 1, -1, 1, -2, 0]
def sourceB2125 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceC2125 : Charge := ![1, 1, -1, 1, -2, 0]
def sourceB2126 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceC2126 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2129 : Charge := ![1, 1, -1, 1, -1, -1]
def sourceC2129 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceB2130 : Charge := ![1, 1, -1, 1, -1, -1]
def sourceC2130 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceB2132 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceC2132 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2133 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceC2133 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2134 : Charge := ![2, 0, 1, -2, 0, -1]
def sourceC2134 : Charge := ![1, 1, -1, 2, -2, -1]
def sourceB2135 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC2135 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB2136 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC2136 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB2137 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC2137 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceB2138 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC2138 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceB2139 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC2139 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2140 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC2140 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2141 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC2141 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB2142 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC2142 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB2143 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC2143 : Charge := ![1, 1, 0, 0, -1, -1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources67
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB2144 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC2144 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceB2145 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC2145 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2146 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC2146 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2147 : Charge := ![1, 1, 0, 1, -3, 0]
def sourceC2147 : Charge := ![2, 0, 0, -1, 1, -2]
def sourceB2148 : Charge := ![2, 0, 0, -1, 1, -2]
def sourceC2148 : Charge := ![1, 1, 0, 1, -3, 0]
def sourceB2149 : Charge := ![2, 0, 0, -1, 1, -2]
def sourceC2149 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2152 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC2152 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceB2153 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC2153 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceB2154 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC2154 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceB2155 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC2155 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceB2156 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC2156 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceB2157 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC2157 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceB2160 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC2160 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2161 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC2161 : Charge := ![1, 1, 0, 2, -3, -1]
def sourceB2168 : Charge := ![1, 2, -1, 0, -2, 0]
def sourceC2168 : Charge := ![2, -1, 1, 0, 0, -2]
def sourceB2169 : Charge := ![2, -1, 1, 0, 0, -2]
def sourceC2169 : Charge := ![1, 2, -1, 0, -2, 0]
def sourceB2170 : Charge := ![2, -1, 1, 0, 0, -2]
def sourceC2170 : Charge := ![1, 2, -1, 0, -2, 0]
def sourceB2171 : Charge := ![2, -1, 1, 0, 0, -2]
def sourceC2171 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2172 : Charge := ![2, -1, 1, 0, 0, -2]
def sourceC2172 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2175 : Charge := ![2, -1, 1, 0, -1, -1]
def sourceC2175 : Charge := ![1, 2, -1, 0, -1, -1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB2176 : Charge := ![2, -1, 1, 0, -1, -1]
def sourceC2176 : Charge := ![1, 2, -1, 0, -1, -1]
def sourceB2177 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC2177 : Charge := ![1, 2, 0, 0, -3, 0]
def sourceB2180 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC2180 : Charge := ![1, 2, 0, 0, -2, -1]
def sourceB2181 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC2181 : Charge := ![1, 2, 0, 0, -2, -1]
def sourceB2182 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC2182 : Charge := ![1, 2, 0, 0, -2, -1]
def sourceB2189 : Charge := ![1, 1, 1, -2, 0, -1]
def sourceC2189 : Charge := ![2, 0, -1, 2, -2, -1]
def sourceB2190 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2190 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceB2191 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2191 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceB2192 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2192 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceB2193 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2193 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceB2194 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2194 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceB2195 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2195 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceB2196 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2196 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceB2197 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceC2197 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceB2203 : Charge := ![1, 1, -1, -1, 0, 0]
def sourceC2203 : Charge := ![2, 0, 1, 1, -2, -2]
def sourceB2207 : Charge := ![1, 0, 2, -1, -1, -1]
def sourceC2207 : Charge := ![2, 1, -2, 1, -1, -1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB2210 : Charge := ![1, 0, 1, 0, 0, -2]
def sourceC2210 : Charge := ![2, 1, -1, 0, -2, 0]
def sourceB2211 : Charge := ![1, 0, 1, 0, 0, -2]
def sourceC2211 : Charge := ![2, 1, -1, 0, -2, 0]
def sourceB2212 : Charge := ![1, 0, 1, 0, 0, -2]
def sourceC2212 : Charge := ![2, 1, -1, 0, -2, 0]
def sourceB2217 : Charge := ![1, 0, 1, 0, -1, -1]
def sourceC2217 : Charge := ![2, 1, -1, 0, -1, -1]
def sourceB2218 : Charge := ![1, 0, 1, 0, -1, -1]
def sourceC2218 : Charge := ![2, 1, -1, 0, -1, -1]
def sourceB2219 : Charge := ![1, 0, 1, 0, -1, -1]
def sourceC2219 : Charge := ![2, 1, -1, 0, -1, -1]
def sourceB2229 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceC2229 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceB2230 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceC2230 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceB2235 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC2235 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceB2236 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC2236 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceB2238 : Charge := ![1, 0, 0, -1, 0, 0]
def sourceC2238 : Charge := ![2, 1, 0, 1, -2, -2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB224 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC224 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceB225 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC225 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceB226 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC226 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceB227 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC227 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceB228 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC228 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceB229 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC229 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceB230 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC230 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceB231 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC231 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceB233 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC233 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceB234 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC234 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceB235 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC235 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceB236 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC236 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceB237 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC237 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceB238 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC238 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceB239 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC239 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceB240 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC240 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceB241 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC241 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceB244 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC244 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB245 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC245 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB246 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC246 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB247 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC247 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB250 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC250 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB251 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC251 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB253 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC253 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceB254 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC254 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceB255 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC255 : Charge := ![2, 1, 0, -1, -2, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB2244 : Charge := ![1, -1, 1, 1, 0, -2]
def sourceC2244 : Charge := ![2, 2, -1, -1, -2, 0]
def sourceB2245 : Charge := ![1, -1, 1, 0, 0, -1]
def sourceC2245 : Charge := ![2, 2, -1, 0, -2, -1]
def sourceB2249 : Charge := ![1, -1, 0, 0, 0, 0]
def sourceC2249 : Charge := ![2, 2, 0, 0, -2, -2]
def sourceB2251 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceC2251 : Charge := ![3, -1, 0, 0, -2, 0]
def sourceB2252 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceC2252 : Charge := ![3, -1, 0, 0, -2, 0]
def sourceB2253 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceC2253 : Charge := ![3, -1, 0, 0, -2, 0]
def sourceB2254 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceC2254 : Charge := ![3, -1, 0, 0, -2, 0]
def sourceB2255 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceC2255 : Charge := ![3, -1, 0, 0, -2, 0]
def sourceB2256 : Charge := ![3, -1, 0, 0, -2, 0]
def sourceC2256 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceB2257 : Charge := ![3, -1, 0, 0, -2, 0]
def sourceC2257 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceB2259 : Charge := ![3, -1, 0, 0, -2, 0]
def sourceC2259 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2260 : Charge := ![3, -1, 0, 0, -2, 0]
def sourceC2260 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2261 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC2261 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceB2262 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC2262 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceB2263 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC2263 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceB2264 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC2264 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceB2265 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC2265 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceB2266 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceC2266 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceB2267 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceC2267 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceB2268 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceC2268 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2269 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceC2269 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2271 : Charge := ![0, 2, 0, -1, 0, -1]
def sourceC2271 : Charge := ![3, -1, 0, 1, -2, -1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB2273 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC2273 : Charge := ![3, 0, -1, 0, -2, 0]
def sourceB2274 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC2274 : Charge := ![3, 0, -1, 0, -2, 0]
def sourceB2275 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC2275 : Charge := ![3, 0, -1, 0, -2, 0]
def sourceB2276 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC2276 : Charge := ![3, 0, -1, 0, -2, 0]
def sourceB2277 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC2277 : Charge := ![3, 0, -1, 0, -2, 0]
def sourceB2278 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC2278 : Charge := ![3, 0, -1, 0, -2, 0]
def sourceB2279 : Charge := ![3, 0, -1, 0, -2, 0]
def sourceC2279 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceB2283 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC2283 : Charge := ![3, 0, -1, 0, -1, -1]
def sourceB2284 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC2284 : Charge := ![3, 0, -1, 0, -1, -1]
def sourceB2285 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC2285 : Charge := ![3, 0, -1, 0, -1, -1]
def sourceB2286 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC2286 : Charge := ![3, 0, -1, 0, -1, -1]
def sourceB2287 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC2287 : Charge := ![3, 0, -1, 0, -1, -1]
def sourceB2288 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC2288 : Charge := ![3, 0, -1, 0, -1, -1]
def sourceB2289 : Charge := ![3, 0, -1, 0, -1, -1]
def sourceC2289 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceB2291 : Charge := ![3, 0, -1, 0, -1, -1]
def sourceC2291 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2295 : Charge := ![0, 1, 0, 0, 1, -2]
def sourceC2295 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceB2296 : Charge := ![0, 1, 0, 0, 1, -2]
def sourceC2296 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceB2297 : Charge := ![0, 1, 0, 0, 1, -2]
def sourceC2297 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceB2298 : Charge := ![0, 1, 0, 0, 1, -2]
def sourceC2298 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceB2302 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC2302 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceB2303 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC2303 : Charge := ![3, 0, 0, 0, -2, -1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB2304 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC2304 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceB2308 : Charge := ![0, 0, 1, 0, 0, -1]
def sourceC2308 : Charge := ![3, 1, -1, 0, -2, -1]
def sourceB2310 : Charge := ![3, 1, -1, 0, -2, -1]
def sourceC2310 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2311 : Charge := ![3, 1, 0, 0, -2, -2]
def sourceC2311 : Charge := ![0, 0, 0, 0, 0, 0]
def sourceB2312 : Charge := ![0, 1, 1, -1, 1, -2]
def sourceC2312 : Charge := ![3, 0, -1, 0, -2, 0]
def sourceB2313 : Charge := ![3, 0, -1, 0, -2, 0]
def sourceC2313 : Charge := ![0, 1, 1, -1, 1, -2]
def sourceB2315 : Charge := ![0, 1, 2, -1, -1, -1]
def sourceC2315 : Charge := ![3, 0, -2, 0, 0, -1]
def sourceB2316 : Charge := ![3, 0, -2, 0, 0, -1]
def sourceC2316 : Charge := ![0, 1, 2, -1, -1, -1]
def sourceB2318 : Charge := ![3, 0, -2, 0, -1, 0]
def sourceC2318 : Charge := ![0, 1, 2, -1, 0, -2]
def sourceB2319 : Charge := ![3, -1, 0, 0, -2, 0]
def sourceC2319 : Charge := ![0, 2, 0, -1, 1, -2]
def sourceB2320 : Charge := ![0, 2, 1, -1, -1, -1]
def sourceC2320 : Charge := ![3, -1, -1, 0, 0, -1]
def sourceB2321 : Charge := ![3, -1, -1, 0, 0, -1]
def sourceC2321 : Charge := ![0, 2, 1, -1, -1, -1]
def sourceB2322 : Charge := ![0, 2, 1, -1, 0, -2]
def sourceC2322 : Charge := ![3, -1, -1, 0, -1, 0]
def sourceB2323 : Charge := ![3, -1, -1, 0, -1, 0]
def sourceC2323 : Charge := ![0, 2, 1, -1, 0, -2]
def sourceB2325 : Charge := ![3, -2, 0, 0, 0, -1]
def sourceC2325 : Charge := ![0, 3, 0, -1, -1, -1]
def sourceB2326 : Charge := ![3, -2, 0, 0, -1, 0]
def sourceC2326 : Charge := ![0, 3, 0, -1, 0, -2]
def sourceB2327 : Charge := ![1, 0, 1, -1, 1, -2]
def sourceC2327 : Charge := ![2, 1, -1, 0, -2, 0]
def sourceB2328 : Charge := ![2, 1, -1, 0, -2, 0]
def sourceC2328 : Charge := ![1, 0, 1, -1, 1, -2]
def sourceB2330 : Charge := ![1, 0, 2, -1, -1, -1]
def sourceC2330 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceB2331 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC2331 : Charge := ![1, 0, 2, -1, -1, -1]
def sourceB2333 : Charge := ![2, 1, -2, 0, -1, 0]
def sourceC2333 : Charge := ![1, 0, 2, -1, 0, -2]
def sourceB2334 : Charge := ![1, 1, -1, -1, -1, 1]
def sourceC2334 : Charge := ![2, 0, 1, 0, 0, -3]
def sourceB2335 : Charge := ![1, 1, -1, -1, 1, -1]
def sourceC2335 : Charge := ![2, 0, 1, 0, -2, -1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB2336 : Charge := ![1, 1, -1, 0, 1, -2]
def sourceC2336 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceB2337 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC2337 : Charge := ![1, 1, -1, 0, 1, -2]
def sourceB2338 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC2338 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB2339 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC2339 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB2340 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC2340 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceB2341 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC2341 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceB2342 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2342 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB2343 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2343 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB2344 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC2344 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceB2345 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC2345 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceB2348 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC2348 : Charge := ![1, 1, 0, -1, 1, -2]
def sourceB2349 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC2349 : Charge := ![1, 1, 0, -1, 1, -2]
def sourceB2350 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC2350 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceB2351 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC2351 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceB2352 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC2352 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceB2353 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC2353 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceB2354 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC2354 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2355 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceC2355 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceB2356 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceC2356 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceB2357 : Charge := ![1, 1, 1, -2, 0, -1]
def sourceC2357 : Charge := ![2, 0, -1, 1, -1, -1]
def sourceB2358 : Charge := ![2, 0, -1, 1, -1, -1]
def sourceC2358 : Charge := ![1, 1, 1, -2, 0, -1]
def sourceB2359 : Charge := ![2, 0, -1, 1, -2, 0]
def sourceC2359 : Charge := ![1, 1, 1, -2, 1, -2]
def sourceB2365 : Charge := ![2, 0, -1, 0, -1, 0]
def sourceC2365 : Charge := ![1, 1, 1, -1, 0, -2]
def sourceB2366 : Charge := ![2, 0, -1, 0, -1, 0]
def sourceC2366 : Charge := ![1, 1, 1, -1, 0, -2]
def sourceB2367 : Charge := ![2, 0, -1, 0, -1, 0]
def sourceC2367 : Charge := ![1, 1, 1, -1, 0, -2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources74
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB2368 : Charge := ![2, 0, -1, 0, -1, 0]
def sourceC2368 : Charge := ![1, 1, 1, -1, 0, -2]
def sourceB2370 : Charge := ![1, 1, 1, 0, 0, -3]
def sourceC2370 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceB2371 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceC2371 : Charge := ![1, 1, 1, 0, 0, -3]
def sourceB2374 : Charge := ![2, -1, 1, 0, 0, -2]
def sourceC2374 : Charge := ![1, 2, -1, -1, -1, 0]
def sourceB2375 : Charge := ![2, -1, 1, 0, -1, -1]
def sourceC2375 : Charge := ![1, 2, -1, -1, 0, -1]
def sourceB2376 : Charge := ![2, -1, 1, -1, -1, 0]
def sourceC2376 : Charge := ![1, 2, -1, 0, 0, -2]
def sourceB2377 : Charge := ![2, -1, 1, -1, -1, 0]
def sourceC2377 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2378 : Charge := ![2, -1, 0, 1, 0, -2]
def sourceC2378 : Charge := ![1, 2, 0, -2, -1, 0]
def sourceB2382 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC2382 : Charge := ![1, 2, 0, -1, -1, -1]
def sourceB2383 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC2383 : Charge := ![1, 2, 0, -1, -1, -1]
def sourceB2386 : Charge := ![2, -1, 0, 0, -1, 0]
def sourceC2386 : Charge := ![1, 2, 0, -1, 0, -2]
def sourceB2387 : Charge := ![2, -1, 0, 0, -1, 0]
def sourceC2387 : Charge := ![1, 2, 0, -1, 0, -2]
def sourceB2388 : Charge := ![2, -1, 0, -1, -1, 1]
def sourceC2388 : Charge := ![1, 2, 0, 0, 0, -3]
def sourceB2390 : Charge := ![1, 2, -2, 0, 0, -1]
def sourceC2390 : Charge := ![2, -1, 2, -1, -1, -1]
def sourceB2391 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC2391 : Charge := ![2, 0, 0, -1, 1, -2]
def sourceB2392 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC2392 : Charge := ![2, 0, 0, -1, 1, -2]
def sourceB2393 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC2393 : Charge := ![2, 0, 0, -1, 1, -2]
def sourceB2394 : Charge := ![2, 0, 0, -1, 1, -2]
def sourceC2394 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceB2397 : Charge := ![1, 1, -1, 0, 0, -1]
def sourceC2397 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceB2398 : Charge := ![1, 1, -1, 0, 0, -1]
def sourceC2398 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceB2399 : Charge := ![1, 1, -1, 0, 0, -1]
def sourceC2399 : Charge := ![2, 0, 1, -1, -1, -1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB2400 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceC2400 : Charge := ![1, 1, -1, 0, 0, -1]
def sourceB2402 : Charge := ![1, 1, -1, 0, -1, 0]
def sourceC2402 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceB2403 : Charge := ![1, 1, -1, 0, -1, 0]
def sourceC2403 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceB2404 : Charge := ![1, 1, -1, 0, -1, 0]
def sourceC2404 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceB2405 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceC2405 : Charge := ![1, 1, -1, 0, -1, 0]
def sourceB2410 : Charge := ![1, 0, 1, 0, -1, -1]
def sourceC2410 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceB2411 : Charge := ![1, 0, 1, 0, -1, -1]
def sourceC2411 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceB2415 : Charge := ![2, 1, -1, -1, 1, -2]
def sourceC2415 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2416 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceC2416 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceB2417 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceC2417 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceB2425 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceC2425 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceB2426 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceC2426 : Charge := ![2, 1, 0, 0, 0, -3]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB2439 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceC2439 : Charge := ![3, -1, 0, -1, -1, 0]
def sourceB2440 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceC2440 : Charge := ![3, -1, 0, -1, -1, 0]
def sourceB2441 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceC2441 : Charge := ![3, -1, 0, -1, -1, 0]
def sourceB2442 : Charge := ![3, -1, 0, -1, -1, 0]
def sourceC2442 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceB2443 : Charge := ![3, -1, 0, -1, -1, 0]
def sourceC2443 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceB2445 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC2445 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceB2446 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC2446 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceB2447 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC2447 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceB2448 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceC2448 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceB2449 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceC2449 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceB2450 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceC2450 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2451 : Charge := ![0, 2, 0, -1, -1, 0]
def sourceC2451 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceB2452 : Charge := ![0, 2, 0, -1, -1, 0]
def sourceC2452 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceB2453 : Charge := ![0, 2, 0, -1, -1, 0]
def sourceC2453 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceB2454 : Charge := ![0, 2, 0, -1, -1, 0]
def sourceC2454 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceB2455 : Charge := ![0, 2, 0, -1, -1, 0]
def sourceC2455 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceB2456 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceC2456 : Charge := ![0, 2, 0, -1, -1, 0]
def sourceB2457 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceC2457 : Charge := ![0, 2, 0, -1, -1, 0]
def sourceB2458 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceC2458 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2460 : Charge := ![0, 2, -1, 0, 0, -1]
def sourceC2460 : Charge := ![3, -1, 1, -1, -1, -1]
def sourceB2461 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC2461 : Charge := ![3, 0, -1, -1, -1, 0]
def sourceB2462 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC2462 : Charge := ![3, 0, -1, -1, -1, 0]
def sourceB2463 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC2463 : Charge := ![3, 0, -1, -1, -1, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB2464 : Charge := ![3, 0, -1, -1, -1, 0]
def sourceC2464 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceB2466 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC2466 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceB2467 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC2467 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceB2468 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC2468 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceB2469 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC2469 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceB2470 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceC2470 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceB2471 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceC2471 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2472 : Charge := ![0, 1, 1, -1, -1, 0]
def sourceC2472 : Charge := ![3, 0, -1, 0, 0, -2]
def sourceB2473 : Charge := ![0, 1, 1, -1, -1, 0]
def sourceC2473 : Charge := ![3, 0, -1, 0, 0, -2]
def sourceB2474 : Charge := ![0, 1, 1, -1, -1, 0]
def sourceC2474 : Charge := ![3, 0, -1, 0, 0, -2]
def sourceB2475 : Charge := ![3, 0, -1, 0, 0, -2]
def sourceC2475 : Charge := ![0, 1, 1, -1, -1, 0]
def sourceB2476 : Charge := ![3, 0, -1, 0, 0, -2]
def sourceC2476 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2477 : Charge := ![0, 1, 0, 1, 0, -2]
def sourceC2477 : Charge := ![3, 0, 0, -2, -1, 0]
def sourceB2478 : Charge := ![0, 1, 0, 1, 0, -2]
def sourceC2478 : Charge := ![3, 0, 0, -2, -1, 0]
def sourceB2479 : Charge := ![0, 1, 0, 1, 0, -2]
def sourceC2479 : Charge := ![3, 0, 0, -2, -1, 0]
def sourceB2481 : Charge := ![3, 0, 0, -2, -1, 0]
def sourceC2481 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2482 : Charge := ![0, 1, 0, 1, -1, -1]
def sourceC2482 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceB2483 : Charge := ![0, 1, 0, 1, -1, -1]
def sourceC2483 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceB2484 : Charge := ![0, 1, 0, 1, -1, -1]
def sourceC2484 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceB2485 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC2485 : Charge := ![0, 1, 0, 1, -1, -1]
def sourceB2486 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC2486 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2487 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC2487 : Charge := ![3, 0, 0, -1, -1, -1]
def sourceB2488 : Charge := ![0, 1, 0, 0, -1, 0]
def sourceC2488 : Charge := ![3, 0, 0, -1, 0, -2]
def sourceB2489 : Charge := ![0, 1, 0, -1, -1, 1]
def sourceC2489 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceB2491 : Charge := ![0, 1, 0, -1, -1, 1]
def sourceC2491 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceB2492 : Charge := ![0, 1, 0, -1, -1, 1]
def sourceC2492 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceB2493 : Charge := ![0, 1, 0, -1, -1, 1]
def sourceC2493 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceB2494 : Charge := ![0, 1, -1, 0, 0, 0]
def sourceC2494 : Charge := ![3, 0, 1, -1, -1, -2]
def sourceB2495 : Charge := ![3, 1, -1, -1, -1, -1]
def sourceC2495 : Charge := ![-3, -1, 0, 1, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB2496 : Charge := ![3, 1, 0, -1, -1, -2]
def sourceC2496 : Charge := ![0, 0, 0, 0, 0, 0]
def sourceB2497 : Charge := ![3, -2, 0, 0, 0, -1]
def sourceC2497 : Charge := ![0, 3, -1, -1, -1, 0]
def sourceB2499 : Charge := ![1, 1, -1, -1, 0, 0]
def sourceC2499 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB2500 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC2500 : Charge := ![1, 1, -1, -1, 0, 0]
def sourceB2502 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC2502 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceB2503 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC2503 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceB2504 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceC2504 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceB2508 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC2508 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceB2509 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC2509 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceB2510 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC2510 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceB2511 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC2511 : Charge := ![-3, -1, 1, 1, 1, 1]
def sourceB2512 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC2512 : Charge := ![3, 0, -2, -1, 0, 0]
def sourceB2513 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC2513 : Charge := ![3, 0, -2, -1, 0, 0]
def sourceB2514 : Charge := ![3, 1, -1, -1, -1, -1]
def sourceC2514 : Charge := ![0, 0, 0, 0, 0, 0]
def sourceB2515 : Charge := ![-1, 2, 0, 1, -2, 0]
def sourceC2515 : Charge := ![3, 0, 0, -1, 0, -2]
def sourceB2516 : Charge := ![3, 0, 0, -1, 0, -2]
def sourceC2516 : Charge := ![-1, 2, 0, 1, -2, 0]
def sourceB2519 : Charge := ![0, 1, 0, 2, -2, -1]
def sourceC2519 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceB2520 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceC2520 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceB2521 : Charge := ![0, 2, -1, 1, -2, 0]
def sourceC2521 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceB2522 : Charge := ![0, 2, -1, 1, -1, -1]
def sourceC2522 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceB2523 : Charge := ![0, 2, -1, 1, -1, -1]
def sourceC2523 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceB2524 : Charge := ![0, 2, 0, 0, -2, 0]
def sourceC2524 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB2525 : Charge := ![0, 2, 0, 0, -2, 0]
def sourceC2525 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB2526 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC2526 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2527 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC2527 : Charge := ![2, 0, 0, 0, -1, -1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB2528 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC2528 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB2529 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC2529 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2532 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC2532 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceB2533 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC2533 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceB2534 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC2534 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceB2535 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC2535 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceB2536 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC2536 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceB2537 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC2537 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceB2545 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC2545 : Charge := ![0, 3, 0, 0, -2, -1]
def sourceB2546 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC2546 : Charge := ![0, 3, 0, 0, -2, -1]
def sourceB2547 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC2547 : Charge := ![0, 3, 0, 0, -2, -1]
def sourceB2550 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC2550 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceB2551 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC2551 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceB2552 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC2552 : Charge := ![-2, -2, 0, 0, 2, 2]

def sourceA2553 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2553 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2553 : Charge := ![1, 1, 0, 1, -2, -1]

def sourceA2555 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2555 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2555 : Charge := ![1, 1, 0, 1, -2, -1]

def sourceA2556 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2556 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2556 : Charge := ![1, 1, 0, 1, -2, -1]

def sourceA2557 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2557 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2557 : Charge := ![1, 1, 0, 1, -2, -1]

def sourceA2558 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2558 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2558 : Charge := ![1, 1, 0, 1, -2, -1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA256 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB256 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC256 : Charge := ![2, 1, 0, -1, -2, 0]

def sourceA257 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB257 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC257 : Charge := ![2, 1, 0, -1, -2, 0]

def sourceA258 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB258 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC258 : Charge := ![2, 1, 0, -1, -2, 0]

def sourceA259 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB259 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC259 : Charge := ![2, 1, 0, -1, -2, 0]

def sourceA260 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB260 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC260 : Charge := ![2, 1, 0, -1, -2, 0]

def sourceA261 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB261 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC261 : Charge := ![2, 1, 0, -1, -2, 0]

def sourceA262 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB262 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC262 : Charge := ![2, 1, 0, -1, -2, 0]

def sourceA263 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB263 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC263 : Charge := ![2, 1, 0, -1, -2, 0]

def sourceA264 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB264 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC264 : Charge := ![2, 1, 0, -1, -2, 0]

def sourceA265 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB265 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC265 : Charge := ![2, 1, 0, -1, -2, 0]

def sourceA268 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB268 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC268 : Charge := ![1, -1, 0, 1, 1, -2]

def sourceA269 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB269 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC269 : Charge := ![1, -1, 0, 1, 1, -2]

def sourceA270 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB270 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC270 : Charge := ![1, -1, 0, 1, 1, -2]

def sourceA271 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB271 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC271 : Charge := ![1, -1, 0, 1, 1, -2]

def sourceA272 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB272 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC272 : Charge := ![1, -1, 0, 1, 1, -2]

def sourceA273 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB273 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC273 : Charge := ![1, -1, 0, 1, 1, -2]

def sourceA274 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB274 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC274 : Charge := ![1, -1, 0, 1, 1, -2]

def sourceA275 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB275 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC275 : Charge := ![1, -1, 0, 1, 1, -2]

def sourceA276 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB276 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC276 : Charge := ![1, -1, 0, 1, 1, -2]

def sourceA277 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB277 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC277 : Charge := ![1, -1, 0, 1, 1, -2]

def sourceA280 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceB280 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC280 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA281 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceB281 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC281 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA282 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceB282 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC282 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA283 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceB283 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC283 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA286 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceB286 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC286 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA287 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceB287 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC287 : Charge := ![-3, 0, 0, 0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2565 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2565 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC2565 : Charge := ![1, 2, 0, 0, -2, -1]

def sourceA2566 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2566 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC2566 : Charge := ![1, 2, 0, 0, -2, -1]

def sourceA2571 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2571 : Charge := ![2, 2, 0, 0, -2, -2]
def sourceC2571 : Charge := ![0, 0, 0, 0, 0, 0]

def sourceA2572 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2572 : Charge := ![0, 2, 0, -1, -1, 0]
def sourceC2572 : Charge := ![2, 0, 0, 0, 0, -2]

def sourceA2573 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2573 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC2573 : Charge := ![0, 2, 0, -1, -1, 0]

def sourceA2574 : Charge := ![0, 2, 0, -1, -1, 0]
def sourceB2574 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC2574 : Charge := ![-2, -2, 0, 1, 1, 2]

def sourceA2575 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2575 : Charge := ![0, 2, 0, -1, 0, -1]
def sourceC2575 : Charge := ![2, 0, 0, 0, -1, -1]

def sourceA2576 : Charge := ![0, 2, 0, -1, 0, -1]
def sourceB2576 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC2576 : Charge := ![-2, -2, 0, 1, 1, 2]

def sourceA2579 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2579 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC2579 : Charge := ![0, 2, 0, -1, 1, -2]

def sourceA2580 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2580 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC2580 : Charge := ![0, 2, 0, -1, 1, -2]

def sourceA2582 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2582 : Charge := ![0, 2, 1, -1, -1, -1]
def sourceC2582 : Charge := ![2, 0, -1, 0, 0, -1]

def sourceA2583 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2583 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceC2583 : Charge := ![0, 2, 1, -1, -1, -1]

def sourceA2584 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2584 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceC2584 : Charge := ![0, 2, 1, -1, -1, -1]

def sourceA2587 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2587 : Charge := ![2, 0, -1, 0, -1, 0]
def sourceC2587 : Charge := ![0, 2, 1, -1, 0, -2]

def sourceA2588 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2588 : Charge := ![2, 0, -1, 0, -1, 0]
def sourceC2588 : Charge := ![0, 2, 1, -1, 0, -2]

def sourceA2591 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2591 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC2591 : Charge := ![0, 3, 0, -1, -1, -1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2592 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2592 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC2592 : Charge := ![0, 3, 0, -1, -1, -1]

def sourceA2595 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2595 : Charge := ![2, -1, 0, 0, -1, 0]
def sourceC2595 : Charge := ![0, 3, 0, -1, 0, -2]

def sourceA2596 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2596 : Charge := ![2, -1, 0, 0, -1, 0]
def sourceC2596 : Charge := ![0, 3, 0, -1, 0, -2]

def sourceA2597 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2597 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC2597 : Charge := ![1, 1, 0, 0, 0, -2]

def sourceA2598 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2598 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC2598 : Charge := ![1, 1, 0, -1, -1, 0]

def sourceA2599 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2599 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2599 : Charge := ![1, 1, 0, 0, -1, -1]

def sourceA2602 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2602 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC2602 : Charge := ![1, 1, 0, -1, 1, -2]

def sourceA2603 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2603 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC2603 : Charge := ![1, 1, 0, -1, 1, -2]

def sourceA2607 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2607 : Charge := ![1, 1, -1, 0, -1, 0]
def sourceC2607 : Charge := ![1, 1, 1, -1, 0, -2]

def sourceA2608 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2608 : Charge := ![1, 1, -1, 0, -1, 0]
def sourceC2608 : Charge := ![1, 1, 1, -1, 0, -2]

def sourceA2611 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2611 : Charge := ![1, 0, 1, 0, 0, -2]
def sourceC2611 : Charge := ![1, 2, -1, -1, -1, 0]

def sourceA2612 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2612 : Charge := ![1, 0, 1, 0, 0, -2]
def sourceC2612 : Charge := ![1, 2, -1, -1, -1, 0]

def sourceA2614 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2614 : Charge := ![1, 0, 1, 0, -1, -1]
def sourceC2614 : Charge := ![1, 2, -1, -1, 0, -1]

def sourceA2615 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2615 : Charge := ![1, 0, 1, 0, -1, -1]
def sourceC2615 : Charge := ![1, 2, -1, -1, 0, -1]

def sourceA2618 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2618 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceC2618 : Charge := ![1, 2, -1, 0, 0, -2]

def sourceA2619 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2619 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceC2619 : Charge := ![1, 2, -1, 0, 0, -2]

def sourceA2621 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2621 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceC2621 : Charge := ![1, 2, 0, -2, -1, 0]

def sourceA2622 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2622 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceC2622 : Charge := ![1, 2, 0, -2, -1, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2624 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2624 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceC2624 : Charge := ![1, 2, 0, -2, 0, -1]

def sourceA2625 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2625 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceC2625 : Charge := ![1, 2, 0, -2, 0, -1]

def sourceA2627 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2627 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC2627 : Charge := ![1, 2, 0, -1, -1, -1]

def sourceA2628 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2628 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC2628 : Charge := ![1, 2, 0, -1, 0, -2]

def sourceA2629 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2629 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceC2629 : Charge := ![1, 2, 0, 0, 0, -3]

def sourceA2630 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2630 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceC2630 : Charge := ![1, 2, 0, 0, 0, -3]

def sourceA2632 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2632 : Charge := ![1, 0, -1, 0, 0, 0]
def sourceC2632 : Charge := ![1, 2, 1, -1, -1, -2]

def sourceA2633 : Charge := ![1, 0, -1, 0, 0, 0]
def sourceB2633 : Charge := ![1, 2, 1, -1, -1, -2]
def sourceC2633 : Charge := ![-2, -2, 0, 1, 1, 2]

def sourceA2638 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2638 : Charge := ![2, 2, 0, -1, -1, -2]
def sourceC2638 : Charge := ![0, 0, 0, 0, 0, 0]

def sourceA2639 : Charge := ![-2, -2, 1, 1, 1, 1]
def sourceB2639 : Charge := ![0, 2, -1, -1, -1, 1]
def sourceC2639 : Charge := ![2, 0, 0, 0, 0, -2]

def sourceA2640 : Charge := ![-2, -2, 1, 1, 1, 1]
def sourceB2640 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC2640 : Charge := ![0, 2, -1, -1, -1, 1]

def sourceA2641 : Charge := ![-2, -2, 1, 1, 1, 1]
def sourceB2641 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC2641 : Charge := ![0, 2, -1, -1, -1, 1]

def sourceA2642 : Charge := ![-2, -2, 1, 1, 1, 1]
def sourceB2642 : Charge := ![0, 2, -1, -1, 0, 0]
def sourceC2642 : Charge := ![2, 0, 0, 0, -1, -1]

def sourceA2644 : Charge := ![-2, -2, 1, 1, 1, 1]
def sourceB2644 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC2644 : Charge := ![0, 3, -1, -1, -1, 0]

def sourceA2645 : Charge := ![-2, -2, 1, 1, 1, 1]
def sourceB2645 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC2645 : Charge := ![0, 3, -1, -1, -1, 0]

def sourceA2647 : Charge := ![-2, -2, 1, 1, 1, 1]
def sourceB2647 : Charge := ![1, 1, -1, -1, 0, 0]
def sourceC2647 : Charge := ![1, 1, 0, 0, -1, -1]

def sourceA2649 : Charge := ![-2, -2, 1, 1, 1, 1]
def sourceB2649 : Charge := ![2, 2, -1, -1, -1, -1]
def sourceC2649 : Charge := ![0, 0, 0, 0, 0, 0]

def sourceA2650 : Charge := ![-2, -1, -1, 1, 1, 2]
def sourceB2650 : Charge := ![0, 1, 1, -1, -1, 0]
def sourceC2650 : Charge := ![2, 0, 0, 0, 0, -2]

def sourceA2651 : Charge := ![-2, -1, -1, 1, 1, 2]
def sourceB2651 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC2651 : Charge := ![0, 1, 1, -1, -1, 0]

def sourceA2652 : Charge := ![-2, -1, -1, 1, 1, 2]
def sourceB2652 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC2652 : Charge := ![0, 1, 1, -1, 1, -2]

def sourceA2653 : Charge := ![-2, -1, -1, 1, 1, 2]
def sourceB2653 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC2653 : Charge := ![0, 1, 1, -1, 1, -2]

def sourceA2654 : Charge := ![-2, -1, -1, 1, 1, 2]
def sourceB2654 : Charge := ![2, 1, 1, -1, -1, -2]
def sourceC2654 : Charge := ![0, 0, 0, 0, 0, 0]

def sourceA2655 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceB2655 : Charge := ![3, 0, 0, 0, -1, -2]
def sourceC2655 : Charge := ![-5, 0, 0, 0, 0, 5]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2656 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB2656 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceC2656 : Charge := ![-5, 0, 0, 0, 0, 5]

def sourceA2657 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceB2657 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceC2657 : Charge := ![-5, 0, 0, 0, 1, 4]

def sourceA2658 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceB2658 : Charge := ![3, 0, 0, -1, 0, -2]
def sourceC2658 : Charge := ![-5, 0, 0, 0, 1, 4]

def sourceA2659 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB2659 : Charge := ![3, 0, 0, 0, -1, -2]
def sourceC2659 : Charge := ![-5, 0, 0, 0, 1, 4]

def sourceA2663 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceB2663 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceC2663 : Charge := ![-5, 0, 0, 0, 2, 3]

def sourceA2664 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceB2664 : Charge := ![3, 0, 0, -1, 0, -2]
def sourceC2664 : Charge := ![-5, 0, 0, 0, 2, 3]

def sourceA2665 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceB2665 : Charge := ![3, 0, 0, -1, -1, -1]
def sourceC2665 : Charge := ![-5, 0, 0, 0, 2, 3]

def sourceA2667 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB2667 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceC2667 : Charge := ![-5, 0, 0, 0, 2, 3]

def sourceA2669 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB2669 : Charge := ![3, 0, 0, 0, -1, -2]
def sourceC2669 : Charge := ![-5, 0, 0, 0, 2, 3]

def sourceA2671 : Charge := ![2, 0, 0, -1, 1, -2]
def sourceB2671 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceC2671 : Charge := ![-5, 0, 0, 1, 1, 3]

def sourceA2672 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceB2672 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceC2672 : Charge := ![-5, 0, 0, 1, 1, 3]

def sourceA2673 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceB2673 : Charge := ![3, 0, -1, 0, 0, -2]
def sourceC2673 : Charge := ![-5, 0, 0, 1, 1, 3]

def sourceA2679 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceB2679 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceC2679 : Charge := ![-5, 0, 0, 1, 2, 2]

def sourceA2680 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceB2680 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC2680 : Charge := ![-5, 0, 0, 1, 2, 2]

def sourceA2681 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceB2681 : Charge := ![3, 0, -1, 0, -1, -1]
def sourceC2681 : Charge := ![-5, 0, 0, 1, 2, 2]

def sourceA2687 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceB2687 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceC2687 : Charge := ![-5, 0, 1, 1, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2688 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceB2688 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceC2688 : Charge := ![-5, 0, 1, 1, 1, 2]

def sourceA2689 : Charge := ![2, 0, -1, 0, 1, -2]
def sourceB2689 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceC2689 : Charge := ![-5, 0, 1, 1, 1, 2]

def sourceA2691 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB2691 : Charge := ![3, 0, -1, -1, -1, 0]
def sourceC2691 : Charge := ![-5, 0, 1, 1, 1, 2]

def sourceA2696 : Charge := ![2, -1, -1, -1, 0, 1]
def sourceB2696 : Charge := ![3, 0, 0, 0, -1, -2]
def sourceC2696 : Charge := ![-5, 1, 1, 1, 1, 1]

def sourceA2697 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB2697 : Charge := ![3, -1, -1, -1, -1, 1]
def sourceC2697 : Charge := ![-5, 1, 1, 1, 1, 1]

def sourceA2699 : Charge := ![1, 1, 0, 0, 1, -3]
def sourceB2699 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceC2699 : Charge := ![-4, -1, 0, 0, 1, 4]

def sourceA2700 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceB2700 : Charge := ![2, 1, 0, -1, 0, -2]
def sourceC2700 : Charge := ![-4, -1, 0, 0, 1, 4]

def sourceA2703 : Charge := ![1, 1, 0, 0, 1, -3]
def sourceB2703 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceC2703 : Charge := ![-4, -1, 0, 0, 2, 3]

def sourceA2704 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceB2704 : Charge := ![3, 0, 0, -1, 0, -2]
def sourceC2704 : Charge := ![-4, -1, 0, 0, 2, 3]

def sourceA2705 : Charge := ![1, 1, 0, 1, -1, -2]
def sourceB2705 : Charge := ![3, 0, 0, -1, -1, -1]
def sourceC2705 : Charge := ![-4, -1, 0, 0, 2, 3]

def sourceA2706 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceB2706 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC2706 : Charge := ![-4, -1, 0, 0, 2, 3]

def sourceA2707 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceB2707 : Charge := ![2, 1, 0, -1, 0, -2]
def sourceC2707 : Charge := ![-4, -1, 0, 0, 2, 3]

def sourceA2708 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceB2708 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceC2708 : Charge := ![-4, -1, 0, 0, 2, 3]

def sourceA2710 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB2710 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC2710 : Charge := ![-4, -1, 0, 0, 2, 3]

def sourceA2712 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB2712 : Charge := ![2, 1, 0, 0, -1, -2]
def sourceC2712 : Charge := ![-4, -1, 0, 0, 2, 3]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2720 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceB2720 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceC2720 : Charge := ![-4, -1, 0, 1, 1, 3]

def sourceA2725 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceB2725 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceC2725 : Charge := ![-4, -1, 0, 1, 2, 2]

def sourceA2726 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceB2726 : Charge := ![2, 1, -1, 0, -1, -1]
def sourceC2726 : Charge := ![-4, -1, 0, 1, 2, 2]

def sourceA2728 : Charge := ![0, 2, 0, 0, 1, -3]
def sourceB2728 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceC2728 : Charge := ![-3, -2, 0, 0, 2, 3]

def sourceA2729 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceB2729 : Charge := ![3, 0, 0, -1, 0, -2]
def sourceC2729 : Charge := ![-3, -2, 0, 0, 2, 3]

def sourceA2730 : Charge := ![0, 2, 0, 1, -1, -2]
def sourceB2730 : Charge := ![3, 0, 0, -1, -1, -1]
def sourceC2730 : Charge := ![-3, -2, 0, 0, 2, 3]

def sourceA2731 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceB2731 : Charge := ![2, 1, 0, -1, 0, -2]
def sourceC2731 : Charge := ![-3, -2, 0, 0, 2, 3]

def sourceA2732 : Charge := ![1, 1, 0, 1, -1, -2]
def sourceB2732 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceC2732 : Charge := ![-3, -2, 0, 0, 2, 3]

def sourceA2733 : Charge := ![1, 2, -1, 0, 0, -2]
def sourceB2733 : Charge := ![2, 0, 1, 0, -2, -1]
def sourceC2733 : Charge := ![-3, -2, 0, 0, 2, 3]

def sourceA2740 : Charge := ![0, 2, 0, -1, 1, -2]
def sourceB2740 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceC2740 : Charge := ![-3, -2, 0, 1, 1, 3]

def sourceA2741 : Charge := ![0, 2, 0, 0, 1, -3]
def sourceB2741 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceC2741 : Charge := ![-3, -2, 0, 1, 1, 3]

def sourceA2742 : Charge := ![0, 2, 1, -1, -1, -1]
def sourceB2742 : Charge := ![3, 0, -1, 0, 0, -2]
def sourceC2742 : Charge := ![-3, -2, 0, 1, 1, 3]

def sourceA2743 : Charge := ![1, 1, 0, -1, 1, -2]
def sourceB2743 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC2743 : Charge := ![-3, -2, 0, 1, 1, 3]

def sourceA2744 : Charge := ![1, 1, 0, 0, 1, -3]
def sourceB2744 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC2744 : Charge := ![-3, -2, 0, 1, 1, 3]

def sourceA2745 : Charge := ![1, 1, 1, -1, -1, -1]
def sourceB2745 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceC2745 : Charge := ![-3, -2, 0, 1, 1, 3]

def sourceA2747 : Charge := ![1, 2, -1, -1, -1, 0]
def sourceB2747 : Charge := ![2, 0, 1, 0, 0, -3]
def sourceC2747 : Charge := ![-3, -2, 0, 1, 1, 3]

def sourceA2748 : Charge := ![1, 2, -1, 0, 0, -2]
def sourceB2748 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceC2748 : Charge := ![-3, -2, 0, 1, 1, 3]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources86
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2756 : Charge := ![0, 2, 0, -1, -2, 1]
def sourceB2756 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceC2756 : Charge := ![-3, -2, 0, 1, 2, 2]

def sourceA2757 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceB2757 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC2757 : Charge := ![-3, -2, 0, 1, 2, 2]

def sourceA2758 : Charge := ![0, 2, 1, -1, -1, -1]
def sourceB2758 : Charge := ![3, 0, -1, 0, -1, -1]
def sourceC2758 : Charge := ![-3, -2, 0, 1, 2, 2]

def sourceA2759 : Charge := ![1, 1, 0, -1, -2, 1]
def sourceB2759 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceC2759 : Charge := ![-3, -2, 0, 1, 2, 2]

def sourceA2766 : Charge := ![1, 1, 1, -1, 0, -2]
def sourceB2766 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC2766 : Charge := ![-3, -1, -1, 1, 1, 3]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA288 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceB288 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC288 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA289 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceB289 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC289 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA291 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB291 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceC291 : Charge := ![2, 1, 0, -2, 0, -1]

def sourceA292 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB292 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceC292 : Charge := ![2, 1, 0, -2, 0, -1]

def sourceA293 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB293 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceC293 : Charge := ![2, 1, 0, -2, 0, -1]

def sourceA294 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB294 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceC294 : Charge := ![2, 1, 0, -2, 0, -1]

def sourceA295 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB295 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceC295 : Charge := ![2, 1, 0, -2, 0, -1]

def sourceA296 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB296 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceC296 : Charge := ![2, 1, 0, -2, 0, -1]

def sourceA297 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB297 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceC297 : Charge := ![2, 1, 0, -2, 0, -1]

def sourceA298 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB298 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceC298 : Charge := ![2, 1, 0, -2, 0, -1]

def sourceA299 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB299 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceC299 : Charge := ![2, 1, 0, -2, 0, -1]

def sourceA300 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB300 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceC300 : Charge := ![2, 1, 0, -2, 0, -1]

def sourceA301 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB301 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceC301 : Charge := ![2, 1, 0, -2, 0, -1]

def sourceA303 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB303 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC303 : Charge := ![1, -1, 0, 2, -1, -1]

def sourceA305 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB305 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC305 : Charge := ![1, -1, 0, 2, -1, -1]

def sourceA306 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB306 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC306 : Charge := ![1, -1, 0, 2, -1, -1]

def sourceA307 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB307 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC307 : Charge := ![1, -1, 0, 2, -1, -1]

def sourceA308 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB308 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC308 : Charge := ![1, -1, 0, 2, -1, -1]

def sourceA309 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB309 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC309 : Charge := ![1, -1, 0, 2, -1, -1]

def sourceA310 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB310 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC310 : Charge := ![1, -1, 0, 2, -1, -1]

def sourceA311 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB311 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC311 : Charge := ![1, -1, 0, 2, -1, -1]

def sourceA312 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB312 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC312 : Charge := ![1, -1, 0, 2, -1, -1]

def sourceA313 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB313 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC313 : Charge := ![1, -1, 0, 2, -1, -1]

def sourceA314 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB314 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC314 : Charge := ![1, -1, 0, 2, -1, -1]

def sourceA315 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB315 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC315 : Charge := ![1, -1, 0, 2, -1, -1]

def sourceA316 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceB316 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC316 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA317 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceB317 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC317 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA318 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceB318 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC318 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA319 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceB319 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC319 : Charge := ![-3, 0, 0, 0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMerge_Block0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairData

def pairMerged0 : Integer.Sparse (Fin 271) := [(0, 138332760), (1, 8501053680), (2, -2890080960), (3, -23120647680), (4, -11560323840), (5, 5080523400), (6, -499592880), (7, -5780161920), (8, -2890080960), (12, -8670242880), (23, 4335121440), (24, 8670242880), (27, -5995114560)]

def pairMerged1 : Integer.Sparse (Fin 271) := [(0, -528840840), (1, -4101114320), (2, -1036820960), (3, -17190215680), (4, 300540160), (5, 5080523400), (6, -499592880), (7, -5780161920), (8, -2890080960), (12, -5705026880), (23, 4335121440), (24, 8670242880), (27, -5995114560)]

def pairMerged10 : Integer.Sparse (Fin 271) := [(0, 425465220), (1, -8119256040), (2, 1356329580), (3, 19540684800), (4, 13543423200), (12, 8303453280), (18, 4932865440), (21, 1596594240), (22, 1596594240), (25, -3288576960), (30, -4352973120)]

def pairMerged11 : Integer.Sparse (Fin 271) := [(0, 527992500), (1, -10658200920), (2, 1757390460), (3, 22274745600), (4, 16496778720), (12, 8731124640), (15, -328942080), (17, 1394798400), (18, 4932865440), (19, 1559269440), (20, 1559269440), (21, 1596594240), (22, 3155863680), (23, 164471040), (24, -2489135040), (25, -2959634880), (27, 348699600), (29, -464932800), (30, -6103056960)]

def pairMerged12 : Integer.Sparse (Fin 271) := [(0, -51436332), (1, -1751623200), (2, 798915720), (3, 13752497280), (4, 4638792480), (12, 5389620000), (14, -1074388320), (15, -2406939840), (16, 676535760), (17, -1549683360), (18, 3349956960), (19, 1559269440), (20, -2596726080), (21, 1596594240), (22, -9953280), (23, 2820124800), (24, -411137280), (25, 4155768000), (27, -538860060), (29, 1901892960), (30, 2397677760)]

def pairMerged13 : Integer.Sparse (Fin 271) := [(0, -1686539584), (1, 26393763270), (2, -9222802470), (3, -48954134400), (4, -35572405920), (5, 6319438920), (6, -499592880), (7, -7432049280), (8, -11149517760), (12, -5320084320), (13, 7467779680), (14, -1074388320), (15, -2406939840), (16, 676535760), (17, -1549683360), (18, 3349956960), (19, 1559269440), (20, -2596726080), (21, 1596594240), (22, -9953280), (23, 7155246240), (24, 13214767680), (25, 9605207520), (26, -12674317440), (27, -6533974620), (29, 11813217120), (30, 18622872000)]

def pairMerged14 : Integer.Sparse (Fin 271) := [(0, -109408634), (1, 1684676680), (2, -2029825900), (3, -9843319200), (4, -1933827360), (5, 2142154040), (6, -123585810), (7, -3954745920), (8, -3954745920), (12, -3911200320), (13, -2636497280), (17, 48988800), (23, -16329600), (27, 12247200), (28, 97977600), (29, -81648000), (34, -1318248640), (50, 5932118880), (51, -1977372960)]

def pairMerged15 : Integer.Sparse (Fin 271) := [(0, 8099576), (1, -56641740), (2, 606072000), (3, 624640320), (4, -276472320), (5, -1541099280), (6, 177490980), (7, 831135360), (8, 1662270720), (12, -484685760), (13, -323123840), (26, -276472320), (34, 346449600), (51, 1662270720), (54, 1454057280)]

def pairMerged16 : Integer.Sparse (Fin 271) := [(0, -101309058), (1, 1628034940), (2, -1423753900), (3, -9218678880), (4, -2210299680), (5, 601054760), (6, 53905170), (7, -3123610560), (8, -2292475200), (12, -4395886080), (13, -2959621120), (17, 48988800), (23, -16329600), (26, -276472320), (27, 12247200), (28, 97977600), (29, -81648000), (34, -971799040), (50, 5932118880), (51, -315102240), (54, 1454057280)]

def pairMerged17 : Integer.Sparse (Fin 271) := [(0, 440260440), (1, -9120956850), (2, 3598850490), (3, 34429673760), (4, 10265991360), (5, -7146635880), (6, 771328020), (7, 8709548640), (8, 9228362880), (12, 2075256960), (13, 6744585120), (26, 10265991360), (34, 5324316000), (51, 2075256960), (53, -1556442720), (55, -3112885440)]

def pairMerged18 : Integer.Sparse (Fin 271) := [(0, -32241928), (1, 1069918200), (2, -85892640), (3, -7259368320), (5, 78413040), (7, -1254608640), (12, -3943336320), (13, -7379041920), (23, 2822869440), (25, 2822869440), (31, -458094080), (34, -627304320), (53, 1881912960)]

def pairMerged19 : Integer.Sparse (Fin 271) := [(0, 408018512), (1, -8051038650), (2, 3512957850), (3, 27170305440), (4, 10265991360), (5, -7068222840), (6, 771328020), (7, 7454940000), (8, 9228362880), (12, -1868079360), (13, -634456800), (23, 2822869440), (25, 2822869440), (26, 10265991360), (31, -458094080), (34, 4697011680), (51, 2075256960), (53, 325470240), (55, -3112885440)]

end MUB6.Certificate.PairData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMerge_Block3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairData

def pairMerged100 : Integer.Sparse (Fin 271) := [(0, -113196), (1, -8511240), (2, 6311340), (3, 94410240), (4, 22360320), (5, -2484480), (7, 14906880), (12, 57143040), (13, 14906880), (14, 110341440), (15, 67080960), (23, -189682560), (24, -22360320), (25, -118281600), (27, 13043520), (32, -44720640), (34, 4968960), (50, -44720640), (53, -44720640), (62, -88467840), (66, 4928400), (111, -71400960), (113, -7453440), (116, 73560960), (124, 44720640), (130, -39427200), (136, 67080960), (144, 110341440)]

def pairMerged101 : Integer.Sparse (Fin 271) := [(0, 9931392), (1, -37706400), (2, 30818880), (5, -14739840), (6, 3684960), (17, 534988800), (23, -356659200), (25, -773729280), (27, 59927040), (29, -178813440), (30, -715737600), (62, -119854080), (66, 14739840), (85, 530634240), (97, 4354560), (100, 534988800), (110, -532085760), (111, -176878080), (130, -117918720), (134, 530634240), (140, 353756160), (142, -176878080), (145, 2903040), (146, -58959360), (147, -178329600)]

def pairMerged102 : Integer.Sparse (Fin 271) := [(0, 9818196), (1, -46217640), (2, 37130220), (3, 94410240), (4, 22360320), (5, -17224320), (6, 3684960), (7, 14906880), (12, 57143040), (13, 14906880), (14, 110341440), (15, 67080960), (17, 534988800), (23, -546341760), (24, -22360320), (25, -892010880), (27, 72970560), (29, -178813440), (30, -715737600), (32, -44720640), (34, 4968960), (50, -44720640), (53, -44720640), (62, -208321920), (66, 19668240), (85, 530634240), (97, 4354560), (100, 534988800), (110, -532085760), (111, -248279040), (113, -7453440), (116, 73560960), (124, 44720640), (130, -157345920), (134, 530634240), (136, 67080960), (140, 353756160), (142, -176878080), (144, 110341440), (145, 2903040), (146, -58959360), (147, -178329600)]

def pairMerged103 : Integer.Sparse (Fin 271) := [(0, 9631404), (1, -153138180), (2, 16920840), (3, 501474240), (4, 300867840), (5, 4687680), (7, -17118720), (12, 101933760), (13, -141854400), (16, -88050240), (18, 198132480), (23, -14688000), (24, -132088320), (25, -132088320), (26, 161441280), (27, 2160), (30, -132088320), (32, -132088320), (34, 1632000), (37, -176100480), (42, 396264960), (46, 198132480), (50, 95385600), (53, 117400320), (54, -73388160), (62, -44029440), (66, -2445840), (111, 29350080), (112, 9783360), (120, -88050240), (121, -58700160), (123, 132088320), (130, 19566720)]

def pairMerged104 : Integer.Sparse (Fin 271) := [(0, -25186536), (1, 338867640), (2, -48609360), (3, -1026794880), (4, -778947840), (5, 11910240), (7, -70813440), (12, -177033600), (13, -47208960), (14, -108164160), (17, -216328320), (23, 404732160), (24, 212440320), (25, 819538560), (26, -354067200), (27, -83479680), (29, 72109440), (30, 747429120), (34, -82615680), (43, -637320960), (54, 318660480), (62, 94849920), (100, -534988800), (110, 178329600), (111, 48072960), (116, -72109440), (134, -432656640), (144, -216328320)]

def pairMerged105 : Integer.Sparse (Fin 271) := [(0, -15555132), (1, 185729460), (2, -31688520), (3, -525320640), (4, -478080000), (5, 16597920), (7, -87932160), (12, -75099840), (13, -189063360), (14, -108164160), (16, -88050240), (17, -216328320), (18, 198132480), (23, 390044160), (24, 80352000), (25, 687450240), (26, -192625920), (27, -83477520), (29, 72109440), (30, 615340800), (32, -132088320), (34, -80983680), (37, -176100480), (42, 396264960), (43, -637320960), (46, 198132480), (50, 95385600), (53, 117400320), (54, 245272320), (62, 50820480), (66, -2445840), (100, -534988800), (110, 178329600), (111, 77423040), (112, 9783360), (116, -72109440), (120, -88050240), (121, -58700160), (123, 132088320), (130, 19566720), (134, -432656640), (144, -216328320)]

def pairMerged106 : Integer.Sparse (Fin 271) := [(0, -5736936), (1, 139511820), (2, 5441700), (3, -430910400), (4, -455719680), (5, -626400), (6, 3684960), (7, -73025280), (12, -17956800), (13, -174156480), (14, 2177280), (15, 67080960), (16, -88050240), (17, 318660480), (18, 198132480), (23, -156297600), (24, 57991680), (25, -204560640), (26, -192625920), (27, -10506960), (29, -106704000), (30, -100396800), (32, -176808960), (34, -76014720), (37, -176100480), (42, 396264960), (43, -637320960), (46, 198132480), (50, 50664960), (53, 72679680), (54, 245272320), (62, -157501440), (66, 17222400), (85, 530634240), (97, 4354560), (110, -353756160), (111, -170856000), (112, 9783360), (113, -7453440), (116, 1451520), (120, -88050240), (121, -58700160), (123, 132088320), (124, 44720640), (130, -137779200), (134, 97977600), (136, 67080960), (140, 353756160), (142, -176878080), (144, -105986880), (145, 2903040), (146, -58959360), (147, -178329600)]

def pairMerged107 : Integer.Sparse (Fin 271) := [(0, 91366470), (1, 217527110), (2, -1047451520), (3, -11539300320), (4, 170845440), (5, 989120680), (6, -44193300), (7, -2873319360), (8, -1370844960), (10, 1364895360), (12, -6704383680), (13, -6646953920), (14, 2177280), (15, 67080960), (16, -88050240), (17, 318660480), (18, 198132480), (23, 468493920), (24, 143488800), (25, -437892480), (26, -1250987520), (27, -151084800), (29, 87134400), (30, -3454591680), (32, 3362918400), (34, -2021673920), (35, -561669120), (36, -1915228800), (37, -164764800), (38, -2465562240), (39, -2465562240), (40, -2729790720), (42, 396264960), (43, -637320960), (45, 2942766720), (46, 933824160), (47, -1189797120), (50, 1477867680), (51, -1424732160), (53, 1548996480), (54, 2303608320), (55, -559454400), (58, 1819860480), (62, -308776320), (66, -17318400), (71, -1364895360), (72, -1364895360), (73, -1364895360), (79, 370667520), (81, -280834560), (82, 5667840), (83, -550333440), (85, -31034880), (86, 11335680), (88, -2058445440), (89, 1807056000), (92, -2941263360), (94, -1364895360), (95, -1364895360), (96, 5667840), (97, -1694502720), (98, 1471383360), (99, 671345280), (110, -353756160), (111, 36388800), (112, 9783360), (113, -7453440), (116, 1451520), (120, -88050240), (121, -58700160), (123, 132088320), (124, 44720640), (130, -68697600), (133, 454965120), (134, 97977600), (136, 67080960), (140, 353756160), (142, -176878080), (143, 368778240), (144, -105986880), (145, 2903040), (146, 355530240), (147, -405241920), (148, -335672640)]

def pairMerged108 : Integer.Sparse (Fin 271) := [(0, -6041016), (1, 18245160), (2, -18884880), (3, 133294080), (4, -224640), (5, 6128640), (12, 68296320), (13, 61923840), (15, -110315520), (16, 88050240), (17, 176100480), (20, -220631040), (23, -51278400), (24, 110315520), (26, 39133440), (27, -45964800), (29, 73543680), (34, 19566720), (37, 88050240), (39, 176100480), (50, 14843520), (51, -4947840), (54, -146750400), (112, -39133440), (113, 49029120), (120, 176100480), (121, 58700160), (124, -73543680), (126, 352200960), (136, -220631040), (138, -441262080)]

def pairMerged109 : Integer.Sparse (Fin 271) := [(0, 877068), (1, -40829400), (2, 17212500), (3, 325054080), (4, 100016640), (5, 421200), (6, -1224720), (7, 50008320), (12, 175029120), (15, 225037440), (17, -88179840), (23, -233150400), (24, -225037440), (25, -148340160), (27, 19517760), (28, -176359680), (29, 146966400), (30, 58786560), (32, -75012480), (47, 225037440), (50, -75012480), (54, -150024960), (66, 9376560), (111, -75012480), (113, -75012480), (117, 225037440), (131, -75012480), (134, -176359680), (136, 225037440), (140, -58786560), (144, 112518720), (146, 39191040), (150, -352719360)]

def pairMerged110 : Integer.Sparse (Fin 271) := [(0, -5163948), (1, -22584240), (2, -1672380), (3, 458348160), (4, 99792000), (5, 6549840), (6, -1224720), (7, 50008320), (12, 243325440), (13, 61923840), (15, 114721920), (16, 88050240), (17, 87920640), (20, -220631040), (23, -284428800), (24, -114721920), (25, -148340160), (26, 39133440), (27, -26447040), (28, -176359680), (29, 220510080), (30, 58786560), (32, -75012480), (34, 19566720), (37, 88050240), (39, 176100480), (47, 225037440), (50, -60168960), (51, -4947840), (54, -296775360), (66, 9376560), (111, -75012480), (112, -39133440), (113, -25983360), (117, 225037440), (120, 176100480), (121, 58700160), (124, -73543680), (126, 352200960), (131, -75012480), (134, -176359680), (136, 4406400), (138, -441262080), (140, -58786560), (144, 112518720), (146, 39191040), (150, -352719360)]

def pairMerged111 : Integer.Sparse (Fin 271) := [(0, 1652724), (1, -7054020), (2, -2395440), (3, 79462080), (4, 65543040), (5, 4920480), (7, -16796160), (12, 115421760), (13, -6903360), (16, -38024640), (23, 118091520), (24, 101399040), (25, -187038720), (26, 56678400), (27, -28518480), (32, -102021120), (37, 51010560), (42, 204042240), (46, -152098560), (49, 51010560), (50, 50699520), (53, -17003520), (54, 101399040), (63, -34007040), (66, -3168720), (101, 102021120), (111, 12674880), (112, 38024640), (113, 25349760), (120, -114073920), (136, -76049280)]

def pairMerged112 : Integer.Sparse (Fin 271) := [(0, -9077328), (1, 213979680), (2, -47004480), (3, -1010188800), (4, -454452480), (5, 12326400), (6, -418320), (7, -47520000), (8, -13386240), (12, -358963200), (13, -82321920), (18, -164643840), (21, -120476160), (23, 177361920), (24, 244961280), (25, 102401280), (26, -78531840), (27, -50699520), (30, 140555520), (32, 95040000), (34, -31680000), (42, -60238080), (46, -285120000), (47, -142560000), (49, -246965760), (50, 268392960), (51, -20079360), (53, 40158720), (54, 219525120), (55, 100396800), (89, -60238080), (103, -82321920), (127, -164643840), (129, -120476160), (139, -120476160), (148, 20079360)]

def pairMerged113 : Integer.Sparse (Fin 271) := [(0, -7424604), (1, 206925660), (2, -49399920), (3, -930726720), (4, -388909440), (5, 17246880), (6, -418320), (7, -64316160), (8, -13386240), (12, -243541440), (13, -89225280), (16, -38024640), (18, -164643840), (21, -120476160), (23, 295453440), (24, 346360320), (25, -84637440), (26, -21853440), (27, -79218000), (30, 140555520), (32, -6981120), (34, -31680000), (37, 51010560), (42, 143804160), (46, -437218560), (47, -142560000), (49, -195955200), (50, 319092480), (51, -20079360), (53, 23155200), (54, 320924160), (55, 100396800), (63, -34007040), (66, -3168720), (89, -60238080), (101, 102021120), (103, -82321920), (111, 12674880), (112, 38024640), (113, 25349760), (120, -114073920), (127, -164643840), (129, -120476160), (136, -76049280), (139, -120476160), (148, 20079360)]

def pairMerged114 : Integer.Sparse (Fin 271) := [(0, -12588552), (1, 184341420), (2, -51072300), (3, -472378560), (4, -289117440), (5, 23796720), (6, -1643040), (7, -14307840), (8, -13386240), (12, -216000), (13, -27301440), (15, 114721920), (16, 50025600), (17, 87920640), (18, -164643840), (20, -220631040), (21, -120476160), (23, 11024640), (24, 231638400), (25, -232977600), (26, 17280000), (27, -105665040), (28, -176359680), (29, 220510080), (30, 199342080), (32, -81993600), (34, -12113280), (37, 139060800), (39, 176100480), (42, 143804160), (46, -437218560), (47, 82477440), (49, -195955200), (50, 258923520), (51, -25027200), (53, 23155200), (54, 24148800), (55, 100396800), (63, -34007040), (66, 6207840), (89, -60238080), (101, 102021120), (103, -82321920), (111, -62337600), (112, -1108800), (113, -633600), (117, 225037440), (120, 62026560), (121, 58700160), (124, -73543680), (126, 352200960), (127, -164643840), (129, -120476160), (131, -75012480), (134, -176359680), (136, -71642880), (138, -441262080), (139, -120476160), (140, -58786560), (144, 112518720), (146, 39191040), (148, 20079360), (150, -352719360)]

def pairMerged115 : Integer.Sparse (Fin 271) := [(0, 11596032), (1, -110172960), (2, 35157600), (3, 438174720), (4, 251089920), (12, 2027520), (13, 121236480), (25, 110039040), (26, 125268480), (30, -250076160), (32, -84188160), (33, 64926720), (40, -41264640), (41, 166717440), (42, -165058560), (43, 166717440), (44, 166717440), (49, -82529280), (104, -41264640), (105, 83358720), (106, -82529280), (107, 166717440), (108, 166717440)]

def pairMerged116 : Integer.Sparse (Fin 271) := [(0, 1069056), (1, -18443520), (2, 5333760), (3, 67092480), (4, 32256000), (5, -414720), (7, 1658880), (8, 1105920), (12, 24698880), (13, 12165120), (22, 9953280), (25, -26542080), (26, 10690560), (30, -39813120), (32, -22118400), (33, 2949120), (34, 1105920), (37, 6635520), (38, 13271040), (42, 23224320), (45, 23224320), (46, 4976640), (48, 9953280), (49, 13271040), (50, -11612160), (53, -6635520), (55, -1658880), (63, -6635520), (89, 4976640), (99, 9953280), (101, 6635520), (102, 13271040), (105, 6635520), (106, 13271040), (135, 9953280), (148, -4976640)]

def pairMerged117 : Integer.Sparse (Fin 271) := [(0, 12665088), (1, -128616480), (2, 40491360), (3, 505267200), (4, 283345920), (5, -414720), (7, 1658880), (8, 1105920), (12, 26726400), (13, 133401600), (22, 9953280), (25, 83496960), (26, 135959040), (30, -289889280), (32, -106306560), (33, 67875840), (34, 1105920), (37, 6635520), (38, 13271040), (40, -41264640), (41, 166717440), (42, -141834240), (43, 166717440), (44, 166717440), (45, 23224320), (46, 4976640), (48, 9953280), (49, -69258240), (50, -11612160), (53, -6635520), (55, -1658880), (63, -6635520), (89, 4976640), (99, 9953280), (101, 6635520), (102, 13271040), (104, -41264640), (105, 89994240), (106, -69258240), (107, 166717440), (108, 166717440), (135, 9953280), (148, -4976640)]

def pairMerged118 : Integer.Sparse (Fin 271) := [(0, 9253872), (1, -121031280), (2, 46465920), (3, 410538240), (4, 223672320), (5, -4847040), (7, 7050240), (8, 14100480), (12, 138827520), (13, 33765120), (15, 31726080), (23, -15863040), (24, -31726080), (25, -55365120), (26, 53222400), (27, 7931520), (30, -179159040), (32, -75686400), (33, 7603200), (38, 63452160), (41, 63452160), (42, 68428800), (44, 136857600), (45, 136857600), (49, 34214400), (50, -63452160), (54, -21150720), (55, -52876800), (63, -10575360), (66, 1321920), (89, 31726080), (101, 31726080), (105, 68428800), (106, 68428800), (111, -5287680), (112, -5287680), (113, -10575360), (120, 15863040), (124, 31726080), (125, 31726080), (131, -10575360), (148, -10575360)]

def pairMerged119 : Integer.Sparse (Fin 271) := [(0, 6964272), (1, -43651440), (2, -35940240), (3, -85881600), (4, 178859520), (5, 7499520), (6, -458640), (7, 5402880), (8, -14676480), (12, -99429120), (13, -315544320), (18, -132088320), (21, 120476160), (23, -78382080), (24, -76446720), (25, -110799360), (26, 137975040), (27, -1451520), (30, 35562240), (32, 179988480), (34, -8628480), (37, -66044160), (38, -132088320), (41, -396264960), (42, 180714240), (43, 361428480), (46, -5806080), (47, 120476160), (50, 200067840), (51, -22014720), (53, 66044160), (54, -94590720), (55, 110073600), (63, 44029440), (89, -66044160), (101, -132088320), (103, 60238080), (104, 120476160), (122, -132088320), (123, -132088320), (129, 120476160), (148, 22014720)]

def pairMerged120 : Integer.Sparse (Fin 271) := [(0, 16218144), (1, -164682720), (2, 10525680), (3, 324656640), (4, 402531840), (5, 2652480), (6, -458640), (7, 12453120), (8, -576000), (12, 39398400), (13, -281779200), (15, 31726080), (18, -132088320), (21, 120476160), (23, -94245120), (24, -108172800), (25, -166164480), (26, 191197440), (27, 6480000), (30, -143596800), (32, 104302080), (33, 7603200), (34, -8628480), (37, -66044160), (38, -68636160), (41, -332812800), (42, 249143040), (43, 361428480), (44, 136857600), (45, 136857600), (46, -5806080), (47, 120476160), (49, 34214400), (50, 136615680), (51, -22014720), (53, 66044160), (54, -115741440), (55, 57196800), (63, 33454080), (66, 1321920), (89, -34318080), (101, -100362240), (103, 60238080), (104, 120476160), (105, 68428800), (106, 68428800), (111, -5287680), (112, -5287680), (113, -10575360), (120, 15863040), (122, -132088320), (123, -132088320), (124, 31726080), (125, 31726080), (129, 120476160), (131, -10575360), (148, 11439360)]

def pairMerged121 : Integer.Sparse (Fin 271) := [(0, 28883232), (1, -293299200), (2, 51017040), (3, 829923840), (4, 685877760), (5, 2237760), (6, -458640), (7, 14112000), (8, 529920), (12, 66124800), (13, -148377600), (15, 31726080), (18, -132088320), (21, 120476160), (22, 9953280), (23, -94245120), (24, -108172800), (25, -82667520), (26, 327156480), (27, 6480000), (30, -433486080), (32, -2004480), (33, 75479040), (34, -7522560), (37, -59408640), (38, -55365120), (40, -41264640), (41, -166095360), (42, 107308800), (43, 528145920), (44, 303575040), (45, 160081920), (46, -829440), (47, 120476160), (48, 9953280), (49, -35043840), (50, 125003520), (51, -22014720), (53, 59408640), (54, -115741440), (55, 55537920), (63, 26818560), (66, 1321920), (89, -29341440), (99, 9953280), (101, -93726720), (102, 13271040), (103, 60238080), (104, 79211520), (105, 158423040), (106, -829440), (107, 166717440), (108, 166717440), (111, -5287680), (112, -5287680), (113, -10575360), (120, 15863040), (122, -132088320), (123, -132088320), (124, 31726080), (125, 31726080), (129, 120476160), (131, -10575360), (135, 9953280), (148, 6462720)]

def pairMerged122 : Integer.Sparse (Fin 271) := [(0, 16294680), (1, -108957780), (2, -55260), (3, 357545280), (4, 396760320), (5, 26034480), (6, -2101680), (7, -195840), (8, -12856320), (12, 65908800), (13, -175679040), (15, 146448000), (16, 50025600), (17, 87920640), (18, -296732160), (20, -220631040), (22, 9953280), (23, -83220480), (24, 123465600), (25, -315645120), (26, 344436480), (27, -99185040), (28, -176359680), (29, 220510080), (30, -234144000), (32, -83998080), (33, 75479040), (34, -19635840), (37, 79652160), (38, -55365120), (39, 176100480), (40, -41264640), (41, -166095360), (42, 251112960), (43, 528145920), (44, 303575040), (45, 160081920), (46, -438048000), (47, 202953600), (48, 9953280), (49, -230999040), (50, 383927040), (51, -47041920), (53, 82563840), (54, -91592640), (55, 155934720), (63, -7188480), (66, 7529760), (89, -89579520), (99, 9953280), (101, 8294400), (102, 13271040), (103, -22083840), (104, 79211520), (105, 158423040), (106, -829440), (107, 166717440), (108, 166717440), (111, -67625280), (112, -6396480), (113, -11208960), (117, 225037440), (120, 77889600), (121, 58700160), (122, -132088320), (123, -132088320), (124, -41817600), (125, 31726080), (126, 352200960), (127, -164643840), (131, -85587840), (134, -176359680), (135, 9953280), (136, -71642880), (138, -441262080), (139, -120476160), (140, -58786560), (144, 112518720), (146, 39191040), (148, 26542080), (150, -352719360)]

def pairMerged123 : Integer.Sparse (Fin 271) := [(0, 107661150), (1, 108569330), (2, -1047506780), (3, -11181755040), (4, 567605760), (5, 1015155160), (6, -46294980), (7, -2873515200), (8, -1383701280), (10, 1364895360), (12, -6638474880), (13, -6822632960), (14, 2177280), (15, 213528960), (16, -38024640), (17, 406581120), (18, -98599680), (20, -220631040), (22, 9953280), (23, 385273440), (24, 266954400), (25, -753537600), (26, -906551040), (27, -250269840), (28, -176359680), (29, 307644480), (30, -3688735680), (32, 3278920320), (33, 75479040), (34, -2041309760), (35, -561669120), (36, -1915228800), (37, -85112640), (38, -2520927360), (39, -2289461760), (40, -2771055360), (41, -166095360), (42, 647377920), (43, -109175040), (44, 303575040), (45, 3102848640), (46, 495776160), (47, -986843520), (48, 9953280), (49, -230999040), (50, 1861794720), (51, -1471774080), (53, 1631560320), (54, 2212015680), (55, -403519680), (58, 1819860480), (62, -308776320), (63, -7188480), (66, -9788640), (71, -1364895360), (72, -1364895360), (73, -1364895360), (79, 370667520), (81, -280834560), (82, 5667840), (83, -550333440), (85, -31034880), (86, 11335680), (88, -2058445440), (89, 1717476480), (92, -2941263360), (94, -1364895360), (95, -1364895360), (96, 5667840), (97, -1694502720), (98, 1471383360), (99, 681298560), (101, 8294400), (102, 13271040), (103, -22083840), (104, 79211520), (105, 158423040), (106, -829440), (107, 166717440), (108, 166717440), (110, -353756160), (111, -31236480), (112, 3386880), (113, -18662400), (116, 1451520), (117, 225037440), (120, -10160640), (122, -132088320), (124, 2903040), (125, 31726080), (126, 352200960), (127, -164643840), (130, -68697600), (131, -85587840), (133, 454965120), (134, -78382080), (135, 9953280), (136, -4561920), (138, -441262080), (139, -120476160), (140, 294969600), (142, -176878080), (143, 368778240), (144, 6531840), (145, 2903040), (146, 394721280), (147, -405241920), (148, -309130560), (150, -352719360)]

def pairMerged124 : Integer.Sparse (Fin 271) := [(0, 28607055), (1, 164967610), (2, 2799028965), (3, 214624800), (4, -4550304480), (5, -1873523240), (6, 163190240), (7, 1454983680), (8, 2332652160), (10, 1930970880), (12, 114093600), (13, 10633488400), (14, 2177280), (15, 213528960), (16, -38024640), (17, 406581120), (18, -98599680), (20, -220631040), (22, 9953280), (23, -6690290400), (24, -13594668480), (25, 3098561040), (26, 1112801280), (27, 6587249760), (28, -176359680), (29, -10260383040), (30, 4303512000), (31, 1811793920), (32, 9673600320), (33, 3352239360), (34, 3108460000), (35, -1630130400), (36, -3244484160), (37, 454407840), (38, -4168575360), (39, -4557669120), (40, 877625280), (41, -3144441600), (42, -658670400), (43, -3900000960), (44, 3665208960), (45, 4416958080), (46, -612787680), (47, -1541125440), (48, 9953280), (49, -4142057040), (50, -5479845120), (51, 5336209440), (53, -1660387680), (54, -2157253920), (55, 725408640), (56, 22256640), (58, -2008293120), (59, 2264051200), (60, -4070315520), (61, -8294400), (62, 8133120), (63, 158618880), (64, 2764800), (65, 309242880), (66, -9788640), (70, -2661120), (71, -864000), (72, -5045760), (73, -18869760), (74, -78243840), (75, 101606400), (76, 22809600), (77, 25453440), (79, -1131402240), (81, 53153280), (82, 93553920), (83, 323066880), (84, 80317440), (85, -31034880), (86, 11335680), (87, -4147200), (88, 177189120), (89, 274752000), (90, 46448640), (91, 291513600), (92, -274406400), (94, 100362240), (95, -216691200), (96, -217900800), (97, -13685760), (98, -29030400), (99, -2211840), (101, 8294400), (102, 13271040), (103, 61015680), (104, 79211520), (105, 158423040), (106, -829440), (107, 166717440), (108, 166717440), (109, -16588800), (110, 3720960), (111, -31236480), (112, 3386880), (113, -18662400), (115, 1356771840), (116, 1451520), (117, 225037440), (120, -10160640), (122, -132088320), (124, 2903040), (125, 31726080), (126, 352200960), (127, -164643840), (130, -68697600), (131, -85587840), (132, -465436800), (133, -969897600), (134, -78382080), (135, 9953280), (136, -4561920), (138, -441262080), (139, -120476160), (140, 294969600), (142, -176878080), (143, -215781120), (144, 6531840), (145, 2903040), (146, 394721280), (147, -405241920), (148, -309130560), (149, 22256640), (150, -352719360)]

def pairMerged125 : Integer.Sparse (Fin 271) := [(0, 20779368), (1, -210600080), (2, 50689520), (3, -176977920), (4, 474679680), (5, 148136960), (6, -21406640), (7, 18702720), (8, -52984320), (9, 11713280), (10, 45233280), (11, 33536640), (12, -285578880), (13, -781952000), (15, 38776320), (17, 275374080), (18, -82321920), (20, -78382080), (21, 37324800), (23, 33459840), (24, -119692800), (25, 146880000), (26, 174209280), (27, -73481760), (28, -78382080), (29, 149126400), (30, -257783040), (31, -2611200), (32, 278087040), (33, -42320640), (34, -323747200), (35, -136632960), (36, 93519360), (37, 20874240), (38, 59304960), (39, 92275200), (40, -4147200), (41, 24883200), (42, -69050880), (43, 142041600), (44, 467389440), (45, 169205760), (46, -125867520), (47, -78382080), (49, -235975680), (50, 274682880), (51, -280479360), (52, 145981440), (53, 370103040), (54, 25568640), (55, 143585280), (56, 97044480), (57, -972360), (58, 120890880), (59, -38563840), (60, -1382400), (61, -8294400), (62, 8133120), (63, 158618880), (64, 2764800), (65, -52300800), (66, -43640640), (67, 80223360), (68, 42957440), (69, 69461760), (70, -2661120), (71, -864000), (72, -5045760), (73, -18869760), (74, -78243840), (75, 101606400), (76, 22809600), (77, 25453440), (79, -46771200), (80, -77095680), (81, 53153280), (82, 93553920), (83, 323066880), (84, 80317440), (85, -31034880), (86, 11335680), (87, -4147200), (88, 177189120), (89, 274752000), (90, 46448640), (91, 291513600), (92, -274406400), (94, 100362240), (95, -216691200), (96, -217900800), (97, -13685760), (98, -29030400), (99, -2211840), (101, 8294400), (102, 13271040), (103, 61015680), (104, 79211520), (105, 158423040), (106, -829440), (107, 166717440), (108, 166717440), (109, -16588800), (110, 3720960), (111, -2488320), (112, 62709120), (113, 47001600), (114, 2488320), (115, -83297280), (116, 1451520), (117, 225037440), (120, -10160640), (122, -132088320), (124, 2903040), (125, 31726080), (126, 352200960), (127, -164643840), (130, -30032640), (131, -101727360), (132, 45941760), (133, 124369920), (134, -78382080), (135, 9953280), (136, -4561920), (138, -441262080), (139, -120476160), (140, 294969600), (142, -6497280), (143, -316391040), (144, 6531840), (145, 2903040), (146, 326039040), (147, 20632320), (148, 116743680), (149, 22256640), (150, -352719360)]

def pairMerged126 : Integer.Sparse (Fin 271) := [(0, -13225464), (1, -75312360), (2, -424080), (3, 849035520), (4, 139858560), (5, -28677600), (6, 2048400), (7, 49161600), (8, 32774400), (12, 341072640), (13, 569905920), (22, 294969600), (23, -49161600), (24, -98323200), (25, -91031040), (26, 159010560), (27, 36871200), (30, 21876480), (32, -234869760), (33, -17602560), (34, 163872000), (35, 147484800), (38, 589939200), (41, 589939200), (43, -158423040), (44, -475269120), (45, -158423040), (50, -393292800), (51, 65548800), (53, -442454400), (54, -147484800), (55, -344131200), (89, 147484800), (104, -79211520), (105, -158423040), (108, -158423040), (135, 294969600), (141, 294969600), (148, -49161600)]

def pairMerged127 : Integer.Sparse (Fin 271) := [(0, -12194280), (1, 380417400), (2, -118573200), (3, -1558080000), (4, -675561600), (5, 54050400), (6, -4096800), (7, -92505600), (8, -83520000), (12, -495043200), (13, -294969600), (15, -40435200), (17, -294969600), (22, -294969600), (23, 143510400), (24, 389318400), (25, 336182400), (26, -247392000), (27, -72748800), (30, 456710400), (32, 313200000), (34, -98323200), (38, -589939200), (41, -589939200), (43, -80870400), (47, -161740800), (50, 402796800), (51, -65548800), (53, 152236800), (54, 250560000), (55, 245808000), (63, 26956800), (66, -15660000), (89, -147484800), (91, -294969600), (92, -80870400), (110, 98323200), (111, 49161600), (112, 40435200), (113, 138758400), (117, -228355200), (125, -40435200), (126, -294969600), (131, 147484800), (135, -294969600), (137, -80870400), (140, -294969600), (141, -294969600), (147, 98323200), (148, 76118400)]

end MUB6.Certificate.PairData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMerge_Block4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairData

def pairMerged128 : Integer.Sparse (Fin 271) := [(0, -25419744), (1, 305105040), (2, -118997280), (3, -709044480), (4, -535703040), (5, 25372800), (6, -2048400), (7, -43344000), (8, -50745600), (12, -153970560), (13, 274936320), (15, -40435200), (17, -294969600), (23, 94348800), (24, 290995200), (25, 245151360), (26, -88381440), (27, -35877600), (30, 478586880), (32, 78330240), (33, -17602560), (34, 65548800), (35, 147484800), (43, -239293440), (44, -475269120), (45, -158423040), (47, -161740800), (50, 9504000), (53, -290217600), (54, 103075200), (55, -98323200), (63, 26956800), (66, -15660000), (91, -294969600), (92, -80870400), (104, -79211520), (105, -158423040), (108, -158423040), (110, 98323200), (111, 49161600), (112, 40435200), (113, 138758400), (117, -228355200), (125, -40435200), (126, -294969600), (131, 147484800), (137, -80870400), (140, -294969600), (147, 98323200), (148, 26956800)]

def pairMerged129 : Integer.Sparse (Fin 271) := [(0, 8872128), (1, -256813920), (2, 70392960), (3, 1050232320), (4, 503700480), (5, -17216640), (6, 853920), (7, 55203840), (8, 14400000), (12, 394767360), (13, 93242880), (15, 1658880), (18, 117987840), (23, -157870080), (24, -80870400), (25, -551715840), (26, 124070400), (27, 39744000), (30, -434833920), (32, -201070080), (33, 1290240), (34, 40250880), (36, 3317760), (42, 117987840), (43, 117987840), (46, 117987840), (47, 235975680), (49, 235975680), (50, -357281280), (51, 39697920), (53, -157317120), (54, -80317440), (55, -78658560), (63, -79764480), (66, 138240), (92, 117987840), (96, 117987840), (99, 3317760), (102, 3317760), (112, -552960), (113, -1658880), (117, 3317760), (118, 1658880), (122, 117987840), (125, 1658880), (126, 1658880), (127, 235975680), (131, -552960), (139, 117987840), (146, -552960), (148, -40435200)]

def pairMerged130 : Integer.Sparse (Fin 271) := [(0, -8782848), (1, 153694080), (2, -48994560), (3, -807045120), (4, -393431040), (5, 6128640), (6, -766080), (7, -8294400), (8, -4147200), (12, -64696320), (13, -52807680), (18, -35665920), (21, -37324800), (26, -405688320), (30, 73543680), (32, 122204160), (33, -72990720), (34, -24514560), (36, -74649600), (39, -37324800), (50, 12441600), (51, -12072960), (52, -145981440), (54, 61102080), (55, 24883200), (56, -108656640), (107, -145981440), (119, -35665920), (127, -71331840), (128, -37324800), (135, -37324800)]

def pairMerged131 : Integer.Sparse (Fin 271) := [(0, 89280), (1, -103119840), (2, 21398400), (3, 243187200), (4, 110269440), (5, -11088000), (6, 87840), (7, 46909440), (8, 10252800), (12, 330071040), (13, 40435200), (15, 1658880), (18, 82321920), (21, -37324800), (23, -157870080), (24, -80870400), (25, -551715840), (26, -281617920), (27, 39744000), (30, -361290240), (32, -78865920), (33, -71700480), (34, 15736320), (36, -71331840), (39, -37324800), (42, 117987840), (43, 117987840), (46, 117987840), (47, 235975680), (49, 235975680), (50, -344839680), (51, 27624960), (52, -145981440), (53, -157317120), (54, -19215360), (55, -53775360), (56, -108656640), (63, -79764480), (66, 138240), (92, 117987840), (96, 117987840), (99, 3317760), (102, 3317760), (107, -145981440), (112, -552960), (113, -1658880), (117, 3317760), (118, 1658880), (119, -35665920), (122, 117987840), (125, 1658880), (126, 1658880), (127, 164643840), (128, -37324800), (131, -552960), (135, -37324800), (139, 117987840), (146, -552960), (148, -40435200)]

def pairMerged132 : Integer.Sparse (Fin 271) := [(0, -25330464), (1, 201985200), (2, -97598880), (3, -465857280), (4, -425433600), (5, 14284800), (6, -1960560), (7, 3565440), (8, -40492800), (12, 176100480), (13, 315371520), (15, -38776320), (17, -294969600), (18, 82321920), (21, -37324800), (23, -63521280), (24, 210124800), (25, -306564480), (26, -369999360), (27, 3866400), (30, 117296640), (32, -535680), (33, -89303040), (34, 81285120), (35, 147484800), (36, -71331840), (39, -37324800), (42, 117987840), (43, -121305600), (44, -475269120), (45, -158423040), (46, 117987840), (47, 74234880), (49, 235975680), (50, -335335680), (51, 27624960), (52, -145981440), (53, -447534720), (54, 83859840), (55, -152098560), (56, -108656640), (63, -52807680), (66, -15521760), (91, -294969600), (92, 37117440), (96, 117987840), (99, 3317760), (102, 3317760), (104, -79211520), (105, -158423040), (107, -145981440), (108, -158423040), (110, 98323200), (111, 49161600), (112, 39882240), (113, 137099520), (117, -225037440), (118, 1658880), (119, -35665920), (122, 117987840), (125, -38776320), (126, -293310720), (127, 164643840), (128, -37324800), (131, 146931840), (135, -37324800), (137, -80870400), (139, 117987840), (140, -294969600), (146, -552960), (147, 98323200), (148, -13478400)]

def pairMerged133 : Integer.Sparse (Fin 271) := [(0, 480456), (1, -15346440), (2, -30987000), (3, -25176960), (5, 90128160), (6, -12461040), (7, -88629120), (8, -92655360), (9, 56429280), (34, -36253440), (51, -16104960), (57, -1803960), (67, -113806080), (68, -59086080), (69, -185310720), (163, 31726080), (164, -14601600), (183, -12078720), (222, -16104960), (247, 12078720), (268, 24157440)]

def pairMerged134 : Integer.Sparse (Fin 271) := [(0, -134328), (1, 9644880), (2, -5616120), (3, -208915200), (4, -68348160), (5, 62546400), (6, -11042280), (7, -11612160), (9, 15690720), (11, -68348160), (26, -136696320), (34, -211495680), (51, -183552000), (54, 96716160), (57, -752280), (67, -7741440), (68, -5160960), (143, 205044480), (164, -14616960), (183, -3870720), (222, -7741440), (247, 11612160), (248, 96716160), (249, 64477440)]

def pairMerged135 : Integer.Sparse (Fin 271) := [(0, 346128), (1, -5701560), (2, -36603120), (3, -234092160), (4, -68348160), (5, 152674560), (6, -23503320), (7, -100241280), (8, -92655360), (9, 72120000), (11, -68348160), (26, -136696320), (34, -247749120), (51, -199656960), (54, 96716160), (57, -2556240), (67, -121547520), (68, -64247040), (69, -185310720), (143, 205044480), (163, 31726080), (164, -29218560), (183, -15949440), (222, -23846400), (247, 23690880), (248, 96716160), (249, 64477440), (268, 24157440)]

def pairMerged136 : Integer.Sparse (Fin 271) := [(0, -229104), (1, 4459320), (2, 11559840), (3, 56712960), (4, 576000), (5, -21784320), (6, 3760560), (7, 22936320), (8, 5760000), (9, -5734080), (12, 17752320), (13, 79885440), (34, 63285120), (50, -5184000), (51, 54984960), (53, -26628480), (57, 220920), (67, 12332160), (68, 7069440), (69, 6912000), (80, 47339520), (115, 44380800), (132, -53256960), (133, -53256960), (164, 11834880), (181, -5184000), (182, -3456000), (183, 9452160), (219, -26628480), (222, 17752320), (246, -17752320), (247, -26628480)]

def pairMerged137 : Integer.Sparse (Fin 271) := [(0, -554040), (1, 11746800), (2, -4980600), (3, -45336960), (4, -12792960), (5, 5163840), (6, 2489400), (7, -55883520), (8, -13916160), (9, -10238400), (11, 5834880), (13, 23339520), (26, -6958080), (27, -6985440), (34, -2246400), (50, 55883520), (51, 8300160), (55, -35009280), (57, 147240), (66, -6985440), (67, -31420800), (69, 4711680), (80, 23339520), (111, 27941760), (113, 55883520), (115, 29174400), (133, -70018560), (143, -17504640), (164, 5834880), (181, 55883520), (183, -6958080), (219, -17504640), (220, 55883520), (222, -6958080), (263, -70018560), (268, -35009280)]

def pairMerged138 : Integer.Sparse (Fin 271) := [(0, -783144), (1, 16206120), (2, 6579240), (3, 11376000), (4, -12216960), (5, -16620480), (6, 6249960), (7, -32947200), (8, -8156160), (9, -15972480), (11, 5834880), (12, 17752320), (13, 103224960), (26, -6958080), (27, -6985440), (34, 61038720), (50, 50699520), (51, 63285120), (53, -26628480), (55, -35009280), (57, 368160), (66, -6985440), (67, -19088640), (68, 7069440), (69, 11623680), (80, 70679040), (111, 27941760), (113, 55883520), (115, 73555200), (132, -53256960), (133, -123275520), (143, -17504640), (164, 17669760), (181, 50699520), (182, -3456000), (183, 2494080), (219, -44133120), (220, 55883520), (222, 10794240), (246, -17752320), (247, -26628480), (263, -70018560), (268, -35009280)]

def pairMerged139 : Integer.Sparse (Fin 271) := [(0, -437016), (1, 10504560), (2, -30023880), (3, -222716160), (4, -80565120), (5, 136054080), (6, -17253360), (7, -133188480), (8, -100811520), (9, 56147520), (11, -62513280), (12, 17752320), (13, 103224960), (26, -143654400), (27, -6985440), (34, -186710400), (50, 50699520), (51, -136371840), (53, -26628480), (54, 96716160), (55, -35009280), (57, -2188080), (66, -6985440), (67, -140636160), (68, -57177600), (69, -173687040), (80, 70679040), (111, 27941760), (113, 55883520), (115, 73555200), (132, -53256960), (133, -123275520), (143, 187539840), (163, 31726080), (164, -11548800), (181, 50699520), (182, -3456000), (183, -13455360), (219, -44133120), (220, 55883520), (222, -13052160), (246, -17752320), (247, -2937600), (248, 96716160), (249, 64477440), (263, -70018560), (268, -10851840)]

def pairMerged140 : Integer.Sparse (Fin 271) := [(0, -25767480), (1, 212489760), (2, -127622760), (3, -688573440), (4, -505998720), (5, 150338880), (6, -19213920), (7, -129623040), (8, -141304320), (9, 56147520), (11, -62513280), (12, 193852800), (13, 418596480), (15, -38776320), (17, -294969600), (18, 82321920), (21, -37324800), (23, -63521280), (24, 210124800), (25, -306564480), (26, -513653760), (27, -3119040), (30, 117296640), (32, -535680), (33, -89303040), (34, -105425280), (35, 147484800), (36, -71331840), (39, -37324800), (42, 117987840), (43, -121305600), (44, -475269120), (45, -158423040), (46, 117987840), (47, 74234880), (49, 235975680), (50, -284636160), (51, -108746880), (52, -145981440), (53, -474163200), (54, 180576000), (55, -187107840), (56, -108656640), (57, -2188080), (63, -52807680), (66, -22507200), (67, -140636160), (68, -57177600), (69, -173687040), (80, 70679040), (91, -294969600), (92, 37117440), (96, 117987840), (99, 3317760), (102, 3317760), (104, -79211520), (105, -158423040), (107, -145981440), (108, -158423040), (110, 98323200), (111, 77103360), (112, 39882240), (113, 192983040), (115, 73555200), (117, -225037440), (118, 1658880), (119, -35665920), (122, 117987840), (125, -38776320), (126, -293310720), (127, 164643840), (128, -37324800), (131, 146931840), (132, -53256960), (133, -123275520), (135, -37324800), (137, -80870400), (139, 117987840), (140, -294969600), (143, 187539840), (146, -552960), (147, 98323200), (148, -13478400), (163, 31726080), (164, -11548800), (181, 50699520), (182, -3456000), (183, -13455360), (219, -44133120), (220, 55883520), (222, -13052160), (246, -17752320), (247, -2937600), (248, 96716160), (249, 64477440), (263, -70018560), (268, -10851840)]

def pairMerged141 : Integer.Sparse (Fin 271) := [(0, 294408), (1, -8806320), (2, -8317080), (3, 49213440), (4, 30620160), (5, -14554080), (6, -951480), (7, -22291200), (8, -8916480), (9, -1283040), (11, 30620160), (12, -17832960), (13, -75790080), (26, 76550400), (27, 11482560), (34, 67046400), (50, 26749440), (51, -22878720), (53, 13374720), (54, -22965120), (57, 199800), (66, 8138880), (67, -8916480), (68, -8916480), (69, -4458240), (80, -17832960), (112, 26749440), (113, 13374720), (115, -22291200), (148, -91860480), (164, 3196800), (182, 26749440), (183, -8916480), (219, 13374720), (220, -45930240), (221, 26749440), (222, 6393600), (248, -22965120)]

def pairMerged142 : Integer.Sparse (Fin 271) := [(0, -668736), (1, 8665920), (2, 44087040), (3, 97920000), (4, 3317760), (5, -152421120), (6, 13080960), (7, 17372160), (8, 104232960), (9, -34744320), (12, 3317760), (13, 4423680), (26, 3317760), (27, 39709440), (34, 3317760), (50, -9953280), (51, 107550720), (54, -9953280), (57, 2171520), (66, 39087360), (67, 17372160), (69, 86860800), (113, -52116480), (114, -2488320), (115, 829440), (146, -104232960), (147, -104232960), (181, -52116480), (183, 17372160), (220, -9953280), (221, -6635520), (222, 1105920)]

def pairMerged143 : Integer.Sparse (Fin 271) := [(0, -374328), (1, -140400), (2, 35769960), (3, 147133440), (4, 33937920), (5, -166975200), (6, 12129480), (7, -4919040), (8, 95316480), (9, -36027360), (11, 30620160), (12, -14515200), (13, -71366400), (26, 79868160), (27, 51192000), (34, 70364160), (50, 16796160), (51, 84672000), (53, 13374720), (54, -32918400), (57, 2371320), (66, 47226240), (67, 8455680), (68, -8916480), (69, 82402560), (80, -17832960), (112, 26749440), (113, -38741760), (114, -2488320), (115, -21461760), (146, -104232960), (147, -104232960), (148, -91860480), (164, 3196800), (181, -52116480), (182, 26749440), (183, 8455680), (219, 13374720), (220, -55883520), (221, 20113920), (222, 7499520), (248, -22965120)]

def pairMerged144 : Integer.Sparse (Fin 271) := [(0, -710208), (1, 1988640), (2, 2613600), (3, 53464320), (4, 4999680), (5, -47597760), (6, 2922480), (7, 9999360), (8, 9999360), (9, -11263680), (11, 16704000), (12, 3352320), (13, 50169600), (26, 43407360), (34, 96871680), (51, 33465600), (54, -10056960), (55, -14999040), (57, 834480), (66, 16277760), (68, 9999360), (69, 14999040), (80, 16704000), (115, 6704640), (131, -29998080), (146, -14999040), (147, -20113920), (148, -14999040), (164, 8352000), (182, -14999040), (183, 4999680), (221, -20113920), (222, 6704640), (249, -10056960), (263, -14999040)]

def pairMerged145 : Integer.Sparse (Fin 271) := [(0, 527616), (1, -14679360), (2, -21980160), (3, -35182080), (5, 71337600), (6, -7646400), (7, -79833600), (8, -80732160), (9, 17815680), (13, -6428160), (26, -6428160), (34, -63636480), (51, -53222400), (53, 19284480), (59, -4285440), (67, -140382720), (68, -64235520), (69, -194503680), (151, 60549120), (152, -17740800), (153, 19284480), (154, 12856320), (222, -22325760)]

def pairMerged146 : Integer.Sparse (Fin 271) := [(0, -182592), (1, -12690720), (2, -19366560), (3, 18282240), (4, 4999680), (5, 23739840), (6, -4723920), (7, -69834240), (8, -70732800), (9, 6552000), (11, 16704000), (12, 3352320), (13, 43741440), (26, 36979200), (34, 33235200), (51, -19756800), (53, 19284480), (54, -10056960), (55, -14999040), (57, 834480), (59, -4285440), (66, 16277760), (67, -140382720), (68, -54236160), (69, -179504640), (80, 16704000), (115, 6704640), (131, -29998080), (146, -14999040), (147, -20113920), (148, -14999040), (151, 60549120), (152, -17740800), (153, 19284480), (154, 12856320), (164, 8352000), (182, -14999040), (183, 4999680), (221, -20113920), (222, -15621120), (249, -10056960), (263, -14999040)]

def pairMerged147 : Integer.Sparse (Fin 271) := [(0, -556920), (1, -12831120), (2, 16403400), (3, 165415680), (4, 38937600), (5, -143235360), (6, 7405560), (7, -74753280), (8, 24583680), (9, -29475360), (11, 47324160), (12, -11162880), (13, -27624960), (26, 116847360), (27, 51192000), (34, 103599360), (50, 16796160), (51, 64915200), (53, 32659200), (54, -42975360), (55, -14999040), (57, 3205800), (59, -4285440), (66, 63504000), (67, -131927040), (68, -63152640), (69, -97102080), (80, -1128960), (112, 26749440), (113, -38741760), (114, -2488320), (115, -14757120), (131, -29998080), (146, -119232000), (147, -124346880), (148, -106859520), (151, 60549120), (152, -17740800), (153, 19284480), (154, 12856320), (164, 11548800), (181, -52116480), (182, 11750400), (183, 13455360), (219, 13374720), (220, -55883520), (222, -8121600), (248, -22965120), (249, -10056960), (263, -14999040)]

def pairMerged148 : Integer.Sparse (Fin 271) := [(0, -758592), (1, 8985600), (2, 20851200), (3, 129162240), (4, 18570240), (5, -66366720), (6, 6580800), (7, 145244160), (8, 80916480), (9, -9699840), (13, 3317760), (26, 54051840), (34, 163814400), (50, -2488320), (51, 62346240), (55, -4976640), (58, -4976640), (65, 35481600), (67, 94510080), (68, 54051840), (69, 83404800), (79, -53222400), (115, 1658880), (151, -55710720), (152, 17740800), (153, -2488320), (155, -9953280), (222, 19399680)]

def pairMerged149 : Integer.Sparse (Fin 271) := [(0, 28944), (1, -25316280), (2, 3903840), (3, 336885120), (4, 73889280), (5, -19432800), (6, 4088520), (7, 82460160), (9, -1896480), (12, 4285440), (13, 103789440), (26, 235952640), (33, 107089920), (34, 178220160), (51, 36944640), (54, -68273280), (59, 2856960), (63, -110833920), (65, 82460160), (67, 6157440), (68, 22757760), (69, 1428480), (112, -55416960), (131, -12856320), (152, 15171840), (156, -36944640), (158, -8570880)]

def pairMerged150 : Integer.Sparse (Fin 271) := [(0, -729648), (1, -16330680), (2, 24755040), (3, 466047360), (4, 92459520), (5, -85799520), (6, 10669320), (7, 227704320), (8, 80916480), (9, -11596320), (12, 4285440), (13, 107107200), (26, 290004480), (33, 107089920), (34, 342034560), (50, -2488320), (51, 99290880), (54, -68273280), (55, -4976640), (58, -4976640), (59, 2856960), (63, -110833920), (65, 117941760), (67, 100667520), (68, 76809600), (69, 84833280), (79, -53222400), (112, -55416960), (115, 1658880), (131, -12856320), (151, -55710720), (152, 32912640), (153, -2488320), (155, -9953280), (156, -36944640), (158, -8570880), (222, 19399680)]

def pairMerged151 : Integer.Sparse (Fin 271) := [(0, 338040), (1, 378720), (2, 461880), (3, -61228800), (4, -2856960), (5, 22893120), (6, -4328640), (7, -42658560), (8, -2856960), (9, 7228800), (13, -29456640), (26, -48372480), (33, -19457280), (34, -95316480), (51, -18570240), (53, 36944640), (55, 8570880), (59, -7142400), (63, 4285440), (65, -27486720), (67, -16600320), (68, -27486720), (69, -15171840), (111, 18472320), (112, 8570880), (113, 4285440), (115, -5713920), (130, 18472320), (131, 41230080), (152, -15171840), (153, 36944640), (154, 4285440), (155, 8570880), (156, 36944640), (158, 8570880), (222, -16600320)]

def pairMerged152 : Integer.Sparse (Fin 271) := [(0, -1415088), (1, 13188240), (2, -8188560), (3, -70548480), (4, -46828800), (5, -50230080), (6, 15040080), (7, -9492480), (8, 45043200), (9, -22968000), (10, 19560960), (11, -13040640), (12, -6520320), (13, -13040640), (26, -51575040), (32, 39121920), (33, -26081280), (34, -86549760), (50, -55123200), (51, 26668800), (54, 19560960), (65, -65203200), (67, 73497600), (68, 18374400), (69, 110246400), (79, 156487680), (80, -6520320), (110, -110246400), (111, -110246400), (113, -55123200), (131, -55123200), (143, 39121920), (146, -110246400), (153, -55123200), (160, 39121920), (162, -13040640), (179, 39121920), (180, 39121920), (222, 18374400)]

def pairMerged153 : Integer.Sparse (Fin 271) := [(0, -1077048), (1, 13566960), (2, -7726680), (3, -131777280), (4, -49685760), (5, -27336960), (6, 10711440), (7, -52151040), (8, 42186240), (9, -15739200), (10, 19560960), (11, -13040640), (12, -6520320), (13, -42497280), (26, -99947520), (32, 39121920), (33, -45538560), (34, -181866240), (50, -55123200), (51, 8098560), (53, 36944640), (54, 19560960), (55, 8570880), (59, -7142400), (63, 4285440), (65, -92689920), (67, 56897280), (68, -9112320), (69, 95074560), (79, 156487680), (80, -6520320), (110, -110246400), (111, -91774080), (112, 8570880), (113, -50837760), (115, -5713920), (130, 18472320), (131, -13893120), (143, 39121920), (146, -110246400), (152, -15171840), (153, -18178560), (154, 4285440), (155, 8570880), (156, 36944640), (158, 8570880), (160, 39121920), (162, -13040640), (179, 39121920), (180, 39121920), (222, 1774080)]

def pairMerged154 : Integer.Sparse (Fin 271) := [(0, -1806696), (1, -2763720), (2, 17028360), (3, 334270080), (4, 42773760), (5, -113136480), (6, 21380760), (7, 175553280), (8, 123102720), (9, -27335520), (10, 19560960), (11, -13040640), (12, -2234880), (13, 64609920), (26, 190056960), (32, 39121920), (33, 61551360), (34, 160168320), (50, -57611520), (51, 107389440), (53, 36944640), (54, -48712320), (55, 3594240), (58, -4976640), (59, -4285440), (63, -106548480), (65, 25251840), (67, 157564800), (68, 67697280), (69, 179907840), (79, 103265280), (80, -6520320), (110, -110246400), (111, -91774080), (112, -46846080), (113, -50837760), (115, -4055040), (130, 18472320), (131, -26749440), (143, 39121920), (146, -110246400), (151, -55710720), (152, 17740800), (153, -20666880), (154, 4285440), (155, -1382400), (160, 39121920), (162, -13040640), (179, 39121920), (180, 39121920), (222, 21173760)]

def pairMerged155 : Integer.Sparse (Fin 271) := [(0, -2363616), (1, -15594840), (2, 33431760), (3, 499685760), (4, 81711360), (5, -256371840), (6, 28786320), (7, 100800000), (8, 147686400), (9, -56810880), (10, 19560960), (11, 34283520), (12, -13397760), (13, 36984960), (26, 306904320), (27, 51192000), (32, 39121920), (33, 61551360), (34, 263767680), (50, -40815360), (51, 172304640), (53, 69603840), (54, -91687680), (55, -11404800), (57, 3205800), (58, -4976640), (59, -8570880), (63, -106548480), (65, 25251840), (66, 63504000), (67, 25637760), (68, 4544640), (69, 82805760), (79, 103265280), (80, -7649280), (110, -110246400), (111, -91774080), (112, -20096640), (113, -89579520), (114, -2488320), (115, -18812160), (130, 18472320), (131, -56747520), (143, 39121920), (146, -229478400), (147, -124346880), (148, -106859520), (151, 4838400), (153, -1382400), (154, 17141760), (155, -1382400), (160, 39121920), (162, -13040640), (164, 11548800), (179, 39121920), (180, 39121920), (181, -52116480), (182, 11750400), (183, 13455360), (219, 13374720), (220, -55883520), (222, 13052160), (248, -22965120), (249, -10056960), (263, -14999040)]

def pairMerged156 : Integer.Sparse (Fin 271) := [(0, -28131096), (1, 196894920), (2, -94191000), (3, -188887680), (4, -424287360), (5, -106032960), (6, 9572400), (7, -28823040), (8, 6382080), (9, -663360), (10, 19560960), (11, -28229760), (12, 180455040), (13, 455581440), (15, -38776320), (17, -294969600), (18, 82321920), (21, -37324800), (23, -63521280), (24, 210124800), (25, -306564480), (26, -206749440), (27, 48072960), (30, 117296640), (32, 38586240), (33, -27751680), (34, 158342400), (35, 147484800), (36, -71331840), (39, -37324800), (42, 117987840), (43, -121305600), (44, -475269120), (45, -158423040), (46, 117987840), (47, 74234880), (49, 235975680), (50, -325451520), (51, 63557760), (52, -145981440), (53, -404559360), (54, 88888320), (55, -198512640), (56, -108656640), (57, 1017720), (58, -4976640), (59, -8570880), (63, -159356160), (65, 25251840), (66, 40996800), (67, -114998400), (68, -52632960), (69, -90881280), (79, 103265280), (80, 63029760), (91, -294969600), (92, 37117440), (96, 117987840), (99, 3317760), (102, 3317760), (104, -79211520), (105, -158423040), (107, -145981440), (108, -158423040), (110, -11923200), (111, -14670720), (112, 19785600), (113, 103403520), (114, -2488320), (115, 54743040), (117, -225037440), (118, 1658880), (119, -35665920), (122, 117987840), (125, -38776320), (126, -293310720), (127, 164643840), (128, -37324800), (130, 18472320), (131, 90184320), (132, -53256960), (133, -123275520), (135, -37324800), (137, -80870400), (139, 117987840), (140, -294969600), (143, 226661760), (146, -230031360), (147, -26023680), (148, -120337920), (151, 4838400), (153, -1382400), (154, 17141760), (155, -1382400), (160, 39121920), (162, -13040640), (163, 31726080), (179, 39121920), (180, 39121920), (181, -1416960), (182, 8294400), (219, -30758400), (246, -17752320), (247, -2937600), (248, 73751040), (249, 54420480), (263, -85017600), (268, -10851840)]

def pairMerged157 : Integer.Sparse (Fin 271) := [(0, -543168), (1, 1853440), (2, 15278400), (3, 173967360), (4, 29936640), (5, -32602880), (6, 3902720), (7, 62622720), (8, 21765120), (11, 13593600), (12, 29821440), (13, 111191040), (26, 76216320), (32, -32532480), (33, 27187200), (34, 144133120), (51, 84157440), (53, -16266240), (58, -81331200), (59, 27136000), (65, 32686080), (79, -49029120), (80, 10844160), (115, 32532480), (132, -8133120), (133, -16266240), (143, -40780800), (159, -16266240), (160, -24514560), (162, 13593600), (218, -32532480), (245, -32532480)]

def pairMerged158 : Integer.Sparse (Fin 271) := [(0, 24960), (1, 270720), (2, -679680), (3, -10321920), (4, -2304000), (5, 1244160), (6, -161280), (7, -2211840), (8, -737280), (11, -1474560), (12, -2211840), (13, -5130240), (26, -4515840), (31, -153600), (32, 3870720), (33, -1658880), (34, -6266880), (50, 1382400), (51, -3409920), (53, 552960), (55, 1105920), (58, 1105920), (59, -1198080), (60, 1382400), (65, -737280), (79, 2211840), (114, 1382400), (115, -645120), (143, 5529600), (159, 552960), (161, 1105920), (162, -552960), (217, 2764800), (218, 2211840), (245, 1105920)]

def pairMerged159 : Integer.Sparse (Fin 271) := [(0, -518208), (1, 2124160), (2, 14598720), (3, 163645440), (4, 27632640), (5, -31358720), (6, 3741440), (7, 60410880), (8, 21027840), (11, 12119040), (12, 27609600), (13, 106060800), (26, 71700480), (31, -153600), (32, -28661760), (33, 25528320), (34, 137866240), (50, 1382400), (51, 80747520), (53, -15713280), (55, 1105920), (58, -80225280), (59, 25937920), (60, 1382400), (65, 31948800), (79, -46817280), (80, 10844160), (114, 1382400), (115, 31887360), (132, -8133120), (133, -16266240), (143, -35251200), (159, -15713280), (160, -24514560), (161, 1105920), (162, 13040640), (217, 2764800), (218, -30320640), (245, -31426560)]

end MUB6.Certificate.PairData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMerge_Block5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairData

def pairMerged160 : Integer.Sparse (Fin 271) := [(0, -322560), (1, 720000), (2, 1324800), (3, 23500800), (5, -8870400), (6, 1411200), (11, 1382400), (12, 2304000), (13, 23961600), (26, 8294400), (32, -5529600), (33, 921600), (34, 18432000), (51, 21657600), (54, -4147200), (59, 921600), (62, -8294400), (80, 1843200), (110, -11059200), (115, 3225600), (147, -11059200), (179, -5529600), (217, -2764800), (245, -4147200)]

def pairMerged161 : Integer.Sparse (Fin 271) := [(0, 603720), (1, 6866280), (2, -3958560), (3, -88750080), (5, 6340320), (6, -429840), (7, -36616320), (8, -8847360), (9, -72000), (10, 6825600), (12, -15926400), (13, -4550400), (23, 54604800), (24, 27302400), (26, -9100800), (27, -11944800), (34, -20494080), (50, 40953600), (51, 1935360), (53, 47779200), (54, 40953600), (67, -2828160), (68, -4083840), (69, 12222720), (75, -81907200), (77, -20476800), (143, 27302400), (151, -5806080), (163, 5374080), (165, 1451520), (166, 5806080), (167, 5806080), (174, -40953600), (175, -61430400), (247, -1451520), (268, -2903040)]

def pairMerged162 : Integer.Sparse (Fin 271) := [(0, 281160), (1, 7586280), (2, -2633760), (3, -65249280), (5, -2530080), (6, 981360), (7, -36616320), (8, -8847360), (9, -72000), (10, 6825600), (11, 1382400), (12, -13622400), (13, 19411200), (23, 54604800), (24, 27302400), (26, -806400), (27, -11944800), (32, -5529600), (33, 921600), (34, -2062080), (50, 40953600), (51, 23592960), (53, 47779200), (54, 36806400), (59, 921600), (62, -8294400), (67, -2828160), (68, -4083840), (69, 12222720), (75, -81907200), (77, -20476800), (80, 1843200), (110, -11059200), (115, 3225600), (143, 27302400), (147, -11059200), (151, -5806080), (163, 5374080), (165, 1451520), (166, 5806080), (167, 5806080), (174, -40953600), (175, -61430400), (179, -5529600), (217, -2764800), (245, -4147200), (247, -1451520), (268, -2903040)]

def pairMerged163 : Integer.Sparse (Fin 271) := [(0, -237048), (1, 9710440), (2, 11964960), (3, 98396160), (4, 27632640), (5, -33888800), (6, 4722800), (7, 23794560), (8, 12180480), (9, -72000), (10, 6825600), (11, 13501440), (12, 13987200), (13, 125472000), (23, 54604800), (24, 27302400), (26, 70894080), (27, -11944800), (31, -153600), (32, -34191360), (33, 26449920), (34, 135804160), (50, 42336000), (51, 104340480), (53, 32065920), (54, 36806400), (55, 1105920), (58, -80225280), (59, 26859520), (60, 1382400), (62, -8294400), (65, 31948800), (67, -2828160), (68, -4083840), (69, 12222720), (75, -81907200), (77, -20476800), (79, -46817280), (80, 12687360), (110, -11059200), (114, 1382400), (115, 35112960), (132, -8133120), (133, -16266240), (143, -7948800), (147, -11059200), (151, -5806080), (159, -15713280), (160, -24514560), (161, 1105920), (162, 13040640), (163, 5374080), (165, 1451520), (166, 5806080), (167, 5806080), (174, -40953600), (175, -61430400), (179, -5529600), (218, -30320640), (245, -35573760), (247, -1451520), (268, -2903040)]

def pairMerged164 : Integer.Sparse (Fin 271) := [(0, 467424), (1, -1856160), (2, -15180480), (3, -52646400), (4, -3801600), (5, 25424640), (6, -1509120), (7, -57945600), (8, -43361280), (9, 3018240), (10, 16312320), (12, -11243520), (13, -12879360), (23, 2903040), (24, 13409280), (26, -2534400), (27, -4078080), (29, 3801600), (34, -33431040), (50, 34629120), (51, -11543040), (53, 15413760), (54, 3801600), (55, 15206400), (58, 30827520), (67, -20113920), (68, -6105600), (69, -41886720), (70, -8709120), (71, -17418240), (72, -40227840), (73, -11404800), (76, -22809600), (132, 8709120), (133, 7603200), (143, 7603200), (151, 19215360), (163, 6704640), (165, -8709120), (166, -28823040), (168, -11404800), (172, -22809600), (173, -22809600), (247, 12510720), (268, 3801600)]

def pairMerged165 : Integer.Sparse (Fin 271) := [(0, 432288), (1, -8563680), (2, -17930880), (3, -29698560), (4, -1359360), (5, 30919680), (6, -2249280), (7, -30965760), (8, -49489920), (9, 2131200), (10, 276480), (12, -92160), (13, -46080), (23, 414720), (24, 138240), (26, -92160), (27, -69120), (34, -13109760), (50, 12510720), (51, -24560640), (53, 691200), (54, 138240), (58, 276480), (67, -18593280), (68, -7349760), (69, -27555840), (70, -829440), (71, -414720), (75, -829440), (79, 16312320), (84, -24468480), (132, 276480), (143, 276480), (151, 8432640), (163, 138240), (165, -414720), (167, -24468480), (168, -414720), (170, -829440), (171, -829440), (194, -12234240), (197, -24468480), (199, -24468480), (247, 276480), (268, 12234240)]

def pairMerged166 : Integer.Sparse (Fin 271) := [(0, 899712), (1, -10419840), (2, -33111360), (3, -82344960), (4, -5160960), (5, 56344320), (6, -3758400), (7, -88911360), (8, -92851200), (9, 5149440), (10, 16588800), (12, -11335680), (13, -12925440), (23, 3317760), (24, 13547520), (26, -2626560), (27, -4147200), (29, 3801600), (34, -46540800), (50, 47139840), (51, -36103680), (53, 16104960), (54, 3939840), (55, 15206400), (58, 31104000), (67, -38707200), (68, -13455360), (69, -69442560), (70, -9538560), (71, -17832960), (72, -40227840), (73, -11404800), (75, -829440), (76, -22809600), (79, 16312320), (84, -24468480), (132, 8985600), (133, 7603200), (143, 7879680), (151, 27648000), (163, 6842880), (165, -9123840), (166, -28823040), (167, -24468480), (168, -11819520), (170, -829440), (171, -829440), (172, -22809600), (173, -22809600), (194, -12234240), (197, -24468480), (199, -24468480), (247, 12787200), (268, 16035840)]

def pairMerged167 : Integer.Sparse (Fin 271) := [(0, -480096), (1, 5484960), (2, 17333280), (3, 56056320), (4, 9446400), (5, -31104000), (6, 2106720), (7, 50457600), (8, 44997120), (9, -2407680), (12, 1704960), (13, 7557120), (24, -2557440), (26, 7188480), (34, 35089920), (50, -26887680), (51, 28753920), (55, -18662400), (58, -15552000), (67, 20298240), (68, 8593920), (69, 27555840), (71, 15344640), (74, 37324800), (75, 9331200), (79, -10229760), (82, 7672320), (83, 15344640), (133, -17556480), (143, -10782720), (151, -21565440), (163, -7672320), (165, 7672320), (166, 15344640), (167, 18662400), (170, 18662400), (171, 9331200), (172, 18662400), (194, 23016960), (199, 15344640), (247, -5667840), (268, -13893120)]

def pairMerged168 : Integer.Sparse (Fin 271) := [(0, 589032), (1, 3965760), (2, 2307240), (3, -60883200), (4, 852480), (5, -6760800), (6, 449280), (7, -22037760), (8, 32394240), (9, 2191680), (12, -15586560), (13, -15586560), (23, 23379840), (26, 1704960), (30, 46759680), (32, 46759680), (34, -21795840), (50, -7672320), (51, -17533440), (67, -7914240), (68, -14734080), (69, 25574400), (79, 93519360), (83, 15344640), (88, -140279040), (111, 23379840), (130, 23379840), (143, -5114880), (151, 41644800), (163, -2557440), (166, 7672320), (194, -132606720), (197, 15344640), (199, 15344640), (205, -140279040), (268, 41644800)]

def pairMerged169 : Integer.Sparse (Fin 271) := [(0, 108936), (1, 9450720), (2, 19640520), (3, -4826880), (4, 10298880), (5, -37864800), (6, 2556000), (7, 28419840), (8, 77391360), (9, -216000), (12, -13881600), (13, -8029440), (23, 23379840), (24, -2557440), (26, 8893440), (30, 46759680), (32, 46759680), (34, 13294080), (50, -34560000), (51, 11220480), (55, -18662400), (58, -15552000), (67, 12384000), (68, -6140160), (69, 53130240), (71, 15344640), (74, 37324800), (75, 9331200), (79, 83289600), (82, 7672320), (83, 30689280), (88, -140279040), (111, 23379840), (130, 23379840), (133, -17556480), (143, -15897600), (151, 20079360), (163, -10229760), (165, 7672320), (166, 23016960), (167, 18662400), (170, 18662400), (171, 9331200), (172, 18662400), (194, -109589760), (197, 15344640), (199, 30689280), (205, -140279040), (247, -5667840), (268, 27751680)]

def pairMerged170 : Integer.Sparse (Fin 271) := [(0, 1008648), (1, -969120), (2, -13470840), (3, -87171840), (4, 5137920), (5, 18479520), (6, -1202400), (7, -60491520), (8, -15459840), (9, 4933440), (10, 16588800), (12, -25217280), (13, -20954880), (23, 26697600), (24, 10990080), (26, 6266880), (27, -4147200), (29, 3801600), (30, 46759680), (32, 46759680), (34, -33246720), (50, 12579840), (51, -24883200), (53, 16104960), (54, 3939840), (55, -3456000), (58, 15552000), (67, -26323200), (68, -19595520), (69, -16312320), (70, -9538560), (71, -2488320), (72, -40227840), (73, -11404800), (74, 37324800), (75, 8501760), (76, -22809600), (79, 99601920), (82, 7672320), (83, 30689280), (84, -24468480), (88, -140279040), (111, 23379840), (130, 23379840), (132, 8985600), (133, -9953280), (143, -8017920), (151, 47727360), (163, -3386880), (165, -1451520), (166, -5806080), (167, -5806080), (168, -11819520), (170, 17832960), (171, 8501760), (172, -4147200), (173, -22809600), (194, -121824000), (197, -9123840), (199, 6220800), (205, -140279040), (247, 7119360), (268, 43787520)]

def pairMerged171 : Integer.Sparse (Fin 271) := [(0, 771600), (1, 8741320), (2, -1505880), (3, 11224320), (4, 32770560), (5, -15409280), (6, 3520400), (7, -36696960), (8, -3279360), (9, 4861440), (10, 23414400), (11, 13501440), (12, -11230080), (13, 104517120), (23, 81302400), (24, 38292480), (26, 77160960), (27, -16092000), (29, 3801600), (30, 46759680), (31, -153600), (32, 12568320), (33, 26449920), (34, 102557440), (50, 54915840), (51, 79457280), (53, 48170880), (54, 40746240), (55, -2350080), (58, -64673280), (59, 26859520), (60, 1382400), (62, -8294400), (65, 31948800), (67, -29151360), (68, -23679360), (69, -4089600), (70, -9538560), (71, -2488320), (72, -40227840), (73, -11404800), (74, 37324800), (75, -73405440), (76, -22809600), (77, -20476800), (79, 52784640), (80, 12687360), (82, 7672320), (83, 30689280), (84, -24468480), (88, -140279040), (110, -11059200), (111, 23379840), (114, 1382400), (115, 35112960), (130, 23379840), (132, 852480), (133, -26219520), (143, -15966720), (147, -11059200), (151, 41921280), (159, -15713280), (160, -24514560), (161, 1105920), (162, 13040640), (163, 1987200), (168, -11819520), (170, 17832960), (171, 8501760), (172, -4147200), (173, -22809600), (174, -40953600), (175, -61430400), (179, -5529600), (194, -121824000), (197, -9123840), (199, 6220800), (205, -140279040), (218, -30320640), (245, -35573760), (247, 5667840), (268, 40884480)]

def pairMerged172 : Integer.Sparse (Fin 271) := [(0, -1147608), (1, -38194200), (2, 82209600), (3, 411903360), (4, 58924800), (5, -36447840), (6, 1829520), (7, -29272320), (8, 71470080), (9, -760320), (12, 99601920), (13, 65387520), (23, -32503680), (24, -9123840), (25, 94089600), (26, 36875520), (32, -374077440), (34, -11594880), (51, 84015360), (53, -22809600), (54, -23379840), (67, 4561920), (68, 1520640), (69, 3041280), (79, -280558080), (89, -225815040), (92, 280558080), (96, 140279040), (103, -56453760), (111, 37635840), (112, -46759680), (113, -46759680), (131, 37635840), (143, -18247680), (151, -9123840), (163, -4561920), (175, 13685760), (204, -112907520), (205, 140279040)]

def pairMerged173 : Integer.Sparse (Fin 271) := [(0, -967032), (1, -1976040), (2, 18897120), (3, 198570240), (4, 12545280), (5, -77251680), (6, 14556960), (7, 111386880), (8, 9884160), (9, -10644480), (12, 2217600), (13, 88323840), (23, -7413120), (26, 37635840), (34, 168917760), (50, -30032640), (51, 220239360), (53, -90288000), (58, 19008000), (67, 35038080), (68, 25027200), (69, 10010880), (90, -22809600), (94, -45619200), (95, 225815040), (112, -52462080), (113, -30032640), (133, 15206400), (143, -75271680), (151, -30032640), (163, -18817920), (171, -11404800), (175, 56453760), (194, 112907520), (199, -22809600), (203, -22809600), (204, 112907520), (247, 3801600), (268, -30032640)]

def pairMerged174 : Integer.Sparse (Fin 271) := [(0, -2114640), (1, -40170240), (2, 101106720), (3, 610473600), (4, 71470080), (5, -113699520), (6, 16386480), (7, 82114560), (8, 81354240), (9, -11404800), (12, 101819520), (13, 153711360), (23, -39916800), (24, -9123840), (25, 94089600), (26, 74511360), (32, -374077440), (34, 157322880), (50, -30032640), (51, 304254720), (53, -113097600), (54, -23379840), (58, 19008000), (67, 39600000), (68, 26547840), (69, 13052160), (79, -280558080), (89, -225815040), (90, -22809600), (92, 280558080), (94, -45619200), (95, 225815040), (96, 140279040), (103, -56453760), (111, 37635840), (112, -99221760), (113, -76792320), (131, 37635840), (133, 15206400), (143, -93519360), (151, -39156480), (163, -23379840), (171, -11404800), (175, 70139520), (194, 112907520), (199, -22809600), (203, -22809600), (205, 140279040), (247, 3801600), (268, -30032640)]

def pairMerged175 : Integer.Sparse (Fin 271) := [(0, -709200), (1, 2697120), (2, 3645360), (3, 88093440), (5, -10601280), (6, 2731680), (7, 88842240), (8, 25735680), (9, -6076800), (10, -14135040), (12, 26092800), (13, 22648320), (23, -23397120), (26, 18132480), (27, 10601280), (34, 39709440), (50, -25539840), (51, 2534400), (53, -6531840), (54, -51667200), (58, -7603200), (67, 25574400), (68, 8709120), (69, 16865280), (85, 39191040), (97, 22809600), (111, -40262400), (130, -13063680), (131, -6531840), (143, -46794240), (146, -20666880), (151, -7603200), (163, -10333440), (168, 19595520), (174, 31000320), (203, 22809600), (247, -6531840)]

def pairMerged176 : Integer.Sparse (Fin 271) := [(0, -336384), (1, 2338560), (2, -4772160), (3, -15851520), (4, -9446400), (5, 4688640), (6, -198720), (7, -6635520), (8, -12165120), (9, -115200), (12, 2626560), (13, -92160), (23, -12441600), (24, -13824000), (25, -4147200), (26, -7603200), (27, 3456000), (30, 22809600), (34, -3225600), (42, -13685760), (47, 12441600), (50, 18662400), (54, -8294400), (55, 9123840), (62, -2764800), (66, 1382400), (67, 1382400), (68, 921600), (75, -13685760), (89, -27371520), (99, -27371520), (111, -8294400), (113, -8294400), (130, -2764800), (131, -8294400), (143, 1520640), (148, 15206400), (181, -1382400), (242, 8294400), (252, -9123840), (256, 12441600)]

def pairMerged177 : Integer.Sparse (Fin 271) := [(0, -1045584), (1, 5035680), (2, -1126800), (3, 72241920), (4, -9446400), (5, -5912640), (6, 2532960), (7, 82206720), (8, 13570560), (9, -6192000), (10, -14135040), (12, 28719360), (13, 22556160), (23, -35838720), (24, -13824000), (25, -4147200), (26, 10529280), (27, 14057280), (30, 22809600), (34, 36483840), (42, -13685760), (47, 12441600), (50, -6877440), (51, 2534400), (53, -6531840), (54, -59961600), (55, 9123840), (58, -7603200), (62, -2764800), (66, 1382400), (67, 26956800), (68, 9630720), (69, 16865280), (75, -13685760), (85, 39191040), (89, -27371520), (97, 22809600), (99, -27371520), (111, -48556800), (113, -8294400), (130, -15828480), (131, -14826240), (143, -45273600), (146, -20666880), (148, 15206400), (151, -7603200), (163, -10333440), (168, 19595520), (174, 31000320), (181, -1382400), (203, 22809600), (242, 8294400), (247, -6531840), (252, -9123840), (256, 12441600)]

def pairMerged178 : Integer.Sparse (Fin 271) := [(0, -3160224), (1, -35134560), (2, 99979920), (3, 682715520), (4, 62023680), (5, -119612160), (6, 18919440), (7, 164321280), (8, 94924800), (9, -17596800), (10, -14135040), (12, 130538880), (13, 176267520), (23, -75755520), (24, -22947840), (25, 89942400), (26, 85040640), (27, 14057280), (30, 22809600), (32, -374077440), (34, 193806720), (42, -13685760), (47, 12441600), (50, -36910080), (51, 306789120), (53, -119629440), (54, -83341440), (55, 9123840), (58, 11404800), (62, -2764800), (66, 1382400), (67, 66556800), (68, 36178560), (69, 29917440), (75, -13685760), (79, -280558080), (85, 39191040), (89, -253186560), (90, -22809600), (92, 280558080), (94, -45619200), (95, 225815040), (96, 140279040), (97, 22809600), (99, -27371520), (103, -56453760), (111, -10920960), (112, -99221760), (113, -85086720), (130, -15828480), (131, 22809600), (133, 15206400), (143, -138792960), (146, -20666880), (148, 15206400), (151, -46759680), (163, -33713280), (168, 19595520), (171, -11404800), (174, 31000320), (175, 70139520), (181, -1382400), (194, 112907520), (199, -22809600), (205, 140279040), (242, 8294400), (247, -2730240), (252, -9123840), (256, 12441600), (268, -30032640)]

def pairMerged179 : Integer.Sparse (Fin 271) := [(0, -77376), (1, -6401440), (2, 12177120), (3, 93818880), (4, 23861760), (5, -18446080), (6, 1129920), (7, 46095360), (8, 29644800), (9, -33920), (10, -33350400), (11, 8225280), (12, 16464640), (13, 22233600), (26, 31272960), (32, -4884480), (34, 38113280), (35, 3663360), (37, 33350400), (39, 74027520), (51, 9853440), (53, -1221120), (54, -37013760), (58, -22233600), (67, 407040), (68, 271360), (70, 33350400), (73, 66700800), (132, -3705600), (143, -24675840), (179, -3663360), (185, 7326720), (193, 66700800), (223, 3663360), (229, 22233600), (232, 133401600), (245, -2442240), (246, -407040), (248, -14822400), (249, -1628160), (258, 7326720), (260, 2442240), (262, 14653440)]

def pairMerged180 : Integer.Sparse (Fin 271) := [(0, -91008), (1, -256320), (2, 892800), (3, 783360), (4, -4055040), (5, -311040), (6, -31680), (7, 2995200), (8, 414720), (9, 126720), (10, 1658880), (12, 322560), (13, -184320), (23, 3456000), (24, 5944320), (25, -2764800), (26, -92160), (27, 933120), (32, -2764800), (34, -1105920), (46, -9123840), (50, -13547520), (51, -1013760), (53, -6912000), (54, 7464960), (64, -2764800), (66, -1140480), (67, -1520640), (68, -1013760), (77, -4976640), (87, 4147200), (103, -4561920), (109, 16588800), (111, 1520640), (112, 13685760), (113, 9123840), (114, -1382400), (131, 3041280), (175, -4561920), (177, 8294400), (178, 8294400), (181, 1520640), (234, -9123840), (241, -9123840), (248, 1520640), (256, -4561920)]

def pairMerged181 : Integer.Sparse (Fin 271) := [(0, -168384), (1, -6657760), (2, 13069920), (3, 94602240), (4, 19806720), (5, -18757120), (6, 1098240), (7, 49090560), (8, 30059520), (9, 92800), (10, -31691520), (11, 8225280), (12, 16787200), (13, 22049280), (23, 3456000), (24, 5944320), (25, -2764800), (26, 31180800), (27, 933120), (32, -7649280), (34, 37007360), (35, 3663360), (37, 33350400), (39, 74027520), (46, -9123840), (50, -13547520), (51, 8839680), (53, -8133120), (54, -29548800), (58, -22233600), (64, -2764800), (66, -1140480), (67, -1113600), (68, -742400), (70, 33350400), (73, 66700800), (77, -4976640), (87, 4147200), (103, -4561920), (109, 16588800), (111, 1520640), (112, 13685760), (113, 9123840), (114, -1382400), (131, 3041280), (132, -3705600), (143, -24675840), (175, -4561920), (177, 8294400), (178, 8294400), (179, -3663360), (181, 1520640), (185, 7326720), (193, 66700800), (223, 3663360), (229, 22233600), (232, 133401600), (234, -9123840), (241, -9123840), (245, -2442240), (246, -407040), (248, -13301760), (249, -1628160), (256, -4561920), (258, 7326720), (260, 2442240), (262, 14653440)]

def pairMerged182 : Integer.Sparse (Fin 271) := [(0, -354240), (1, 7585920), (2, -13435200), (3, -53314560), (4, -22855680), (5, 14065920), (6, -910080), (7, -16819200), (8, -29214720), (9, 518400), (12, -4055040), (23, 6082560), (24, 36495360), (26, -8478720), (27, -14446080), (29, 21288960), (30, 24883200), (32, 12165120), (34, -6359040), (45, -19077120), (48, -18247680), (50, 53637120), (51, -7372800), (54, 24330240), (55, 22256640), (66, -2280960), (67, -4193280), (68, -2119680), (69, -8294400), (75, -19077120), (89, -9538560), (97, -9123840), (98, -18247680), (99, -19077120), (111, 3041280), (113, 21288960), (131, 12165120), (143, 6359040), (146, 18247680), (147, 9123840), (148, 9538560), (155, 12718080), (170, -9538560), (174, -9123840), (177, -18247680), (179, 6082560), (181, 3041280), (182, 9538560), (199, -19077120), (249, 3041280), (250, -19077120), (251, -19077120), (256, -9123840), (263, 3179520), (266, -18247680), (267, -18247680)]

def pairMerged183 : Integer.Sparse (Fin 271) := [(0, 131904), (1, 2931840), (2, -538560), (3, -21058560), (4, -3502080), (5, -887040), (6, 305280), (7, -8064000), (8, 5990400), (9, -11520), (12, -5760000), (13, -4147200), (23, 10920960), (24, 6912000), (25, 13824000), (26, -1843200), (27, -864000), (29, -3041280), (30, 11059200), (32, -552960), (34, -5990400), (44, 18247680), (47, -8294400), (50, 5253120), (51, -2672640), (53, 8847360), (54, 5529600), (55, 6912000), (63, 13824000), (66, -1036800), (67, -875520), (68, -921600), (69, 4055040), (89, -4147200), (92, -24883200), (96, -8294400), (111, 1382400), (112, 12441600), (113, 8294400), (131, 2764800), (148, 9676800), (153, -6082560), (168, 4561920), (175, -4147200), (176, 9123840), (178, -8294400), (180, 2764800), (181, -4561920), (182, 1382400), (197, 9123840), (234, -4147200), (238, -8294400), (242, -8294400), (245, -3041280), (246, -1520640), (248, 1382400), (253, 18247680), (254, 18247680)]

def pairMerged184 : Integer.Sparse (Fin 271) := [(0, -222336), (1, 10517760), (2, -13973760), (3, -74373120), (4, -26357760), (5, 13178880), (6, -604800), (7, -24883200), (8, -23224320), (9, 506880), (12, -9815040), (13, -4147200), (23, 17003520), (24, 43407360), (25, 13824000), (26, -10321920), (27, -15310080), (29, 18247680), (30, 35942400), (32, 11612160), (34, -12349440), (44, 18247680), (45, -19077120), (47, -8294400), (48, -18247680), (50, 58890240), (51, -10045440), (53, 8847360), (54, 29859840), (55, 29168640), (63, 13824000), (66, -3317760), (67, -5068800), (68, -3041280), (69, -4239360), (75, -19077120), (89, -13685760), (92, -24883200), (96, -8294400), (97, -9123840), (98, -18247680), (99, -19077120), (111, 4423680), (112, 12441600), (113, 29583360), (131, 14929920), (143, 6359040), (146, 18247680), (147, 9123840), (148, 19215360), (153, -6082560), (155, 12718080), (168, 4561920), (170, -9538560), (174, -9123840), (175, -4147200), (176, 9123840), (177, -18247680), (178, -8294400), (179, 6082560), (180, 2764800), (181, -1520640), (182, 10920960), (197, 9123840), (199, -19077120), (234, -4147200), (238, -8294400), (242, -8294400), (245, -3041280), (246, -1520640), (248, 1382400), (249, 3041280), (250, -19077120), (251, -19077120), (253, 18247680), (254, 18247680), (256, -9123840), (263, 3179520), (266, -18247680), (267, -18247680)]

def pairMerged185 : Integer.Sparse (Fin 271) := [(0, -390720), (1, 3860000), (2, -903840), (3, 20229120), (4, -6551040), (5, -5578240), (6, 493440), (7, 24207360), (8, 6835200), (9, 599680), (10, -31691520), (11, 8225280), (12, 6972160), (13, 17902080), (23, 20459520), (24, 49351680), (25, 11059200), (26, 20858880), (27, -14376960), (29, 18247680), (30, 35942400), (32, 3962880), (34, 24657920), (35, 3663360), (37, 33350400), (39, 74027520), (44, 18247680), (45, -19077120), (46, -9123840), (47, -8294400), (48, -18247680), (50, 45342720), (51, -1205760), (53, 714240), (54, 311040), (55, 29168640), (58, -22233600), (63, 13824000), (64, -2764800), (66, -4458240), (67, -6182400), (68, -3783680), (69, -4239360), (70, 33350400), (73, 66700800), (75, -19077120), (77, -4976640), (87, 4147200), (89, -13685760), (92, -24883200), (96, -8294400), (97, -9123840), (98, -18247680), (99, -19077120), (103, -4561920), (109, 16588800), (111, 5944320), (112, 26127360), (113, 38707200), (114, -1382400), (131, 17971200), (132, -3705600), (143, -18316800), (146, 18247680), (147, 9123840), (148, 19215360), (153, -6082560), (155, 12718080), (168, 4561920), (170, -9538560), (174, -9123840), (175, -8709120), (176, 9123840), (177, -9953280), (179, 2419200), (180, 2764800), (182, 10920960), (185, 7326720), (193, 66700800), (197, 9123840), (199, -19077120), (223, 3663360), (229, 22233600), (232, 133401600), (234, -13271040), (238, -8294400), (241, -9123840), (242, -8294400), (245, -5483520), (246, -1927680), (248, -11919360), (249, 1413120), (250, -19077120), (251, -19077120), (253, 18247680), (254, 18247680), (256, -13685760), (258, 7326720), (260, 2442240), (262, 14653440), (263, 3179520), (266, -18247680), (267, -18247680)]

def pairMerged186 : Integer.Sparse (Fin 271) := [(0, -3550944), (1, -31274560), (2, 99076080), (3, 702944640), (4, 55472640), (5, -125190400), (6, 19412880), (7, 188528640), (8, 101760000), (9, -16997120), (10, -45826560), (11, 8225280), (12, 137511040), (13, 194169600), (23, -55296000), (24, 26403840), (25, 101001600), (26, 105899520), (27, -319680), (29, 18247680), (30, 58752000), (32, -370114560), (34, 218464640), (35, 3663360), (37, 33350400), (39, 74027520), (42, -13685760), (44, 18247680), (45, -19077120), (46, -9123840), (47, 4147200), (48, -18247680), (50, 8432640), (51, 305583360), (53, -118915200), (54, -83030400), (55, 38292480), (58, -10828800), (62, -2764800), (63, 13824000), (64, -2764800), (66, -3075840), (67, 60374400), (68, 32394880), (69, 25678080), (70, 33350400), (73, 66700800), (75, -32762880), (77, -4976640), (79, -280558080), (85, 39191040), (87, 4147200), (89, -266872320), (90, -22809600), (92, 255674880), (94, -45619200), (95, 225815040), (96, 131984640), (97, 13685760), (98, -18247680), (99, -46448640), (103, -61015680), (109, 16588800), (111, -4976640), (112, -73094400), (113, -46379520), (114, -1382400), (130, -15828480), (131, 40780800), (132, -3705600), (133, 15206400), (143, -157109760), (146, -2419200), (147, 9123840), (148, 34421760), (151, -46759680), (153, -6082560), (155, 12718080), (163, -33713280), (168, 24157440), (170, -9538560), (171, -11404800), (174, 21876480), (175, 61430400), (176, 9123840), (177, -9953280), (179, 2419200), (180, 2764800), (181, -1382400), (182, 10920960), (185, 7326720), (193, 66700800), (194, 112907520), (197, 9123840), (199, -41886720), (205, 140279040), (223, 3663360), (229, 22233600), (232, 133401600), (234, -13271040), (238, -8294400), (241, -9123840), (245, -5483520), (246, -1927680), (247, -2730240), (248, -11919360), (249, 1413120), (250, -19077120), (251, -19077120), (252, -9123840), (253, 18247680), (254, 18247680), (256, -1244160), (258, 7326720), (260, 2442240), (262, 14653440), (263, 3179520), (266, -18247680), (267, -18247680), (268, -30032640)]

def pairMerged187 : Integer.Sparse (Fin 271) := [(0, -2779344), (1, -22533240), (2, 97570200), (3, 714168960), (4, 88243200), (5, -140599680), (6, 22933280), (7, 151831680), (8, 98480640), (9, -12135680), (10, -22412160), (11, 21726720), (12, 126280960), (13, 298686720), (23, 26006400), (24, 64696320), (25, 101001600), (26, 183060480), (27, -16411680), (29, 22049280), (30, 105511680), (31, -153600), (32, -357546240), (33, 26449920), (34, 321022080), (35, 3663360), (37, 33350400), (39, 74027520), (42, -13685760), (44, 18247680), (45, -19077120), (46, -9123840), (47, 4147200), (48, -18247680), (50, 63348480), (51, 385040640), (53, -70744320), (54, -42284160), (55, 35942400), (58, -75502080), (59, 26859520), (60, 1382400), (62, -11059200), (63, 13824000), (64, -2764800), (65, 31948800), (66, -3075840), (67, 31223040), (68, 8715520), (69, 21588480), (70, 23811840), (71, -2488320), (72, -40227840), (73, 55296000), (74, 37324800), (75, -106168320), (76, -22809600), (77, -25453440), (79, -227773440), (80, 12687360), (82, 7672320), (83, 30689280), (84, -24468480), (85, 39191040), (87, 4147200), (88, -140279040), (89, -266872320), (90, -22809600), (92, 255674880), (94, -45619200), (95, 225815040), (96, 131984640), (97, 13685760), (98, -18247680), (99, -46448640), (103, -61015680), (109, 16588800), (110, -11059200), (111, 18403200), (112, -73094400), (113, -46379520), (115, 35112960), (130, 7551360), (131, 40780800), (132, -2853120), (133, -11013120), (143, -173076480), (146, -2419200), (147, -1935360), (148, 34421760), (151, -4838400), (153, -6082560), (155, 12718080), (159, -15713280), (160, -24514560), (161, 1105920), (162, 13040640), (163, -31726080), (168, 12337920), (170, 8294400), (171, -2903040), (172, -4147200), (173, -22809600), (174, -19077120), (176, 9123840), (177, -9953280), (179, -3110400), (180, 2764800), (181, -1382400), (182, 10920960), (185, 7326720), (193, 66700800), (194, -8916480), (199, -35665920), (218, -30320640), (223, 3663360), (229, 22233600), (232, 133401600), (234, -13271040), (238, -8294400), (241, -9123840), (245, -41057280), (246, -1927680), (247, 2937600), (248, -11919360), (249, 1413120), (250, -19077120), (251, -19077120), (252, -9123840), (253, 18247680), (254, 18247680), (256, -1244160), (258, 7326720), (260, 2442240), (262, 14653440), (263, 3179520), (266, -18247680), (267, -18247680), (268, 10851840)]

def pairMerged188 : Integer.Sparse (Fin 271) := [(0, -30910440), (1, 174361680), (2, 3379200), (3, 525281280), (4, -336044160), (5, -246632640), (6, 32505680), (7, 123008640), (8, 104862720), (9, -12799040), (10, -2851200), (11, -6503040), (12, 306736000), (13, 754268160), (15, -38776320), (17, -294969600), (18, 82321920), (21, -37324800), (23, -37514880), (24, 274821120), (25, -205562880), (26, -23688960), (27, 31661280), (29, 22049280), (30, 222808320), (31, -153600), (32, -318960000), (33, -1301760), (34, 479364480), (35, 151148160), (36, -71331840), (37, 33350400), (39, 36702720), (42, 104302080), (43, -121305600), (44, -457021440), (45, -177500160), (46, 108864000), (47, 78382080), (48, -18247680), (49, 235975680), (50, -262103040), (51, 448598400), (52, -145981440), (53, -475303680), (54, 46604160), (55, -162570240), (56, -108656640), (57, 1017720), (58, -80478720), (59, 18288640), (60, 1382400), (62, -11059200), (63, -145532160), (64, -2764800), (65, 57200640), (66, 37920960), (67, -83775360), (68, -43917440), (69, -69292800), (70, 23811840), (71, -2488320), (72, -40227840), (73, 55296000), (74, 37324800), (75, -106168320), (76, -22809600), (77, -25453440), (79, -124508160), (80, 75717120), (82, 7672320), (83, 30689280), (84, -24468480), (85, 39191040), (87, 4147200), (88, -140279040), (89, -266872320), (90, -22809600), (91, -294969600), (92, 292792320), (94, -45619200), (95, 225815040), (96, 249972480), (97, 13685760), (98, -18247680), (99, -43130880), (102, 3317760), (103, -61015680), (104, -79211520), (105, -158423040), (107, -145981440), (108, -158423040), (109, 16588800), (110, -22982400), (111, 3732480), (112, -53308800), (113, 57024000), (114, -2488320), (115, 89856000), (117, -225037440), (118, 1658880), (119, -35665920), (122, 117987840), (125, -38776320), (126, -293310720), (127, 164643840), (128, -37324800), (130, 26023680), (131, 130965120), (132, -56110080), (133, -134288640), (135, -37324800), (137, -80870400), (139, 117987840), (140, -294969600), (143, 53585280), (146, -232450560), (147, -27959040), (148, -85916160), (153, -7464960), (154, 17141760), (155, 11335680), (159, -15713280), (160, 14607360), (161, 1105920), (168, 12337920), (170, 8294400), (171, -2903040), (172, -4147200), (173, -22809600), (174, -19077120), (176, 9123840), (177, -9953280), (179, 36011520), (180, 41886720), (181, -2799360), (182, 19215360), (185, 7326720), (193, 66700800), (194, -8916480), (199, -35665920), (218, -30320640), (219, -30758400), (223, 3663360), (229, 22233600), (232, 133401600), (234, -13271040), (238, -8294400), (241, -9123840), (245, -41057280), (246, -19680000), (248, 61831680), (249, 55833600), (250, -19077120), (251, -19077120), (252, -9123840), (253, 18247680), (254, 18247680), (256, -1244160), (258, 7326720), (260, 2442240), (262, 14653440), (263, -81838080), (266, -18247680), (267, -18247680)]

def pairMerged189 : Integer.Sparse (Fin 271) := [(0, 513792), (1, -7562880), (2, 403200), (3, -15298560), (4, 3271680), (5, 2914560), (6, -984960), (7, 13685760), (8, 10506240), (9, 34560), (10, -6082560), (11, -2304000), (12, -7557120), (13, -36218880), (24, -24330240), (26, 368640), (27, 6842880), (29, -12165120), (30, -12165120), (34, -17326080), (44, -20736000), (48, 18247680), (50, 276480), (51, -37140480), (53, 13824000), (54, -21288960), (55, 13824000), (66, 2280960), (67, -2442240), (68, -2304000), (69, -552960), (80, 2027520), (88, 18247680), (94, -41472000), (95, -20736000), (99, 36495360), (111, -3041280), (113, -21288960), (131, -12165120), (143, 6912000), (146, -18247680), (148, -12165120), (155, 13824000), (170, -10368000), (174, 9123840), (182, 7326720), (199, -20736000), (234, 9123840), (249, -3041280), (254, -20736000), (263, 3456000), (265, 18247680), (266, 18247680), (270, -20736000)]

end MUB6.Certificate.PairData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMerge_Block6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairData

def pairMerged192 : Integer.Sparse (Fin 271) := [(0, 37632), (1, -247680), (2, -23040), (3, 1935360), (4, 2304000), (5, 576000), (6, -63360), (7, -1843200), (9, 84480), (12, 460800), (13, 1597440), (23, -829440), (24, -9953280), (25, -3594240), (27, -391680), (32, -552960), (34, -552960), (50, 9123840), (53, 12165120), (54, -13271040), (62, -2396160), (66, -230400), (67, -1013760), (68, -675840), (111, 2764800), (113, -3317760), (130, 1843200), (131, -6635520), (153, 6082560), (168, -9123840), (174, 9953280), (176, -9123840), (177, 9953280), (179, -3317760), (181, 3041280), (245, 3041280), (246, 3041280), (249, -3317760)]

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

def value0 : Sparse (Fin 909) := [(0, (1 / 1))]

end MUB6.Certificate.PairSemantics

end OAI
end


