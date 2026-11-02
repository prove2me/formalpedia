-- Prove2me | Definitions.Def_OAIQ106D134
-- name    : OAIQ106D134
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T13:26:04.432208+00:00
-- url     : https://prove2.me/theorems/2c185fca-bff1-4e2e-a16d-9fb379c87649
-- title:
--   Definitions bundle OAIQ106D134 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1788 declarations of OpenAI's Lean: 1788 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.singlePairValue120`, `OAI.MUB6.Certificate.MixedSemantics.singlePairValue122`, `OAI.MUB6.Certificate.MixedSemantics.singlePairValue123`, `OAI.MUB6.Certificate.MixedSemantics.singlePairValue124`, `OAI.MUB6.Certificate.MixedSemantics.singlePairValue125`, `OAI.MUB6.Certificate.MixedSemantics.singlePairValue126`, `OAI.MUB6.Certificate.MixedSemantics.singlePairValue127`, `OAI.MUB6.Certificate.MixedSemantics.singlePairValue128`, `OAI.MUB6.Certificate.MixedSemantics.singlePairValue129`, `OAI.MUB6.Certificate.MixedSemantics.singlePairValue13`, `OAI.MUB6.Certificate.MixedSemantics.singlePairValue130`, `OAI.MUB6.Certificate.MixedSemantics.singlePairValue131`, `OAI.MUB6.Certificate.MixedSemantics.singlePairValue132`, `OAI.MUB6.Certificate.MixedSemantics.singlePairValue133`, `OAI.MUB6.Certificate.MixedSemantics.singlePairValue134`, `OAI.MUB6.Certificate.MixedSemantics.singlePairValue139`, `OAI.MUB6.Certificate.MixedSemantics.singlePairValue14`, `OAI.MUB6.Certificate.MixedSemantics.singlePairValue140`, `OAI.MUB6.Certificate.MixedSemantics.singlePairValue141`, `OAI.MUB6.Certificate.MixedSemantics.singlePairValue142`, `OAI.MUB6.Certificate.MixedSemantics.singlePairValue143`, `OAI.MUB6.Certificate.MixedSemantics.singlePairValue144`, `OAI.MUB6.Certificate.MixedSemantics.singlePairValue145`, `OAI.MUB6.Certificate.MixedSemantics.singlePairValue146`, `OAI.MUB6.Certificate.MixedSemantics.singlePairValue147`, `OAI.MUB6.Certificate.MixedSemantics.singlePairValue148`, `OAI.MUB6.Certificate.MixedSemantics.singlePairValue149`, `OAI.MUB6.Certificate.MixedSemantics.singlePairValue15`, `OAI.MUB6.Certificate.MixedSemantics.singlePairValue150`, `OAI.MUB6.Certificate.MixedSemantics.singlePairValue151`, `OAI.MUB6.Certificate.MixedSemantics.singlePairValue152`, `OAI.MUB6.Certificate.MixedSemantics.singlePairValue153`, `OAI.MUB6.Certificate.MixedSemantics.singlePairValue154`, `OAI.MUB6.Certificate.MixedSemantics.singlePairValue155`, `OAI.MUB6.Certificate.MixedSemantics.singlePairValue156`, `OAI.MUB6.Certificate.MixedSemantics.singlePairValue157`, `OAI.MUB6.Certificate.MixedSemantics.singlePairValue158`, `OAI.MUB6.Certificate.MixedSemantics.singlePairValue159`, `OAI.MUB6.Certificate.MixedSemantics.singlePairValue16`, `OAI.MUB6.Certificate.MixedSemantics.singlePairValue160` and 1748 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedSemantics_Single3`, `MutuallyUnbiased_MixedSemantics_Single4`, `MutuallyUnbiased_MixedSemantics_Single5`, `MutuallyUnbiased_MixedSemantics_Single6`, `MutuallyUnbiased_MixedSemantics_Single7`, `MutuallyUnbiased_MixedSemantics_SingleGroup0`, `MutuallyUnbiased_MixedSemantics_SingleGroup1`, `MutuallyUnbiased_MixedSemantics_SingleGroup10`, `MutuallyUnbiased_MixedSemantics_SingleGroup11`, `MutuallyUnbiased_MixedSemantics_SingleGroup12`, `MutuallyUnbiased_MixedSemantics_SingleGroup13`, `MutuallyUnbiased_MixedSemantics_SingleGroup14`, `MutuallyUnbiased_MixedSemantics_SingleGroup15`, `MutuallyUnbiased_MixedSemantics_SingleGroup16`, `MutuallyUnbiased_MixedSemantics_SingleGroup17`, `MutuallyUnbiased_MixedSemantics_SingleGroup18`, `MutuallyUnbiased_MixedSemantics_SingleGroup19`, `MutuallyUnbiased_MixedSemantics_SingleGroup2`, `MutuallyUnbiased_MixedSemantics_SingleGroup20`, `MutuallyUnbiased_MixedSemantics_SingleGroup21`, `MutuallyUnbiased_MixedSemantics_SingleGroup22`, `MutuallyUnbiased_MixedSemantics_SingleGroup23`, `MutuallyUnbiased_MixedSemantics_SingleGroup24`, `MutuallyUnbiased_MixedSemantics_SingleGroup25`, `MutuallyUnbiased_MixedSemantics_SingleGroup26`, `MutuallyUnbiased_MixedSemantics_SingleGroup27`, `MutuallyUnbiased_MixedSemantics_SingleGroup28`, `MutuallyUnbiased_MixedSemantics_SingleGroup29`, `MutuallyUnbiased_MixedSemantics_SingleGroup3`, `MutuallyUnbiased_MixedSemantics_SingleGroup30`, `MutuallyUnbiased_MixedSemantics_SingleGroup31`, `MutuallyUnbiased_MixedSemantics_SingleGroup32`, `MutuallyUnbiased_MixedSemantics_SingleGroup4`, `MutuallyUnbiased_MixedSemantics_SingleGroup5`, `MutuallyUnbiased_MixedSemantics_SingleGroup7`, `MutuallyUnbiased_MixedSemantics_SingleGroup8`, `MutuallyUnbiased_MixedSemantics_SingleGroup9`, `MutuallyUnbiased_MixedSemantics_SinglePriority`, `MutuallyUnbiased_MixedSemantics_Sources0`, `MutuallyUnbiased_MixedSemantics_Sources3`, `MutuallyUnbiased_MixedSemantics_Sources31`, `MutuallyUnbiased_MixedSemantics_Sources32`, `MutuallyUnbiased_MixedSemantics_Sources33`, `MutuallyUnbiased_MixedSemantics_Sources34`, `MutuallyUnbiased_MixedSemantics_Sources35`, `MutuallyUnbiased_MixedSemantics_Sources36`, `MutuallyUnbiased_MixedSemantics_Sources37`, `MutuallyUnbiased_MixedSemantics_Sources38`, `MutuallyUnbiased_MixedSemantics_Sources39`, `MutuallyUnbiased_MixedSemantics_Sources4`, `MutuallyUnbiased_MixedSemantics_Sources40`, `MutuallyUnbiased_MixedSemantics_Sources41`, `MutuallyUnbiased_MixedSemantics_Sources42`, `MutuallyUnbiased_MixedSemantics_Sources43`, `MutuallyUnbiased_MixedSemantics_Sources44`, `MutuallyUnbiased_MixedSemantics_Sources45`, `MutuallyUnbiased_MixedSemantics_Sources46`, `MutuallyUnbiased_MixedSemantics_Sources47`, `MutuallyUnbiased_MixedSemantics_Sources48`, `MutuallyUnbiased_MixedSemantics_Sources49`, `MutuallyUnbiased_MixedSemantics_Sources5`, `MutuallyUnbiased_MixedSemantics_Sources50`, `MutuallyUnbiased_MixedSemantics_Sources51`, `MutuallyUnbiased_MixedSemantics_Sources52`, `MutuallyUnbiased_MixedSemantics_Sources53`, `MutuallyUnbiased_MixedSemantics_Sources54`, `MutuallyUnbiased_MixedSemantics_Sources55`, `MutuallyUnbiased_MixedSemantics_Sources56`, `MutuallyUnbiased_MixedSemantics_Sources57`, `MutuallyUnbiased_MixedSemantics_Sources58`, `MutuallyUnbiased_MixedSemantics_Sources59`, `MutuallyUnbiased_MixedSemantics_Sources6`, `MutuallyUnbiased_MixedSemantics_Sources60`, `MutuallyUnbiased_MixedSemantics_Sources61`, `MutuallyUnbiased_MixedSemantics_Sources62`, `MutuallyUnbiased_MixedSemantics_Sources63`, `MutuallyUnbiased_MixedSemantics_Sources64`, `MutuallyUnbiased_MixedSemantics_Sources65`, `MutuallyUnbiased_MixedSemantics_Sources66`, `MutuallyUnbiased_MixedSemantics_Sources67`, `MutuallyUnbiased_MixedSemantics_Sources68`, `MutuallyUnbiased_MixedSemantics_Sources69`, `MutuallyUnbiased_MixedSemantics_Sources7`, `MutuallyUnbiased_MixedSemantics_Sources70`, `MutuallyUnbiased_MixedSemantics_Sources71`, `MutuallyUnbiased_MixedSemantics_Sources72`, `MutuallyUnbiased_MixedSemantics_Sources73`, `MutuallyUnbiased_MixedSemantics_Sources74`, `MutuallyUnbiased_MixedSemantics_Sources75`, `MutuallyUnbiased_MixedSemantics_Sources76`, `MutuallyUnbiased_MixedSemantics_Sources77`, `MutuallyUnbiased_MixedSemantics_Sources78`, `MutuallyUnbiased_MixedSemantics_Sources79`, `MutuallyUnbiased_PairSemantics_Values1`.
--
--   **Imports.** It imports the published bundle `Def_MUBSix`; the bundles `OAIQ106D000` and `OAIQ106D002` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1161`, `OAI.MUB6.Certificate.MixedSemantics.sound1162`, `OAI.MUB6.Certificate.MixedSemantics.sound1163`, `OAI.MUB6.Certificate.MixedSemantics.sound1166`, `OAI.MUB6.Certificate.MixedSemantics.sound1168`, `OAI.MUB6.Certificate.MixedSemantics.sound1172`, `OAI.MUB6.Certificate.MixedSemantics.sound1173`, `OAI.MUB6.Certificate.MixedSemantics.sound1175`, `OAI.MUB6.Certificate.MixedSemantics.sound1265`, `OAI.MUB6.Certificate.MixedSemantics.sound1266`, `OAI.MUB6.Certificate.MixedSemantics.sound1267`, `OAI.MUB6.Certificate.MixedSemantics.sound1271`, `OAI.MUB6.Certificate.MixedSemantics.sound1298`, `OAI.MUB6.Certificate.MixedSemantics.sound1299`, `OAI.MUB6.Certificate.MixedSemantics.sound1301`, `OAI.MUB6.Certificate.MixedSemantics.sound1339`, `OAI.MUB6.Certificate.MixedSemantics.sound1340`, `OAI.MUB6.Certificate.MixedSemantics.sound1341`, `OAI.MUB6.Certificate.MixedSemantics.sound1342`, `OAI.MUB6.Certificate.MixedSemantics.sound1343`, `OAI.MUB6.Certificate.MixedSemantics.sound1344`, `OAI.MUB6.Certificate.MixedSemantics.sound1346`, `OAI.MUB6.Certificate.MixedSemantics.sound1395`, `OAI.MUB6.Certificate.MixedSemantics.sound1396`, `OAI.MUB6.Certificate.MixedSemantics.sound1397`, `OAI.MUB6.Certificate.MixedSemantics.sound1399`, `OAI.MUB6.Certificate.MixedSemantics.sound1401`, `OAI.MUB6.Certificate.MixedSemantics.sound1409`, `OAI.MUB6.Certificate.MixedSemantics.sound1410`, `OAI.MUB6.Certificate.MixedSemantics.sound1411`, `OAI.MUB6.Certificate.MixedSemantics.sound1412`, `OAI.MUB6.Certificate.MixedSemantics.sound1413`, `OAI.MUB6.Certificate.MixedSemantics.sound1414`, `OAI.MUB6.Certificate.MixedSemantics.sound1416`, `OAI.MUB6.Certificate.MixedSemantics.sound1417`, `OAI.MUB6.Certificate.MixedSemantics.sound1427`, `OAI.MUB6.Certificate.MixedSemantics.sound1475`, `OAI.MUB6.Certificate.MixedSemantics.sound1477`, `OAI.MUB6.Certificate.MixedSemantics.sound1478`, `OAI.MUB6.Certificate.MixedSemantics.sound1479`, `OAI.MUB6.Certificate.MixedSemantics.sound1480`, `OAI.MUB6.Certificate.MixedSemantics.sound171`, `OAI.MUB6.Certificate.MixedSemantics.sound174`, `OAI.MUB6.Certificate.MixedSemantics.sound206`, `OAI.MUB6.Certificate.MixedSemantics.sound207`, `OAI.MUB6.Certificate.MixedSemantics.sound2357`, `OAI.MUB6.Certificate.MixedSemantics.sound2358`, `OAI.MUB6.Certificate.MixedSemantics.sound2359`, `OAI.MUB6.Certificate.MixedSemantics.sound2527`, `OAI.MUB6.Certificate.MixedSemantics.sound2530`, `OAI.MUB6.Certificate.MixedSemantics.sound2531`, `OAI.MUB6.Certificate.MixedSemantics.sound2532`, `OAI.MUB6.Certificate.MixedSemantics.sound2570`, `OAI.MUB6.Certificate.MixedSemantics.sound2572`, `OAI.MUB6.Certificate.MixedSemantics.sound2574`, `OAI.MUB6.Certificate.MixedSemantics.sound2576`, `OAI.MUB6.Certificate.MixedSemantics.sound2593`, `OAI.MUB6.Certificate.MixedSemantics.sound2594`, `OAI.MUB6.Certificate.MixedSemantics.sound2595`, `OAI.MUB6.Certificate.MixedSemantics.sound2596`, `OAI.MUB6.Certificate.MixedSemantics.sound2598`, `OAI.MUB6.Certificate.MixedSemantics.sound2599`, `OAI.MUB6.Certificate.MixedSemantics.sound2601`, `OAI.MUB6.Certificate.MixedSemantics.sound2636`, `OAI.MUB6.Certificate.MixedSemantics.sound2637`, `OAI.MUB6.Certificate.MixedSemantics.sound2638`, `OAI.MUB6.Certificate.MixedSemantics.sound2640`, `OAI.MUB6.Certificate.MixedSemantics.sound2753`, `OAI.MUB6.Certificate.MixedSemantics.sound2766`, `OAI.MUB6.Certificate.MixedSemantics.sound2828`, `OAI.MUB6.Certificate.MixedSemantics.sound2904`, `OAI.MUB6.Certificate.MixedSemantics.sound293`, `OAI.MUB6.Certificate.MixedSemantics.sound2936`, `OAI.MUB6.Certificate.MixedSemantics.sound2937`, `OAI.MUB6.Certificate.MixedSemantics.sound2939`, `OAI.MUB6.Certificate.MixedSemantics.sound294`, `OAI.MUB6.Certificate.MixedSemantics.sound2941`, `OAI.MUB6.Certificate.MixedSemantics.sound2943`, `OAI.MUB6.Certificate.MixedSemantics.sound2957`, `OAI.MUB6.Certificate.MixedSemantics.sound2958`, `OAI.MUB6.Certificate.MixedSemantics.sound2959`, `OAI.MUB6.Certificate.MixedSemantics.sound2960`, `OAI.MUB6.Certificate.MixedSemantics.sound2961`, `OAI.MUB6.Certificate.MixedSemantics.sound2963`, `OAI.MUB6.Certificate.MixedSemantics.sound2965`, `OAI.MUB6.Certificate.MixedSemantics.sound2966`, `OAI.MUB6.Certificate.MixedSemantics.sound2968`, `OAI.MUB6.Certificate.MixedSemantics.sound2969`, `OAI.MUB6.Certificate.MixedSemantics.sound2986`, `OAI.MUB6.Certificate.MixedSemantics.sound2987`, `OAI.MUB6.Certificate.MixedSemantics.sound2988`, `OAI.MUB6.Certificate.MixedSemantics.sound2990`, `OAI.MUB6.Certificate.MixedSemantics.sound2996`, `OAI.MUB6.Certificate.MixedSemantics.sound2997`, `OAI.MUB6.Certificate.MixedSemantics.sound2998`, `OAI.MUB6.Certificate.MixedSemantics.sound3003`, `OAI.MUB6.Certificate.MixedSemantics.sound3005`, `OAI.MUB6.Certificate.MixedSemantics.sound3082`, `OAI.MUB6.Certificate.MixedSemantics.sound3087`, `OAI.MUB6.Certificate.MixedSemantics.sound3088`, `OAI.MUB6.Certificate.MixedSemantics.sound3089`, `OAI.MUB6.Certificate.MixedSemantics.sound3090`, `OAI.MUB6.Certificate.MixedSemantics.sound3093`, `OAI.MUB6.Certificate.MixedSemantics.sound3094`, `OAI.MUB6.Certificate.MixedSemantics.sound3099`, `OAI.MUB6.Certificate.MixedSemantics.sound3100`, `OAI.MUB6.Certificate.MixedSemantics.sound3101`, `OAI.MUB6.Certificate.MixedSemantics.sound3102`, `OAI.MUB6.Certificate.MixedSemantics.sound3106`, `OAI.MUB6.Certificate.MixedSemantics.sound3109`, `OAI.MUB6.Certificate.MixedSemantics.sound3110`, `OAI.MUB6.Certificate.MixedSemantics.sound3116`, `OAI.MUB6.Certificate.MixedSemantics.sound3120`, `OAI.MUB6.Certificate.MixedSemantics.sound3143`, `OAI.MUB6.Certificate.MixedSemantics.sound3144`, `OAI.MUB6.Certificate.MixedSemantics.sound3178`, `OAI.MUB6.Certificate.MixedSemantics.sound3184`, `OAI.MUB6.Certificate.MixedSemantics.sound3185`, `OAI.MUB6.Certificate.MixedSemantics.sound3190`, `OAI.MUB6.Certificate.MixedSemantics.sound3191`, `OAI.MUB6.Certificate.MixedSemantics.sound3203`, `OAI.MUB6.Certificate.MixedSemantics.sound3204`, `OAI.MUB6.Certificate.MixedSemantics.sound3205`, `OAI.MUB6.Certificate.MixedSemantics.sound3206`, `OAI.MUB6.Certificate.MixedSemantics.sound3207`, `OAI.MUB6.Certificate.MixedSemantics.sound3209`, `OAI.MUB6.Certificate.MixedSemantics.sound3210`, `OAI.MUB6.Certificate.MixedSemantics.sound3211`, `OAI.MUB6.Certificate.MixedSemantics.sound3223`, `OAI.MUB6.Certificate.MixedSemantics.sound3226`, `OAI.MUB6.Certificate.MixedSemantics.sound3227`, `OAI.MUB6.Certificate.MixedSemantics.sound370`, `OAI.MUB6.Certificate.MixedSemantics.sound371`, `OAI.MUB6.Certificate.MixedSemantics.sound3711`, `OAI.MUB6.Certificate.MixedSemantics.sound3726`, `OAI.MUB6.Certificate.MixedSemantics.sound3727`, `OAI.MUB6.Certificate.MixedSemantics.sound3734`, `OAI.MUB6.Certificate.MixedSemantics.sound3735`, `OAI.MUB6.Certificate.MixedSemantics.sound3736`, `OAI.MUB6.Certificate.MixedSemantics.sound3737`, `OAI.MUB6.Certificate.MixedSemantics.sound3738`, `OAI.MUB6.Certificate.MixedSemantics.sound3739`, `OAI.MUB6.Certificate.MixedSemantics.sound3818`, `OAI.MUB6.Certificate.MixedSemantics.sound3821`, `OAI.MUB6.Certificate.MixedSemantics.sound3822`, `OAI.MUB6.Certificate.MixedSemantics.sound3823`, `OAI.MUB6.Certificate.MixedSemantics.sound3824`, `OAI.MUB6.Certificate.MixedSemantics.sound3829`, `OAI.MUB6.Certificate.MixedSemantics.sound3831`, `OAI.MUB6.Certificate.MixedSemantics.sound3847`, `OAI.MUB6.Certificate.MixedSemantics.sound3851`, `OAI.MUB6.Certificate.MixedSemantics.sound3852`, `OAI.MUB6.Certificate.MixedSemantics.sound3853`, `OAI.MUB6.Certificate.MixedSemantics.sound3855`, `OAI.MUB6.Certificate.MixedSemantics.sound3856`, `OAI.MUB6.Certificate.MixedSemantics.sound3858`, `OAI.MUB6.Certificate.MixedSemantics.sound3882`, `OAI.MUB6.Certificate.MixedSemantics.sound3883`, `OAI.MUB6.Certificate.MixedSemantics.sound3887`, `OAI.MUB6.Certificate.MixedSemantics.sound3888`, `OAI.MUB6.Certificate.MixedSemantics.sound3925`, `OAI.MUB6.Certificate.MixedSemantics.sound3931`, `OAI.MUB6.Certificate.MixedSemantics.sound3933`, `OAI.MUB6.Certificate.MixedSemantics.sound3936`, `OAI.MUB6.Certificate.MixedSemantics.sound3937`, `OAI.MUB6.Certificate.MixedSemantics.sound3965`, `OAI.MUB6.Certificate.MixedSemantics.sound3966`, `OAI.MUB6.Certificate.MixedSemantics.sound3967`, `OAI.MUB6.Certificate.MixedSemantics.sound3977`, `OAI.MUB6.Certificate.MixedSemantics.sound3980`, `OAI.MUB6.Certificate.MixedSemantics.sound3982`, `OAI.MUB6.Certificate.MixedSemantics.sound3984`, `OAI.MUB6.Certificate.MixedSemantics.sound3987`, `OAI.MUB6.Certificate.MixedSemantics.sound3992`, `OAI.MUB6.Certificate.MixedSemantics.sound3993`, `OAI.MUB6.Certificate.MixedSemantics.sound3994`, `OAI.MUB6.Certificate.MixedSemantics.sound3997`, `OAI.MUB6.Certificate.MixedSemantics.sound3998`, `OAI.MUB6.Certificate.MixedSemantics.sound4002`, `OAI.MUB6.Certificate.MixedSemantics.sound4003`, `OAI.MUB6.Certificate.MixedSemantics.sound4012`, `OAI.MUB6.Certificate.MixedSemantics.sound4013`, `OAI.MUB6.Certificate.MixedSemantics.sound4014`, `OAI.MUB6.Certificate.MixedSemantics.sound4023`, `OAI.MUB6.Certificate.MixedSemantics.sound4026`, `OAI.MUB6.Certificate.MixedSemantics.sound4027`, `OAI.MUB6.Certificate.MixedSemantics.sound4029`, `OAI.MUB6.Certificate.MixedSemantics.sound4031`, `OAI.MUB6.Certificate.MixedSemantics.sound4032`, `OAI.MUB6.Certificate.MixedSemantics.sound4033`, `OAI.MUB6.Certificate.MixedSemantics.sound4039`, `OAI.MUB6.Certificate.MixedSemantics.sound4050`, `OAI.MUB6.Certificate.MixedSemantics.sound4053`, `OAI.MUB6.Certificate.MixedSemantics.sound436`, `OAI.MUB6.Certificate.MixedSemantics.sound454`, `OAI.MUB6.Certificate.MixedSemantics.sound455`, `OAI.MUB6.Certificate.MixedSemantics.sound4623`, `OAI.MUB6.Certificate.MixedSemantics.sound4625`, `OAI.MUB6.Certificate.MixedSemantics.sound479`, `OAI.MUB6.Certificate.MixedSemantics.sound511`, `OAI.MUB6.Certificate.MixedSemantics.sound514`, `OAI.MUB6.Certificate.MixedSemantics.sound5176`, `OAI.MUB6.Certificate.MixedSemantics.sound5177`, `OAI.MUB6.Certificate.MixedSemantics.sound521`, `OAI.MUB6.Certificate.MixedSemantics.sound5293`, `OAI.MUB6.Certificate.MixedSemantics.sound5294`, `OAI.MUB6.Certificate.MixedSemantics.sound5296`, `OAI.MUB6.Certificate.MixedSemantics.sound5306`, `OAI.MUB6.Certificate.MixedSemantics.sound5310`, `OAI.MUB6.Certificate.MixedSemantics.sound5415`, `OAI.MUB6.Certificate.MixedSemantics.sound5443`, `OAI.MUB6.Certificate.MixedSemantics.sound5452`, `OAI.MUB6.Certificate.MixedSemantics.sound5453`, `OAI.MUB6.Certificate.MixedSemantics.sound5464`, `OAI.MUB6.Certificate.MixedSemantics.sound5492`, `OAI.MUB6.Certificate.MixedSemantics.sound5498`, `OAI.MUB6.Certificate.MixedSemantics.sound644`, `OAI.MUB6.Certificate.MixedSemantics.sound645`, `OAI.MUB6.Certificate.MixedSemantics.sourceEq1094`, `OAI.MUB6.Certificate.MixedSemantics.sourceEq1095`, `OAI.MUB6.Certificate.MixedSemantics.sourceEq1100`, `OAI.MUB6.Certificate.MixedSemantics.sourceEq1104`, `OAI.MUB6.Certificate.MixedSourceBridge.allRowsSound`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound0`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound10`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound100`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound101`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound102`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound103`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound104`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound105`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound106`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound107`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound108`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound109`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound11`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound110`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound111`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound112`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound113`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound114`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound115`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound116`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound117`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound118`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound119`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound12`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound120`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound121`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound122`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound123`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound124`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound125`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound126`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound127`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound13`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound54`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound55`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound56`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound57`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound58`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound59`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound6`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound60`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound61`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound62`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound63`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound64`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound65`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound66`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound67`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound68`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound69`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound7`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound70`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound71`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound72`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound73`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound74`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound75`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound76`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound77`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound78`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound79`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound8`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound80`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound81`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound82`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound83`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound84`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound85`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound86`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound87`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound88`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound89`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound9`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound90`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound91`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound92`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound93`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound94`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound95`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound96`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound97`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound98`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound99`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1098`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1423`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero15`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1780`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero539`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero733`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero863`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero925`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound0`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound10`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound100`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1000`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1001`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1003`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1004`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1005`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1006`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1007`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1008`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1009`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound101`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1010`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1012`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1013`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1014`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1019`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1020`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1021`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1022`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1023`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1030`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1031`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1033`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1034`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1035`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1071`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound109`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1093`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1094`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1095`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1096`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1097`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound11`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound110`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1103`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1108`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1109`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound111`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1110`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1111`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1114`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1115`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1120`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1121`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1123`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1124`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound113`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1130`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1131`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound114`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1158`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1159`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound116`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1165`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1166`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1167`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1169`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound117`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1170`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1177`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1178`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1179`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1191`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1194`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1195`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1197`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1198`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1205`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1227`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1231`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1232`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1233`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound126`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1261`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1262`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1263`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1264`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1266`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1267`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1268`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1269`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound127`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1271`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1272`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1278`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1279`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound129`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1293`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1294`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound13`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound130`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1300`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1301`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1303`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1309`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1310`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1311`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1312`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1317`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1318`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1321`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1324`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1326`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1335`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1340`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound137`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound138`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound14`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound140`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1409`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound141`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1410`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1411`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1412`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1414`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1417`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1418`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1420`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1421`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1422`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1428`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1429`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound143`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1430`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1433`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1435`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1436`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1437`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1438`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1441`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1442`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound145`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1465`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1469`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1470`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1471`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1472`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1477`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1478`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1480`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1483`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1484`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1490`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1493`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1505`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1507`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1508`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound151`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1510`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1511`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1513`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1514`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1516`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1517`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound152`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1521`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound153`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1536`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1539`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1559`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1560`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1561`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1567`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1568`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1569`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1571`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1575`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1584`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1587`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1589`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1593`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1595`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1598`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1599`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound16`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound163`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1648`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1649`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1650`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1651`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1652`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1653`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1655`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1656`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1657`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1662`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1668`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1669`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1672`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1673`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1674`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1679`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1684`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1685`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1686`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1687`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound17`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1702`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1703`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1708`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1709`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1710`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1715`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1716`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1717`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1723`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1734`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1738`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1739`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1740`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1741`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1743`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1744`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1781`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1782`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1783`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1785`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1786`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1787`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1788`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1789`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1795`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1796`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1797`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound18`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1811`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1815`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1816`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1817`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1822`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1825`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1826`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1828`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1829`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1831`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1833`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1835`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1838`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1839`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound184`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1840`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1844`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1845`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1846`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1847`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1848`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1849`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1853`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1854`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1856`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1858`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1859`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1864`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1865`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1866`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1871`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1872`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1873`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1874`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1877`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound188`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1880`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1881`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1882`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound19`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1904`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1905`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1906`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1907`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1908`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1909`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1910`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1911`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1912`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1914`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1915`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1916`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1917`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1924`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1925`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1935`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1937`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1938`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1941`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1942`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1944`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1945`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1948`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1949`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1950`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1952`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1953`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1954`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1956`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1957`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1958`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1960`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1963`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1964`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1965`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1968`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1969`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1970`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1971`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1972`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1976`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1977`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound198`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1980`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1983`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1984`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1985`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1988`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1989`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound199`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1990`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1991`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1993`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1994`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1995`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1998`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1999`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound20`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2002`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2003`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2004`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2005`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2006`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2010`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2011`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2014`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2015`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2016`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2017`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2018`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2019`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2021`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2022`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2023`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2033`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2034`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2035`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2036`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2037`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2038`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2039`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2040`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2041`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2045`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2046`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2047`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2048`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2049`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2050`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2059`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2062`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound207`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2075`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2077`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound21`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound213`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound214`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound22`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound23`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2324`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound236`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound24`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound244`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound245`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound25`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound255`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound268`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound269`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound28`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound286`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound287`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound29`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound296`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound3`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound310`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound339`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound340`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound341`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound342`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound344`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound345`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound349`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound35`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound354`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound356`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound358`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound359`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound366`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound368`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound370`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound371`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound372`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound380`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound388`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound391`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound392`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound395`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound396`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound404`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound412`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound413`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound418`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound428`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound438`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound445`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound453`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound456`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound462`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound463`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound474`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound482`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound484`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound485`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound488`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound498`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound5`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound500`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound501`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound504`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound515`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound516`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound518`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound519`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound521`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound522`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound523`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound525`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound526`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound532`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound534`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound543`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound545`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound547`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound548`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound552`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound554`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound555`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound558`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound565`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound567`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound568`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound571`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound572`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound579`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound58`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound581`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound582`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound585`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound59`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound590`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound6`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound600`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound613`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound621`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound629`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound631`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound633`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound635`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound649`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound659`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound663`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound664`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound667`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound675`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound711`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound718`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound731`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound732`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound734`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound736`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound737`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound741`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound743`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound750`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound779`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound780`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound787`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound788`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound790`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound792`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound794`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound796`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound8`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound800`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound802`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound813`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound864`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound865`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound866`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound868`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound871`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound872`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound877`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound878`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound881`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound882`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound883`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound884`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound885`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound886`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound888`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound890`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound892`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound894`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound896`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound897`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound898`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound899`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound9`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound900`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound901`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound903`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound905`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound906`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound908`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound909`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound91`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound910`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound911`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound912`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound914`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound915`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound916`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound918`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound92`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound920`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound921`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound922`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound923`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound924`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound926`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound927`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound928`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound93`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound930`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound931`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound932`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound933`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound934`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound935`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound936`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound938`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound939`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound94`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound940`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound941`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound942`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound943`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound944`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound945`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound946`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound947`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound949`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound950`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound951`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound952`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound954`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound955`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound956`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound958`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound960`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound961`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound963`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound964`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound965`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound966`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound967`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound968`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound969`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound97`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound970`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound971`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound972`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound973`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound974`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound975`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound976`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound977`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound978`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound979`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound98`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound980`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound982`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound983`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound984`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound986`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound988`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound989`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound990`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound991`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound992`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound993`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound994`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound995`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound997`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound998`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound999`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval106`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1074`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval109`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval116`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval117`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1192`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval12`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval120`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1210`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval124`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1254`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval130`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval133`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval134`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval141`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval143`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval145`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval146`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval147`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval149`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval155`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1553`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1554`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval159`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval164`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval165`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval167`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval173`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval174`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval18`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval181`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval182`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval185`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval202`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval203`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval207`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval21`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval214`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval215`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval218`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval220`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval224`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval225`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval226`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval229`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval231`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval234`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval235`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval242`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval243`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval245`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval249`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval255`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval257`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval258`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval263`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval270`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval271`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval273`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval278`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval280`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval285`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval286`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval287`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval292`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval296`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval301`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval308`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval310`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval323`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval325`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval331`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval332`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval334`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval335`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval343`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval344`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval348`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval353`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval358`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval359`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval366`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval368`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval37`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval370`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval371`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval372`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval373`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval377`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval380`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval383`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval389`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval39`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval391`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval394`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval401`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval403`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval408`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval41`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval413`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval414`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval444`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval46`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval475`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval476`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval477`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval52`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval54`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval56`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval6`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval63`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval77`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval79`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval83`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval86`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval91`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval99`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval113`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval119`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval147`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval150`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval208`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval21`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval215`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval216`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval220`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval222`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval271`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval359`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval360`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval362`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval373`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval375`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval384`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval44`, `OAI.MUB6.Certificate.PairSemantics.sound1395`, `OAI.MUB6.Certificate.PairSemantics.sound1414` and `OAI.MUB6.Certificate.PairSourceBridge.rowSound156`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106D000
import Definitions.Def_OAIQ106D002

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Single3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue3 : Sparse (Fin 909) := [(0, (1 / 9)), (1, (5 / 24)), (2, (-5 / 72))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Single4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue4 : Sparse (Fin 909) := [(0, (11 / 72)), (1, (-5 / 36)), (2, (5 / 72))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Single5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue5 : Sparse (Fin 909) := [(0, (5 / 24)), (1, (-5 / 24))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Single6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue6 : Sparse (Fin 909) := [(0, (1 / 6)), (1, (5 / 6))]

end MUB6.Certificate.MixedSemantics

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

def value100 : Sparse (Fin 909) := [(268, (1 / 1))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Single7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue7 : Sparse (Fin 909) := [(0, (19 / 72)), (1, (5 / 72))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue8 : Sparse (Fin 909) := [(0, (1 / 54)), (1, (-5 / 864)), (2, (-5 / 72)), (5, (25 / 72)), (6, (-5 / 72)), (7, (-5 / 9)), (9, (25 / 108)), (35, (-5 / 18)), (58, (-5 / 864)), (69, (-5 / 6)), (70, (-20 / 27)), (71, (-5 / 9)), (257, (-5 / 27))]

def singlePairValue9 : Sparse (Fin 909) := [(0, (1 / 54)), (1, (5 / 288)), (2, (-5 / 288)), (5, (-5 / 54)), (6, (5 / 108)), (9, (-5 / 36)), (58, (5 / 432)), (69, (5 / 54)), (70, (5 / 54)), (71, (5 / 27))]

def singlePairValue13 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-25 / 432)), (2, (-5 / 144)), (5, (5 / 54)), (6, (-5 / 108)), (9, (5 / 36)), (58, (-5 / 144))]

def singlePairValue14 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (5 / 864)), (2, (-5 / 864)), (5, (-5 / 108)), (6, (5 / 144)), (9, (-5 / 54)), (35, (5 / 27)), (58, (5 / 432)), (69, (5 / 54)), (70, (5 / 54)), (257, (5 / 27)), (495, (5 / 27))]

def singlePairValue15 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (5 / 288)), (2, (35 / 864)), (5, (-5 / 72)), (7, (5 / 54)), (8, (5 / 54)), (9, (-5 / 54)), (69, (5 / 27)), (70, (5 / 54)), (71, (5 / 18)), (256, (-5 / 18))]

def singlePairValue16 : Sparse (Fin 909) := [(0, (11 / 432)), (2, (-5 / 216)), (5, (5 / 108)), (6, (-5 / 108)), (9, (5 / 54)), (58, (-5 / 144)), (495, (-5 / 27))]

def singlePairValue17 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-25 / 432)), (2, (-5 / 216)), (9, (5 / 36)), (69, (-5 / 27)), (70, (-5 / 27)), (71, (-5 / 27))]

def singlePairValue18 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (5 / 432)), (2, (5 / 144)), (9, (5 / 36)), (69, (-5 / 27)), (71, (-10 / 27))]

def singlePairValue19 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 72)), (2, (-5 / 72)), (9, (5 / 36)), (69, (-5 / 27)), (70, (-5 / 27)), (257, (-5 / 27))]

def singlePairValue20 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 72)), (2, (-5 / 72)), (9, (-5 / 18)), (58, (5 / 36))]

def singlePairValue21 : Sparse (Fin 909) := [(0, (1 / 54)), (1, (25 / 864)), (2, (25 / 864)), (3, (-5 / 18)), (5, (-5 / 27)), (6, (5 / 72)), (7, (-5 / 18)), (9, (-95 / 216)), (35, (-25 / 54)), (52, (-5 / 9)), (58, (5 / 216)), (69, (-5 / 9)), (70, (-5 / 18)), (71, (-5 / 18)), (256, (5 / 6)), (257, (-5 / 27)), (495, (-5 / 18))]

def singlePairValue22 : Sparse (Fin 909) := [(0, (29 / 864)), (1, (-5 / 216)), (2, (5 / 432)), (6, (5 / 96)), (7, (-5 / 18)), (8, (-5 / 9)), (9, (-10 / 27)), (58, (5 / 216)), (69, (-5 / 9)), (70, (-5 / 27)), (71, (-10 / 9))]

def singlePairValue23 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-65 / 864)), (2, (-35 / 864)), (6, (-5 / 864)), (7, (5 / 54)), (9, (5 / 54)), (58, (-5 / 864)), (69, (5 / 27)), (70, (5 / 54)), (71, (5 / 27))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue24 : Sparse (Fin 909) := [(0, (1 / 54)), (1, (5 / 288)), (2, (-35 / 864)), (5, (5 / 216)), (6, (-5 / 288)), (9, (25 / 216)), (52, (5 / 27)), (58, (-5 / 864)), (69, (5 / 27)), (71, (5 / 54)), (256, (-5 / 18)), (495, (5 / 54))]

def singlePairValue25 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 144)), (2, (25 / 144)), (58, (5 / 432)), (70, (-5 / 27))]

def singlePairValue26 : Sparse (Fin 909) := [(0, (1 / 32)), (1, (5 / 216)), (2, (5 / 144)), (6, (-5 / 432)), (8, (5 / 27)), (9, (5 / 54)), (58, (-5 / 864)), (69, (5 / 54)), (71, (10 / 27))]

def singlePairValue27 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-55 / 864)), (2, (-35 / 864)), (3, (5 / 54)), (5, (5 / 72)), (6, (-5 / 288)), (7, (5 / 54)), (9, (25 / 216)), (35, (5 / 27)), (52, (5 / 54)), (58, (-5 / 864)), (69, (5 / 54)), (70, (5 / 54)), (256, (-5 / 18)), (257, (5 / 54)), (495, (5 / 54))]

def singlePairValue28 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-35 / 432)), (2, (-5 / 108)), (5, (5 / 108)), (6, (5 / 432)), (58, (5 / 432)), (71, (-5 / 27))]

def singlePairValue29 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 216)), (2, (65 / 432)), (5, (-5 / 108)), (9, (-5 / 54)), (35, (-5 / 27)), (70, (-5 / 27)), (257, (-5 / 27))]

def singlePairValue30 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-35 / 432)), (2, (-5 / 108)), (9, (-5 / 54)), (69, (-5 / 27)), (71, (-5 / 27))]

def singlePairValue31 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (35 / 216)), (2, (5 / 216)), (5, (5 / 54)), (6, (5 / 216)), (58, (5 / 432)), (69, (-5 / 27))]

def singlePairValue32 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 72)), (2, (-25 / 432)), (6, (5 / 216)), (9, (-5 / 108)), (35, (-5 / 27)), (58, (5 / 432)), (257, (-5 / 27)), (495, (-5 / 27))]

def singlePairValue33 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (5 / 48)), (2, (-5 / 144)), (5, (-5 / 108)), (7, (-5 / 27)), (9, (-5 / 54)), (69, (-5 / 27)), (70, (-5 / 27))]

def singlePairValue34 : Sparse (Fin 909) := [(0, (7 / 216)), (2, (5 / 216)), (5, (-5 / 108)), (8, (-5 / 27)), (9, (-5 / 54)), (71, (-10 / 27))]

def singlePairValue35 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (5 / 48)), (2, (-5 / 144)), (5, (-5 / 36)), (6, (-5 / 144)), (9, (-5 / 36)), (58, (-5 / 144))]

def singlePairValue36 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-25 / 432)), (2, (-5 / 216)), (5, (-5 / 108)), (9, (-5 / 54)), (256, (5 / 9))]

def singlePairValue37 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 72)), (2, (-5 / 72)), (6, (-5 / 144)), (58, (-5 / 144)), (495, (5 / 9))]

def singlePairValue38 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (5 / 36)), (2, (5 / 36)), (9, (5 / 36)), (70, (5 / 9))]

def singlePairValue39 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 72)), (2, (-5 / 144)), (9, (5 / 36)), (71, (5 / 9))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue168 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-25 / 432)), (2, (-5 / 216)), (68, (5 / 36)), (124, (-5 / 18)), (196, (-5 / 18)), (197, (-5 / 18)), (266, (-5 / 18))]

def singlePairValue169 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (5 / 432)), (2, (5 / 144)), (68, (5 / 36)), (125, (-5 / 18)), (126, (-5 / 18)), (197, (-5 / 18)), (268, (-5 / 18))]

def singlePairValue170 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 72)), (2, (-5 / 72)), (68, (5 / 36)), (125, (-5 / 9)), (264, (-5 / 9))]

def singlePairValue171 : Sparse (Fin 909) := [(0, (29 / 864)), (1, (-25 / 864)), (2, (25 / 864)), (3, (-5 / 18)), (5, (-5 / 54)), (6, (5 / 864)), (7, (-5 / 54)), (9, (-5 / 216)), (12, (-5 / 54)), (13, (-5 / 54)), (23, (5 / 18)), (26, (-5 / 27)), (27, (5 / 24)), (35, (-5 / 18)), (54, (5 / 18)), (55, (5 / 9)), (68, (25 / 72)), (70, (-5 / 54)), (125, (5 / 9)), (196, (5 / 18)), (197, (5 / 9))]

def singlePairValue172 : Sparse (Fin 909) := [(0, (5 / 288)), (1, (-5 / 864)), (2, (-5 / 288)), (3, (-5 / 27)), (5, (-5 / 54)), (6, (5 / 288)), (9, (-5 / 216)), (13, (-5 / 27)), (27, (5 / 24)), (33, (5 / 18)), (52, (-5 / 27)), (55, (5 / 9)), (64, (5 / 9)), (68, (25 / 72)), (125, (5 / 9)), (197, (5 / 18)), (260, (5 / 18)), (263, (-5 / 9))]

def singlePairValue173 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-35 / 864)), (2, (5 / 32)), (5, (5 / 108)), (9, (5 / 216)), (13, (5 / 54)), (35, (5 / 27)), (68, (-5 / 72)), (70, (5 / 54)), (196, (-5 / 18))]

def singlePairValue174 : Sparse (Fin 909) := [(0, (25 / 864)), (1, (85 / 864)), (2, (5 / 54)), (3, (-25 / 54)), (4, (-5 / 27)), (5, (-25 / 216)), (6, (5 / 432)), (7, (-5 / 27)), (9, (-5 / 216)), (13, (-5 / 54)), (24, (5 / 9)), (26, (-5 / 27)), (27, (5 / 24)), (35, (-5 / 18)), (55, (5 / 18)), (56, (5 / 9)), (68, (25 / 72)), (70, (-5 / 54)), (125, (5 / 18)), (197, (10 / 9))]

def singlePairValue175 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-85 / 864)), (2, (-5 / 72)), (3, (5 / 54)), (5, (5 / 108)), (6, (-5 / 864)), (7, (5 / 54)), (9, (5 / 216)), (26, (5 / 54)), (35, (5 / 27)), (68, (-5 / 72)), (70, (5 / 54)), (197, (-5 / 18))]

def singlePairValue176 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-55 / 864)), (2, (-5 / 288)), (5, (5 / 108)), (6, (-5 / 432)), (9, (5 / 216)), (13, (5 / 54)), (52, (5 / 54)), (64, (-5 / 18)), (68, (-5 / 72)), (125, (-5 / 18)), (260, (-5 / 18))]

def singlePairValue177 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-25 / 864)), (2, (35 / 288)), (5, (5 / 216)), (13, (5 / 54)), (27, (-5 / 72)), (35, (5 / 54)), (63, (-5 / 18)), (68, (-5 / 36)), (196, (-5 / 18)), (264, (-5 / 18))]

def singlePairValue178 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-25 / 288)), (2, (-5 / 96)), (27, (-5 / 72)), (55, (-5 / 18)), (68, (-5 / 36)), (125, (-5 / 18)), (197, (-5 / 18))]

def singlePairValue179 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (175 / 864)), (2, (5 / 108)), (3, (-5 / 9)), (5, (-5 / 36)), (6, (5 / 288)), (7, (-5 / 18)), (9, (-5 / 216)), (12, (-5 / 18)), (13, (-10 / 27)), (23, (5 / 6)), (27, (5 / 24)), (35, (-5 / 18)), (54, (5 / 6)), (68, (25 / 72)), (70, (-5 / 54)), (125, (5 / 6)), (196, (5 / 9))]

def singlePairValue180 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (5 / 36)), (2, (5 / 216)), (3, (5 / 27)), (5, (5 / 108)), (6, (-5 / 432)), (7, (5 / 27)), (9, (5 / 216)), (13, (5 / 54)), (35, (5 / 27)), (68, (-5 / 72)), (70, (5 / 54)), (125, (-5 / 18))]

def singlePairValue181 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-25 / 288)), (2, (-65 / 864)), (5, (5 / 108)), (6, (-5 / 432)), (9, (5 / 216)), (54, (-5 / 18)), (62, (-5 / 18)), (68, (-5 / 72)), (260, (-5 / 18)), (264, (-5 / 18))]

def singlePairValue182 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (5 / 54)), (2, (-5 / 108)), (5, (5 / 216)), (23, (-5 / 18)), (27, (-5 / 72)), (54, (-5 / 18)), (68, (-5 / 36)), (125, (-5 / 18)), (196, (-5 / 18))]

def singlePairValue183 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (-5 / 432)), (2, (5 / 432)), (5, (5 / 216)), (24, (-5 / 18)), (27, (-5 / 72)), (56, (-5 / 18)), (68, (-5 / 36)), (197, (-5 / 9))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue184 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 72)), (2, (-5 / 144)), (5, (5 / 216)), (27, (-5 / 72)), (68, (-5 / 36)), (263, (5 / 9))]

def singlePairValue185 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (5 / 36)), (2, (5 / 36)), (68, (5 / 36)), (196, (5 / 9))]

def singlePairValue186 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 72)), (2, (-5 / 144)), (68, (5 / 36)), (197, (5 / 9))]

def singlePairValue187 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (5 / 48)), (2, (-5 / 144)), (68, (5 / 36)), (125, (5 / 9))]

def singlePairValue188 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 144)), (2, (5 / 48)), (68, (5 / 36)), (264, (5 / 9))]

def singlePairValue189 : Sparse (Fin 909) := [(0, (19 / 864)), (1, (65 / 864)), (2, (25 / 288)), (3, (-5 / 18)), (5, (-5 / 36)), (6, (5 / 288)), (9, (-5 / 216)), (13, (-5 / 54)), (26, (-5 / 9)), (27, (5 / 24)), (34, (-5 / 18)), (35, (-5 / 18)), (54, (5 / 6)), (65, (5 / 6)), (67, (-5 / 18)), (68, (25 / 72)), (257, (-5 / 54)), (264, (5 / 9)), (266, (5 / 6))]

def singlePairValue190 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 432)), (2, (-5 / 144)), (5, (5 / 108)), (6, (-5 / 432)), (9, (5 / 216)), (26, (5 / 27)), (34, (5 / 54)), (35, (5 / 27)), (67, (5 / 27)), (68, (-5 / 72)), (257, (5 / 54)), (266, (-5 / 18))]

def singlePairValue191 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (5 / 108)), (2, (35 / 864)), (3, (-10 / 27)), (5, (-5 / 36)), (6, (5 / 288)), (9, (-5 / 216)), (12, (-5 / 27)), (13, (-5 / 9)), (26, (-5 / 27)), (27, (5 / 24)), (32, (-5 / 54)), (34, (-5 / 27)), (35, (-5 / 18)), (54, (5 / 18)), (55, (5 / 9)), (60, (-5 / 27)), (61, (5 / 9)), (65, (5 / 18)), (67, (-5 / 54)), (68, (25 / 72)), (257, (-5 / 54)), (264, (5 / 18)), (266, (5 / 9)), (268, (5 / 9))]

def singlePairValue192 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 288)), (2, (-5 / 288)), (3, (5 / 54)), (5, (5 / 108)), (6, (-5 / 432)), (9, (5 / 216)), (13, (5 / 54)), (26, (5 / 54)), (34, (5 / 54)), (35, (5 / 27)), (60, (5 / 54)), (67, (5 / 54)), (68, (-5 / 72)), (257, (5 / 54)), (268, (-5 / 18))]

def singlePairValue193 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-35 / 432)), (2, (-35 / 432)), (5, (5 / 216)), (27, (-5 / 72)), (54, (-5 / 18)), (65, (-5 / 18)), (68, (-5 / 36)), (264, (-5 / 18)), (266, (-5 / 18))]

def singlePairValue194 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (5 / 216)), (2, (5 / 36)), (5, (5 / 108)), (6, (-5 / 432)), (9, (5 / 216)), (13, (5 / 27)), (32, (5 / 54)), (35, (5 / 27)), (60, (5 / 27)), (68, (-5 / 72)), (257, (5 / 54)), (264, (-5 / 18))]

def singlePairValue195 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 432)), (2, (-5 / 216)), (5, (5 / 216)), (27, (-5 / 72)), (55, (-5 / 18)), (61, (-5 / 18)), (68, (-5 / 36)), (266, (-5 / 18)), (268, (-5 / 18))]

def singlePairValue196 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 72)), (2, (-5 / 72)), (68, (5 / 36)), (266, (5 / 9))]

def singlePairValue197 : Sparse (Fin 909) := [(0, (11 / 432)), (2, (-5 / 432)), (68, (5 / 36)), (268, (5 / 9))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue206 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (-5 / 216)), (2, (-5 / 144)), (3, (-5 / 54)), (5, (5 / 216)), (6, (-35 / 864)), (7, (-5 / 54)), (9, (-5 / 216)), (26, (-5 / 27)), (35, (-5 / 18)), (58, (5 / 864)), (68, (5 / 72)), (70, (-5 / 54)), (71, (-5 / 54)), (197, (5 / 18))]

def singlePairValue207 : Sparse (Fin 909) := [(0, (29 / 864)), (1, (-25 / 432)), (3, (-10 / 27)), (5, (5 / 54)), (6, (-25 / 432)), (7, (-5 / 27)), (9, (-5 / 216)), (13, (-25 / 54)), (35, (-10 / 27)), (52, (-10 / 27)), (58, (5 / 864)), (68, (5 / 72)), (69, (-5 / 54)), (70, (-5 / 54)), (125, (5 / 18))]

def singlePairValue208 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 144)), (2, (-5 / 864)), (3, (-10 / 27)), (5, (-5 / 54)), (6, (-5 / 216)), (9, (-5 / 108)), (12, (-5 / 27)), (13, (-65 / 54)), (32, (-5 / 18)), (35, (-25 / 54)), (52, (-10 / 27)), (54, (5 / 18)), (58, (5 / 864)), (60, (-25 / 54)), (62, (5 / 9)), (68, (5 / 72)), (128, (-5 / 27)), (257, (-5 / 54)), (260, (5 / 18)), (264, (5 / 18)), (495, (-5 / 54))]

def singlePairValue209 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 48)), (2, (-25 / 432)), (3, (-10 / 27)), (5, (5 / 72)), (6, (5 / 432)), (7, (-5 / 18)), (9, (-5 / 108)), (12, (-5 / 54)), (13, (-10 / 27)), (23, (5 / 18)), (27, (5 / 72)), (35, (-10 / 27)), (52, (-5 / 27)), (54, (5 / 9)), (68, (5 / 36)), (69, (-5 / 54)), (70, (-5 / 54)), (125, (5 / 18)), (196, (5 / 18))]

def singlePairValue210 : Sparse (Fin 909) := [(0, (1 / 24)), (1, (5 / 108)), (2, (5 / 216)), (5, (35 / 216)), (8, (-5 / 18)), (9, (-5 / 108)), (24, (5 / 18)), (27, (5 / 72)), (56, (5 / 9)), (68, (5 / 36)), (71, (-5 / 27)), (197, (5 / 9))]

def singlePairValue211 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-65 / 864)), (2, (-25 / 864)), (6, (-5 / 432)), (9, (5 / 216)), (13, (5 / 54)), (52, (5 / 27)), (68, (-5 / 72)), (69, (5 / 54)), (125, (-5 / 18))]

def singlePairValue212 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-25 / 864)), (2, (5 / 96)), (3, (-10 / 27)), (4, (-5 / 54)), (5, (-5 / 72)), (6, (-25 / 864)), (9, (-5 / 108)), (13, (-5 / 18)), (26, (-5 / 18)), (34, (-5 / 27)), (35, (-10 / 27)), (52, (-5 / 18)), (56, (5 / 18)), (58, (5 / 864)), (60, (-5 / 27)), (67, (-5 / 54)), (68, (5 / 72)), (128, (-5 / 54)), (257, (-5 / 54)), (262, (5 / 18)), (268, (5 / 18)), (495, (-5 / 54))]

def singlePairValue213 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (5 / 864)), (2, (25 / 864)), (3, (-10 / 27)), (4, (-5 / 54)), (5, (-5 / 216)), (6, (5 / 216)), (9, (-5 / 108)), (12, (-5 / 27)), (13, (-10 / 27)), (26, (-5 / 54)), (27, (5 / 72)), (35, (-5 / 27)), (51, (5 / 9)), (54, (5 / 9)), (55, (5 / 18)), (56, (5 / 9)), (59, (5 / 18)), (61, (5 / 9)), (68, (5 / 36)), (259, (5 / 18)), (262, (5 / 18)), (266, (5 / 18)), (268, (5 / 18))]

def singlePairValue214 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 72)), (2, (-5 / 108)), (5, (5 / 108)), (6, (-5 / 432)), (9, (5 / 216)), (26, (5 / 54)), (35, (5 / 54)), (54, (-5 / 18)), (68, (-5 / 72)), (259, (-5 / 18)), (266, (-5 / 18))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue218 : Sparse (Fin 909) := [(0, (11 / 432)), (2, (-5 / 432)), (3, (-10 / 27)), (5, (5 / 108)), (12, (-5 / 54)), (13, (-40 / 27)), (32, (-10 / 27)), (35, (-10 / 27)), (52, (-10 / 27)), (60, (-10 / 27)), (62, (5 / 9)), (128, (-5 / 54))]

def singlePairValue220 : Sparse (Fin 909) := [(0, (7 / 144)), (1, (-25 / 432)), (2, (-5 / 72)), (3, (-5 / 27)), (5, (5 / 54)), (6, (-5 / 216)), (7, (-5 / 54)), (13, (-5 / 54)), (26, (-5 / 27)), (35, (-5 / 27)), (54, (5 / 18))]

def singlePairValue221 : Sparse (Fin 909) := [(0, (37 / 864)), (1, (85 / 864)), (2, (35 / 864)), (3, (-5 / 18)), (4, (-5 / 54)), (5, (25 / 216)), (6, (-5 / 288)), (8, (-5 / 54)), (13, (-5 / 27)), (26, (-5 / 54)), (35, (-5 / 54)), (52, (-5 / 54)), (56, (5 / 18))]

def singlePairValue222 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (-5 / 108)), (2, (-25 / 432)), (5, (-5 / 216)), (6, (5 / 216)), (26, (5 / 54)), (35, (5 / 54))]

def singlePairValue223 : Sparse (Fin 909) := [(0, (31 / 864)), (1, (65 / 864)), (2, (5 / 432)), (3, (-20 / 27)), (5, (5 / 72)), (6, (-5 / 432)), (7, (-5 / 54)), (12, (-10 / 27)), (13, (-5 / 6)), (35, (-5 / 18)), (52, (-5 / 27)), (54, (5 / 18))]

def singlePairValue224 : Sparse (Fin 909) := [(0, (1 / 32)), (1, (35 / 864)), (2, (5 / 864)), (3, (5 / 54)), (5, (-5 / 216)), (6, (5 / 288)), (13, (5 / 27)), (35, (5 / 54)), (52, (5 / 54))]

def singlePairValue225 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (5 / 216)), (2, (-5 / 216)), (3, (5 / 54)), (6, (5 / 432)), (13, (5 / 18)), (32, (5 / 54)), (35, (5 / 54)), (52, (5 / 54)), (60, (5 / 54)), (62, (-5 / 18))]

def singlePairValue226 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-55 / 864)), (2, (-25 / 864)), (3, (5 / 54)), (5, (-5 / 72)), (7, (5 / 54)), (13, (5 / 54)), (35, (5 / 54)), (54, (-5 / 18))]

def singlePairValue227 : Sparse (Fin 909) := [(0, (17 / 432)), (1, (35 / 432)), (2, (5 / 108)), (5, (-5 / 54)), (8, (5 / 54)), (56, (-5 / 18))]

def singlePairValue228 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-25 / 432)), (2, (-5 / 54)), (6, (5 / 432)), (12, (5 / 54)), (13, (5 / 9)), (32, (5 / 27)), (60, (5 / 27)), (128, (5 / 54))]

def singlePairValue229 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 216)), (2, (5 / 432)), (3, (5 / 54)), (5, (-5 / 108)), (12, (5 / 54)), (13, (5 / 18)), (59, (-5 / 18)), (61, (-5 / 18))]

def singlePairValue231 : Sparse (Fin 909) := [(0, (31 / 864)), (1, (-5 / 864)), (2, (25 / 864)), (5, (-5 / 108)), (6, (-5 / 864)), (54, (-5 / 18)), (56, (-5 / 18)), (228, (-5 / 18))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue232 : Sparse (Fin 909) := [(0, (47 / 864)), (1, (-35 / 288)), (2, (-25 / 216)), (3, (-10 / 27)), (5, (-5 / 216)), (6, (5 / 432)), (12, (-5 / 54)), (13, (-10 / 27)), (35, (-5 / 54)), (52, (-5 / 27))]

def singlePairValue233 : Sparse (Fin 909) := [(0, (13 / 288)), (1, (5 / 432)), (2, (185 / 864)), (5, (5 / 216)), (13, (5 / 54)), (35, (5 / 54))]

def singlePairValue234 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (-5 / 288)), (2, (-5 / 144)), (3, (5 / 54)), (6, (-5 / 864)), (13, (5 / 54)), (52, (5 / 54))]

def singlePairValue235 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 108)), (2, (-5 / 288)), (3, (5 / 27)), (5, (5 / 216)), (6, (-5 / 864)), (12, (5 / 54)), (13, (5 / 18)), (35, (5 / 54)), (52, (5 / 54))]

def singlePairValue236 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-35 / 432)), (2, (-35 / 432)), (6, (5 / 432)), (13, (-5 / 27)), (52, (-5 / 27))]

def singlePairValue237 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 216)), (2, (85 / 432)), (5, (-5 / 108)), (13, (-5 / 27)), (35, (-5 / 27))]

def singlePairValue238 : Sparse (Fin 909) := [(0, (25 / 864)), (1, (35 / 864)), (2, (5 / 288)), (3, (-20 / 27)), (4, (-5 / 54)), (5, (5 / 216)), (6, (-5 / 864)), (12, (-10 / 27)), (13, (-25 / 27)), (26, (-5 / 54)), (32, (-5 / 54)), (33, (5 / 18)), (34, (-5 / 54)), (35, (-5 / 27)), (51, (5 / 18)), (52, (-5 / 54)), (54, (5 / 9)), (56, (5 / 18)), (60, (-5 / 54)), (61, (5 / 18)), (62, (5 / 18))]

def singlePairValue239 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (35 / 864)), (2, (5 / 864)), (3, (5 / 27)), (6, (5 / 432)), (13, (5 / 27)), (26, (5 / 54)), (34, (5 / 54)), (35, (5 / 27)), (52, (5 / 54)), (60, (5 / 54))]

def singlePairValue240 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (5 / 144)), (2, (25 / 432)), (5, (-5 / 108)), (51, (-5 / 18)), (54, (-5 / 18)), (56, (-5 / 18)), (61, (-5 / 18))]

def singlePairValue242 : Sparse (Fin 909) := [(0, (29 / 864)), (1, (-65 / 864)), (2, (-85 / 864)), (3, (-5 / 9)), (5, (-5 / 72)), (6, (5 / 288)), (13, (-5 / 18)), (26, (-5 / 18)), (33, (5 / 6)), (35, (-5 / 54)), (54, (5 / 6)), (62, (5 / 9))]

def singlePairValue243 : Sparse (Fin 909) := [(0, (11 / 288)), (1, (5 / 288)), (2, (5 / 288)), (3, (-5 / 6)), (4, (-10 / 27)), (5, (-5 / 72)), (6, (5 / 288)), (12, (-5 / 27)), (13, (-25 / 54)), (26, (-10 / 27)), (35, (-5 / 18)), (54, (5 / 18)), (56, (5 / 9))]

def singlePairValue244 : Sparse (Fin 909) := [(0, (31 / 864)), (1, (-5 / 48)), (2, (-5 / 72)), (3, (5 / 54)), (5, (5 / 216)), (6, (-5 / 864)), (26, (5 / 27)), (35, (5 / 54)), (54, (-5 / 18))]

def singlePairValue245 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (5 / 432)), (2, (25 / 864)), (3, (5 / 27)), (4, (5 / 54)), (5, (5 / 216)), (6, (-5 / 864)), (13, (5 / 54)), (26, (5 / 54)), (35, (5 / 54)), (56, (-5 / 18))]

def singlePairValue246 : Sparse (Fin 909) := [(0, (23 / 864)), (1, (-5 / 144)), (3, (5 / 54)), (5, (5 / 216)), (6, (-5 / 864)), (13, (5 / 54)), (33, (-5 / 18)), (54, (-5 / 18)), (62, (-5 / 18))]

def singlePairValue247 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 72)), (2, (-5 / 216)), (6, (5 / 432)), (26, (-5 / 27)), (35, (-5 / 27))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue248 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (145 / 864)), (2, (5 / 144)), (3, (5 / 27)), (5, (5 / 216)), (6, (-5 / 864)), (12, (5 / 27)), (13, (5 / 18)), (35, (5 / 54)), (54, (-5 / 18))]

def singlePairValue249 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (5 / 27)), (3, (-5 / 27)), (6, (5 / 432)), (13, (-5 / 27)), (35, (-5 / 27))]

def singlePairValue250 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-25 / 432)), (2, (-5 / 54)), (6, (5 / 432)), (62, (5 / 9))]

def singlePairValue251 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (55 / 432)), (2, (-5 / 432)), (5, (-5 / 108)), (54, (5 / 9))]

def singlePairValue252 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (5 / 216)), (2, (5 / 108)), (5, (-5 / 108)), (56, (5 / 9))]

def singlePairValue253 : Sparse (Fin 909) := [(0, (1 / 27)), (1, (-5 / 48)), (2, (-25 / 288)), (3, (-5 / 6)), (5, (-5 / 72)), (6, (5 / 288)), (12, (-5 / 18)), (13, (-35 / 27)), (26, (-5 / 18)), (32, (-5 / 27)), (34, (-5 / 9)), (60, (-5 / 18)), (61, (5 / 6))]

def singlePairValue254 : Sparse (Fin 909) := [(0, (23 / 864)), (1, (5 / 216)), (2, (5 / 432)), (3, (5 / 27)), (5, (5 / 216)), (6, (-5 / 864)), (13, (5 / 27)), (26, (5 / 54)), (34, (5 / 27)), (60, (5 / 54)), (61, (-5 / 18))]

def singlePairValue255 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-25 / 432)), (2, (-5 / 54)), (6, (5 / 432)), (13, (-5 / 27)), (34, (-5 / 27)), (60, (-5 / 27))]

def singlePairValue256 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 108)), (2, (-5 / 108)), (5, (-5 / 108)), (61, (5 / 9))]

def singlePairValue257 : Sparse (Fin 909) := [(0, (23 / 864)), (1, (5 / 96)), (2, (-5 / 72)), (3, (-5 / 6)), (12, (-5 / 9)), (13, (-85 / 54)), (32, (-5 / 27))]

def singlePairValue258 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (5 / 48)), (2, (25 / 144)), (13, (5 / 9)), (32, (5 / 27))]

def singlePairValue259 : Sparse (Fin 909) := [(0, (13 / 432)), (1, (115 / 432)), (2, (5 / 54)), (3, (-10 / 27)), (12, (-5 / 54)), (13, (-10 / 27))]

def singlePairValue260 : Sparse (Fin 909) := [(0, (11 / 288)), (1, (-5 / 864)), (2, (-5 / 216)), (3, (5 / 54)), (13, (5 / 54))]

def singlePairValue261 : Sparse (Fin 909) := [(0, (13 / 432)), (1, (-25 / 864)), (2, (5 / 864)), (3, (5 / 27)), (12, (5 / 54)), (13, (5 / 18))]

def singlePairValue262 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (-5 / 144)), (2, (25 / 144)), (13, (-5 / 27))]

def singlePairValue263 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-35 / 432)), (2, (-5 / 108)), (3, (5 / 27)), (12, (5 / 27)), (13, (5 / 9)), (32, (5 / 54))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue264 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 72)), (2, (5 / 72)), (13, (-10 / 27)), (32, (-5 / 27))]

def singlePairValue268 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-55 / 432)), (2, (-5 / 54)), (3, (-5 / 27)), (13, (-5 / 27))]

def singlePairValue269 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (5 / 72)), (2, (-5 / 72)), (12, (-5 / 27)), (13, (-10 / 27))]

def singlePairValue271 : Sparse (Fin 909) := [(0, (1 / 36)), (2, (5 / 12)), (32, (5 / 9))]

def singlePairValue273 : Sparse (Fin 909) := [(0, (17 / 432)), (1, (-25 / 864)), (2, (5 / 216)), (6, (-5 / 864)), (8, (5 / 54)), (9, (5 / 216)), (68, (-5 / 72)), (71, (5 / 54)), (236, (-5 / 18))]

def singlePairValue274 : Sparse (Fin 909) := [(0, (19 / 864)), (1, (35 / 864)), (2, (5 / 216)), (6, (-5 / 432)), (8, (5 / 27)), (9, (5 / 216)), (68, (-5 / 72)), (71, (5 / 54)), (126, (-5 / 18))]

def singlePairValue275 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (-25 / 288)), (2, (5 / 864)), (3, (5 / 54)), (5, (5 / 216)), (7, (5 / 54)), (24, (-5 / 18)), (27, (-5 / 72)), (68, (-5 / 36)), (126, (-5 / 18)), (197, (-5 / 18))]

def singlePairValue277 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (-25 / 432)), (2, (5 / 432)), (68, (5 / 36)), (126, (5 / 9))]

def singlePairValue278 : Sparse (Fin 909) := [(0, (7 / 288)), (1, (-5 / 432)), (2, (-5 / 864)), (3, (-5 / 27)), (5, (5 / 216)), (7, (-5 / 27)), (23, (5 / 9)), (24, (5 / 18)), (27, (-5 / 36)), (51, (5 / 18)), (54, (5 / 18)), (55, (5 / 18)), (64, (5 / 18)), (68, (-5 / 36)), (124, (5 / 9)), (125, (5 / 6)), (126, (5 / 9)), (196, (5 / 18)), (197, (5 / 18)), (266, (5 / 18))]

def singlePairValue279 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-5 / 108)), (2, (5 / 216)), (68, (5 / 36)), (125, (-5 / 9)), (126, (-5 / 9))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue280 : Sparse (Fin 909) := [(0, (19 / 864)), (1, (5 / 144)), (2, (5 / 72)), (3, (-10 / 27)), (4, (-5 / 54)), (5, (-5 / 36)), (6, (5 / 288)), (7, (-5 / 54)), (9, (-5 / 216)), (12, (-5 / 54)), (23, (5 / 18)), (25, (5 / 18)), (26, (-5 / 27)), (27, (5 / 24)), (35, (-5 / 54)), (51, (5 / 18)), (54, (5 / 18)), (55, (5 / 18)), (64, (5 / 18)), (68, (25 / 72)), (123, (5 / 18)), (124, (5 / 18)), (125, (5 / 18)), (259, (5 / 18)), (266, (5 / 18)), (487, (-5 / 9))]

def singlePairValue281 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-55 / 864)), (2, (5 / 288)), (5, (5 / 108)), (6, (-5 / 432)), (9, (5 / 216)), (51, (-5 / 18)), (68, (-5 / 72)), (123, (-5 / 18)), (124, (-5 / 18)), (259, (-5 / 18))]

def singlePairValue282 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-25 / 432)), (2, (5 / 432)), (5, (5 / 216)), (27, (-5 / 72)), (68, (-5 / 36)), (487, (5 / 9))]

def singlePairValue283 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (55 / 864)), (2, (-25 / 432)), (3, (-5 / 18)), (4, (-5 / 54)), (5, (-5 / 72)), (6, (5 / 288)), (7, (-5 / 27)), (8, (-5 / 27)), (9, (-5 / 216)), (24, (5 / 9)), (27, (5 / 36)), (51, (5 / 18)), (52, (-5 / 54)), (68, (25 / 72)), (69, (-5 / 54)), (124, (5 / 18)), (126, (10 / 9))]

def singlePairValue284 : Sparse (Fin 909) := [(0, (1 / 54)), (1, (95 / 864)), (2, (-5 / 288)), (3, (5 / 54)), (6, (-5 / 432)), (7, (5 / 27)), (9, (5 / 216)), (68, (-5 / 72)), (69, (5 / 54)), (124, (-5 / 18))]

def singlePairValue285 : Sparse (Fin 909) := [(0, (1 / 32)), (1, (-25 / 432)), (2, (35 / 864)), (3, (5 / 54)), (6, (-5 / 432)), (7, (5 / 54)), (9, (5 / 216)), (52, (5 / 54)), (68, (-5 / 72)), (69, (5 / 54)), (126, (-5 / 18))]

def singlePairValue286 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (25 / 288)), (2, (5 / 864)), (3, (5 / 54)), (5, (5 / 216)), (7, (5 / 54)), (23, (-5 / 18)), (27, (-5 / 72)), (68, (-5 / 36)), (124, (-5 / 18)), (125, (-5 / 18))]

def singlePairValue287 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (5 / 432)), (2, (-5 / 432)), (5, (5 / 216)), (8, (5 / 54)), (24, (-5 / 18)), (27, (-5 / 72)), (68, (-5 / 36)), (126, (-5 / 9))]

def singlePairValue288 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 72)), (2, (-5 / 144)), (5, (5 / 216)), (27, (-5 / 72)), (55, (-5 / 18)), (64, (-5 / 18)), (68, (-5 / 36)), (125, (-5 / 18)), (266, (-5 / 18))]

def singlePairValue289 : Sparse (Fin 909) := [(0, (1 / 32)), (1, (-35 / 432)), (2, (5 / 864)), (5, (5 / 216)), (51, (-5 / 18)), (68, (-5 / 36)), (124, (-5 / 18)), (126, (-5 / 18))]

def singlePairValue290 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (25 / 216)), (2, (5 / 432)), (68, (5 / 36)), (124, (5 / 9))]

def singlePairValue291 : Sparse (Fin 909) := [(0, (37 / 864)), (1, (-5 / 108)), (2, (5 / 216)), (5, (5 / 108)), (6, (-5 / 108)), (8, (-5 / 27)), (9, (-5 / 216)), (58, (5 / 864)), (68, (5 / 72)), (71, (-5 / 27)), (236, (5 / 18))]

def singlePairValue292 : Sparse (Fin 909) := [(0, (17 / 864)), (1, (-5 / 108)), (2, (-65 / 864)), (3, (-10 / 27)), (6, (-25 / 864)), (7, (-5 / 54)), (9, (-5 / 108)), (12, (-5 / 54)), (13, (-10 / 27)), (35, (-5 / 27)), (51, (5 / 18)), (52, (-10 / 27)), (58, (5 / 864)), (68, (5 / 72)), (69, (-5 / 54)), (126, (5 / 18)), (128, (-5 / 54)), (262, (5 / 18)), (495, (-5 / 54))]

def singlePairValue293 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (-55 / 864)), (2, (-25 / 432)), (3, (-5 / 27)), (5, (5 / 54)), (6, (5 / 288)), (7, (-5 / 27)), (8, (-5 / 27)), (9, (-5 / 108)), (52, (-5 / 54)), (68, (5 / 36)), (69, (-5 / 54)), (71, (-5 / 54)), (126, (5 / 18)), (236, (5 / 18))]

def singlePairValue294 : Sparse (Fin 909) := [(0, (7 / 288)), (1, (5 / 288)), (2, (-5 / 108)), (3, (-5 / 27)), (6, (-35 / 864)), (7, (-5 / 54)), (8, (-5 / 27)), (9, (-5 / 216)), (52, (-5 / 27)), (58, (5 / 864)), (68, (5 / 72)), (69, (-5 / 54)), (71, (-5 / 54)), (126, (5 / 18))]

def singlePairValue295 : Sparse (Fin 909) := [(0, (1 / 32)), (1, (-5 / 216)), (2, (-5 / 144)), (3, (-25 / 54)), (4, (-5 / 54)), (5, (5 / 108)), (6, (5 / 288)), (7, (-5 / 18)), (9, (-5 / 108)), (24, (5 / 18)), (26, (-5 / 27)), (27, (5 / 72)), (35, (-5 / 18)), (52, (-5 / 54)), (68, (5 / 36)), (69, (-5 / 54)), (70, (-5 / 54)), (126, (5 / 18)), (197, (5 / 18))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue296 : Sparse (Fin 909) := [(0, (17 / 864)), (1, (-5 / 216)), (2, (-25 / 288)), (3, (-10 / 27)), (4, (-5 / 54)), (5, (5 / 216)), (6, (5 / 216)), (7, (-5 / 27)), (8, (-5 / 54)), (9, (-5 / 108)), (12, (-5 / 54)), (13, (-5 / 54)), (26, (-5 / 54)), (27, (5 / 72)), (33, (5 / 18)), (35, (-5 / 27)), (51, (5 / 18)), (52, (-5 / 27)), (59, (5 / 18)), (68, (5 / 36)), (81, (5 / 18)), (256, (5 / 18)), (486, (-5 / 9))]

def singlePairValue297 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-5 / 432)), (2, (-5 / 144)), (3, (-25 / 54)), (6, (5 / 216)), (7, (-5 / 18)), (9, (-5 / 108)), (12, (-5 / 54)), (13, (-5 / 54)), (23, (5 / 18)), (25, (5 / 18)), (26, (-5 / 54)), (27, (5 / 72)), (35, (-5 / 54)), (51, (5 / 9)), (52, (-5 / 54)), (54, (5 / 9)), (64, (5 / 9)), (68, (5 / 36)), (123, (5 / 18)), (124, (5 / 18)), (125, (5 / 18)), (259, (5 / 18)), (260, (5 / 18))]

def singlePairValue298 : Sparse (Fin 909) := [(0, (5 / 288)), (1, (5 / 432)), (2, (-35 / 864)), (3, (-5 / 27)), (5, (-5 / 216)), (6, (5 / 216)), (9, (-5 / 108)), (12, (-5 / 54)), (13, (-5 / 54)), (31, (5 / 18)), (33, (5 / 18)), (51, (5 / 9)), (52, (-5 / 54)), (59, (5 / 18)), (68, (5 / 36)), (123, (5 / 18)), (124, (5 / 18)), (126, (5 / 18)), (259, (5 / 18)), (262, (5 / 18))]

def singlePairValue299 : Sparse (Fin 909) := [(0, (1 / 54)), (1, (5 / 48)), (2, (-25 / 432)), (3, (-10 / 27)), (5, (5 / 27)), (6, (-5 / 216)), (12, (-5 / 54)), (13, (-10 / 27)), (52, (-10 / 27)), (128, (-5 / 54))]

def singlePairValue300 : Sparse (Fin 909) := [(0, (7 / 288)), (1, (65 / 864)), (2, (-65 / 432)), (3, (-5 / 9)), (5, (5 / 54)), (7, (-10 / 27)), (8, (-10 / 27)), (12, (-5 / 54)), (13, (-5 / 54)), (26, (-5 / 54)), (33, (5 / 18)), (35, (-5 / 54)), (51, (5 / 9)), (59, (5 / 18))]

def singlePairValue301 : Sparse (Fin 909) := [(0, (37 / 864)), (1, (-5 / 864)), (2, (5 / 54)), (3, (-10 / 27)), (5, (25 / 216)), (6, (-5 / 216)), (7, (-5 / 27)), (26, (-5 / 27)), (35, (-5 / 54))]

def singlePairValue302 : Sparse (Fin 909) := [(0, (23 / 864)), (1, (5 / 48)), (2, (-35 / 432)), (3, (-5 / 27)), (5, (5 / 36)), (6, (-5 / 288)), (8, (-5 / 27)), (52, (-5 / 54))]

def singlePairValue303 : Sparse (Fin 909) := [(0, (17 / 432)), (1, (-5 / 216)), (2, (-5 / 144)), (5, (-5 / 108)), (6, (5 / 216))]

def singlePairValue304 : Sparse (Fin 909) := [(0, (19 / 864)), (1, (5 / 144)), (2, (-5 / 96)), (3, (-5 / 18)), (4, (-5 / 27)), (5, (5 / 54)), (6, (-5 / 432)), (7, (-5 / 27)), (26, (-5 / 27)), (35, (-5 / 27)), (52, (-5 / 27))]

def singlePairValue305 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (5 / 432)), (2, (-5 / 288)), (3, (5 / 54)), (5, (-5 / 108)), (6, (5 / 288)), (52, (5 / 54))]

def singlePairValue306 : Sparse (Fin 909) := [(0, (1 / 32)), (1, (-5 / 72)), (2, (55 / 864)), (3, (5 / 18)), (5, (-5 / 72)), (7, (5 / 27)), (26, (5 / 54)), (35, (5 / 54))]

def singlePairValue307 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (25 / 216)), (2, (5 / 72)), (5, (-5 / 54)), (8, (5 / 27))]

def singlePairValue308 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-5 / 432)), (2, (5 / 216)), (3, (5 / 27)), (6, (5 / 432)), (12, (5 / 54)), (13, (10 / 27)), (52, (5 / 27)), (128, (5 / 54))]

def singlePairValue309 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-5 / 216)), (2, (5 / 108)), (3, (5 / 54)), (5, (-5 / 108)), (12, (5 / 54)), (13, (5 / 54)), (33, (-5 / 18)), (51, (-5 / 18)), (59, (-5 / 18))]

def singlePairValue310 : Sparse (Fin 909) := [(0, (37 / 864)), (1, (-25 / 288)), (2, (-5 / 54)), (3, (-10 / 27)), (4, (-5 / 27)), (5, (-5 / 216)), (6, (5 / 432)), (26, (-5 / 27)), (35, (-5 / 54)), (52, (-5 / 27))]

def singlePairValue311 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (-55 / 864)), (2, (-65 / 864)), (3, (5 / 54)), (5, (5 / 216)), (26, (5 / 27)), (35, (5 / 54))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue312 : Sparse (Fin 909) := [(0, (11 / 288)), (1, (5 / 432)), (2, (35 / 432)), (3, (5 / 27)), (6, (-5 / 864)), (52, (5 / 54))]

def singlePairValue313 : Sparse (Fin 909) := [(0, (23 / 864)), (1, (-5 / 108)), (2, (-5 / 432)), (3, (5 / 18)), (5, (5 / 216)), (6, (-5 / 864)), (12, (5 / 54)), (13, (5 / 18)), (26, (5 / 54)), (34, (5 / 27)), (35, (5 / 54)), (60, (5 / 54))]

def singlePairValue314 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (-5 / 96)), (2, (5 / 144)), (4, (5 / 54)), (5, (5 / 216)), (6, (-5 / 864)), (26, (5 / 54)), (35, (5 / 54)), (52, (5 / 54))]

def singlePairValue315 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (-5 / 72)), (2, (-5 / 144)), (3, (-5 / 27)), (6, (5 / 432)), (52, (-5 / 27))]

def singlePairValue316 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 108)), (2, (-5 / 432)), (3, (-5 / 27)), (5, (-5 / 108)), (26, (-5 / 27)), (35, (-5 / 27))]

def singlePairValue317 : Sparse (Fin 909) := [(0, (1 / 54)), (1, (35 / 288)), (2, (-5 / 288)), (3, (-5 / 54)), (5, (5 / 216)), (6, (5 / 216)), (7, (-5 / 54)), (9, (-5 / 108)), (12, (-5 / 54)), (13, (-5 / 54)), (23, (5 / 18)), (27, (5 / 72)), (35, (-5 / 27)), (68, (5 / 36)), (69, (-5 / 54)), (70, (-5 / 54)), (124, (5 / 18)), (125, (5 / 18))]

def singlePairValue318 : Sparse (Fin 909) := [(0, (23 / 864)), (2, (-145 / 864)), (3, (-5 / 18)), (5, (5 / 36)), (6, (5 / 216)), (7, (-10 / 27)), (8, (-10 / 27)), (9, (-5 / 108)), (51, (5 / 9)), (68, (5 / 36)), (69, (-5 / 54)), (71, (-5 / 54)), (124, (5 / 18)), (126, (5 / 18))]

def singlePairValue319 : Sparse (Fin 909) := [(0, (1 / 72)), (1, (35 / 432)), (2, (-5 / 108)), (3, (-10 / 27)), (5, (5 / 54)), (6, (-5 / 432)), (13, (-10 / 27)), (35, (-5 / 27)), (52, (-10 / 27))]

def singlePairValue320 : Sparse (Fin 909) := [(0, (37 / 864)), (1, (-5 / 144)), (2, (5 / 216)), (3, (-10 / 27)), (4, (-5 / 54)), (5, (25 / 216)), (6, (-5 / 288)), (7, (-5 / 27)), (8, (-5 / 54)), (26, (-5 / 27)), (35, (-5 / 54))]

def singlePairValue321 : Sparse (Fin 909) := [(0, (19 / 864)), (1, (85 / 432)), (2, (-25 / 432)), (3, (-5 / 27)), (5, (5 / 36)), (6, (-5 / 288)), (7, (-5 / 54)), (8, (-5 / 27))]

def singlePairValue322 : Sparse (Fin 909) := [(0, (1 / 48)), (1, (65 / 864)), (2, (-25 / 432)), (3, (-35 / 54)), (4, (-5 / 27)), (5, (5 / 108)), (6, (-5 / 864)), (7, (-5 / 27)), (12, (-5 / 27)), (13, (-25 / 54)), (26, (-10 / 27)), (34, (-5 / 27)), (35, (-10 / 27)), (52, (-5 / 27)), (67, (-5 / 54))]

def singlePairValue323 : Sparse (Fin 909) := [(0, (13 / 864)), (1, (65 / 864)), (2, (5 / 216)), (3, (5 / 27)), (5, (-5 / 216)), (6, (5 / 432)), (13, (5 / 27)), (35, (5 / 54)), (52, (5 / 27))]

def singlePairValue324 : Sparse (Fin 909) := [(0, (1 / 54)), (1, (5 / 432)), (2, (-5 / 144)), (3, (5 / 27)), (5, (-5 / 108)), (7, (5 / 54)), (13, (5 / 54)), (26, (5 / 27)), (34, (5 / 54)), (35, (5 / 27)), (67, (5 / 54))]

def singlePairValue325 : Sparse (Fin 909) := [(0, (11 / 288)), (1, (5 / 432)), (2, (55 / 864)), (3, (5 / 54)), (5, (-5 / 54)), (7, (5 / 54)), (8, (5 / 54))]

def singlePairValue326 : Sparse (Fin 909) := [(0, (23 / 864)), (1, (35 / 432)), (2, (-65 / 864)), (3, (-10 / 27)), (5, (5 / 54)), (6, (-5 / 432)), (7, (-5 / 27)), (8, (-5 / 54)), (12, (-5 / 27)), (13, (-5 / 27)), (35, (-5 / 54)), (51, (5 / 18)), (52, (-5 / 54))]

def singlePairValue327 : Sparse (Fin 909) := [(0, (17 / 864)), (1, (35 / 288)), (3, (-55 / 54)), (4, (-5 / 27)), (5, (5 / 108)), (6, (-5 / 432)), (7, (-5 / 54)), (13, (-10 / 27)), (26, (-20 / 27)), (34, (-25 / 54)), (35, (-5 / 18)), (52, (-5 / 54)), (64, (5 / 18)), (67, (-5 / 27))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue40 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (5 / 48)), (2, (-5 / 144)), (9, (5 / 36)), (69, (5 / 9))]

def singlePairValue41 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 144)), (2, (5 / 48)), (9, (5 / 36)), (257, (5 / 9))]

def singlePairValue42 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (5 / 36)), (2, (5 / 36)), (9, (5 / 9)), (58, (5 / 36))]

def singlePairValue43 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (35 / 432)), (2, (5 / 27)), (5, (-5 / 36)), (6, (5 / 72)), (7, (-5 / 27)), (35, (-10 / 27)), (82, (-5 / 27)), (199, (5 / 18))]

def singlePairValue44 : Sparse (Fin 909) := [(0, (7 / 144)), (1, (-5 / 48)), (2, (-55 / 432)), (3, (-5 / 54)), (5, (5 / 36)), (6, (-5 / 144)), (8, (-5 / 54)), (13, (-5 / 54)), (35, (-5 / 54)), (52, (-10 / 27)), (82, (-5 / 54)), (128, (-5 / 27)), (201, (5 / 18))]

def singlePairValue45 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (35 / 864)), (2, (-5 / 108)), (5, (-25 / 216)), (6, (-5 / 96)), (35, (5 / 54)), (82, (5 / 54))]

def singlePairValue47 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 432)), (2, (5 / 108)), (5, (5 / 54)), (6, (5 / 216)), (7, (5 / 54)), (35, (5 / 27)), (82, (5 / 54)), (199, (-5 / 18))]

def singlePairValue48 : Sparse (Fin 909) := [(0, (13 / 288)), (2, (-5 / 432)), (5, (55 / 216)), (6, (-5 / 864)), (8, (5 / 54)), (201, (-5 / 18))]

def singlePairValue49 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 216)), (6, (25 / 144)), (82, (-5 / 27))]

def singlePairValue50 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (5 / 72)), (2, (5 / 48)), (5, (-5 / 36)), (6, (5 / 108)), (52, (5 / 27)), (128, (5 / 54))]

def singlePairValue51 : Sparse (Fin 909) := [(0, (5 / 144)), (2, (5 / 72)), (3, (5 / 54)), (5, (-5 / 36)), (6, (5 / 144)), (13, (5 / 54)), (35, (5 / 54)), (52, (5 / 54)), (82, (5 / 54)), (128, (5 / 54)), (201, (-5 / 18))]

def singlePairValue53 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 144)), (2, (-5 / 108)), (5, (5 / 27)), (6, (-5 / 108)), (35, (-5 / 27)), (82, (-5 / 27))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue328 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (5 / 288)), (2, (55 / 864)), (3, (5 / 27)), (5, (-5 / 108)), (7, (5 / 54)), (26, (5 / 27)), (34, (5 / 54)), (35, (5 / 54)), (64, (-5 / 18)), (67, (5 / 54))]

def singlePairValue329 : Sparse (Fin 909) := [(0, (19 / 864)), (1, (25 / 864)), (2, (5 / 108)), (3, (5 / 54)), (5, (-5 / 72)), (7, (5 / 54)), (8, (5 / 54)), (51, (-5 / 18))]

def singlePairValue330 : Sparse (Fin 909) := [(0, (23 / 864)), (1, (-5 / 864)), (2, (-55 / 864)), (3, (-5 / 6)), (4, (-5 / 18)), (5, (-5 / 72)), (6, (5 / 288)), (7, (-5 / 54)), (12, (-5 / 54)), (13, (-5 / 54)), (26, (-25 / 54)), (33, (5 / 18)), (34, (-5 / 27)), (35, (-5 / 27)), (67, (-5 / 54)), (81, (5 / 18))]

def singlePairValue331 : Sparse (Fin 909) := [(0, (17 / 864)), (1, (25 / 216)), (2, (-25 / 216)), (3, (-10 / 9)), (4, (-5 / 9)), (5, (-5 / 108)), (6, (5 / 288)), (7, (-5 / 18)), (26, (-5 / 9)), (35, (-5 / 27))]

def singlePairValue332 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (-5 / 54)), (2, (5 / 288)), (3, (5 / 18)), (4, (5 / 54)), (5, (5 / 216)), (6, (-5 / 864)), (7, (5 / 54)), (26, (5 / 27)), (35, (5 / 54))]

def singlePairValue333 : Sparse (Fin 909) := [(0, (7 / 432)), (1, (5 / 108)), (2, (25 / 864)), (3, (5 / 27)), (4, (5 / 54)), (5, (5 / 216)), (6, (-5 / 864)), (26, (5 / 54)), (33, (-5 / 18)), (81, (-5 / 18))]

def singlePairValue334 : Sparse (Fin 909) := [(0, (49 / 864)), (1, (-35 / 432)), (2, (-55 / 432)), (3, (-5 / 27)), (6, (5 / 288)), (7, (-5 / 54)), (8, (-5 / 27))]

def singlePairValue335 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (95 / 432)), (2, (-5 / 864)), (3, (5 / 54)), (6, (-5 / 864)), (7, (5 / 54))]

def singlePairValue336 : Sparse (Fin 909) := [(0, (47 / 864)), (1, (-5 / 216)), (2, (5 / 144)), (6, (-5 / 864)), (8, (5 / 54))]

def singlePairValue337 : Sparse (Fin 909) := [(0, (1 / 54)), (1, (65 / 432)), (2, (5 / 864)), (5, (5 / 216)), (6, (-5 / 864)), (7, (5 / 54)), (12, (5 / 54)), (13, (5 / 54)), (35, (5 / 54))]

def singlePairValue338 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (25 / 108)), (5, (5 / 108)), (6, (5 / 432))]

def singlePairValue339 : Sparse (Fin 909) := [(0, (37 / 864)), (1, (-35 / 432)), (2, (25 / 432)), (3, (5 / 27)), (6, (-5 / 864)), (7, (5 / 54))]

def singlePairValue340 : Sparse (Fin 909) := [(0, (7 / 288)), (1, (5 / 216)), (2, (5 / 108)), (3, (5 / 18)), (4, (5 / 54)), (5, (5 / 216)), (6, (-5 / 864)), (13, (5 / 54)), (26, (5 / 18)), (34, (5 / 27)), (35, (5 / 54)), (67, (5 / 54))]

def singlePairValue341 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (-25 / 216)), (2, (-5 / 72)), (5, (5 / 108)), (6, (5 / 432))]

def singlePairValue342 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (5 / 216)), (2, (5 / 432)), (5, (-5 / 108)), (26, (-5 / 27)), (34, (-5 / 27)), (67, (-5 / 27))]

def singlePairValue343 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (35 / 216)), (2, (5 / 432)), (3, (-5 / 27)), (5, (-5 / 108)), (7, (-5 / 27))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue344 : Sparse (Fin 909) := [(0, (1 / 18)), (1, (-5 / 108)), (5, (-5 / 108)), (8, (-5 / 27))]

def singlePairValue345 : Sparse (Fin 909) := [(0, (7 / 288)), (1, (5 / 96)), (2, (-95 / 864)), (3, (-25 / 27)), (5, (5 / 108)), (6, (-5 / 864)), (7, (-5 / 54)), (12, (-10 / 27)), (13, (-35 / 54)), (34, (-5 / 54)), (35, (-5 / 54)), (51, (5 / 9)), (52, (-5 / 18)), (54, (5 / 18)), (64, (5 / 18))]

def singlePairValue346 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-35 / 864)), (2, (5 / 96)), (3, (5 / 54)), (5, (-5 / 108)), (7, (5 / 54)), (51, (-5 / 18)), (54, (-5 / 18)), (64, (-5 / 18))]

def singlePairValue347 : Sparse (Fin 909) := [(0, (7 / 288)), (2, (-5 / 54)), (3, (-35 / 54)), (4, (-5 / 27)), (5, (-5 / 72)), (6, (5 / 288)), (12, (-5 / 27)), (13, (-5 / 27)), (25, (5 / 18)), (26, (-5 / 27)), (31, (5 / 9)), (33, (5 / 9)), (34, (-5 / 54)), (51, (5 / 9)), (52, (-5 / 54)), (64, (5 / 18)), (123, (5 / 9))]

def singlePairValue348 : Sparse (Fin 909) := [(0, (7 / 288)), (1, (-5 / 96)), (2, (35 / 864)), (3, (5 / 54)), (5, (5 / 216)), (6, (-5 / 864)), (25, (-5 / 18)), (26, (5 / 54)), (64, (-5 / 18)), (123, (-5 / 18))]

def singlePairValue349 : Sparse (Fin 909) := [(0, (5 / 288)), (1, (5 / 216)), (2, (5 / 432)), (5, (5 / 216)), (6, (-5 / 864)), (31, (-5 / 18)), (33, (-5 / 18)), (51, (-5 / 18)), (123, (-5 / 18))]

def singlePairValue350 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-5 / 144)), (6, (5 / 432)), (123, (5 / 9))]

def singlePairValue351 : Sparse (Fin 909) := [(0, (25 / 864)), (1, (5 / 144)), (2, (-25 / 144)), (3, (-5 / 6)), (4, (-5 / 18)), (5, (-5 / 72)), (6, (5 / 288)), (12, (-5 / 18)), (13, (-5 / 27)), (51, (5 / 6)), (52, (-5 / 18))]

def singlePairValue352 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (5 / 432)), (2, (25 / 864)), (3, (5 / 27)), (4, (5 / 54)), (5, (5 / 216)), (6, (-5 / 864)), (51, (-5 / 18)), (52, (5 / 54))]

def singlePairValue353 : Sparse (Fin 909) := [(0, (1 / 32)), (1, (-25 / 432)), (2, (5 / 108)), (3, (5 / 27)), (5, (5 / 216)), (6, (-5 / 864)), (12, (5 / 54)), (13, (5 / 54)), (51, (-5 / 18)), (52, (5 / 54))]

def singlePairValue354 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 144)), (5, (-5 / 108)), (64, (5 / 9))]

def singlePairValue355 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (-5 / 144)), (2, (5 / 144)), (5, (-5 / 108)), (51, (5 / 9))]

def singlePairValue356 : Sparse (Fin 909) := [(0, (19 / 864)), (1, (-25 / 864)), (2, (25 / 432)), (3, (-5 / 27)), (5, (-5 / 54)), (12, (-5 / 54)), (13, (-5 / 54)), (23, (5 / 9)), (25, (5 / 18)), (26, (-5 / 54)), (27, (5 / 36)), (33, (5 / 18)), (35, (-5 / 54)), (54, (5 / 9)), (55, (5 / 9)), (63, (5 / 9)), (64, (5 / 18)), (65, (5 / 9)), (68, (5 / 18)), (125, (5 / 18)), (196, (5 / 18)), (264, (5 / 18)), (266, (5 / 18))]

def singlePairValue357 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (5 / 96)), (2, (-25 / 864)), (3, (-20 / 27)), (5, (5 / 216)), (7, (-5 / 54)), (12, (-5 / 18)), (13, (-5 / 9)), (23, (5 / 18)), (26, (-10 / 27)), (27, (-5 / 72)), (34, (-5 / 27)), (35, (-5 / 18)), (55, (5 / 9)), (63, (5 / 18)), (65, (5 / 18)), (67, (-5 / 54))]

def singlePairValue358 : Sparse (Fin 909) := [(0, (31 / 864)), (1, (-35 / 432)), (2, (5 / 864)), (3, (-5 / 9)), (5, (-5 / 72)), (12, (-5 / 27)), (13, (-5 / 18)), (25, (5 / 18)), (26, (-5 / 54)), (27, (5 / 24)), (33, (5 / 6)), (35, (-5 / 54)), (55, (5 / 9)), (63, (5 / 18)), (64, (5 / 9))]

def singlePairValue359 : Sparse (Fin 909) := [(0, (1 / 48)), (1, (145 / 864)), (2, (-25 / 864)), (3, (-25 / 27)), (4, (-10 / 27)), (5, (5 / 216)), (7, (-5 / 54)), (12, (-5 / 54)), (13, (-5 / 54)), (24, (5 / 18)), (26, (-5 / 9)), (27, (-5 / 72)), (33, (5 / 18)), (34, (-5 / 27)), (35, (-5 / 27)), (55, (5 / 6)), (64, (5 / 18)), (66, (5 / 18)), (67, (-5 / 54))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue360 : Sparse (Fin 909) := [(0, (17 / 432)), (1, (25 / 288)), (2, (35 / 288)), (3, (-10 / 9)), (4, (-5 / 9)), (5, (-5 / 72)), (12, (-5 / 18)), (13, (-5 / 27)), (26, (-5 / 9)), (27, (5 / 24)), (35, (-5 / 18)), (55, (5 / 6))]

def singlePairValue361 : Sparse (Fin 909) := [(0, (31 / 864)), (1, (-25 / 288)), (2, (-5 / 72)), (3, (5 / 27)), (5, (5 / 216)), (12, (5 / 54)), (13, (5 / 54)), (26, (5 / 54)), (27, (-5 / 72)), (35, (5 / 54)), (55, (-5 / 18))]

def singlePairValue362 : Sparse (Fin 909) := [(0, (17 / 864)), (1, (5 / 144)), (2, (-5 / 96)), (3, (5 / 54)), (5, (5 / 216)), (27, (-5 / 72)), (33, (-5 / 18)), (55, (-5 / 18)), (64, (-5 / 18))]

def singlePairValue363 : Sparse (Fin 909) := [(0, (25 / 864)), (1, (5 / 144)), (2, (-5 / 864)), (3, (-35 / 54)), (4, (-5 / 27)), (5, (5 / 216)), (7, (-5 / 54)), (12, (-5 / 54)), (13, (-5 / 54)), (23, (5 / 18)), (25, (5 / 9)), (26, (-10 / 27)), (27, (-5 / 72)), (33, (5 / 9)), (34, (-5 / 27)), (35, (-5 / 54)), (55, (5 / 18)), (63, (5 / 9)), (64, (5 / 9)), (65, (5 / 18)), (67, (-5 / 54))]

def singlePairValue364 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-25 / 432)), (2, (-5 / 216)), (23, (-5 / 18)), (27, (5 / 36)), (55, (-5 / 18)), (63, (-5 / 18)), (65, (-5 / 18))]

def singlePairValue365 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 108)), (2, (-5 / 108)), (5, (5 / 216)), (25, (-5 / 18)), (27, (-5 / 72)), (33, (-5 / 18)), (63, (-5 / 18)), (64, (-5 / 18))]

def singlePairValue366 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 216)), (2, (65 / 432)), (27, (5 / 36)), (63, (5 / 9))]

def singlePairValue367 : Sparse (Fin 909) := [(0, (7 / 432)), (1, (5 / 72)), (2, (5 / 432)), (24, (-5 / 18)), (27, (5 / 36)), (55, (-5 / 9)), (66, (-5 / 18))]

def singlePairValue368 : Sparse (Fin 909) := [(0, (29 / 864)), (1, (-5 / 864)), (3, (5 / 18)), (4, (5 / 27)), (5, (5 / 216)), (26, (5 / 27)), (27, (-5 / 72)), (35, (5 / 54)), (55, (-5 / 18))]

def singlePairValue369 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 72)), (2, (-5 / 144)), (27, (5 / 36)), (55, (5 / 9))]

def singlePairValue370 : Sparse (Fin 909) := [(0, (25 / 432)), (1, (-25 / 432)), (2, (-5 / 108)), (3, (-10 / 27)), (5, (-5 / 216)), (12, (-5 / 54)), (13, (-5 / 54)), (26, (-5 / 27)), (27, (5 / 72)), (35, (-5 / 54)), (55, (5 / 18))]

def singlePairValue371 : Sparse (Fin 909) := [(0, (35 / 864)), (1, (205 / 864)), (2, (5 / 108)), (3, (-35 / 54)), (4, (-10 / 27)), (5, (-5 / 216)), (26, (-10 / 27)), (27, (5 / 72)), (35, (-5 / 54)), (55, (5 / 18))]

def singlePairValue372 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (-5 / 216)), (2, (-25 / 432)), (3, (5 / 54)), (27, (-5 / 72)), (55, (-5 / 18))]

def singlePairValue373 : Sparse (Fin 909) := [(0, (11 / 864)), (1, (5 / 96)), (2, (-5 / 108)), (3, (-5 / 18)), (12, (-5 / 27)), (13, (-25 / 54)), (26, (-5 / 27)), (34, (-5 / 27))]

def singlePairValue374 : Sparse (Fin 909) := [(0, (1 / 108)), (1, (5 / 144)), (2, (5 / 144)), (13, (5 / 27))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue376 : Sparse (Fin 909) := [(0, (17 / 864)), (1, (55 / 216)), (2, (-5 / 288)), (3, (-25 / 54)), (4, (-5 / 27)), (26, (-5 / 27))]

def singlePairValue377 : Sparse (Fin 909) := [(0, (17 / 432)), (1, (-35 / 864)), (2, (-5 / 96)), (3, (5 / 54)), (26, (5 / 54))]

def singlePairValue378 : Sparse (Fin 909) := [(0, (29 / 864)), (1, (-5 / 216)), (2, (-35 / 864)), (3, (5 / 54))]

def singlePairValue379 : Sparse (Fin 909) := [(0, (1 / 24)), (2, (5 / 24))]

def singlePairValue380 : Sparse (Fin 909) := [(0, (31 / 864)), (1, (5 / 48)), (2, (5 / 432)), (3, (-65 / 54)), (4, (-10 / 27)), (5, (-5 / 108)), (6, (5 / 864)), (12, (-10 / 27)), (13, (-5 / 9)), (26, (-5 / 9)), (27, (5 / 72)), (33, (5 / 9)), (34, (-10 / 27)), (35, (-5 / 54)), (54, (5 / 18)), (65, (5 / 18)), (67, (-5 / 54))]

def singlePairValue381 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-55 / 864)), (2, (-35 / 864)), (3, (5 / 54)), (5, (5 / 216)), (26, (5 / 54)), (27, (-5 / 72)), (33, (-5 / 18)), (54, (-5 / 18)), (65, (-5 / 18))]

def singlePairValue382 : Sparse (Fin 909) := [(0, (7 / 432)), (1, (155 / 864)), (2, (-35 / 864)), (3, (-10 / 9)), (4, (-5 / 27)), (12, (-5 / 9)), (13, (-35 / 54)), (26, (-5 / 27)), (33, (5 / 9)), (34, (-5 / 27))]

def singlePairValue383 : Sparse (Fin 909) := [(0, (1 / 72)), (1, (-5 / 864)), (2, (-5 / 864)), (3, (5 / 27)), (12, (5 / 54)), (13, (5 / 27)), (33, (-5 / 18))]

def singlePairValue384 : Sparse (Fin 909) := [(0, (19 / 864)), (1, (-25 / 288)), (3, (5 / 18)), (12, (5 / 27)), (13, (10 / 27)), (34, (5 / 54))]

def singlePairValue385 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-5 / 72)), (2, (5 / 36)), (13, (-10 / 27))]

def singlePairValue386 : Sparse (Fin 909) := [(0, (13 / 864)), (1, (5 / 288)), (2, (-5 / 216)), (3, (5 / 18)), (13, (5 / 54)), (26, (5 / 27)), (34, (5 / 27))]

def singlePairValue387 : Sparse (Fin 909) := [(0, (17 / 432)), (1, (-5 / 432)), (2, (5 / 108)), (3, (5 / 27)), (4, (5 / 54)), (26, (5 / 54))]

def singlePairValue388 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (-5 / 144)), (2, (-5 / 108)), (26, (-5 / 27))]

def singlePairValue390 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (-5 / 54)), (2, (-25 / 432)), (3, (-5 / 27))]

def singlePairValue391 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 54)), (2, (-25 / 432)), (3, (-5 / 27)), (13, (-5 / 27)), (34, (-5 / 27))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue392 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (5 / 144)), (2, (25 / 216)), (3, (-10 / 9)), (4, (-10 / 27)), (5, (-5 / 72)), (13, (-5 / 27)), (26, (-10 / 9)), (27, (5 / 24)), (34, (-20 / 27)), (65, (5 / 18)), (66, (5 / 9)), (67, (-5 / 18))]

def singlePairValue393 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 864)), (2, (-25 / 864)), (3, (5 / 27)), (5, (5 / 216)), (13, (5 / 54)), (26, (5 / 27)), (27, (-5 / 72)), (34, (5 / 27)), (65, (-5 / 18)), (67, (5 / 54))]

def singlePairValue394 : Sparse (Fin 909) := [(0, (1 / 432)), (1, (25 / 96)), (2, (-65 / 864)), (3, (-65 / 54)), (4, (-5 / 9)), (12, (-5 / 54)), (13, (-5 / 54)), (26, (-35 / 54)), (33, (5 / 18)), (34, (-5 / 27))]

def singlePairValue395 : Sparse (Fin 909) := [(0, (5 / 864)), (1, (5 / 108)), (2, (-5 / 288)), (3, (5 / 27)), (26, (5 / 54)), (33, (-5 / 18))]

def singlePairValue397 : Sparse (Fin 909) := [(0, (1 / 48)), (1, (-55 / 864)), (2, (-25 / 864)), (3, (5 / 27)), (12, (5 / 54)), (13, (5 / 54))]

def singlePairValue398 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 108)), (2, (-5 / 108)), (3, (5 / 54)), (5, (5 / 216)), (12, (5 / 54)), (13, (5 / 54)), (27, (-5 / 72)), (33, (-5 / 18)), (55, (-5 / 18)), (61, (-5 / 18))]

def singlePairValue399 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (35 / 432)), (2, (5 / 216)), (3, (5 / 27)), (4, (5 / 54)), (5, (5 / 216)), (26, (5 / 18)), (27, (-5 / 72)), (34, (5 / 27)), (66, (-5 / 18)), (67, (5 / 54))]

def singlePairValue400 : Sparse (Fin 909) := [(0, (11 / 864)), (1, (5 / 432)), (2, (25 / 864)), (3, (10 / 27)), (4, (5 / 27)), (26, (5 / 18)), (34, (5 / 54))]

def singlePairValue401 : Sparse (Fin 909) := [(0, (7 / 288)), (2, (25 / 864)), (3, (5 / 18)), (4, (5 / 27)), (26, (5 / 27))]

def singlePairValue402 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (-25 / 432)), (2, (-5 / 144)), (3, (-5 / 27)), (26, (-5 / 27))]

def singlePairValue403 : Sparse (Fin 909) := [(0, (47 / 864)), (1, (-5 / 216)), (2, (55 / 864)), (3, (5 / 54))]

def singlePairValue404 : Sparse (Fin 909) := [(0, (1 / 18)), (1, (-5 / 72)), (2, (-5 / 72))]

def singlePairValue405 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (-5 / 54)), (2, (-25 / 432)), (3, (-5 / 27))]

def singlePairValue406 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-5 / 216)), (3, (-5 / 27)), (26, (-5 / 27)), (34, (-5 / 27))]

def singlePairValue407 : Sparse (Fin 909) := [(0, (1 / 24)), (2, (5 / 24))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue408 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 72)), (2, (-5 / 72)), (27, (5 / 36)), (65, (5 / 9))]

def singlePairValue409 : Sparse (Fin 909) := [(0, (17 / 864)), (1, (-25 / 864)), (2, (5 / 108)), (3, (5 / 18)), (4, (5 / 54)), (12, (5 / 54)), (13, (5 / 54)), (26, (5 / 54)), (33, (-5 / 18)), (34, (5 / 54))]

def singlePairValue410 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-35 / 432)), (2, (-5 / 432)), (33, (5 / 9))]

def singlePairValue411 : Sparse (Fin 909) := [(0, (11 / 864)), (1, (5 / 36)), (2, (5 / 288)), (3, (5 / 18)), (12, (5 / 18)), (13, (5 / 27))]

def singlePairValue412 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (35 / 432)), (2, (-5 / 216)), (3, (-5 / 27)), (12, (-5 / 27)), (13, (-5 / 27))]

def singlePairValue413 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (5 / 72)), (2, (5 / 108)), (27, (5 / 36)), (66, (5 / 9))]

def singlePairValue414 : Sparse (Fin 909) := [(0, (13 / 432)), (1, (-5 / 216)), (2, (5 / 144)), (3, (-5 / 27)), (4, (-5 / 27)), (26, (-5 / 27))]

def singlePairValue415 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 48)), (2, (-5 / 72)), (26, (5 / 9))]

def singlePairValue416 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (55 / 216)), (2, (5 / 432)), (3, (-5 / 27))]

def singlePairValue421 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 48)), (2, (-5 / 48)), (34, (5 / 9))]

def singlePairValue423 : Sparse (Fin 909) := [(0, (1 / 24)), (1, (5 / 432)), (2, (5 / 144)), (5, (-5 / 108)), (31, (5 / 18)), (51, (5 / 9)), (68, (5 / 18)), (124, (5 / 18)), (126, (5 / 9)), (236, (5 / 18))]

def singlePairValue424 : Sparse (Fin 909) := [(0, (1 / 32)), (1, (5 / 432)), (2, (5 / 96)), (3, (-10 / 27)), (4, (-5 / 54)), (5, (-5 / 72)), (7, (-5 / 27)), (12, (-5 / 54)), (23, (5 / 9)), (24, (5 / 9)), (51, (5 / 18)), (55, (5 / 9)), (68, (5 / 18)), (124, (5 / 18)), (125, (5 / 18)), (126, (5 / 18)), (197, (5 / 18))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue426 : Sparse (Fin 909) := [(0, (5 / 288)), (1, (35 / 432)), (2, (5 / 96)), (3, (-5 / 27)), (4, (-5 / 54)), (5, (-5 / 54)), (12, (-5 / 54)), (27, (5 / 72)), (31, (5 / 18)), (51, (5 / 9)), (55, (5 / 18)), (68, (5 / 18)), (194, (-5 / 9)), (486, (-5 / 9)), (487, (-5 / 9))]

def singlePairValue427 : Sparse (Fin 909) := [(0, (1 / 48)), (1, (-5 / 288)), (2, (25 / 288)), (3, (-5 / 54)), (5, (-5 / 54)), (12, (-5 / 54)), (23, (5 / 9)), (24, (5 / 18)), (25, (5 / 18)), (27, (5 / 72)), (54, (5 / 18)), (55, (5 / 18)), (68, (5 / 18)), (195, (-5 / 9)), (263, (-5 / 9)), (487, (-5 / 9))]

def singlePairValue428 : Sparse (Fin 909) := [(0, (7 / 432)), (1, (5 / 36)), (2, (-25 / 432)), (23, (5 / 9)), (24, (10 / 9)), (27, (-5 / 18)), (30, (5 / 9)), (55, (5 / 9)), (194, (-5 / 9))]

def singlePairValue429 : Sparse (Fin 909) := [(0, (5 / 108)), (2, (-5 / 72)), (3, (-5 / 18)), (5, (5 / 54)), (7, (-5 / 54)), (8, (-5 / 54)), (12, (-5 / 54)), (23, (5 / 18)), (24, (5 / 18)), (27, (-5 / 24)), (55, (5 / 18))]

def singlePairValue430 : Sparse (Fin 909) := [(0, (1 / 48)), (1, (155 / 864)), (2, (-115 / 864)), (3, (-5 / 27)), (4, (-5 / 54)), (5, (5 / 72)), (7, (-5 / 54)), (8, (-5 / 54)), (24, (5 / 18)), (27, (-5 / 18)), (30, (5 / 18)), (31, (5 / 18)), (51, (5 / 18))]

def singlePairValue431 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (5 / 36)), (2, (-5 / 48)), (3, (-5 / 9)), (4, (-5 / 27)), (5, (5 / 108)), (7, (-5 / 54)), (8, (-5 / 54)), (12, (-5 / 18)), (23, (5 / 18)), (24, (5 / 18)), (27, (-5 / 36)), (51, (5 / 9)), (55, (5 / 9))]

def singlePairValue432 : Sparse (Fin 909) := [(0, (1 / 32)), (1, (-5 / 72)), (2, (5 / 288)), (23, (-5 / 18)), (24, (-5 / 18)), (27, (5 / 24)), (55, (-5 / 18))]

def singlePairValue433 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (5 / 216)), (24, (-5 / 18)), (27, (5 / 18)), (30, (-5 / 18))]

def singlePairValue434 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (25 / 432)), (2, (-5 / 432)), (3, (-35 / 54)), (4, (-5 / 54)), (5, (5 / 216)), (12, (-10 / 27)), (13, (-25 / 54)), (27, (-5 / 72)), (33, (5 / 9)), (51, (5 / 18)), (55, (5 / 18)), (59, (5 / 18)), (61, (5 / 18)), (194, (-5 / 9))]

def singlePairValue435 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-5 / 108)), (2, (5 / 216)), (27, (5 / 36)), (194, (5 / 9))]

def singlePairValue436 : Sparse (Fin 909) := [(0, (19 / 432)), (2, (25 / 432)), (3, (-5 / 18)), (4, (-5 / 27)), (5, (-5 / 108)), (12, (-5 / 54)), (27, (5 / 72)), (31, (5 / 9)), (51, (5 / 9)), (55, (5 / 18))]

def singlePairValue437 : Sparse (Fin 909) := [(0, (35 / 864)), (1, (-5 / 144)), (2, (5 / 864)), (5, (5 / 216)), (31, (-5 / 18)), (51, (-5 / 18))]

def singlePairValue438 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (-35 / 432)), (2, (-5 / 432)), (3, (5 / 27)), (4, (5 / 54)), (5, (5 / 216)), (12, (5 / 54)), (27, (-5 / 72)), (51, (-5 / 18)), (55, (-5 / 18))]

def singlePairValue439 : Sparse (Fin 909) := [(0, (7 / 288)), (1, (55 / 432)), (2, (55 / 864)), (3, (-10 / 27)), (5, (-5 / 54)), (7, (-5 / 27)), (12, (-5 / 27)), (23, (5 / 9)), (25, (5 / 18)), (27, (5 / 36)), (54, (5 / 9)), (68, (5 / 18)), (124, (5 / 18)), (125, (5 / 9)), (196, (5 / 18))]

def singlePairValue440 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 216)), (2, (5 / 432)), (23, (5 / 9)), (24, (5 / 9)), (55, (10 / 9)), (63, (5 / 9)), (65, (5 / 9))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue441 : Sparse (Fin 909) := [(0, (11 / 288)), (1, (25 / 864)), (2, (-5 / 144)), (3, (-35 / 54)), (4, (-5 / 54)), (5, (5 / 108)), (7, (-5 / 27)), (12, (-5 / 18)), (13, (-5 / 54)), (23, (5 / 9)), (24, (5 / 18)), (25, (5 / 18)), (26, (-5 / 54)), (27, (-5 / 36)), (35, (-5 / 54)), (54, (5 / 18)), (55, (5 / 18))]

def singlePairValue442 : Sparse (Fin 909) := [(0, (19 / 864)), (1, (155 / 864)), (2, (-5 / 48)), (3, (-5 / 6)), (4, (-10 / 27)), (5, (5 / 108)), (7, (-5 / 18)), (12, (-5 / 54)), (23, (5 / 18)), (24, (5 / 9)), (26, (-5 / 27)), (27, (-5 / 36)), (35, (-5 / 54)), (55, (5 / 18))]

def singlePairValue443 : Sparse (Fin 909) := [(0, (1 / 32)), (1, (5 / 432)), (2, (-5 / 288)), (3, (-5 / 9)), (4, (-5 / 54)), (5, (5 / 216)), (7, (-5 / 54)), (12, (-5 / 18)), (23, (5 / 9)), (25, (5 / 9)), (26, (-5 / 54)), (27, (-5 / 72)), (33, (5 / 9)), (51, (5 / 18)), (54, (5 / 9)), (55, (5 / 18)), (63, (5 / 18)), (64, (5 / 18)), (65, (5 / 18))]

def singlePairValue444 : Sparse (Fin 909) := [(0, (1 / 27)), (1, (-5 / 144)), (2, (5 / 48)), (3, (-5 / 9)), (4, (-5 / 18)), (5, (-5 / 72)), (12, (-5 / 27)), (23, (5 / 18)), (25, (5 / 9)), (26, (-5 / 27)), (27, (5 / 24)), (31, (5 / 18)), (33, (5 / 9)), (54, (5 / 9)), (65, (5 / 18)), (195, (-5 / 9))]

def singlePairValue445 : Sparse (Fin 909) := [(0, (1 / 32)), (1, (5 / 36)), (2, (55 / 864)), (3, (-35 / 54)), (5, (-5 / 72)), (7, (-5 / 54)), (12, (-5 / 9)), (23, (5 / 6)), (25, (5 / 6)), (27, (5 / 24)), (54, (5 / 9))]

def singlePairValue446 : Sparse (Fin 909) := [(0, (23 / 864)), (1, (95 / 864)), (2, (-5 / 432)), (3, (5 / 54)), (5, (5 / 216)), (12, (5 / 54)), (23, (-5 / 18)), (25, (-5 / 18)), (27, (-5 / 72)), (54, (-5 / 18))]

def singlePairValue447 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 144)), (5, (5 / 216)), (27, (-5 / 72)), (195, (5 / 9))]

def singlePairValue448 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (5 / 432)), (2, (5 / 108)), (3, (-20 / 27)), (4, (-10 / 27)), (5, (-5 / 72)), (7, (-5 / 18)), (12, (-5 / 27)), (23, (5 / 18)), (24, (5 / 9)), (27, (5 / 24))]

def singlePairValue449 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (5 / 36)), (2, (-5 / 432)), (3, (5 / 27)), (5, (5 / 216)), (7, (5 / 54)), (12, (5 / 54)), (23, (-5 / 18)), (27, (-5 / 72))]

def singlePairValue450 : Sparse (Fin 909) := [(0, (13 / 288)), (1, (-35 / 288)), (2, (-5 / 432)), (3, (5 / 27)), (4, (5 / 54)), (5, (5 / 216)), (7, (5 / 54)), (24, (-5 / 18)), (27, (-5 / 72))]

def singlePairValue451 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (5 / 18)), (23, (5 / 9)), (27, (5 / 36))]

def singlePairValue452 : Sparse (Fin 909) := [(0, (1 / 24)), (1, (-5 / 72)), (24, (5 / 9)), (27, (5 / 36))]

def singlePairValue453 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (5 / 54)), (2, (-5 / 48)), (3, (-5 / 27)), (4, (-5 / 27)), (5, (5 / 72)), (8, (-5 / 27)), (24, (5 / 9)), (27, (-5 / 24)), (30, (5 / 18)), (56, (5 / 18))]

def singlePairValue454 : Sparse (Fin 909) := [(0, (7 / 144)), (1, (5 / 216)), (2, (-5 / 96)), (3, (-25 / 54)), (4, (-5 / 54)), (5, (-5 / 216)), (6, (5 / 864)), (12, (-5 / 27)), (13, (-5 / 54)), (31, (5 / 18)), (51, (5 / 18)), (52, (-5 / 54))]

def singlePairValue455 : Sparse (Fin 909) := [(0, (1 / 24)), (1, (65 / 864)), (2, (-5 / 432)), (3, (-35 / 54)), (4, (-5 / 18)), (5, (-5 / 108)), (6, (5 / 864)), (12, (-5 / 18)), (13, (-5 / 18)), (26, (-5 / 54)), (27, (5 / 72)), (35, (-5 / 54)), (51, (5 / 18)), (52, (-5 / 54)), (55, (5 / 18))]

def singlePairValue456 : Sparse (Fin 909) := [(0, (37 / 864)), (1, (-5 / 432)), (2, (5 / 216)), (3, (-5 / 6)), (4, (-10 / 27)), (5, (-5 / 108)), (6, (5 / 864)), (7, (-5 / 54)), (12, (-5 / 27)), (23, (5 / 18)), (25, (5 / 9)), (26, (-10 / 27)), (27, (5 / 72)), (35, (-5 / 54)), (54, (5 / 18))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue457 : Sparse (Fin 909) := [(0, (23 / 864)), (1, (35 / 216)), (2, (-5 / 216)), (3, (-35 / 54)), (4, (-10 / 27)), (5, (-5 / 108)), (6, (5 / 864)), (7, (-5 / 54)), (12, (-5 / 27)), (13, (-5 / 54)), (24, (5 / 18)), (26, (-5 / 27)), (27, (5 / 72)), (35, (-5 / 54)), (56, (5 / 18))]

def singlePairValue458 : Sparse (Fin 909) := [(0, (37 / 864)), (1, (25 / 432)), (3, (-20 / 27)), (4, (-5 / 27)), (5, (-5 / 108)), (6, (5 / 864)), (12, (-25 / 54)), (13, (-5 / 27)), (23, (5 / 18)), (25, (5 / 9)), (27, (5 / 72)), (31, (5 / 18)), (33, (10 / 9)), (54, (5 / 9)), (62, (5 / 18))]

def singlePairValue459 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (155 / 864)), (2, (-5 / 216)), (3, (-5 / 27)), (5, (-5 / 108)), (6, (5 / 864)), (7, (-5 / 54)), (12, (-5 / 54)), (13, (-5 / 18)), (23, (5 / 18)), (25, (5 / 18)), (27, (5 / 72)), (35, (-5 / 54)), (54, (5 / 18))]

def singlePairValue461 : Sparse (Fin 909) := [(0, (-1 / 216)), (1, (95 / 864)), (2, (-25 / 864)), (3, (-10 / 27)), (4, (-5 / 27)), (12, (-5 / 27)), (13, (-5 / 54))]

def singlePairValue462 : Sparse (Fin 909) := [(0, (1 / 108)), (1, (145 / 864)), (2, (-35 / 864)), (3, (-20 / 27)), (4, (-5 / 27)), (12, (-10 / 27)), (13, (-5 / 18))]

def singlePairValue463 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (5 / 48)), (3, (-10 / 9)), (4, (-5 / 27)), (12, (-5 / 9)), (13, (-10 / 9)), (32, (-5 / 54))]

def singlePairValue467 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 36)), (2, (5 / 144)), (3, (5 / 18)), (4, (5 / 54)), (12, (5 / 27)), (13, (5 / 54))]

def singlePairValue468 : Sparse (Fin 909) := [(0, (1 / 48)), (1, (25 / 432)), (2, (5 / 216)), (3, (5 / 27)), (13, (5 / 27))]

def singlePairValue470 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (35 / 288)), (2, (-25 / 432)), (3, (-5 / 6)), (4, (-5 / 18)), (5, (-5 / 108)), (6, (5 / 864)), (12, (-10 / 27)), (26, (-5 / 27)), (27, (5 / 72)), (33, (5 / 6)), (81, (5 / 18)), (195, (-5 / 9))]

def singlePairValue471 : Sparse (Fin 909) := [(0, (43 / 864)), (1, (55 / 216)), (2, (5 / 216)), (3, (-10 / 27)), (5, (-5 / 216)), (6, (5 / 864)), (7, (-5 / 27)), (12, (-5 / 27)), (23, (5 / 18)), (27, (5 / 72))]

def singlePairValue472 : Sparse (Fin 909) := [(0, (23 / 432)), (1, (-5 / 216)), (2, (-5 / 96)), (3, (-5 / 18)), (4, (-5 / 27)), (5, (-5 / 216)), (6, (5 / 864)), (7, (-5 / 54)), (8, (-5 / 54)), (24, (5 / 18)), (27, (5 / 72))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue473 : Sparse (Fin 909) := [(0, (41 / 864)), (1, (5 / 48)), (2, (-5 / 54)), (3, (-20 / 27)), (5, (-5 / 216)), (6, (5 / 864)), (7, (-5 / 27)), (12, (-25 / 54)), (23, (5 / 18)), (27, (5 / 72))]

def singlePairValue474 : Sparse (Fin 909) := [(0, (1 / 18)), (1, (-5 / 108)), (5, (5 / 216)), (8, (5 / 54)), (24, (-5 / 18)), (27, (-5 / 72))]

def singlePairValue475 : Sparse (Fin 909) := [(0, (1 / 27)), (1, (-5 / 108)), (2, (5 / 864)), (3, (-10 / 27)), (4, (-5 / 27)), (5, (-5 / 108)), (6, (5 / 864)), (25, (5 / 9)), (26, (-5 / 27)), (27, (5 / 72)), (31, (5 / 18)), (33, (5 / 9)), (63, (5 / 18)), (64, (5 / 9)), (123, (5 / 18))]

def singlePairValue476 : Sparse (Fin 909) := [(0, (25 / 864)), (1, (65 / 432)), (2, (-5 / 216)), (3, (-35 / 54)), (4, (-5 / 18)), (5, (-5 / 108)), (6, (5 / 864)), (12, (-5 / 18)), (25, (5 / 9)), (26, (-5 / 54)), (27, (5 / 72)), (31, (5 / 9)), (33, (5 / 6)), (51, (5 / 18)), (55, (5 / 18)), (64, (5 / 18)), (123, (5 / 18))]

def singlePairValue477 : Sparse (Fin 909) := [(0, (25 / 864)), (1, (5 / 288)), (2, (-35 / 864)), (3, (-5 / 18)), (4, (-5 / 54)), (5, (-5 / 108)), (6, (5 / 864)), (12, (-5 / 54)), (26, (-5 / 27)), (27, (5 / 72)), (35, (-5 / 54)), (51, (5 / 18)), (52, (-5 / 54)), (55, (5 / 18))]

def singlePairValue478 : Sparse (Fin 909) := [(0, (13 / 432)), (2, (25 / 432)), (3, (-10 / 27)), (4, (-5 / 27)), (25, (5 / 18)), (26, (-5 / 27))]

def singlePairValue479 : Sparse (Fin 909) := [(0, (7 / 432)), (1, (85 / 864)), (2, (-25 / 864)), (3, (-25 / 54)), (4, (-5 / 27)), (12, (-5 / 27)), (26, (-5 / 54))]

def singlePairValue480 : Sparse (Fin 909) := [(0, (5 / 288)), (1, (5 / 48)), (2, (-35 / 864)), (3, (-20 / 27)), (4, (-5 / 27)), (12, (-10 / 27)), (13, (-10 / 27)), (26, (-5 / 54)), (33, (5 / 9)), (34, (-5 / 54))]

def singlePairValue481 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (5 / 48)), (3, (-10 / 9)), (12, (-5 / 9)), (13, (-10 / 9)), (34, (-5 / 27))]

def singlePairValue483 : Sparse (Fin 909) := [(0, (1 / 27)), (1, (-35 / 432)), (2, (25 / 432)), (3, (5 / 27)), (12, (5 / 54))]

def singlePairValue484 : Sparse (Fin 909) := [(0, (1 / 432)), (1, (25 / 216)), (2, (-25 / 432)), (3, (-35 / 54)), (4, (-10 / 27)), (12, (-5 / 27)), (25, (5 / 9)), (26, (-5 / 54)), (31, (5 / 9)), (33, (5 / 6))]

def singlePairValue485 : Sparse (Fin 909) := [(0, (1 / 216)), (1, (25 / 216)), (2, (-5 / 108)), (3, (-35 / 54)), (4, (-5 / 18)), (12, (-5 / 27)), (13, (-5 / 54)), (25, (5 / 18)), (26, (-5 / 18)), (31, (5 / 18)), (33, (5 / 18)), (34, (-5 / 54))]

def singlePairValue486 : Sparse (Fin 909) := [(0, (-1 / 864)), (1, (35 / 108)), (2, (-5 / 96)), (3, (-5 / 6)), (4, (-5 / 9)), (12, (-10 / 27)), (25, (5 / 18)), (26, (-5 / 27))]

def singlePairValue487 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-25 / 432)), (2, (5 / 144)), (3, (5 / 27)), (4, (5 / 54)), (25, (-5 / 18)), (26, (5 / 54))]

def singlePairValue488 : Sparse (Fin 909) := [(0, (29 / 864)), (1, (5 / 48)), (2, (-5 / 96)), (3, (-5 / 18)), (4, (-5 / 27)), (12, (-5 / 27))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue56 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 216)), (2, (5 / 216)), (5, (5 / 54)), (6, (5 / 432)), (201, (5 / 9))]

def singlePairValue58 : Sparse (Fin 909) := [(0, (7 / 288)), (2, (5 / 432)), (3, (-5 / 27)), (5, (5 / 24)), (6, (-5 / 216)), (7, (-5 / 54)), (9, (5 / 72)), (13, (-10 / 27)), (35, (-20 / 27)), (52, (-20 / 27)), (58, (-5 / 864)), (60, (-25 / 54)), (69, (-5 / 54)), (70, (-5 / 54)), (128, (-10 / 27)), (257, (-5 / 27)), (260, (5 / 18)), (495, (-5 / 18))]

def singlePairValue59 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (35 / 432)), (2, (5 / 54)), (5, (-5 / 54)), (9, (-5 / 108)), (52, (5 / 27)), (58, (5 / 432)), (128, (5 / 27)), (495, (5 / 27))]

def singlePairValue60 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (5 / 864)), (2, (5 / 864)), (5, (-5 / 72)), (6, (5 / 432)), (7, (5 / 54)), (9, (-5 / 108)), (35, (5 / 27)), (52, (5 / 54)), (60, (5 / 54)), (69, (5 / 54)), (70, (5 / 54)), (257, (5 / 54)), (260, (-5 / 18))]

def singlePairValue61 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (-35 / 864)), (2, (-5 / 108)), (3, (-5 / 54)), (5, (5 / 54)), (6, (-5 / 432)), (7, (-5 / 27)), (9, (-5 / 54)), (35, (-5 / 27)), (52, (-5 / 27)), (58, (5 / 864)), (69, (-5 / 27)), (70, (-5 / 54)), (71, (-5 / 27))]

def singlePairValue62 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (5 / 432)), (2, (185 / 864)), (5, (5 / 216)), (35, (5 / 54)), (58, (-5 / 864)), (70, (5 / 54))]

def singlePairValue63 : Sparse (Fin 909) := [(0, (37 / 864)), (1, (-5 / 216)), (2, (-35 / 432)), (5, (5 / 18)), (6, (-5 / 144)), (8, (-10 / 27)), (9, (-5 / 54)), (52, (-5 / 27)), (58, (5 / 864)), (69, (-5 / 54)), (71, (-10 / 27))]

def singlePairValue64 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (-35 / 864)), (2, (-5 / 108)), (5, (-5 / 108)), (6, (5 / 216)), (58, (-5 / 864)), (71, (5 / 54))]

def singlePairValue65 : Sparse (Fin 909) := [(0, (29 / 864)), (1, (-5 / 216)), (2, (-55 / 432)), (3, (-5 / 9)), (5, (5 / 18)), (6, (-5 / 144)), (7, (-5 / 9)), (9, (-5 / 54)), (35, (-5 / 9)), (52, (-5 / 9)), (58, (5 / 864)), (69, (-5 / 18)), (70, (-5 / 27))]

def singlePairValue66 : Sparse (Fin 909) := [(0, (1 / 32)), (1, (5 / 108)), (2, (5 / 48)), (5, (-5 / 54)), (6, (5 / 144)), (52, (5 / 27)), (58, (-5 / 864)), (69, (5 / 54))]

def singlePairValue67 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 864)), (2, (5 / 864)), (3, (5 / 54)), (5, (5 / 216)), (6, (5 / 288)), (9, (5 / 216)), (13, (5 / 54)), (35, (5 / 18)), (52, (5 / 27)), (58, (-5 / 864)), (60, (5 / 27)), (128, (5 / 54)), (257, (5 / 54)), (495, (5 / 54))]

def singlePairValue68 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-25 / 288)), (2, (-25 / 432)), (3, (5 / 54)), (5, (-5 / 108)), (6, (-5 / 864)), (7, (5 / 27)), (9, (5 / 108)), (35, (5 / 27)), (52, (5 / 54)), (69, (5 / 54)), (70, (5 / 54))]

def singlePairValue69 : Sparse (Fin 909) := [(0, (17 / 432)), (1, (5 / 54)), (2, (25 / 432)), (5, (-5 / 54)), (8, (5 / 27)), (9, (5 / 108)), (71, (5 / 27))]

def singlePairValue70 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-35 / 432)), (2, (-25 / 432)), (5, (5 / 54)), (6, (-5 / 108)), (9, (5 / 108)), (58, (5 / 432))]

def singlePairValue71 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 144)), (2, (5 / 27)), (5, (-5 / 108)), (9, (-5 / 108)), (35, (-5 / 27)), (70, (-5 / 27))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue489 : Sparse (Fin 909) := [(0, (1 / 18)), (1, (-35 / 864)), (2, (25 / 864)), (3, (5 / 54)), (4, (5 / 54))]

def singlePairValue490 : Sparse (Fin 909) := [(0, (1 / 24)), (1, (-5 / 27)), (2, (5 / 216)), (3, (5 / 27)), (12, (5 / 27))]

def singlePairValue491 : Sparse (Fin 909) := [(0, (1 / 54)), (1, (-5 / 48)), (2, (5 / 144)), (3, (5 / 27)), (12, (5 / 27)), (33, (-5 / 9))]

def singlePairValue492 : Sparse (Fin 909) := [(0, (1 / 432)), (1, (5 / 36)), (2, (-5 / 144)), (3, (-5 / 9)), (13, (-10 / 27))]

def singlePairValue493 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-25 / 288)), (2, (5 / 864)), (3, (5 / 18)), (4, (5 / 27)), (12, (5 / 54)), (26, (5 / 54))]

def singlePairValue494 : Sparse (Fin 909) := [(0, (11 / 288)), (1, (95 / 432)), (2, (-5 / 864)), (3, (5 / 54)), (12, (5 / 54))]

def singlePairValue497 : Sparse (Fin 909) := [(1, (115 / 432)), (2, (-25 / 432)), (3, (-20 / 27)), (4, (-10 / 27)), (12, (-10 / 27)), (13, (-5 / 27)), (25, (5 / 9)), (31, (5 / 9)), (33, (5 / 9))]

def singlePairValue498 : Sparse (Fin 909) := [(0, (11 / 864)), (1, (-25 / 864)), (2, (5 / 432)), (3, (5 / 54)), (4, (5 / 54)), (25, (-5 / 18)), (31, (-5 / 18)), (33, (-5 / 18))]

def singlePairValue499 : Sparse (Fin 909) := [(0, (-17 / 864)), (1, (5 / 12)), (2, (-5 / 96)), (3, (-5 / 6)), (4, (-5 / 9)), (12, (-5 / 9)), (13, (-5 / 27))]

def singlePairValue500 : Sparse (Fin 909) := [(0, (1 / 108)), (1, (25 / 216)), (2, (-5 / 216)), (3, (5 / 27)), (12, (5 / 27)), (25, (-5 / 18))]

def singlePairValue501 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (5 / 54)), (2, (5 / 216)), (25, (5 / 9))]

def singlePairValue502 : Sparse (Fin 909) := [(0, (17 / 432)), (1, (-25 / 216)), (2, (-5 / 432)), (3, (5 / 27)), (4, (5 / 27)), (12, (5 / 54))]

def singlePairValue503 : Sparse (Fin 909) := [(0, (1 / 24)), (1, (-25 / 432)), (2, (5 / 432)), (3, (-5 / 27)), (4, (-5 / 27))]

def singlePairValue504 : Sparse (Fin 909) := [(0, (35 / 432)), (1, (-25 / 144)), (12, (5 / 54))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue507 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (5 / 12)), (12, (5 / 9))]

def singlePairValue508 : Sparse (Fin 909) := [(0, (13 / 216)), (1, (5 / 216)), (5, (-5 / 72)), (8, (-5 / 18)), (24, (5 / 18)), (27, (5 / 24)), (30, (5 / 9))]

def singlePairValue509 : Sparse (Fin 909) := [(0, (2 / 27)), (1, (5 / 108)), (5, (5 / 216)), (8, (5 / 54)), (27, (-5 / 72)), (30, (-5 / 18))]

def singlePairValue510 : Sparse (Fin 909) := [(0, (13 / 216)), (1, (5 / 216)), (27, (5 / 36)), (30, (5 / 9))]

def singlePairValue511 : Sparse (Fin 909) := [(0, (7 / 432)), (1, (35 / 144)), (2, (-115 / 864)), (3, (-10 / 27)), (4, (-5 / 18)), (5, (-5 / 216)), (6, (5 / 864)), (31, (5 / 9)), (51, (5 / 18)), (52, (-5 / 54))]

def singlePairValue513 : Sparse (Fin 909) := [(1, (10 / 27)), (2, (-5 / 54)), (3, (-10 / 27)), (4, (-10 / 27)), (12, (-5 / 54)), (31, (5 / 9))]

def singlePairValue514 : Sparse (Fin 909) := [(0, (31 / 864)), (1, (-5 / 216)), (2, (5 / 288)), (3, (5 / 54)), (4, (5 / 54)), (31, (-5 / 18))]

def singlePairValue516 : Sparse (Fin 909) := [(0, (17 / 432)), (1, (-5 / 144)), (2, (5 / 216)), (31, (5 / 9))]

def singlePairValue517 : Sparse (Fin 909) := [(0, (17 / 288)), (1, (25 / 216)), (2, (-5 / 72)), (5, (-5 / 216)), (6, (5 / 864)), (8, (-5 / 27)), (27, (5 / 72)), (30, (5 / 18))]

def singlePairValue519 : Sparse (Fin 909) := [(0, (1 / 864)), (1, (245 / 864)), (2, (-25 / 432)), (3, (-10 / 27)), (4, (-5 / 18)), (26, (-5 / 54)), (31, (5 / 18))]

def singlePairValue520 : Sparse (Fin 909) := [(0, (47 / 864)), (1, (115 / 432)), (2, (-55 / 864)), (3, (-5 / 54)), (4, (-5 / 27))]

def singlePairValue521 : Sparse (Fin 909) := [(0, (11 / 144)), (1, (-5 / 72)), (2, (5 / 144))]

def singlePairValue522 : Sparse (Fin 909) := [(0, (5 / 288)), (1, (5 / 864)), (2, (-5 / 216)), (3, (5 / 27)), (26, (5 / 54))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue523 : Sparse (Fin 909) := [(0, (49 / 864)), (1, (-25 / 432)), (2, (-5 / 864)), (3, (5 / 54)), (4, (5 / 27))]

def singlePairValue526 : Sparse (Fin 909) := [(0, (67 / 864)), (1, (-25 / 288)), (4, (5 / 54))]

def singlePairValue527 : Sparse (Fin 909) := [(0, (1 / 18)), (1, (5 / 18))]

def singlePairValue528 : Sparse (Fin 909) := [(0, (23 / 432)), (1, (-5 / 144)), (4, (-5 / 27))]

def singlePairValue530 : Sparse (Fin 909) := [(0, (7 / 144)), (1, (-5 / 48)), (4, (5 / 9))]

def singlePairValue531 : Sparse (Fin 909) := [(0, (79 / 432)), (1, (35 / 144)), (12, (-5 / 54))]

def singlePairValue533 : Sparse (Fin 909) := [(0, (47 / 432)), (1, (35 / 144)), (4, (-5 / 27))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue72 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-35 / 432)), (2, (-5 / 144)), (6, (5 / 432)), (9, (-5 / 108)), (52, (-5 / 27)), (69, (-5 / 27))]

def singlePairValue73 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (5 / 144)), (2, (25 / 144)), (5, (-5 / 108)), (6, (5 / 432)), (9, (-5 / 108)), (35, (-5 / 27)), (60, (-5 / 27)), (257, (-5 / 27))]

def singlePairValue74 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-55 / 864)), (2, (-35 / 864)), (5, (-5 / 216)), (6, (-5 / 432)), (7, (5 / 54)), (9, (5 / 108)), (35, (5 / 54)), (54, (-5 / 18)), (259, (-5 / 18)), (260, (-5 / 18))]

def singlePairValue75 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-25 / 432)), (2, (-5 / 432)), (5, (-5 / 108)), (6, (5 / 432)), (9, (-5 / 108)), (259, (5 / 9))]

def singlePairValue76 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 72)), (2, (-25 / 432)), (5, (-5 / 108)), (6, (5 / 432)), (9, (-5 / 108)), (260, (5 / 9))]

def singlePairValue77 : Sparse (Fin 909) := [(0, (41 / 864)), (1, (25 / 864)), (2, (55 / 864)), (3, (-5 / 54)), (5, (5 / 216)), (6, (5 / 864)), (7, (-5 / 27)), (8, (-5 / 54)), (11, (-5 / 54)), (26, (-5 / 54)), (35, (-5 / 18)), (52, (-5 / 54)), (228, (5 / 18))]

def singlePairValue78 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (5 / 144)), (2, (-25 / 432)), (5, (-5 / 216)), (6, (-25 / 432)), (11, (5 / 54)), (35, (5 / 54))]

def singlePairValue79 : Sparse (Fin 909) := [(0, (49 / 864)), (1, (-35 / 216)), (2, (-55 / 432)), (3, (-5 / 27)), (5, (5 / 54)), (6, (5 / 864)), (7, (-5 / 54)), (8, (-5 / 27)), (35, (-5 / 27)), (52, (-10 / 27))]

def singlePairValue80 : Sparse (Fin 909) := [(0, (13 / 288)), (1, (5 / 144)), (2, (-5 / 108)), (5, (-5 / 108)), (6, (-5 / 96)), (52, (5 / 54))]

def singlePairValue81 : Sparse (Fin 909) := [(0, (13 / 288)), (1, (25 / 864)), (2, (5 / 216)), (5, (5 / 24)), (7, (5 / 54)), (8, (5 / 54)), (35, (5 / 54))]

def singlePairValue83 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (5 / 144)), (2, (-5 / 108)), (5, (-5 / 54)), (6, (5 / 216)), (11, (5 / 54)), (26, (5 / 54)), (35, (5 / 27))]

def singlePairValue87 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (25 / 288)), (2, (5 / 288)), (5, (-5 / 108)), (6, (-5 / 216)), (13, (5 / 54)), (35, (5 / 27)), (52, (5 / 27)), (60, (5 / 27)), (128, (5 / 54))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue88 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (5 / 72)), (2, (5 / 216)), (5, (5 / 54)), (6, (25 / 216)), (128, (-5 / 27))]

def singlePairValue89 : Sparse (Fin 909) := [(0, (31 / 864)), (1, (-5 / 216)), (2, (25 / 864)), (3, (5 / 54)), (5, (-5 / 108)), (6, (5 / 432)), (7, (5 / 54)), (11, (5 / 54)), (26, (5 / 54)), (35, (5 / 27)), (228, (-5 / 18))]

def singlePairValue90 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 216)), (2, (-5 / 216)), (6, (-5 / 144)), (11, (-5 / 27)), (35, (-5 / 27))]

def singlePairValue91 : Sparse (Fin 909) := [(0, (37 / 864)), (1, (-5 / 216)), (2, (-55 / 432)), (3, (-5 / 27)), (5, (10 / 27)), (6, (-55 / 864)), (7, (-5 / 54)), (8, (-5 / 27)), (35, (-5 / 27)), (52, (-10 / 27))]

def singlePairValue92 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (-35 / 864)), (2, (-5 / 108)), (5, (-25 / 216)), (6, (25 / 864)), (7, (5 / 54)), (35, (5 / 54))]

def singlePairValue93 : Sparse (Fin 909) := [(0, (17 / 432)), (1, (5 / 48)), (2, (5 / 54)), (5, (-5 / 36)), (6, (5 / 216)), (8, (5 / 54)), (52, (5 / 54))]

def singlePairValue94 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (-5 / 108)), (2, (-5 / 72)), (5, (5 / 108)), (6, (-25 / 432))]

def singlePairValue95 : Sparse (Fin 909) := [(0, (1 / 32)), (1, (5 / 216)), (2, (35 / 432)), (3, (5 / 27)), (5, (-5 / 54)), (6, (5 / 288)), (7, (5 / 54)), (35, (5 / 27)), (52, (5 / 27))]

def singlePairValue96 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (-5 / 216)), (2, (-5 / 108)), (5, (5 / 108)), (6, (-5 / 108)), (52, (-5 / 27))]

def singlePairValue97 : Sparse (Fin 909) := [(0, (11 / 432)), (2, (-5 / 108)), (6, (-5 / 144)), (35, (-5 / 27)), (52, (-5 / 27)), (60, (-5 / 27))]

def singlePairValue98 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-35 / 432)), (2, (-5 / 108)), (5, (5 / 27)), (7, (-5 / 27)), (35, (-5 / 27))]

def singlePairValue99 : Sparse (Fin 909) := [(0, (1 / 24)), (1, (5 / 216)), (5, (25 / 108)), (8, (-5 / 27))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue120 : Sparse (Fin 909) := [(0, (7 / 288)), (1, (-5 / 216)), (2, (-5 / 48)), (5, (5 / 36)), (6, (-5 / 432)), (7, (-5 / 27)), (8, (-5 / 27)), (9, (-5 / 54)), (58, (5 / 864)), (69, (-5 / 54)), (71, (-10 / 27))]

def singlePairValue122 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-25 / 864)), (2, (5 / 72)), (3, (5 / 54)), (5, (-5 / 108)), (6, (5 / 216)), (7, (5 / 54)), (9, (5 / 216)), (35, (5 / 27)), (52, (5 / 27)), (58, (-5 / 864)), (69, (5 / 54)), (495, (5 / 54))]

def singlePairValue123 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 72)), (2, (-5 / 108)), (3, (5 / 54)), (6, (-5 / 432)), (7, (5 / 27)), (9, (5 / 108)), (26, (5 / 54)), (35, (10 / 27)), (67, (5 / 27)), (70, (5 / 54)), (257, (5 / 54))]

def singlePairValue124 : Sparse (Fin 909) := [(0, (1 / 32)), (1, (-5 / 96)), (2, (5 / 216)), (5, (-5 / 54)), (6, (-5 / 432)), (7, (5 / 27)), (8, (5 / 27)), (9, (5 / 108)), (69, (5 / 54)), (71, (5 / 54))]

def singlePairValue125 : Sparse (Fin 909) := [(0, (1 / 54)), (1, (35 / 216)), (2, (5 / 288)), (3, (-5 / 18)), (5, (-5 / 108)), (9, (-5 / 54)), (35, (-5 / 27)), (58, (5 / 864)), (69, (-5 / 18)), (70, (-5 / 27))]

def singlePairValue126 : Sparse (Fin 909) := [(0, (1 / 54)), (1, (55 / 432)), (2, (-5 / 432)), (5, (5 / 54)), (6, (5 / 288)), (7, (5 / 54)), (58, (-5 / 864)), (69, (5 / 54))]

def singlePairValue127 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (5 / 54)), (3, (5 / 54)), (5, (-5 / 216)), (6, (-5 / 432)), (9, (5 / 108)), (35, (5 / 54)), (69, (5 / 54)), (70, (5 / 54))]

def singlePairValue128 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (5 / 216)), (2, (-5 / 432)), (5, (-5 / 108)), (6, (-5 / 432)), (9, (5 / 108)), (71, (5 / 27))]

def singlePairValue129 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (5 / 48)), (2, (5 / 432)), (5, (-5 / 54)), (6, (-5 / 216)), (9, (5 / 108)), (58, (5 / 432))]

def singlePairValue130 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-5 / 96)), (2, (5 / 864)), (3, (5 / 54)), (5, (-5 / 216)), (6, (-5 / 432)), (7, (5 / 27)), (8, (5 / 54)), (9, (5 / 108)), (35, (5 / 54)), (81, (-5 / 18)), (256, (-5 / 18))]

def singlePairValue131 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (5 / 48)), (2, (-5 / 216)), (5, (-5 / 108)), (6, (5 / 432)), (7, (-5 / 27)), (9, (-5 / 108)), (35, (-5 / 27)), (70, (-5 / 27))]

def singlePairValue132 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (-5 / 72)), (2, (5 / 432)), (6, (5 / 432)), (8, (-5 / 27)), (9, (-5 / 108)), (71, (-5 / 27))]

def singlePairValue133 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (5 / 48)), (2, (5 / 432)), (6, (5 / 432)), (7, (-5 / 27)), (9, (-5 / 108)), (69, (-5 / 27))]

def singlePairValue134 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 72)), (2, (-25 / 432)), (5, (-5 / 108)), (6, (5 / 432)), (9, (-5 / 108)), (35, (-5 / 27)), (67, (-5 / 27)), (257, (-5 / 27))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue139 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-5 / 144)), (2, (5 / 144)), (5, (5 / 54)), (8, (5 / 54)), (35, (5 / 27)), (67, (5 / 54))]

def singlePairValue140 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-5 / 108)), (5, (-5 / 54)), (6, (25 / 216))]

def singlePairValue141 : Sparse (Fin 909) := [(0, (23 / 864)), (1, (-25 / 432)), (2, (-205 / 864)), (3, (-5 / 18)), (5, (10 / 27)), (6, (-5 / 144)), (7, (-5 / 9)), (8, (-5 / 9)), (35, (-5 / 27))]

def singlePairValue142 : Sparse (Fin 909) := [(0, (1 / 32)), (1, (-5 / 96)), (2, (5 / 96)), (3, (5 / 54)), (5, (-25 / 216)), (6, (5 / 288)), (7, (5 / 27)), (8, (5 / 54)), (35, (5 / 54))]

def singlePairValue143 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-35 / 432)), (2, (-5 / 108)), (5, (5 / 108)), (6, (-5 / 108)), (35, (-5 / 27))]

def singlePairValue144 : Sparse (Fin 909) := [(0, (19 / 864)), (1, (25 / 432)), (2, (5 / 72)), (5, (-5 / 36)), (6, (5 / 288)), (7, (5 / 54)), (8, (5 / 27))]

def singlePairValue145 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-5 / 108)), (2, (25 / 432)), (3, (5 / 27)), (5, (-5 / 72)), (6, (5 / 432)), (7, (5 / 27)), (26, (5 / 54)), (35, (5 / 18)), (52, (5 / 54)), (67, (5 / 54))]

def singlePairValue146 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (-5 / 54)), (2, (-5 / 72)), (5, (5 / 54)), (6, (-5 / 108))]

def singlePairValue147 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-25 / 432)), (2, (-5 / 216)), (5, (5 / 108)), (6, (-5 / 144)), (35, (-5 / 27)), (52, (-5 / 27))]

def singlePairValue148 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-25 / 432)), (2, (-5 / 216)), (5, (5 / 36)), (7, (-5 / 27)), (35, (-5 / 27)), (67, (-5 / 27))]

def singlePairValue149 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (-5 / 72)), (5, (5 / 27)), (7, (-5 / 27)), (8, (-5 / 27))]

def singlePairValue150 : Sparse (Fin 909) := [(0, (7 / 288)), (1, (-35 / 432)), (2, (-5 / 216)), (3, (5 / 27)), (4, (5 / 54)), (5, (5 / 72)), (6, (-5 / 288)), (7, (5 / 54)), (26, (5 / 27)), (35, (5 / 27)), (67, (5 / 54)), (81, (-5 / 18))]

def singlePairValue151 : Sparse (Fin 909) := [(0, (1 / 54)), (1, (5 / 54)), (2, (-35 / 864)), (3, (5 / 18)), (5, (5 / 108)), (6, (-5 / 288)), (7, (5 / 18)), (35, (5 / 27))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue152 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (55 / 432)), (2, (5 / 144)), (3, (-5 / 27)), (5, (-5 / 108)), (6, (5 / 432)), (7, (-5 / 27)), (35, (-5 / 27))]

def singlePairValue153 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-5 / 144)), (2, (5 / 108)), (5, (-5 / 108)), (6, (5 / 432)), (81, (5 / 9))]

def singlePairValue154 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (5 / 48)), (2, (-5 / 72)), (6, (-5 / 144)), (35, (5 / 9))]

def singlePairValue155 : Sparse (Fin 909) := [(0, (37 / 864)), (1, (-35 / 432)), (6, (-5 / 288)), (7, (5 / 54)), (8, (5 / 27))]

def singlePairValue156 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (5 / 36)), (6, (5 / 432)), (7, (-5 / 27))]

def singlePairValue157 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (-5 / 54)), (6, (5 / 432)), (8, (-5 / 27))]

def singlePairValue158 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (5 / 36)), (5, (-5 / 36)), (6, (-5 / 144))]

def singlePairValue159 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 72)), (2, (-5 / 72)), (5, (5 / 36)), (67, (5 / 9))]

def singlePairValue160 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (5 / 18)), (5, (5 / 36)), (7, (5 / 9))]

def singlePairValue161 : Sparse (Fin 909) := [(0, (1 / 24)), (1, (-5 / 72)), (5, (5 / 36)), (8, (5 / 9))]

def singlePairValue162 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (5 / 18)), (5, (5 / 9)), (6, (5 / 36))]

def singlePairValue163 : Sparse (Fin 909) := [(0, (1 / 54)), (1, (5 / 144)), (3, (-5 / 18)), (5, (5 / 54)), (6, (-5 / 144)), (7, (-10 / 27)), (9, (5 / 216)), (13, (-5 / 54)), (26, (-10 / 27)), (34, (-5 / 54)), (35, (-20 / 27)), (67, (-5 / 27)), (68, (-5 / 72)), (69, (-5 / 54)), (70, (-5 / 18)), (124, (5 / 18)), (196, (5 / 18)), (197, (5 / 9)), (257, (-5 / 54)), (266, (5 / 18))]

def singlePairValue164 : Sparse (Fin 909) := [(0, (7 / 288)), (1, (-5 / 864)), (2, (5 / 864)), (3, (-25 / 54)), (5, (5 / 54)), (6, (-5 / 288)), (7, (-10 / 27)), (9, (5 / 216)), (13, (-5 / 18)), (26, (-5 / 27)), (34, (-5 / 54)), (35, (-5 / 9)), (52, (-5 / 27)), (60, (-5 / 54)), (64, (5 / 18)), (67, (-5 / 54)), (68, (-5 / 72)), (69, (-5 / 54)), (70, (-5 / 27)), (125, (5 / 9)), (126, (5 / 18)), (197, (5 / 18)), (257, (-5 / 54)), (260, (5 / 18)), (268, (5 / 18))]

def singlePairValue165 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 96)), (2, (-5 / 288)), (3, (-5 / 54)), (5, (5 / 108)), (7, (-5 / 54)), (13, (-5 / 54)), (23, (5 / 9)), (27, (-5 / 72)), (35, (-5 / 54)), (54, (5 / 9)), (55, (5 / 18)), (63, (5 / 18)), (65, (5 / 18)), (68, (-5 / 36)), (124, (5 / 18)), (125, (5 / 6)), (196, (5 / 9)), (197, (5 / 18)), (264, (5 / 9)), (266, (5 / 18))]

def singlePairValue166 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 288)), (2, (-5 / 288)), (3, (-5 / 27)), (5, (5 / 54)), (6, (-5 / 432)), (7, (-5 / 27)), (9, (5 / 216)), (13, (-10 / 27)), (32, (-5 / 54)), (35, (-10 / 27)), (52, (-5 / 27)), (54, (5 / 9)), (60, (-5 / 27)), (62, (5 / 9)), (68, (-5 / 72)), (69, (-5 / 54)), (70, (-5 / 54)), (125, (5 / 9)), (257, (-5 / 54)), (260, (5 / 9)), (264, (5 / 6))]

def singlePairValue167 : Sparse (Fin 909) := [(0, (7 / 288)), (1, (5 / 432)), (2, (5 / 288)), (5, (5 / 216)), (23, (5 / 18)), (24, (5 / 18)), (27, (-5 / 36)), (51, (5 / 18)), (54, (5 / 18)), (55, (5 / 18)), (56, (5 / 18)), (61, (5 / 18)), (68, (-5 / 36)), (124, (5 / 18)), (125, (5 / 18)), (126, (5 / 18)), (196, (5 / 18)), (197, (5 / 9)), (263, (-5 / 9)), (266, (5 / 18)), (268, (5 / 18))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SinglePriority
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue420 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (5 / 72)), (2, (-5 / 144)), (3, (5 / 9))]

def singlePairValue496 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (25 / 216)), (2, (5 / 432)), (3, (-5 / 27)), (12, (-5 / 27))]

def singlePairValue505 : Sparse (Fin 909) := [(0, (5 / 108)), (1, (5 / 36)), (12, (-5 / 27))]

end MUB6.Certificate.MixedSemantics

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

def sourceA0 : Charge := ![-2, 0, 0, 0, 0, 2]

def sourceA1 : Charge := ![-2, 0, 0, 0, 0, 2]

def sourceA2 : Charge := ![-2, 0, 0, 0, 0, 2]

def sourceA10 : Charge := ![1, 0, 0, 0, -1, 0]

def sourceA11 : Charge := ![-2, 0, 0, 0, 0, 2]

def sourceA12 : Charge := ![-2, 0, 0, 0, 1, 1]

def sourceA13 : Charge := ![-2, 0, 0, 0, 1, 1]

def sourceA14 : Charge := ![-2, 0, 0, 0, 1, 1]

def sourceA15 : Charge := ![-2, 0, 0, 0, 1, 1]

def sourceA16 : Charge := ![-2, 0, 0, 0, 1, 1]

def sourceA17 : Charge := ![-2, 0, 0, 0, 1, 1]

def sourceA18 : Charge := ![-2, 0, 0, 0, 1, 1]

def sourceA19 : Charge := ![-2, 0, 0, 0, 1, 1]

def sourceA20 : Charge := ![1, -1, 0, 1, -1, 0]

def sourceA21 : Charge := ![-2, 0, 0, 0, 1, 1]

def sourceA22 : Charge := ![-2, 0, 0, 0, 1, 1]

def sourceA23 : Charge := ![1, 0, 0, -1, 0, 0]

def sourceA24 : Charge := ![-2, 0, 0, 0, 1, 1]

def sourceA25 : Charge := ![-2, 0, 0, 0, 1, 1]

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

def sourceA100 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA101 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA102 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA103 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA106 : Charge := ![1, -1, 0, 1, 1, -2]

def sourceA107 : Charge := ![1, -1, 0, 1, 1, -2]

def sourceA108 : Charge := ![1, -1, 0, 1, 1, -2]

def sourceA109 : Charge := ![1, -1, 0, 1, 1, -2]

def sourceA110 : Charge := ![1, -1, 0, 1, 1, -2]

def sourceA111 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA112 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA113 : Charge := ![1, 0, 0, 0, 1, -2]

def sourceA114 : Charge := ![1, 0, 0, 0, 1, -2]

def sourceA115 : Charge := ![1, 0, 0, 0, 1, -2]

def sourceA116 : Charge := ![1, 0, 0, 0, 1, -2]

def sourceA117 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA118 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA119 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA120 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA121 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA122 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA123 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA124 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA125 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA126 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA127 : Charge := ![-3, 0, 0, 0, 0, 3]

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

def sourceA1000 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1001 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1003 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1004 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1005 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1006 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1008 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1012 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1013 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1015 : Charge := ![0, 2, 0, 1, -2, -1]

def sourceA1016 : Charge := ![0, 2, 0, 1, -2, -1]

def sourceA1017 : Charge := ![0, 2, 0, 1, -2, -1]

def sourceA1018 : Charge := ![0, 2, 0, 1, -2, -1]

def sourceA1020 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1021 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1022 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1023 : Charge := ![0, 2, 0, 1, -1, -2]

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

def sourceA1024 : Charge := ![0, 2, 0, 1, -1, -2]

def sourceA1025 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1026 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1027 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1029 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1030 : Charge := ![1, -1, 1, 1, -1, -1]

def sourceA1031 : Charge := ![1, -1, 1, 1, -1, -1]

def sourceA1032 : Charge := ![1, -1, 1, 1, -1, -1]

def sourceA1033 : Charge := ![1, -1, 1, 1, -1, -1]

def sourceA1036 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1039 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1040 : Charge := ![1, 0, -1, 2, -1, -1]

def sourceA1041 : Charge := ![1, 0, -1, 2, -1, -1]

def sourceA1043 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1044 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1045 : Charge := ![1, 0, 0, 1, -1, -1]

def sourceA1048 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1049 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1050 : Charge := ![1, 0, 1, 1, -1, -2]

def sourceA1051 : Charge := ![1, 0, 1, 1, -1, -2]

def sourceA1052 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1053 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1054 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1055 : Charge := ![-2, -1, 0, 0, 1, 2]

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

def sourceA1056 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1057 : Charge := ![1, 0, 1, 0, -2, 0]

def sourceA1058 : Charge := ![1, 0, 1, 0, -2, 0]

def sourceA1059 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1060 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1061 : Charge := ![1, 0, 1, -1, 0, -1]

def sourceA1062 : Charge := ![1, 0, 1, -1, 0, -1]

def sourceA1063 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1064 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1065 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1066 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1067 : Charge := ![1, 0, 1, -1, -1, 0]

def sourceA1068 : Charge := ![1, 0, 1, -1, -1, 0]

def sourceA1069 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1070 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1071 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1072 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1073 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1074 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1075 : Charge := ![1, 0, 0, -1, 1, -1]

def sourceA1076 : Charge := ![1, 0, 0, -1, 1, -1]

def sourceA1077 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1078 : Charge := ![1, 0, 0, -1, 0, 0]

def sourceA1079 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1080 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1081 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1082 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1083 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1084 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1085 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1086 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1087 : Charge := ![-2, -1, 0, 0, 1, 2]

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

def sourceA1088 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1089 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1090 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1091 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1092 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1093 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1094 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1095 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1096 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1097 : Charge := ![-2, -1, 0, 1, 1, 1]

def sourceA1098 : Charge := ![-2, -1, 0, 1, 1, 1]

def sourceA1099 : Charge := ![-2, -1, 0, 1, 1, 1]

def sourceA1100 : Charge := ![0, 1, 1, -1, -1, 0]

def sourceA1101 : Charge := ![-2, -1, 0, 1, 1, 1]

def sourceA1102 : Charge := ![-2, -1, 0, 1, 1, 1]

def sourceA1103 : Charge := ![-2, -1, 0, 1, 1, 1]

def sourceA1104 : Charge := ![0, 2, 0, -1, -1, 0]

def sourceA1105 : Charge := ![-2, -1, 0, 1, 1, 1]

def sourceA1106 : Charge := ![-2, -1, 0, 1, 1, 1]

def sourceA1107 : Charge := ![-2, -1, 0, 1, 1, 1]

def sourceA1108 : Charge := ![0, 2, 1, -1, -1, -1]

def sourceA1109 : Charge := ![0, 2, 1, -1, -1, -1]

def sourceA1110 : Charge := ![-2, -1, 0, 1, 1, 1]

def sourceA1111 : Charge := ![-2, -1, 0, 1, 1, 1]

def sourceA1112 : Charge := ![-2, -1, 0, 1, 1, 1]

def sourceA1113 : Charge := ![-2, -1, 0, 1, 1, 1]

def sourceA1114 : Charge := ![-2, -1, 0, 1, 1, 1]

def sourceA1116 : Charge := ![-2, -1, 0, 1, 1, 1]

def sourceA1117 : Charge := ![-2, -1, 0, 1, 1, 1]

def sourceA1118 : Charge := ![-2, -1, 0, 1, 1, 1]

def sourceA1119 : Charge := ![-2, -1, 0, 1, 1, 1]

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

def sourceA1120 : Charge := ![1, 0, 1, 0, 0, -2]

def sourceA1121 : Charge := ![1, 0, 1, 0, 0, -2]

def sourceA1122 : Charge := ![-2, -1, 0, 1, 1, 1]

def sourceA1123 : Charge := ![-2, -1, 0, 1, 1, 1]

def sourceA1124 : Charge := ![-2, -1, 0, 1, 1, 1]

def sourceA1125 : Charge := ![-2, -1, 0, 1, 1, 1]

def sourceA1126 : Charge := ![-2, -1, 0, 1, 1, 1]

def sourceA1127 : Charge := ![1, 0, -1, 0, 0, 0]

def sourceA1128 : Charge := ![-2, -1, 0, 1, 1, 1]

def sourceA1129 : Charge := ![-2, -1, 0, 1, 1, 1]

def sourceA1130 : Charge := ![-2, -1, 0, 1, 1, 1]

def sourceA1131 : Charge := ![-2, -1, 0, 1, 1, 1]

def sourceA1132 : Charge := ![-2, -1, 0, 1, 1, 1]

def sourceA1133 : Charge := ![-2, -1, 0, 1, 1, 1]

def sourceA1134 : Charge := ![-2, -1, 0, 1, 1, 1]

def sourceA1135 : Charge := ![-2, -1, 0, 1, 1, 1]

def sourceA1136 : Charge := ![0, 2, -1, 0, 0, -1]

def sourceA1137 : Charge := ![-2, -1, 0, 1, 1, 1]

def sourceA1138 : Charge := ![-2, -1, 0, 1, 1, 1]

def sourceA1139 : Charge := ![-2, -1, 0, 1, 1, 1]

def sourceA1140 : Charge := ![-1, -1, -1, 1, 1, 1]

def sourceA1141 : Charge := ![-1, -1, -1, 1, 1, 1]

def sourceA1142 : Charge := ![-4, 0, 0, 0, 0, 4]

def sourceA1143 : Charge := ![1, 0, 0, 0, 2, -3]

def sourceA1145 : Charge := ![1, 0, 0, 0, 2, -3]

def sourceA1147 : Charge := ![-4, 0, 0, 0, 0, 4]

def sourceA1148 : Charge := ![1, 0, 0, 1, 1, -3]

def sourceA1150 : Charge := ![-4, 0, 0, 0, 0, 4]

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

def sourceA1152 : Charge := ![-4, 0, 0, 0, 0, 4]

def sourceA1153 : Charge := ![2, -1, 0, 0, 1, -2]

def sourceA1154 : Charge := ![2, -1, 0, 0, 1, -2]

def sourceA1155 : Charge := ![-4, 0, 0, 0, 0, 4]

def sourceA1156 : Charge := ![-4, 0, 0, 0, 0, 4]

def sourceA1157 : Charge := ![-4, 0, 0, 0, 0, 4]

def sourceA1158 : Charge := ![-4, 0, 0, 0, 0, 4]

def sourceA1159 : Charge := ![-4, 0, 0, 0, 0, 4]

def sourceA1160 : Charge := ![-4, 0, 0, 0, 0, 4]

def sourceA1161 : Charge := ![2, 0, 0, 0, 0, -2]

def sourceA1162 : Charge := ![2, 0, 0, 0, 0, -2]

def sourceA1163 : Charge := ![2, 0, 0, 0, 0, -2]

def sourceA1164 : Charge := ![-4, 0, 0, 0, 0, 4]

def sourceA1165 : Charge := ![-4, 0, 0, 0, 0, 4]

def sourceA1166 : Charge := ![-4, 0, 0, 0, 0, 4]

def sourceA1167 : Charge := ![-4, 0, 0, 0, 0, 4]

def sourceA1168 : Charge := ![-4, 0, 0, 0, 0, 4]

def sourceA1169 : Charge := ![-4, 0, 0, 0, 0, 4]

def sourceA1170 : Charge := ![-4, 0, 0, 0, 0, 4]

def sourceA1171 : Charge := ![-4, 0, 0, 0, 0, 4]

def sourceA1172 : Charge := ![-4, 0, 0, 0, 0, 4]

def sourceA1173 : Charge := ![-4, 0, 0, 0, 0, 4]

def sourceA1177 : Charge := ![2, 0, 0, 0, -1, -1]

def sourceA1178 : Charge := ![-4, 0, 0, 0, 0, 4]

def sourceA1179 : Charge := ![-4, 0, 0, 0, 0, 4]

def sourceA1180 : Charge := ![-4, 0, 0, 0, 0, 4]

def sourceA1182 : Charge := ![-4, 0, 0, 0, 0, 4]

def sourceA1183 : Charge := ![-4, 0, 0, 0, 0, 4]

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

def sourceA1184 : Charge := ![-4, 0, 0, 0, 0, 4]

def sourceA1186 : Charge := ![-4, 0, 0, 0, 0, 4]

def sourceA1189 : Charge := ![-4, 0, 0, 0, 0, 4]

def sourceA1190 : Charge := ![-4, 0, 0, 0, 0, 4]

def sourceA1191 : Charge := ![-4, 0, 0, 0, 0, 4]

def sourceA1192 : Charge := ![1, 0, 0, 0, 0, -1]

def sourceA1193 : Charge := ![-4, 0, 0, 0, 0, 4]

def sourceA1194 : Charge := ![-4, 0, 0, 0, 0, 4]

def sourceA1195 : Charge := ![-4, 0, 0, 0, 0, 4]

def sourceA1197 : Charge := ![-4, 0, 0, 0, 0, 4]

def sourceA1198 : Charge := ![-4, 0, 0, 0, 0, 4]

def sourceA1200 : Charge := ![-4, 0, 0, 0, 0, 4]

def sourceA1201 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1202 : Charge := ![1, 0, 0, 0, 2, -3]

def sourceA1203 : Charge := ![1, 0, 0, 0, 2, -3]

def sourceA1204 : Charge := ![1, 0, 0, 0, 2, -3]

def sourceA1205 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1206 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1207 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1208 : Charge := ![1, 0, 0, 1, 1, -3]

def sourceA1210 : Charge := ![1, 0, 0, 1, 1, -3]

def sourceA1211 : Charge := ![1, 0, 0, 1, 1, -3]

def sourceA1212 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1213 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1214 : Charge := ![1, 0, 0, 2, -1, -2]

def sourceA1215 : Charge := ![1, 0, 0, 2, -1, -2]

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

def sourceA1216 : Charge := ![1, 0, 0, 2, -1, -2]

def sourceA1217 : Charge := ![1, 0, 0, 2, -1, -2]

def sourceA1218 : Charge := ![1, 0, 0, 2, -1, -2]

def sourceA1220 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1221 : Charge := ![1, 0, 0, 2, 0, -3]

def sourceA1224 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1225 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1226 : Charge := ![1, 0, 1, 1, -1, -2]

def sourceA1228 : Charge := ![1, 0, 1, 1, -1, -2]

def sourceA1229 : Charge := ![1, 0, 1, 1, -1, -2]

def sourceA1231 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1232 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1233 : Charge := ![1, 0, 1, 1, 0, -3]

def sourceA1235 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1237 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1238 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1239 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1240 : Charge := ![2, -1, 0, 0, 1, -2]

def sourceA1241 : Charge := ![2, -1, 0, 0, 1, -2]

def sourceA1242 : Charge := ![2, -1, 0, 0, 1, -2]

def sourceA1243 : Charge := ![2, -1, 0, 0, 1, -2]

def sourceA1244 : Charge := ![2, -1, 0, 0, 1, -2]

def sourceA1246 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1247 : Charge := ![-4, 0, 0, 0, 1, 3]

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

def sourceA1248 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1249 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1250 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1251 : Charge := ![2, -1, 0, 1, -1, -1]

def sourceA1252 : Charge := ![2, -1, 0, 1, -1, -1]

def sourceA1253 : Charge := ![2, -1, 0, 1, -1, -1]

def sourceA1254 : Charge := ![2, -1, 0, 1, -1, -1]

def sourceA1255 : Charge := ![2, -1, 0, 1, -1, -1]

def sourceA1256 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1257 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1258 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1259 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1260 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1261 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1262 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1263 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1264 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1265 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1266 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1267 : Charge := ![2, 0, 0, 0, -1, -1]

def sourceA1268 : Charge := ![2, 0, 0, 0, -1, -1]

def sourceA1269 : Charge := ![2, 0, 0, 0, -1, -1]

def sourceA1270 : Charge := ![2, 0, 0, 0, -1, -1]

def sourceA1271 : Charge := ![2, 0, 0, 0, -1, -1]

def sourceA1272 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1273 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1274 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1275 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1276 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1277 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1278 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1279 : Charge := ![-4, 0, 0, 0, 1, 3]

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

def sourceA128 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA129 : Charge := ![1, 0, 0, 0, 2, -3]

def sourceA130 : Charge := ![1, 0, 0, 0, 2, -3]

def sourceA131 : Charge := ![1, 0, 0, 0, 2, -3]

def sourceA132 : Charge := ![1, 0, 0, 0, 2, -3]

def sourceA133 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA134 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA135 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA136 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA137 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA138 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA139 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA140 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA141 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA142 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA143 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA144 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA145 : Charge := ![1, 0, 0, 1, 1, -3]

def sourceA146 : Charge := ![1, 0, 0, 1, 1, -3]

def sourceA147 : Charge := ![1, 0, 0, 1, 1, -3]

def sourceA148 : Charge := ![1, 0, 0, 1, 1, -3]

def sourceA149 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA150 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA151 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA152 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA153 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA154 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA155 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA156 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA157 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA158 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA159 : Charge := ![1, 1, 0, 0, -1, -1]

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

def sourceA1281 : Charge := ![2, 0, 0, 0, -2, 0]

def sourceA1282 : Charge := ![2, 0, 0, 0, -2, 0]

def sourceA1283 : Charge := ![2, 0, 0, 0, -2, 0]

def sourceA1284 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1285 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1286 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1287 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1288 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1289 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1290 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1291 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1292 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1295 : Charge := ![2, 0, 0, -1, 0, -1]

def sourceA1296 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1297 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1298 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1299 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1300 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1301 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1302 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1303 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1304 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1307 : Charge := ![2, 0, 0, -1, -1, 0]

def sourceA1308 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1309 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1310 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1311 : Charge := ![-4, 0, 0, 0, 1, 3]

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

def sourceA1312 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1313 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1315 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1316 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1317 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1318 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1319 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1320 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1322 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1323 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1324 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1325 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1326 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1327 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1328 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1329 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1330 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1331 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1332 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1333 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1334 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1335 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1336 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1337 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1338 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1339 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1340 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1341 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1342 : Charge := ![-4, 0, 0, 0, 1, 3]

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

def sourceA1344 : Charge := ![1, 1, 0, 0, 0, -2]

def sourceA1345 : Charge := ![1, 1, 0, 0, 0, -2]

def sourceA1347 : Charge := ![1, 1, 0, 0, 0, -2]

def sourceA1348 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1349 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1350 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1351 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1352 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1353 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1354 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1355 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1356 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1357 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1360 : Charge := ![1, 1, 0, 0, -1, -1]

def sourceA1361 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1362 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1363 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1364 : Charge := ![1, 1, 0, 0, -2, 0]

def sourceA1366 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1367 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1370 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1373 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1375 : Charge := ![-4, 0, 0, 0, 1, 3]

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

def sourceA1376 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1377 : Charge := ![1, 1, 0, -1, -1, 0]

def sourceA1378 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1379 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1380 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1381 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1385 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1386 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1387 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1388 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1389 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1390 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1391 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1392 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1393 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1396 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1399 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1400 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1401 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1403 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1405 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1406 : Charge := ![-4, 0, 0, 0, 1, 3]

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

def sourceA1408 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1410 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1411 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1412 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1413 : Charge := ![0, 2, 0, 0, -1, -1]

def sourceA1415 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1417 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1418 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1419 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1421 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1422 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1423 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1424 : Charge := ![0, 1, 1, 0, -1, -1]

def sourceA1425 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1426 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1427 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1429 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1430 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1431 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1433 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1435 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1437 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1438 : Charge := ![0, 0, 0, 0, 1, -1]

def sourceA1439 : Charge := ![-4, 0, 0, 0, 1, 3]

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

def sourceA1440 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1441 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1443 : Charge := ![1, 0, 0, 2, -2, -1]

def sourceA1444 : Charge := ![1, 0, 0, 2, -2, -1]

def sourceA1445 : Charge := ![1, 0, 0, 2, -2, -1]

def sourceA1448 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1449 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1450 : Charge := ![1, 0, 1, 1, -2, -1]

def sourceA1452 : Charge := ![1, 0, 1, 1, -2, -1]

def sourceA1453 : Charge := ![1, 0, 1, 1, -2, -1]

def sourceA1455 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1457 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1458 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1459 : Charge := ![2, -1, 0, 0, -2, 1]

def sourceA1460 : Charge := ![2, -1, 0, 0, -2, 1]

def sourceA1461 : Charge := ![2, -1, 0, 0, -2, 1]

def sourceA1462 : Charge := ![2, -1, 0, 0, -2, 1]

def sourceA1463 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1464 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1465 : Charge := ![2, -1, 0, 1, -2, 0]

def sourceA1467 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1468 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1469 : Charge := ![2, -1, 0, 1, -1, -1]

def sourceA1470 : Charge := ![2, -1, 0, 1, -1, -1]

def sourceA1471 : Charge := ![-4, 0, 0, 0, 2, 2]

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

def sourceA1472 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1473 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1474 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1475 : Charge := ![2, 0, 0, 0, -2, 0]

def sourceA1476 : Charge := ![2, 0, 0, 0, -2, 0]

def sourceA1477 : Charge := ![2, 0, 0, 0, -2, 0]

def sourceA1478 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1479 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1480 : Charge := ![2, 0, 0, 0, -1, -1]

def sourceA1481 : Charge := ![2, 0, 0, 0, -1, -1]

def sourceA1482 : Charge := ![2, 0, 0, 0, -1, -1]

def sourceA1483 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1484 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1485 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1486 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1487 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1488 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1489 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1490 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1491 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1495 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1496 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1497 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1499 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1500 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1501 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1503 : Charge := ![-4, 0, 0, 0, 2, 2]

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

def sourceA1504 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1505 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1506 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1507 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1508 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1509 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1510 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1511 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1512 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1513 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1514 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1515 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1516 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1517 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1518 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1522 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1523 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1524 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1525 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1526 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1527 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1528 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1529 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1531 : Charge := ![1, 1, 0, 0, -1, -1]

def sourceA1532 : Charge := ![1, 1, 0, 0, -1, -1]

def sourceA1533 : Charge := ![1, 1, 0, 0, -1, -1]

def sourceA1534 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1535 : Charge := ![-4, 0, 0, 0, 2, 2]

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

def sourceA1537 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1538 : Charge := ![1, 1, 0, -1, 0, -1]

def sourceA1540 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1541 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1542 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1543 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1550 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1551 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1552 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1553 : Charge := ![1, 0, 0, 0, 0, -1]

def sourceA1554 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1556 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1558 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1561 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1562 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1564 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1565 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1566 : Charge := ![0, 1, 1, 0, 0, -2]

def sourceA1567 : Charge := ![-4, 0, 0, 0, 2, 2]

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

def sourceA1568 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1569 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1570 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1571 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1572 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1573 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1574 : Charge := ![0, 1, 0, 0, 0, -1]

def sourceA1575 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1576 : Charge := ![1, 0, 0, -1, 2, -2]

def sourceA1577 : Charge := ![1, 0, 0, -1, 2, -2]

def sourceA1578 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1579 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1580 : Charge := ![1, 0, 1, -1, 1, -2]

def sourceA1581 : Charge := ![1, 0, 1, -1, 1, -2]

def sourceA1582 : Charge := ![1, 0, 1, -1, 1, -2]

def sourceA1583 : Charge := ![1, 0, 1, -1, 1, -2]

def sourceA1584 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1585 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1586 : Charge := ![1, 0, 2, -1, -1, -1]

def sourceA1587 : Charge := ![1, 0, 2, -1, -1, -1]

def sourceA1588 : Charge := ![1, 0, 2, -1, -1, -1]

def sourceA1590 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1591 : Charge := ![1, 0, 2, -1, 0, -2]

def sourceA1592 : Charge := ![1, 0, 2, -1, 0, -2]

def sourceA1594 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1595 : Charge := ![1, 1, 1, -1, -1, -1]

def sourceA1596 : Charge := ![1, 1, 1, -1, -1, -1]

def sourceA1597 : Charge := ![1, 1, 1, -1, -1, -1]

def sourceA1598 : Charge := ![1, 1, 1, -1, -1, -1]

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

def sourceA160 : Charge := ![1, 1, 0, 0, -1, -1]

def sourceA161 : Charge := ![1, 1, 0, 0, -1, -1]

def sourceA162 : Charge := ![1, 1, 0, 0, -1, -1]

def sourceA163 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA164 : Charge := ![1, 0, 0, 0, 0, -1]

def sourceA165 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA166 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA167 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA168 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA169 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA170 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA171 : Charge := ![1, 0, 0, 0, -1, 0]

def sourceA172 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA174 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA176 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA177 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA178 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA179 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA180 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA181 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA182 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA183 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA184 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA186 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA187 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA188 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA189 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA190 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA191 : Charge := ![-3, 0, 0, 0, 1, 2]

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

def sourceA1600 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1601 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1602 : Charge := ![1, 1, 1, -1, 0, -2]

def sourceA1604 : Charge := ![1, 1, 1, -1, 0, -2]

def sourceA1606 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1607 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1608 : Charge := ![2, -1, 0, -1, -1, 1]

def sourceA1609 : Charge := ![2, -1, 0, -1, -1, 1]

def sourceA1610 : Charge := ![2, -1, 0, -1, -1, 1]

def sourceA1611 : Charge := ![2, -1, 0, -1, -1, 1]

def sourceA1612 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1613 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1614 : Charge := ![2, -1, 0, -1, 1, -1]

def sourceA1615 : Charge := ![2, -1, 0, -1, 1, -1]

def sourceA1616 : Charge := ![2, -1, 0, -1, 1, -1]

def sourceA1617 : Charge := ![2, -1, 0, -1, 1, -1]

def sourceA1618 : Charge := ![2, -1, 0, -1, 1, -1]

def sourceA1619 : Charge := ![2, -1, 0, -1, 1, -1]

def sourceA1620 : Charge := ![2, -1, 0, -1, 1, -1]

def sourceA1621 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1622 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1623 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1624 : Charge := ![2, -1, 0, 0, 1, -2]

def sourceA1625 : Charge := ![2, -1, 0, 0, 1, -2]

def sourceA1626 : Charge := ![2, -1, 0, 0, 1, -2]

def sourceA1627 : Charge := ![2, -1, 0, 0, 1, -2]

def sourceA1628 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1629 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1630 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1631 : Charge := ![-4, 0, 0, 1, 1, 2]

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

def sourceA1632 : Charge := ![2, -1, 1, -1, -1, 0]

def sourceA1633 : Charge := ![2, -1, 1, -1, -1, 0]

def sourceA1634 : Charge := ![2, -1, 1, -1, -1, 0]

def sourceA1635 : Charge := ![2, -1, 1, -1, -1, 0]

def sourceA1636 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1637 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1638 : Charge := ![2, -1, 1, -1, 0, -1]

def sourceA1639 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1640 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1641 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1642 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1643 : Charge := ![2, 0, 0, -2, -1, 1]

def sourceA1644 : Charge := ![2, 0, 0, -2, -1, 1]

def sourceA1645 : Charge := ![2, 0, 0, -2, 1, -1]

def sourceA1646 : Charge := ![2, 0, 0, -2, 1, -1]

def sourceA1647 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1648 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1649 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1650 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1651 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1652 : Charge := ![2, 0, 0, -1, -1, 0]

def sourceA1653 : Charge := ![2, 0, 0, -1, -1, 0]

def sourceA1654 : Charge := ![2, 0, 0, -1, -1, 0]

def sourceA1655 : Charge := ![2, 0, 0, -1, -1, 0]

def sourceA1656 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1657 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1658 : Charge := ![2, 0, 0, -1, 0, -1]

def sourceA1659 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1660 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1661 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1662 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1663 : Charge := ![-4, 0, 0, 1, 1, 2]

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

def sourceA1664 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1667 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1668 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1669 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1670 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1671 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1672 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1673 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1674 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1675 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1677 : Charge := ![2, 0, -1, 0, 0, -1]

def sourceA1678 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1679 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1680 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1681 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1682 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1683 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1684 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1686 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1688 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1689 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1690 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1693 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1695 : Charge := ![-4, 0, 0, 1, 1, 2]

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

def sourceA1696 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1697 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1700 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1702 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1703 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1704 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1706 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1707 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1708 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1709 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1710 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1711 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1712 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1713 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1714 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1715 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1716 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1717 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1718 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1719 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1720 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1723 : Charge := ![1, 1, 0, 0, 0, -2]

def sourceA1724 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1725 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1726 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1727 : Charge := ![-4, 0, 0, 1, 1, 2]

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

def sourceA1728 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1729 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1730 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1732 : Charge := ![1, 1, 0, 0, -1, -1]

def sourceA1733 : Charge := ![1, 1, 0, 0, -1, -1]

def sourceA1734 : Charge := ![1, 1, 0, 0, -1, -1]

def sourceA1735 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1737 : Charge := ![1, 1, 0, 0, -2, 0]

def sourceA1738 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1739 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1740 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1741 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1742 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1743 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1744 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1745 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1746 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1747 : Charge := ![1, 1, 0, -1, -1, 0]

def sourceA1748 : Charge := ![1, 1, 0, -1, -1, 0]

def sourceA1749 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1750 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1751 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1752 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1753 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1756 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1759 : Charge := ![-4, 0, 0, 1, 1, 2]

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

def sourceA1761 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1762 : Charge := ![1, 1, -1, 0, -1, 0]

def sourceA1763 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1766 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1769 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1770 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1773 : Charge := ![1, 0, 0, 1, 0, -2]

def sourceA1775 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1776 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1777 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1779 : Charge := ![1, 0, 0, 1, -1, -1]

def sourceA1780 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1781 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1782 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1783 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1784 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1785 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1786 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1787 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1788 : Charge := ![-4, 0, 0, 1, 1, 2]

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

def sourceA1792 : Charge := ![1, 0, 0, -1, -1, 1]

def sourceA1793 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1795 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1796 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1797 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1798 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1800 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1803 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1804 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1807 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1809 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1811 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1812 : Charge := ![0, 1, 1, 0, 0, -2]

def sourceA1813 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1814 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1815 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1816 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1817 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1818 : Charge := ![0, 1, 0, 0, 0, -1]

def sourceA1821 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1822 : Charge := ![1, 0, -1, -1, -1, 2]

def sourceA1823 : Charge := ![1, 0, -1, -1, -1, 2]

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

def sourceA1824 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1825 : Charge := ![1, 1, -1, -1, -1, 1]

def sourceA1826 : Charge := ![1, 1, -1, -1, -1, 1]

def sourceA1827 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1828 : Charge := ![1, 2, -1, -1, -1, 0]

def sourceA1831 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1832 : Charge := ![2, -1, -1, -1, -1, 2]

def sourceA1833 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1834 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1835 : Charge := ![2, -1, -1, -1, 0, 1]

def sourceA1836 : Charge := ![2, -1, -1, -1, 0, 1]

def sourceA1837 : Charge := ![2, -1, -1, -1, 0, 1]

def sourceA1838 : Charge := ![2, -1, -1, -1, 0, 1]

def sourceA1839 : Charge := ![2, -1, -1, -1, 0, 1]

def sourceA1841 : Charge := ![2, 0, -2, -1, -1, 2]

def sourceA1842 : Charge := ![2, 0, -2, -1, 0, 1]

def sourceA1843 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1844 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1845 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1846 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1847 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1848 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1850 : Charge := ![2, 0, -1, -1, -1, 1]

def sourceA1851 : Charge := ![2, 0, -1, -1, -1, 1]

def sourceA1852 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1853 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1854 : Charge := ![2, 0, -1, -1, 0, 0]

def sourceA1855 : Charge := ![-4, 0, 1, 1, 1, 1]

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

def sourceA1856 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1857 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1858 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1859 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1860 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1861 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1863 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1864 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1865 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1867 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1868 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1869 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1870 : Charge := ![1, 1, 0, 0, 0, -2]

def sourceA1871 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1872 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1873 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1874 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1875 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1876 : Charge := ![1, 1, 0, 0, -1, -1]

def sourceA1877 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1878 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1879 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1880 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1881 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1884 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1885 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1886 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1887 : Charge := ![-4, 0, 1, 1, 1, 1]

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

def sourceA1889 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1890 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1891 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1892 : Charge := ![0, 1, 0, 0, 2, -3]

def sourceA1893 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1894 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1895 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1897 : Charge := ![0, 1, 0, 1, 1, -3]

def sourceA1898 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1899 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1900 : Charge := ![0, 1, 0, 2, -1, -2]

def sourceA1901 : Charge := ![0, 1, 0, 2, -1, -2]

def sourceA1902 : Charge := ![0, 1, 0, 2, -1, -2]

def sourceA1903 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1904 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1905 : Charge := ![0, 1, 1, 1, -1, -2]

def sourceA1907 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1908 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1909 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1910 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1911 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1912 : Charge := ![0, 2, 0, 1, -1, -2]

def sourceA1913 : Charge := ![0, 2, 0, 1, -1, -2]

def sourceA1914 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1915 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1916 : Charge := ![0, 3, 0, 0, -1, -2]

def sourceA1917 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1918 : Charge := ![1, 0, 0, 2, -1, -2]

def sourceA1919 : Charge := ![1, 0, 0, 2, -1, -2]

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

def sourceA192 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA193 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA197 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA198 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA199 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA200 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA201 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA203 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA205 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA206 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA207 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA208 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA209 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA210 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA211 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA214 : Charge := ![0, 1, 1, 1, -1, -2]

def sourceA215 : Charge := ![0, 1, 1, 1, -1, -2]

def sourceA217 : Charge := ![0, 1, 1, 1, -1, -2]

def sourceA219 : Charge := ![0, 1, 1, 1, -1, -2]

def sourceA222 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA223 : Charge := ![-3, 0, 0, 0, 1, 2]

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

def sourceA1920 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1921 : Charge := ![1, 0, 1, 1, -1, -2]

def sourceA1923 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1924 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1925 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1926 : Charge := ![1, 1, -1, 0, 1, -2]

def sourceA1927 : Charge := ![1, 1, -1, 0, 1, -2]

def sourceA1929 : Charge := ![1, 1, -1, 0, 1, -2]

def sourceA1930 : Charge := ![1, 1, -1, 0, 1, -2]

def sourceA1931 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1932 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1933 : Charge := ![1, 1, -1, 1, -1, -1]

def sourceA1934 : Charge := ![1, 1, -1, 1, -1, -1]

def sourceA1935 : Charge := ![1, 1, -1, 1, -1, -1]

def sourceA1936 : Charge := ![1, 1, -1, 1, -1, -1]

def sourceA1937 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1938 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1939 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1940 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1942 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1943 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1944 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1945 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1946 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1947 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1948 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1949 : Charge := ![1, 1, 0, 0, 0, -2]

def sourceA1950 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1951 : Charge := ![-3, -1, 0, 0, 1, 3]

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

def sourceA1952 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1953 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1954 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1955 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1956 : Charge := ![1, 1, 0, 0, 1, -3]

def sourceA1957 : Charge := ![1, 1, 0, 0, 1, -3]

def sourceA1958 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1959 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1960 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1961 : Charge := ![1, 1, 0, 1, -2, -1]

def sourceA1962 : Charge := ![1, 1, 0, 1, -2, -1]

def sourceA1965 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1966 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1967 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1968 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1971 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1973 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1974 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1975 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1976 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1977 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1978 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1979 : Charge := ![1, 1, 0, 1, 0, -3]

def sourceA1981 : Charge := ![-3, -1, 0, 0, 1, 3]

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

def sourceA1987 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1991 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1993 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1996 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1997 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1998 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2000 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2001 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2002 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2003 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2008 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2009 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2011 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2012 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2014 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2015 : Charge := ![-3, -1, 0, 0, 1, 3]

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

def sourceA2016 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2017 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2018 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2019 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2020 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2021 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2022 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2023 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2024 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2025 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2026 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2027 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2028 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2031 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2032 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2033 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2034 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2035 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2036 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2039 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2040 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2041 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2042 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2043 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2044 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2045 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2046 : Charge := ![-3, -1, 0, 0, 1, 3]

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

def sourceA2051 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2052 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2054 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2056 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2057 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2059 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2061 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2062 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2064 : Charge := ![1, 0, 1, 0, -2, 0]

def sourceA2065 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2072 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2073 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2074 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2077 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2079 : Charge := ![-3, -1, 0, 0, 1, 3]

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

def sourceA2084 : Charge := ![1, -1, 0, 0, 0, 0]

def sourceA2085 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2086 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2087 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2088 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2089 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2091 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2092 : Charge := ![0, 1, 0, 2, -2, -1]

def sourceA2093 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2094 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2095 : Charge := ![0, 1, 1, 1, -2, -1]

def sourceA2097 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2098 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2099 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2100 : Charge := ![0, 2, 0, 1, -2, -1]

def sourceA2101 : Charge := ![0, 2, 0, 1, -2, -1]

def sourceA2102 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2103 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2104 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2105 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2106 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2108 : Charge := ![1, 0, 0, 2, -2, -1]

def sourceA2110 : Charge := ![1, 0, 0, 2, -2, -1]

def sourceA2111 : Charge := ![-3, -1, 0, 0, 2, 2]

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

def sourceA2112 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2114 : Charge := ![1, 0, 1, 1, -2, -1]

def sourceA2115 : Charge := ![1, 0, 1, 1, -2, -1]

def sourceA2118 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2119 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2120 : Charge := ![1, 1, -1, 0, -2, 1]

def sourceA2121 : Charge := ![1, 1, -1, 0, -2, 1]

def sourceA2122 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2123 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2124 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2125 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2126 : Charge := ![1, 1, -1, 1, -2, 0]

def sourceA2129 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2130 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2132 : Charge := ![1, 1, -1, 1, -1, -1]

def sourceA2133 : Charge := ![1, 1, -1, 1, -1, -1]

def sourceA2134 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2135 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2136 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2137 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2138 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2139 : Charge := ![1, 1, 0, 0, -2, 0]

def sourceA2140 : Charge := ![1, 1, 0, 0, -2, 0]

def sourceA2141 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2142 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2143 : Charge := ![-3, -1, 0, 0, 2, 2]

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

def sourceA2144 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2145 : Charge := ![1, 1, 0, 0, -1, -1]

def sourceA2146 : Charge := ![1, 1, 0, 0, -1, -1]

def sourceA2147 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2148 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2149 : Charge := ![1, 1, 0, 1, -3, 0]

def sourceA2152 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2153 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2154 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2155 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2156 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2157 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2160 : Charge := ![1, 1, 0, 1, -2, -1]

def sourceA2161 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2168 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2169 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2170 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2171 : Charge := ![1, 2, -1, 0, -2, 0]

def sourceA2172 : Charge := ![1, 2, -1, 0, -2, 0]

def sourceA2175 : Charge := ![-3, -1, 0, 0, 2, 2]

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

def sourceA2176 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2177 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2180 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2181 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2182 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2189 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2190 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2191 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2192 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2193 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2194 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2195 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2196 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2197 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2203 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2207 : Charge := ![-3, -1, 0, 0, 2, 2]

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

def sourceA2210 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2211 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2212 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2217 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2218 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2219 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2229 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2230 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2235 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2236 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2238 : Charge := ![-3, -1, 0, 0, 2, 2]

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

def sourceA224 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA225 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA226 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA227 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA228 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA229 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA230 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA231 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA233 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA234 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA235 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA236 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA237 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA238 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA239 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA240 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA241 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA244 : Charge := ![1, -1, 0, 0, 2, -2]

def sourceA245 : Charge := ![1, -1, 0, 0, 2, -2]

def sourceA246 : Charge := ![1, -1, 0, 0, 2, -2]

def sourceA247 : Charge := ![1, -1, 0, 0, 2, -2]

def sourceA250 : Charge := ![1, -1, 0, 0, 2, -2]

def sourceA251 : Charge := ![1, -1, 0, 0, 2, -2]

def sourceA253 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA254 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA255 : Charge := ![-3, 0, 0, 0, 1, 2]

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

def sourceA2244 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2245 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2249 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2251 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2252 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2253 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2254 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2255 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2256 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2257 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2259 : Charge := ![0, 2, 0, 0, 0, -2]

def sourceA2260 : Charge := ![0, 2, 0, 0, 0, -2]

def sourceA2261 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2262 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2263 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2264 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2265 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2266 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2267 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2268 : Charge := ![0, 2, 0, 0, -1, -1]

def sourceA2269 : Charge := ![0, 2, 0, 0, -1, -1]

def sourceA2271 : Charge := ![-3, -1, 0, 0, 2, 2]

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

def sourceA2273 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2274 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2275 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2276 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2277 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2278 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2279 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2283 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2284 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2285 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2286 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2287 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2288 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2289 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2291 : Charge := ![0, 1, 1, 0, -1, -1]

def sourceA2295 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2296 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2297 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2298 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2302 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2303 : Charge := ![-3, -1, 0, 0, 2, 2]

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

def sourceA2304 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2308 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2310 : Charge := ![0, 0, 1, 0, 0, -1]

def sourceA2311 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2312 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2313 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2315 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2316 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2318 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2319 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2320 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2321 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2322 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2323 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2325 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2326 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2327 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2328 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2330 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2331 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2333 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2334 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2335 : Charge := ![-3, -1, 0, 1, 1, 2]

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

def sourceA2336 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2337 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2338 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2339 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2340 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2341 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2342 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2343 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2344 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2345 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2348 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2349 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2350 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2351 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2352 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2353 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2354 : Charge := ![1, 1, 0, 0, 0, -2]

def sourceA2355 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2356 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2357 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2358 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2359 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2365 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2366 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2367 : Charge := ![-3, -1, 0, 1, 1, 2]

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

def sourceA2368 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2370 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2371 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2374 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2375 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2376 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2377 : Charge := ![1, 2, -1, 0, 0, -2]

def sourceA2378 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2382 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2383 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2386 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2387 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2388 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2390 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2391 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2392 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2393 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2394 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2397 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2398 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2399 : Charge := ![-3, -1, 0, 1, 1, 2]

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

def sourceA2400 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2402 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2403 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2404 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2405 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2410 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2411 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2415 : Charge := ![1, 0, 1, 0, -2, 0]

def sourceA2416 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2417 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2425 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2426 : Charge := ![-3, -1, 0, 1, 1, 2]

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

def sourceA2439 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2440 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2441 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2442 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2443 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2445 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2446 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2447 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2448 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2449 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2450 : Charge := ![0, 2, 0, 0, -1, -1]

def sourceA2451 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2452 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2453 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2454 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2455 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2456 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2457 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2458 : Charge := ![0, 2, 0, -1, -1, 0]

def sourceA2460 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2461 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2462 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2463 : Charge := ![-3, -1, 0, 1, 1, 2]

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

def sourceA2464 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2466 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2467 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2468 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2469 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2470 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2471 : Charge := ![0, 1, 1, 0, -1, -1]

def sourceA2472 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2473 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2474 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2475 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2476 : Charge := ![0, 1, 1, -1, -1, 0]

def sourceA2477 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2478 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2479 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2481 : Charge := ![0, 1, 0, 1, 0, -2]

def sourceA2482 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2483 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2484 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2485 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2486 : Charge := ![0, 1, 0, 1, -1, -1]

def sourceA2487 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2488 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2489 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2491 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2492 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2493 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2494 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2495 : Charge := ![0, 0, 1, 0, 0, -1]

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

def sourceA2496 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2497 : Charge := ![-3, -1, 1, 1, 1, 1]

def sourceA2499 : Charge := ![-3, -1, 1, 1, 1, 1]

def sourceA2500 : Charge := ![-3, -1, 1, 1, 1, 1]

def sourceA2502 : Charge := ![-3, -1, 1, 1, 1, 1]

def sourceA2503 : Charge := ![-3, -1, 1, 1, 1, 1]

def sourceA2504 : Charge := ![-3, -1, 1, 1, 1, 1]

def sourceA2508 : Charge := ![-3, -1, 1, 1, 1, 1]

def sourceA2509 : Charge := ![-3, -1, 1, 1, 1, 1]

def sourceA2510 : Charge := ![-3, -1, 1, 1, 1, 1]

def sourceA2511 : Charge := ![0, 2, 0, 0, -1, -1]

def sourceA2512 : Charge := ![-3, -1, 1, 1, 1, 1]

def sourceA2513 : Charge := ![-3, -1, 1, 1, 1, 1]

def sourceA2514 : Charge := ![-3, -1, 1, 1, 1, 1]

def sourceA2515 : Charge := ![-2, -2, 0, 0, 2, 2]

def sourceA2516 : Charge := ![-2, -2, 0, 0, 2, 2]

def sourceA2519 : Charge := ![-2, -2, 0, 0, 2, 2]

def sourceA2520 : Charge := ![-2, -2, 0, 0, 2, 2]

def sourceA2521 : Charge := ![-2, -2, 0, 0, 2, 2]

def sourceA2522 : Charge := ![-2, -2, 0, 0, 2, 2]

def sourceA2523 : Charge := ![-2, -2, 0, 0, 2, 2]

def sourceA2524 : Charge := ![-2, -2, 0, 0, 2, 2]

def sourceA2525 : Charge := ![-2, -2, 0, 0, 2, 2]

def sourceA2526 : Charge := ![0, 2, 0, 0, -2, 0]

def sourceA2527 : Charge := ![-2, -2, 0, 0, 2, 2]

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

def sourceA2528 : Charge := ![-2, -2, 0, 0, 2, 2]

def sourceA2529 : Charge := ![0, 2, 0, 0, -1, -1]

def sourceA2532 : Charge := ![-2, -2, 0, 0, 2, 2]

def sourceA2533 : Charge := ![-2, -2, 0, 0, 2, 2]

def sourceA2534 : Charge := ![-2, -2, 0, 0, 2, 2]

def sourceA2535 : Charge := ![-2, -2, 0, 0, 2, 2]

def sourceA2536 : Charge := ![-2, -2, 0, 0, 2, 2]

def sourceA2537 : Charge := ![-2, -2, 0, 0, 2, 2]

def sourceA2545 : Charge := ![-2, -2, 0, 0, 2, 2]

def sourceA2546 : Charge := ![-2, -2, 0, 0, 2, 2]

def sourceA2547 : Charge := ![-2, -2, 0, 0, 2, 2]

def sourceA2550 : Charge := ![-2, -2, 0, 0, 2, 2]

def sourceA2551 : Charge := ![-2, -2, 0, 0, 2, 2]

def sourceA2552 : Charge := ![1, 1, 0, 0, -1, -1]

end MUB6.Certificate.MixedSemantics

end OAI
end


