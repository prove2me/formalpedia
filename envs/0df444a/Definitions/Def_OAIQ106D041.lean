-- Prove2me | Definitions.Def_OAIQ106D041
-- name    : OAIQ106D041
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T12:21:55.42691+00:00
-- url     : https://prove2.me/theorems/dcb95366-419d-435c-966d-9cd5553bb366
-- title:
--   Definitions bundle OAIQ106D041 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2667 declarations of OpenAI's Lean: 2667 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw9786step1`, `OAI.MUB6.Certificate.MixedSemantics.raw9786step2`, `OAI.MUB6.Certificate.MixedSemantics.raw9786step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw9787`, `OAI.MUB6.Certificate.MixedSemantics.raw9787Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw9787step0`, `OAI.MUB6.Certificate.MixedSemantics.raw9787step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw9787step1`, `OAI.MUB6.Certificate.MixedSemantics.raw9787step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw9788`, `OAI.MUB6.Certificate.MixedSemantics.raw9788Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw9788step0`, `OAI.MUB6.Certificate.MixedSemantics.raw9788step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw9788step1`, `OAI.MUB6.Certificate.MixedSemantics.raw9788step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw9788step2`, `OAI.MUB6.Certificate.MixedSemantics.raw9788step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw9789`, `OAI.MUB6.Certificate.MixedSemantics.raw9789Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw9789step0`, `OAI.MUB6.Certificate.MixedSemantics.raw9789step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw9789step1`, `OAI.MUB6.Certificate.MixedSemantics.raw9789step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw9789step2`, `OAI.MUB6.Certificate.MixedSemantics.raw9789step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw978Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw978step0`, `OAI.MUB6.Certificate.MixedSemantics.raw978step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw978step1`, `OAI.MUB6.Certificate.MixedSemantics.raw978step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw979`, `OAI.MUB6.Certificate.MixedSemantics.raw9790`, `OAI.MUB6.Certificate.MixedSemantics.raw9790Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw9790step0`, `OAI.MUB6.Certificate.MixedSemantics.raw9790step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw9790step1`, `OAI.MUB6.Certificate.MixedSemantics.raw9790step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw9790step2`, `OAI.MUB6.Certificate.MixedSemantics.raw9790step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw9790step3` and 2627 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedSemantics_Canonical0`, `MutuallyUnbiased_MixedSemantics_Canonical7`, `MutuallyUnbiased_MixedSemantics_Canonical76`, `MutuallyUnbiased_MixedSemantics_Canonical77`, `MutuallyUnbiased_MixedSemantics_Canonical78`, `MutuallyUnbiased_MixedSemantics_Singletons10`, `MutuallyUnbiased_MixedSemantics_Singletons18`, `MutuallyUnbiased_MixedSemantics_Singletons19`, `MutuallyUnbiased_MixedSemantics_Singletons20`, `MutuallyUnbiased_MixedSemantics_Singletons21`, `MutuallyUnbiased_MixedSemantics_Singletons22`, `MutuallyUnbiased_MixedSemantics_Singletons23`, `MutuallyUnbiased_MixedSemantics_Singletons36`, `MutuallyUnbiased_MixedSemantics_Singletons39`, `MutuallyUnbiased_MixedSemantics_Singletons40`, `MutuallyUnbiased_MixedSemantics_Singletons41`, `MutuallyUnbiased_MixedSemantics_Singletons43`, `MutuallyUnbiased_MixedSemantics_Singletons45`, `MutuallyUnbiased_MixedSemantics_Singletons46`, `MutuallyUnbiased_MixedSemantics_Singletons48`, `MutuallyUnbiased_MixedSemantics_Singletons49`, `MutuallyUnbiased_MixedSemantics_Singletons50`, `MutuallyUnbiased_MixedSemantics_Singletons57`, `MutuallyUnbiased_MixedSemantics_Singletons58`, `MutuallyUnbiased_MixedSemantics_Singletons59`, `MutuallyUnbiased_MixedSemantics_Singletons60`, `MutuallyUnbiased_MixedSemantics_Singletons61`, `MutuallyUnbiased_MixedSemantics_Singletons62`, `MutuallyUnbiased_MixedSemantics_Singletons63`, `MutuallyUnbiased_MixedSemantics_Singletons64`, `MutuallyUnbiased_MixedSemantics_Singletons65`, `MutuallyUnbiased_MixedSemantics_Singletons66`, `MutuallyUnbiased_MixedSemantics_Singletons67`, `MutuallyUnbiased_MixedSemantics_Singletons68`, `MutuallyUnbiased_MixedSemantics_Singletons69`, `MutuallyUnbiased_MixedSemantics_Singletons70`, `MutuallyUnbiased_MixedSemantics_Singletons71`, `MutuallyUnbiased_MixedSemantics_Singletons72`, `MutuallyUnbiased_MixedSemantics_Singletons73`, `MutuallyUnbiased_MixedSemantics_Singletons74`, `MutuallyUnbiased_MixedSemantics_Singletons75`, `MutuallyUnbiased_MixedSemantics_Singletons76`, `MutuallyUnbiased_MixedSemantics_Singletons77`, `MutuallyUnbiased_MixedSemantics_Singletons78`, `MutuallyUnbiased_MixedSemantics_Singletons79`, `MutuallyUnbiased_MixedSemantics_Singletons80`, `MutuallyUnbiased_MixedSemantics_Singletons81`, `MutuallyUnbiased_MixedSemantics_Singletons82`, `MutuallyUnbiased_MixedSemantics_Singletons83`, `MutuallyUnbiased_MixedSemantics_Singletons84`, `MutuallyUnbiased_MixedSemantics_Singletons85`, `MutuallyUnbiased_PairSemantics_Boundary0`, `MutuallyUnbiased_PairSemantics_Boundary1`, `MutuallyUnbiased_PairSemantics_Boundary10`, `MutuallyUnbiased_PairSemantics_Boundary11`, `MutuallyUnbiased_PairSemantics_Boundary12`, `MutuallyUnbiased_PairSemantics_Boundary13`, `MutuallyUnbiased_PairSemantics_Boundary14`, `MutuallyUnbiased_PairSemantics_Boundary15`, `MutuallyUnbiased_PairSemantics_Boundary2`, `MutuallyUnbiased_PairSemantics_Boundary5`, `MutuallyUnbiased_PairSemantics_Boundary6`, `MutuallyUnbiased_PairSemantics_Boundary7`, `MutuallyUnbiased_PairSemantics_Boundary8`, `MutuallyUnbiased_PairSemantics_Boundary9`, `MutuallyUnbiased_PairSemantics_Nodes0`, `MutuallyUnbiased_PairSemantics_Nodes1`, `MutuallyUnbiased_PairSemantics_Nodes15`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the statements `OAI.MUB6.Certificate.PairSemantics.canonical7982`, `OAI.MUB6.Certificate.PairSemantics.canonical9056` and `OAI.MUB6.Certificate.PairSemantics.sound0`; the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1161`, `OAI.MUB6.Certificate.MixedSemantics.sound1162`, `OAI.MUB6.Certificate.MixedSemantics.sound1163`, `OAI.MUB6.Certificate.MixedSemantics.sound1164`, `OAI.MUB6.Certificate.MixedSemantics.sound1165`, `OAI.MUB6.Certificate.MixedSemantics.sound1166`, `OAI.MUB6.Certificate.MixedSemantics.sound1168`, `OAI.MUB6.Certificate.MixedSemantics.sound1170`, `OAI.MUB6.Certificate.MixedSemantics.sound1172`, `OAI.MUB6.Certificate.MixedSemantics.sound1173`, `OAI.MUB6.Certificate.MixedSemantics.sound1175`, `OAI.MUB6.Certificate.MixedSemantics.sound1265`, `OAI.MUB6.Certificate.MixedSemantics.sound1266`, `OAI.MUB6.Certificate.MixedSemantics.sound1267`, `OAI.MUB6.Certificate.MixedSemantics.sound1271`, `OAI.MUB6.Certificate.MixedSemantics.sound1298`, `OAI.MUB6.Certificate.MixedSemantics.sound1299`, `OAI.MUB6.Certificate.MixedSemantics.sound1301`, `OAI.MUB6.Certificate.MixedSemantics.sound1339`, `OAI.MUB6.Certificate.MixedSemantics.sound1340`, `OAI.MUB6.Certificate.MixedSemantics.sound1341`, `OAI.MUB6.Certificate.MixedSemantics.sound1342`, `OAI.MUB6.Certificate.MixedSemantics.sound1343`, `OAI.MUB6.Certificate.MixedSemantics.sound1344`, `OAI.MUB6.Certificate.MixedSemantics.sound1346`, `OAI.MUB6.Certificate.MixedSemantics.sound1395`, `OAI.MUB6.Certificate.MixedSemantics.sound1396`, `OAI.MUB6.Certificate.MixedSemantics.sound1397`, `OAI.MUB6.Certificate.MixedSemantics.sound1399`, `OAI.MUB6.Certificate.MixedSemantics.sound1401`, `OAI.MUB6.Certificate.MixedSemantics.sound1409`, `OAI.MUB6.Certificate.MixedSemantics.sound1410`, `OAI.MUB6.Certificate.MixedSemantics.sound1411`, `OAI.MUB6.Certificate.MixedSemantics.sound1412`, `OAI.MUB6.Certificate.MixedSemantics.sound1413`, `OAI.MUB6.Certificate.MixedSemantics.sound1414`, `OAI.MUB6.Certificate.MixedSemantics.sound1416`, `OAI.MUB6.Certificate.MixedSemantics.sound1417`, `OAI.MUB6.Certificate.MixedSemantics.sound1427`, `OAI.MUB6.Certificate.MixedSemantics.sound1441`, `OAI.MUB6.Certificate.MixedSemantics.sound1443`, `OAI.MUB6.Certificate.MixedSemantics.sound1451`, `OAI.MUB6.Certificate.MixedSemantics.sound1475`, `OAI.MUB6.Certificate.MixedSemantics.sound1477`, `OAI.MUB6.Certificate.MixedSemantics.sound1478`, `OAI.MUB6.Certificate.MixedSemantics.sound1479`, `OAI.MUB6.Certificate.MixedSemantics.sound1480`, `OAI.MUB6.Certificate.MixedSemantics.sound171`, `OAI.MUB6.Certificate.MixedSemantics.sound174`, `OAI.MUB6.Certificate.MixedSemantics.sound206`, `OAI.MUB6.Certificate.MixedSemantics.sound207`, `OAI.MUB6.Certificate.MixedSemantics.sound2357`, `OAI.MUB6.Certificate.MixedSemantics.sound2358`, `OAI.MUB6.Certificate.MixedSemantics.sound2359`, `OAI.MUB6.Certificate.MixedSemantics.sound2527`, `OAI.MUB6.Certificate.MixedSemantics.sound2530`, `OAI.MUB6.Certificate.MixedSemantics.sound2531`, `OAI.MUB6.Certificate.MixedSemantics.sound2532`, `OAI.MUB6.Certificate.MixedSemantics.sound2570`, `OAI.MUB6.Certificate.MixedSemantics.sound2572`, `OAI.MUB6.Certificate.MixedSemantics.sound2574`, `OAI.MUB6.Certificate.MixedSemantics.sound2576`, `OAI.MUB6.Certificate.MixedSemantics.sound2593`, `OAI.MUB6.Certificate.MixedSemantics.sound2594`, `OAI.MUB6.Certificate.MixedSemantics.sound2595`, `OAI.MUB6.Certificate.MixedSemantics.sound2596`, `OAI.MUB6.Certificate.MixedSemantics.sound2598`, `OAI.MUB6.Certificate.MixedSemantics.sound2599`, `OAI.MUB6.Certificate.MixedSemantics.sound2601`, `OAI.MUB6.Certificate.MixedSemantics.sound2636`, `OAI.MUB6.Certificate.MixedSemantics.sound2637`, `OAI.MUB6.Certificate.MixedSemantics.sound2638`, `OAI.MUB6.Certificate.MixedSemantics.sound2640`, `OAI.MUB6.Certificate.MixedSemantics.sound2753`, `OAI.MUB6.Certificate.MixedSemantics.sound2766`, `OAI.MUB6.Certificate.MixedSemantics.sound2828`, `OAI.MUB6.Certificate.MixedSemantics.sound2904`, `OAI.MUB6.Certificate.MixedSemantics.sound293`, `OAI.MUB6.Certificate.MixedSemantics.sound2936`, `OAI.MUB6.Certificate.MixedSemantics.sound2937`, `OAI.MUB6.Certificate.MixedSemantics.sound2939`, `OAI.MUB6.Certificate.MixedSemantics.sound294`, `OAI.MUB6.Certificate.MixedSemantics.sound2941`, `OAI.MUB6.Certificate.MixedSemantics.sound2943`, `OAI.MUB6.Certificate.MixedSemantics.sound2957`, `OAI.MUB6.Certificate.MixedSemantics.sound2958`, `OAI.MUB6.Certificate.MixedSemantics.sound2959`, `OAI.MUB6.Certificate.MixedSemantics.sound2960`, `OAI.MUB6.Certificate.MixedSemantics.sound2961`, `OAI.MUB6.Certificate.MixedSemantics.sound2963`, `OAI.MUB6.Certificate.MixedSemantics.sound2965`, `OAI.MUB6.Certificate.MixedSemantics.sound2966`, `OAI.MUB6.Certificate.MixedSemantics.sound2968`, `OAI.MUB6.Certificate.MixedSemantics.sound2969`, `OAI.MUB6.Certificate.MixedSemantics.sound2986`, `OAI.MUB6.Certificate.MixedSemantics.sound2987`, `OAI.MUB6.Certificate.MixedSemantics.sound2988`, `OAI.MUB6.Certificate.MixedSemantics.sound2990`, `OAI.MUB6.Certificate.MixedSemantics.sound2996`, `OAI.MUB6.Certificate.MixedSemantics.sound2997`, `OAI.MUB6.Certificate.MixedSemantics.sound2998`, `OAI.MUB6.Certificate.MixedSemantics.sound3003`, `OAI.MUB6.Certificate.MixedSemantics.sound3005`, `OAI.MUB6.Certificate.MixedSemantics.sound3082`, `OAI.MUB6.Certificate.MixedSemantics.sound3087`, `OAI.MUB6.Certificate.MixedSemantics.sound3088`, `OAI.MUB6.Certificate.MixedSemantics.sound3089`, `OAI.MUB6.Certificate.MixedSemantics.sound3090`, `OAI.MUB6.Certificate.MixedSemantics.sound3093`, `OAI.MUB6.Certificate.MixedSemantics.sound3094`, `OAI.MUB6.Certificate.MixedSemantics.sound3099`, `OAI.MUB6.Certificate.MixedSemantics.sound3100`, `OAI.MUB6.Certificate.MixedSemantics.sound3101`, `OAI.MUB6.Certificate.MixedSemantics.sound3102`, `OAI.MUB6.Certificate.MixedSemantics.sound3106`, `OAI.MUB6.Certificate.MixedSemantics.sound3109`, `OAI.MUB6.Certificate.MixedSemantics.sound3110`, `OAI.MUB6.Certificate.MixedSemantics.sound3116`, `OAI.MUB6.Certificate.MixedSemantics.sound3120`, `OAI.MUB6.Certificate.MixedSemantics.sound3143`, `OAI.MUB6.Certificate.MixedSemantics.sound3144`, `OAI.MUB6.Certificate.MixedSemantics.sound3178`, `OAI.MUB6.Certificate.MixedSemantics.sound3184`, `OAI.MUB6.Certificate.MixedSemantics.sound3185`, `OAI.MUB6.Certificate.MixedSemantics.sound3190`, `OAI.MUB6.Certificate.MixedSemantics.sound3191`, `OAI.MUB6.Certificate.MixedSemantics.sound3203`, `OAI.MUB6.Certificate.MixedSemantics.sound3204`, `OAI.MUB6.Certificate.MixedSemantics.sound3205`, `OAI.MUB6.Certificate.MixedSemantics.sound3206`, `OAI.MUB6.Certificate.MixedSemantics.sound3207`, `OAI.MUB6.Certificate.MixedSemantics.sound3209`, `OAI.MUB6.Certificate.MixedSemantics.sound3210`, `OAI.MUB6.Certificate.MixedSemantics.sound3211`, `OAI.MUB6.Certificate.MixedSemantics.sound3223`, `OAI.MUB6.Certificate.MixedSemantics.sound3226`, `OAI.MUB6.Certificate.MixedSemantics.sound3227`, `OAI.MUB6.Certificate.MixedSemantics.sound370`, `OAI.MUB6.Certificate.MixedSemantics.sound371`, `OAI.MUB6.Certificate.MixedSemantics.sound3711`, `OAI.MUB6.Certificate.MixedSemantics.sound3726`, `OAI.MUB6.Certificate.MixedSemantics.sound3727`, `OAI.MUB6.Certificate.MixedSemantics.sound3734`, `OAI.MUB6.Certificate.MixedSemantics.sound3735`, `OAI.MUB6.Certificate.MixedSemantics.sound3736`, `OAI.MUB6.Certificate.MixedSemantics.sound3737`, `OAI.MUB6.Certificate.MixedSemantics.sound3738`, `OAI.MUB6.Certificate.MixedSemantics.sound3739`, `OAI.MUB6.Certificate.MixedSemantics.sound3818`, `OAI.MUB6.Certificate.MixedSemantics.sound3821`, `OAI.MUB6.Certificate.MixedSemantics.sound3822`, `OAI.MUB6.Certificate.MixedSemantics.sound3823`, `OAI.MUB6.Certificate.MixedSemantics.sound3824`, `OAI.MUB6.Certificate.MixedSemantics.sound3829`, `OAI.MUB6.Certificate.MixedSemantics.sound3831`, `OAI.MUB6.Certificate.MixedSemantics.sound3847`, `OAI.MUB6.Certificate.MixedSemantics.sound3851`, `OAI.MUB6.Certificate.MixedSemantics.sound3852`, `OAI.MUB6.Certificate.MixedSemantics.sound3853`, `OAI.MUB6.Certificate.MixedSemantics.sound3855`, `OAI.MUB6.Certificate.MixedSemantics.sound3856`, `OAI.MUB6.Certificate.MixedSemantics.sound3858`, `OAI.MUB6.Certificate.MixedSemantics.sound3882`, `OAI.MUB6.Certificate.MixedSemantics.sound3883`, `OAI.MUB6.Certificate.MixedSemantics.sound3887`, `OAI.MUB6.Certificate.MixedSemantics.sound3888`, `OAI.MUB6.Certificate.MixedSemantics.sound3925`, `OAI.MUB6.Certificate.MixedSemantics.sound3931`, `OAI.MUB6.Certificate.MixedSemantics.sound3933`, `OAI.MUB6.Certificate.MixedSemantics.sound3936`, `OAI.MUB6.Certificate.MixedSemantics.sound3937`, `OAI.MUB6.Certificate.MixedSemantics.sound3965`, `OAI.MUB6.Certificate.MixedSemantics.sound3966`, `OAI.MUB6.Certificate.MixedSemantics.sound3967`, `OAI.MUB6.Certificate.MixedSemantics.sound3977`, `OAI.MUB6.Certificate.MixedSemantics.sound3980`, `OAI.MUB6.Certificate.MixedSemantics.sound3981`, `OAI.MUB6.Certificate.MixedSemantics.sound3982`, `OAI.MUB6.Certificate.MixedSemantics.sound3984`, `OAI.MUB6.Certificate.MixedSemantics.sound3987`, `OAI.MUB6.Certificate.MixedSemantics.sound3992`, `OAI.MUB6.Certificate.MixedSemantics.sound3993`, `OAI.MUB6.Certificate.MixedSemantics.sound3994`, `OAI.MUB6.Certificate.MixedSemantics.sound3995`, `OAI.MUB6.Certificate.MixedSemantics.sound3997`, `OAI.MUB6.Certificate.MixedSemantics.sound3998`, `OAI.MUB6.Certificate.MixedSemantics.sound4002`, `OAI.MUB6.Certificate.MixedSemantics.sound4003`, `OAI.MUB6.Certificate.MixedSemantics.sound4012`, `OAI.MUB6.Certificate.MixedSemantics.sound4013`, `OAI.MUB6.Certificate.MixedSemantics.sound4014`, `OAI.MUB6.Certificate.MixedSemantics.sound4023`, `OAI.MUB6.Certificate.MixedSemantics.sound4026`, `OAI.MUB6.Certificate.MixedSemantics.sound4027`, `OAI.MUB6.Certificate.MixedSemantics.sound4029`, `OAI.MUB6.Certificate.MixedSemantics.sound4031`, `OAI.MUB6.Certificate.MixedSemantics.sound4032`, `OAI.MUB6.Certificate.MixedSemantics.sound4033`, `OAI.MUB6.Certificate.MixedSemantics.sound4039`, `OAI.MUB6.Certificate.MixedSemantics.sound4050`, `OAI.MUB6.Certificate.MixedSemantics.sound4053`, `OAI.MUB6.Certificate.MixedSemantics.sound436`, `OAI.MUB6.Certificate.MixedSemantics.sound454`, `OAI.MUB6.Certificate.MixedSemantics.sound455`, `OAI.MUB6.Certificate.MixedSemantics.sound4622`, `OAI.MUB6.Certificate.MixedSemantics.sound4623`, `OAI.MUB6.Certificate.MixedSemantics.sound4625`, `OAI.MUB6.Certificate.MixedSemantics.sound479`, `OAI.MUB6.Certificate.MixedSemantics.sound511`, `OAI.MUB6.Certificate.MixedSemantics.sound514`, `OAI.MUB6.Certificate.MixedSemantics.sound5167`, `OAI.MUB6.Certificate.MixedSemantics.sound5168`, `OAI.MUB6.Certificate.MixedSemantics.sound5169`, `OAI.MUB6.Certificate.MixedSemantics.sound5171`, `OAI.MUB6.Certificate.MixedSemantics.sound5172`, `OAI.MUB6.Certificate.MixedSemantics.sound5174`, `OAI.MUB6.Certificate.MixedSemantics.sound5176`, `OAI.MUB6.Certificate.MixedSemantics.sound5177`, `OAI.MUB6.Certificate.MixedSemantics.sound521`, `OAI.MUB6.Certificate.MixedSemantics.sound5292`, `OAI.MUB6.Certificate.MixedSemantics.sound5293`, `OAI.MUB6.Certificate.MixedSemantics.sound5294`, `OAI.MUB6.Certificate.MixedSemantics.sound5296`, `OAI.MUB6.Certificate.MixedSemantics.sound5306`, `OAI.MUB6.Certificate.MixedSemantics.sound5310`, `OAI.MUB6.Certificate.MixedSemantics.sound5386`, `OAI.MUB6.Certificate.MixedSemantics.sound5387`, `OAI.MUB6.Certificate.MixedSemantics.sound5388`, `OAI.MUB6.Certificate.MixedSemantics.sound5415`, `OAI.MUB6.Certificate.MixedSemantics.sound5416`, `OAI.MUB6.Certificate.MixedSemantics.sound5418`, `OAI.MUB6.Certificate.MixedSemantics.sound5433`, `OAI.MUB6.Certificate.MixedSemantics.sound5434`, `OAI.MUB6.Certificate.MixedSemantics.sound5435`, `OAI.MUB6.Certificate.MixedSemantics.sound5439`, `OAI.MUB6.Certificate.MixedSemantics.sound5443`, `OAI.MUB6.Certificate.MixedSemantics.sound5450`, `OAI.MUB6.Certificate.MixedSemantics.sound5451`, `OAI.MUB6.Certificate.MixedSemantics.sound5452`, `OAI.MUB6.Certificate.MixedSemantics.sound5453`, `OAI.MUB6.Certificate.MixedSemantics.sound5464`, `OAI.MUB6.Certificate.MixedSemantics.sound5465`, `OAI.MUB6.Certificate.MixedSemantics.sound5476`, `OAI.MUB6.Certificate.MixedSemantics.sound5482`, `OAI.MUB6.Certificate.MixedSemantics.sound5483`, `OAI.MUB6.Certificate.MixedSemantics.sound5485`, `OAI.MUB6.Certificate.MixedSemantics.sound5490`, `OAI.MUB6.Certificate.MixedSemantics.sound5491`, `OAI.MUB6.Certificate.MixedSemantics.sound5492`, `OAI.MUB6.Certificate.MixedSemantics.sound5498`, `OAI.MUB6.Certificate.MixedSemantics.sound5500`, `OAI.MUB6.Certificate.MixedSemantics.sound644`, `OAI.MUB6.Certificate.MixedSemantics.sound645`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound0`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound1`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound103`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound111`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound115`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound119`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound123`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound135`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound136`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound137`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound138`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound139`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound140`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound141`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound142`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound143`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound145`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound146`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound147`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound148`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound149`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound150`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound151`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound19`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound20`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound21`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound22`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound28`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound30`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound31`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound32`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound33`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound34`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound35`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound36`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound44`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound46`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound49`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound58`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound6`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound67`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound68`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound7`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound8`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound81`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound88`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound9`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound93`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1098`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1423`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero15`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1780`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero539`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero733`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero863`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero925`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound0`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound10`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound100`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1007`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1008`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1009`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound101`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1010`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1012`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1013`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1020`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1021`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1030`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1033`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1034`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound109`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1093`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1094`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1095`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1096`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1097`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound11`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound110`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1103`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1108`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1109`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound111`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1110`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1111`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1114`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1115`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1120`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1121`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1123`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1124`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound113`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1130`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1131`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound114`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1158`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1159`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound116`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1165`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1166`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1167`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1169`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound117`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1170`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1177`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1178`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1179`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1191`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1194`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1195`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1197`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1205`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1227`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1231`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1232`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1233`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound126`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1261`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1262`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1263`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1264`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1266`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1267`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1268`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1269`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound127`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1271`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1272`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1278`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1279`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound129`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1293`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1294`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound13`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound130`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1300`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1301`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1303`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1309`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1310`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1311`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1312`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1317`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1318`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1321`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1324`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1326`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1335`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1340`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound137`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound138`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound14`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound140`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1409`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound141`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1410`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1411`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1414`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1417`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1418`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1420`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1421`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1422`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1428`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1429`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound143`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1433`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1435`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1436`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1437`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1441`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1442`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound145`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1465`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1469`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1470`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1471`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1472`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1477`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1478`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1480`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1483`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1484`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1490`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1493`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1505`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1507`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1508`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound151`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1510`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1511`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1513`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1514`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1516`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1517`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound152`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1521`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound153`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1536`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1539`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1559`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1560`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1561`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1567`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1568`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1569`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1571`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1575`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1584`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1587`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1589`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1593`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1595`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1598`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1599`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound16`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1648`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1649`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1650`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1651`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1652`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1653`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1655`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1656`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1657`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1662`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1668`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1669`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1672`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1673`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1674`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1679`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1684`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1686`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1687`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound17`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1702`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1703`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1708`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1709`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1710`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1715`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1716`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1717`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1723`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1734`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1738`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1739`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1740`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1743`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1781`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1782`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1783`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1785`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1786`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1787`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1788`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1789`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1795`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1796`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound18`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1811`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1815`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1816`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1822`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1825`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1828`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1831`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1833`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1835`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1838`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1839`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1840`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1844`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1845`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1846`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1847`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1848`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1849`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1853`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1854`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1856`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1858`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1859`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1864`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1865`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1866`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1871`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1872`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1873`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1874`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1877`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound188`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1880`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1881`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound19`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1904`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1905`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1906`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1908`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1910`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1911`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1912`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1914`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1915`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1916`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1917`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1924`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1925`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1935`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1937`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1941`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1944`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1945`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1948`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1949`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1952`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1953`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1956`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1958`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1960`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1963`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1964`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1965`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1968`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1970`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1971`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1972`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1976`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound198`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1980`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1983`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1984`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1985`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1988`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1989`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound199`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1990`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1991`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1993`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1994`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1995`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1998`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1999`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound20`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2002`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2003`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2004`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2005`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2006`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2010`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2011`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2014`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2015`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2016`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2018`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2019`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2021`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2022`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2023`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2033`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2034`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2035`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2036`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2037`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2038`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2039`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2040`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2045`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2046`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2048`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2049`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2050`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2051`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2056`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2059`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2060`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2061`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2062`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2063`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2064`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2066`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2067`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2069`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound207`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2071`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2073`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2075`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2076`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2077`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2078`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2080`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2082`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2084`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2086`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2088`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2090`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2092`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2093`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2094`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2096`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2097`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2099`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound21`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2100`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2102`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2103`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2105`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2107`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2108`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2109`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2166`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2168`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2169`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2170`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2171`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2172`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2174`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2175`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2176`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2177`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2178`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2179`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2180`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2181`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2182`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2183`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2184`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2185`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2187`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2188`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2189`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2190`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2191`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2192`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2194`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2197`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2198`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2199`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound22`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2200`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2201`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2202`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2203`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2204`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2205`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2206`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2207`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2208`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2211`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2212`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2214`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2216`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2217`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2218`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2219`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2221`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2222`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2223`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2224`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2225`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2226`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2227`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2228`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2229`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2230`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2231`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2232`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2233`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2235`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2238`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2240`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2242`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2244`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2245`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2246`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2247`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2248`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2249`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2250`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2251`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2252`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2254`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2255`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2257`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2258`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2259`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2260`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2261`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2263`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2264`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2266`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2267`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2268`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2269`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2270`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2271`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2272`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2273`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2274`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2275`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2276`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2277`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2278`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2279`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2280`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2282`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2283`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2284`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2286`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2287`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2288`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2289`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2291`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2292`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2293`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2294`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2296`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2297`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2298`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2299`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound23`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2300`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2301`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2302`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2303`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2304`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2306`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2307`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2308`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2309`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2313`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2315`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2317`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2318`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2320`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2321`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2322`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2323`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2324`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2325`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2326`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2327`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2329`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2330`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2331`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2332`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2333`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2334`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2335`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2336`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2337`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2338`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2340`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2341`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2343`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2344`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2345`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2346`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2347`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2348`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2350`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2351`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2352`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2353`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2354`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2355`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2356`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2357`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound236`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2360`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2361`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2362`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2363`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2364`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2365`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2366`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2367`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2368`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2369`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2371`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2372`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2373`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2374`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2375`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2377`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2378`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2379`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2380`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2381`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2382`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2383`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2384`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2385`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2386`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2388`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2389`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2390`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2391`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2393`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2394`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2395`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2396`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2397`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2398`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2399`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound24`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2400`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2401`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2402`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2403`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2404`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2405`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2406`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2407`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2408`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2409`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2410`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2411`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2413`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2414`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2415`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2418`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2419`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2420`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2423`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2424`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound244`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound245`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound25`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound255`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound267`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound268`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound269`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound28`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound286`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound287`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound29`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound296`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound3`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound310`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound327`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound339`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound340`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound341`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound342`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound344`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound345`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound349`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound35`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound353`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound354`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound356`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound357`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound358`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound359`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound365`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound366`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound367`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound368`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound369`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound370`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound371`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound372`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound380`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound388`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound391`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound392`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound395`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound396`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound4`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound404`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound411`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound412`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound413`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound417`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound418`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound426`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound428`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound438`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound444`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound445`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound446`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound452`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound453`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound456`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound462`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound463`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound473`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound474`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound482`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound483`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound484`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound485`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound487`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound488`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound489`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound497`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound498`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound499`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound5`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound500`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound501`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound503`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound504`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound512`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound514`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound515`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound516`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound518`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound519`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound520`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound521`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound522`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound523`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound525`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound526`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound531`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound532`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound533`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound534`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound536`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound537`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound538`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound542`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound543`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound545`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound546`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound547`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound548`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound551`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound552`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound553`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound554`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound555`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound558`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound564`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound565`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound566`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound567`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound568`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound571`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound572`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound579`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound58`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound580`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound581`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound582`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound584`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound585`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound587`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound588`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound589`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound59`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound590`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound599`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound6`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound600`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound612`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound613`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound620`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound621`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound628`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound629`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound630`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound631`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound632`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound633`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound635`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound642`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound649`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound656`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound658`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound659`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound660`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound663`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound664`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound666`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound667`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound675`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound682`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound686`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound693`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound700`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound708`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound710`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound711`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound717`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound718`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound719`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound721`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound726`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound728`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound730`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound731`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound732`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound734`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound735`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound736`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound737`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound738`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound740`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound741`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound742`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound743`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound744`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound745`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound746`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound749`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound750`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound757`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound758`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound759`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound779`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound780`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound786`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound787`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound788`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound790`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound791`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound792`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound793`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound794`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound795`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound796`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound797`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound798`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound799`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound8`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound800`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound801`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound802`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound813`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound814`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound816`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound817`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound821`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound833`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound840`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound843`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound844`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound851`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound852`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound857`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound858`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound859`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound864`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound865`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound866`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound867`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound871`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound872`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound877`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound878`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound881`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound882`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound884`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound885`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound886`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound888`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound890`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound892`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound894`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound896`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound897`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound898`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound899`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound9`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound900`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound901`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound903`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound905`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound908`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound909`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound91`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound910`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound911`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound912`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound914`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound915`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound916`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound918`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound92`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound920`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound921`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound922`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound923`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound924`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound926`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound927`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound928`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound93`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound930`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound931`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound932`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound933`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound934`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound935`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound936`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound938`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound939`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound94`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound940`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound941`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound943`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound944`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound946`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound947`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound948`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound949`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound950`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound951`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound952`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound953`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound954`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound955`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound956`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound957`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound958`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound960`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound961`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound963`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound964`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound965`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound966`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound968`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound969`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound97`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound970`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound971`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound972`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound973`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound974`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound976`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound977`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound978`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound979`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound98`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound980`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound982`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound983`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound984`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound986`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound988`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound989`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound990`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound991`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound992`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound993`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval106`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1074`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval109`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval116`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval117`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1192`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval12`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval120`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1210`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval124`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1254`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval130`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval133`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval134`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval141`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval143`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval145`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval146`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval147`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval149`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval155`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1553`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1554`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval159`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval164`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval165`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval167`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval173`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval174`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval18`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval181`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval182`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval185`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1852`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1853`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1882`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1913`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1914`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval202`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval203`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval207`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval21`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval214`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval215`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval218`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval220`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval224`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval225`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval226`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval229`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval231`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval234`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval235`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval242`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval243`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval245`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval249`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval255`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval257`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval258`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval263`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval270`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval271`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval273`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval278`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval280`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval285`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval286`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval287`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval292`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval296`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval301`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval308`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval310`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval323`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval325`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval331`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval332`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval334`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval335`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval343`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval344`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval348`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval353`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval358`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval359`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval366`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval368`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval37`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval370`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval371`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval372`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval373`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval377`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval380`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval383`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval389`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval39`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval391`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval394`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval401`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval403`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval408`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval41`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval413`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval414`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval444`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval46`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval475`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval476`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval477`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval52`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval54`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval56`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval6`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval63`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval69`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval73`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval74`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval77`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval79`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval8`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval83`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval86`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval91`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval99`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval113`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval119`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval147`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval150`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval208`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval21`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval215`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval216`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval220`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval222`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval271`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval359`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval360`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval362`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval373`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval375`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval384`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval44`, `OAI.MUB6.Certificate.PairSemantics.boundarySound165`, `OAI.MUB6.Certificate.PairSemantics.boundarySound243`, `OAI.MUB6.Certificate.PairSemantics.boundarySound248`, `OAI.MUB6.Certificate.PairSemantics.boundarySound249`, `OAI.MUB6.Certificate.PairSemantics.boundarySound250`, `OAI.MUB6.Certificate.PairSemantics.boundarySound252`, `OAI.MUB6.Certificate.PairSemantics.boundarySound261`, `OAI.MUB6.Certificate.PairSemantics.boundarySound264`, `OAI.MUB6.Certificate.PairSemantics.boundarySound305`, `OAI.MUB6.Certificate.PairSemantics.boundarySound347`, `OAI.MUB6.Certificate.PairSemantics.boundarySound377`, `OAI.MUB6.Certificate.PairSemantics.boundarySound445`, `OAI.MUB6.Certificate.PairSemantics.boundarySound454`, `OAI.MUB6.Certificate.PairSemantics.boundarySound49`, `OAI.MUB6.Certificate.PairSemantics.boundarySound51`, `OAI.MUB6.Certificate.PairSemantics.boundarySound56`, `OAI.MUB6.Certificate.PairSemantics.boundarySound7`, `OAI.MUB6.Certificate.PairSemantics.boundarySound73`, `OAI.MUB6.Certificate.PairSemantics.boundarySound75`, `OAI.MUB6.Certificate.PairSemantics.boundarySound83`, `OAI.MUB6.Certificate.PairSemantics.boundarySound97`, `OAI.MUB6.Certificate.PairSemantics.canonical7982`, `OAI.MUB6.Certificate.PairSemantics.canonical9056`, `OAI.MUB6.Certificate.PairSemantics.sound0`, `OAI.MUB6.Certificate.PairSemantics.sound1141`, `OAI.MUB6.Certificate.PairSemantics.sound1151`, `OAI.MUB6.Certificate.PairSemantics.sound1152`, `OAI.MUB6.Certificate.PairSemantics.sound117`, `OAI.MUB6.Certificate.PairSemantics.sound1381`, `OAI.MUB6.Certificate.PairSemantics.sound1383`, `OAI.MUB6.Certificate.PairSemantics.sound1384`, `OAI.MUB6.Certificate.PairSemantics.sound1387`, `OAI.MUB6.Certificate.PairSemantics.sound1390`, `OAI.MUB6.Certificate.PairSemantics.sound1391`, `OAI.MUB6.Certificate.PairSemantics.sound1392`, `OAI.MUB6.Certificate.PairSemantics.sound1395`, `OAI.MUB6.Certificate.PairSemantics.sound1399`, `OAI.MUB6.Certificate.PairSemantics.sound1414`, `OAI.MUB6.Certificate.PairSemantics.sound1419`, `OAI.MUB6.Certificate.PairSemantics.sound1423`, `OAI.MUB6.Certificate.PairSemantics.sound1424`, `OAI.MUB6.Certificate.PairSemantics.sound1425`, `OAI.MUB6.Certificate.PairSemantics.sound1432`, `OAI.MUB6.Certificate.PairSemantics.sound1434`, `OAI.MUB6.Certificate.PairSemantics.sound1437`, `OAI.MUB6.Certificate.PairSemantics.sound1443`, `OAI.MUB6.Certificate.PairSemantics.sound1458`, `OAI.MUB6.Certificate.PairSemantics.sound1486`, `OAI.MUB6.Certificate.PairSemantics.sound1500`, `OAI.MUB6.Certificate.PairSemantics.sound1504`, `OAI.MUB6.Certificate.PairSemantics.sound1506`, `OAI.MUB6.Certificate.PairSemantics.sound1512`, `OAI.MUB6.Certificate.PairSemantics.sound1518`, `OAI.MUB6.Certificate.PairSemantics.sound1520`, `OAI.MUB6.Certificate.PairSemantics.sound1523`, `OAI.MUB6.Certificate.PairSemantics.sound1530`, `OAI.MUB6.Certificate.PairSemantics.sound1531`, `OAI.MUB6.Certificate.PairSemantics.sound1533`, `OAI.MUB6.Certificate.PairSemantics.sound1535`, `OAI.MUB6.Certificate.PairSemantics.sound1540`, `OAI.MUB6.Certificate.PairSemantics.sound1548`, `OAI.MUB6.Certificate.PairSemantics.sound1552`, `OAI.MUB6.Certificate.PairSemantics.sound1563`, `OAI.MUB6.Certificate.PairSemantics.sound1585`, `OAI.MUB6.Certificate.PairSemantics.sound1605`, `OAI.MUB6.Certificate.PairSemantics.sound1614`, `OAI.MUB6.Certificate.PairSemantics.sound1617`, `OAI.MUB6.Certificate.PairSemantics.sound1624`, `OAI.MUB6.Certificate.PairSemantics.sound1625`, `OAI.MUB6.Certificate.PairSemantics.sound1627`, `OAI.MUB6.Certificate.PairSemantics.sound1628`, `OAI.MUB6.Certificate.PairSemantics.sound1631`, `OAI.MUB6.Certificate.PairSemantics.sound1634`, `OAI.MUB6.Certificate.PairSemantics.sound1635`, `OAI.MUB6.Certificate.PairSemantics.sound1637`, `OAI.MUB6.Certificate.PairSemantics.sound1638`, `OAI.MUB6.Certificate.PairSemantics.sound1643`, `OAI.MUB6.Certificate.PairSemantics.sound1646`, `OAI.MUB6.Certificate.PairSemantics.sound1648`, `OAI.MUB6.Certificate.PairSemantics.sound1652`, `OAI.MUB6.Certificate.PairSemantics.sound1668`, `OAI.MUB6.Certificate.PairSemantics.sound1669`, `OAI.MUB6.Certificate.PairSemantics.sound1682`, `OAI.MUB6.Certificate.PairSemantics.sound1685`, `OAI.MUB6.Certificate.PairSemantics.sound1686`, `OAI.MUB6.Certificate.PairSemantics.sound1707`, `OAI.MUB6.Certificate.PairSemantics.sound1716`, `OAI.MUB6.Certificate.PairSemantics.sound1718`, `OAI.MUB6.Certificate.PairSemantics.sound1736`, `OAI.MUB6.Certificate.PairSemantics.sound1739`, `OAI.MUB6.Certificate.PairSemantics.sound1768`, `OAI.MUB6.Certificate.PairSemantics.sound1769`, `OAI.MUB6.Certificate.PairSemantics.sound1770`, `OAI.MUB6.Certificate.PairSemantics.sound1774`, `OAI.MUB6.Certificate.PairSemantics.sound1784`, `OAI.MUB6.Certificate.PairSemantics.sound1793`, `OAI.MUB6.Certificate.PairSemantics.sound1800`, `OAI.MUB6.Certificate.PairSemantics.sound1803`, `OAI.MUB6.Certificate.PairSemantics.sound1826`, `OAI.MUB6.Certificate.PairSemantics.sound1828`, `OAI.MUB6.Certificate.PairSemantics.sound1830`, `OAI.MUB6.Certificate.PairSemantics.sound1849`, `OAI.MUB6.Certificate.PairSemantics.sound1858`, `OAI.MUB6.Certificate.PairSemantics.sound1860`, `OAI.MUB6.Certificate.PairSemantics.sound1865`, `OAI.MUB6.Certificate.PairSemantics.sound1866`, `OAI.MUB6.Certificate.PairSemantics.sound1867`, `OAI.MUB6.Certificate.PairSemantics.sound1869`, `OAI.MUB6.Certificate.PairSemantics.sound1870`, `OAI.MUB6.Certificate.PairSemantics.sound1872`, `OAI.MUB6.Certificate.PairSemantics.sound1873`, `OAI.MUB6.Certificate.PairSemantics.sound1879`, `OAI.MUB6.Certificate.PairSemantics.sound1885`, `OAI.MUB6.Certificate.PairSemantics.sound1890`, `OAI.MUB6.Certificate.PairSemantics.sound1938`, `OAI.MUB6.Certificate.PairSemantics.sound1968`, `OAI.MUB6.Certificate.PairSemantics.sound1977`, `OAI.MUB6.Certificate.PairSemantics.sound1978`, `OAI.MUB6.Certificate.PairSemantics.sound1980`, `OAI.MUB6.Certificate.PairSemantics.sound1986`, `OAI.MUB6.Certificate.PairSemantics.sound1987`, `OAI.MUB6.Certificate.PairSemantics.sound2041`, `OAI.MUB6.Certificate.PairSemantics.sound2058`, `OAI.MUB6.Certificate.PairSemantics.sound2106`, `OAI.MUB6.Certificate.PairSemantics.sound2108`, `OAI.MUB6.Certificate.PairSemantics.sound2113`, `OAI.MUB6.Certificate.PairSemantics.sound2117`, `OAI.MUB6.Certificate.PairSemantics.sound2122`, `OAI.MUB6.Certificate.PairSemantics.sound2123`, `OAI.MUB6.Certificate.PairSemantics.sound2128`, `OAI.MUB6.Certificate.PairSemantics.sound2132`, `OAI.MUB6.Certificate.PairSemantics.sound2152`, `OAI.MUB6.Certificate.PairSemantics.sound2168`, `OAI.MUB6.Certificate.PairSemantics.sound2175`, `OAI.MUB6.Certificate.PairSemantics.sound2177`, `OAI.MUB6.Certificate.PairSemantics.sound2183`, `OAI.MUB6.Certificate.PairSemantics.sound2190`, `OAI.MUB6.Certificate.PairSemantics.sound2192`, `OAI.MUB6.Certificate.PairSemantics.sound2197`, `OAI.MUB6.Certificate.PairSemantics.sound2201`, `OAI.MUB6.Certificate.PairSemantics.sound2202`, `OAI.MUB6.Certificate.PairSemantics.sound2204`, `OAI.MUB6.Certificate.PairSemantics.sound2213`, `OAI.MUB6.Certificate.PairSemantics.sound2216`, `OAI.MUB6.Certificate.PairSemantics.sound2228`, `OAI.MUB6.Certificate.PairSemantics.sound2243`, `OAI.MUB6.Certificate.PairSemantics.sound2244`, `OAI.MUB6.Certificate.PairSemantics.sound2262`, `OAI.MUB6.Certificate.PairSemantics.sound2284`, `OAI.MUB6.Certificate.PairSemantics.sound2285`, `OAI.MUB6.Certificate.PairSemantics.sound2286`, `OAI.MUB6.Certificate.PairSemantics.sound2293`, `OAI.MUB6.Certificate.PairSemantics.sound2294`, `OAI.MUB6.Certificate.PairSemantics.sound2295`, `OAI.MUB6.Certificate.PairSemantics.sound2296`, `OAI.MUB6.Certificate.PairSemantics.sound2298`, `OAI.MUB6.Certificate.PairSemantics.sound2304`, `OAI.MUB6.Certificate.PairSemantics.sound2307`, `OAI.MUB6.Certificate.PairSemantics.sound2312`, `OAI.MUB6.Certificate.PairSemantics.sound2315`, `OAI.MUB6.Certificate.PairSemantics.sound232`, `OAI.MUB6.Certificate.PairSemantics.sound2324`, `OAI.MUB6.Certificate.PairSemantics.sound2325`, `OAI.MUB6.Certificate.PairSemantics.sound2327`, `OAI.MUB6.Certificate.PairSemantics.sound2338`, `OAI.MUB6.Certificate.PairSemantics.sound2349`, `OAI.MUB6.Certificate.PairSemantics.sound2357`, `OAI.MUB6.Certificate.PairSemantics.sound2375`, `OAI.MUB6.Certificate.PairSemantics.sound2382`, `OAI.MUB6.Certificate.PairSemantics.sound2389`, `OAI.MUB6.Certificate.PairSemantics.sound2390`, `OAI.MUB6.Certificate.PairSemantics.sound2391`, `OAI.MUB6.Certificate.PairSemantics.sound2399`, `OAI.MUB6.Certificate.PairSemantics.sound2400`, `OAI.MUB6.Certificate.PairSemantics.sound2403`, `OAI.MUB6.Certificate.PairSemantics.sound2411`, `OAI.MUB6.Certificate.PairSemantics.sound2413`, `OAI.MUB6.Certificate.PairSemantics.sound2414`, `OAI.MUB6.Certificate.PairSemantics.sound2415`, `OAI.MUB6.Certificate.PairSemantics.sound2416`, `OAI.MUB6.Certificate.PairSemantics.sound2417`, `OAI.MUB6.Certificate.PairSemantics.sound2420`, `OAI.MUB6.Certificate.PairSemantics.sound2428`, `OAI.MUB6.Certificate.PairSemantics.sound2433`, `OAI.MUB6.Certificate.PairSemantics.sound2434`, `OAI.MUB6.Certificate.PairSemantics.sound2435`, `OAI.MUB6.Certificate.PairSemantics.sound2436`, `OAI.MUB6.Certificate.PairSemantics.sound2440`, `OAI.MUB6.Certificate.PairSemantics.sound2441`, `OAI.MUB6.Certificate.PairSemantics.sound2442`, `OAI.MUB6.Certificate.PairSemantics.sound2443`, `OAI.MUB6.Certificate.PairSemantics.sound2444`, `OAI.MUB6.Certificate.PairSemantics.sound2445`, `OAI.MUB6.Certificate.PairSemantics.sound2455`, `OAI.MUB6.Certificate.PairSemantics.sound2456`, `OAI.MUB6.Certificate.PairSemantics.sound2457`, `OAI.MUB6.Certificate.PairSemantics.sound2462`, `OAI.MUB6.Certificate.PairSemantics.sound2463`, `OAI.MUB6.Certificate.PairSemantics.sound2464`, `OAI.MUB6.Certificate.PairSemantics.sound2465`, `OAI.MUB6.Certificate.PairSemantics.sound2466`, `OAI.MUB6.Certificate.PairSemantics.sound2470`, `OAI.MUB6.Certificate.PairSemantics.sound2472`, `OAI.MUB6.Certificate.PairSemantics.sound2473`, `OAI.MUB6.Certificate.PairSemantics.sound2477`, `OAI.MUB6.Certificate.PairSemantics.sound2479`, `OAI.MUB6.Certificate.PairSemantics.sound2486`, `OAI.MUB6.Certificate.PairSemantics.sound2489`, `OAI.MUB6.Certificate.PairSemantics.sound2490`, `OAI.MUB6.Certificate.PairSemantics.sound2491`, `OAI.MUB6.Certificate.PairSemantics.sound2492`, `OAI.MUB6.Certificate.PairSemantics.sound2507`, `OAI.MUB6.Certificate.PairSemantics.sound2520`, `OAI.MUB6.Certificate.PairSemantics.sound2521`, `OAI.MUB6.Certificate.PairSemantics.sound2524`, `OAI.MUB6.Certificate.PairSemantics.sound2525`, `OAI.MUB6.Certificate.PairSemantics.sound2533`, `OAI.MUB6.Certificate.PairSemantics.sound2540`, `OAI.MUB6.Certificate.PairSemantics.sound2546`, `OAI.MUB6.Certificate.PairSemantics.sound2547`, `OAI.MUB6.Certificate.PairSemantics.sound2548`, `OAI.MUB6.Certificate.PairSemantics.sound2557`, `OAI.MUB6.Certificate.PairSemantics.sound2558`, `OAI.MUB6.Certificate.PairSemantics.sound2559`, `OAI.MUB6.Certificate.PairSemantics.sound2564`, `OAI.MUB6.Certificate.PairSemantics.sound2565`, `OAI.MUB6.Certificate.PairSemantics.sound2566`, `OAI.MUB6.Certificate.PairSemantics.sound2573`, `OAI.MUB6.Certificate.PairSemantics.sound2578`, `OAI.MUB6.Certificate.PairSemantics.sound2579`, `OAI.MUB6.Certificate.PairSemantics.sound2580`, `OAI.MUB6.Certificate.PairSemantics.sound2602`, `OAI.MUB6.Certificate.PairSemantics.sound2604`, `OAI.MUB6.Certificate.PairSemantics.sound2606`, `OAI.MUB6.Certificate.PairSemantics.sound2619`, `OAI.MUB6.Certificate.PairSemantics.sound2626`, `OAI.MUB6.Certificate.PairSemantics.sound2627`, `OAI.MUB6.Certificate.PairSemantics.sound2641`, `OAI.MUB6.Certificate.PairSemantics.sound2657`, `OAI.MUB6.Certificate.PairSemantics.sound2658`, `OAI.MUB6.Certificate.PairSemantics.sound2661`, `OAI.MUB6.Certificate.PairSemantics.sound2666`, `OAI.MUB6.Certificate.PairSemantics.sound2670`, `OAI.MUB6.Certificate.PairSemantics.sound2671`, `OAI.MUB6.Certificate.PairSemantics.sound2674`, `OAI.MUB6.Certificate.PairSemantics.sound2683`, `OAI.MUB6.Certificate.PairSemantics.sound2686`, `OAI.MUB6.Certificate.PairSemantics.sound2690`, `OAI.MUB6.Certificate.PairSemantics.sound2693`, `OAI.MUB6.Certificate.PairSemantics.sound2709`, `OAI.MUB6.Certificate.PairSemantics.sound2710`, `OAI.MUB6.Certificate.PairSemantics.sound2711`, `OAI.MUB6.Certificate.PairSemantics.sound2714`, `OAI.MUB6.Certificate.PairSemantics.sound2717`, `OAI.MUB6.Certificate.PairSemantics.sound2723`, `OAI.MUB6.Certificate.PairSemantics.sound2732`, `OAI.MUB6.Certificate.PairSemantics.sound2733`, `OAI.MUB6.Certificate.PairSemantics.sound2754`, `OAI.MUB6.Certificate.PairSemantics.sound2757`, `OAI.MUB6.Certificate.PairSemantics.sound2765`, `OAI.MUB6.Certificate.PairSemantics.sound2788`, `OAI.MUB6.Certificate.PairSemantics.sound2790`, `OAI.MUB6.Certificate.PairSemantics.sound2793`, `OAI.MUB6.Certificate.PairSemantics.sound2827`, `OAI.MUB6.Certificate.PairSemantics.sound2829`, `OAI.MUB6.Certificate.PairSemantics.sound2836`, `OAI.MUB6.Certificate.PairSemantics.sound2839`, `OAI.MUB6.Certificate.PairSemantics.sound284`, `OAI.MUB6.Certificate.PairSemantics.sound2845`, `OAI.MUB6.Certificate.PairSemantics.sound2850`, `OAI.MUB6.Certificate.PairSemantics.sound2852`, `OAI.MUB6.Certificate.PairSemantics.sound2854`, `OAI.MUB6.Certificate.PairSemantics.sound2855`, `OAI.MUB6.Certificate.PairSemantics.sound2863`, `OAI.MUB6.Certificate.PairSemantics.sound2864`, `OAI.MUB6.Certificate.PairSemantics.sound2865`, `OAI.MUB6.Certificate.PairSemantics.sound2866`, `OAI.MUB6.Certificate.PairSemantics.sound2867`, `OAI.MUB6.Certificate.PairSemantics.sound2868`, `OAI.MUB6.Certificate.PairSemantics.sound2872`, `OAI.MUB6.Certificate.PairSemantics.sound2873`, `OAI.MUB6.Certificate.PairSemantics.sound2874`, `OAI.MUB6.Certificate.PairSemantics.sound2875`, `OAI.MUB6.Certificate.PairSemantics.sound2878`, `OAI.MUB6.Certificate.PairSemantics.sound2879`, `OAI.MUB6.Certificate.PairSemantics.sound2880`, `OAI.MUB6.Certificate.PairSemantics.sound2881`, `OAI.MUB6.Certificate.PairSemantics.sound2882`, `OAI.MUB6.Certificate.PairSemantics.sound2883`, `OAI.MUB6.Certificate.PairSemantics.sound2884`, `OAI.MUB6.Certificate.PairSemantics.sound2886`, `OAI.MUB6.Certificate.PairSemantics.sound2887`, `OAI.MUB6.Certificate.PairSemantics.sound2888`, `OAI.MUB6.Certificate.PairSemantics.sound2889`, `OAI.MUB6.Certificate.PairSemantics.sound2890`, `OAI.MUB6.Certificate.PairSemantics.sound2891`, `OAI.MUB6.Certificate.PairSemantics.sound2892`, `OAI.MUB6.Certificate.PairSemantics.sound2894`, `OAI.MUB6.Certificate.PairSemantics.sound2895`, `OAI.MUB6.Certificate.PairSemantics.sound2896`, `OAI.MUB6.Certificate.PairSemantics.sound2897`, `OAI.MUB6.Certificate.PairSemantics.sound2898`, `OAI.MUB6.Certificate.PairSemantics.sound2899`, `OAI.MUB6.Certificate.PairSemantics.sound2900`, `OAI.MUB6.Certificate.PairSemantics.sound2901`, `OAI.MUB6.Certificate.PairSemantics.sound2902`, `OAI.MUB6.Certificate.PairSemantics.sound2903`, `OAI.MUB6.Certificate.PairSemantics.sound2906`, `OAI.MUB6.Certificate.PairSemantics.sound2909`, `OAI.MUB6.Certificate.PairSemantics.sound2910`, `OAI.MUB6.Certificate.PairSemantics.sound2912`, `OAI.MUB6.Certificate.PairSemantics.sound2913`, `OAI.MUB6.Certificate.PairSemantics.sound2914`, `OAI.MUB6.Certificate.PairSemantics.sound2915`, `OAI.MUB6.Certificate.PairSemantics.sound2916`, `OAI.MUB6.Certificate.PairSemantics.sound2917`, `OAI.MUB6.Certificate.PairSemantics.sound2918`, `OAI.MUB6.Certificate.PairSemantics.sound2919`, `OAI.MUB6.Certificate.PairSemantics.sound2920`, `OAI.MUB6.Certificate.PairSemantics.sound2922`, `OAI.MUB6.Certificate.PairSemantics.sound2924`, `OAI.MUB6.Certificate.PairSemantics.sound2927`, `OAI.MUB6.Certificate.PairSemantics.sound2928`, `OAI.MUB6.Certificate.PairSemantics.sound2929`, `OAI.MUB6.Certificate.PairSemantics.sound2930`, `OAI.MUB6.Certificate.PairSemantics.sound2931`, `OAI.MUB6.Certificate.PairSemantics.sound2933`, `OAI.MUB6.Certificate.PairSemantics.sound2934`, `OAI.MUB6.Certificate.PairSemantics.sound2935`, `OAI.MUB6.Certificate.PairSemantics.sound2936`, `OAI.MUB6.Certificate.PairSemantics.sound2939`, `OAI.MUB6.Certificate.PairSemantics.sound2940`, `OAI.MUB6.Certificate.PairSemantics.sound2941`, `OAI.MUB6.Certificate.PairSemantics.sound2943`, `OAI.MUB6.Certificate.PairSemantics.sound2944`, `OAI.MUB6.Certificate.PairSemantics.sound2947`, `OAI.MUB6.Certificate.PairSemantics.sound2948`, `OAI.MUB6.Certificate.PairSemantics.sound2949`, `OAI.MUB6.Certificate.PairSemantics.sound2950`, `OAI.MUB6.Certificate.PairSemantics.sound2952`, `OAI.MUB6.Certificate.PairSemantics.sound2953`, `OAI.MUB6.Certificate.PairSemantics.sound2954`, `OAI.MUB6.Certificate.PairSemantics.sound2955`, `OAI.MUB6.Certificate.PairSemantics.sound2956`, `OAI.MUB6.Certificate.PairSemantics.sound2957`, `OAI.MUB6.Certificate.PairSemantics.sound2958`, `OAI.MUB6.Certificate.PairSemantics.sound2959`, `OAI.MUB6.Certificate.PairSemantics.sound2960`, `OAI.MUB6.Certificate.PairSemantics.sound2962`, `OAI.MUB6.Certificate.PairSemantics.sound2964`, `OAI.MUB6.Certificate.PairSemantics.sound2965`, `OAI.MUB6.Certificate.PairSemantics.sound2966`, `OAI.MUB6.Certificate.PairSemantics.sound2967`, `OAI.MUB6.Certificate.PairSemantics.sound2968`, `OAI.MUB6.Certificate.PairSemantics.sound2969`, `OAI.MUB6.Certificate.PairSemantics.sound2970`, `OAI.MUB6.Certificate.PairSemantics.sound2972`, `OAI.MUB6.Certificate.PairSemantics.sound2973`, `OAI.MUB6.Certificate.PairSemantics.sound2974`, `OAI.MUB6.Certificate.PairSemantics.sound2975`, `OAI.MUB6.Certificate.PairSemantics.sound2976`, `OAI.MUB6.Certificate.PairSemantics.sound2977`, `OAI.MUB6.Certificate.PairSemantics.sound2979`, `OAI.MUB6.Certificate.PairSemantics.sound2980`, `OAI.MUB6.Certificate.PairSemantics.sound2982`, `OAI.MUB6.Certificate.PairSemantics.sound2985`, `OAI.MUB6.Certificate.PairSemantics.sound2986`, `OAI.MUB6.Certificate.PairSemantics.sound2987`, `OAI.MUB6.Certificate.PairSemantics.sound2988`, `OAI.MUB6.Certificate.PairSemantics.sound2989`, `OAI.MUB6.Certificate.PairSemantics.sound2990`, `OAI.MUB6.Certificate.PairSemantics.sound2991`, `OAI.MUB6.Certificate.PairSemantics.sound2993`, `OAI.MUB6.Certificate.PairSemantics.sound2994`, `OAI.MUB6.Certificate.PairSemantics.sound2996`, `OAI.MUB6.Certificate.PairSemantics.sound2997`, `OAI.MUB6.Certificate.PairSemantics.sound2998`, `OAI.MUB6.Certificate.PairSemantics.sound2999`, `OAI.MUB6.Certificate.PairSemantics.sound3000`, `OAI.MUB6.Certificate.PairSemantics.sound3001`, `OAI.MUB6.Certificate.PairSemantics.sound3002`, `OAI.MUB6.Certificate.PairSemantics.sound3004`, `OAI.MUB6.Certificate.PairSemantics.sound3006`, `OAI.MUB6.Certificate.PairSemantics.sound3009`, `OAI.MUB6.Certificate.PairSemantics.sound3010`, `OAI.MUB6.Certificate.PairSemantics.sound3011`, `OAI.MUB6.Certificate.PairSemantics.sound3012`, `OAI.MUB6.Certificate.PairSemantics.sound3013`, `OAI.MUB6.Certificate.PairSemantics.sound3014`, `OAI.MUB6.Certificate.PairSemantics.sound3015`, `OAI.MUB6.Certificate.PairSemantics.sound3016`, `OAI.MUB6.Certificate.PairSemantics.sound3017`, `OAI.MUB6.Certificate.PairSemantics.sound3018`, `OAI.MUB6.Certificate.PairSemantics.sound3019`, `OAI.MUB6.Certificate.PairSemantics.sound3020`, `OAI.MUB6.Certificate.PairSemantics.sound3021`, `OAI.MUB6.Certificate.PairSemantics.sound3022`, `OAI.MUB6.Certificate.PairSemantics.sound3023`, `OAI.MUB6.Certificate.PairSemantics.sound3024`, `OAI.MUB6.Certificate.PairSemantics.sound3025`, `OAI.MUB6.Certificate.PairSemantics.sound3026`, `OAI.MUB6.Certificate.PairSemantics.sound3027`, `OAI.MUB6.Certificate.PairSemantics.sound3028`, `OAI.MUB6.Certificate.PairSemantics.sound3029`, `OAI.MUB6.Certificate.PairSemantics.sound3030`, `OAI.MUB6.Certificate.PairSemantics.sound3031`, `OAI.MUB6.Certificate.PairSemantics.sound3032`, `OAI.MUB6.Certificate.PairSemantics.sound3033`, `OAI.MUB6.Certificate.PairSemantics.sound3034`, `OAI.MUB6.Certificate.PairSemantics.sound3035`, `OAI.MUB6.Certificate.PairSemantics.sound3036`, `OAI.MUB6.Certificate.PairSemantics.sound3038`, `OAI.MUB6.Certificate.PairSemantics.sound3039`, `OAI.MUB6.Certificate.PairSemantics.sound3040`, `OAI.MUB6.Certificate.PairSemantics.sound3041`, `OAI.MUB6.Certificate.PairSemantics.sound3042`, `OAI.MUB6.Certificate.PairSemantics.sound3043`, `OAI.MUB6.Certificate.PairSemantics.sound3044`, `OAI.MUB6.Certificate.PairSemantics.sound3045`, `OAI.MUB6.Certificate.PairSemantics.sound3047`, `OAI.MUB6.Certificate.PairSemantics.sound3048`, `OAI.MUB6.Certificate.PairSemantics.sound3049`, `OAI.MUB6.Certificate.PairSemantics.sound3050`, `OAI.MUB6.Certificate.PairSemantics.sound3051`, `OAI.MUB6.Certificate.PairSemantics.sound3053`, `OAI.MUB6.Certificate.PairSemantics.sound3054`, `OAI.MUB6.Certificate.PairSemantics.sound3056`, `OAI.MUB6.Certificate.PairSemantics.sound3058`, `OAI.MUB6.Certificate.PairSemantics.sound3059`, `OAI.MUB6.Certificate.PairSemantics.sound3060`, `OAI.MUB6.Certificate.PairSemantics.sound3061`, `OAI.MUB6.Certificate.PairSemantics.sound3062`, `OAI.MUB6.Certificate.PairSemantics.sound3063`, `OAI.MUB6.Certificate.PairSemantics.sound3065`, `OAI.MUB6.Certificate.PairSemantics.sound3066`, `OAI.MUB6.Certificate.PairSemantics.sound3067`, `OAI.MUB6.Certificate.PairSemantics.sound3068`, `OAI.MUB6.Certificate.PairSemantics.sound3069`, `OAI.MUB6.Certificate.PairSemantics.sound3071`, `OAI.MUB6.Certificate.PairSemantics.sound3072`, `OAI.MUB6.Certificate.PairSemantics.sound3073`, `OAI.MUB6.Certificate.PairSemantics.sound3074`, `OAI.MUB6.Certificate.PairSemantics.sound3075`, `OAI.MUB6.Certificate.PairSemantics.sound3076`, `OAI.MUB6.Certificate.PairSemantics.sound3077`, `OAI.MUB6.Certificate.PairSemantics.sound3078`, `OAI.MUB6.Certificate.PairSemantics.sound3079`, `OAI.MUB6.Certificate.PairSemantics.sound3080`, `OAI.MUB6.Certificate.PairSemantics.sound3081`, `OAI.MUB6.Certificate.PairSemantics.sound3082`, `OAI.MUB6.Certificate.PairSemantics.sound3083`, `OAI.MUB6.Certificate.PairSemantics.sound3084`, `OAI.MUB6.Certificate.PairSemantics.sound3085`, `OAI.MUB6.Certificate.PairSemantics.sound3086`, `OAI.MUB6.Certificate.PairSemantics.sound3090`, `OAI.MUB6.Certificate.PairSemantics.sound3091`, `OAI.MUB6.Certificate.PairSemantics.sound3092`, `OAI.MUB6.Certificate.PairSemantics.sound3093`, `OAI.MUB6.Certificate.PairSemantics.sound3094`, `OAI.MUB6.Certificate.PairSemantics.sound3095`, `OAI.MUB6.Certificate.PairSemantics.sound3096`, `OAI.MUB6.Certificate.PairSemantics.sound3097`, `OAI.MUB6.Certificate.PairSemantics.sound3098`, `OAI.MUB6.Certificate.PairSemantics.sound3099`, `OAI.MUB6.Certificate.PairSemantics.sound3100`, `OAI.MUB6.Certificate.PairSemantics.sound3101`, `OAI.MUB6.Certificate.PairSemantics.sound3102`, `OAI.MUB6.Certificate.PairSemantics.sound3105`, `OAI.MUB6.Certificate.PairSemantics.sound3106`, `OAI.MUB6.Certificate.PairSemantics.sound3107`, `OAI.MUB6.Certificate.PairSemantics.sound3108`, `OAI.MUB6.Certificate.PairSemantics.sound3109`, `OAI.MUB6.Certificate.PairSemantics.sound3110`, `OAI.MUB6.Certificate.PairSemantics.sound3111`, `OAI.MUB6.Certificate.PairSemantics.sound3112`, `OAI.MUB6.Certificate.PairSemantics.sound3113`, `OAI.MUB6.Certificate.PairSemantics.sound3114`, `OAI.MUB6.Certificate.PairSemantics.sound3115`, `OAI.MUB6.Certificate.PairSemantics.sound3116`, `OAI.MUB6.Certificate.PairSemantics.sound3118`, `OAI.MUB6.Certificate.PairSemantics.sound3119`, `OAI.MUB6.Certificate.PairSemantics.sound3120`, `OAI.MUB6.Certificate.PairSemantics.sound3121`, `OAI.MUB6.Certificate.PairSemantics.sound3122`, `OAI.MUB6.Certificate.PairSemantics.sound3123`, `OAI.MUB6.Certificate.PairSemantics.sound3124`, `OAI.MUB6.Certificate.PairSemantics.sound3125`, `OAI.MUB6.Certificate.PairSemantics.sound3128`, `OAI.MUB6.Certificate.PairSemantics.sound3129`, `OAI.MUB6.Certificate.PairSemantics.sound3130`, `OAI.MUB6.Certificate.PairSemantics.sound3131`, `OAI.MUB6.Certificate.PairSemantics.sound3133`, `OAI.MUB6.Certificate.PairSemantics.sound3135`, `OAI.MUB6.Certificate.PairSemantics.sound3136`, `OAI.MUB6.Certificate.PairSemantics.sound3138`, `OAI.MUB6.Certificate.PairSemantics.sound3139`, `OAI.MUB6.Certificate.PairSemantics.sound3140`, `OAI.MUB6.Certificate.PairSemantics.sound3141`, `OAI.MUB6.Certificate.PairSemantics.sound3142`, `OAI.MUB6.Certificate.PairSemantics.sound3144`, `OAI.MUB6.Certificate.PairSemantics.sound3145`, `OAI.MUB6.Certificate.PairSemantics.sound3146`, `OAI.MUB6.Certificate.PairSemantics.sound3150`, `OAI.MUB6.Certificate.PairSemantics.sound3151`, `OAI.MUB6.Certificate.PairSemantics.sound3152`, `OAI.MUB6.Certificate.PairSemantics.sound3153`, `OAI.MUB6.Certificate.PairSemantics.sound3155`, `OAI.MUB6.Certificate.PairSemantics.sound3158`, `OAI.MUB6.Certificate.PairSemantics.sound3159`, `OAI.MUB6.Certificate.PairSemantics.sound3160`, `OAI.MUB6.Certificate.PairSemantics.sound3161`, `OAI.MUB6.Certificate.PairSemantics.sound3162`, `OAI.MUB6.Certificate.PairSemantics.sound3163`, `OAI.MUB6.Certificate.PairSemantics.sound3164`, `OAI.MUB6.Certificate.PairSemantics.sound3166`, `OAI.MUB6.Certificate.PairSemantics.sound3167`, `OAI.MUB6.Certificate.PairSemantics.sound3168`, `OAI.MUB6.Certificate.PairSemantics.sound3169`, `OAI.MUB6.Certificate.PairSemantics.sound3170`, `OAI.MUB6.Certificate.PairSemantics.sound3171`, `OAI.MUB6.Certificate.PairSemantics.sound3172`, `OAI.MUB6.Certificate.PairSemantics.sound3173`, `OAI.MUB6.Certificate.PairSemantics.sound3174`, `OAI.MUB6.Certificate.PairSemantics.sound3176`, `OAI.MUB6.Certificate.PairSemantics.sound3178`, `OAI.MUB6.Certificate.PairSemantics.sound3179`, `OAI.MUB6.Certificate.PairSemantics.sound3180`, `OAI.MUB6.Certificate.PairSemantics.sound3181`, `OAI.MUB6.Certificate.PairSemantics.sound3183`, `OAI.MUB6.Certificate.PairSemantics.sound3184`, `OAI.MUB6.Certificate.PairSemantics.sound3185`, `OAI.MUB6.Certificate.PairSemantics.sound3186`, `OAI.MUB6.Certificate.PairSemantics.sound3187`, `OAI.MUB6.Certificate.PairSemantics.sound3188`, `OAI.MUB6.Certificate.PairSemantics.sound3189`, `OAI.MUB6.Certificate.PairSemantics.sound3191`, `OAI.MUB6.Certificate.PairSemantics.sound3192`, `OAI.MUB6.Certificate.PairSemantics.sound3193`, `OAI.MUB6.Certificate.PairSemantics.sound3194`, `OAI.MUB6.Certificate.PairSemantics.sound3195`, `OAI.MUB6.Certificate.PairSemantics.sound3196`, `OAI.MUB6.Certificate.PairSemantics.sound3197`, `OAI.MUB6.Certificate.PairSemantics.sound3198`, `OAI.MUB6.Certificate.PairSemantics.sound3199`, `OAI.MUB6.Certificate.PairSemantics.sound3200`, `OAI.MUB6.Certificate.PairSemantics.sound3201`, `OAI.MUB6.Certificate.PairSemantics.sound3202`, `OAI.MUB6.Certificate.PairSemantics.sound3203`, `OAI.MUB6.Certificate.PairSemantics.sound3204`, `OAI.MUB6.Certificate.PairSemantics.sound3205`, `OAI.MUB6.Certificate.PairSemantics.sound3206`, `OAI.MUB6.Certificate.PairSemantics.sound3208`, `OAI.MUB6.Certificate.PairSemantics.sound3211`, `OAI.MUB6.Certificate.PairSemantics.sound3212`, `OAI.MUB6.Certificate.PairSemantics.sound3213`, `OAI.MUB6.Certificate.PairSemantics.sound3214`, `OAI.MUB6.Certificate.PairSemantics.sound3215`, `OAI.MUB6.Certificate.PairSemantics.sound3216`, `OAI.MUB6.Certificate.PairSemantics.sound3217`, `OAI.MUB6.Certificate.PairSemantics.sound3218`, `OAI.MUB6.Certificate.PairSemantics.sound3219`, `OAI.MUB6.Certificate.PairSemantics.sound3221`, `OAI.MUB6.Certificate.PairSemantics.sound3222`, `OAI.MUB6.Certificate.PairSemantics.sound3223`, `OAI.MUB6.Certificate.PairSemantics.sound3224`, `OAI.MUB6.Certificate.PairSemantics.sound3226`, `OAI.MUB6.Certificate.PairSemantics.sound3227`, `OAI.MUB6.Certificate.PairSemantics.sound3228`, `OAI.MUB6.Certificate.PairSemantics.sound3230`, `OAI.MUB6.Certificate.PairSemantics.sound3231`, `OAI.MUB6.Certificate.PairSemantics.sound3233`, `OAI.MUB6.Certificate.PairSemantics.sound3234`, `OAI.MUB6.Certificate.PairSemantics.sound3235`, `OAI.MUB6.Certificate.PairSemantics.sound3237`, `OAI.MUB6.Certificate.PairSemantics.sound3238`, `OAI.MUB6.Certificate.PairSemantics.sound3239`, `OAI.MUB6.Certificate.PairSemantics.sound3240`, `OAI.MUB6.Certificate.PairSemantics.sound3241`, `OAI.MUB6.Certificate.PairSemantics.sound3242`, `OAI.MUB6.Certificate.PairSemantics.sound3243`, `OAI.MUB6.Certificate.PairSemantics.sound3244`, `OAI.MUB6.Certificate.PairSemantics.sound3246`, `OAI.MUB6.Certificate.PairSemantics.sound3247`, `OAI.MUB6.Certificate.PairSemantics.sound3248`, `OAI.MUB6.Certificate.PairSemantics.sound3249`, `OAI.MUB6.Certificate.PairSemantics.sound3250`, `OAI.MUB6.Certificate.PairSemantics.sound3251`, `OAI.MUB6.Certificate.PairSemantics.sound3253`, `OAI.MUB6.Certificate.PairSemantics.sound3254`, `OAI.MUB6.Certificate.PairSemantics.sound3255`, `OAI.MUB6.Certificate.PairSemantics.sound3256`, `OAI.MUB6.Certificate.PairSemantics.sound3258`, `OAI.MUB6.Certificate.PairSemantics.sound3259`, `OAI.MUB6.Certificate.PairSemantics.sound3261`, `OAI.MUB6.Certificate.PairSemantics.sound3262`, `OAI.MUB6.Certificate.PairSemantics.sound3263`, `OAI.MUB6.Certificate.PairSemantics.sound3266`, `OAI.MUB6.Certificate.PairSemantics.sound3267`, `OAI.MUB6.Certificate.PairSemantics.sound3268`, `OAI.MUB6.Certificate.PairSemantics.sound3269`, `OAI.MUB6.Certificate.PairSemantics.sound3270`, `OAI.MUB6.Certificate.PairSemantics.sound3271`, `OAI.MUB6.Certificate.PairSemantics.sound3273`, `OAI.MUB6.Certificate.PairSemantics.sound3275`, `OAI.MUB6.Certificate.PairSemantics.sound3276`, `OAI.MUB6.Certificate.PairSemantics.sound3277`, `OAI.MUB6.Certificate.PairSemantics.sound3279`, `OAI.MUB6.Certificate.PairSemantics.sound3280`, `OAI.MUB6.Certificate.PairSemantics.sound3281`, `OAI.MUB6.Certificate.PairSemantics.sound3282`, `OAI.MUB6.Certificate.PairSemantics.sound3283`, `OAI.MUB6.Certificate.PairSemantics.sound3284`, `OAI.MUB6.Certificate.PairSemantics.sound3288`, `OAI.MUB6.Certificate.PairSemantics.sound3289`, `OAI.MUB6.Certificate.PairSemantics.sound3290`, `OAI.MUB6.Certificate.PairSemantics.sound3291`, `OAI.MUB6.Certificate.PairSemantics.sound3292`, `OAI.MUB6.Certificate.PairSemantics.sound3293`, `OAI.MUB6.Certificate.PairSemantics.sound3294`, `OAI.MUB6.Certificate.PairSemantics.sound3295`, `OAI.MUB6.Certificate.PairSemantics.sound3296`, `OAI.MUB6.Certificate.PairSemantics.sound3297`, `OAI.MUB6.Certificate.PairSemantics.sound3298`, `OAI.MUB6.Certificate.PairSemantics.sound3299`, `OAI.MUB6.Certificate.PairSemantics.sound3300`, `OAI.MUB6.Certificate.PairSemantics.sound3301`, `OAI.MUB6.Certificate.PairSemantics.sound3302`, `OAI.MUB6.Certificate.PairSemantics.sound3304`, `OAI.MUB6.Certificate.PairSemantics.sound3305`, `OAI.MUB6.Certificate.PairSemantics.sound3307`, `OAI.MUB6.Certificate.PairSemantics.sound3308`, `OAI.MUB6.Certificate.PairSemantics.sound3310`, `OAI.MUB6.Certificate.PairSemantics.sound3311`, `OAI.MUB6.Certificate.PairSemantics.sound3312`, `OAI.MUB6.Certificate.PairSemantics.sound3313`, `OAI.MUB6.Certificate.PairSemantics.sound3314`, `OAI.MUB6.Certificate.PairSemantics.sound3315`, `OAI.MUB6.Certificate.PairSemantics.sound3316`, `OAI.MUB6.Certificate.PairSemantics.sound3317`, `OAI.MUB6.Certificate.PairSemantics.sound3319`, `OAI.MUB6.Certificate.PairSemantics.sound3322`, `OAI.MUB6.Certificate.PairSemantics.sound3323`, `OAI.MUB6.Certificate.PairSemantics.sound3324`, `OAI.MUB6.Certificate.PairSemantics.sound3325`, `OAI.MUB6.Certificate.PairSemantics.sound3327`, `OAI.MUB6.Certificate.PairSemantics.sound3328`, `OAI.MUB6.Certificate.PairSemantics.sound3332`, `OAI.MUB6.Certificate.PairSemantics.sound3333`, `OAI.MUB6.Certificate.PairSemantics.sound3334`, `OAI.MUB6.Certificate.PairSemantics.sound3335`, `OAI.MUB6.Certificate.PairSemantics.sound3336`, `OAI.MUB6.Certificate.PairSemantics.sound3338`, `OAI.MUB6.Certificate.PairSemantics.sound3340`, `OAI.MUB6.Certificate.PairSemantics.sound3341`, `OAI.MUB6.Certificate.PairSemantics.sound3342`, `OAI.MUB6.Certificate.PairSemantics.sound3343`, `OAI.MUB6.Certificate.PairSemantics.sound3344`, `OAI.MUB6.Certificate.PairSemantics.sound3345`, `OAI.MUB6.Certificate.PairSemantics.sound3346`, `OAI.MUB6.Certificate.PairSemantics.sound3347`, `OAI.MUB6.Certificate.PairSemantics.sound3348`, `OAI.MUB6.Certificate.PairSemantics.sound3349`, `OAI.MUB6.Certificate.PairSemantics.sound3350`, `OAI.MUB6.Certificate.PairSemantics.sound3351`, `OAI.MUB6.Certificate.PairSemantics.sound3352`, `OAI.MUB6.Certificate.PairSemantics.sound3353`, `OAI.MUB6.Certificate.PairSemantics.sound3354`, `OAI.MUB6.Certificate.PairSemantics.sound3355`, `OAI.MUB6.Certificate.PairSemantics.sound3356`, `OAI.MUB6.Certificate.PairSemantics.sound3357`, `OAI.MUB6.Certificate.PairSemantics.sound3359`, `OAI.MUB6.Certificate.PairSemantics.sound3360`, `OAI.MUB6.Certificate.PairSemantics.sound3361`, `OAI.MUB6.Certificate.PairSemantics.sound3362`, `OAI.MUB6.Certificate.PairSemantics.sound3364`, `OAI.MUB6.Certificate.PairSemantics.sound3365`, `OAI.MUB6.Certificate.PairSemantics.sound3366`, `OAI.MUB6.Certificate.PairSemantics.sound3367`, `OAI.MUB6.Certificate.PairSemantics.sound3369`, `OAI.MUB6.Certificate.PairSemantics.sound3370`, `OAI.MUB6.Certificate.PairSemantics.sound3371`, `OAI.MUB6.Certificate.PairSemantics.sound3372`, `OAI.MUB6.Certificate.PairSemantics.sound3373`, `OAI.MUB6.Certificate.PairSemantics.sound3375`, `OAI.MUB6.Certificate.PairSemantics.sound3376`, `OAI.MUB6.Certificate.PairSemantics.sound3377`, `OAI.MUB6.Certificate.PairSemantics.sound3378`, `OAI.MUB6.Certificate.PairSemantics.sound3380`, `OAI.MUB6.Certificate.PairSemantics.sound3381`, `OAI.MUB6.Certificate.PairSemantics.sound3382`, `OAI.MUB6.Certificate.PairSemantics.sound3383`, `OAI.MUB6.Certificate.PairSemantics.sound3384`, `OAI.MUB6.Certificate.PairSemantics.sound3385`, `OAI.MUB6.Certificate.PairSemantics.sound3388`, `OAI.MUB6.Certificate.PairSemantics.sound3390`, `OAI.MUB6.Certificate.PairSemantics.sound3391`, `OAI.MUB6.Certificate.PairSemantics.sound3392`, `OAI.MUB6.Certificate.PairSemantics.sound3393`, `OAI.MUB6.Certificate.PairSemantics.sound3394`, `OAI.MUB6.Certificate.PairSemantics.sound3395`, `OAI.MUB6.Certificate.PairSemantics.sound3396`, `OAI.MUB6.Certificate.PairSemantics.sound3399`, `OAI.MUB6.Certificate.PairSemantics.sound3400`, `OAI.MUB6.Certificate.PairSemantics.sound3401`, `OAI.MUB6.Certificate.PairSemantics.sound3402`, `OAI.MUB6.Certificate.PairSemantics.sound3405`, `OAI.MUB6.Certificate.PairSemantics.sound3407`, `OAI.MUB6.Certificate.PairSemantics.sound3408`, `OAI.MUB6.Certificate.PairSemantics.sound3411`, `OAI.MUB6.Certificate.PairSemantics.sound3412`, `OAI.MUB6.Certificate.PairSemantics.sound3413`, `OAI.MUB6.Certificate.PairSemantics.sound3414`, `OAI.MUB6.Certificate.PairSemantics.sound3415`, `OAI.MUB6.Certificate.PairSemantics.sound3416`, `OAI.MUB6.Certificate.PairSemantics.sound3417`, `OAI.MUB6.Certificate.PairSemantics.sound3418`, `OAI.MUB6.Certificate.PairSemantics.sound3420`, `OAI.MUB6.Certificate.PairSemantics.sound3421`, `OAI.MUB6.Certificate.PairSemantics.sound3422`, `OAI.MUB6.Certificate.PairSemantics.sound3423`, `OAI.MUB6.Certificate.PairSemantics.sound3424`, `OAI.MUB6.Certificate.PairSemantics.sound3425`, `OAI.MUB6.Certificate.PairSemantics.sound3426`, `OAI.MUB6.Certificate.PairSemantics.sound3428`, `OAI.MUB6.Certificate.PairSemantics.sound3431`, `OAI.MUB6.Certificate.PairSemantics.sound3433`, `OAI.MUB6.Certificate.PairSemantics.sound3434`, `OAI.MUB6.Certificate.PairSemantics.sound3435`, `OAI.MUB6.Certificate.PairSemantics.sound3436`, `OAI.MUB6.Certificate.PairSemantics.sound3437`, `OAI.MUB6.Certificate.PairSemantics.sound3438`, `OAI.MUB6.Certificate.PairSemantics.sound3439`, `OAI.MUB6.Certificate.PairSemantics.sound3440`, `OAI.MUB6.Certificate.PairSemantics.sound3441`, `OAI.MUB6.Certificate.PairSemantics.sound3445`, `OAI.MUB6.Certificate.PairSemantics.sound3447`, `OAI.MUB6.Certificate.PairSemantics.sound3449`, `OAI.MUB6.Certificate.PairSemantics.sound3454`, `OAI.MUB6.Certificate.PairSemantics.sound3456`, `OAI.MUB6.Certificate.PairSemantics.sound3457`, `OAI.MUB6.Certificate.PairSemantics.sound3458`, `OAI.MUB6.Certificate.PairSemantics.sound3459`, `OAI.MUB6.Certificate.PairSemantics.sound3460`, `OAI.MUB6.Certificate.PairSemantics.sound3461`, `OAI.MUB6.Certificate.PairSemantics.sound3462`, `OAI.MUB6.Certificate.PairSemantics.sound3463`, `OAI.MUB6.Certificate.PairSemantics.sound3467`, `OAI.MUB6.Certificate.PairSemantics.sound3468`, `OAI.MUB6.Certificate.PairSemantics.sound381`, `OAI.MUB6.Certificate.PairSemantics.sound46`, `OAI.MUB6.Certificate.PairSemantics.sound5`, `OAI.MUB6.Certificate.PairSemantics.sound545`, `OAI.MUB6.Certificate.PairSemantics.sound659`, `OAI.MUB6.Certificate.PairSemantics.sound856`, `OAI.MUB6.Certificate.PairSemantics.sound858`, `OAI.MUB6.Certificate.PairSourceBridge.allRowsSound`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound0`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound1`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound10`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound100`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound101`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound102`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound103`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound104`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound105`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound106`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound107`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound108`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound111`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound112`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound113`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound114`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound115`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound116`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound117`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound118`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound119`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound12`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound120`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound121`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound124`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound125`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound126`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound127`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound128`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound129`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound13`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound130`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound131`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound132`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound133`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound134`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound135`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound136`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound137`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound139`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound14`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound140`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound141`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound142`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound146`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound148`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound15`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound150`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound151`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound153`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound154`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound155`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound156`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound157`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound158`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound159`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound16`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound160`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound161`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound162`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound163`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound164`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound165`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound166`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound167`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound168`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound169`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound17`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound170`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound171`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound173`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound174`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound175`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound176`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound177`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound178`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound179`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound18`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound180`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound181`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound182`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound183`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound184`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound185`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound186`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound187`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound188`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound19`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound190`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound191`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound192`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound193`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound194`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound195`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound196`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound197`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound198`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound199`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound2`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound20`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound200`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound201`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound202`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound203`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound204`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound205`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound207`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound208`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound209`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound21`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound210`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound211`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound212`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound213`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound214`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound215`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound216`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound217`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound218`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound219`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound22`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound220`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound221`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound222`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound223`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound224`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound225`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound226`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound227`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound228`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound229`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound23`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound230`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound231`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound232`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound233`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound234`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound235`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound236`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound237`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound238`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound239`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound24`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound240`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound241`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound242`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound243`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound244`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound245`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound246`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound248`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound249`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound25`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound250`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound253`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound254`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound26`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound27`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound28`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound3`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound30`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound31`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound32`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound34`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound35`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound36`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound38`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound39`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound4`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound40`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound41`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound42`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound43`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound44`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound45`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound46`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound47`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound49`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound5`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound51`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound52`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound53`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound54`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound56`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound57`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound58`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound59`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound6`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound60`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound61`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound62`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound63`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound64`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound65`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound66`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound67`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound69`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound70`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound72`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound74`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound76`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound77`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound78`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound79`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound8`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound80`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound81`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound82`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound83`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound84`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound85`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound86`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound87`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound89`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound9`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound90`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound91`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound92`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound93`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound94`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound95`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound96`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound97`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound98`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound99`, `OAI.MUB6.Certificate.PairTargetSemantics.certificate_zero1`, `OAI.MUB6.Certificate.PairTargetSemantics.expandedIdentity0`, `OAI.MUB6.Certificate.PairTargetSemantics.partition12`, `OAI.MUB6.Certificate.PairTargetSemantics.partition14`, `OAI.MUB6.Certificate.PairTargetSemantics.partition16`, `OAI.MUB6.Certificate.PairTargetSemantics.partition19`, `OAI.MUB6.Certificate.PairTargetSemantics.partition24`, `OAI.MUB6.Certificate.PairTargetSemantics.partition25`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm1`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm10`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm11`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm13`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm15`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm17`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm18`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm20`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm21`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm23`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm26`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm6`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm7`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm8` and `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm9`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw9Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw9step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw9step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw97Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw97step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw97step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw98 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw98Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw98step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw98step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw98step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw98step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw99 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw99Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw99step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw99step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw978Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw978step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw978step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw978step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw979 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw979Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw979step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw980 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw980Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw980step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw980step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw980step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw980step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw980step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw981 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw981Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw981step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw981step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw981step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw982 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw982Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw982step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw983 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw983Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw983step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw983step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw983step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw983step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw983step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw983step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw984 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw984Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw984step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw984step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw984step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw985 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw985Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw985step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw986 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw986Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw986step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw986step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw986step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw986step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw986step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw987 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-2, 4, -2]]
def raw987Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw987step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw987step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw987step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw987step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw988 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-2, 4, -2]]
def raw988Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw988step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw988step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw989 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-2, 4, -2]]
def raw989Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw989step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw989step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw989step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw989step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw989step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw989step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw990 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw990Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw990step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw990step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw990step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw991 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw991Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw991step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw992 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw992Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw992step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw992step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw992step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw992step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw992step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw993 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw993Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw993step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw993step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw993step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw994 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw994Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw994step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw995 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw995Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw995step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw995step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw995step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw995step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw995step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw996 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw996Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw996step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw996step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw996step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw996step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw997 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw997Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw997step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw997step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw998 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw998Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw998step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw998step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw998step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw998step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw998step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw998step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw999 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![-2, 2, 0], ![1, 2, -3]]
def raw999Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw999step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw999step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw999step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw999step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw9786step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]

def raw9786step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw9786step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9787Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9787step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw9787step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9787step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw9787step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9788Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9788step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9788step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw9788step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9788step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9788step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw9789Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw9789step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9789step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw9789step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9789step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw9789step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9790Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9790step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9790step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw9790step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9790step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9790step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9790step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9790step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9791Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9791step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9791step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9791step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9791step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9791step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9791step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9792Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9792step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9792step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9792step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9792step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9792step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9792step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9792step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9793Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9793step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9793step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw9793step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9793step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9793step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9793step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9793step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9794Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9794step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9794step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw9794step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9794step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw9794step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9794step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw9794step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9795Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9795step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9795step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw9795step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9795step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw9795step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9795step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw9795step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9796Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9796step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw9796step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9796step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw9796step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9796step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw9796step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9797Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9797step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9797step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw9797step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9797step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw9797step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9797step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw9797step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9798Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9798step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9798step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9798step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9798step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9798step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9798step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9798step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9798step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9799Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9799step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9799step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw9799step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9799step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw9799step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9799step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw9799step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9800Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9800step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9800step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9800step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9800step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9800step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9800step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9801Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9801step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw9801step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9801step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9801step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9801step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9801step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9802Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9802step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9802step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9802step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9802step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9802step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9802step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9803Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9803step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw9803step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9803step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9803step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9803step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9803step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9804Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9804step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw9804step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9804step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw9804step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9804step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw9804step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9805Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9805step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9805step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw9805step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9805step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9805step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9805step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9805step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9806Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9806step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9806step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw9806step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9806step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9806step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9806step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9806step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9807Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9807step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9807step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9807step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9807step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9807step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9807step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9808Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9808step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9808step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9808step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw9808step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9808step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9808step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9808step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9808step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9809Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9809step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9809step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw9809step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9809step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw9809step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9809step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw9809step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9810Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9810step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9810step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw9810step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9810step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw9810step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9810step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw9810step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9811Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9811step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9811step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw9811step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9811step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw9811step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9811step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw9811step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9812Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9812step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw9812step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9812step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw9812step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9812step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw9812step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9813Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9813step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9813step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw9813step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9813step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw9813step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9813step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw9813step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw9814Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9814step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw9814step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9814step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9814step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9814step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9814step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9814step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9814step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9815Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9815step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9815step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw9815step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9815step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw9815step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9815step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw9815step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9816Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9816step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9816step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9816step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw9816step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9816step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw9816step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9817Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9817step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9817step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9817step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9817step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9818Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9818step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9818step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw9818step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9818step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9818step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9818step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9818step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw9819Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw9819step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9819step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9819step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9819step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9819step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9820Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9820step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9820step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9820step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9821Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9821step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9822Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9822step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9822step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9823Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9823step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9823step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9823step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9823step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9824Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9824step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9824step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw9824step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9825Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9825step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9825step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw9825step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9826 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![-1, 1], ![1, -1], ![1, -1]]
def raw9826Labels : Fin 2 → Fin 2 := ![0, 1]

def raw9826step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![1, -1], ![1, -1]]
def raw9826step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw9826step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw9826step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw9827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9827Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9827step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9827step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9827step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9827step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9828Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9828step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9828step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9829Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9829step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9829step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9830Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9830step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9830step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9830step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw9830step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9831Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9831step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9831step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw9831step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9832Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9832step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9832step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9833Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9833step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9833step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9833step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9834Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9834step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9834step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9834step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9835Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9835step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9835step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw9835step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9836Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9836step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9836step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9837Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9837step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9838Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9838step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9838step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9839Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9839step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9839step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9840Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9840step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9840step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9841Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9841step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw9841step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9842Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9842step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw9842step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9843Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9843step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9843step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9844Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9844step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9844step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw9844step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9845Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9845step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9845step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw9845step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw9846Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9846step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw9846step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9846step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9846step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw9847Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw9847step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9848Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9848step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9848step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9848step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9848step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9848step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9849Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9849step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9849step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9849step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9849step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9850Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9850step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9850step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9850step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9850step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9850step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw9851Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw9851step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9851step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9851step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9851step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9851step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9851step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9851step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9852Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9852step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9852step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9852step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9852step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9853Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9853step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9853step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9853step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9853step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9854Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9854step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9854step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9854step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9854step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw9855Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9855step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw9855step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9855step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9855step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9855step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9855step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw9856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9856Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9856step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9856step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9856step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9856step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9856step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9856step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9857Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9857step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9857step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9857step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9857step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9857step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9857step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9858Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9858step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9858step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9858step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9858step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw9859Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9859step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9859step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9859step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9859step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9859step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9859step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9859step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9859step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9860Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9860step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9860step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw9860step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9860step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw9860step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9861Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9861step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9861step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9861step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9861step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9861step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9862Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9862step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw9862step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9862step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw9862step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9863Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9863step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9863step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9863step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw9863step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9863step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw9863step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9864Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9864step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9864step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw9864step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9864step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw9864step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9865Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9865step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9865step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw9865step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9865step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw9865step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9865step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw9865step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9866Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9866step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw9866step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9866step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw9866step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9867Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9867step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9867step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw9867step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9867step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw9867step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw9868Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw9868step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9868step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw9868step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9868step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw9868step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9868step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw9868step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw9869Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw9869step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9869step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw9869step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9870Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9870step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9870step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9870step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9871Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9871step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9871step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9872Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9872step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9872step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9872step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw9873Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw9873step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9873step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9873step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9873step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9873step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9874Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9874step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9874step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9875Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9875step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9875step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9876Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9876step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9876step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw9877Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw9877step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9877step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9877step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9878Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9878step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9878step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9878step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9879Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9879step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9879step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9879step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9880Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9880step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9880step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw9881Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9881step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9881step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9881step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9881step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9881step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9882Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9882step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9882step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw9882step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9883Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9883step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9883step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9883step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9884Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9884step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw9884step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9885Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9885step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9885step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw9885step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9886Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9886step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9886step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9886step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw9886step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9887Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9887step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9887step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw9887step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9887step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw9887step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9888Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9888step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw9888step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9889Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9889step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9889step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw9889step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw9890Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9890step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw9890step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9890step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw9890step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9890step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw9890step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9891 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9891Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9891step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9891step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9891step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9891step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9891step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9891step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9891step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9892 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9892Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9892step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9892step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9892step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9892step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9893 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9893Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9893step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9893step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9893step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9893step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9893step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9894 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9894Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9894step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9894step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9894step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9894step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9894step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9895 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw9895Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw9895step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9895step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9895step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9895step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9895step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9896 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9896Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9896step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9896step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw9896step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9896step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9896step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9896step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9896step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9897 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9897Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9897step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw9897step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9897step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw9897step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9898 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9898Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9898step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9898step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw9898step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9898step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw9898step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9899 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9899Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9899step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9899step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9899step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9899step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9899step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9900 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw9900Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw9900step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9900step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw9900step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9900step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw9900step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9901 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9901Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9901step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9901step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9901step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9901step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9901step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9901step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9902 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9902Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9902step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9902step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9902step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9902step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9902step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9903 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9903Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9903step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9903step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9903step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9903step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9904 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9904Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9904step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9904step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9904step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9904step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9905 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw9905Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9905step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9905step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9905step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9905step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9906 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9906Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9906step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9906step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9906step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9906step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9906step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9906step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9906step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9907 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9907Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9907step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9907step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9907step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9907step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9907step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9907step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9908 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw9908Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9908step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw9908step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9908step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw9908step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9908step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw9908step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9908step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw9908step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9909 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw9909Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9909step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9909step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9909step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9909step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9910 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw9910Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw9910step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9910step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9910step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9910step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9910step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9911 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9911Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9911step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9911step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9911step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9911step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9911step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw9911step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9911step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw9911step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9912 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9912Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9912step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9912step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9912step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9912step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9912step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9912step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9912step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9913 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9913Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9913step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw9913step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9913step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw9913step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9914 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9914Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9914step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9914step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9914step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw9914step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9914step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw9914step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9915 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9915Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9915step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9915step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9915step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9915step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9915step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9915step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9916 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9916Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9916step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9916step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9917 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9917Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9917step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9917step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9917step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9918 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9918Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9918step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9918step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9918step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9919 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw9919Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw9919step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9919step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9919step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9920 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9920Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9920step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9920step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw9920step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9921 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9921Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9921step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw9921step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9922 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9922Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9922step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9922step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw9922step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9923 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9923Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9923step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9923step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9923step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9924 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw9924Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9924step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw9924step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9924step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw9924step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9925 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9925Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9925step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9925step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9926 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9926Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9926step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9926step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9926step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9927 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9927Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9927step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9927step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9928 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9928Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9928step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9928step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9929 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw9929Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9929step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9929step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9930 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9930Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9930step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9930step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9930step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9930step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9930step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9931 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9931Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9931step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9931step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9931step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9932 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw9932Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw9932step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9932step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9932step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9933 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw9933Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9933step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9933step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9934 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw9934Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw9934step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9934step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9934step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9935 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9935Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9935step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9935step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw9935step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9936 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9936Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9936step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9936step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9936step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9936step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9936step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9937 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9937Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9937step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw9937step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9938 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9938Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9938step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9938step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw9938step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9939 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9939Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9939step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9939step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9939step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9939step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9939step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9939step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9939step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9940 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9940Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9940step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9940step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9940step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9940step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9941 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9941Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9941step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9941step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9941step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9941step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9941step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9942 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9942Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9942step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9942step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9942step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9942step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9942step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9943 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw9943Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw9943step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9943step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9943step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9943step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9943step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9944 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9944Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9944step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9944step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9944step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw9944step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9944step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9944step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9944step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9944step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9945 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9945Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9945step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9945step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9945step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9945step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9946 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9946Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9946step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9946step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9946step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9946step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9946step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9947 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9947Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9947step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9947step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9947step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9947step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9947step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9948 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw9948Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw9948step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9948step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9948step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9948step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9948step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9949 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9949Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9949step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw9949step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9949step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw9949step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9949step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw9949step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9950 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9950Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9950step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9950step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9950step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9950step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9950step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9951 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9951Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9951step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9951step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9951step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9951step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9952 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9952Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9952step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9952step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9952step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9952step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9953 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw9953Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9953step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9953step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9953step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9953step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9954 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9954Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9954step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9954step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9954step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9954step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw9954step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9954step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw9954step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9955 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9955Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9955step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9955step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9955step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9955step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9955step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9955step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9956 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw9956Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9956step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw9956step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9956step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw9956step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9956step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9956step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9956step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9956step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9957 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw9957Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9957step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw9957step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9957step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw9957step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9958 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw9958Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw9958step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9958step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw9958step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9958step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw9958step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9959 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9959Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9959step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9959step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw9959step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9959step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw9959step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9959step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw9959step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9960 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9960Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9960step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9960step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9960step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9960step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9960step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9960step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9960step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9961 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9961Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9961step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9961step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9961step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9961step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9962 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9962Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9962step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9962step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw9962step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9962step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw9962step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9963 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9963Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9963step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9963step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9963step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9963step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9963step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9964 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9964Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9964step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9964step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw9964step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9964step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9964step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9965 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9965Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9965step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9965step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9965step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9965step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9966 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9966Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9966step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9966step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9966step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9966step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9966step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9966step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9966step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9967 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw9967Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw9967step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9967step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw9967step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9967step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw9967step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9968 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9968Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9968step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9968step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9968step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9968step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9968step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw9968step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9969Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9969step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9969step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9969step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw9969step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9969step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9969step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9970Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9970step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9970step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9971Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9971step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9971step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9971step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw9972Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw9972step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9972step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw9972step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9972step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw9972step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9972step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw9972step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw9973Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw9973step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9973step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw9973step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9973step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9973step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9973step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9973step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9974Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9974step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9974step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw9974step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9975Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9975step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw9975step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9976Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9976step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9976step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw9976step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw9977Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw9977step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9977step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw9977step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9977step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9977step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw9978Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw9978step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9978step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9978step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9979Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9979step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw9979step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9980Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9980step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw9980step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9981Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9981step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw9981step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw9982Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw9982step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9982step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9982step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw9983Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9983step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9983step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw9984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9984Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9984step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9984step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9984step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9984step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9984step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9985Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9985step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9986Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9986step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9986step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw9987Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9987step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9987step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9987step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw9988Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw9988step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw9989Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw9989step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9989step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw9989step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw9990Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw9990step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw9991Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9991step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw9991step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw9992Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw9992step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9992step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw9992step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw9993Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw9993step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9993step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9993step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw9994Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw9994step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9994step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw9994step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw9995Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw9995step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9995step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw9995step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9995step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw9995step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw9996Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9996step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw9996step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw9997Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw9997step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9997step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw9997step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, -1, -2]]
def raw9998Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw9998step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9998step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![3, -1, -2]]
def raw9998step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9998step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw9998step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9999Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9999step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9999step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9999step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall644 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall645 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall646 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall647 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall648 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall649 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall650 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall652 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall655 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall1164 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1165 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1166 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1167 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1168 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1170 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1172 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1173 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1175 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1176 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1177 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall1266 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1267 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1269 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1271 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1274 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1275 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall1298 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1299 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1300 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1301 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1302 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1304 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1305 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1307 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1308 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1311 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1312 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1313 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1339 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1340 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1341 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1342 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1343 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall1344 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1346 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1349 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1395 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1396 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1397 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1399 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1401 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall1409 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1410 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1411 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1412 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1413 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1414 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1416 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1417 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1419 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1420 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1427 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1441 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1442 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1443 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1444 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1445 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1449 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1451 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1453 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1454 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1468 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1470 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1471 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall1473 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1475 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1477 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1478 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1479 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1480 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall2357 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2358 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2359 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2363 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall2526 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2527 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2528 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2530 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2531 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2532 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall2570 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2572 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2574 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2576 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2593 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2594 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2595 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2596 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2598 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2599 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2601 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2602 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2604 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2605 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall2637 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2638 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2640 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2642 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2644 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall2753 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2755 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2766 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2767 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2768 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2770 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2775 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2776 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2778 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2784 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2788 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall2936 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2937 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2939 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2941 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2943 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall2957 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2958 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2959 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2960 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2961 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2963 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2965 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2966 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2968 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2969 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2986 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2987 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2988 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2990 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2991 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2996 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2997 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2998 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3003 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3005 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall3081 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3082 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3087 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3088 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3089 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3090 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3093 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3094 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3095 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3099 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3100 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3101 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3102 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3103 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3105 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3106 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3109 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3110 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3113 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3116 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3117 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3119 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3120 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3121 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3125 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall3139 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3140 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3141 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3142 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3143 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3144 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3145 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3178 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3184 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3185 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3187 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3188 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3190 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3191 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall3203 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3204 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3205 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3206 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3207 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3209 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3210 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3211 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3223 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3224 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3225 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3226 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3227 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall3711 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall3726 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3727 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3728 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3734 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3735 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3736 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3737 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3738 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3739 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3740 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3741 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall3818 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3820 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3821 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3822 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3823 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3824 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3829 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3830 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3831 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall3847 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3851 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3852 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3853 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3855 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3856 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3858 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3862 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3882 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3883 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3887 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3888 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3889 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall3911 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3912 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3915 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3916 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3925 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3926 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3930 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3931 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3933 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3934 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3936 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3937 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3938 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3939 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3965 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3966 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3967 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall3969 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3970 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3977 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3980 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3981 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3982 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3984 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3987 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3990 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3992 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3993 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3994 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3995 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3997 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3998 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall4002 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall4003 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall4004 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall4012 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall4013 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall4014 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall4015 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall4017 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall4020 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall4023 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall4026 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall4027 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall4028 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall4029 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall4030 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall4031 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall4032 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall4033 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall4039 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall4050 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall4051 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall4053 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall4093 : Fin 1 → Fin 1 := ![0]

def singletonSmall4094 : Fin 1 → Fin 1 := ![0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall4096 : Fin 1 → Fin 1 := ![0]

def singletonSmall4098 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4099 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4100 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4101 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4102 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4103 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4104 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4105 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4106 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4107 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4108 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4109 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4110 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4111 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4112 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4113 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4115 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4119 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4121 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4122 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4126 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4128 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4132 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4133 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4134 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4138 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4139 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4140 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4141 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4142 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4143 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4144 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4145 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4146 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4147 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4148 : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall4164 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4165 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4166 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4167 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4168 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4171 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4172 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4174 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4175 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4177 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4180 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4181 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4182 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4183 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4185 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4186 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4187 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4190 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4191 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4192 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4194 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4195 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4196 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4197 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4198 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4199 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4200 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4201 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4202 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4203 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4204 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4205 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4207 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4210 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4212 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4213 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4217 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4219 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4223 : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall4224 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4225 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4229 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4230 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4231 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4232 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4233 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4234 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4235 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4236 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4237 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4238 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4239 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4240 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4241 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4242 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4243 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4248 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4249 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4251 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4252 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4253 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4255 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4256 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4257 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4265 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4268 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4270 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4272 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4275 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4276 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4278 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4279 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4280 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4285 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4286 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4287 : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons67
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall4288 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4289 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4290 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4291 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4292 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4293 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4294 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4295 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4296 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4298 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4301 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4303 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4304 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4307 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4309 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4313 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4314 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4315 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4319 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4320 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4321 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4322 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4323 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4324 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4325 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4337 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4338 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4339 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4341 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4343 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4344 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4346 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4349 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4350 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4351 : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall4352 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4354 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4355 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4356 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4359 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4360 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4361 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4396 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4398 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4399 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4401 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4404 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4405 : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall4417 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4418 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4419 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4421 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4424 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4428 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4431 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4451 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4452 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4454 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4456 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4457 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4458 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4460 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4461 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4463 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4466 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4467 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4468 : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall4489 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4490 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4491 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4493 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4495 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4496 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4499 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4503 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4507 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4510 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4513 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4514 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4515 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4516 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4517 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4518 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4519 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4520 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4521 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4522 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4523 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4524 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4525 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4526 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4537 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4538 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4539 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4541 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4543 : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall4544 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4546 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4549 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4550 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4551 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4553 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4554 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4555 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4557 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4558 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4559 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4569 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4570 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4572 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4575 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4581 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4583 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4586 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4601 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4602 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4605 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4606 : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall4608 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4612 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4618 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4619 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4621 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4622 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4623 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4624 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4625 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4627 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4628 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4629 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4630 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4631 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4632 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4633 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4634 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4635 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4636 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4637 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4638 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4640 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4642 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4644 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4645 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4648 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4650 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4653 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4654 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4657 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4658 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4660 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4661 : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall4672 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4673 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4676 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4678 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4679 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4681 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4684 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4685 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4686 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4688 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4689 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4691 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4692 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4693 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4706 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4707 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4709 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4710 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4713 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4716 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4717 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4719 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4720 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4721 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4722 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4723 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4724 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4725 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4726 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4727 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4728 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4729 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4731 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4732 : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons74
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall4737 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4740 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4742 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4744 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4746 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4747 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4749 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4750 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4754 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4759 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4760 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4763 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4764 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4766 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4767 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4769 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4770 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4778 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4779 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4782 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4787 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4788 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4798 : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall4800 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4801 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4802 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4804 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4805 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4807 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4810 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4811 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4826 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4827 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4828 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4831 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4832 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4835 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4839 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4843 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4845 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4859 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4860 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4862 : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall4864 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4865 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4866 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4868 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4869 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4871 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4874 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4875 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4887 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4888 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4889 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4890 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4896 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4898 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4899 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4902 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4907 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4913 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4926 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4927 : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall4928 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4936 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4937 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4939 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4941 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4943 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4946 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4947 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4948 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4949 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4950 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4952 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4953 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4960 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4961 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4967 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4968 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4969 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4970 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4971 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4972 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4973 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4974 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4977 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4979 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4985 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4986 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4987 : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall4996 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4998 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5000 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5003 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5013 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5014 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5015 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5018 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5021 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5023 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5030 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5032 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5033 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5036 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5037 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5038 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5039 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5047 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5050 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5055 : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall5056 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5059 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5070 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5072 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5073 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5075 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5076 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5078 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5080 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5081 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5093 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5094 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5095 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5098 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5099 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5102 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5105 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5109 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5110 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5114 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5117 : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall5123 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5125 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5126 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5134 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5137 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5141 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5142 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5149 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5152 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5155 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5156 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5162 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5163 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5167 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5168 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5169 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5170 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5171 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5172 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5174 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5176 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5177 : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall5192 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5193 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5202 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5203 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5204 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5207 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5227 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5228 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5237 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5238 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5241 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5247 : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall5248 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5257 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5258 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5259 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5261 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5271 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5272 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5275 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5284 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5290 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5291 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5292 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5293 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5294 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5296 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5301 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5302 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5304 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5305 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5306 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5310 : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall5328 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5329 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5333 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5335 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5336 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5337 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5341 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5344 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5346 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5349 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5351 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5352 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5354 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5355 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5356 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5363 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5364 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5365 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5368 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5370 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5372 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5373 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5374 : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall5378 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5380 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5383 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5384 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5386 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5387 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5388 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5389 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5390 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5391 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5393 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5395 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5397 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5398 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5400 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5401 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5403 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5404 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5405 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5406 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5411 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5412 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5415 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5416 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5417 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5418 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5422 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5423 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5424 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5428 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5431 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5432 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5433 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5434 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5435 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5437 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5438 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5439 : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall5443 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5447 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5448 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5449 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5450 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5451 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5452 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5453 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5456 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5464 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5465 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5466 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5467 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5469 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5472 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5473 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5475 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5476 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5478 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5482 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5483 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5484 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5485 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5490 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5491 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5492 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5494 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5498 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5500 : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node0 : Matrix (Fin 0) (Fin 0) ℤ := ![]

def node1 : Matrix (Fin 2) (Fin 2) ℤ := ![![-5, 5], ![5, -5]]

def node10 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node100 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![1, 1, -2], ![1, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node1000 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def node1001 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, -3, 1], ![1, 0, 2, -3]]

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

def boundaryMatrix0 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def boundaryMatrix1 : Matrix (Fin 7) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]

def boundaryMatrix2 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, 0, 2]]

def boundaryMatrix3 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2]]

def boundaryMatrix4 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, 2, 0]]

def boundaryMatrix10 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 1, 1]]

def boundaryMatrix11 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 2, 0, 0]]

def boundaryMatrix12 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 1, 1, 0]]

def boundaryMatrix13 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, 1, 0]]

def boundaryMatrix14 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 0, 2, 0]]

def boundaryMatrix16 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

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

def boundaryMatrix17 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, -1, 3]]

def boundaryMatrix18 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-1, 3, -2]]

def boundaryMatrix19 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def boundaryMatrix20 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![0, 3, -3]]

def boundaryMatrix21 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-1, -2, 3]]

def boundaryMatrix22 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![2, 0, -2]]

def boundaryMatrix23 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![-3, 3, 0]]

def boundaryMatrix24 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-3, 2, 1]]

def boundaryMatrix25 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-2, 1, 1], ![-1, 2, -1]]

def boundaryMatrix26 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, -1, 2, 1]]

def boundaryMatrix27 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, -1, 2]]

def boundaryMatrix28 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 1, 2]]

def boundaryMatrix29 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, -1, 1, 2]]

def boundaryMatrix30 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 2, 1, -1]]

def boundaryMatrix31 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, 2, -1]]

def boundaryMatrix32 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, -1, 2]]

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

def boundaryMatrix269 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-3, 0, 3], ![1, 2, -3]]

def boundaryMatrix270 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-2, -1, 3], ![2, 1, -3]]

def boundaryMatrix271 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![-1, -1, 2], ![3, 0, -3]]

def boundaryMatrix273 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-1, 2, -1], ![2, 0, -2], ![-2, -1, 3]]

def boundaryMatrix275 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![-2, 4, -2]]

def boundaryMatrix276 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![-2, 0, 2], ![-1, 4, -3]]

def boundaryMatrix277 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![-2, 4, -2]]

def boundaryMatrix278 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![1, 3, -4]]

def boundaryMatrix285 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![-2, 3, -1], ![2, 1, -3]]

def boundaryMatrix286 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, 3, -1], ![1, -3, 2]]

def boundaryMatrix287 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-1, 3, -2], ![1, -3, 2]]

def boundaryMatrix297 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 2, 2, -5]]

def boundaryMatrix298 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, 0, -2], ![-2, -2, 1, 3]]

def boundaryMatrix300 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1], ![-2, -2, 0, 4]]

def boundaryMatrix301 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 0, -2], ![-2, -2, 0, 4]]

def boundaryMatrix302 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, 0, -2], ![-2, -1, -1, 4]]

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

def boundaryMatrix303 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2], ![-2, -2, 0, 4]]

def boundaryMatrix304 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, 2, 0, -2], ![-2, -1, -1, 4]]

def boundaryMatrix305 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2], ![-2, -2, 0, 4]]

def boundaryMatrix306 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 1, -2], ![-2, -1, -1, 4]]

def boundaryMatrix307 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![-2, -1, 0, 3], ![1, 2, 0, -3]]

def boundaryMatrix308 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, -1, 0, 3], ![2, -1, 1, -2]]

def boundaryMatrix311 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, -1, 0, 3], ![1, -1, 2, -2]]

def boundaryMatrix312 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, -1, 0, 3], ![1, 0, 2, -3]]

def boundaryMatrix313 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, -1, 0, 3], ![0, 1, 2, -3]]

def boundaryMatrix314 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, -1, 1, 2], ![2, 1, 0, -3]]

def boundaryMatrix315 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![-2, -1, 0, 3], ![2, 1, 0, -3]]

def boundaryMatrix332 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -2, 2, -2]]

def boundaryMatrix337 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, 1, 1], ![-1, 2, 2, -3]]

def boundaryMatrix338 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 1, 1], ![0, 2, 2, -4]]

def boundaryMatrix339 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, 0, 1], ![0, 1, 3, -4]]

def boundaryMatrix340 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1], ![-2, -2, 2, 2]]

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

def boundaryMatrix343 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![-2, 0, 0, 2], ![2, -2, 2, -2]]

def boundaryMatrix345 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, -1, -1, 2], ![-2, 2, 2, -2]]

def boundaryMatrix346 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 0, 2], ![-1, 2, 2, -3]]

def boundaryMatrix347 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 0, -1, 2], ![-1, 2, 2, -3]]

def boundaryMatrix349 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -2, 0, 2], ![-2, 1, 3, -2]]

def boundaryMatrix350 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, -1, -1, 2], ![-2, 1, 3, -2]]

def boundaryMatrix351 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 0, 2], ![-1, 1, 3, -3]]

def boundaryMatrix353 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, 0, 2], ![-1, 1, 3, -3]]

def boundaryMatrix354 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![0, 1, 3, -4]]

def boundaryMatrix355 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -2, -2, 2]]

def boundaryMatrix356 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 1, -2, 3]]

def boundaryMatrix362 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, -1, 2, -1], ![-2, 1, -2, 3]]

def boundaryMatrix363 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-2, 0, 2, 0], ![1, 2, 1, -4]]

def boundaryMatrix364 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-2, 1, 1, 0], ![1, 1, 2, -4]]

def boundaryMatrix365 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-2, 2, 0, 0], ![1, 0, 3, -4]]

def boundaryMatrix368 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, 0, 1, 1], ![1, 1, 2, -4]]

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

def boundaryMatrix369 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, 1, 0, 1], ![1, 0, 3, -4]]

def boundaryMatrix372 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![0, 2, 2, -4]]

def boundaryMatrix373 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![0, 1, 3, -4]]

def boundaryMatrix374 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1], ![0, -1, 2, -1], ![-2, 2, -2, 2]]

def boundaryMatrix377 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![1, 0, 3, -4]]

def boundaryMatrix378 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 1, 3, -4]]

def boundaryMatrix379 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-2, 0, 2, 0], ![2, 1, 1, -4]]

def boundaryMatrix381 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 0, 2, 0], ![1, 2, 1, -4]]

def boundaryMatrix382 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 1, 1, 0], ![1, 1, 2, -4]]

def boundaryMatrix383 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 2, 0, 0], ![1, 0, 3, -4]]

def boundaryMatrix384 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, 0, 1, 1], ![2, 0, 2, -4]]

def boundaryMatrix385 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![1, 1, 2, -4]]

def boundaryMatrix386 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![1, 0, 3, -4]]

def boundaryMatrix387 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![0, 2, 2, -4]]

def boundaryMatrix388 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![0, 1, 3, -4]]

def boundaryMatrix389 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![1, 0, 3, -4]]

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

def boundaryMatrix390 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 1, 3, -4]]

def boundaryMatrix393 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-2, 2, 0, 0], ![2, 0, 2, -4]]

def boundaryMatrix394 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-2, 0, 1, 1], ![2, 1, 1, -4]]

def boundaryMatrix395 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-2, 1, 0, 1], ![2, 0, 2, -4]]

def boundaryMatrix396 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![1, 2, 1, -4]]

def boundaryMatrix397 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![1, 1, 2, -4]]

def boundaryMatrix398 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, 0, 0, 2], ![2, 0, 2, -4]]

def boundaryMatrix399 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![1, 1, 2, -4]]

def boundaryMatrix400 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 2, 2, -4]]

def boundaryMatrix401 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-1, -1, 2, 0], ![1, 2, 1, -4]]

def boundaryMatrix402 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-1, -1, 1, 1], ![1, 1, 2, -4]]

def boundaryMatrix403 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 1, 1], ![0, 2, 2, -4]]

def boundaryMatrix404 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 1, -1, 1], ![0, 1, 3, -4]]

def boundaryMatrix405 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-1, -1, 0, 2], ![1, 0, 3, -4]]

def boundaryMatrix406 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 0, 2], ![0, 1, 3, -4]]

def boundaryMatrix407 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 0, -1, 2], ![0, 1, 3, -4]]

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

def boundaryMatrix408 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-1, -1, 2, 0], ![2, 1, 1, -4]]

def boundaryMatrix409 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-1, 2, -1, 0], ![1, 0, 3, -4]]

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

def boundaryMatrix33 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-2, -1, 1, 2]]

def boundaryMatrix34 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![0, 1, 2, -3]]

def boundaryMatrix35 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 1, -3]]

def boundaryMatrix36 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def boundaryMatrix37 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def boundaryMatrix38 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 1, 2, -3]]

def boundaryMatrix39 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def boundaryMatrix40 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, 1, -3]]

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

def boundaryMatrix100 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 2, 0, -1], ![-1, -1, -1, 3]]

def boundaryMatrix101 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, 0, -2], ![-2, -1, 0, 3]]

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

def boundaryMatrix102 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-1, 1, 1, -1], ![-1, -2, 0, 3]]

def boundaryMatrix103 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 1, 1, -1], ![-1, -1, -1, 3]]

def boundaryMatrix104 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -1, 2, -1], ![-2, -1, 0, 3]]

def boundaryMatrix105 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-1, 0, 2, -1], ![-1, -2, 0, 3]]

def boundaryMatrix106 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -1, 1, -2]]

def boundaryMatrix107 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![1, -1, 2, -2]]

def boundaryMatrix108 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 2, 1, -3]]

def boundaryMatrix128 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 2, 2, -2]]

def boundaryMatrix129 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, 3, -2]]

def boundaryMatrix130 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, 3, -2]]

def boundaryMatrix131 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-2, 2, 0, 0], ![2, -2, 1, -1]]

def boundaryMatrix133 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 1, 2, -1]]

def boundaryMatrix134 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![-2, 2, 0, 0], ![1, -1, 2, -2]]

def boundaryMatrix135 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1], ![-2, 2, 1, -1]]

def boundaryMatrix138 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 0, 3, -1]]

def boundaryMatrix139 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 1, 1, 0], ![1, -2, 2, -1]]

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

def boundaryMatrix140 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 1, 1, 0], ![1, -1, 2, -2]]

def boundaryMatrix144 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![0, 0, 2, -2], ![-2, 2, 1, -1]]

def boundaryMatrix145 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 0, 2, -1], ![-1, 2, 1, -2]]

def boundaryMatrix146 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 2, 0], ![0, 2, 1, -3]]

def boundaryMatrix147 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 1, 1, -1], ![-1, 1, 2, -2]]

def boundaryMatrix150 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 1, 0], ![2, -2, -1, 1]]

def boundaryMatrix151 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, 2, 0], ![2, -2, -1, 1]]

def boundaryMatrix152 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0], ![-2, -1, 2, 1]]

def boundaryMatrix153 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![1, -2, 2, -1]]

def boundaryMatrix156 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![-2, 0, 1, 1], ![2, -2, 1, -1]]

def boundaryMatrix157 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 0, -1], ![-2, -1, 2, 1]]

def boundaryMatrix158 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 0, -2], ![-2, -1, 2, 1]]

def boundaryMatrix161 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 1, 1], ![-1, 2, 1, -2]]

def boundaryMatrix162 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, 0, -2], ![-2, -1, 2, 1]]

def boundaryMatrix165 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, -2, 0, 1], ![-2, 0, 3, -1]]

def boundaryMatrix166 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, -1, 1, -1], ![-2, -1, 2, 1]]

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

def boundaryMatrix167 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -2, 1, 1], ![-2, 1, 2, -1]]

def boundaryMatrix168 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![0, -2, 3, -1]]

def boundaryMatrix169 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-1, 1, 1, -1], ![-1, -2, 2, 1]]

def boundaryMatrix171 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![0, -1, 3, -2]]

def boundaryMatrix173 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![0, -1, 3, -2]]

def boundaryMatrix175 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![-2, 0, 2, 0], ![1, -2, -1, 2]]

def boundaryMatrix176 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -2, 2, 0], ![-2, 1, -1, 2]]

def boundaryMatrix183 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, -1, -1, 2], ![-2, 0, 3, -1]]

def boundaryMatrix184 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, 0, -1, 2], ![-1, -1, 3, -1]]

def boundaryMatrix187 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 0, -1, 2], ![-1, -1, 3, -1]]

def boundaryMatrix240 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 4, -5]]

def boundaryMatrix241 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 3, -5]]

def boundaryMatrix242 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![1, 3, -4]]

def boundaryMatrix243 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![-1, 4, -3]]

def boundaryMatrix244 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-2, 0, 2], ![0, 4, -4]]

def boundaryMatrix245 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![-2, -2, 4]]

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

def boundaryMatrix246 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-1, -1, 2], ![0, 4, -4]]

def boundaryMatrix247 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-2, -1, 3], ![1, 2, -3]]

def boundaryMatrix248 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, -2, 3], ![-1, 3, -2]]

def boundaryMatrix249 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, -1, 3], ![0, 3, -3]]

def boundaryMatrix250 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![2, 1, -3]]

def boundaryMatrix251 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-1, -2, 3], ![1, 2, -3]]

def boundaryMatrix252 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, 3, -2], ![0, -3, 3]]

def boundaryMatrix253 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-1, -2, 3], ![0, 3, -3]]

def boundaryMatrix261 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]

def boundaryMatrix262 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![-3, -1, 4]]

def boundaryMatrix263 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![-3, -1, 4]]

def boundaryMatrix264 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![2, 2, -4]]

def boundaryMatrix265 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-3, 1, 2], ![3, 0, -3]]

def boundaryMatrix266 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-3, 1, 2], ![2, 1, -3]]

def boundaryMatrix267 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-3, 1, 2], ![1, 2, -3]]

def boundaryMatrix268 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-3, 0, 3], ![2, 1, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end


