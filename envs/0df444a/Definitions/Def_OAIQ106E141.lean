-- Prove2me | Definitions.Def_OAIQ106E141
-- name    : OAIQ106E141
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T18:27:32.770791+00:00
-- url     : https://prove2.me/theorems/5621fe9d-85bc-4a24-8122-86a8ac6c050a
-- title:
--   Definitions bundle OAIQ106E141 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 4771 declarations of OpenAI's Lean: 4771 definitions. The definitions and types are `OAI.MUB6.Certificate.PairSemantics.node3366`, `OAI.MUB6.Certificate.PairSemantics.node3367`, `OAI.MUB6.Certificate.PairSemantics.node3368`, `OAI.MUB6.Certificate.PairSemantics.node3369`, `OAI.MUB6.Certificate.PairSemantics.node3370`, `OAI.MUB6.Certificate.PairSemantics.node3371`, `OAI.MUB6.Certificate.PairSemantics.node3372`, `OAI.MUB6.Certificate.PairSemantics.node3373`, `OAI.MUB6.Certificate.PairSemantics.node3374`, `OAI.MUB6.Certificate.PairSemantics.node3375`, `OAI.MUB6.Certificate.PairSemantics.node3376`, `OAI.MUB6.Certificate.PairSemantics.node3377`, `OAI.MUB6.Certificate.PairSemantics.node3378`, `OAI.MUB6.Certificate.PairSemantics.node3379`, `OAI.MUB6.Certificate.PairSemantics.node338`, `OAI.MUB6.Certificate.PairSemantics.node3380`, `OAI.MUB6.Certificate.PairSemantics.node3381`, `OAI.MUB6.Certificate.PairSemantics.node3382`, `OAI.MUB6.Certificate.PairSemantics.node3383`, `OAI.MUB6.Certificate.PairSemantics.node3384`, `OAI.MUB6.Certificate.PairSemantics.node3385`, `OAI.MUB6.Certificate.PairSemantics.node3386`, `OAI.MUB6.Certificate.PairSemantics.node3387`, `OAI.MUB6.Certificate.PairSemantics.node3388`, `OAI.MUB6.Certificate.PairSemantics.node3389`, `OAI.MUB6.Certificate.PairSemantics.node339`, `OAI.MUB6.Certificate.PairSemantics.node3390`, `OAI.MUB6.Certificate.PairSemantics.node3391`, `OAI.MUB6.Certificate.PairSemantics.node3392`, `OAI.MUB6.Certificate.PairSemantics.node3393`, `OAI.MUB6.Certificate.PairSemantics.node3394`, `OAI.MUB6.Certificate.PairSemantics.node3395`, `OAI.MUB6.Certificate.PairSemantics.node3396`, `OAI.MUB6.Certificate.PairSemantics.node3397`, `OAI.MUB6.Certificate.PairSemantics.node3398`, `OAI.MUB6.Certificate.PairSemantics.node3399`, `OAI.MUB6.Certificate.PairSemantics.node34`, `OAI.MUB6.Certificate.PairSemantics.node340`, `OAI.MUB6.Certificate.PairSemantics.node3400`, `OAI.MUB6.Certificate.PairSemantics.node3401` and 4731 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_PairSemantics_Nodes0`, `MutuallyUnbiased_PairSemantics_Nodes1`, `MutuallyUnbiased_PairSemantics_Nodes10`, `MutuallyUnbiased_PairSemantics_Nodes11`, `MutuallyUnbiased_PairSemantics_Nodes12`, `MutuallyUnbiased_PairSemantics_Nodes13`, `MutuallyUnbiased_PairSemantics_Nodes14`, `MutuallyUnbiased_PairSemantics_Nodes15`, `MutuallyUnbiased_PairSemantics_Nodes5`, `MutuallyUnbiased_PairSemantics_Nodes52`, `MutuallyUnbiased_PairSemantics_Nodes53`, `MutuallyUnbiased_PairSemantics_Nodes54`, `MutuallyUnbiased_PairSemantics_Nodes6`, `MutuallyUnbiased_PairSemantics_Nodes7`, `MutuallyUnbiased_PairSemantics_Nodes8`, `MutuallyUnbiased_PairSemantics_Nodes9`, `MutuallyUnbiased_PairSemantics_Permutations`, `MutuallyUnbiased_PairSemantics_Sound0`, `MutuallyUnbiased_PairSemantics_Sound1`, `MutuallyUnbiased_PairSemantics_Sound10`, `MutuallyUnbiased_PairSemantics_Sound11`, `MutuallyUnbiased_PairSemantics_Sound12`, `MutuallyUnbiased_PairSemantics_Sound13`, `MutuallyUnbiased_PairSemantics_Sound14`, `MutuallyUnbiased_PairSemantics_Sound15`, `MutuallyUnbiased_PairSemantics_Sound16`, `MutuallyUnbiased_PairSemantics_Sound17`, `MutuallyUnbiased_PairSemantics_Sound18`, `MutuallyUnbiased_PairSemantics_Sound19`, `MutuallyUnbiased_PairSemantics_Sound2`, `MutuallyUnbiased_PairSemantics_Sound20`, `MutuallyUnbiased_PairSemantics_Sound21`, `MutuallyUnbiased_PairSemantics_Sound22`, `MutuallyUnbiased_PairSemantics_Sound23`, `MutuallyUnbiased_PairSemantics_Sound24`, `MutuallyUnbiased_PairSemantics_Sound25`, `MutuallyUnbiased_PairSemantics_Sound26`, `MutuallyUnbiased_PairSemantics_Sound27`, `MutuallyUnbiased_PairSemantics_Sound28`, `MutuallyUnbiased_PairSemantics_Sound29`, `MutuallyUnbiased_PairSemantics_Sound3`, `MutuallyUnbiased_PairSemantics_Sound30`, `MutuallyUnbiased_PairSemantics_Sound31`, `MutuallyUnbiased_PairSemantics_Sound32`, `MutuallyUnbiased_PairSemantics_Sound33`, `MutuallyUnbiased_PairSemantics_Sound34`, `MutuallyUnbiased_PairSemantics_Sound35`, `MutuallyUnbiased_PairSemantics_Sound36`, `MutuallyUnbiased_PairSemantics_Sound37`, `MutuallyUnbiased_PairSemantics_Sound38`, `MutuallyUnbiased_PairSemantics_Sound39`, `MutuallyUnbiased_PairSemantics_Sound4`, `MutuallyUnbiased_PairSemantics_Sound40`, `MutuallyUnbiased_PairSemantics_Sound41`, `MutuallyUnbiased_PairSemantics_Sound42`, `MutuallyUnbiased_PairSemantics_Sound43`, `MutuallyUnbiased_PairSemantics_Sound44`, `MutuallyUnbiased_PairSemantics_Sound45`, `MutuallyUnbiased_PairSemantics_Sound46`, `MutuallyUnbiased_PairSemantics_Sound47`, `MutuallyUnbiased_PairSemantics_Sound48`, `MutuallyUnbiased_PairSemantics_Sound49`, `MutuallyUnbiased_PairSemantics_Sound5`, `MutuallyUnbiased_PairSemantics_Sound50`, `MutuallyUnbiased_PairSemantics_Sound51`, `MutuallyUnbiased_PairSemantics_Sound52`, `MutuallyUnbiased_PairSemantics_Sound53`, `MutuallyUnbiased_PairSemantics_Sound54`, `MutuallyUnbiased_PairSemantics_Sound6`, `MutuallyUnbiased_PairSemantics_Sound8`, `MutuallyUnbiased_PairSemantics_Sound9`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the statements `OAI.MUB6.Certificate.PairSemantics.sound3366_e`, `OAI.MUB6.Certificate.PairSemantics.sound3367_e`, `OAI.MUB6.Certificate.PairSemantics.sound3368_e`, `OAI.MUB6.Certificate.PairSemantics.sound3369_e`, `OAI.MUB6.Certificate.PairSemantics.sound3370_e`, `OAI.MUB6.Certificate.PairSemantics.sound3371_e`, `OAI.MUB6.Certificate.PairSemantics.sound3372_e`, `OAI.MUB6.Certificate.PairSemantics.sound3375_e`, `OAI.MUB6.Certificate.PairSemantics.sound3376_e`, `OAI.MUB6.Certificate.PairSemantics.sound3377_e`, `OAI.MUB6.Certificate.PairSemantics.sound3378_e`, `OAI.MUB6.Certificate.PairSemantics.sound3380_e`, `OAI.MUB6.Certificate.PairSemantics.sound3382_e`, `OAI.MUB6.Certificate.PairSemantics.sound3383_e`, `OAI.MUB6.Certificate.PairSemantics.sound3384_e`, `OAI.MUB6.Certificate.PairSemantics.sound3385_e`, `OAI.MUB6.Certificate.PairSemantics.sound3387_e`, `OAI.MUB6.Certificate.PairSemantics.sound3388_e`, `OAI.MUB6.Certificate.PairSemantics.sound3389_e`, `OAI.MUB6.Certificate.PairSemantics.sound3390_e`, `OAI.MUB6.Certificate.PairSemantics.sound3391_e`, `OAI.MUB6.Certificate.PairSemantics.sound3392_e`, `OAI.MUB6.Certificate.PairSemantics.sound3393_e`, `OAI.MUB6.Certificate.PairSemantics.sound3394_e`, `OAI.MUB6.Certificate.PairSemantics.sound3395_e`, `OAI.MUB6.Certificate.PairSemantics.sound3396_e`, `OAI.MUB6.Certificate.PairSemantics.sound3397_e`, `OAI.MUB6.Certificate.PairSemantics.sound3399_e`, `OAI.MUB6.Certificate.PairSemantics.sound3400_e`, `OAI.MUB6.Certificate.PairSemantics.sound3401_e`, `OAI.MUB6.Certificate.PairSemantics.sound3402_e`, `OAI.MUB6.Certificate.PairSemantics.sound3405_e`, `OAI.MUB6.Certificate.PairSemantics.sound3407_e`, `OAI.MUB6.Certificate.PairSemantics.sound3408_e`, `OAI.MUB6.Certificate.PairSemantics.sound3411_e`, `OAI.MUB6.Certificate.PairSemantics.sound3412_e`, `OAI.MUB6.Certificate.PairSemantics.sound3413_e`, `OAI.MUB6.Certificate.PairSemantics.sound3414_e`, `OAI.MUB6.Certificate.PairSemantics.sound3415_e`, `OAI.MUB6.Certificate.PairSemantics.sound3416_e`, `OAI.MUB6.Certificate.PairSemantics.sound3417_e`, `OAI.MUB6.Certificate.PairSemantics.sound3418_e`, `OAI.MUB6.Certificate.PairSemantics.sound3419_e`, `OAI.MUB6.Certificate.PairSemantics.sound3420_e`, `OAI.MUB6.Certificate.PairSemantics.sound3421_e`, `OAI.MUB6.Certificate.PairSemantics.sound3422_e`, `OAI.MUB6.Certificate.PairSemantics.sound3423_e`, `OAI.MUB6.Certificate.PairSemantics.sound3424_e`, `OAI.MUB6.Certificate.PairSemantics.sound3425_e`, `OAI.MUB6.Certificate.PairSemantics.sound3428_e`, `OAI.MUB6.Certificate.PairSemantics.sound3431_e`, `OAI.MUB6.Certificate.PairSemantics.sound3433_e`, `OAI.MUB6.Certificate.PairSemantics.sound3434_e`, `OAI.MUB6.Certificate.PairSemantics.sound3435_e`, `OAI.MUB6.Certificate.PairSemantics.sound3436_e`, `OAI.MUB6.Certificate.PairSemantics.sound3437_e`, `OAI.MUB6.Certificate.PairSemantics.sound3439_e`, `OAI.MUB6.Certificate.PairSemantics.sound3440_e`, `OAI.MUB6.Certificate.PairSemantics.sound3441_e`, `OAI.MUB6.Certificate.PairSemantics.sound3442_e`, `OAI.MUB6.Certificate.PairSemantics.sound3443_e`, `OAI.MUB6.Certificate.PairSemantics.sound3444_e`, `OAI.MUB6.Certificate.PairSemantics.sound3447_e`, `OAI.MUB6.Certificate.PairSemantics.sound3449_e`, `OAI.MUB6.Certificate.PairSemantics.sound3451_e`, `OAI.MUB6.Certificate.PairSemantics.sound3454_e`, `OAI.MUB6.Certificate.PairSemantics.sound3455_e`, `OAI.MUB6.Certificate.PairSemantics.sound3456_e`, `OAI.MUB6.Certificate.PairSemantics.sound3457_e`, `OAI.MUB6.Certificate.PairSemantics.sound3458_e`, `OAI.MUB6.Certificate.PairSemantics.sound3459_e`, `OAI.MUB6.Certificate.PairSemantics.sound3460_e`, `OAI.MUB6.Certificate.PairSemantics.sound3461_e`, `OAI.MUB6.Certificate.PairSemantics.sound3462_e`, `OAI.MUB6.Certificate.PairSemantics.sound3463_e`, `OAI.MUB6.Certificate.PairSemantics.sound3467_e` and `OAI.MUB6.Certificate.PairSemantics.sound3468_e`; the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1162_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1163_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1164_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1165_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1170_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1172_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1265_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1266_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1267_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1298_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1299_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1339_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1340_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1341_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1342_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1343_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1395_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1396_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1397_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1399_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1409_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1410_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1411_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1412_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1414_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1441_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1475_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1477_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1478_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2357_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2358_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2526_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2527_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2528_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2530_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2531_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2570_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2572_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2574_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2576_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2593_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2594_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2595_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2599_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2636_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2766_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2828_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2901_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2903_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2904_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2936_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2937_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2939_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2941_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2943_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2957_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2958_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2959_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2960_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2961_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2963_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2986_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2987_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2988_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2990_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2996_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2998_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3003_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3081_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3082_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3087_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3088_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3089_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3094_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3100_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3106_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3109_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3139_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3140_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3184_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3185_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3190_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3191_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3203_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3204_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3205_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3206_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3209_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3210_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3211_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3223_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3226_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3227_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3711_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3727_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3735_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3737_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3739_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3818_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3821_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3823_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3829_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3830_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3847_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3851_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3852_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3853_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3882_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3925_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3936_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3937_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3938_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3965_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3966_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3967_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3969_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3970_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3977_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3980_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3981_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3982_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3984_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3990_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3992_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3994_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3995_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3998_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4003_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4023_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4026_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4031_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4032_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4033_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4053_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5174_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5387_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5415_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5418_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5439_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5450_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5452_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5464_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5465_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5490_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5492_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound0_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound111_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound12_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound135_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound136_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound137_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound138_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound139_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound140_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound141_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound142_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound143_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound144_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound145_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound146_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound147_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound148_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound149_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound150_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound151_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound16_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound19_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound1_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound20_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound21_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound23_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound28_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound29_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound2_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound30_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound32_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound35_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound36_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound37_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound3_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound41_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound49_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound5_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound61_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound62_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound6_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound78_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound7_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound9_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1472_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero14_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero15_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1674_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1785_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero18_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1909_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero488_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero621_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero794_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero818_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound0_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1007_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1008_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound100_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1010_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1013_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1020_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1021_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1033_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1093_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1094_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1095_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1096_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1097_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1098_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound10_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1103_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1108_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound110_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1110_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1111_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1115_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound111_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1120_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1121_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1124_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1130_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1131_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound113_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound114_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1159_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound115_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1165_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1166_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1167_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound116_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1170_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1177_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1178_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1179_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1194_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound125_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1261_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1262_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1264_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1266_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1267_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1268_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1269_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound126_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1272_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1278_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1279_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound127_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1294_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound12_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1300_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1301_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1303_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1309_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound130_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1310_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1311_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1312_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1318_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1324_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound137_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound138_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound139_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound13_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1409_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound140_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1410_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1411_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1412_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1413_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1414_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1418_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1419_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound141_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1420_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1421_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1423_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1429_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1433_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1434_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1435_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1437_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound143_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1441_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1442_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound144_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1469_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1470_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1477_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1478_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1479_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1480_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1484_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1492_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1493_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1507_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1510_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1511_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1517_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound151_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1521_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound153_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1559_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1560_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1562_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1567_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1568_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1572_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound163_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1648_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1649_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1650_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1651_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1652_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1653_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1654_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1655_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1656_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1662_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1669_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1672_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1686_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound16_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1703_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1708_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1709_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1715_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1717_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1780_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1781_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1782_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1783_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1784_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1786_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1787_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1788_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1789_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1796_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound17_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1816_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1840_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1844_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1845_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1846_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1847_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1849_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1853_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1854_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1855_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1856_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1859_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1866_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1872_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1874_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound188_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1904_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1905_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1907_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1911_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1914_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1915_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1916_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1917_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1925_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1944_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1963_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1964_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1968_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1969_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1972_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1977_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1985_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound199_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound19_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2033_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2034_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2035_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2036_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2037_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2038_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2040_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2046_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2048_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2049_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2050_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2059_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2062_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2075_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2077_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound207_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound213_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound214_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2166_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2168_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2169_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2170_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2171_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2172_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2173_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2174_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2175_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2176_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2177_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2178_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2179_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2180_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2181_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2182_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2183_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2184_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2185_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2187_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2188_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2189_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2191_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2192_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2193_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2195_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2196_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2197_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2198_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2199_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound21_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2200_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2201_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2202_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2203_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2204_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2205_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2206_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2207_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2208_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2211_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2212_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2214_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2215_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2216_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2217_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2218_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2219_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2220_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2223_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2224_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2225_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2226_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2227_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2228_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2229_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2230_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2231_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2232_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2233_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2235_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2236_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2238_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2240_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2241_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2242_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2244_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2245_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2246_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2247_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2248_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2249_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2250_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2251_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2252_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2253_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2254_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2255_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2256_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2257_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2258_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2259_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2260_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2261_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2262_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2263_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2264_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2265_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2266_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2267_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2268_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound226_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2270_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2271_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2272_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2273_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2274_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2275_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2276_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2277_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2278_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2279_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2281_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2282_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2283_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2284_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2285_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2286_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2287_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2288_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2289_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2290_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2291_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2292_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2293_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2294_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2295_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2296_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2297_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2298_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2299_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound22_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2300_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2301_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2302_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2304_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2305_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2306_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2307_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2308_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2309_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2310_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2311_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2312_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2313_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2314_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2315_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2316_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2317_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2318_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2321_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2322_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2323_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2324_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2325_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2326_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2327_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2328_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2329_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2330_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2331_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2332_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2333_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2334_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2335_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2336_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2337_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2338_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2339_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2340_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2341_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2342_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2344_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2345_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2346_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2347_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2348_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2350_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2352_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2353_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2354_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2355_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2356_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2357_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2358_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2361_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2362_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2363_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2364_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2365_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2366_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2367_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2368_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2369_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound236_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2371_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2373_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2374_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2375_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2376_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2377_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2378_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2379_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2380_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2381_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2382_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2383_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2384_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2385_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2386_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2387_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2388_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2390_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2391_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2392_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2393_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2394_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2395_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2396_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2397_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2398_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2399_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound23_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2400_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2401_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2402_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2404_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2405_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2406_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2407_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2408_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2409_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2410_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2411_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2412_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2413_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2414_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2415_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2416_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2418_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2419_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2421_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2422_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2423_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2424_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound244_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound245_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound24_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound255_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound267_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound269_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound281_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound282_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound286_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound287_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound28_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound296_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound301_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound310_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound311_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound319_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound327_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound335_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound339_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound340_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound341_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound342_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound343_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound344_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound345_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound353_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound354_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound355_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound356_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound357_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound358_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound359_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound365_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound366_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound367_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound368_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound369_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound370_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound371_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound380_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound388_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound391_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound392_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound395_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound396_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound3_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound404_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound411_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound412_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound413_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound418_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound419_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound427_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound428_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound438_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound444_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound445_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound447_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound448_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound452_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound453_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound454_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound456_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound462_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound463_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound470_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound473_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound474_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound481_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound482_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound483_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound484_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound485_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound497_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound498_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound499_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound4_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound500_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound501_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound504_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound513_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound514_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound515_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound516_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound518_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound519_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound521_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound523_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound524_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound525_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound526_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound531_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound532_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound533_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound534_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound537_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound538_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound539_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound540_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound541_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound542_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound543_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound545_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound546_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound547_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound548_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound551_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound552_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound553_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound554_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound555_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound558_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound564_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound565_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound566_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound567_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound568_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound570_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound571_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound579_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound580_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound581_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound582_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound584_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound585_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound587_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound588_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound589_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound58_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound599_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound5_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound600_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound613_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound614_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound628_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound629_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound630_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound631_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound633_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound635_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound636_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound643_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound644_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound649_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound656_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound657_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound658_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound659_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound663_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound664_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound666_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound667_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound668_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound675_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound683_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound688_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound694_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound6_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound700_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound707_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound711_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound712_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound717_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound718_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound719_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound720_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound722_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound727_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound730_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound731_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound732_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound733_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound734_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound735_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound736_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound737_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound740_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound741_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound742_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound743_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound750_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound751_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound758_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound759_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound769_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound76_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound779_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound780_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound786_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound787_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound788_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound789_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound790_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound792_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound793_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound796_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound797_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound798_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound799_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound7_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound800_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound801_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound802_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound804_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound805_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound813_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound815_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound817_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound822_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound823_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound834_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound841_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound842_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound844_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound847_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound852_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound853_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound857_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound858_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound859_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound863_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound864_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound865_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound866_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound867_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound868_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound872_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound873_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound877_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound878_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound881_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound883_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound884_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound885_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound887_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound888_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound891_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound894_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound897_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound898_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound899_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound902_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound906_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound909_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound911_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound912_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound913_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound917_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound919_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound91_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound922_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound923_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound925_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound926_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound927_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound928_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound929_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound92_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound932_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound933_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound935_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound936_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound937_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound938_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound939_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound940_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound941_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound942_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound947_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound949_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound94_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound950_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound954_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound956_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound959_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound962_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound963_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound964_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound966_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound967_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound968_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound971_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound973_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound975_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound976_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound977_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound97_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound981_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound983_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound987_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound991_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound992_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound99_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound9_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval100_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval105_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1075_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval108_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval111_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval113_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval117_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval118_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1194_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1225_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval122_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval126_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval12_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1315_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval131_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval136_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval137_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval141_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval143_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1465_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval151_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1523_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval152_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1554_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1555_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval155_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval164_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval165_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval169_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval174_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval175_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval181_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval185_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval18_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval190_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval201_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval202_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval211_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval212_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval217_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval21_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval220_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval224_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval226_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval229_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval232_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval234_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval235_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval242_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval246_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval250_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval256_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval260_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval264_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval266_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval268_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval269_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval275_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval280_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval285_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval286_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval287_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval289_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval296_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval301_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval308_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval310_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval316_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval325_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval332_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval335_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval338_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval339_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval341_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval343_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval351_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval352_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval356_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval357_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval358_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval359_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval366_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval369_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval372_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval378_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval37_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval382_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval383_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval385_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval390_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval398_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval39_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval405_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval408_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval413_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval46_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval474_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval476_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval53_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval55_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval56_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval63_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval69_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval73_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval74_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval79_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval84_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval86_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval8_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval92_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval957_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval145_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval147_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval150_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval215_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval216_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval219_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval21_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval220_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval223_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval238_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval373_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval375_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval44_e`, `OAI.MUB6.Certificate.PairSemantics.boundarySound26_e`, `OAI.MUB6.Certificate.PairSemantics.boundarySound49_e`, `OAI.MUB6.Certificate.PairSemantics.boundarySound58_e`, `OAI.MUB6.Certificate.PairSemantics.boundarySound73_e`, `OAI.MUB6.Certificate.PairSemantics.sound1379_e`, `OAI.MUB6.Certificate.PairSemantics.sound1381_e`, `OAI.MUB6.Certificate.PairSemantics.sound1383_e`, `OAI.MUB6.Certificate.PairSemantics.sound1384_e`, `OAI.MUB6.Certificate.PairSemantics.sound1387_e`, `OAI.MUB6.Certificate.PairSemantics.sound1390_e`, `OAI.MUB6.Certificate.PairSemantics.sound1391_e`, `OAI.MUB6.Certificate.PairSemantics.sound1395_e`, `OAI.MUB6.Certificate.PairSemantics.sound1399_e`, `OAI.MUB6.Certificate.PairSemantics.sound1414_e`, `OAI.MUB6.Certificate.PairSemantics.sound1419_e`, `OAI.MUB6.Certificate.PairSemantics.sound1423_e`, `OAI.MUB6.Certificate.PairSemantics.sound1424_e`, `OAI.MUB6.Certificate.PairSemantics.sound1425_e`, `OAI.MUB6.Certificate.PairSemantics.sound1434_e`, `OAI.MUB6.Certificate.PairSemantics.sound1437_e`, `OAI.MUB6.Certificate.PairSemantics.sound1443_e`, `OAI.MUB6.Certificate.PairSemantics.sound1458_e`, `OAI.MUB6.Certificate.PairSemantics.sound1486_e`, `OAI.MUB6.Certificate.PairSemantics.sound1504_e`, `OAI.MUB6.Certificate.PairSemantics.sound1506_e`, `OAI.MUB6.Certificate.PairSemantics.sound1512_e`, `OAI.MUB6.Certificate.PairSemantics.sound1518_e`, `OAI.MUB6.Certificate.PairSemantics.sound1529_e`, `OAI.MUB6.Certificate.PairSemantics.sound1530_e`, `OAI.MUB6.Certificate.PairSemantics.sound1531_e`, `OAI.MUB6.Certificate.PairSemantics.sound1535_e`, `OAI.MUB6.Certificate.PairSemantics.sound1540_e`, `OAI.MUB6.Certificate.PairSemantics.sound1548_e`, `OAI.MUB6.Certificate.PairSemantics.sound1605_e`, `OAI.MUB6.Certificate.PairSemantics.sound1614_e`, `OAI.MUB6.Certificate.PairSemantics.sound1617_e`, `OAI.MUB6.Certificate.PairSemantics.sound1624_e`, `OAI.MUB6.Certificate.PairSemantics.sound1627_e`, `OAI.MUB6.Certificate.PairSemantics.sound1628_e`, `OAI.MUB6.Certificate.PairSemantics.sound1631_e`, `OAI.MUB6.Certificate.PairSemantics.sound1634_e`, `OAI.MUB6.Certificate.PairSemantics.sound1635_e`, `OAI.MUB6.Certificate.PairSemantics.sound1637_e`, `OAI.MUB6.Certificate.PairSemantics.sound1644_e`, `OAI.MUB6.Certificate.PairSemantics.sound1646_e`, `OAI.MUB6.Certificate.PairSemantics.sound1648_e`, `OAI.MUB6.Certificate.PairSemantics.sound1685_e`, `OAI.MUB6.Certificate.PairSemantics.sound1716_e`, `OAI.MUB6.Certificate.PairSemantics.sound1736_e`, `OAI.MUB6.Certificate.PairSemantics.sound1739_e`, `OAI.MUB6.Certificate.PairSemantics.sound1768_e`, `OAI.MUB6.Certificate.PairSemantics.sound1770_e`, `OAI.MUB6.Certificate.PairSemantics.sound1793_e`, `OAI.MUB6.Certificate.PairSemantics.sound1800_e`, `OAI.MUB6.Certificate.PairSemantics.sound1828_e`, `OAI.MUB6.Certificate.PairSemantics.sound1849_e`, `OAI.MUB6.Certificate.PairSemantics.sound1858_e`, `OAI.MUB6.Certificate.PairSemantics.sound1860_e`, `OAI.MUB6.Certificate.PairSemantics.sound1865_e`, `OAI.MUB6.Certificate.PairSemantics.sound1866_e`, `OAI.MUB6.Certificate.PairSemantics.sound1867_e`, `OAI.MUB6.Certificate.PairSemantics.sound1869_e`, `OAI.MUB6.Certificate.PairSemantics.sound1870_e`, `OAI.MUB6.Certificate.PairSemantics.sound1872_e`, `OAI.MUB6.Certificate.PairSemantics.sound1875_e`, `OAI.MUB6.Certificate.PairSemantics.sound1876_e`, `OAI.MUB6.Certificate.PairSemantics.sound1879_e`, `OAI.MUB6.Certificate.PairSemantics.sound1885_e`, `OAI.MUB6.Certificate.PairSemantics.sound1978_e`, `OAI.MUB6.Certificate.PairSemantics.sound1980_e`, `OAI.MUB6.Certificate.PairSemantics.sound1986_e`, `OAI.MUB6.Certificate.PairSemantics.sound1987_e`, `OAI.MUB6.Certificate.PairSemantics.sound2041_e`, `OAI.MUB6.Certificate.PairSemantics.sound2058_e`, `OAI.MUB6.Certificate.PairSemantics.sound2071_e`, `OAI.MUB6.Certificate.PairSemantics.sound2097_e`, `OAI.MUB6.Certificate.PairSemantics.sound2106_e`, `OAI.MUB6.Certificate.PairSemantics.sound2107_e`, `OAI.MUB6.Certificate.PairSemantics.sound2108_e`, `OAI.MUB6.Certificate.PairSemantics.sound2117_e`, `OAI.MUB6.Certificate.PairSemantics.sound2122_e`, `OAI.MUB6.Certificate.PairSemantics.sound2123_e`, `OAI.MUB6.Certificate.PairSemantics.sound2128_e`, `OAI.MUB6.Certificate.PairSemantics.sound2132_e`, `OAI.MUB6.Certificate.PairSemantics.sound2152_e`, `OAI.MUB6.Certificate.PairSemantics.sound2168_e`, `OAI.MUB6.Certificate.PairSemantics.sound2175_e`, `OAI.MUB6.Certificate.PairSemantics.sound2177_e`, `OAI.MUB6.Certificate.PairSemantics.sound2189_e`, `OAI.MUB6.Certificate.PairSemantics.sound2190_e`, `OAI.MUB6.Certificate.PairSemantics.sound2197_e`, `OAI.MUB6.Certificate.PairSemantics.sound2201_e`, `OAI.MUB6.Certificate.PairSemantics.sound2202_e`, `OAI.MUB6.Certificate.PairSemantics.sound2213_e`, `OAI.MUB6.Certificate.PairSemantics.sound2228_e`, `OAI.MUB6.Certificate.PairSemantics.sound2244_e`, `OAI.MUB6.Certificate.PairSemantics.sound2262_e`, `OAI.MUB6.Certificate.PairSemantics.sound2284_e`, `OAI.MUB6.Certificate.PairSemantics.sound2286_e`, `OAI.MUB6.Certificate.PairSemantics.sound2293_e`, `OAI.MUB6.Certificate.PairSemantics.sound2294_e`, `OAI.MUB6.Certificate.PairSemantics.sound2295_e`, `OAI.MUB6.Certificate.PairSemantics.sound2296_e`, `OAI.MUB6.Certificate.PairSemantics.sound2312_e`, `OAI.MUB6.Certificate.PairSemantics.sound2324_e`, `OAI.MUB6.Certificate.PairSemantics.sound2327_e`, `OAI.MUB6.Certificate.PairSemantics.sound2338_e`, `OAI.MUB6.Certificate.PairSemantics.sound2375_e`, `OAI.MUB6.Certificate.PairSemantics.sound2382_e`, `OAI.MUB6.Certificate.PairSemantics.sound2390_e`, `OAI.MUB6.Certificate.PairSemantics.sound2391_e`, `OAI.MUB6.Certificate.PairSemantics.sound2394_e`, `OAI.MUB6.Certificate.PairSemantics.sound2399_e`, `OAI.MUB6.Certificate.PairSemantics.sound2400_e`, `OAI.MUB6.Certificate.PairSemantics.sound2401_e`, `OAI.MUB6.Certificate.PairSemantics.sound2403_e`, `OAI.MUB6.Certificate.PairSemantics.sound2415_e`, `OAI.MUB6.Certificate.PairSemantics.sound2416_e`, `OAI.MUB6.Certificate.PairSemantics.sound2420_e`, `OAI.MUB6.Certificate.PairSemantics.sound2433_e`, `OAI.MUB6.Certificate.PairSemantics.sound2434_e`, `OAI.MUB6.Certificate.PairSemantics.sound2435_e`, `OAI.MUB6.Certificate.PairSemantics.sound2436_e`, `OAI.MUB6.Certificate.PairSemantics.sound2442_e`, `OAI.MUB6.Certificate.PairSemantics.sound2444_e`, `OAI.MUB6.Certificate.PairSemantics.sound2445_e`, `OAI.MUB6.Certificate.PairSemantics.sound2454_e`, `OAI.MUB6.Certificate.PairSemantics.sound2456_e`, `OAI.MUB6.Certificate.PairSemantics.sound2457_e`, `OAI.MUB6.Certificate.PairSemantics.sound2463_e`, `OAI.MUB6.Certificate.PairSemantics.sound2464_e`, `OAI.MUB6.Certificate.PairSemantics.sound2465_e`, `OAI.MUB6.Certificate.PairSemantics.sound2472_e`, `OAI.MUB6.Certificate.PairSemantics.sound2473_e`, `OAI.MUB6.Certificate.PairSemantics.sound2477_e`, `OAI.MUB6.Certificate.PairSemantics.sound2479_e`, `OAI.MUB6.Certificate.PairSemantics.sound2489_e`, `OAI.MUB6.Certificate.PairSemantics.sound2490_e`, `OAI.MUB6.Certificate.PairSemantics.sound2491_e`, `OAI.MUB6.Certificate.PairSemantics.sound2492_e`, `OAI.MUB6.Certificate.PairSemantics.sound2507_e`, `OAI.MUB6.Certificate.PairSemantics.sound2520_e`, `OAI.MUB6.Certificate.PairSemantics.sound2521_e`, `OAI.MUB6.Certificate.PairSemantics.sound2522_e`, `OAI.MUB6.Certificate.PairSemantics.sound2524_e`, `OAI.MUB6.Certificate.PairSemantics.sound2525_e`, `OAI.MUB6.Certificate.PairSemantics.sound2527_e`, `OAI.MUB6.Certificate.PairSemantics.sound2533_e`, `OAI.MUB6.Certificate.PairSemantics.sound2540_e`, `OAI.MUB6.Certificate.PairSemantics.sound2546_e`, `OAI.MUB6.Certificate.PairSemantics.sound2547_e`, `OAI.MUB6.Certificate.PairSemantics.sound2548_e`, `OAI.MUB6.Certificate.PairSemantics.sound2557_e`, `OAI.MUB6.Certificate.PairSemantics.sound2558_e`, `OAI.MUB6.Certificate.PairSemantics.sound2559_e`, `OAI.MUB6.Certificate.PairSemantics.sound2564_e`, `OAI.MUB6.Certificate.PairSemantics.sound2565_e`, `OAI.MUB6.Certificate.PairSemantics.sound2566_e`, `OAI.MUB6.Certificate.PairSemantics.sound2573_e`, `OAI.MUB6.Certificate.PairSemantics.sound2578_e`, `OAI.MUB6.Certificate.PairSemantics.sound2580_e`, `OAI.MUB6.Certificate.PairSemantics.sound2593_e`, `OAI.MUB6.Certificate.PairSemantics.sound2602_e`, `OAI.MUB6.Certificate.PairSemantics.sound2604_e`, `OAI.MUB6.Certificate.PairSemantics.sound2606_e`, `OAI.MUB6.Certificate.PairSemantics.sound2619_e`, `OAI.MUB6.Certificate.PairSemantics.sound2620_e`, `OAI.MUB6.Certificate.PairSemantics.sound2623_e`, `OAI.MUB6.Certificate.PairSemantics.sound2627_e`, `OAI.MUB6.Certificate.PairSemantics.sound2641_e`, `OAI.MUB6.Certificate.PairSemantics.sound2657_e`, `OAI.MUB6.Certificate.PairSemantics.sound2658_e`, `OAI.MUB6.Certificate.PairSemantics.sound2661_e`, `OAI.MUB6.Certificate.PairSemantics.sound2666_e`, `OAI.MUB6.Certificate.PairSemantics.sound2669_e`, `OAI.MUB6.Certificate.PairSemantics.sound2670_e`, `OAI.MUB6.Certificate.PairSemantics.sound2671_e`, `OAI.MUB6.Certificate.PairSemantics.sound2686_e`, `OAI.MUB6.Certificate.PairSemantics.sound2690_e`, `OAI.MUB6.Certificate.PairSemantics.sound2693_e`, `OAI.MUB6.Certificate.PairSemantics.sound2698_e`, `OAI.MUB6.Certificate.PairSemantics.sound2708_e`, `OAI.MUB6.Certificate.PairSemantics.sound2710_e`, `OAI.MUB6.Certificate.PairSemantics.sound2714_e`, `OAI.MUB6.Certificate.PairSemantics.sound2729_e`, `OAI.MUB6.Certificate.PairSemantics.sound2732_e`, `OAI.MUB6.Certificate.PairSemantics.sound2733_e`, `OAI.MUB6.Certificate.PairSemantics.sound2735_e`, `OAI.MUB6.Certificate.PairSemantics.sound2754_e`, `OAI.MUB6.Certificate.PairSemantics.sound2757_e`, `OAI.MUB6.Certificate.PairSemantics.sound2788_e`, `OAI.MUB6.Certificate.PairSemantics.sound2790_e`, `OAI.MUB6.Certificate.PairSemantics.sound2793_e`, `OAI.MUB6.Certificate.PairSemantics.sound2807_e`, `OAI.MUB6.Certificate.PairSemantics.sound2817_e`, `OAI.MUB6.Certificate.PairSemantics.sound2829_e`, `OAI.MUB6.Certificate.PairSemantics.sound2836_e`, `OAI.MUB6.Certificate.PairSemantics.sound2845_e`, `OAI.MUB6.Certificate.PairSemantics.sound2853_e`, `OAI.MUB6.Certificate.PairSemantics.sound2854_e`, `OAI.MUB6.Certificate.PairSemantics.sound2858_e`, `OAI.MUB6.Certificate.PairSemantics.sound2863_e`, `OAI.MUB6.Certificate.PairSemantics.sound2864_e`, `OAI.MUB6.Certificate.PairSemantics.sound2865_e`, `OAI.MUB6.Certificate.PairSemantics.sound2866_e`, `OAI.MUB6.Certificate.PairSemantics.sound2867_e`, `OAI.MUB6.Certificate.PairSemantics.sound2868_e`, `OAI.MUB6.Certificate.PairSemantics.sound2872_e`, `OAI.MUB6.Certificate.PairSemantics.sound2873_e`, `OAI.MUB6.Certificate.PairSemantics.sound2874_e`, `OAI.MUB6.Certificate.PairSemantics.sound2875_e`, `OAI.MUB6.Certificate.PairSemantics.sound2878_e`, `OAI.MUB6.Certificate.PairSemantics.sound2879_e`, `OAI.MUB6.Certificate.PairSemantics.sound2880_e`, `OAI.MUB6.Certificate.PairSemantics.sound2882_e`, `OAI.MUB6.Certificate.PairSemantics.sound2883_e`, `OAI.MUB6.Certificate.PairSemantics.sound2884_e`, `OAI.MUB6.Certificate.PairSemantics.sound2887_e`, `OAI.MUB6.Certificate.PairSemantics.sound2888_e`, `OAI.MUB6.Certificate.PairSemantics.sound2889_e`, `OAI.MUB6.Certificate.PairSemantics.sound2890_e`, `OAI.MUB6.Certificate.PairSemantics.sound2891_e`, `OAI.MUB6.Certificate.PairSemantics.sound2892_e`, `OAI.MUB6.Certificate.PairSemantics.sound2894_e`, `OAI.MUB6.Certificate.PairSemantics.sound2895_e`, `OAI.MUB6.Certificate.PairSemantics.sound2896_e`, `OAI.MUB6.Certificate.PairSemantics.sound2897_e`, `OAI.MUB6.Certificate.PairSemantics.sound2898_e`, `OAI.MUB6.Certificate.PairSemantics.sound2899_e`, `OAI.MUB6.Certificate.PairSemantics.sound2900_e`, `OAI.MUB6.Certificate.PairSemantics.sound2901_e`, `OAI.MUB6.Certificate.PairSemantics.sound2902_e`, `OAI.MUB6.Certificate.PairSemantics.sound2904_e`, `OAI.MUB6.Certificate.PairSemantics.sound2905_e`, `OAI.MUB6.Certificate.PairSemantics.sound2906_e`, `OAI.MUB6.Certificate.PairSemantics.sound2908_e`, `OAI.MUB6.Certificate.PairSemantics.sound2909_e`, `OAI.MUB6.Certificate.PairSemantics.sound2910_e`, `OAI.MUB6.Certificate.PairSemantics.sound2912_e`, `OAI.MUB6.Certificate.PairSemantics.sound2913_e`, `OAI.MUB6.Certificate.PairSemantics.sound2914_e`, `OAI.MUB6.Certificate.PairSemantics.sound2915_e`, `OAI.MUB6.Certificate.PairSemantics.sound2916_e`, `OAI.MUB6.Certificate.PairSemantics.sound2917_e`, `OAI.MUB6.Certificate.PairSemantics.sound2919_e`, `OAI.MUB6.Certificate.PairSemantics.sound2920_e`, `OAI.MUB6.Certificate.PairSemantics.sound2922_e`, `OAI.MUB6.Certificate.PairSemantics.sound2924_e`, `OAI.MUB6.Certificate.PairSemantics.sound2925_e`, `OAI.MUB6.Certificate.PairSemantics.sound2926_e`, `OAI.MUB6.Certificate.PairSemantics.sound2927_e`, `OAI.MUB6.Certificate.PairSemantics.sound2928_e`, `OAI.MUB6.Certificate.PairSemantics.sound2929_e`, `OAI.MUB6.Certificate.PairSemantics.sound2931_e`, `OAI.MUB6.Certificate.PairSemantics.sound2933_e`, `OAI.MUB6.Certificate.PairSemantics.sound2935_e`, `OAI.MUB6.Certificate.PairSemantics.sound2936_e`, `OAI.MUB6.Certificate.PairSemantics.sound2939_e`, `OAI.MUB6.Certificate.PairSemantics.sound2940_e`, `OAI.MUB6.Certificate.PairSemantics.sound2941_e`, `OAI.MUB6.Certificate.PairSemantics.sound2942_e`, `OAI.MUB6.Certificate.PairSemantics.sound2943_e`, `OAI.MUB6.Certificate.PairSemantics.sound2944_e`, `OAI.MUB6.Certificate.PairSemantics.sound2946_e`, `OAI.MUB6.Certificate.PairSemantics.sound2949_e`, `OAI.MUB6.Certificate.PairSemantics.sound2950_e`, `OAI.MUB6.Certificate.PairSemantics.sound2951_e`, `OAI.MUB6.Certificate.PairSemantics.sound2952_e`, `OAI.MUB6.Certificate.PairSemantics.sound2953_e`, `OAI.MUB6.Certificate.PairSemantics.sound2954_e`, `OAI.MUB6.Certificate.PairSemantics.sound2956_e`, `OAI.MUB6.Certificate.PairSemantics.sound2957_e`, `OAI.MUB6.Certificate.PairSemantics.sound2959_e`, `OAI.MUB6.Certificate.PairSemantics.sound2960_e`, `OAI.MUB6.Certificate.PairSemantics.sound2961_e`, `OAI.MUB6.Certificate.PairSemantics.sound2962_e`, `OAI.MUB6.Certificate.PairSemantics.sound2963_e`, `OAI.MUB6.Certificate.PairSemantics.sound2964_e`, `OAI.MUB6.Certificate.PairSemantics.sound2965_e`, `OAI.MUB6.Certificate.PairSemantics.sound2966_e`, `OAI.MUB6.Certificate.PairSemantics.sound2967_e`, `OAI.MUB6.Certificate.PairSemantics.sound2968_e`, `OAI.MUB6.Certificate.PairSemantics.sound2969_e`, `OAI.MUB6.Certificate.PairSemantics.sound2970_e`, `OAI.MUB6.Certificate.PairSemantics.sound2972_e`, `OAI.MUB6.Certificate.PairSemantics.sound2973_e`, `OAI.MUB6.Certificate.PairSemantics.sound2974_e`, `OAI.MUB6.Certificate.PairSemantics.sound2975_e`, `OAI.MUB6.Certificate.PairSemantics.sound2976_e`, `OAI.MUB6.Certificate.PairSemantics.sound2977_e`, `OAI.MUB6.Certificate.PairSemantics.sound2979_e`, `OAI.MUB6.Certificate.PairSemantics.sound2980_e`, `OAI.MUB6.Certificate.PairSemantics.sound2984_e`, `OAI.MUB6.Certificate.PairSemantics.sound2985_e`, `OAI.MUB6.Certificate.PairSemantics.sound2986_e`, `OAI.MUB6.Certificate.PairSemantics.sound2987_e`, `OAI.MUB6.Certificate.PairSemantics.sound2989_e`, `OAI.MUB6.Certificate.PairSemantics.sound2990_e`, `OAI.MUB6.Certificate.PairSemantics.sound2991_e`, `OAI.MUB6.Certificate.PairSemantics.sound2992_e`, `OAI.MUB6.Certificate.PairSemantics.sound2994_e`, `OAI.MUB6.Certificate.PairSemantics.sound2996_e`, `OAI.MUB6.Certificate.PairSemantics.sound2997_e`, `OAI.MUB6.Certificate.PairSemantics.sound2998_e`, `OAI.MUB6.Certificate.PairSemantics.sound2999_e`, `OAI.MUB6.Certificate.PairSemantics.sound3000_e`, `OAI.MUB6.Certificate.PairSemantics.sound3001_e`, `OAI.MUB6.Certificate.PairSemantics.sound3002_e`, `OAI.MUB6.Certificate.PairSemantics.sound3004_e`, `OAI.MUB6.Certificate.PairSemantics.sound3006_e`, `OAI.MUB6.Certificate.PairSemantics.sound3007_e`, `OAI.MUB6.Certificate.PairSemantics.sound3009_e`, `OAI.MUB6.Certificate.PairSemantics.sound3011_e`, `OAI.MUB6.Certificate.PairSemantics.sound3012_e`, `OAI.MUB6.Certificate.PairSemantics.sound3013_e`, `OAI.MUB6.Certificate.PairSemantics.sound3014_e`, `OAI.MUB6.Certificate.PairSemantics.sound3015_e`, `OAI.MUB6.Certificate.PairSemantics.sound3016_e`, `OAI.MUB6.Certificate.PairSemantics.sound3017_e`, `OAI.MUB6.Certificate.PairSemantics.sound3018_e`, `OAI.MUB6.Certificate.PairSemantics.sound3019_e`, `OAI.MUB6.Certificate.PairSemantics.sound3020_e`, `OAI.MUB6.Certificate.PairSemantics.sound3021_e`, `OAI.MUB6.Certificate.PairSemantics.sound3022_e`, `OAI.MUB6.Certificate.PairSemantics.sound3023_e`, `OAI.MUB6.Certificate.PairSemantics.sound3024_e`, `OAI.MUB6.Certificate.PairSemantics.sound3025_e`, `OAI.MUB6.Certificate.PairSemantics.sound3026_e`, `OAI.MUB6.Certificate.PairSemantics.sound3027_e`, `OAI.MUB6.Certificate.PairSemantics.sound3028_e`, `OAI.MUB6.Certificate.PairSemantics.sound3029_e`, `OAI.MUB6.Certificate.PairSemantics.sound3030_e`, `OAI.MUB6.Certificate.PairSemantics.sound3032_e`, `OAI.MUB6.Certificate.PairSemantics.sound3034_e`, `OAI.MUB6.Certificate.PairSemantics.sound3035_e`, `OAI.MUB6.Certificate.PairSemantics.sound3036_e`, `OAI.MUB6.Certificate.PairSemantics.sound3037_e`, `OAI.MUB6.Certificate.PairSemantics.sound3038_e`, `OAI.MUB6.Certificate.PairSemantics.sound3039_e`, `OAI.MUB6.Certificate.PairSemantics.sound3040_e`, `OAI.MUB6.Certificate.PairSemantics.sound3041_e`, `OAI.MUB6.Certificate.PairSemantics.sound3042_e`, `OAI.MUB6.Certificate.PairSemantics.sound3045_e`, `OAI.MUB6.Certificate.PairSemantics.sound3049_e`, `OAI.MUB6.Certificate.PairSemantics.sound3050_e`, `OAI.MUB6.Certificate.PairSemantics.sound3051_e`, `OAI.MUB6.Certificate.PairSemantics.sound3052_e`, `OAI.MUB6.Certificate.PairSemantics.sound3053_e`, `OAI.MUB6.Certificate.PairSemantics.sound3054_e`, `OAI.MUB6.Certificate.PairSemantics.sound3055_e`, `OAI.MUB6.Certificate.PairSemantics.sound3057_e`, `OAI.MUB6.Certificate.PairSemantics.sound3059_e`, `OAI.MUB6.Certificate.PairSemantics.sound3060_e`, `OAI.MUB6.Certificate.PairSemantics.sound3061_e`, `OAI.MUB6.Certificate.PairSemantics.sound3062_e`, `OAI.MUB6.Certificate.PairSemantics.sound3063_e`, `OAI.MUB6.Certificate.PairSemantics.sound3065_e`, `OAI.MUB6.Certificate.PairSemantics.sound3066_e`, `OAI.MUB6.Certificate.PairSemantics.sound3067_e`, `OAI.MUB6.Certificate.PairSemantics.sound3068_e`, `OAI.MUB6.Certificate.PairSemantics.sound3069_e`, `OAI.MUB6.Certificate.PairSemantics.sound3071_e`, `OAI.MUB6.Certificate.PairSemantics.sound3072_e`, `OAI.MUB6.Certificate.PairSemantics.sound3073_e`, `OAI.MUB6.Certificate.PairSemantics.sound3074_e`, `OAI.MUB6.Certificate.PairSemantics.sound3075_e`, `OAI.MUB6.Certificate.PairSemantics.sound3076_e`, `OAI.MUB6.Certificate.PairSemantics.sound3077_e`, `OAI.MUB6.Certificate.PairSemantics.sound3078_e`, `OAI.MUB6.Certificate.PairSemantics.sound3079_e`, `OAI.MUB6.Certificate.PairSemantics.sound3081_e`, `OAI.MUB6.Certificate.PairSemantics.sound3082_e`, `OAI.MUB6.Certificate.PairSemantics.sound3084_e`, `OAI.MUB6.Certificate.PairSemantics.sound3085_e`, `OAI.MUB6.Certificate.PairSemantics.sound3086_e`, `OAI.MUB6.Certificate.PairSemantics.sound3087_e`, `OAI.MUB6.Certificate.PairSemantics.sound3088_e`, `OAI.MUB6.Certificate.PairSemantics.sound3090_e`, `OAI.MUB6.Certificate.PairSemantics.sound3091_e`, `OAI.MUB6.Certificate.PairSemantics.sound3092_e`, `OAI.MUB6.Certificate.PairSemantics.sound3093_e`, `OAI.MUB6.Certificate.PairSemantics.sound3094_e`, `OAI.MUB6.Certificate.PairSemantics.sound3095_e`, `OAI.MUB6.Certificate.PairSemantics.sound3096_e`, `OAI.MUB6.Certificate.PairSemantics.sound3098_e`, `OAI.MUB6.Certificate.PairSemantics.sound3099_e`, `OAI.MUB6.Certificate.PairSemantics.sound3100_e`, `OAI.MUB6.Certificate.PairSemantics.sound3101_e`, `OAI.MUB6.Certificate.PairSemantics.sound3105_e`, `OAI.MUB6.Certificate.PairSemantics.sound3106_e`, `OAI.MUB6.Certificate.PairSemantics.sound3107_e`, `OAI.MUB6.Certificate.PairSemantics.sound3108_e`, `OAI.MUB6.Certificate.PairSemantics.sound3110_e`, `OAI.MUB6.Certificate.PairSemantics.sound3111_e`, `OAI.MUB6.Certificate.PairSemantics.sound3112_e`, `OAI.MUB6.Certificate.PairSemantics.sound3113_e`, `OAI.MUB6.Certificate.PairSemantics.sound3114_e`, `OAI.MUB6.Certificate.PairSemantics.sound3115_e`, `OAI.MUB6.Certificate.PairSemantics.sound3118_e`, `OAI.MUB6.Certificate.PairSemantics.sound3119_e`, `OAI.MUB6.Certificate.PairSemantics.sound3120_e`, `OAI.MUB6.Certificate.PairSemantics.sound3122_e`, `OAI.MUB6.Certificate.PairSemantics.sound3123_e`, `OAI.MUB6.Certificate.PairSemantics.sound3124_e`, `OAI.MUB6.Certificate.PairSemantics.sound3125_e`, `OAI.MUB6.Certificate.PairSemantics.sound3127_e`, `OAI.MUB6.Certificate.PairSemantics.sound3128_e`, `OAI.MUB6.Certificate.PairSemantics.sound3129_e`, `OAI.MUB6.Certificate.PairSemantics.sound3130_e`, `OAI.MUB6.Certificate.PairSemantics.sound3131_e`, `OAI.MUB6.Certificate.PairSemantics.sound3132_e`, `OAI.MUB6.Certificate.PairSemantics.sound3133_e`, `OAI.MUB6.Certificate.PairSemantics.sound3135_e`, `OAI.MUB6.Certificate.PairSemantics.sound3136_e`, `OAI.MUB6.Certificate.PairSemantics.sound3137_e`, `OAI.MUB6.Certificate.PairSemantics.sound3138_e`, `OAI.MUB6.Certificate.PairSemantics.sound3139_e`, `OAI.MUB6.Certificate.PairSemantics.sound3140_e`, `OAI.MUB6.Certificate.PairSemantics.sound3141_e`, `OAI.MUB6.Certificate.PairSemantics.sound3142_e`, `OAI.MUB6.Certificate.PairSemantics.sound3144_e`, `OAI.MUB6.Certificate.PairSemantics.sound3145_e`, `OAI.MUB6.Certificate.PairSemantics.sound3146_e`, `OAI.MUB6.Certificate.PairSemantics.sound3149_e`, `OAI.MUB6.Certificate.PairSemantics.sound3150_e`, `OAI.MUB6.Certificate.PairSemantics.sound3151_e`, `OAI.MUB6.Certificate.PairSemantics.sound3152_e`, `OAI.MUB6.Certificate.PairSemantics.sound3153_e`, `OAI.MUB6.Certificate.PairSemantics.sound3154_e`, `OAI.MUB6.Certificate.PairSemantics.sound3158_e`, `OAI.MUB6.Certificate.PairSemantics.sound3159_e`, `OAI.MUB6.Certificate.PairSemantics.sound3160_e`, `OAI.MUB6.Certificate.PairSemantics.sound3161_e`, `OAI.MUB6.Certificate.PairSemantics.sound3163_e`, `OAI.MUB6.Certificate.PairSemantics.sound3164_e`, `OAI.MUB6.Certificate.PairSemantics.sound3166_e`, `OAI.MUB6.Certificate.PairSemantics.sound3167_e`, `OAI.MUB6.Certificate.PairSemantics.sound3169_e`, `OAI.MUB6.Certificate.PairSemantics.sound3170_e`, `OAI.MUB6.Certificate.PairSemantics.sound3171_e`, `OAI.MUB6.Certificate.PairSemantics.sound3172_e`, `OAI.MUB6.Certificate.PairSemantics.sound3173_e`, `OAI.MUB6.Certificate.PairSemantics.sound3174_e`, `OAI.MUB6.Certificate.PairSemantics.sound3176_e`, `OAI.MUB6.Certificate.PairSemantics.sound3178_e`, `OAI.MUB6.Certificate.PairSemantics.sound3179_e`, `OAI.MUB6.Certificate.PairSemantics.sound3180_e`, `OAI.MUB6.Certificate.PairSemantics.sound3181_e`, `OAI.MUB6.Certificate.PairSemantics.sound3183_e`, `OAI.MUB6.Certificate.PairSemantics.sound3184_e`, `OAI.MUB6.Certificate.PairSemantics.sound3185_e`, `OAI.MUB6.Certificate.PairSemantics.sound3187_e`, `OAI.MUB6.Certificate.PairSemantics.sound3188_e`, `OAI.MUB6.Certificate.PairSemantics.sound3189_e`, `OAI.MUB6.Certificate.PairSemantics.sound3191_e`, `OAI.MUB6.Certificate.PairSemantics.sound3192_e`, `OAI.MUB6.Certificate.PairSemantics.sound3193_e`, `OAI.MUB6.Certificate.PairSemantics.sound3194_e`, `OAI.MUB6.Certificate.PairSemantics.sound3195_e`, `OAI.MUB6.Certificate.PairSemantics.sound3196_e`, `OAI.MUB6.Certificate.PairSemantics.sound3197_e`, `OAI.MUB6.Certificate.PairSemantics.sound3198_e`, `OAI.MUB6.Certificate.PairSemantics.sound3199_e`, `OAI.MUB6.Certificate.PairSemantics.sound3200_e`, `OAI.MUB6.Certificate.PairSemantics.sound3201_e`, `OAI.MUB6.Certificate.PairSemantics.sound3202_e`, `OAI.MUB6.Certificate.PairSemantics.sound3203_e`, `OAI.MUB6.Certificate.PairSemantics.sound3204_e`, `OAI.MUB6.Certificate.PairSemantics.sound3205_e`, `OAI.MUB6.Certificate.PairSemantics.sound3206_e`, `OAI.MUB6.Certificate.PairSemantics.sound3208_e`, `OAI.MUB6.Certificate.PairSemantics.sound3209_e`, `OAI.MUB6.Certificate.PairSemantics.sound3211_e`, `OAI.MUB6.Certificate.PairSemantics.sound3212_e`, `OAI.MUB6.Certificate.PairSemantics.sound3213_e`, `OAI.MUB6.Certificate.PairSemantics.sound3215_e`, `OAI.MUB6.Certificate.PairSemantics.sound3216_e`, `OAI.MUB6.Certificate.PairSemantics.sound3218_e`, `OAI.MUB6.Certificate.PairSemantics.sound3220_e`, `OAI.MUB6.Certificate.PairSemantics.sound3221_e`, `OAI.MUB6.Certificate.PairSemantics.sound3222_e`, `OAI.MUB6.Certificate.PairSemantics.sound3223_e`, `OAI.MUB6.Certificate.PairSemantics.sound3224_e`, `OAI.MUB6.Certificate.PairSemantics.sound3225_e`, `OAI.MUB6.Certificate.PairSemantics.sound3226_e`, `OAI.MUB6.Certificate.PairSemantics.sound3227_e`, `OAI.MUB6.Certificate.PairSemantics.sound3228_e`, `OAI.MUB6.Certificate.PairSemantics.sound3229_e`, `OAI.MUB6.Certificate.PairSemantics.sound3230_e`, `OAI.MUB6.Certificate.PairSemantics.sound3233_e`, `OAI.MUB6.Certificate.PairSemantics.sound3234_e`, `OAI.MUB6.Certificate.PairSemantics.sound3235_e`, `OAI.MUB6.Certificate.PairSemantics.sound3237_e`, `OAI.MUB6.Certificate.PairSemantics.sound3238_e`, `OAI.MUB6.Certificate.PairSemantics.sound3240_e`, `OAI.MUB6.Certificate.PairSemantics.sound3242_e`, `OAI.MUB6.Certificate.PairSemantics.sound3243_e`, `OAI.MUB6.Certificate.PairSemantics.sound3244_e`, `OAI.MUB6.Certificate.PairSemantics.sound3246_e`, `OAI.MUB6.Certificate.PairSemantics.sound3247_e`, `OAI.MUB6.Certificate.PairSemantics.sound3248_e`, `OAI.MUB6.Certificate.PairSemantics.sound3249_e`, `OAI.MUB6.Certificate.PairSemantics.sound3253_e`, `OAI.MUB6.Certificate.PairSemantics.sound3254_e`, `OAI.MUB6.Certificate.PairSemantics.sound3255_e`, `OAI.MUB6.Certificate.PairSemantics.sound3256_e`, `OAI.MUB6.Certificate.PairSemantics.sound3258_e`, `OAI.MUB6.Certificate.PairSemantics.sound3260_e`, `OAI.MUB6.Certificate.PairSemantics.sound3262_e`, `OAI.MUB6.Certificate.PairSemantics.sound3263_e`, `OAI.MUB6.Certificate.PairSemantics.sound3264_e`, `OAI.MUB6.Certificate.PairSemantics.sound3266_e`, `OAI.MUB6.Certificate.PairSemantics.sound3267_e`, `OAI.MUB6.Certificate.PairSemantics.sound3268_e`, `OAI.MUB6.Certificate.PairSemantics.sound3269_e`, `OAI.MUB6.Certificate.PairSemantics.sound3271_e`, `OAI.MUB6.Certificate.PairSemantics.sound3272_e`, `OAI.MUB6.Certificate.PairSemantics.sound3273_e`, `OAI.MUB6.Certificate.PairSemantics.sound3274_e`, `OAI.MUB6.Certificate.PairSemantics.sound3275_e`, `OAI.MUB6.Certificate.PairSemantics.sound3276_e`, `OAI.MUB6.Certificate.PairSemantics.sound3277_e`, `OAI.MUB6.Certificate.PairSemantics.sound3278_e`, `OAI.MUB6.Certificate.PairSemantics.sound3279_e`, `OAI.MUB6.Certificate.PairSemantics.sound3280_e`, `OAI.MUB6.Certificate.PairSemantics.sound3281_e`, `OAI.MUB6.Certificate.PairSemantics.sound3282_e`, `OAI.MUB6.Certificate.PairSemantics.sound3283_e`, `OAI.MUB6.Certificate.PairSemantics.sound3284_e`, `OAI.MUB6.Certificate.PairSemantics.sound3288_e`, `OAI.MUB6.Certificate.PairSemantics.sound3289_e`, `OAI.MUB6.Certificate.PairSemantics.sound3290_e`, `OAI.MUB6.Certificate.PairSemantics.sound3291_e`, `OAI.MUB6.Certificate.PairSemantics.sound3292_e`, `OAI.MUB6.Certificate.PairSemantics.sound3293_e`, `OAI.MUB6.Certificate.PairSemantics.sound3294_e`, `OAI.MUB6.Certificate.PairSemantics.sound3295_e`, `OAI.MUB6.Certificate.PairSemantics.sound3296_e`, `OAI.MUB6.Certificate.PairSemantics.sound3297_e`, `OAI.MUB6.Certificate.PairSemantics.sound3298_e`, `OAI.MUB6.Certificate.PairSemantics.sound3299_e`, `OAI.MUB6.Certificate.PairSemantics.sound3300_e`, `OAI.MUB6.Certificate.PairSemantics.sound3301_e`, `OAI.MUB6.Certificate.PairSemantics.sound3302_e`, `OAI.MUB6.Certificate.PairSemantics.sound3303_e`, `OAI.MUB6.Certificate.PairSemantics.sound3304_e`, `OAI.MUB6.Certificate.PairSemantics.sound3305_e`, `OAI.MUB6.Certificate.PairSemantics.sound3307_e`, `OAI.MUB6.Certificate.PairSemantics.sound3308_e`, `OAI.MUB6.Certificate.PairSemantics.sound3309_e`, `OAI.MUB6.Certificate.PairSemantics.sound3310_e`, `OAI.MUB6.Certificate.PairSemantics.sound3311_e`, `OAI.MUB6.Certificate.PairSemantics.sound3313_e`, `OAI.MUB6.Certificate.PairSemantics.sound3314_e`, `OAI.MUB6.Certificate.PairSemantics.sound3315_e`, `OAI.MUB6.Certificate.PairSemantics.sound3316_e`, `OAI.MUB6.Certificate.PairSemantics.sound3317_e`, `OAI.MUB6.Certificate.PairSemantics.sound3319_e`, `OAI.MUB6.Certificate.PairSemantics.sound3322_e`, `OAI.MUB6.Certificate.PairSemantics.sound3324_e`, `OAI.MUB6.Certificate.PairSemantics.sound3325_e`, `OAI.MUB6.Certificate.PairSemantics.sound3326_e`, `OAI.MUB6.Certificate.PairSemantics.sound3327_e`, `OAI.MUB6.Certificate.PairSemantics.sound3328_e`, `OAI.MUB6.Certificate.PairSemantics.sound3331_e`, `OAI.MUB6.Certificate.PairSemantics.sound3333_e`, `OAI.MUB6.Certificate.PairSemantics.sound3334_e`, `OAI.MUB6.Certificate.PairSemantics.sound3335_e`, `OAI.MUB6.Certificate.PairSemantics.sound3336_e`, `OAI.MUB6.Certificate.PairSemantics.sound3338_e`, `OAI.MUB6.Certificate.PairSemantics.sound3339_e`, `OAI.MUB6.Certificate.PairSemantics.sound3341_e`, `OAI.MUB6.Certificate.PairSemantics.sound3343_e`, `OAI.MUB6.Certificate.PairSemantics.sound3345_e`, `OAI.MUB6.Certificate.PairSemantics.sound3346_e`, `OAI.MUB6.Certificate.PairSemantics.sound3347_e`, `OAI.MUB6.Certificate.PairSemantics.sound3348_e`, `OAI.MUB6.Certificate.PairSemantics.sound3349_e`, `OAI.MUB6.Certificate.PairSemantics.sound3350_e`, `OAI.MUB6.Certificate.PairSemantics.sound3351_e`, `OAI.MUB6.Certificate.PairSemantics.sound3352_e`, `OAI.MUB6.Certificate.PairSemantics.sound3353_e`, `OAI.MUB6.Certificate.PairSemantics.sound3354_e`, `OAI.MUB6.Certificate.PairSemantics.sound3355_e`, `OAI.MUB6.Certificate.PairSemantics.sound3356_e`, `OAI.MUB6.Certificate.PairSemantics.sound3357_e`, `OAI.MUB6.Certificate.PairSemantics.sound3358_e`, `OAI.MUB6.Certificate.PairSemantics.sound3359_e`, `OAI.MUB6.Certificate.PairSemantics.sound3360_e`, `OAI.MUB6.Certificate.PairSemantics.sound3361_e`, `OAI.MUB6.Certificate.PairSemantics.sound3362_e`, `OAI.MUB6.Certificate.PairSemantics.sound3363_e`, `OAI.MUB6.Certificate.PairSemantics.sound3364_e`, `OAI.MUB6.Certificate.PairSemantics.sound3366_e`, `OAI.MUB6.Certificate.PairSemantics.sound3367_e`, `OAI.MUB6.Certificate.PairSemantics.sound3368_e`, `OAI.MUB6.Certificate.PairSemantics.sound3369_e`, `OAI.MUB6.Certificate.PairSemantics.sound3370_e`, `OAI.MUB6.Certificate.PairSemantics.sound3371_e`, `OAI.MUB6.Certificate.PairSemantics.sound3372_e`, `OAI.MUB6.Certificate.PairSemantics.sound3375_e`, `OAI.MUB6.Certificate.PairSemantics.sound3376_e`, `OAI.MUB6.Certificate.PairSemantics.sound3377_e`, `OAI.MUB6.Certificate.PairSemantics.sound3378_e`, `OAI.MUB6.Certificate.PairSemantics.sound3380_e`, `OAI.MUB6.Certificate.PairSemantics.sound3382_e`, `OAI.MUB6.Certificate.PairSemantics.sound3383_e`, `OAI.MUB6.Certificate.PairSemantics.sound3384_e`, `OAI.MUB6.Certificate.PairSemantics.sound3385_e`, `OAI.MUB6.Certificate.PairSemantics.sound3387_e`, `OAI.MUB6.Certificate.PairSemantics.sound3388_e`, `OAI.MUB6.Certificate.PairSemantics.sound3389_e`, `OAI.MUB6.Certificate.PairSemantics.sound3390_e`, `OAI.MUB6.Certificate.PairSemantics.sound3391_e`, `OAI.MUB6.Certificate.PairSemantics.sound3392_e`, `OAI.MUB6.Certificate.PairSemantics.sound3393_e`, `OAI.MUB6.Certificate.PairSemantics.sound3394_e`, `OAI.MUB6.Certificate.PairSemantics.sound3395_e`, `OAI.MUB6.Certificate.PairSemantics.sound3396_e`, `OAI.MUB6.Certificate.PairSemantics.sound3397_e`, `OAI.MUB6.Certificate.PairSemantics.sound3399_e`, `OAI.MUB6.Certificate.PairSemantics.sound3400_e`, `OAI.MUB6.Certificate.PairSemantics.sound3401_e`, `OAI.MUB6.Certificate.PairSemantics.sound3402_e`, `OAI.MUB6.Certificate.PairSemantics.sound3405_e`, `OAI.MUB6.Certificate.PairSemantics.sound3407_e`, `OAI.MUB6.Certificate.PairSemantics.sound3408_e`, `OAI.MUB6.Certificate.PairSemantics.sound3411_e`, `OAI.MUB6.Certificate.PairSemantics.sound3412_e`, `OAI.MUB6.Certificate.PairSemantics.sound3413_e`, `OAI.MUB6.Certificate.PairSemantics.sound3414_e`, `OAI.MUB6.Certificate.PairSemantics.sound3415_e`, `OAI.MUB6.Certificate.PairSemantics.sound3416_e`, `OAI.MUB6.Certificate.PairSemantics.sound3417_e`, `OAI.MUB6.Certificate.PairSemantics.sound3418_e`, `OAI.MUB6.Certificate.PairSemantics.sound3419_e`, `OAI.MUB6.Certificate.PairSemantics.sound3420_e`, `OAI.MUB6.Certificate.PairSemantics.sound3421_e`, `OAI.MUB6.Certificate.PairSemantics.sound3422_e`, `OAI.MUB6.Certificate.PairSemantics.sound3423_e`, `OAI.MUB6.Certificate.PairSemantics.sound3424_e`, `OAI.MUB6.Certificate.PairSemantics.sound3425_e`, `OAI.MUB6.Certificate.PairSemantics.sound3428_e`, `OAI.MUB6.Certificate.PairSemantics.sound3431_e`, `OAI.MUB6.Certificate.PairSemantics.sound3433_e`, `OAI.MUB6.Certificate.PairSemantics.sound3434_e`, `OAI.MUB6.Certificate.PairSemantics.sound3435_e`, `OAI.MUB6.Certificate.PairSemantics.sound3436_e`, `OAI.MUB6.Certificate.PairSemantics.sound3437_e`, `OAI.MUB6.Certificate.PairSemantics.sound3439_e`, `OAI.MUB6.Certificate.PairSemantics.sound3440_e`, `OAI.MUB6.Certificate.PairSemantics.sound3441_e`, `OAI.MUB6.Certificate.PairSemantics.sound3442_e`, `OAI.MUB6.Certificate.PairSemantics.sound3443_e`, `OAI.MUB6.Certificate.PairSemantics.sound3444_e`, `OAI.MUB6.Certificate.PairSemantics.sound3447_e`, `OAI.MUB6.Certificate.PairSemantics.sound3449_e`, `OAI.MUB6.Certificate.PairSemantics.sound3451_e`, `OAI.MUB6.Certificate.PairSemantics.sound3454_e`, `OAI.MUB6.Certificate.PairSemantics.sound3455_e`, `OAI.MUB6.Certificate.PairSemantics.sound3456_e`, `OAI.MUB6.Certificate.PairSemantics.sound3457_e`, `OAI.MUB6.Certificate.PairSemantics.sound3458_e`, `OAI.MUB6.Certificate.PairSemantics.sound3459_e`, `OAI.MUB6.Certificate.PairSemantics.sound3460_e`, `OAI.MUB6.Certificate.PairSemantics.sound3461_e`, `OAI.MUB6.Certificate.PairSemantics.sound3462_e`, `OAI.MUB6.Certificate.PairSemantics.sound3463_e`, `OAI.MUB6.Certificate.PairSemantics.sound3467_e`, `OAI.MUB6.Certificate.PairSemantics.sound3468_e`, `OAI.MUB6.Certificate.PairSourceBridge.allRowsSound_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound0_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound100_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound101_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound102_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound103_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound104_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound105_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound106_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound107_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound108_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound10_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound110_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound111_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound112_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound113_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound114_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound115_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound116_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound117_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound118_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound119_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound120_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound121_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound123_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound124_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound125_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound127_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound128_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound129_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound12_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound130_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound131_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound132_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound133_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound134_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound135_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound136_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound137_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound138_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound139_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound140_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound141_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound142_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound143_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound144_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound145_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound146_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound147_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound148_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound149_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound14_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound150_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound151_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound152_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound153_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound154_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound155_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound156_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound157_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound158_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound159_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound15_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound160_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound161_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound162_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound163_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound164_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound165_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound166_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound167_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound168_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound16_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound170_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound171_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound172_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound174_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound175_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound176_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound177_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound178_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound179_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound17_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound180_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound181_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound182_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound183_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound184_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound185_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound186_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound187_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound188_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound189_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound18_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound190_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound191_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound192_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound193_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound194_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound195_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound196_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound197_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound198_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound199_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound19_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound1_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound200_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound202_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound203_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound204_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound205_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound206_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound207_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound208_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound209_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound20_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound210_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound211_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound212_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound213_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound214_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound215_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound216_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound217_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound218_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound219_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound21_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound220_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound221_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound222_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound223_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound224_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound225_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound226_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound227_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound228_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound229_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound22_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound230_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound231_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound232_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound233_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound234_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound235_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound236_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound237_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound238_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound239_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound23_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound240_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound241_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound242_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound243_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound244_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound245_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound246_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound247_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound248_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound249_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound24_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound250_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound251_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound252_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound253_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound254_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound26_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound27_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound28_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound29_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound2_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound30_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound31_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound32_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound34_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound35_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound36_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound37_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound38_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound39_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound3_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound40_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound41_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound42_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound43_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound44_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound45_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound46_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound47_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound49_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound4_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound50_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound51_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound52_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound53_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound54_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound55_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound56_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound58_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound59_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound5_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound60_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound61_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound62_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound63_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound64_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound65_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound66_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound67_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound69_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound6_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound70_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound72_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound73_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound74_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound75_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound76_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound77_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound78_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound79_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound7_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound80_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound81_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound82_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound83_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound84_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound85_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound86_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound87_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound88_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound89_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound8_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound90_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound91_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound92_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound93_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound94_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound95_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound96_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound97_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound98_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound99_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound9_e`, `OAI.MUB6.Certificate.PairTargetSemantics.expandedIdentity1_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm11_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm12_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm13_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm14_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm16_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm17_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm18_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm19_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm21_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm22_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm23_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm24_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm25_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm26_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm6_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm7_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm8_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm9_e` and `OAI.MUB6.pair_cross_certificate_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

def node5 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

def node6 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![4, -4]]

def node7 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![2, -2], ![3, -3]]

def node8 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]

def node9 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![2, -2]]

def node34 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![1, -2, 1], ![1, 4, -5]]

def node35 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![1, 1, -2], ![1, 1, -2]]

def node36 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]

def node37 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![2, -2, 0]]

def node38 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 4, -4], ![2, -3, 1]]

def node39 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -3, 2], ![1, 4, -5]]

def node40 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -2, 1], ![1, 3, -4]]

def node41 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]

def node42 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -4, 3], ![1, 3, -4]]

def node43 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -3, 2], ![1, 2, -3]]

def node44 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]

def node45 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![2, -2]]

def node46 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def node47 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 1, -1], ![1, 3, -4]]

def node48 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 2, -2], ![1, 2, -3]]

def node49 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 3, -3], ![1, 1, -2]]

def node50 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 4, -4], ![1, 0, -1]]

def node51 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![1, 2, -3]]

def node52 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![1, 1, -2]]

def node53 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 3, -3], ![1, 0, -1]]

def node54 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 4, -4], ![1, -1, 0]]

def node55 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 5, -5], ![1, -2, 1]]

def node56 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![1, 1, -2]]

def node57 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![1, 0, -1]]

def node58 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 3, -3], ![1, -1, 0]]

def node59 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 4, -4], ![1, -2, 1]]

def node60 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 5, -5], ![1, -3, 2]]

def node61 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![1, 0, -1]]

def node62 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -1, 0]]

def node63 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -2, 1]]

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

def node64 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![1, -1, 0]]

def node65 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def node66 : Matrix (Fin 5) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]

def node67 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![3, -3]]

def node68 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]

def node69 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]

def node70 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]

def node71 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]

def node72 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]

def node73 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]

def node74 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

def node75 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]

def node76 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]

def node77 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]

def node78 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]

def node79 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]

def node80 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]

def node81 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]

def node82 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]

def node83 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]

def node84 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]

def node85 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

def node86 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]

def node87 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]

def node88 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]

def node89 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]

def node90 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]

def node91 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![3, -1, -2]]

def node92 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![3, -2, -1]]

def node93 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]

def node94 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]

def node95 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]

def node96 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]

def node97 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]

def node98 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]

def node99 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 4, -4], ![1, -2, 1], ![2, -2, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node640 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![1, 2, -3]]

def node641 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def node642 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def node644 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 3, -4]]

def node645 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def node646 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def node647 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def node648 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def node649 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 4, -4], ![1, -2, 1], ![1, 0, -1]]

def node650 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

def node651 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![2, -1, -1]]

def node652 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 4, -5]]

def node653 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def node654 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]

def node655 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def node656 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def node657 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -3, 2], ![1, 3, -4]]

def node658 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

def node659 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def node660 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def node661 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def node662 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def node663 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def node664 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 4, -4], ![1, -3, 2], ![1, 0, -1]]

def node665 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 4, -4], ![1, -2, 1], ![1, -1, 0]]

def node666 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2]]

def node667 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

def node668 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]

def node669 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1]]

def node670 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]

def node671 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 3, -3], ![1, -3, 2], ![1, -1, 0]]

def node672 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 3, -3], ![1, -2, 1], ![1, -2, 1]]

def node673 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def node674 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 3, -2], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def node675 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 3, -3], ![1, -2, 0, 1], ![1, 1, -1, -1]]

def node676 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, -1, 2, -2]]

def node677 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, -1, 1, -1]]

def node678 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![2, -1, 1, -2]]

def node679 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![1, -1, -2, 2], ![1, 1, 1, -3]]

def node680 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def node681 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, -2, 2, -2]]

def node682 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![1, -2, 2, -1], ![1, 1, 1, -3]]

def node683 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, -2, 1, -1]]

def node684 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, -2, 1], ![1, -2, 2, -1], ![1, 0, 1, -2]]

def node685 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def node686 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 0, -2, 1]]

def node687 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, -1, 1]]

def node688 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -2, 3], ![0, 1, 3, -4], ![2, -1, -1, 0]]

def node689 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, -3, 2], ![2, -1, 0, -1]]

def node690 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![1, -1, -2, 2], ![1, 1, -1, -1]]

def node691 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -3, 3], ![0, 1, 3, -4], ![2, -2, 0, 0]]

def node692 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -3, 3], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def node693 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, 3, -4], ![1, -1, -2, 2], ![1, -1, -1, 1]]

def node694 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]

def node695 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 3, -4]]

def node696 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def node697 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def node698 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def node699 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def node700 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def node701 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def node702 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node704 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def node705 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def node706 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def node707 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 3, -4]]

def node708 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]

def node709 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]

def node710 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def node711 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def node712 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![1, -1, 1, -1], ![1, 1, 1, -3]]

def node713 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -2, 3], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def node714 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -1, 2], ![1, -1, -2, 2], ![1, 1, 0, -2]]

set_option maxHeartbeats 1000000 in
def node715 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]

set_option maxHeartbeats 1000000 in
def node716 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]

def node717 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]

def node718 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, -1, 2], ![1, -1, 2, -2], ![1, 0, 1, -2]]

def node719 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![2, -2, 1, -1]]

set_option maxHeartbeats 1000000 in
def node720 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, 3, -3], ![1, -1, -1, 1], ![1, -1, -1, 1]]

set_option maxHeartbeats 1000000 in
def node721 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -4, 5], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def node722 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -4, 5], ![-1, 3, -2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def node723 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]

def node724 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

def node725 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -3, 1, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 2, -1, -2]]

def node726 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -3, 1, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, 1, -1, -1]]

def node727 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -3, 1, 3], ![0, 0, 2, -2], ![0, 3, -1, -2], ![1, 0, -2, 1]]

def node728 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -3, 2, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 2, -1, -2]]

def node729 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -3, 2, 2], ![0, 0, -2, 2], ![0, 3, -1, -2], ![1, 0, 1, -2]]

def node730 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -3, 2, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def node731 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -3, 2, 2], ![0, 1, -2, 1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def node732 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

def node733 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

def node734 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def node735 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 2, -3]]

def node736 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def node737 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def node738 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def node739 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def node740 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def node741 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def node742 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def node743 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def node744 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def node745 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 4, -3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

def node746 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 2, -3]]

def node747 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, -1, 1], ![0, 1, -1], ![0, 3, -3], ![1, 0, -1]]

def node748 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def node749 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def node750 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, 0, -2]]

def node751 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def node752 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def node753 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def node754 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def node755 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def node756 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 2, -2, -1]]

def node757 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 1, 1, -3]]

def node758 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, 1, -2, 0]]

def node759 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, -1, 2, -1], ![0, 3, -2, -1], ![1, 0, 1, -2]]

def node760 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 2, 0, -3]]

def node761 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 1, 1, -3]]

def node762 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 1, 0, -2]]

def node763 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, 2, -3]]

def node764 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, 1, -2]]

def node765 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, 2, -2, -1]]

def node766 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def node767 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, 2, -3], ![1, 1, -2, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node768 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 2, -3]]

def node769 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def node770 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 1, 1, -3]]

def node771 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

def node772 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def node773 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def node774 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def node775 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def node776 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def node777 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 3, -2, -1], ![1, -1, 1, -1]]

def node778 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def node779 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, 1, -1, -1]]

def node780 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def node781 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def node782 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 3, -3], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def node783 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 3, -3], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def node784 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 2, -3]]

def node785 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, 0, 1, -2]]

def node786 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def node787 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def node788 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, 1, -2], ![0, 1, 2, -3], ![1, 0, -2, 1]]

def node789 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 2, 0, -3]]

def node790 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 1, 1, -3]]

def node791 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, 1, 0, -2]]

def node792 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, 1, -1, -1]]

def node793 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 2, -3]]

def node794 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, 0, 1, -2]]

def node795 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, 0, 0, -1]]

def node796 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 2, -1, -2]]

def node797 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 1, -1, -1]]

def node798 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, 1, -2, 0]]

def node799 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 2, -3]]

def node800 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 1, 1, -3]]

def node801 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def node802 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def node803 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def node804 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def node805 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, -1, -1]]

def node806 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def node807 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def node808 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def node809 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 1, -1, -1]]

def node810 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, 1, -2, 0]]

def node811 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, 0, -1, 0]]

def node812 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 3, -3], ![0, 2, -1, -1], ![1, 0, -2, 1]]

def node813 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 4, -4], ![0, 1, -2, 1], ![1, 1, -2, 0]]

def node814 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 4, -4], ![0, 2, -2, 0], ![1, 0, -2, 1]]

def node815 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def node816 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def node817 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def node818 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -2, 1]]

def node819 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, -2, 1]]

def node820 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, 0, -2, 1]]

def node821 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 1, -2, 0]]

def node822 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 2, -1, -2]]

def node823 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, -1, 2, -1], ![0, 2, -3, 1], ![1, 1, 0, -2]]

def node824 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, -1, 2, -1], ![0, 3, -1, -2], ![1, 0, -2, 1]]

def node825 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 2, -1, -2]]

def node826 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, 1, 2, -4]]

def node827 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 1, 1, -3]]

def node828 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 1, 0, -2]]

def node829 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, 1, -1, -1]]

def node830 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, 1, -2, 0]]

def node831 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node832 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def node833 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def node834 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, 1, 2, -4]]

def node835 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def node836 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 1, -2, 0]]

def node837 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def node838 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def node839 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, 0, 1, -2]]

def node840 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def node841 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 2, -2], ![0, 1, -3, 2], ![1, 1, 0, -2]]

def node842 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 1, -1, -1]]

def node843 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 2, -2], ![0, 2, -3, 1], ![1, 0, 0, -1]]

def node844 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, -2, 1]]

def node845 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def node846 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def node847 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def node848 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, 0, -2, 1]]

def node849 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -2, 1], ![0, 2, 2, -4], ![1, -1, -1, 1]]

def node850 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -2, 1]]

def node851 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, 1, -2], ![0, 2, -3, 1], ![1, -1, 1, -1]]

def node852 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, 2, -3], ![0, 2, -2, 0], ![1, -1, -1, 1]]

def node853 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 1, 0, -2]]

def node854 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def node855 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

def node856 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

def node857 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 2, -3]]

def node858 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def node859 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![1, 1, -2]]

def node860 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def node861 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 4, -4], ![1, -1, 0], ![1, 0, -1]]

def node862 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def node863 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def node864 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def node865 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

def node866 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]

def node867 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

def node868 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def node869 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def node870 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]

def node871 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def node872 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def node873 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

def node874 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]

def node875 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]

def node876 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

def node877 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 4, -3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]

def node878 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 2, -3]]

def node879 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -2, 2], ![0, 1, -1], ![0, 3, -3], ![1, 0, -1]]

def node880 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, -1, 1], ![0, 4, -4], ![1, 0, -1]]

def node881 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]

def node882 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

def node883 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0]]

def node884 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def node885 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1]]

def node886 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -3, 5], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 1, 0, -2]]

def node887 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -3, 5], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def node888 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -3, 5], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def node889 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -3, 5], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def node890 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -3, 5], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def node891 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 1, 1, -1], ![1, -1, 2, -2], ![1, 1, -1, -1]]

def node892 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, 2, -3]]

def node893 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 1, 1, -3]]

def node894 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def node895 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node896 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def node897 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def node898 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

def node899 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def node900 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 3, -2], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def node901 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 3, -2], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def node902 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def node903 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 3, -2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def node904 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, 1, -3]]

def node905 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, -1, 1], ![0, 0, 3, -3], ![1, 1, 0, -2]]

def node906 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 1, 0, -2]]

def node907 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, 1, -1, -1]]

def node908 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 3, -3], ![1, 1, -2, 0]]

def node909 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def node910 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def node911 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 2, -2]]

def node912 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 0, 2, -2], ![1, 1, -2, 0]]

def node913 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 2, -3]]

def node914 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def node915 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def node916 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 2, -2]]

def node917 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def node918 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, 1, -2]]

def node919 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def node920 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 3, -3], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def node921 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 2, -2]]

def node922 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 1, -1]]

def node923 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 1, 1, -2], ![0, 1, 2, -3], ![1, -1, -1, 1]]

def node924 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, -1, 1, 1], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def node925 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, -1, 1], ![1, -1, 3, -3], ![1, 1, -1, -1]]

def node926 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 1, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def node927 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -2, 1, 1], ![0, 2, 2, -4], ![1, 1, -2, 0]]

def node928 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -2, 2, 0], ![0, 2, 1, -3], ![1, 1, -2, 0]]

def node929 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -2, 2, 0], ![0, 3, 1, -4], ![1, 0, -2, 1]]

def node930 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 1, 1, -3]]

def node931 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, 1, 0, -2]]

def node932 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, -1, 2], ![0, 2, -1, -1], ![1, 0, 3, -4]]

def node933 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 0, 1], ![0, 1, 2, -3], ![1, 1, -1, -1]]

def node934 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 0, 1], ![0, 1, 3, -4], ![1, 1, -2, 0]]

def node935 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 0, 1], ![0, 2, -2, 0], ![1, 0, 3, -4]]

def node936 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def node937 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 2, -3], ![1, 1, -2, 0]]

def node938 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 2, -2, 0], ![1, 0, 2, -3]]

def node939 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def node940 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def node941 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 1, 1, -3]]

def node942 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def node943 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def node944 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def node945 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def node946 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def node947 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def node948 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def node949 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, 1, -1, -1]]

def node950 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def node951 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def node952 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def node953 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def node954 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 4, -3], ![0, 2, -1, -1], ![1, 0, -2, 1]]

def node955 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 1, 1, -3]]

def node956 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, 1, 0, -2]]

def node957 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -2, 2], ![0, 0, 4, -4], ![1, 1, -1, -1]]

def node958 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 0, 2, -3]]

def node959 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, 0, -2]]

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

def node960 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 3, -3], ![1, 1, -1, -1]]

def node961 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 4, -4], ![1, 1, -2, 0]]

def node962 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 3, -4]]

def node963 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def node964 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def node965 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 3, -3]]

def node966 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 1, -1, -1]]

def node967 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, 1, -2, 0]]

def node968 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 2, -3]]

def node969 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def node970 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def node971 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 2, -2]]

def node972 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def node973 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 1, -2]]

def node974 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def node975 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 1, -1]]

def node976 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def node977 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def node978 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def node979 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def node980 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def node981 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 4, -4], ![0, 1, -2, 1], ![1, 0, -1, 0]]

def node982 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 3, -3]]

def node983 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 2, -2]]

def node984 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 1, -1]]

def node985 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def node986 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def node987 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -1, -1, 1]]

def node988 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -2, 1, 1], ![0, 2, 2, -4], ![1, 1, -3, 1]]

def node989 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -2, 3, -1], ![0, 2, -3, 1], ![1, 1, 0, -2]]

def node990 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -2, 3, -1], ![0, 3, -1, -2], ![1, 0, -2, 1]]

def node991 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -2, 3], ![0, 1, 2, -3], ![1, 1, 0, -2]]

def node992 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -2, 3], ![0, 1, 3, -4], ![1, 1, -1, -1]]

def node993 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -2, 3], ![0, 2, 1, -3], ![1, 0, 1, -2]]

def node994 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -2, 3], ![0, 2, 2, -4], ![1, 0, 0, -1]]

def node995 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, 1, -1, -1]]

def node996 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, 1, -2, 0]]

def node997 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 2, -2, 0], ![1, 0, 3, -4]]

def node998 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def node999 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 2, 3, -5], ![1, 0, -2, 1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node338 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

def node339 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]

def node340 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]

def node341 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]

def node342 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]

def node343 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

def node344 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]

def node345 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

def node346 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]

def node347 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]

def node348 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 2, -3]]

def node349 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]

def node350 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]

def node351 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]

def node352 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]

def node353 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]

def node354 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]

def node355 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

def node356 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]

def node357 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

def node358 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

def node359 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]

def node360 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

def node361 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]

def node362 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]

def node363 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]

def node364 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]

def node365 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]

def node366 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]

def node367 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]

def node368 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]

def node369 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

def node370 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 3, -4]]

def node371 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]

def node372 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

def node373 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]

def node374 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]

def node375 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]

def node376 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]

def node377 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

def node378 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]

def node379 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]

def node380 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]

def node381 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![3, -3]]

def node382 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]

def node383 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node3366 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def node3367 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def node3368 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 0, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def node3369 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 0, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -2, 1]]

def node3370 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def node3371 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def node3372 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def node3373 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def node3374 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def node3375 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def node3376 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def node3377 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def node3378 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def node3379 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def node3380 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def node3381 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def node3382 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, 0, 0], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def node3383 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, 0, 0], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def node3384 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def node3385 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def node3386 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 3, -3], ![1, 0, -2, 1]]

def node3387 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 3, -4]]

def node3388 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def node3389 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def node3390 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def node3391 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node3392 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def node3393 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def node3394 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def node3395 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def node3396 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, -1, 0, 0]]

def node3397 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def node3398 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, -1, 1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def node3399 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def node3400 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def node3401 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def node3402 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def node3403 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def node3404 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def node3405 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def node3406 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, 0, 0]]

def node3407 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def node3408 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![-1, 0, -3, 4], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def node3409 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![-1, 0, -2, 3], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def node3410 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 0, 1, 0], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def node3411 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 1, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def node3412 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def node3413 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def node3414 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def node3415 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def node3416 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def node3417 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def node3418 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, 3, -3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def node3419 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def node3420 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def node3421 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def node3422 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def node3423 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def node3424 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def node3425 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def node3426 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def node3427 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def node3428 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def node3429 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def node3430 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def node3431 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, 0, 0, -1]]

def node3432 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def node3433 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def node3434 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def node3435 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def node3436 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def node3437 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def node3438 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 0, 1, -1], ![0, 1, -3, 2], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def node3439 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def node3440 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def node3441 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def node3442 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def node3443 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def node3444 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def node3445 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def node3446 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def node3447 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 3, -2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def node3448 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def node3449 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def node3450 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def node3451 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 0, 1]]

def node3452 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -3, 2], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def node3453 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

def node3454 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def node3455 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, -1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node3456 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def node3457 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -2, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0]]

def node3458 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def node3459 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -2, 0, 1]]

def node3460 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

def node3461 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![-1, 1, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def node3462 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def node3463 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def node3464 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def node3465 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -3, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def node3466 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -2, 3, -2]]

def node3467 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def node3468 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -2, 0, 1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node384 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def node385 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def node386 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def node387 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def node388 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def node389 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def node390 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def node391 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def node392 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def node393 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, 1, -2], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def node394 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, 1, 0, -3]]

def node395 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![2, 0, 0, -2]]

def node396 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def node397 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def node398 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def node399 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 3, -3], ![0, 2, -2, 0], ![2, 0, -1, -1]]

def node400 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, 0, 1, -3]]

def node401 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![0, 1, 2, -3], ![2, 0, 0, -2]]

def node402 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![1, 0, 1, -2], ![1, 1, 1, -3]]

def node403 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![1, 0, 2, -3], ![1, 1, 0, -2]]

def node404 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 1, -2], ![1, 0, 1, -2], ![1, 1, -2, 0]]

def node405 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, 1, 0, -3]]

def node406 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, 0, 1, -3]]

def node407 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, 1, -1, -2]]

def node408 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def node409 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -2, 1], ![1, 0, 1, -2], ![1, 1, 0, -2]]

def node410 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, 1, -1, -2]]

def node411 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 2, -1, -1], ![2, 0, 1, -3]]

def node412 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, 0, 0, -2]]

def node413 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![1, 1, 0, -2], ![1, 1, 0, -2]]

def node414 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]

def node415 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]

def node416 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]

def node417 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

def node418 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]

def node419 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]

set_option maxHeartbeats 1000000 in
def node420 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

def node421 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

def node422 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def node423 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]

set_option maxHeartbeats 1000000 in
def node424 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

set_option maxHeartbeats 1000000 in
def node425 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

def node426 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

def node427 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

def node428 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def node429 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]

def node430 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

def node431 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 3, -4]]

def node432 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

set_option maxHeartbeats 1000000 in
def node433 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

def node434 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

set_option maxHeartbeats 1000000 in
def node435 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def node436 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0], ![1, 0, -1]]

def node437 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def node438 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def node439 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

def node440 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def node441 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def node442 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def node443 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def node444 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def node445 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def node446 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

def node447 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![2, 1, -2, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node448 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, -2, 0], ![2, 0, 1, -3]]

def node449 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def node450 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def node451 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, 1, -3], ![2, 0, -2, 0]]

def node452 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 0, 1, -2], ![1, 2, -2, -1]]

def node453 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 1, -2, 0], ![1, 1, 1, -3]]

def node454 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def node455 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 3, -2], ![0, 2, -2, 0], ![2, 0, 0, -2]]

def node456 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 3, -2], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def node457 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 3, -2], ![0, 2, 0, -2], ![2, 0, -2, 0]]

def node458 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 3, -2], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def node459 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![2, -1, 1, -2]]

def node460 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 2, 0, -3]]

def node461 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 3, -3], ![0, 2, -2, 0], ![2, -1, 0, -1]]

def node462 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 3, -3], ![0, 2, -1, -1], ![2, -1, -1, 0]]

def node463 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 1, 1, -3]]

set_option maxHeartbeats 1000000 in
def node464 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def node465 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 1, -2], ![1, -1, 2, -2], ![1, 1, -2, 0]]

set_option maxHeartbeats 1000000 in
def node466 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def node467 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 1, -2, 0]]

set_option maxHeartbeats 1000000 in
def node468 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 2, -3]]

def node469 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, -2, 0], ![1, -1, 2, -2], ![1, 0, 1, -2]]

def node470 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, -1, 2], ![0, 1, 2, -3], ![2, 1, -1, -2]]

def node471 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -2, 1], ![2, 1, 0, -3]]

set_option maxHeartbeats 1000000 in
def node472 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![2, 0, 0, -2]]

def node473 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def node474 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -2, 0]]

def node475 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 0, -2, 1], ![1, 2, 0, -3]]

def node476 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def node477 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def node478 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 2, 1, -3], ![2, -1, 1, -2]]

set_option maxHeartbeats 1000000 in
def node479 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![1, -1, 2, -2], ![1, 2, 0, -3]]

def node480 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, -3, 1], ![2, -1, 1, -2]]

def node481 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, -1, -1, 0]]

def node482 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![2, -1, -2, 1]]

def node483 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 2, -1, -2]]

def node484 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, 1, -2]]

def node485 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![2, -1, 0, -1]]

def node486 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 3, -4], ![2, -1, -1, 0]]

def node487 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 1, 1, -3]]

def node488 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 2, -2], ![1, 1, 0, -2]]

def node489 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 1, -2], ![0, 1, 1, -2], ![2, -1, -2, 1]]

def node490 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def node491 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def node492 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 1, -3, 1]]

def node493 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, 1, -2, 0]]

def node494 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, -3, 1], ![1, -1, 1, -1], ![1, 0, 2, -3]]

def node495 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 2, -3]]

def node496 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, 0, -2], ![1, -1, 2, -2], ![1, 0, -2, 1]]

def node497 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 1, 1, -2], ![2, 1, -1, -2]]

def node498 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 2, -2, 0], ![2, 0, 2, -4]]

def node499 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 2, 2, -4], ![2, 0, -2, 0]]

def node500 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 0, 1, -2], ![1, 2, -1, -2]]

def node501 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 1, -2, 0], ![1, 1, 2, -4]]

def node502 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def node503 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![2, 1, -1, -2]]

def node504 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -3, 1]]

def node505 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 2, -1], ![1, 1, -3, 1], ![1, 1, 0, -2]]

def node506 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, -1, 1, -2]]

def node507 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, -1, -2, 1]]

def node508 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 2, -2, -1]]

def node509 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -3, 2], ![1, -1, 1, -1], ![1, 1, 1, -3]]

def node510 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def node511 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![2, -1, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node512 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def node513 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def node514 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def node515 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -3, 1]]

def node516 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, 1, -2, 0]]

def node517 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def node518 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, 0, -2], ![1, -1, -2, 2], ![1, 0, 1, -2]]

def node519 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, 1, -3], ![1, -1, 1, -1], ![1, 0, -3, 2]]

def node520 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def node521 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def node522 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def node523 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, -1, 0, -1]]

def node524 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]

def node525 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]

def node526 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

def node527 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]

def node528 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]

def node529 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

def node530 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]

def node531 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]

def node532 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]

def node533 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]

def node534 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]

def node535 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]

def node536 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]

def node537 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

def node538 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]

def node539 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

def node540 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 4, -3], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

def node541 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]

def node542 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

def node543 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 3, -4]]

def node544 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

def node545 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

def node546 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 2, -3]]

def node547 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def node548 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 1, -2]]

def node549 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def node550 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 4, -4], ![1, -1, 0], ![1, 0, -1]]

def node551 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![2, 0, -2]]

def node552 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 4, -5]]

def node553 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 3, -4]]

def node554 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 2, -3]]

def node555 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def node556 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def node558 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 3, -4]]

def node559 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def node560 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def node561 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def node562 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def node563 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def node564 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 4, -4], ![1, -2, 1], ![1, 0, -1]]

def node565 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

def node566 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

def node567 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]

def node568 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 2, -3]]

def node569 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def node570 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def node571 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

def node572 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

def node573 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

def node574 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

def node575 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node576 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 2, -1, -1], ![2, 0, 1, -3]]

def node577 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 2, 1, -3], ![2, 0, -1, -1]]

def node578 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def node579 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, -1, 1, -2]]

def node580 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 2, 1, -3], ![2, -1, -1, 0]]

def node581 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 3, -2], ![0, 2, -1, -1], ![2, -1, 0, -1]]

def node582 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 3, -3], ![0, 2, -1, -1], ![2, -2, 0, 0]]

def node583 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 2, -3], ![1, -2, 1, 0], ![1, 1, -1, -1]]

def node584 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -2, 1, 0], ![1, 0, 2, -3]]

def node585 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def node586 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -2, 1, 1], ![1, 1, -2, 0], ![1, 1, 2, -4]]

def node587 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -2, 2, 0], ![0, 2, -2, 0], ![2, 0, 1, -3]]

def node588 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![2, -1, 1, -2]]

def node589 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 2, -2, 0], ![2, -1, 0, -1]]

def node590 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 2, -1, -1], ![2, -1, -1, 0]]

def node591 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![2, -2, 1, -1]]

def node592 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 3, -3], ![0, 2, -2, 0], ![2, -2, 0, 0]]

def node593 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -2, 2, -2]]

def node594 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![2, -2, 1, -1]]

def node595 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 3, -4], ![2, -2, 0, 0]]

def node596 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def node597 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![1, -2, 3, -2], ![1, 1, 0, -2]]

def node598 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 1, -2, 0]]

def node599 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 2, -3], ![1, -2, 1, 0], ![1, 1, -2, 0]]

def node600 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 3, -4], ![1, -2, 0, 1], ![1, 1, -2, 0]]

def node601 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -2, 1, 0], ![1, 0, 2, -3]]

def node602 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -2, 2, -1], ![1, 0, 1, -2]]

def node603 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def node604 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, -1, 3, -3]]

def node605 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 2, -2, 0], ![2, 0, 0, -2]]

def node606 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def node607 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 2, 0, -2], ![2, 0, -2, 0]]

def node608 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def node609 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, -1, -1, 0]]

def node610 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -3, 2], ![0, 1, 1, -2], ![2, -2, 2, -2]]

def node611 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -3, 2], ![1, -2, 3, -2], ![1, 1, 0, -2]]

def node612 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 1, -3, 1]]

def node613 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def node614 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def node615 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -3, 2], ![1, -2, 0, 1], ![1, 1, 2, -4]]

def node616 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -3, 2], ![1, -2, 1, 0], ![1, 1, 1, -3]]

def node617 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -3, 2], ![1, -2, 2, -1], ![1, 1, 0, -2]]

def node618 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![1, -2, -1, 2], ![1, 1, 2, -4]]

def node619 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![1, -2, 0, 1], ![1, 1, 1, -3]]

def node620 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![1, -2, 1, 0], ![1, 1, 0, -2]]

def node621 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, -1, 1, -1]]

def node622 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

def node623 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 3, -4], ![2, -2, 0]]

def node624 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

def node625 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]

def node626 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]

def node627 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -3, 2], ![1, -1, 0], ![1, 1, -2]]

def node628 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![0, -2, 2], ![1, -1, 0], ![2, -1, -1]]

def node629 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![1, -3, 2], ![1, -1, 0], ![1, 0, -1]]

def node630 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![1, -2, 1], ![1, -2, 1], ![1, 0, -1]]

def node631 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

def node632 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![1, -1, 0], ![1, 3, -4]]

def node633 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

def node634 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

def node635 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def node636 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def node637 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 4, -4], ![1, -1, 0], ![1, 0, -1]]

def node638 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 4, -5]]

def node639 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 3, -4]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Permutations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def permutation0 : Equiv.Perm (Fin 1) where
  toFun := ![0]
  invFun := ![0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation1 : Equiv.Perm (Fin 2) where
  toFun := ![0, 1]
  invFun := ![0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation2 : Equiv.Perm (Fin 2) where
  toFun := ![1, 0]
  invFun := ![1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation3 : Equiv.Perm (Fin 3) where
  toFun := ![0, 1, 2]
  invFun := ![0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation4 : Equiv.Perm (Fin 3) where
  toFun := ![0, 2, 1]
  invFun := ![0, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation5 : Equiv.Perm (Fin 3) where
  toFun := ![1, 0, 2]
  invFun := ![1, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation6 : Equiv.Perm (Fin 3) where
  toFun := ![1, 2, 0]
  invFun := ![2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation7 : Equiv.Perm (Fin 3) where
  toFun := ![2, 0, 1]
  invFun := ![1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation8 : Equiv.Perm (Fin 3) where
  toFun := ![2, 1, 0]
  invFun := ![2, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation9 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation10 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 3, 2]
  invFun := ![0, 1, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation11 : Equiv.Perm (Fin 4) where
  toFun := ![0, 2, 1, 3]
  invFun := ![0, 2, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation12 : Equiv.Perm (Fin 4) where
  toFun := ![0, 2, 3, 1]
  invFun := ![0, 3, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation13 : Equiv.Perm (Fin 4) where
  toFun := ![0, 3, 1, 2]
  invFun := ![0, 2, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation14 : Equiv.Perm (Fin 4) where
  toFun := ![0, 3, 2, 1]
  invFun := ![0, 3, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation15 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation16 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 3, 2]
  invFun := ![1, 0, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation17 : Equiv.Perm (Fin 4) where
  toFun := ![1, 2, 0, 3]
  invFun := ![2, 0, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation18 : Equiv.Perm (Fin 4) where
  toFun := ![1, 2, 3, 0]
  invFun := ![3, 0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation19 : Equiv.Perm (Fin 4) where
  toFun := ![1, 3, 0, 2]
  invFun := ![2, 0, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation20 : Equiv.Perm (Fin 4) where
  toFun := ![1, 3, 2, 0]
  invFun := ![3, 0, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation21 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation22 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 3, 1]
  invFun := ![1, 3, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation23 : Equiv.Perm (Fin 4) where
  toFun := ![2, 1, 0, 3]
  invFun := ![2, 1, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation24 : Equiv.Perm (Fin 4) where
  toFun := ![2, 1, 3, 0]
  invFun := ![3, 1, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation25 : Equiv.Perm (Fin 4) where
  toFun := ![2, 3, 0, 1]
  invFun := ![2, 3, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation26 : Equiv.Perm (Fin 4) where
  toFun := ![2, 3, 1, 0]
  invFun := ![3, 2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation27 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation28 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 2, 1]
  invFun := ![1, 3, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation29 : Equiv.Perm (Fin 4) where
  toFun := ![3, 1, 0, 2]
  invFun := ![2, 1, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation30 : Equiv.Perm (Fin 4) where
  toFun := ![3, 1, 2, 0]
  invFun := ![3, 1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation31 : Equiv.Perm (Fin 4) where
  toFun := ![3, 2, 0, 1]
  invFun := ![2, 3, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation32 : Equiv.Perm (Fin 4) where
  toFun := ![3, 2, 1, 0]
  invFun := ![3, 2, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation33 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation34 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 4, 3]
  invFun := ![0, 1, 2, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation35 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 3, 2, 4]
  invFun := ![0, 1, 3, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation36 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 3, 4, 2]
  invFun := ![0, 1, 4, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation37 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 4, 2, 3]
  invFun := ![0, 1, 3, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation38 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 4, 3, 2]
  invFun := ![0, 1, 4, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation39 : Equiv.Perm (Fin 5) where
  toFun := ![0, 2, 1, 3, 4]
  invFun := ![0, 2, 1, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation40 : Equiv.Perm (Fin 5) where
  toFun := ![0, 2, 1, 4, 3]
  invFun := ![0, 2, 1, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation41 : Equiv.Perm (Fin 5) where
  toFun := ![0, 2, 3, 1, 4]
  invFun := ![0, 3, 1, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation42 : Equiv.Perm (Fin 5) where
  toFun := ![0, 2, 3, 4, 1]
  invFun := ![0, 4, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation43 : Equiv.Perm (Fin 5) where
  toFun := ![0, 2, 4, 1, 3]
  invFun := ![0, 3, 1, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation44 : Equiv.Perm (Fin 5) where
  toFun := ![0, 2, 4, 3, 1]
  invFun := ![0, 4, 1, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation45 : Equiv.Perm (Fin 5) where
  toFun := ![0, 3, 1, 2, 4]
  invFun := ![0, 2, 3, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation46 : Equiv.Perm (Fin 5) where
  toFun := ![0, 3, 1, 4, 2]
  invFun := ![0, 2, 4, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation47 : Equiv.Perm (Fin 5) where
  toFun := ![0, 3, 2, 1, 4]
  invFun := ![0, 3, 2, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation48 : Equiv.Perm (Fin 5) where
  toFun := ![0, 3, 2, 4, 1]
  invFun := ![0, 4, 2, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation49 : Equiv.Perm (Fin 5) where
  toFun := ![0, 3, 4, 1, 2]
  invFun := ![0, 3, 4, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation50 : Equiv.Perm (Fin 5) where
  toFun := ![0, 3, 4, 2, 1]
  invFun := ![0, 4, 3, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation51 : Equiv.Perm (Fin 5) where
  toFun := ![0, 4, 1, 2, 3]
  invFun := ![0, 2, 3, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation52 : Equiv.Perm (Fin 5) where
  toFun := ![0, 4, 1, 3, 2]
  invFun := ![0, 2, 4, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation53 : Equiv.Perm (Fin 5) where
  toFun := ![0, 4, 2, 1, 3]
  invFun := ![0, 3, 2, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation54 : Equiv.Perm (Fin 5) where
  toFun := ![0, 4, 2, 3, 1]
  invFun := ![0, 4, 2, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation55 : Equiv.Perm (Fin 5) where
  toFun := ![0, 4, 3, 1, 2]
  invFun := ![0, 3, 4, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation56 : Equiv.Perm (Fin 5) where
  toFun := ![0, 4, 3, 2, 1]
  invFun := ![0, 4, 3, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation57 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation58 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 4, 3]
  invFun := ![1, 0, 2, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation59 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 3, 2, 4]
  invFun := ![1, 0, 3, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation60 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 3, 4, 2]
  invFun := ![1, 0, 4, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation61 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 4, 2, 3]
  invFun := ![1, 0, 3, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation62 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 4, 3, 2]
  invFun := ![1, 0, 4, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation63 : Equiv.Perm (Fin 5) where
  toFun := ![1, 2, 0, 3, 4]
  invFun := ![2, 0, 1, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation64 : Equiv.Perm (Fin 5) where
  toFun := ![1, 2, 3, 0, 4]
  invFun := ![3, 0, 1, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation65 : Equiv.Perm (Fin 5) where
  toFun := ![1, 2, 3, 4, 0]
  invFun := ![4, 0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation66 : Equiv.Perm (Fin 5) where
  toFun := ![1, 2, 4, 0, 3]
  invFun := ![3, 0, 1, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation67 : Equiv.Perm (Fin 5) where
  toFun := ![1, 2, 4, 3, 0]
  invFun := ![4, 0, 1, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation68 : Equiv.Perm (Fin 5) where
  toFun := ![1, 3, 0, 2, 4]
  invFun := ![2, 0, 3, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation69 : Equiv.Perm (Fin 5) where
  toFun := ![1, 3, 0, 4, 2]
  invFun := ![2, 0, 4, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation70 : Equiv.Perm (Fin 5) where
  toFun := ![1, 3, 2, 0, 4]
  invFun := ![3, 0, 2, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation71 : Equiv.Perm (Fin 5) where
  toFun := ![1, 3, 2, 4, 0]
  invFun := ![4, 0, 2, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation72 : Equiv.Perm (Fin 5) where
  toFun := ![1, 3, 4, 0, 2]
  invFun := ![3, 0, 4, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation73 : Equiv.Perm (Fin 5) where
  toFun := ![1, 3, 4, 2, 0]
  invFun := ![4, 0, 3, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation74 : Equiv.Perm (Fin 5) where
  toFun := ![1, 4, 0, 2, 3]
  invFun := ![2, 0, 3, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation75 : Equiv.Perm (Fin 5) where
  toFun := ![1, 4, 0, 3, 2]
  invFun := ![2, 0, 4, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation76 : Equiv.Perm (Fin 5) where
  toFun := ![1, 4, 2, 0, 3]
  invFun := ![3, 0, 2, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation77 : Equiv.Perm (Fin 5) where
  toFun := ![1, 4, 2, 3, 0]
  invFun := ![4, 0, 2, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation78 : Equiv.Perm (Fin 5) where
  toFun := ![1, 4, 3, 0, 2]
  invFun := ![3, 0, 4, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation79 : Equiv.Perm (Fin 5) where
  toFun := ![1, 4, 3, 2, 0]
  invFun := ![4, 0, 3, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation80 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation81 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 4, 3]
  invFun := ![1, 2, 0, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation82 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 3, 1, 4]
  invFun := ![1, 3, 0, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation83 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 3, 4, 1]
  invFun := ![1, 4, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation84 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 4, 1, 3]
  invFun := ![1, 3, 0, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation85 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 4, 3, 1]
  invFun := ![1, 4, 0, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation86 : Equiv.Perm (Fin 5) where
  toFun := ![2, 1, 0, 3, 4]
  invFun := ![2, 1, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation87 : Equiv.Perm (Fin 5) where
  toFun := ![2, 1, 0, 4, 3]
  invFun := ![2, 1, 0, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation88 : Equiv.Perm (Fin 5) where
  toFun := ![2, 1, 3, 0, 4]
  invFun := ![3, 1, 0, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation89 : Equiv.Perm (Fin 5) where
  toFun := ![2, 1, 3, 4, 0]
  invFun := ![4, 1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation90 : Equiv.Perm (Fin 5) where
  toFun := ![2, 1, 4, 0, 3]
  invFun := ![3, 1, 0, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation91 : Equiv.Perm (Fin 5) where
  toFun := ![2, 1, 4, 3, 0]
  invFun := ![4, 1, 0, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation92 : Equiv.Perm (Fin 5) where
  toFun := ![2, 3, 0, 1, 4]
  invFun := ![2, 3, 0, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation93 : Equiv.Perm (Fin 5) where
  toFun := ![2, 3, 0, 4, 1]
  invFun := ![2, 4, 0, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation94 : Equiv.Perm (Fin 5) where
  toFun := ![2, 3, 1, 0, 4]
  invFun := ![3, 2, 0, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation95 : Equiv.Perm (Fin 5) where
  toFun := ![2, 3, 1, 4, 0]
  invFun := ![4, 2, 0, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation96 : Equiv.Perm (Fin 5) where
  toFun := ![2, 3, 4, 0, 1]
  invFun := ![3, 4, 0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation97 : Equiv.Perm (Fin 5) where
  toFun := ![2, 3, 4, 1, 0]
  invFun := ![4, 3, 0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation98 : Equiv.Perm (Fin 5) where
  toFun := ![2, 4, 0, 1, 3]
  invFun := ![2, 3, 0, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation99 : Equiv.Perm (Fin 5) where
  toFun := ![2, 4, 0, 3, 1]
  invFun := ![2, 4, 0, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation100 : Equiv.Perm (Fin 5) where
  toFun := ![2, 4, 1, 0, 3]
  invFun := ![3, 2, 0, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation101 : Equiv.Perm (Fin 5) where
  toFun := ![2, 4, 1, 3, 0]
  invFun := ![4, 2, 0, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation102 : Equiv.Perm (Fin 5) where
  toFun := ![2, 4, 3, 0, 1]
  invFun := ![3, 4, 0, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation103 : Equiv.Perm (Fin 5) where
  toFun := ![2, 4, 3, 1, 0]
  invFun := ![4, 3, 0, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation104 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation105 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 4, 2]
  invFun := ![1, 2, 4, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation106 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 2, 1, 4]
  invFun := ![1, 3, 2, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation107 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 2, 4, 1]
  invFun := ![1, 4, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation108 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 4, 1, 2]
  invFun := ![1, 3, 4, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation109 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 4, 2, 1]
  invFun := ![1, 4, 3, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation110 : Equiv.Perm (Fin 5) where
  toFun := ![3, 1, 0, 2, 4]
  invFun := ![2, 1, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation111 : Equiv.Perm (Fin 5) where
  toFun := ![3, 1, 0, 4, 2]
  invFun := ![2, 1, 4, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation112 : Equiv.Perm (Fin 5) where
  toFun := ![3, 1, 2, 0, 4]
  invFun := ![3, 1, 2, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation113 : Equiv.Perm (Fin 5) where
  toFun := ![3, 1, 2, 4, 0]
  invFun := ![4, 1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation114 : Equiv.Perm (Fin 5) where
  toFun := ![3, 1, 4, 0, 2]
  invFun := ![3, 1, 4, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation115 : Equiv.Perm (Fin 5) where
  toFun := ![3, 1, 4, 2, 0]
  invFun := ![4, 1, 3, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation116 : Equiv.Perm (Fin 5) where
  toFun := ![3, 2, 0, 1, 4]
  invFun := ![2, 3, 1, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation117 : Equiv.Perm (Fin 5) where
  toFun := ![3, 2, 0, 4, 1]
  invFun := ![2, 4, 1, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation118 : Equiv.Perm (Fin 5) where
  toFun := ![3, 2, 1, 0, 4]
  invFun := ![3, 2, 1, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation119 : Equiv.Perm (Fin 5) where
  toFun := ![3, 2, 1, 4, 0]
  invFun := ![4, 2, 1, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation120 : Equiv.Perm (Fin 5) where
  toFun := ![3, 2, 4, 0, 1]
  invFun := ![3, 4, 1, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation121 : Equiv.Perm (Fin 5) where
  toFun := ![3, 2, 4, 1, 0]
  invFun := ![4, 3, 1, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation122 : Equiv.Perm (Fin 5) where
  toFun := ![3, 4, 0, 1, 2]
  invFun := ![2, 3, 4, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation123 : Equiv.Perm (Fin 5) where
  toFun := ![3, 4, 0, 2, 1]
  invFun := ![2, 4, 3, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation124 : Equiv.Perm (Fin 5) where
  toFun := ![3, 4, 1, 0, 2]
  invFun := ![3, 2, 4, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation125 : Equiv.Perm (Fin 5) where
  toFun := ![3, 4, 1, 2, 0]
  invFun := ![4, 2, 3, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation126 : Equiv.Perm (Fin 5) where
  toFun := ![3, 4, 2, 0, 1]
  invFun := ![3, 4, 2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation127 : Equiv.Perm (Fin 5) where
  toFun := ![3, 4, 2, 1, 0]
  invFun := ![4, 3, 2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation128 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation129 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 3, 2]
  invFun := ![1, 2, 4, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation130 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 2, 1, 3]
  invFun := ![1, 3, 2, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation131 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 2, 3, 1]
  invFun := ![1, 4, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation132 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 3, 1, 2]
  invFun := ![1, 3, 4, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation133 : Equiv.Perm (Fin 5) where
  toFun := ![4, 1, 0, 2, 3]
  invFun := ![2, 1, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation134 : Equiv.Perm (Fin 5) where
  toFun := ![4, 1, 0, 3, 2]
  invFun := ![2, 1, 4, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation135 : Equiv.Perm (Fin 5) where
  toFun := ![4, 1, 2, 0, 3]
  invFun := ![3, 1, 2, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation136 : Equiv.Perm (Fin 5) where
  toFun := ![4, 1, 2, 3, 0]
  invFun := ![4, 1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation137 : Equiv.Perm (Fin 5) where
  toFun := ![4, 1, 3, 0, 2]
  invFun := ![3, 1, 4, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation138 : Equiv.Perm (Fin 5) where
  toFun := ![4, 1, 3, 2, 0]
  invFun := ![4, 1, 3, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation139 : Equiv.Perm (Fin 5) where
  toFun := ![4, 2, 0, 1, 3]
  invFun := ![2, 3, 1, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation140 : Equiv.Perm (Fin 5) where
  toFun := ![4, 2, 0, 3, 1]
  invFun := ![2, 4, 1, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation141 : Equiv.Perm (Fin 5) where
  toFun := ![4, 2, 1, 0, 3]
  invFun := ![3, 2, 1, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation142 : Equiv.Perm (Fin 5) where
  toFun := ![4, 2, 1, 3, 0]
  invFun := ![4, 2, 1, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation143 : Equiv.Perm (Fin 5) where
  toFun := ![4, 2, 3, 0, 1]
  invFun := ![3, 4, 1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation144 : Equiv.Perm (Fin 5) where
  toFun := ![4, 2, 3, 1, 0]
  invFun := ![4, 3, 1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation145 : Equiv.Perm (Fin 5) where
  toFun := ![4, 3, 0, 1, 2]
  invFun := ![2, 3, 4, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation146 : Equiv.Perm (Fin 5) where
  toFun := ![4, 3, 0, 2, 1]
  invFun := ![2, 4, 3, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation147 : Equiv.Perm (Fin 5) where
  toFun := ![4, 3, 1, 0, 2]
  invFun := ![3, 2, 4, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation148 : Equiv.Perm (Fin 5) where
  toFun := ![4, 3, 1, 2, 0]
  invFun := ![4, 2, 3, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation149 : Equiv.Perm (Fin 5) where
  toFun := ![4, 3, 2, 0, 1]
  invFun := ![3, 4, 2, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation150 : Equiv.Perm (Fin 5) where
  toFun := ![4, 3, 2, 1, 0]
  invFun := ![4, 3, 2, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation151 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation152 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 5, 4]
  invFun := ![0, 1, 2, 3, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation153 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 4, 3, 5]
  invFun := ![0, 1, 2, 4, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation154 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 4, 5, 3]
  invFun := ![0, 1, 2, 5, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation155 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation156 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 3, 2, 4, 5]
  invFun := ![0, 1, 3, 2, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation157 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 3, 2, 5, 4]
  invFun := ![0, 1, 3, 2, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation158 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 3, 4, 2, 5]
  invFun := ![0, 1, 4, 2, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation159 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 3, 4, 5, 2]
  invFun := ![0, 1, 5, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation160 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 3, 5, 2, 4]
  invFun := ![0, 1, 4, 2, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation161 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 3, 5, 4, 2]
  invFun := ![0, 1, 5, 2, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation162 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation163 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 3, 5, 2]
  invFun := ![0, 1, 5, 3, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation164 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 5, 2, 3]
  invFun := ![0, 1, 4, 5, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation165 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 5, 2, 3, 4]
  invFun := ![0, 1, 3, 4, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation166 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 1, 3, 4, 5]
  invFun := ![0, 2, 1, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation167 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 1, 4, 3, 5]
  invFun := ![0, 2, 1, 4, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation168 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 1, 5, 3, 4]
  invFun := ![0, 2, 1, 4, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation169 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 3, 1, 4, 5]
  invFun := ![0, 3, 1, 2, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation170 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 3, 1, 5, 4]
  invFun := ![0, 3, 1, 2, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation171 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 3, 4, 1, 5]
  invFun := ![0, 4, 1, 2, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation172 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 3, 4, 5, 1]
  invFun := ![0, 5, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation173 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 4, 1, 5, 3]
  invFun := ![0, 3, 1, 5, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation174 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 4, 5, 1, 3]
  invFun := ![0, 4, 1, 5, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation175 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 5, 1, 3, 4]
  invFun := ![0, 3, 1, 4, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation176 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 1, 2, 4, 5]
  invFun := ![0, 2, 3, 1, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation177 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 1, 2, 5, 4]
  invFun := ![0, 2, 3, 1, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation178 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 4, 1, 2, 5]
  invFun := ![0, 3, 4, 1, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation179 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 4, 2, 1, 5]
  invFun := ![0, 4, 3, 1, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation180 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 4, 5, 1, 2]
  invFun := ![0, 4, 5, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation181 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 5, 1, 2, 4]
  invFun := ![0, 3, 4, 1, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation182 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 1, 2, 5, 3]
  invFun := ![0, 2, 3, 5, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation183 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 1, 3, 2, 5]
  invFun := ![0, 2, 4, 3, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation184 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 1, 3, 5, 2]
  invFun := ![0, 2, 5, 3, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation185 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 1, 5, 2, 3]
  invFun := ![0, 2, 4, 5, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation186 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 1, 5, 3, 2]
  invFun := ![0, 2, 5, 4, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation187 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 2, 1, 5, 3]
  invFun := ![0, 3, 2, 5, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation188 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 2, 3, 1, 5]
  invFun := ![0, 4, 2, 3, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation189 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 2, 3, 5, 1]
  invFun := ![0, 5, 2, 3, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation190 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 2, 5, 1, 3]
  invFun := ![0, 4, 2, 5, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation191 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 2, 5, 3, 1]
  invFun := ![0, 5, 2, 4, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation192 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 3, 1, 2, 5]
  invFun := ![0, 3, 4, 2, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation193 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 3, 2, 5, 1]
  invFun := ![0, 5, 3, 2, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation194 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 3, 5, 1, 2]
  invFun := ![0, 4, 5, 2, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation195 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 5, 1, 2, 3]
  invFun := ![0, 3, 4, 5, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation196 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 5, 2, 3, 1]
  invFun := ![0, 5, 3, 4, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation197 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 2, 3, 4]
  invFun := ![0, 2, 3, 4, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation198 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 4, 2, 3]
  invFun := ![0, 2, 4, 5, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation199 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 2, 3, 4, 1]
  invFun := ![0, 5, 2, 3, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation200 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 3, 1, 2, 4]
  invFun := ![0, 3, 4, 2, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation201 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 4, 2, 3, 1]
  invFun := ![0, 5, 3, 4, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation202 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation203 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 5, 3, 4]
  invFun := ![1, 0, 2, 4, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation204 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 3, 4, 2, 5]
  invFun := ![1, 0, 4, 2, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation205 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 3, 4, 5, 2]
  invFun := ![1, 0, 5, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation206 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 4, 5, 2, 3]
  invFun := ![1, 0, 4, 5, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation207 : Equiv.Perm (Fin 6) where
  toFun := ![1, 2, 0, 5, 3, 4]
  invFun := ![2, 0, 1, 4, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation208 : Equiv.Perm (Fin 6) where
  toFun := ![1, 2, 3, 5, 4, 0]
  invFun := ![5, 0, 1, 2, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation209 : Equiv.Perm (Fin 6) where
  toFun := ![1, 2, 4, 5, 0, 3]
  invFun := ![4, 0, 1, 5, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation210 : Equiv.Perm (Fin 6) where
  toFun := ![1, 2, 4, 5, 3, 0]
  invFun := ![5, 0, 1, 4, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation211 : Equiv.Perm (Fin 6) where
  toFun := ![1, 2, 5, 4, 3, 0]
  invFun := ![5, 0, 1, 4, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation212 : Equiv.Perm (Fin 6) where
  toFun := ![1, 3, 0, 5, 4, 2]
  invFun := ![2, 0, 5, 1, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation213 : Equiv.Perm (Fin 6) where
  toFun := ![1, 3, 4, 5, 0, 2]
  invFun := ![4, 0, 5, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation214 : Equiv.Perm (Fin 6) where
  toFun := ![1, 4, 0, 5, 2, 3]
  invFun := ![2, 0, 4, 5, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation215 : Equiv.Perm (Fin 6) where
  toFun := ![1, 5, 0, 2, 3, 4]
  invFun := ![2, 0, 3, 4, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation216 : Equiv.Perm (Fin 6) where
  toFun := ![1, 5, 0, 2, 4, 3]
  invFun := ![2, 0, 3, 5, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation217 : Equiv.Perm (Fin 6) where
  toFun := ![1, 5, 0, 4, 2, 3]
  invFun := ![2, 0, 4, 5, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation218 : Equiv.Perm (Fin 6) where
  toFun := ![1, 5, 0, 4, 3, 2]
  invFun := ![2, 0, 5, 4, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation219 : Equiv.Perm (Fin 6) where
  toFun := ![1, 5, 2, 3, 4, 0]
  invFun := ![5, 0, 2, 3, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation220 : Equiv.Perm (Fin 6) where
  toFun := ![1, 5, 3, 2, 4, 0]
  invFun := ![5, 0, 3, 2, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation221 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation222 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 4, 3, 5]
  invFun := ![1, 2, 0, 4, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation223 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 4, 5, 3]
  invFun := ![1, 2, 0, 5, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation224 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 5, 3, 4]
  invFun := ![1, 2, 0, 4, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation225 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 3, 1, 4, 5]
  invFun := ![1, 3, 0, 2, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation227 : Equiv.Perm (Fin 6) where
  toFun := ![2, 1, 3, 4, 5, 0]
  invFun := ![5, 1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation228 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 0, 1, 4, 5]
  invFun := ![2, 3, 0, 1, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation230 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 4, 0, 5, 1]
  invFun := ![3, 5, 0, 1, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation231 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 4, 5, 0, 1]
  invFun := ![4, 5, 0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation232 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 4, 5, 1, 0]
  invFun := ![5, 4, 0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation233 : Equiv.Perm (Fin 6) where
  toFun := ![2, 4, 0, 5, 1, 3]
  invFun := ![2, 4, 0, 5, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation234 : Equiv.Perm (Fin 6) where
  toFun := ![2, 4, 3, 5, 0, 1]
  invFun := ![4, 5, 0, 2, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation235 : Equiv.Perm (Fin 6) where
  toFun := ![2, 5, 0, 1, 3, 4]
  invFun := ![2, 3, 0, 4, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation236 : Equiv.Perm (Fin 6) where
  toFun := ![2, 5, 0, 1, 4, 3]
  invFun := ![2, 3, 0, 5, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation237 : Equiv.Perm (Fin 6) where
  toFun := ![2, 5, 1, 3, 4, 0]
  invFun := ![5, 2, 0, 3, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation238 : Equiv.Perm (Fin 6) where
  toFun := ![2, 5, 1, 4, 3, 0]
  invFun := ![5, 2, 0, 4, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation239 : Equiv.Perm (Fin 6) where
  toFun := ![2, 5, 3, 0, 1, 4]
  invFun := ![3, 4, 0, 2, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation240 : Equiv.Perm (Fin 6) where
  toFun := ![2, 5, 4, 0, 1, 3]
  invFun := ![3, 4, 0, 5, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation241 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation242 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 5, 4]
  invFun := ![1, 2, 3, 0, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation243 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 2, 1, 4, 5]
  invFun := ![1, 3, 2, 0, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation244 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 2, 4, 1, 5]
  invFun := ![1, 4, 2, 0, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation245 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 4, 5, 1, 2]
  invFun := ![1, 4, 5, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation246 : Equiv.Perm (Fin 6) where
  toFun := ![3, 1, 2, 4, 0, 5]
  invFun := ![4, 1, 2, 0, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation247 : Equiv.Perm (Fin 6) where
  toFun := ![3, 2, 4, 0, 1, 5]
  invFun := ![3, 4, 1, 0, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation248 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 0, 1, 2, 5]
  invFun := ![2, 3, 4, 0, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation249 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 0, 1, 5, 2]
  invFun := ![2, 3, 5, 0, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation250 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 1, 0, 5, 2]
  invFun := ![3, 2, 5, 0, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation251 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 2, 5, 0, 1]
  invFun := ![4, 5, 2, 0, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation252 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 0, 1, 2]
  invFun := ![3, 4, 5, 0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation253 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 0, 2, 1]
  invFun := ![3, 5, 4, 0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation255 : Equiv.Perm (Fin 6) where
  toFun := ![3, 5, 1, 2, 0, 4]
  invFun := ![4, 2, 3, 0, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation256 : Equiv.Perm (Fin 6) where
  toFun := ![3, 5, 1, 2, 4, 0]
  invFun := ![5, 2, 3, 0, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation257 : Equiv.Perm (Fin 6) where
  toFun := ![3, 5, 4, 0, 1, 2]
  invFun := ![3, 4, 5, 0, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation258 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 2, 3, 5]
  invFun := ![1, 2, 3, 4, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation259 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 2, 5, 3]
  invFun := ![1, 2, 3, 5, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation260 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 3, 2, 5]
  invFun := ![1, 2, 4, 3, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation261 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 3, 5, 2]
  invFun := ![1, 2, 5, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation262 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 5, 2, 3]
  invFun := ![1, 2, 4, 5, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation263 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 5, 3, 2]
  invFun := ![1, 2, 5, 4, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation264 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 2, 1, 3, 5]
  invFun := ![1, 3, 2, 4, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation265 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 2, 1, 5, 3]
  invFun := ![1, 3, 2, 5, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation266 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 2, 3, 1, 5]
  invFun := ![1, 4, 2, 3, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation267 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 2, 3, 5, 1]
  invFun := ![1, 5, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation268 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 2, 5, 1, 3]
  invFun := ![1, 4, 2, 5, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation269 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 2, 5, 3, 1]
  invFun := ![1, 5, 2, 4, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation270 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 3, 1, 2, 5]
  invFun := ![1, 3, 4, 2, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation271 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 3, 1, 5, 2]
  invFun := ![1, 3, 5, 2, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation272 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 3, 2, 1, 5]
  invFun := ![1, 4, 3, 2, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation273 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 3, 2, 5, 1]
  invFun := ![1, 5, 3, 2, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation274 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 3, 5, 1, 2]
  invFun := ![1, 4, 5, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation275 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 5, 1, 2, 3]
  invFun := ![1, 3, 4, 5, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation276 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 5, 1, 3, 2]
  invFun := ![1, 3, 5, 4, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation277 : Equiv.Perm (Fin 6) where
  toFun := ![4, 1, 0, 2, 3, 5]
  invFun := ![2, 1, 3, 4, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation278 : Equiv.Perm (Fin 6) where
  toFun := ![4, 1, 0, 2, 5, 3]
  invFun := ![2, 1, 3, 5, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation279 : Equiv.Perm (Fin 6) where
  toFun := ![4, 1, 0, 5, 2, 3]
  invFun := ![2, 1, 4, 5, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation280 : Equiv.Perm (Fin 6) where
  toFun := ![4, 1, 2, 0, 3, 5]
  invFun := ![3, 1, 2, 4, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation281 : Equiv.Perm (Fin 6) where
  toFun := ![4, 1, 3, 2, 0, 5]
  invFun := ![4, 1, 3, 2, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation282 : Equiv.Perm (Fin 6) where
  toFun := ![4, 1, 3, 5, 2, 0]
  invFun := ![5, 1, 4, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation283 : Equiv.Perm (Fin 6) where
  toFun := ![4, 2, 0, 1, 3, 5]
  invFun := ![2, 3, 1, 4, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation284 : Equiv.Perm (Fin 6) where
  toFun := ![4, 2, 0, 1, 5, 3]
  invFun := ![2, 3, 1, 5, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation285 : Equiv.Perm (Fin 6) where
  toFun := ![4, 2, 0, 3, 5, 1]
  invFun := ![2, 5, 1, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation286 : Equiv.Perm (Fin 6) where
  toFun := ![4, 2, 3, 0, 1, 5]
  invFun := ![3, 4, 1, 2, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation287 : Equiv.Perm (Fin 6) where
  toFun := ![4, 2, 5, 0, 3, 1]
  invFun := ![3, 5, 1, 4, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation288 : Equiv.Perm (Fin 6) where
  toFun := ![4, 3, 0, 1, 2, 5]
  invFun := ![2, 3, 4, 1, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation289 : Equiv.Perm (Fin 6) where
  toFun := ![4, 3, 0, 1, 5, 2]
  invFun := ![2, 3, 5, 1, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation290 : Equiv.Perm (Fin 6) where
  toFun := ![4, 3, 1, 2, 0, 5]
  invFun := ![4, 2, 3, 1, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation291 : Equiv.Perm (Fin 6) where
  toFun := ![4, 3, 1, 2, 5, 0]
  invFun := ![5, 2, 3, 1, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation292 : Equiv.Perm (Fin 6) where
  toFun := ![4, 3, 2, 5, 0, 1]
  invFun := ![4, 5, 2, 1, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation293 : Equiv.Perm (Fin 6) where
  toFun := ![4, 3, 5, 0, 2, 1]
  invFun := ![3, 5, 4, 1, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation294 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 0, 1, 2, 3]
  invFun := ![2, 3, 4, 5, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation295 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 0, 1, 3, 2]
  invFun := ![2, 3, 5, 4, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation296 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 0, 2, 1, 3]
  invFun := ![2, 4, 3, 5, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation297 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 0, 2, 3, 1]
  invFun := ![2, 5, 3, 4, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation298 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 1, 0, 2, 3]
  invFun := ![3, 2, 4, 5, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation299 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 1, 0, 3, 2]
  invFun := ![3, 2, 5, 4, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation300 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 1, 2, 3, 0]
  invFun := ![5, 2, 3, 4, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation301 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 2, 1, 3, 0]
  invFun := ![5, 3, 2, 4, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation302 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 2, 3, 0, 1]
  invFun := ![4, 5, 2, 3, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation303 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 3, 0, 1, 2]
  invFun := ![3, 4, 5, 2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation304 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 3, 0, 2, 1]
  invFun := ![3, 5, 4, 2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation305 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 3, 1, 0, 2]
  invFun := ![4, 3, 5, 2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation306 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 3, 1, 2, 0]
  invFun := ![5, 3, 4, 2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation307 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 3, 2, 0, 1]
  invFun := ![4, 5, 3, 2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation308 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation309 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 4, 3]
  invFun := ![1, 2, 3, 5, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation310 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 3, 2, 4]
  invFun := ![1, 2, 4, 3, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation311 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 3, 4, 2]
  invFun := ![1, 2, 5, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation312 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 4, 2, 3]
  invFun := ![1, 2, 4, 5, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation313 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 4, 3, 2]
  invFun := ![1, 2, 5, 4, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation314 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 2, 1, 3, 4]
  invFun := ![1, 3, 2, 4, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation315 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 2, 1, 4, 3]
  invFun := ![1, 3, 2, 5, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation316 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 2, 3, 1, 4]
  invFun := ![1, 4, 2, 3, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation317 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 2, 3, 4, 1]
  invFun := ![1, 5, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation318 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 2, 4, 1, 3]
  invFun := ![1, 4, 2, 5, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation319 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 2, 4, 3, 1]
  invFun := ![1, 5, 2, 4, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation320 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 3, 1, 2, 4]
  invFun := ![1, 3, 4, 2, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation321 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 3, 1, 4, 2]
  invFun := ![1, 3, 5, 2, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation322 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 3, 2, 1, 4]
  invFun := ![1, 4, 3, 2, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation323 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 3, 2, 4, 1]
  invFun := ![1, 5, 3, 2, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation324 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 3, 4, 1, 2]
  invFun := ![1, 4, 5, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation325 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 3, 4, 2, 1]
  invFun := ![1, 5, 4, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation326 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 4, 1, 2, 3]
  invFun := ![1, 3, 4, 5, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation327 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 4, 1, 3, 2]
  invFun := ![1, 3, 5, 4, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation328 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 4, 2, 3, 1]
  invFun := ![1, 5, 3, 4, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation329 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 4, 3, 1, 2]
  invFun := ![1, 4, 5, 3, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation330 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 4, 3, 2, 1]
  invFun := ![1, 5, 4, 3, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation331 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 0, 2, 3, 4]
  invFun := ![2, 1, 3, 4, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation332 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 0, 2, 4, 3]
  invFun := ![2, 1, 3, 5, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation333 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 0, 3, 2, 4]
  invFun := ![2, 1, 4, 3, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation334 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 0, 3, 4, 2]
  invFun := ![2, 1, 5, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation335 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 0, 4, 2, 3]
  invFun := ![2, 1, 4, 5, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation336 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 0, 4, 3, 2]
  invFun := ![2, 1, 5, 4, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation337 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 2, 0, 3, 4]
  invFun := ![3, 1, 2, 4, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation338 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 2, 0, 4, 3]
  invFun := ![3, 1, 2, 5, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation339 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 2, 3, 0, 4]
  invFun := ![4, 1, 2, 3, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation340 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 2, 3, 4, 0]
  invFun := ![5, 1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation341 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 2, 4, 0, 3]
  invFun := ![4, 1, 2, 5, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation342 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 2, 4, 3, 0]
  invFun := ![5, 1, 2, 4, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation343 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 3, 0, 2, 4]
  invFun := ![3, 1, 4, 2, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation344 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 3, 0, 4, 2]
  invFun := ![3, 1, 5, 2, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation345 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 3, 2, 0, 4]
  invFun := ![4, 1, 3, 2, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation346 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 3, 2, 4, 0]
  invFun := ![5, 1, 3, 2, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation347 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 3, 4, 0, 2]
  invFun := ![4, 1, 5, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation348 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 3, 4, 2, 0]
  invFun := ![5, 1, 4, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation349 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 4, 0, 2, 3]
  invFun := ![3, 1, 4, 5, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation350 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 4, 0, 3, 2]
  invFun := ![3, 1, 5, 4, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation351 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 4, 2, 0, 3]
  invFun := ![4, 1, 3, 5, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation352 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 4, 2, 3, 0]
  invFun := ![5, 1, 3, 4, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation353 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 4, 3, 0, 2]
  invFun := ![4, 1, 5, 3, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation354 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 4, 3, 2, 0]
  invFun := ![5, 1, 4, 3, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation355 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 0, 1, 3, 4]
  invFun := ![2, 3, 1, 4, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation356 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 0, 1, 4, 3]
  invFun := ![2, 3, 1, 5, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation357 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 1, 0, 3, 4]
  invFun := ![3, 2, 1, 4, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation358 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 1, 0, 4, 3]
  invFun := ![3, 2, 1, 5, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation359 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 1, 3, 0, 4]
  invFun := ![4, 2, 1, 3, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation360 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 1, 3, 4, 0]
  invFun := ![5, 2, 1, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation361 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 1, 4, 0, 3]
  invFun := ![4, 2, 1, 5, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation362 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 1, 4, 3, 0]
  invFun := ![5, 2, 1, 4, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation363 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 3, 0, 1, 4]
  invFun := ![3, 4, 1, 2, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation364 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 3, 1, 0, 4]
  invFun := ![4, 3, 1, 2, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation365 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 3, 1, 4, 0]
  invFun := ![5, 3, 1, 2, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation366 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 3, 4, 0, 1]
  invFun := ![4, 5, 1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation367 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 3, 4, 1, 0]
  invFun := ![5, 4, 1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation368 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 4, 0, 1, 3]
  invFun := ![3, 4, 1, 5, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation369 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 4, 0, 3, 1]
  invFun := ![3, 5, 1, 4, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation370 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 4, 1, 3, 0]
  invFun := ![5, 3, 1, 4, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation371 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 4, 3, 0, 1]
  invFun := ![4, 5, 1, 3, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation372 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 4, 3, 1, 0]
  invFun := ![5, 4, 1, 3, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation373 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 0, 1, 2, 4]
  invFun := ![2, 3, 4, 1, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation374 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 0, 1, 4, 2]
  invFun := ![2, 3, 5, 1, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation375 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 0, 2, 1, 4]
  invFun := ![2, 4, 3, 1, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation376 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 0, 4, 2, 1]
  invFun := ![2, 5, 4, 1, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation377 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 1, 0, 2, 4]
  invFun := ![3, 2, 4, 1, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation378 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 1, 0, 4, 2]
  invFun := ![3, 2, 5, 1, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation379 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 1, 2, 0, 4]
  invFun := ![4, 2, 3, 1, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation380 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 1, 2, 4, 0]
  invFun := ![5, 2, 3, 1, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation381 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 1, 4, 0, 2]
  invFun := ![4, 2, 5, 1, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation382 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 1, 4, 2, 0]
  invFun := ![5, 2, 4, 1, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation383 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 2, 0, 1, 4]
  invFun := ![3, 4, 2, 1, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation384 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 2, 0, 4, 1]
  invFun := ![3, 5, 2, 1, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation385 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 2, 1, 0, 4]
  invFun := ![4, 3, 2, 1, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation386 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 2, 1, 4, 0]
  invFun := ![5, 3, 2, 1, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation387 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 2, 4, 0, 1]
  invFun := ![4, 5, 2, 1, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation388 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 2, 4, 1, 0]
  invFun := ![5, 4, 2, 1, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation389 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 4, 0, 1, 2]
  invFun := ![3, 4, 5, 1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation390 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 4, 0, 2, 1]
  invFun := ![3, 5, 4, 1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation391 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 4, 1, 0, 2]
  invFun := ![4, 3, 5, 1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation392 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 4, 1, 2, 0]
  invFun := ![5, 3, 4, 1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation393 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 4, 2, 0, 1]
  invFun := ![4, 5, 3, 1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation394 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 4, 2, 1, 0]
  invFun := ![5, 4, 3, 1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation395 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 0, 1, 2, 3]
  invFun := ![2, 3, 4, 5, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation396 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 0, 1, 3, 2]
  invFun := ![2, 3, 5, 4, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation397 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 0, 2, 3, 1]
  invFun := ![2, 5, 3, 4, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation398 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 1, 0, 2, 3]
  invFun := ![3, 2, 4, 5, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation399 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 1, 0, 3, 2]
  invFun := ![3, 2, 5, 4, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation400 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 1, 2, 0, 3]
  invFun := ![4, 2, 3, 5, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation401 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 1, 2, 3, 0]
  invFun := ![5, 2, 3, 4, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation402 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 1, 3, 0, 2]
  invFun := ![4, 2, 5, 3, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation403 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 2, 1, 0, 3]
  invFun := ![4, 3, 2, 5, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation404 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 2, 3, 0, 1]
  invFun := ![4, 5, 2, 3, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation405 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 2, 3, 1, 0]
  invFun := ![5, 4, 2, 3, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation406 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 3, 0, 1, 2]
  invFun := ![3, 4, 5, 2, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation407 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 3, 1, 0, 2]
  invFun := ![4, 3, 5, 2, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation408 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 3, 2, 0, 1]
  invFun := ![4, 5, 3, 2, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation409 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 3, 2, 1, 0]
  invFun := ![5, 4, 3, 2, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

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

def pivotMatrix5 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

def pivotMatrix6 : Matrix (Fin 3) (Fin 2) ℤ := ![![1, -1], ![-5, 5], ![4, -4]]

def pivotMatrix8 : Matrix (Fin 3) (Fin 2) ℤ := ![![1, -1], ![-4, 4], ![3, -3]]

def pivotPermutation10 : Equiv.Perm (Fin 3) where
  toFun := ![1, 0, 2]
  invFun := ![1, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix10 : Matrix (Fin 3) (Fin 2) ℤ := ![![1, -1], ![-3, 3], ![2, -2]]

def pivotPermutation11 : Equiv.Perm (Fin 3) where
  toFun := ![1, 0, 2]
  invFun := ![1, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix11 : Matrix (Fin 3) (Fin 2) ℤ := ![![1, -1], ![-2, 2], ![1, -1]]

def pivotPermutation12 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix12 : Matrix (Fin 4) (Fin 2) ℤ := ![![1, -1], ![-5, 5], ![1, -1], ![3, -3]]

def pivotPermutation13 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix13 : Matrix (Fin 4) (Fin 2) ℤ := ![![1, -1], ![-5, 5], ![2, -2], ![2, -2]]

def pivotMatrix14 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-4, 4], ![1, -1], ![4, -4]]

def pivotMatrix15 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-4, 4], ![2, -2], ![3, -3]]

def pivotMatrix16 : Matrix (Fin 4) (Fin 2) ℤ := ![![1, -1], ![-4, 4], ![1, -1], ![2, -2]]

def pivotMatrix24 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-3, 3], ![1, -1], ![3, -3]]

def pivotMatrix25 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-3, 3], ![2, -2], ![2, -2]]

def pivotMatrix26 : Matrix (Fin 4) (Fin 2) ℤ := ![![1, -1], ![-3, 3], ![1, -1], ![1, -1]]

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

def pivotMatrix102 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-3, 1, 2], ![0, -2, 2], ![2, 2, -4]]

def pivotPermutation105 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix105 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, 2, -2], ![3, -2, -1]]

def pivotPermutation106 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix106 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![1, -2, 1], ![2, 2, -4]]

def pivotPermutation107 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix107 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![1, 2, -3], ![2, -2, 0]]

def pivotPermutation108 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix108 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 1, 2], ![1, -3, 2], ![2, 1, -3]]

def pivotPermutation109 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix109 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 1, 2], ![1, 1, -2], ![2, -3, 1]]

def pivotPermutation113 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix113 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-3, 1, 2], ![1, -3, 2], ![1, 3, -4]]

def pivotPermutation116 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix116 : Matrix (Fin 5) (Fin 2) ℤ := ![![1, -1], ![-3, 3], ![-2, 2], ![1, -1], ![3, -3]]

def pivotPermutation117 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix117 : Matrix (Fin 5) (Fin 2) ℤ := ![![1, -1], ![-3, 3], ![-2, 2], ![2, -2], ![2, -2]]

def pivotPermutation118 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix118 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-3, 3], ![1, -1], ![1, -1], ![2, -2]]

def pivotPermutation119 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix119 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -3, 5], ![0, 1, -1], ![2, 1, -3]]

def pivotPermutation120 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix120 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -3, 5], ![0, 2, -2], ![2, 0, -2]]

def pivotPermutation121 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix121 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -3, 5], ![0, 3, -3], ![2, -1, -1]]

def pivotPermutation122 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix122 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -3, 5], ![1, -1, 0], ![1, 3, -4]]

def pivotPermutation123 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix123 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -3, 5], ![1, 0, -1], ![1, 2, -3]]

def pivotPermutation124 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix124 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -3, 5], ![1, 1, -2], ![1, 1, -2]]

def pivotPermutation126 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix126 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-2, -3, 5], ![0, 2, -2], ![1, 2, -3]]

def pivotPermutation127 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix127 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-2, -3, 5], ![0, 2, -2], ![1, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotPermutation128 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix128 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-2, -3, 5], ![0, 3, -3], ![1, 1, -2]]

def pivotPermutation129 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix129 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-2, -3, 5], ![0, 3, -3], ![1, 0, -1]]

def pivotPermutation130 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix130 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-2, -3, 5], ![0, 4, -4], ![1, 0, -1]]

def pivotPermutation131 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix131 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -2, 4], ![1, -1, 0], ![2, 2, -4]]

def pivotPermutation132 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix132 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -2, 4], ![1, 2, -3], ![2, -1, -1]]

def pivotMatrix133 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -2, 4], ![1, 3, -4], ![2, -2, 0]]

def pivotMatrix137 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-2, -2, 4], ![-1, 4, -3], ![2, -1, -1]]

def pivotMatrix138 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-2, -2, 4], ![-1, 4, -3], ![2, -2, 0]]

def pivotMatrix139 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -2, 4], ![0, 1, -1], ![2, 2, -4]]

def pivotMatrix140 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -2, 4], ![0, 2, -2], ![2, 1, -3]]

def pivotMatrix141 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -2, 4], ![0, 3, -3], ![2, 0, -2]]

def pivotMatrix142 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -2, 4], ![1, -1, 0], ![1, 4, -5]]

def pivotMatrix143 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -2, 4], ![1, 0, -1], ![1, 3, -4]]

def pivotMatrix144 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -2, 4], ![1, 1, -2], ![1, 2, -3]]

def pivotMatrix145 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -2, 4], ![0, 1, -1], ![2, 0, -2]]

def pivotMatrix146 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -2, 4], ![0, 2, -2], ![2, -1, -1]]

def pivotMatrix147 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -2, 4], ![0, 3, -3], ![2, -2, 0]]

def pivotMatrix148 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -2, 4], ![1, -2, 1], ![1, 3, -4]]

def pivotMatrix149 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -2, 4], ![1, -1, 0], ![1, 2, -3]]

def pivotMatrix150 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -2, 4], ![1, 0, -1], ![1, 1, -2]]

def pivotMatrix153 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-2, -2, 4], ![0, 2, -2], ![1, 1, -2]]

def pivotMatrix155 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-2, -2, 4], ![0, 3, -3], ![1, 0, -1]]

def pivotMatrix156 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-2, -2, 4], ![0, 4, -4], ![1, -2, 1]]

def pivotMatrix157 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-2, -2, 4], ![0, 4, -4], ![1, -1, 0]]

def pivotMatrix158 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![1, 3, -4], ![2, -3, 1]]

def pivotMatrix165 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-2, -1, 3], ![0, -2, 2], ![1, 4, -5]]

def pivotMatrix166 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-2, -1, 3], ![0, -2, 2], ![1, 3, -4]]

def pivotMatrix168 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, 1, -1], ![2, 1, -3]]

def pivotMatrix169 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, 2, -2], ![2, 0, -2]]

def pivotMatrix170 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, 3, -3], ![2, -1, -1]]

def pivotMatrix171 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, 4, -4], ![2, -2, 0]]

def pivotMatrix172 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![1, -2, 1], ![1, 4, -5]]

def pivotMatrix173 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![1, -1, 0], ![1, 3, -4]]

def pivotMatrix174 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![1, 0, -1], ![1, 2, -3]]

def pivotMatrix175 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![1, 1, -2], ![1, 1, -2]]

def pivotMatrix176 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![0, 1, -1], ![2, -1, -1]]

def pivotMatrix177 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![0, 2, -2], ![2, -2, 0]]

def pivotMatrix178 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![0, 3, -3], ![2, -3, 1]]

def pivotMatrix179 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![1, -3, 2], ![1, 3, -4]]

def pivotMatrix180 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![1, -2, 1], ![1, 2, -3]]

def pivotMatrix181 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![1, -1, 0], ![1, 1, -2]]

def pivotMatrix185 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-2, -1, 3], ![0, 2, -2], ![1, 0, -1]]

def pivotMatrix187 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-2, -1, 3], ![0, 3, -3], ![1, -2, 1]]

def pivotMatrix188 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-2, -1, 3], ![0, 3, -3], ![1, -1, 0]]

def pivotMatrix189 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-2, -1, 3], ![0, 4, -4], ![1, -3, 2]]

def pivotMatrix190 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-2, -1, 3], ![0, 4, -4], ![1, -2, 1]]

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

def pivotMatrix194 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-2, 0, 2], ![0, -3, 3], ![1, 4, -5]]

def pivotMatrix195 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-2, 0, 2], ![0, -3, 3], ![1, 3, -4]]

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

def pivotMatrix254 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -3, 4], ![0, 2, -2], ![1, 0, -1]]

def pivotMatrix255 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -3, 4], ![0, 3, -3], ![1, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix256 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-1, -3, 4], ![0, 2, -2], ![0, 2, -2]]

def pivotMatrix257 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-3, 2, 3, -2], ![4, -2, -3, 1]]

def pivotMatrix259 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 2, -3]]

def pivotMatrix261 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-1, -2, 3], ![-1, 2, -1], ![1, 1, -2]]

def pivotMatrix263 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-1, -2, 3], ![-1, 3, -2], ![1, 0, -1]]

def pivotMatrix264 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, -2, 2, 2], ![3, 2, -2, -3]]

def pivotMatrix265 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, -2, 3, 1], ![3, 2, -3, -2]]

def pivotMatrix266 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, -2, 3], ![0, -2, 2], ![0, 4, -4]]

def pivotMatrix267 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -2, 3], ![0, 1, -1], ![1, 2, -3]]

def pivotMatrix268 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -2, 3], ![0, 2, -2], ![1, 1, -2]]

def pivotMatrix269 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -2, 3], ![0, 3, -3], ![1, 0, -1]]

def pivotMatrix270 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -2, 3], ![0, 4, -4], ![1, -1, 0]]

def pivotMatrix271 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -2, 3], ![0, 1, -1], ![1, 0, -1]]

def pivotMatrix272 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -2, 3], ![0, 2, -2], ![1, -1, 0]]

def pivotMatrix273 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -2, 3], ![0, 3, -3], ![1, -2, 1]]

def pivotMatrix274 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 2, 2, -2], ![3, -2, -2, 1]]

def pivotMatrix277 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -3, 3, 1], ![2, 3, -3, -2]]

def pivotMatrix278 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, -1, 2], ![0, -3, 3], ![0, 4, -4]]

def pivotMatrix279 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -2, 2, 1], ![2, 2, -2, -2]]

def pivotMatrix280 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, -1, 2], ![0, -2, 2], ![0, 3, -3]]

def pivotMatrix281 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-1, -1, 2], ![0, -2, 2], ![0, 4, -4]]

def pivotMatrix282 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -2, 5, -2], ![2, 2, -5, 1]]

def pivotMatrix283 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2]]

def pivotMatrix284 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1]]

def pivotMatrix285 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0]]

def pivotMatrix286 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, 4, -4], ![1, -2, 1]]

def pivotMatrix287 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0]]

def pivotMatrix288 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -1, 2], ![0, 2, -2], ![1, -2, 1]]

def pivotMatrix289 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 3, -3], ![1, 0, -1]]

def pivotMatrix290 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 4, -4], ![1, -1, 0]]

def pivotMatrix291 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

def pivotMatrix292 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0]]

def pivotMatrix293 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]

def pivotMatrix294 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0]]

def pivotMatrix295 : Matrix (Fin 6) (Fin 2) ℤ := ![![1, -1], ![-5, 5], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]

def pivotMatrix296 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]

def pivotMatrix297 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

def pivotMatrix298 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -2, 5], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]

def pivotMatrix299 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

def pivotMatrix300 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -2, 5], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

def pivotMatrix301 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -2, 5], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

def pivotMatrix302 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -2, 5], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]

def pivotMatrix303 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-3, -2, 5], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def pivotMatrix304 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix305 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]

def pivotMatrix306 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]

def pivotMatrix307 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]

def pivotMatrix308 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

def pivotMatrix309 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]

def pivotMatrix310 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]

def pivotMatrix311 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]

def pivotMatrix312 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]

def pivotMatrix313 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]

def pivotMatrix314 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]

def pivotMatrix315 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]

def pivotMatrix316 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]

def pivotMatrix317 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

def pivotMatrix318 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -1, 4], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]

def pivotMatrix319 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]

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

def pivotMatrix1000 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, 0, 2], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def pivotPermutation1001 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1001 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, 0, 2], ![0, 2, -3, 1], ![1, 0, 2, -3]]

def pivotPermutation1002 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1002 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, 0, 2], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def pivotPermutation1003 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1003 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, 0, 2], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def pivotPermutation1004 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1004 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, 0, 2], ![0, 2, 2, -4], ![1, 0, -3, 2]]

def pivotPermutation1005 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1005 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 1, 1], ![0, 2, -2, 0], ![2, -1, 1, -2]]

def pivotPermutation1006 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1006 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 0, 2], ![0, -1, 2, -1], ![1, 1, -1, -1]]

def pivotPermutation1007 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1007 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![0, 2, -3, 1], ![2, -1, 1, -2]]

def pivotPermutation1008 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1008 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -2, 0]]

def pivotPermutation1009 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1009 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1]]

def pivotPermutation1010 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1010 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![0, 2, 0, -2], ![2, -1, -2, 1]]

def pivotPermutation1011 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1011 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![0, 2, 1, -3], ![2, -1, -3, 2]]

def pivotPermutation1012 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1012 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 1, 1], ![0, 3, -3, 0], ![2, -2, 2, -2]]

def pivotPermutation1013 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1013 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 1, 1], ![0, 3, -2, -1], ![2, -2, 1, -1]]

def pivotPermutation1014 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1014 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![0, 3, -4, 1], ![2, -2, 2, -2]]

def pivotPermutation1015 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1015 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 2, -3, 1]]

def pivotPermutation1016 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1016 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![0, 3, -1, -2], ![2, -2, -1, 1]]

def pivotPermutation1017 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1017 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![0, 3, 0, -3], ![2, -2, -2, 2]]

def pivotPermutation1018 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1018 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 3, -1], ![0, 3, -2, -1], ![2, -2, -1, 1]]

def pivotPermutation1019 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1019 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 1, 1], ![0, 4, -3, -1], ![2, -3, 2, -1]]

def pivotPermutation1020 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1020 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![0, 4, -1, -3], ![2, -3, -1, 2]]

def pivotPermutation1021 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1021 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, -3, 3, 0], ![2, 3, -3, -2]]

def pivotPermutation1022 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1022 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, -3, 4, -1], ![2, 3, -4, -1]]

def pivotPermutation1023 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1023 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, 0, 2], ![0, 0, -3, 3], ![1, 0, 3, -4]]

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

def pivotMatrix1024 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 1, 0], ![0, -3, 1, 2], ![2, 3, -2, -3]]

def pivotPermutation1025 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1025 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![0, -3, 0, 3], ![2, 3, -2, -3]]

def pivotPermutation1026 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1026 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![0, -3, 2, 1], ![2, 3, -4, -1]]

def pivotPermutation1027 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1027 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, -2, 2, 0], ![2, 2, -2, -2]]

def pivotPermutation1028 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1028 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, -2, 3, -1], ![2, 2, -3, -1]]

def pivotPermutation1029 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1029 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, -2, 4, -2], ![2, 2, -4, 0]]

def pivotPermutation1030 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1030 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 1, 0], ![0, -2, -2, 4], ![2, 2, 1, -5]]

def pivotPermutation1031 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1031 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 0, 2], ![0, 0, -2, 2], ![1, 0, 3, -4]]

def pivotPermutation1032 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1032 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, 0, 2], ![0, 0, -2, 2], ![1, 0, 2, -3]]

def pivotPermutation1033 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1033 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 1, 0], ![0, -2, 1, 1], ![2, 2, -2, -2]]

def pivotPermutation1034 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1034 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![0, -2, -2, 4], ![2, 2, 0, -4]]

def pivotPermutation1035 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1035 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![0, -2, -1, 3], ![2, 2, -1, -3]]

def pivotPermutation1036 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1036 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![0, -2, 1, 1], ![2, 2, -3, -1]]

def pivotPermutation1037 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1037 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 2, -4]]

def pivotPermutation1038 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1038 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![0, -2, 3, -1], ![2, 2, -5, 1]]

def pivotPermutation1039 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1039 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 0, 2], ![0, 0, 1, -1], ![1, 1, 0, -2]]

def pivotPermutation1040 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1040 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 0, 2], ![0, 0, 2, -2], ![1, 1, -1, -1]]

def pivotPermutation1041 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1041 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 0, 2], ![0, 0, 3, -3], ![1, 1, -2, 0]]

def pivotPermutation1042 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1042 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 0, 2], ![0, 1, -2, 1], ![1, 0, 3, -4]]

def pivotPermutation1043 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1043 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 0, 2], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def pivotPermutation1044 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1044 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 0, 2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def pivotPermutation1045 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1045 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, 0, 2], ![0, 0, 1, -1], ![1, 1, -2, 0]]

def pivotPermutation1046 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1046 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, 0, 2], ![0, 1, -3, 2], ![1, 0, 2, -3]]

def pivotPermutation1047 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1047 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, 0, 2], ![0, 1, -2, 1], ![1, 0, 1, -2]]

def pivotPermutation1048 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1048 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, 0, 2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def pivotPermutation1049 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1049 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, 0, 2], ![0, 2, -3, 1], ![1, -1, 2, -2]]

def pivotPermutation1050 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1050 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, 0, 2], ![0, 2, 1, -3], ![1, -1, -2, 2]]

def pivotPermutation1051 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1051 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 1, 0], ![0, 2, -4, 2], ![2, -2, 3, -3]]

def pivotPermutation1052 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1052 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 1, 0], ![0, 2, -3, 1], ![2, -2, 2, -2]]

def pivotPermutation1053 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1053 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1]]

def pivotPermutation1054 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1054 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 0, 2], ![0, 0, 2, -2], ![1, 0, -1, 0]]

def pivotPermutation1055 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1055 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![0, 2, -4, 2], ![2, -2, 2, -2]]

def pivotPermutation1056 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1056 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![0, 2, -3, 1], ![2, -2, 1, -1]]

def pivotPermutation1057 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1057 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -2, 0]]

def pivotPermutation1058 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1058 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![0, 2, -1, -1], ![2, -2, -1, 1]]

def pivotPermutation1059 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1059 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![0, 2, 0, -2], ![2, -2, -2, 2]]

def pivotPermutation1060 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1060 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![0, 2, 1, -3], ![2, -2, -3, 3]]

def pivotPermutation1061 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1061 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 1, 0], ![0, 3, -4, 1], ![2, -3, 3, -2]]

def pivotPermutation1062 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1062 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -3, 2]]

def pivotPermutation1063 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1063 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -2, 1]]

def pivotPermutation1064 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1064 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![0, 3, -4, 1], ![2, -3, 2, -1]]

def pivotPermutation1065 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1065 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 2, -3, 1]]

def pivotPermutation1066 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1066 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![0, 3, -2, -1], ![2, -3, 0, 1]]

def pivotPermutation1067 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1067 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![0, 3, -1, -2], ![2, -3, -1, 2]]

def pivotPermutation1068 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1068 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![0, 3, 0, -3], ![2, -3, -2, 3]]

def pivotPermutation1069 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1069 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-1, -1, 0, 2], ![0, 0, 4, -4], ![0, 1, -3, 2]]

def pivotPermutation1070 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1070 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 1, 0], ![0, 4, -2, -2], ![2, -4, 1, 1]]

def pivotPermutation1071 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1071 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![0, 4, -3, -1], ![2, -4, 1, 1]]

def pivotPermutation1072 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1072 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, 0, 2], ![0, 1, -3, 2], ![1, -1, 3, -3]]

def pivotPermutation1073 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1073 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![0, -3, 1, 2], ![2, 2, -2, -2]]

def pivotPermutation1074 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1074 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![0, -3, 2, 1], ![2, 2, -3, -1]]

def pivotPermutation1075 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1075 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, -1, 0, 2], ![0, 1, -3, 2], ![0, 1, 3, -4]]

def pivotPermutation1076 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1076 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 2, -2], ![0, -3, 2, 1], ![2, 2, -4, 0]]

def pivotPermutation1077 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1077 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![0, -2, -2, 4], ![2, 1, 1, -4]]

def pivotPermutation1078 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1078 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![0, -2, 1, 1], ![2, 1, -2, -1]]

def pivotPermutation1079 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1079 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 2, -3]]

def pivotPermutation1080 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1080 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![0, -2, 3, -1], ![2, 1, -4, 1]]

def pivotPermutation1081 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1081 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 0, 2], ![0, 1, 2, -3], ![1, -1, -1, 1]]

def pivotPermutation1082 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1082 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 0, 2], ![0, 1, 3, -4], ![1, -1, -2, 2]]

def pivotPermutation1083 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1083 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, 0, 2], ![0, 1, 2, -3], ![1, -1, -2, 2]]

def pivotPermutation1084 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1084 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![0, 1, 1, -2], ![2, -2, -2, 2]]

def pivotPermutation1085 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1085 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![0, 1, 2, -3], ![2, -2, -3, 3]]

def pivotPermutation1086 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1086 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 2, -2], ![0, 3, -3, 0], ![2, -4, 1, 1]]

def pivotPermutation1087 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1087 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 2, -2], ![0, 3, -2, -1], ![2, -4, 0, 2]]

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

def pivotMatrix1089 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -2, 2, 1], ![1, -1, 2, -2], ![1, 3, -4, 0]]

def pivotPermutation1090 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1090 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -2, 2, 1], ![1, 0, 2, -3], ![1, 2, -4, 1]]

def pivotPermutation1091 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1091 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![1, -3, 1, 1], ![1, 4, -3, -2]]

def pivotPermutation1092 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1092 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 1, 1], ![1, -2, 2, -1], ![1, 3, -3, -1]]

def pivotPermutation1093 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1093 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![1, -2, -1, 2], ![1, 3, -1, -3]]

def pivotPermutation1094 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1094 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 2, 1, -3]]

def pivotPermutation1095 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1095 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 2, 2, -4]]

def pivotPermutation1096 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1096 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 1, 1], ![1, -1, 1, -1], ![1, 2, -2, -1]]

def pivotPermutation1097 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1097 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![1, -1, -3, 3], ![1, 2, 1, -4]]

def pivotPermutation1098 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1098 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![1, -1, -2, 2], ![1, 2, 0, -3]]

def pivotPermutation1099 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1099 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, 1, -3]]

def pivotPermutation1100 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1100 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![1, -1, 2, -2], ![1, 2, -4, 1]]

def pivotPermutation1101 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1101 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![1, -3, 3, -1], ![1, 3, -3, -1]]

def pivotPermutation1102 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1102 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 1, 1], ![0, 0, -3, 3], ![1, 0, 3, -4]]

def pivotPermutation1103 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1103 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, 1, 1], ![0, 0, -3, 3], ![1, 0, 2, -3]]

def pivotPermutation1104 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1104 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 1, 0], ![1, -3, 1, 1], ![1, 3, -2, -2]]

def pivotPermutation1105 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1105 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![1, -3, 1, 1], ![1, 3, -3, -1]]

def pivotPermutation1106 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1106 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 3, -2], ![1, -3, 1, 1], ![1, 3, -4, 0]]

def pivotPermutation1107 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1107 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![1, -2, 2, -1], ![1, 2, -2, -1]]

def pivotPermutation1108 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1108 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 1, 0], ![1, -2, -2, 3], ![1, 2, 1, -4]]

def pivotPermutation1109 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1109 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 1, 1], ![0, 0, -2, 2], ![1, 0, 2, -3]]

def pivotPermutation1110 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1110 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, 1, 1], ![0, 0, -2, 2], ![1, 0, 1, -2]]

def pivotPermutation1111 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1111 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![1, -2, -1, 2], ![1, 2, -1, -2]]

def pivotPermutation1112 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1112 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![1, -2, 0, 1], ![1, 2, -2, -1]]

def pivotPermutation1113 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1113 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![1, -2, 2, -1], ![1, 2, -4, 1]]

def pivotPermutation1114 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1114 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 1, 1], ![0, 0, 1, -1], ![1, 1, -1, -1]]

def pivotPermutation1115 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1115 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 1, 1], ![0, 1, -3, 2], ![1, 0, 3, -4]]

def pivotPermutation1116 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1116 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 1, 1], ![0, 1, -2, 1], ![1, 0, 2, -3]]

def pivotPermutation1117 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1117 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 1, 1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def pivotPermutation1118 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1118 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def pivotPermutation1119 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1119 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 1, 1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def pivotPermutation1120 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1120 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![1, 2, 0, -3], ![1, -2, -2, 3]]

def pivotPermutation1121 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1121 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![1, -4, 2, 1], ![1, 3, -3, -1]]

def pivotPermutation1122 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1122 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, 1, 1], ![0, 1, -3, 2], ![1, -1, 2, -2]]

def pivotPermutation1123 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1123 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![1, -3, 1, 1], ![1, 2, -2, -1]]

def pivotPermutation1124 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1124 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, -1, 1, 1], ![0, 1, -3, 2], ![0, 1, 2, -3]]

def pivotPermutation1125 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1125 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 2, -2], ![1, -3, 2, 0], ![1, 2, -4, 1]]

def pivotPermutation1126 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1126 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, -1, 1, 1], ![0, 1, -2, 1], ![0, 1, 1, -2]]

def pivotPermutation1127 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1127 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 2, -2], ![1, -2, 2, -1], ![1, 1, -4, 2]]

def pivotPermutation1128 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1128 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, 1, 1], ![0, 1, 2, -3], ![1, -1, -3, 3]]

def pivotPermutation1129 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1129 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![1, 1, 1, -3], ![1, -2, -2, 3]]

def pivotPermutation1130 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1130 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2]]

def pivotPermutation1131 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1131 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2]]

def pivotPermutation1132 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1132 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1]]

def pivotPermutation1133 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1133 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![-1, -1, 2], ![-1, -1, 2], ![0, 4, -4], ![1, -2, 1]]

def pivotPermutation1134 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1134 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2], ![0, 4, -4], ![1, -1, 0]]

def pivotPermutation1135 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1135 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def pivotPermutation1136 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1136 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def pivotPermutation1137 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1137 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![1, -3, 2], ![1, 1, -2]]

def pivotPermutation1138 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1138 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def pivotPermutation1139 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1139 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def pivotPermutation1140 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1140 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 4, -4], ![1, -2, 1], ![1, -1, 0]]

def pivotPermutation1141 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1141 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def pivotPermutation1142 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1142 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

def pivotPermutation1143 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1143 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![-1, -1, 2], ![-1, 3, -2], ![0, -2, 2], ![1, 0, -1]]

def pivotPermutation1144 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1144 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![-1, -1, 2], ![-1, 4, -3], ![0, -3, 3], ![1, 0, -1]]

def pivotPermutation1145 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1145 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, -2, 2], ![0, 4, -4], ![1, 0, -1]]

def pivotPermutation1146 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1146 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2]]

def pivotPermutation1147 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1147 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

def pivotPermutation1149 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1149 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1]]

def pivotPermutation1150 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1150 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0]]

def pivotPermutation1151 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1151 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

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

def pivotMatrix1152 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def pivotPermutation1153 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1153 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1]]

def pivotPermutation1154 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1154 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -2, 3, 0], ![2, -1, 1, -2], ![0, 3, -4, 1]]

def pivotPermutation1155 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1155 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![2, -3, 0, 1], ![0, 4, -2, -2]]

def pivotPermutation1156 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1156 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, -1, 2, 0], ![0, -1, -3, 4], ![0, 2, 1, -3]]

def pivotPermutation1157 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1157 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 3, -1], ![2, -2, 1, -1], ![0, 3, -4, 1]]

def pivotPermutation1158 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1158 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 3, -2], ![2, -3, 1, 0], ![0, 3, -4, 1]]

def pivotPermutation1159 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1159 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 3, -2], ![2, -2, 1, -1], ![0, 2, -4, 2]]

def pivotPermutation1160 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1160 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![-4, 2, 1, 1], ![5, -1, -2, -2]]

def pivotPermutation1161 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1161 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![-4, 2, 1, 1], ![5, -2, -2, -1]]

def pivotPermutation1162 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1162 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![-3, 1, 0, 2], ![4, 1, -2, -3]]

def pivotPermutation1163 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1163 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![-3, 2, -1, 2], ![4, 0, -1, -3]]

def pivotPermutation1164 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1164 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![-3, 2, 0, 1], ![4, 0, -2, -2]]

def pivotPermutation1165 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1165 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, 0, -3, 4], ![0, -2, 2, 0], ![0, 2, 1, -3]]

def pivotPermutation1166 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1166 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![-3, 3, -1, 1], ![4, -1, -1, -2]]

def pivotPermutation1167 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1167 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -3, 4], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def pivotPermutation1168 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1168 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -3, 4], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def pivotPermutation1169 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1169 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -3, 4], ![0, 2, 0, -2], ![1, -1, 2, -2]]

def pivotPermutation1170 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1170 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, 0, -3, 4], ![0, -1, 2, -1], ![1, 0, 1, -2]]

def pivotPermutation1171 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1171 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 1, 1, -2]]

def pivotPermutation1172 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1172 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![-3, 2, -1, 2], ![4, -1, -1, -2]]

def pivotPermutation1173 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1173 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![-3, 2, 0, 1], ![4, -1, -2, -1]]

def pivotPermutation1174 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1174 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-1, 0, -3, 4], ![0, -1, 3, -2], ![0, 1, 1, -2]]

def pivotPermutation1175 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1175 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, 0, -3, 4], ![0, -1, 3, -2], ![0, 2, 0, -2]]

def pivotPermutation1176 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1176 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 0, -3, 4], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def pivotPermutation1177 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1177 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, 0, -3, 4], ![0, 0, 2, -2], ![1, -1, 1, -1]]

def pivotPermutation1178 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1178 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 1, 1, -2]]

def pivotPermutation1179 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1179 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![-3, 2, -1, 2], ![4, -2, -1, -1]]

def pivotPermutation1180 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1180 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![-3, 2, 0, 1], ![4, -2, -2, 0]]

def pivotPermutation1181 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1181 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, 0, -3, 4], ![0, 0, 3, -3], ![1, -1, 0, 0]]

def pivotPermutation1182 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1182 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![-3, 3, 1, -1], ![4, -3, -2, 1]]

def pivotPermutation1183 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1183 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![-3, 3, -1, 1], ![4, -3, -1, 0]]

def pivotPermutation1184 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1184 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![-3, 3, 0, 0], ![4, -3, -2, 1]]

def pivotPermutation1185 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1185 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, 0, -3, 4], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def pivotPermutation1186 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1186 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![-3, 1, 1, 1], ![4, -2, -2, 0]]

def pivotPermutation1187 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1187 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![-3, 1, 2, 0], ![4, -2, -3, 1]]

def pivotPermutation1188 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1188 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![-2, 1, -1, 2], ![3, 1, -1, -3]]

def pivotPermutation1189 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1189 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-1, 0, -2, 3], ![0, -2, 1, 1], ![0, 2, 2, -4]]

def pivotPermutation1190 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1190 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![-2, 2, -1, 1], ![3, 0, -1, -2]]

def pivotPermutation1191 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1191 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-1, 0, -2, 3], ![0, -2, 2, 0], ![0, 2, 1, -3]]

def pivotPermutation1192 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1192 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![-2, 2, 2, -2], ![3, 0, -4, 1]]

def pivotPermutation1193 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1193 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-1, 0, -2, 3], ![0, -2, 3, -1], ![0, 2, 0, -2]]

def pivotPermutation1194 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1194 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![-2, 4, 0, -2], ![3, -2, -2, 1]]

def pivotPermutation1195 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1195 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![-2, -1, 1, 2], ![3, 2, -2, -3]]

def pivotPermutation1196 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1196 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![-2, -1, 0, 3], ![3, 2, -2, -3]]

def pivotPermutation1197 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1197 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, -2, 3], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def pivotPermutation1198 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1198 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, -2, 3], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def pivotPermutation1199 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1199 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, -2, 3], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def pivotPermutation1200 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1200 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, -2, 3], ![0, 2, -1, -1], ![1, -1, 3, -3]]

def pivotPermutation1201 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1201 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -2, 3], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def pivotPermutation1202 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1202 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -2, 3], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def pivotPermutation1203 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1203 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -2, 3], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def pivotPermutation1204 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1204 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -2, 3], ![0, 2, -1, -1], ![1, -1, 2, -2]]

def pivotPermutation1205 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1205 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![-2, 2, -2, 2], ![3, -1, 1, -3]]

def pivotPermutation1206 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1206 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, 0, -2, 3], ![0, -1, 2, -1], ![1, 0, 1, -2]]

def pivotPermutation1207 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1207 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, 1, -2]]

def pivotPermutation1208 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1208 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![-2, 2, -1, 1], ![3, -1, -1, -1]]

def pivotPermutation1209 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1209 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![-2, 2, 1, -1], ![3, -1, -3, 1]]

def pivotPermutation1210 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1210 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![-2, 3, -2, 1], ![3, -2, 1, -2]]

def pivotPermutation1211 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1211 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, 0, -2, 3], ![0, -1, 3, -2], ![1, 0, 0, -1]]

def pivotPermutation1212 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1212 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, 0, -2, 3], ![0, -1, 3, -2], ![1, 0, -1, 0]]

def pivotPermutation1213 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1213 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![-2, 3, 1, -2], ![3, -2, -2, 1]]

def pivotPermutation1214 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1214 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, 0, -2, 3], ![0, -1, 3, -2], ![0, 2, -1, -1]]

def pivotPermutation1215 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1215 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![-2, 3, 0, -1], ![3, -2, -2, 1]]

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

def pivotMatrix1216 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, -2, 3], ![0, 1, 1, -2], ![1, -1, 2, -2]]

def pivotPermutation1217 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1217 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, -2, 3], ![0, 1, 2, -3], ![1, -1, 1, -1]]

def pivotPermutation1218 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1218 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 0, -2, 3], ![0, 1, -2, 1], ![1, -1, 3, -3]]

def pivotPermutation1219 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1219 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![-2, 2, -2, 2], ![3, -2, 1, -2]]

def pivotPermutation1220 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1220 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, 0, -2, 3], ![0, 0, 2, -2], ![1, -1, 1, -1]]

def pivotPermutation1221 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1221 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, 0, -2, 3], ![0, 0, 2, -2], ![1, -1, 0, 0]]

def pivotPermutation1222 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1222 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![-2, 2, 1, -1], ![3, -2, -2, 1]]

def pivotPermutation1223 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1223 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![-2, 2, -1, 1], ![3, -2, -1, 0]]

def pivotPermutation1224 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1224 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![-2, 3, -2, 1], ![3, -3, 1, -1]]

def pivotPermutation1225 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1225 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, 0, -2, 3], ![0, 0, 3, -3], ![1, -1, 0, 0]]

def pivotPermutation1226 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1226 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![-2, 3, -1, 0], ![3, -3, -1, 1]]

def pivotPermutation1227 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1227 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, 0, -2, 3], ![0, 0, 4, -4], ![0, 1, -2, 1]]

def pivotPermutation1228 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1228 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, 0, -2, 3], ![0, 0, 4, -4], ![1, -1, -1, 1]]

def pivotPermutation1229 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1229 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![-2, 4, -2, 0], ![3, -4, 0, 1]]

def pivotPermutation1230 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1230 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![-2, -2, 3, 1], ![3, 1, -4, 0]]

def pivotPermutation1231 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1231 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, 0, -2, 3], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def pivotPermutation1232 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1232 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, 0, -2, 3], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def pivotPermutation1233 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1233 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![-1, 0, 3, -2], ![2, 2, -5, 1]]

def pivotPermutation1234 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1234 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![-1, 1, 2, -2], ![2, 1, -4, 1]]

def pivotPermutation1235 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1235 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![-1, 2, 1, -2], ![2, 0, -3, 1]]

def pivotPermutation1236 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1236 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![-1, -2, 2, 1], ![2, 3, -4, -1]]

def pivotPermutation1237 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1237 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![-1, -1, 1, 1], ![2, 2, -2, -2]]

def pivotPermutation1238 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1238 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![-1, -1, -2, 4], ![2, 2, 0, -4]]

def pivotPermutation1239 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1239 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![-1, -1, -1, 3], ![2, 2, -1, -3]]

def pivotPermutation1240 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1240 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![-1, -1, 3, -1], ![2, 2, -5, 1]]

def pivotPermutation1241 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1241 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def pivotPermutation1242 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1242 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -1, 2], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def pivotPermutation1243 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1243 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -1, 2], ![0, 2, 2, -4], ![1, -1, -2, 2]]

def pivotPermutation1244 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1244 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![-1, 2, -2, 1], ![2, -1, 1, -2]]

def pivotPermutation1245 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1245 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, 0, -1, 2], ![0, -1, 2, -1], ![1, 0, 0, -1]]

def pivotPermutation1246 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1246 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, 0, -1, 2], ![0, -1, 2, -1], ![1, 0, -1, 0]]

def pivotPermutation1247 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1247 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![-1, 2, 1, -2], ![2, -1, -2, 1]]

def pivotPermutation1248 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1248 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![-1, 2, 1, -2], ![2, -1, -3, 2]]

def pivotPermutation1249 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1249 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![-1, 3, -1, -1], ![2, -2, -1, 1]]

def pivotPermutation1250 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1250 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![-1, 3, 0, -2], ![2, -2, -2, 2]]

def pivotPermutation1251 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1251 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![-1, 4, -1, -2], ![2, -3, -1, 2]]

def pivotPermutation1252 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1252 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, 0, -1, 2], ![0, 0, -2, 2], ![1, -1, 3, -3]]

def pivotPermutation1253 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1253 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![-1, -2, 1, 2], ![2, 2, -2, -2]]

def pivotPermutation1254 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1254 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![-1, -2, -1, 4], ![2, 2, -1, -3]]

def pivotPermutation1255 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1255 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![-1, -2, 0, 3], ![2, 2, -2, -2]]

def pivotPermutation1256 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1256 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![-1, -2, 1, 2], ![2, 2, -3, -1]]

def pivotPermutation1257 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1257 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![-1, -2, 2, 1], ![2, 2, -4, 0]]

def pivotPermutation1258 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1258 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![-1, -2, 3, 0], ![2, 2, -5, 1]]

def pivotPermutation1259 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1259 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, -1, 2], ![0, 1, 0, -1], ![1, -1, 2, -2]]

def pivotPermutation1260 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1260 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, -1, 2], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def pivotPermutation1261 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1261 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 0, -1, 2], ![0, 1, -2, 1], ![1, -1, 2, -2]]

def pivotPermutation1262 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1262 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![1, -1, 1, -1]]

def pivotPermutation1263 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1263 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![-1, 2, -2, 1], ![2, -2, 1, -1]]

def pivotPermutation1264 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1264 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, 0, -1, 2], ![0, 0, 2, -2], ![1, -1, 0, 0]]

def pivotPermutation1265 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1265 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, 0, -1, 2], ![0, 0, 2, -2], ![1, -1, -1, 1]]

def pivotPermutation1266 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1266 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![-1, 2, 1, -2], ![2, -2, -3, 3]]

def pivotPermutation1267 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1267 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 1, -2, 1]]

def pivotPermutation1268 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1268 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, 0, -1, 2], ![0, 0, 3, -3], ![1, -1, -1, 1]]

def pivotPermutation1269 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1269 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![-1, 3, -2, 0], ![2, -3, 0, 1]]

def pivotPermutation1270 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1270 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![-1, 3, -1, -1], ![2, -3, -1, 2]]

def pivotPermutation1271 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1271 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![-1, 3, 0, -2], ![2, -3, -2, 3]]

def pivotPermutation1272 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1272 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![-1, 4, -2, -1], ![2, -4, 1, 1]]

def pivotPermutation1273 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1273 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![-1, 4, -3, 0], ![2, -4, 1, 1]]

def pivotPermutation1274 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1274 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![-1, -3, 1, 3], ![2, 2, -2, -2]]

def pivotPermutation1275 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1275 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![-1, -3, 3, 1], ![2, 2, -4, 0]]

def pivotPermutation1276 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1276 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![-1, -2, 1, 2], ![2, 1, -2, -1]]

def pivotPermutation1277 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1277 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![-1, -2, 2, 1], ![2, 1, -3, 0]]

def pivotPermutation1278 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1278 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![-1, -2, 3, 0], ![2, 1, -4, 1]]

def pivotPermutation1279 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1279 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![-1, 1, 2, -2], ![2, -2, -3, 3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotPermutation1280 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1280 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def pivotPermutation1281 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1281 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def pivotPermutation1282 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1282 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, -1, -3, 3]]

def pivotPermutation1283 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1283 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, -2, 2]]

def pivotPermutation1284 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1284 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 2, -2]]

def pivotPermutation1285 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1285 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -2, -2, 3]]

def pivotPermutation1286 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1286 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, -3, 2], ![0, 1, 1, -2], ![1, -2, 2, -1]]

def pivotPermutation1287 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1287 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

def pivotPermutation1288 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1288 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

def pivotPermutation1290 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1290 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0]]

def pivotPermutation1291 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1291 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def pivotPermutation1292 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1292 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def pivotPermutation1293 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1293 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

def pivotPermutation1294 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1294 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def pivotPermutation1295 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1295 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, -1, 3], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def pivotPermutation1296 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1296 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, 0, 2], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def pivotPermutation1297 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1297 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, 0, 2], ![0, 2, 2, -4], ![1, 0, -3, 2]]

def pivotPermutation1298 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1298 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -2, 3], ![0, 2, 2, -4], ![1, -1, -1, 1]]

def pivotPermutation1299 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1299 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -1, 2], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def pivotPermutation1300 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1300 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -3, 3], ![0, 2, 2, -4], ![1, -2, 0, 1]]

def pivotPermutation1301 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1301 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -2, 0, 1]]

def pivotPermutation1302 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1302 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -2, -1, 2]]

def pivotPermutation1303 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1303 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![2, -1, 1, -2], ![-1, 3, -3, 1]]

def pivotPermutation1304 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1304 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![2, 0, 0, -2], ![-1, 2, -2, 1]]

def pivotPermutation1305 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1305 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![2, 0, 1, -3], ![-1, 2, -3, 2]]

def pivotPermutation1306 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1306 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![2, -3, 0, 1], ![-1, 4, -2, -1]]

def pivotPermutation1307 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1307 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, 0, 2, -1], ![0, -1, -3, 4], ![0, 2, 1, -3]]

def pivotPermutation1308 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1308 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![2, -2, 1, -1], ![-1, 3, -3, 1]]

def pivotPermutation1309 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1309 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![2, -1, 0, -1], ![-1, 2, -2, 1]]

def pivotPermutation1310 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1310 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![2, -1, 1, -2], ![-1, 2, -3, 2]]

def pivotPermutation1311 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1311 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def pivotPermutation1312 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1312 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![0, 2, 1, -3], ![1, -1, -3, 3]]

def pivotPermutation1313 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1313 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![2, -3, 1, 0], ![-1, 3, -3, 1]]

def pivotPermutation1314 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1314 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![2, -2, 0, 0], ![-1, 2, -2, 1]]

def pivotPermutation1315 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1315 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![2, -2, 1, -1], ![-1, 2, -3, 2]]

def pivotPermutation1316 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1316 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![0, 2, 0, -2], ![1, -2, -1, 2]]

def pivotPermutation1317 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1317 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![0, 2, 1, -3], ![1, -2, -2, 3]]

def pivotPermutation1318 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1318 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![3, -2, 0, -1], ![-2, 3, -2, 1]]

def pivotPermutation1319 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1319 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![3, -1, 0, -2], ![-2, 2, -2, 2]]

def pivotPermutation1320 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1320 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 3, -2], ![0, 2, 0, -2], ![1, -1, -3, 3]]

def pivotPermutation1321 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1321 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![3, -3, 0, 0], ![-2, 3, -2, 1]]

def pivotPermutation1322 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1322 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![3, -2, 0, -1], ![-2, 2, -2, 2]]

def pivotPermutation1323 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1323 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def pivotPermutation1324 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1324 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, -1, 1, -1], ![-4, 2, 1, 1], ![4, -1, -2, -1]]

def pivotMatrix1325 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-4, 2, 1, 1], ![4, -2, -2, 0]]

def pivotMatrix1326 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, -3, 3], ![0, 1, 1, -2], ![1, -1, 2, -2]]

def pivotMatrix1327 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, -1, 1, -1], ![-3, 3, 1, -1], ![3, -2, -2, 1]]

def pivotMatrix1328 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, -3, 3], ![0, 0, 2, -2], ![1, -1, 2, -2]]

def pivotMatrix1329 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-3, 2, 1, 0], ![3, -2, -2, 1]]

def pivotMatrix1331 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, -1, 1, -1], ![-2, -1, 1, 2], ![2, 2, -2, -2]]

def pivotMatrix1332 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, -1, 1, -1], ![-2, -1, 2, 1], ![2, 2, -3, -1]]

def pivotMatrix1333 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, -1, 1, -1], ![-2, 2, 1, -1], ![2, -1, -2, 1]]

def pivotMatrix1334 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, 1, -2, 2], ![0, -1, 3, -2], ![1, -1, -1, 1]]

def pivotMatrix1335 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, -2, 2], ![0, 0, 2, -2], ![1, -1, 1, -1]]

def pivotMatrix1336 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, -2, 2], ![0, 1, 1, -2], ![1, -2, 2, -1]]

def pivotMatrix1337 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, 1, -2, 2], ![0, 0, 3, -3], ![1, -2, -1, 2]]

def pivotMatrix1338 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-2, 4, -2, 0], ![2, -4, 1, 1]]

def pivotMatrix1339 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, -1, 1, -1], ![-1, -2, 2, 1], ![1, 3, -3, -1]]

def pivotMatrix1340 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, 1, -1, 1], ![0, -1, -2, 3], ![0, 1, 3, -4]]

def pivotMatrix1341 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, -1, 1, -1], ![-1, -1, 3, -1], ![1, 2, -4, 1]]

def pivotMatrix1342 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-1, -3, 1, 3], ![1, 3, -2, -2]]

def pivotMatrix1343 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-1, -3, 3, 1], ![1, 3, -4, 0]]

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

def pivotMatrix320 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

def pivotMatrix321 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def pivotMatrix322 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def pivotMatrix323 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def pivotMatrix324 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix325 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]

def pivotMatrix326 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]

def pivotMatrix327 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 0, 3], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]

def pivotMatrix328 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![2, 1, -3]]

def pivotMatrix330 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![2, 0, -2]]

def pivotMatrix331 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

def pivotMatrix332 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-3, 0, 3], ![0, -2, 2], ![1, 1, -2], ![1, 2, -3]]

def pivotMatrix333 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]

def pivotMatrix334 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]

def pivotMatrix335 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]

def pivotMatrix336 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix1344 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 0, -1], ![-1, -2, 2, 1], ![1, 2, -2, -1]]

def pivotMatrix1345 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 0, 3, -3]]

def pivotMatrix1346 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-1, -2, 1, 2], ![1, 2, -2, -1]]

def pivotMatrix1347 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-1, -2, 2, 1], ![1, 2, -3, 0]]

def pivotMatrix1348 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-1, -2, 3, 0], ![1, 2, -4, 1]]

def pivotMatrix1349 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1]]

def pivotMatrix1350 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, -1, 1], ![0, 0, 3, -3], ![1, -1, -1, 1]]

def pivotMatrix1351 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-1, 2, 1, -2], ![1, -2, -2, 3]]

def pivotMatrix1352 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-1, 3, -2, 0], ![1, -3, 1, 1]]

def pivotMatrix1353 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-1, 4, -3, 0], ![1, -4, 2, 1]]

def pivotMatrix1354 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, -1, -2, 3], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def pivotMatrix1355 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -3, 3], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def pivotMatrix1356 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -3, 3], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def pivotMatrix1357 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, -1, 0, 0]]

def pivotMatrix1358 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, -2, 2, -1], ![1, 1, 1, -3], ![-1, 1, -3, 3]]

def pivotMatrix1359 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, -1, 1, -1], ![1, -2, 2, -1], ![-1, 3, -3, 1]]

def pivotMatrix1360 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, -1, 1, -1], ![1, -1, 1, -1], ![-1, 2, -2, 1]]

def pivotMatrix1361 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, -1, 1, -1], ![1, -1, 2, -2], ![-1, 2, -3, 2]]

def pivotMatrix1362 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, 1, -1], ![0, 1, 1, -2], ![1, -1, -2, 2]]

def pivotMatrix1363 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, 1, -1], ![0, 1, 2, -3], ![1, -1, -3, 3]]

def pivotMatrix1364 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, -1, 2, -2], ![1, 2, 0, -3], ![-1, -1, -2, 4]]

def pivotMatrix1365 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![1, -3, 2, 0], ![-1, 3, -3, 1]]

def pivotMatrix1366 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![1, -2, 2, -1], ![-1, 2, -3, 2]]

def pivotMatrix1367 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 1, -1], ![0, 1, 2, -3], ![1, -2, -2, 3]]

def pivotMatrix1368 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, -1, 1, -1], ![2, -1, 1, -2], ![-2, 2, -2, 2]]

def pivotMatrix1369 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![2, -3, 1, 0], ![-2, 3, -2, 1]]

def pivotMatrix1370 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![2, -2, 1, -1], ![-2, 2, -2, 2]]

def pivotMatrix1371 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 2, -2], ![0, 1, 1, -2], ![1, -2, -2, 3]]

def pivotMatrix1372 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 1, 1, -3], ![2, -2, 1, -1], ![-2, 1, -2, 3]]

def pivotMatrix1373 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![2, 0, 0, -2], ![-1, -3, 4, 0], ![0, 3, -4, 1]]

def pivotMatrix1374 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![2, 0, 0, -2], ![-1, -2, 3, 0], ![0, 2, -3, 1]]

def pivotMatrix1375 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![2, 0, 0, -2], ![0, -3, 3, 0], ![-1, 3, -3, 1]]

def pivotMatrix1376 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![2, 0, 0, -2], ![0, -2, 3, -1], ![-1, 2, -3, 2]]

def pivotMatrix1377 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![2, 0, 0, -2], ![1, -2, 2, -1], ![-2, 2, -2, 2]]

def pivotMatrix1378 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 2, 1, -2], ![0, 0, 2, -2], ![1, -2, -2, 3]]

def pivotMatrix1379 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

def pivotMatrix1380 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def pivotMatrix1381 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def pivotMatrix1382 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix1383 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

def pivotMatrix1384 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

def pivotMatrix1385 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix1386 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]

def pivotMatrix1387 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

def pivotMatrix1388 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]

def pivotMatrix1389 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

def pivotMatrix1390 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

def pivotMatrix1391 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix1392 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

def pivotMatrix1393 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]

def pivotMatrix1394 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

def pivotMatrix1395 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

def pivotMatrix1396 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -1, 0], ![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def pivotMatrix1397 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -1, 0], ![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix1398 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]

def pivotMatrix1399 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]

def pivotMatrix1400 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]

def pivotMatrix1401 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

def pivotMatrix1402 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]

def pivotMatrix1403 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]

def pivotMatrix1404 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]

def pivotMatrix1405 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

def pivotMatrix1406 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

def pivotMatrix1407 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix1408 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]

def pivotMatrix1409 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]

def pivotMatrix1410 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]

def pivotMatrix1411 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]

def pivotMatrix1412 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix1413 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix1414 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]

def pivotMatrix1415 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]

def pivotMatrix1416 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]

def pivotMatrix1417 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

def pivotMatrix1418 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def pivotMatrix1419 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def pivotMatrix1420 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -1, 0], ![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix1421 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]

def pivotMatrix1422 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

def pivotMatrix1423 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]

def pivotMatrix1424 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]

def pivotMatrix1425 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

def pivotMatrix1426 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]

def pivotMatrix1427 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

def pivotMatrix1428 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]

def pivotMatrix1429 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

def pivotMatrix1430 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

def pivotMatrix1431 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix1432 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix1433 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix1434 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix1435 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]

def pivotMatrix1436 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def pivotMatrix1437 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def pivotMatrix1438 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix1439 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, 0, -3]]

def pivotMatrix1440 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -1, -2]]

def pivotMatrix1441 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, -1, 5], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 1, -3]]

def pivotMatrix1442 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, -1, 5], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def pivotMatrix1443 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, -1, 5], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 1, -3]]

def pivotMatrix1444 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, -1, 5], ![0, 1, -1, 0], ![1, 0, 1, -2], ![1, 1, 0, -2]]

def pivotMatrix1445 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, -1, 5], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def pivotMatrix1446 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def pivotMatrix1447 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, -1, 5], ![0, 0, 2, -2], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def pivotMatrix1448 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def pivotMatrix1449 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -2, -1, 5], ![0, 0, 2, -2], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def pivotMatrix1450 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, -1, 5], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 2, -3]]

def pivotMatrix1451 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, -1, 5], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 0, 1, -2]]

def pivotMatrix1452 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, -1, 5], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def pivotMatrix1453 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, -1, 5], ![0, 1, 2, -3], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def pivotMatrix1454 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, 1, -1, -2]]

def pivotMatrix1455 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, 0, 0, -2]]

def pivotMatrix1456 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 0, 4], ![0, 1, 0, -1], ![1, 0, 2, -3], ![1, 1, -1, -1]]

def pivotMatrix1457 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -2, 1], ![2, 1, 0, -3]]

def pivotMatrix1458 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, -1, -2]]

def pivotMatrix1459 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def pivotMatrix1460 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, 0, 0, -2]]

def pivotMatrix1461 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def pivotMatrix1462 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 0, 1, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def pivotMatrix1463 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, 0, 1, -3]]

def pivotMatrix1464 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def pivotMatrix1465 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 1, 1, -3]]

def pivotMatrix1466 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 1, -2, 1], ![1, 0, 1, -2], ![1, 1, 0, -2]]

def pivotMatrix1467 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 1, -3]]

def pivotMatrix1468 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def pivotMatrix1469 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def pivotMatrix1470 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 1, -1, 0], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def pivotMatrix1471 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix1472 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -2, 0]]

def pivotMatrix1473 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, 0, 0, -2]]

def pivotMatrix1474 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def pivotMatrix1475 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def pivotMatrix1476 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def pivotMatrix1477 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def pivotMatrix1478 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def pivotMatrix1479 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def pivotMatrix1480 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def pivotMatrix1481 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -2, 0, 4], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def pivotMatrix1482 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -2, 0, 4], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def pivotMatrix1483 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, 0, 4], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def pivotMatrix1484 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, 0, 4], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 2, -3]]

def pivotMatrix1485 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, 0, 4], ![0, 1, -1, 0], ![1, 0, 1, -2], ![1, 0, 1, -2]]

def pivotMatrix1486 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, 0, 4], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 2, -3]]

def pivotMatrix1487 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, 0, 4], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def pivotMatrix1488 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 1, 3], ![0, 0, -2, 2], ![0, 1, 0, -1], ![2, 1, 0, -3]]

def pivotMatrix1489 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -2, 1, 3], ![0, 0, -2, 2], ![0, 1, 0, -1], ![2, 0, 1, -3]]

def pivotMatrix1490 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -2, 1, 3], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def pivotMatrix1491 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, 1, -3]]

def pivotMatrix1492 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, 0, -3]]

def pivotMatrix1493 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -1, -2]]

def pivotMatrix1494 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 2, -4]]

def pivotMatrix1495 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 1, -3]]

def pivotMatrix1496 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def pivotMatrix1497 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 1, 3], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def pivotMatrix1498 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 1, 3], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 1, -3]]

def pivotMatrix1499 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 1, 3], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def pivotMatrix1500 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 1, 3], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def pivotMatrix1501 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 1, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def pivotMatrix1502 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 1, 3], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def pivotMatrix1503 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def pivotMatrix1504 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def pivotMatrix1505 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 1, 3], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def pivotMatrix1506 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 1, 3], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def pivotMatrix1507 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 1, 3], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def pivotMatrix1508 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 1, 3], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def pivotMatrix1509 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, 1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, 0, -1, -1]]

def pivotMatrix1510 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -2, 1, 3], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def pivotMatrix1511 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -2, 1, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def pivotMatrix1512 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, 1, 3], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def pivotMatrix1513 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, 1, 3], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def pivotMatrix1514 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def pivotMatrix1515 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def pivotMatrix1516 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -2, 2, 2], ![0, 0, -2, 2], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def pivotMatrix1517 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, 0, -2]]

def pivotMatrix1518 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 2, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def pivotMatrix1519 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 2, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def pivotMatrix1520 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 2, 2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def pivotMatrix1521 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def pivotMatrix1522 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 2, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

def pivotMatrix1523 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -2, 2, 2], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def pivotMatrix1524 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, 2, 2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def pivotMatrix1525 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, 2, 2], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def pivotMatrix1526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

def pivotMatrix1527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

def pivotMatrix1528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def pivotMatrix1529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

def pivotMatrix1530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def pivotMatrix1531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -2, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def pivotMatrix1532 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

def pivotMatrix1533 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -2, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

def pivotMatrix1534 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -1, 0], ![-2, -2, 4], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix1535 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -2, 4], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix1536 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def pivotMatrix1537 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def pivotMatrix1538 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def pivotMatrix1539 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix1540 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -2, 4], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix1541 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def pivotMatrix1542 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix1543 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

def pivotMatrix1544 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, -1, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, 1, -3]]

def pivotMatrix1545 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, -1, 4], ![0, 1, 0, -1], ![1, 0, 2, -3], ![1, 1, -1, -1]]

def pivotMatrix1546 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, -1, 4], ![0, 1, 2, -3], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def pivotMatrix1547 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, -1, 4], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 2, -3]]

def pivotMatrix1548 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -1, -2]]

def pivotMatrix1549 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def pivotMatrix1550 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def pivotMatrix1551 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, 0, -3]]

def pivotMatrix1552 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -1, -2]]

def pivotMatrix1553 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def pivotMatrix1554 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def pivotMatrix1555 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def pivotMatrix1556 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 1, -1, 0], ![1, 0, 1, -2], ![1, 1, 0, -2]]

def pivotMatrix1557 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def pivotMatrix1558 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def pivotMatrix1559 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def pivotMatrix1560 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def pivotMatrix1561 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def pivotMatrix1562 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def pivotMatrix1563 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def pivotMatrix1564 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, -1, 0], ![2, 1, -1, -2]]

def pivotMatrix1565 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def pivotMatrix1566 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, -2, 0], ![2, 0, 0, -2]]

def pivotMatrix1567 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def pivotMatrix1568 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -2, 0]]

def pivotMatrix1569 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 0, -1, 0], ![1, 2, -1, -2]]

def pivotMatrix1570 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 0, 0, -1], ![1, 2, -2, -1]]

def pivotMatrix1571 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def pivotMatrix1572 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def pivotMatrix1573 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def pivotMatrix1574 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

def pivotMatrix1575 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def pivotMatrix1576 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def pivotMatrix1577 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 0, 1, -2], ![1, 1, -2, 0]]

def pivotMatrix1578 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def pivotMatrix1579 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def pivotMatrix1580 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def pivotMatrix1581 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def pivotMatrix1582 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, -1, 1, -2]]

def pivotMatrix1583 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, -1, -1, 0]]

def pivotMatrix1584 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 2, 0, -3]]

def pivotMatrix1585 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 2, -1, -2]]

def pivotMatrix1586 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 2, -2, -1]]

def pivotMatrix1587 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![2, -1, 0, -1]]

def pivotMatrix1588 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 2, -2, -1]]

def pivotMatrix1589 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 2, -3]]

def pivotMatrix1590 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, -1, -1, 0]]

def pivotMatrix1591 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def pivotMatrix1592 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def pivotMatrix1593 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 1, -2, 0]]

def pivotMatrix1594 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def pivotMatrix1595 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def pivotMatrix1596 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def pivotMatrix1597 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def pivotMatrix1598 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def pivotMatrix1599 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix1600 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 2, -2, 0], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def pivotMatrix1601 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 2, -1, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def pivotMatrix1602 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def pivotMatrix1603 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def pivotMatrix1604 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 2, 1, -3], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def pivotMatrix1605 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 2, 1, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def pivotMatrix1606 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def pivotMatrix1607 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, -1, 4], ![0, 0, 2, -2], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def pivotMatrix1608 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def pivotMatrix1609 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def pivotMatrix1610 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 1, -1]]

def pivotMatrix1611 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def pivotMatrix1612 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def pivotMatrix1613 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def pivotMatrix1614 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, -1, 4], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def pivotMatrix1615 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, -1, 4], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 2, -3]]

def pivotMatrix1616 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, -1, 4], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def pivotMatrix1617 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, -1, 4], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def pivotMatrix1618 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, -1, -1, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def pivotMatrix1619 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, -1, -1, 2], ![0, 1, 1, -2], ![2, 1, -1, -2]]

def pivotMatrix1620 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, -1, -1, 2], ![0, 0, 2, -2], ![2, 1, 0, -3]]

def pivotMatrix1621 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, -1, -1, 2], ![0, 1, 2, -3], ![2, 0, 0, -2]]

def pivotMatrix1622 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -1, 0, 3], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, 1, -1, -1]]

def pivotMatrix1623 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, 0, -1, -1]]

def pivotMatrix1624 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![1, 0, 2, -3], ![1, 1, -1, -1]]

def pivotMatrix1625 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 0, 3], ![0, 1, 2, -3], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def pivotMatrix1626 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 0, 3], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 2, -3]]

def pivotMatrix1627 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, 1, -2], ![2, 1, -1, -2]]

def pivotMatrix1628 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 2, 1, -3], ![2, 0, -1, -1]]

def pivotMatrix1629 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![2, 1, 0, -3]]

def pivotMatrix1630 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, -1, -2]]

def pivotMatrix1631 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def pivotMatrix1632 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, 0, 0, -2]]

def pivotMatrix1633 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, 0, -2, 0]]

def pivotMatrix1634 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, -1, -2]]

def pivotMatrix1635 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -2, -1]]

def pivotMatrix1636 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def pivotMatrix1637 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def pivotMatrix1638 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

def pivotMatrix1639 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -2, 0]]

def pivotMatrix1640 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def pivotMatrix1641 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def pivotMatrix1642 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def pivotMatrix1643 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def pivotMatrix1644 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def pivotMatrix1645 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def pivotMatrix1646 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def pivotMatrix1647 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def pivotMatrix1648 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def pivotMatrix1649 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def pivotMatrix1650 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def pivotMatrix1651 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 0, -2, 1], ![1, 1, 0, -2]]

def pivotMatrix1652 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def pivotMatrix1653 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def pivotMatrix1654 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def pivotMatrix1655 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def pivotMatrix1656 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def pivotMatrix1657 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def pivotMatrix1658 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 0, -2, 2], ![1, -1, 1, -1], ![1, 2, 0, -3]]

def pivotMatrix1659 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 2, 0, -3]]

def pivotMatrix1660 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, -1, 1, -2]]

def pivotMatrix1661 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 0, 3], ![0, 0, -2, 2], ![1, -1, 2, -2], ![1, 1, 0, -2]]

def pivotMatrix1662 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -1, 2, -2]]

def pivotMatrix1663 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -1, 1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix1664 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 2, 1, -3], ![2, -1, 1, -2]]

def pivotMatrix1665 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 2, -1, -2]]

def pivotMatrix1666 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 2, -1, -2]]

def pivotMatrix1667 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 3, -4]]

def pivotMatrix1668 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, -1, 0, -1]]

def pivotMatrix1669 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 0, 3], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def pivotMatrix1670 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 0, 3], ![0, 2, 0, -2], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def pivotMatrix1671 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 0, 3], ![0, 2, 1, -3], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def pivotMatrix1672 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, -1, 0, -1]]

def pivotMatrix1673 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 2, -1, -2]]

def pivotMatrix1674 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 2, -2, -1]]

def pivotMatrix1675 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -1, 2, -3]]

def pivotMatrix1676 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -1, 1, -2]]

def pivotMatrix1677 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def pivotMatrix1678 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def pivotMatrix1679 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def pivotMatrix1680 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def pivotMatrix1681 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -1, -1, 0]]

def pivotMatrix1682 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def pivotMatrix1683 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def pivotMatrix1684 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, -1, -2, 1]]

def pivotMatrix1685 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def pivotMatrix1686 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def pivotMatrix1687 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def pivotMatrix1688 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def pivotMatrix1689 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def pivotMatrix1690 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def pivotMatrix1691 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, -2, 1]]

def pivotMatrix1692 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, -1, 1, -2]]

def pivotMatrix1693 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, -1, 0, -1]]

def pivotMatrix1694 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def pivotMatrix1695 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def pivotMatrix1696 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def pivotMatrix1697 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def pivotMatrix1698 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def pivotMatrix1699 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -1, -2, 1]]

def pivotMatrix1700 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def pivotMatrix1701 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def pivotMatrix1702 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def pivotMatrix1703 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def pivotMatrix1704 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def pivotMatrix1705 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def pivotMatrix1706 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def pivotMatrix1707 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def pivotMatrix1708 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 0, 2, -3]]

def pivotMatrix1709 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def pivotMatrix1710 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def pivotMatrix1711 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def pivotMatrix1712 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 1, -1]]

def pivotMatrix1713 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def pivotMatrix1714 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 3, -4]]

def pivotMatrix1715 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def pivotMatrix1716 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def pivotMatrix1717 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def pivotMatrix1718 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def pivotMatrix1719 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def pivotMatrix1720 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def pivotMatrix1721 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 0, -2, 1]]

def pivotMatrix1722 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def pivotMatrix1723 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def pivotMatrix1724 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 0, 3], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -2, 1]]

def pivotMatrix1725 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![2, 0, 2, -4]]

def pivotMatrix1726 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def pivotMatrix1727 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 0, -1, 0], ![1, 1, 2, -4]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix1728 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 0, 0, -1], ![1, 1, 1, -3]]

def pivotMatrix1729 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def pivotMatrix1730 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def pivotMatrix1731 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def pivotMatrix1732 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def pivotMatrix1733 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def pivotMatrix1734 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def pivotMatrix1735 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def pivotMatrix1736 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 0, -1, 1], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def pivotMatrix1737 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def pivotMatrix1738 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -2, -1]]

def pivotMatrix1739 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def pivotMatrix1740 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def pivotMatrix1741 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def pivotMatrix1742 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def pivotMatrix1743 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def pivotMatrix1744 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def pivotMatrix1745 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def pivotMatrix1746 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def pivotMatrix1747 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def pivotMatrix1748 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def pivotMatrix1749 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def pivotMatrix1750 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def pivotMatrix1751 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def pivotMatrix1752 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def pivotMatrix1753 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 2, 0, -2], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def pivotMatrix1754 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 1, 2], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def pivotMatrix1755 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 1, 2], ![0, 0, -2, 2], ![1, -1, 1, -1], ![1, 1, 1, -3]]

def pivotMatrix1756 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![2, -1, 1, -2]]

def pivotMatrix1757 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def pivotMatrix1758 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 1, 2], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def pivotMatrix1759 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 1, 2], ![0, 0, -2, 2], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def pivotMatrix1760 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def pivotMatrix1761 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def pivotMatrix1762 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -1, 1, -1]]

def pivotMatrix1763 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def pivotMatrix1764 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def pivotMatrix1765 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 2, -3]]

def pivotMatrix1766 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def pivotMatrix1767 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def pivotMatrix1768 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def pivotMatrix1769 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, -1, -1, 0]]

def pivotMatrix1770 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def pivotMatrix1771 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def pivotMatrix1772 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def pivotMatrix1773 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def pivotMatrix1774 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def pivotMatrix1775 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def pivotMatrix1776 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def pivotMatrix1777 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 2, 2, -4], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def pivotMatrix1778 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 2, 2, -4], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def pivotMatrix1779 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, -3, 2], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def pivotMatrix1780 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def pivotMatrix1781 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def pivotMatrix1782 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, -1, 0]]

def pivotMatrix1783 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, -2, 1], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def pivotMatrix1784 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def pivotMatrix1785 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def pivotMatrix1786 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def pivotMatrix1787 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -1, -2, 1]]

def pivotMatrix1788 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![1, -1, -2, 2], ![1, 1, 1, -3]]

def pivotMatrix1789 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def pivotMatrix1790 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def pivotMatrix1791 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -2, 1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix1792 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def pivotMatrix1793 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def pivotMatrix1794 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -3, 1]]

def pivotMatrix1795 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 1, -2, 0]]

def pivotMatrix1796 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -3, 1]]

def pivotMatrix1797 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 2, -3, 1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def pivotMatrix1798 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 2, -3, 1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def pivotMatrix1799 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 2, -2, 0], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def pivotMatrix1800 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def pivotMatrix1801 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def pivotMatrix1802 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 2, 0, -2], ![1, -1, -2, 2], ![1, 0, 0, -1]]

def pivotMatrix1803 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def pivotMatrix1804 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def pivotMatrix1805 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 2, 1, -3], ![1, -1, -2, 2], ![1, 0, -1, 0]]

def pivotMatrix1806 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 2, 1, -3], ![1, -1, -1, 1], ![1, 0, -2, 1]]

def pivotMatrix1807 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 2, 1, -3], ![1, -1, 0, 0], ![1, 0, -3, 2]]

def pivotMatrix1808 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, -1, 0, -1]]

def pivotMatrix1809 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, -1, -1, 0]]

def pivotMatrix1810 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -1, -2, 1]]

def pivotMatrix1811 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 1, 2], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def pivotMatrix1812 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 1, 2], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 1, -2, 0]]

def pivotMatrix1813 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 1, 2], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, -3, 1]]

def pivotMatrix1814 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 2, -3, 1], ![1, 0, 0, -1]]

def pivotMatrix1815 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, -1, 1]]

def pivotMatrix1816 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def pivotMatrix1817 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 1, 2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def pivotMatrix1818 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 1, 2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def pivotMatrix1819 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 1, 2], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def pivotMatrix1820 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def pivotMatrix1821 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def pivotMatrix1822 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 2, -3]]

def pivotMatrix1823 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def pivotMatrix1824 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 1, 2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def pivotMatrix1825 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 1, 2], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def pivotMatrix1826 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 1, 2], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def pivotMatrix1827 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 1, 2], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def pivotMatrix1828 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 1, 2], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def pivotMatrix1829 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 1, 2], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -2, 1]]

def pivotMatrix1830 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 1, 2], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def pivotMatrix1831 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 1, 2], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def pivotMatrix1832 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![2, 0, 0, -2]]

def pivotMatrix1833 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def pivotMatrix1834 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 2, 1], ![0, -1, -1, 2], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def pivotMatrix1835 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def pivotMatrix1836 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 2, 1], ![0, -1, -1, 2], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def pivotMatrix1837 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def pivotMatrix1838 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def pivotMatrix1839 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def pivotMatrix1840 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def pivotMatrix1841 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 2, 1], ![0, 0, -1, 1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def pivotMatrix1842 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 2, 1], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def pivotMatrix1843 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def pivotMatrix1844 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 2, 1], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def pivotMatrix1845 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def pivotMatrix1846 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, -1, 0, -1]]

def pivotMatrix1847 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 2, 1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def pivotMatrix1848 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 2, 1], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def pivotMatrix1849 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

def pivotMatrix1850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]

def pivotMatrix1851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

def pivotMatrix1852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]

def pivotMatrix1853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

def pivotMatrix1854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

def pivotMatrix1855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix1856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

def pivotMatrix1857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]

def pivotMatrix1858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

def pivotMatrix1859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

def pivotMatrix1860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

def pivotMatrix1861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

def pivotMatrix1862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

def pivotMatrix1863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix1864 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]

def pivotMatrix1865 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

def pivotMatrix1866 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def pivotMatrix1867 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

def pivotMatrix1868 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix1869 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix1870 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def pivotMatrix1871 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def pivotMatrix1872 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix1873 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]

def pivotMatrix1874 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

def pivotMatrix1875 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 3, -4]]

def pivotMatrix1876 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

def pivotMatrix1877 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def pivotMatrix1878 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix1879 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix1880 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def pivotMatrix1881 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def pivotMatrix1882 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

def pivotMatrix1883 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def pivotMatrix1884 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix1885 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix1886 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, 1, -1], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def pivotMatrix1887 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def pivotMatrix1888 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]

def pivotMatrix1889 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2]]

def pivotMatrix1890 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

def pivotMatrix1891 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]

def pivotMatrix1892 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def pivotMatrix1893 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def pivotMatrix1894 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -2, 4], ![0, -2, 2, 0], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def pivotMatrix1895 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def pivotMatrix1896 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def pivotMatrix1897 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, -2, 4], ![0, -2, 2, 0], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def pivotMatrix1898 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def pivotMatrix1899 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def pivotMatrix1900 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def pivotMatrix1901 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def pivotMatrix1902 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, -2, 4], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def pivotMatrix1903 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -1, 1, -2]]

def pivotMatrix1904 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, -2, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -1, 1, -2]]

def pivotMatrix1905 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, -2, 4], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 1, -1, -1]]

def pivotMatrix1906 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def pivotMatrix1907 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def pivotMatrix1908 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, -2, 4], ![0, 2, 0, -2], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def pivotMatrix1909 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, -1, 0, -1]]

def pivotMatrix1910 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def pivotMatrix1911 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, -2, 4], ![0, -1, 2, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def pivotMatrix1912 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def pivotMatrix1913 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def pivotMatrix1914 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def pivotMatrix1915 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def pivotMatrix1916 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, -2, 4], ![0, -1, 3, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def pivotMatrix1917 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 0, -2, 4], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def pivotMatrix1918 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -2, 1, -1]]

def pivotMatrix1919 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -2, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, -2, 0, 0]]

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

def pivotMatrix1920 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -2, 4], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def pivotMatrix1921 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -2, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -2, 1, -1]]

def pivotMatrix1922 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -2, 4], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, -2, 0, 0]]

def pivotMatrix1923 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -2, 4], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 1, -1, -1]]

def pivotMatrix1924 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -2, 4], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 1, -1, -1]]

def pivotMatrix1925 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -2, 1, 0], ![1, 0, 1, -2]]

def pivotMatrix1926 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def pivotMatrix1927 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def pivotMatrix1928 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def pivotMatrix1929 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -2, 4], ![0, 2, 0, -2], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def pivotMatrix1930 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -2, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def pivotMatrix1931 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -2, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![2, -2, 0, 0]]

def pivotMatrix1932 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 0, -2, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def pivotMatrix1933 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 0, -2, 4], ![0, 0, 3, -3], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def pivotMatrix1934 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -2, 4], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def pivotMatrix1935 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -2, 4], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def pivotMatrix1936 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -2, 4], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def pivotMatrix1937 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -2, 4], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def pivotMatrix1938 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -2, 4], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def pivotMatrix1939 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -2, 4], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def pivotMatrix1940 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -1, 3], ![0, -2, 1, 1], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def pivotMatrix1941 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, -1, 3], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def pivotMatrix1942 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -1, 3], ![0, -1, 2, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def pivotMatrix1943 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def pivotMatrix1944 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, -1, 1, -1]]

def pivotMatrix1945 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def pivotMatrix1946 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -1, 3], ![0, -1, 3, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def pivotMatrix1947 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, -1, 3], ![0, -1, 3, -2], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def pivotMatrix1948 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, -1, 3], ![0, -1, 3, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def pivotMatrix1949 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def pivotMatrix1950 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def pivotMatrix1951 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, 0, -1, 0]]

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

def pivotMatrix2528 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, -1, 3], ![-1, 1, 1, -1], ![1, -1, 2, -2], ![1, 0, -2, 1]]

def pivotMatrix2529 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, -1, 3], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def pivotMatrix2530 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 1, 0, -2]]

def pivotMatrix2531 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def pivotMatrix2532 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def pivotMatrix2533 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def pivotMatrix2534 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, -1, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def pivotMatrix2535 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, -1, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def pivotMatrix2536 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, -1, 3], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def pivotMatrix2537 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def pivotMatrix2538 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def pivotMatrix2539 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def pivotMatrix2540 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def pivotMatrix2541 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def pivotMatrix2542 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def pivotMatrix2543 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def pivotMatrix2544 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def pivotMatrix2545 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def pivotMatrix2546 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, 0, -2, 1]]

def pivotMatrix2547 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def pivotMatrix2548 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, -1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 3, -3]]

def pivotMatrix2549 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, -1, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def pivotMatrix2550 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 1, -2, 0]]

def pivotMatrix2551 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def pivotMatrix2552 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 1, -1]]

def pivotMatrix2553 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def pivotMatrix2554 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def pivotMatrix2555 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def pivotMatrix2556 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def pivotMatrix2557 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -1, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 2, -2]]

def pivotMatrix2558 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 2, -2]]

def pivotMatrix2559 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -1, 3], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -1, -1, 1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix2560 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def pivotMatrix2561 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, -1, 0, 2], ![-1, 0, -1, 2], ![0, 1, 3, -4], ![1, 1, -2, 0]]

def pivotMatrix2562 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 0, 2], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 1, -3, 1]]

def pivotMatrix2563 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 0, 2], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 1, -3, 1]]

def pivotMatrix2564 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 0, 2], ![-1, 1, -2, 2], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def pivotMatrix2565 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 0, 2], ![-1, 1, -2, 2], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def pivotMatrix2566 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, 0, 2], ![-1, 1, -2, 2], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def pivotMatrix2567 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, -1, 0, 2], ![-1, 1, -2, 2], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def pivotMatrix2568 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 1, -2, 1], ![1, 0, 3, -4]]

def pivotMatrix2569 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 1, -2, 1], ![1, -1, 3, -3]]

def pivotMatrix2570 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 0, 2], ![-1, 1, -1, 1], ![1, -1, -1, 1], ![1, 0, 3, -4]]

def pivotMatrix2571 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 0, 2], ![-1, 1, -1, 1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def pivotMatrix2572 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, 0, 2], ![-1, 1, -1, 1], ![1, -1, 3, -3], ![1, 0, -2, 1]]

def pivotMatrix2573 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 1, 3, -4], ![1, 0, -2, 1]]

def pivotMatrix2574 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, 0, 2], ![0, -1, -2, 3], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def pivotMatrix2575 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, 0, 3, -4]]

def pivotMatrix2576 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def pivotMatrix2577 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def pivotMatrix2578 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def pivotMatrix2579 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def pivotMatrix2580 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def pivotMatrix2581 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 1, -1, -1]]

def pivotMatrix2582 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def pivotMatrix2583 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def pivotMatrix2584 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def pivotMatrix2585 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def pivotMatrix2586 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def pivotMatrix2587 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def pivotMatrix2588 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def pivotMatrix2589 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -1, 0, 0]]

def pivotMatrix2590 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, 0, 0, -1]]

def pivotMatrix2591 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 3, -3]]

def pivotMatrix2592 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def pivotMatrix2593 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 3, -4]]

def pivotMatrix2594 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def pivotMatrix2595 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, 1, -1]]

def pivotMatrix2596 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, 0, 0]]

def pivotMatrix2597 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def pivotMatrix2598 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def pivotMatrix2599 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def pivotMatrix2600 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def pivotMatrix2601 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def pivotMatrix2602 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 3, -3]]

def pivotMatrix2603 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def pivotMatrix2604 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 3, -3]]

def pivotMatrix2605 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def pivotMatrix2606 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def pivotMatrix2607 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def pivotMatrix2608 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, -1, 1, -1]]

def pivotMatrix2609 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def pivotMatrix2610 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def pivotMatrix2611 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -3, 1], ![1, -1, 0, 0]]

def pivotMatrix2612 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1]]

def pivotMatrix2613 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def pivotMatrix2614 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1]]

def pivotMatrix2615 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def pivotMatrix2616 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -1, 0, 0]]

def pivotMatrix2617 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, -1, 1]]

def pivotMatrix2618 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 1, 1], ![-1, -1, 1, 1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def pivotMatrix2619 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def pivotMatrix2620 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def pivotMatrix2621 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def pivotMatrix2622 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def pivotMatrix2623 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, -1, -1], ![1, 0, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix2624 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def pivotMatrix2625 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def pivotMatrix2626 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def pivotMatrix2627 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def pivotMatrix2628 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 1, -1, -1]]

def pivotMatrix2629 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 1, 1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def pivotMatrix2630 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 1, 1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def pivotMatrix2631 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 1, 1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def pivotMatrix2632 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def pivotMatrix2633 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def pivotMatrix2634 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -1, 0, 0]]

def pivotMatrix2635 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def pivotMatrix2636 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def pivotMatrix2637 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 1, -1]]

def pivotMatrix2638 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def pivotMatrix2639 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def pivotMatrix2640 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, 0, 0]]

def pivotMatrix2641 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, -1, 1]]

def pivotMatrix2642 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def pivotMatrix2643 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 1, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def pivotMatrix2644 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 1, 1], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def pivotMatrix2645 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def pivotMatrix2646 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1]]

def pivotMatrix2647 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, 1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def pivotMatrix2649 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix2650 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![-1, -1, 2], ![0, 4, -4], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix2651 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix2652 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix2653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def pivotMatrix2654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix2655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def pivotMatrix2656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def pivotMatrix2657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix2658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

def pivotMatrix2659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def pivotMatrix2660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix2661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

def pivotMatrix2662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

def pivotMatrix2663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix2666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix2667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

def pivotMatrix2668 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -1, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix2669 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix2670 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -1, 2], ![-1, 3, -2], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix2671 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix2672 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![-1, 4, -3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix2673 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 4, -4], ![1, 0, -1]]

def pivotMatrix2674 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

def pivotMatrix2675 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def pivotMatrix2676 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, 2, 0], ![0, -1, -2, 3], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def pivotMatrix2677 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, 3, -1], ![0, -1, -3, 4], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def pivotMatrix2678 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, 0, -3, 4], ![-1, 1, 1, -1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def pivotMatrix2679 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, 0, -3, 4], ![-1, 1, 1, -1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def pivotMatrix2680 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, 0, -3, 4], ![-1, 1, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def pivotMatrix2681 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 0, -3, 4], ![0, -2, 2, 0], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def pivotMatrix2682 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, 0, -3, 4], ![0, -2, 3, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def pivotMatrix2683 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def pivotMatrix2684 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def pivotMatrix2685 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def pivotMatrix2686 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def pivotMatrix2687 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, 0, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix2688 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -3, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def pivotMatrix2689 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def pivotMatrix2690 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def pivotMatrix2691 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -2, 1, 0]]

def pivotMatrix2692 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 0, -3, 4], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, 2, -1]]

def pivotMatrix2693 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 0, -3, 4], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -2, 1, 0]]

def pivotMatrix2694 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def pivotMatrix2695 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, 0, -2, 3], ![-1, 1, 3, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def pivotMatrix2696 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 0, -2, 3], ![0, -2, 2, 0], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def pivotMatrix2697 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 0, -2, 3], ![0, -2, 2, 0], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def pivotMatrix2698 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, 0, -2, 3], ![0, -2, 3, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def pivotMatrix2699 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, 0, -2, 3], ![0, -2, 3, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def pivotMatrix2700 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, -2, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def pivotMatrix2701 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def pivotMatrix2702 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def pivotMatrix2703 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def pivotMatrix2704 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -2, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def pivotMatrix2705 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -2, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def pivotMatrix2706 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -2, 3], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def pivotMatrix2707 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def pivotMatrix2708 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 0, -2, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0]]

def pivotMatrix2709 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 0, -2, 3], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -2, 1, 0]]

def pivotMatrix2710 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def pivotMatrix2711 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, 0, -1, 2], ![-1, 1, -1, 1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def pivotMatrix2712 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![-1, 0, -1, 2], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def pivotMatrix2713 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, 0, -1, 2], ![-1, 1, 3, -3], ![0, 1, -2, 1], ![1, -1, 0, 0]]

def pivotMatrix2714 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, 0, -1, 2], ![-1, 1, 3, -3], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def pivotMatrix2715 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, 0, -1, 2], ![0, -2, 0, 2], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def pivotMatrix2716 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def pivotMatrix2717 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def pivotMatrix2718 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, -1, 2], ![0, -2, 2, 0], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def pivotMatrix2719 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, 0, -1, 2], ![0, -2, 3, -1], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def pivotMatrix2720 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def pivotMatrix2721 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def pivotMatrix2722 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def pivotMatrix2723 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, -1, 1]]

def pivotMatrix2724 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def pivotMatrix2725 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def pivotMatrix2726 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def pivotMatrix2727 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1]]

def pivotMatrix2728 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, -1, 2], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def pivotMatrix2729 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -2, 3, -2]]

def pivotMatrix2730 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def pivotMatrix2731 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 3, -2]]

def pivotMatrix2732 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def pivotMatrix2733 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def pivotMatrix2734 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def pivotMatrix2735 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -2, 0, 1]]

def pivotMatrix2736 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, -2, 4], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def pivotMatrix2737 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, -1, 3], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def pivotMatrix2738 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, -1, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def pivotMatrix2739 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def pivotMatrix2740 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def pivotMatrix2741 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def pivotMatrix2742 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def pivotMatrix2743 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def pivotMatrix2744 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def pivotMatrix2745 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def pivotMatrix2746 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 3, -1], ![0, 1, -3, 2], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def pivotMatrix2747 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, -1, 2], ![0, -1, 0, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def pivotMatrix2748 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, -1, 2], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def pivotMatrix2749 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def pivotMatrix2750 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def pivotMatrix2751 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 2, 2, -4], ![1, 0, -3, 2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix2752 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def pivotMatrix2753 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, 0, -3, 2]]

def pivotMatrix2754 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, -2, 0], ![1, -1, 3, -3]]

def pivotMatrix2755 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, -1, 1]]

def pivotMatrix2756 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def pivotMatrix2757 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, -1, 2, -2]]

def pivotMatrix2758 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def pivotMatrix2759 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def pivotMatrix2760 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 2, -3, 1], ![1, -1, 1, -1]]

def pivotMatrix2761 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def pivotMatrix2762 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def pivotMatrix2763 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 3, -3], ![0, 2, -3, 1], ![1, -1, 0, 0]]

def pivotMatrix2764 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, -1, 1]]

def pivotMatrix2765 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 1, -3, 2], ![0, 1, 2, -3], ![1, -1, 1, -1]]

def pivotMatrix2766 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 1, -3, 2], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def pivotMatrix2767 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1]]

def pivotMatrix2768 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, -2, 2]]

def pivotMatrix2769 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def pivotMatrix2770 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -3, 3]]

def pivotMatrix2771 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -3, 3]]

def pivotMatrix2772 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 1, -3, 2], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def pivotMatrix2773 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 1, -3, 2], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def pivotMatrix2774 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, -1, 1]]

def pivotMatrix2775 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, -2, 2]]

def pivotMatrix2776 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -3, 3]]

def pivotMatrix2777 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![0, 1, -3, 2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def pivotMatrix2778 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def pivotMatrix2779 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 3, -2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def pivotMatrix2780 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 1, -1]]

def pivotMatrix2781 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 2, -2]]

def pivotMatrix2782 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -2, 3, -2]]

def pivotMatrix2783 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 1, -1]]

def pivotMatrix2784 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def pivotMatrix2785 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -1, 1]]

def pivotMatrix2786 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -2, -2, 3]]

def pivotMatrix2787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -3, 3], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix2788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix2789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

def pivotMatrix2790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def pivotMatrix2791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def pivotMatrix2792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]

def pivotMatrix2793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1]]

def pivotMatrix2795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix2796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix2797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def pivotMatrix2799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0]]

def pivotMatrix2800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def pivotMatrix2801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def pivotMatrix2802 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, -2, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def pivotMatrix2803 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, -1, 3], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def pivotMatrix2804 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def pivotMatrix2805 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, 0, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def pivotMatrix2806 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, 0, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -2, 1]]

def pivotMatrix2807 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def pivotMatrix2808 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -3, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def pivotMatrix2809 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -3, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def pivotMatrix2810 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -2, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def pivotMatrix2811 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -2, 3], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def pivotMatrix2812 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def pivotMatrix2813 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def pivotMatrix2814 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def pivotMatrix2815 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -3, 3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix2816 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -3, 3]]

def pivotMatrix2817 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -1, -2, 2]]

def pivotMatrix2818 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -2, 0, 1]]

def pivotMatrix2819 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -2, 0, 1]]

def pivotMatrix2820 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -2, -1, 2]]

def pivotMatrix2821 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -2, -1, 2]]

def pivotMatrix2822 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -2, -1, 2]]

def pivotMatrix2823 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

def pivotMatrix2824 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 1, 0, -1], ![1, 0, -2, 1]]

def pivotMatrix2825 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 0, 2, -1], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def pivotMatrix2826 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 2, 1, -3], ![1, 0, -3, 2]]

def pivotMatrix2827 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![0, 0, -3, 3], ![0, 2, 1, -3], ![1, -1, 0, 0]]

def pivotMatrix2828 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def pivotMatrix2829 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -3, 3]]

def pivotMatrix2830 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def pivotMatrix2831 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -1, 2]]

def pivotMatrix2832 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 0, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -3, 4]]

def pivotMatrix2833 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 1, -3, 3], ![-1, 1, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def pivotMatrix2834 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, 1, -3, 3], ![-1, 1, 1, -1], ![0, 0, 2, -2], ![1, -1, 0, 0]]

def pivotMatrix2835 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 1, -3, 3], ![-1, 1, 2, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def pivotMatrix2836 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 1, -3, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def pivotMatrix2837 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 1, -2, 2], ![-1, 1, -1, 1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def pivotMatrix2838 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 1, -2, 2], ![-1, 1, -1, 1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def pivotMatrix2839 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 2, -2], ![1, -1, 1, -1]]

def pivotMatrix2840 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 3, -3], ![1, -1, 0, 0]]

def pivotMatrix2841 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, -1, 1], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def pivotMatrix2842 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, 3, -3], ![1, -1, 0, 0]]

def pivotMatrix2843 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -2, 3, -2]]

def pivotMatrix2844 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def pivotMatrix2845 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def pivotMatrix2846 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0]]

def pivotMatrix2847 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, -1, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -2, 0, 1]]

def pivotMatrix2848 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -3, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 2, -1]]

def pivotMatrix2849 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -3, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def pivotMatrix2850 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -2, 3, -2]]

def pivotMatrix2851 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0]]

def pivotMatrix2852 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -2, 2], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -2, -1, 2]]

def pivotMatrix2853 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -2, -1, 2]]

def pivotMatrix2854 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 2, -3], ![1, -2, -2, 3]]

def pivotMatrix2855 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -2, -2, 3]]

def pivotMatrix2856 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 1, 1, -1], ![0, -1, -1, 2], ![0, 1, 0, -1], ![1, -1, -1, 1]]

def pivotMatrix2857 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def pivotMatrix2858 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 1, -1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -2, -1, 2]]

def pivotMatrix2859 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -2, -2, 3]]

def pivotMatrix2860 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 2, -3, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -2, 0, 1]]

def pivotMatrix2861 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 2, -1, 0], ![0, 0, -1, 1], ![0, 0, 3, -3], ![1, -2, 0, 1]]

def pivotMatrix2862 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 2, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -2, -3, 4]]

def pivotMatrix2863 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def pivotMatrix2864 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def pivotMatrix2865 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def pivotMatrix2866 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, -1, 5], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def pivotMatrix2867 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, -1, 5], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def pivotMatrix2868 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def pivotMatrix2869 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, 0, -3]]

def pivotMatrix2870 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def pivotMatrix2871 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def pivotMatrix2872 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def pivotMatrix2873 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def pivotMatrix2874 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def pivotMatrix2875 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def pivotMatrix2876 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def pivotMatrix2877 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def pivotMatrix2878 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def pivotMatrix2879 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix2880 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def pivotMatrix2881 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def pivotMatrix2882 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 1, 3], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def pivotMatrix2883 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, 0, -3]]

def pivotMatrix2884 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def pivotMatrix2885 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def pivotMatrix2886 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def pivotMatrix2887 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 1, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def pivotMatrix2888 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def pivotMatrix2889 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def pivotMatrix2890 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def pivotMatrix2891 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def pivotMatrix2892 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 2, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def pivotMatrix2893 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 2, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def pivotMatrix2894 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 2, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def pivotMatrix2895 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -1, -2]]

def pivotMatrix2896 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, 0, -3]]

def pivotMatrix2897 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -1, -2]]

def pivotMatrix2898 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def pivotMatrix2899 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, -1, 4], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 2, -3]]

def pivotMatrix2900 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, -1, -2]]

def pivotMatrix2901 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def pivotMatrix2902 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, 0, 0, -2]]

def pivotMatrix2903 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def pivotMatrix2904 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, 0, -2, 0]]

def pivotMatrix2905 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, -1, -2]]

def pivotMatrix2906 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -2, -1]]

def pivotMatrix2907 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def pivotMatrix2908 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def pivotMatrix2909 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def pivotMatrix2910 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def pivotMatrix2911 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def pivotMatrix2912 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

def pivotMatrix2913 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def pivotMatrix2914 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def pivotMatrix2915 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -2, 0]]

def pivotMatrix2916 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def pivotMatrix2917 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def pivotMatrix2918 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def pivotMatrix2919 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def pivotMatrix2920 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def pivotMatrix2921 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def pivotMatrix2922 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def pivotMatrix2923 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, -1, 0, -1]]

def pivotMatrix2924 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 2, -2, -1]]

def pivotMatrix2925 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def pivotMatrix2926 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def pivotMatrix2927 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def pivotMatrix2928 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def pivotMatrix2929 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def pivotMatrix2930 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def pivotMatrix2931 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def pivotMatrix2932 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def pivotMatrix2933 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def pivotMatrix2934 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def pivotMatrix2935 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def pivotMatrix2936 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def pivotMatrix2937 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def pivotMatrix2938 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def pivotMatrix2939 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, -1, -1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, 0, -3]]

def pivotMatrix2940 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, 1, -1, -2]]

def pivotMatrix2941 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, 0, 0, -2]]

def pivotMatrix2942 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def pivotMatrix2943 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, -1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix2944 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def pivotMatrix2945 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, -1, -2]]

def pivotMatrix2946 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def pivotMatrix2947 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def pivotMatrix2948 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def pivotMatrix2949 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def pivotMatrix2950 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def pivotMatrix2951 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def pivotMatrix2952 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def pivotMatrix2953 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def pivotMatrix2954 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 2, -3]]

def pivotMatrix2955 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def pivotMatrix2956 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def pivotMatrix2957 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 0, 3], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def pivotMatrix2958 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![2, 0, 0, -2]]

def pivotMatrix2959 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, 0, -3]]

def pivotMatrix2960 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 2, -4]]

def pivotMatrix2961 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def pivotMatrix2962 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def pivotMatrix2963 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def pivotMatrix2964 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def pivotMatrix2965 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def pivotMatrix2966 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def pivotMatrix2967 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def pivotMatrix2968 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def pivotMatrix2969 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def pivotMatrix2970 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def pivotMatrix2971 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def pivotMatrix2972 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def pivotMatrix2973 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def pivotMatrix2974 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def pivotMatrix2975 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def pivotMatrix2976 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def pivotMatrix2977 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def pivotMatrix2978 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def pivotMatrix2979 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def pivotMatrix2980 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 2, 0, -3]]

def pivotMatrix2981 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, 1, -2]]

def pivotMatrix2982 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def pivotMatrix2983 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 2, 0, -3]]

def pivotMatrix2984 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def pivotMatrix2985 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 2, -1, -2]]

def pivotMatrix2986 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 1, -2]]

def pivotMatrix2987 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def pivotMatrix2988 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def pivotMatrix2989 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def pivotMatrix2990 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def pivotMatrix2991 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def pivotMatrix2992 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 0, 3], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def pivotMatrix2993 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def pivotMatrix2994 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def pivotMatrix2995 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def pivotMatrix2996 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def pivotMatrix2997 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def pivotMatrix2998 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def pivotMatrix2999 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def pivotMatrix3000 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -2, 1]]

def pivotMatrix3001 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def pivotMatrix3002 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def pivotMatrix3003 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def pivotMatrix3004 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def pivotMatrix3005 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def pivotMatrix3006 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def pivotMatrix3007 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix3008 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def pivotMatrix3009 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def pivotMatrix3010 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 2, -3]]

def pivotMatrix3011 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def pivotMatrix3012 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def pivotMatrix3013 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def pivotMatrix3014 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def pivotMatrix3015 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def pivotMatrix3016 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def pivotMatrix3017 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def pivotMatrix3018 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def pivotMatrix3019 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 2, -4]]

def pivotMatrix3020 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def pivotMatrix3021 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def pivotMatrix3022 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 1, -3]]

def pivotMatrix3023 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def pivotMatrix3024 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def pivotMatrix3025 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def pivotMatrix3026 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def pivotMatrix3027 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def pivotMatrix3028 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def pivotMatrix3029 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def pivotMatrix3030 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def pivotMatrix3031 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def pivotMatrix3032 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def pivotMatrix3033 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def pivotMatrix3034 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def pivotMatrix3035 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def pivotMatrix3036 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def pivotMatrix3037 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def pivotMatrix3038 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, 0, -2]]

def pivotMatrix3039 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def pivotMatrix3040 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def pivotMatrix3041 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def pivotMatrix3042 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def pivotMatrix3043 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def pivotMatrix3044 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def pivotMatrix3045 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def pivotMatrix3046 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def pivotMatrix3047 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def pivotMatrix3048 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def pivotMatrix3049 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def pivotMatrix3050 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def pivotMatrix3051 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def pivotMatrix3052 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def pivotMatrix3053 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def pivotMatrix3054 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def pivotMatrix3055 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def pivotMatrix3056 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def pivotMatrix3057 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def pivotMatrix3058 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -1, -1, 0]]

def pivotMatrix3059 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def pivotMatrix3060 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def pivotMatrix3061 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def pivotMatrix3062 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def pivotMatrix3063 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def pivotMatrix3064 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def pivotMatrix3065 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def pivotMatrix3066 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def pivotMatrix3067 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def pivotMatrix3068 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def pivotMatrix3069 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def pivotMatrix3070 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def pivotMatrix3071 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, 0, 0], ![1, 0, -2, 1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix3072 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def pivotMatrix3073 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def pivotMatrix3074 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def pivotMatrix3075 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def pivotMatrix3076 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def pivotMatrix3077 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def pivotMatrix3078 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def pivotMatrix3079 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def pivotMatrix3080 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def pivotMatrix3081 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def pivotMatrix3082 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def pivotMatrix3083 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def pivotMatrix3084 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def pivotMatrix3085 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def pivotMatrix3086 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def pivotMatrix3087 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def pivotMatrix3088 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def pivotMatrix3089 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, 0, -2]]

def pivotMatrix3090 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def pivotMatrix3091 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def pivotMatrix3092 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def pivotMatrix3093 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def pivotMatrix3094 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def pivotMatrix3095 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def pivotMatrix3096 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 2, 1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def pivotMatrix3097 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 2, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def pivotMatrix3098 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def pivotMatrix3099 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def pivotMatrix3100 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 2, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def pivotMatrix3101 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def pivotMatrix3102 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def pivotMatrix3103 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def pivotMatrix3104 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def pivotMatrix3105 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def pivotMatrix3106 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def pivotMatrix3107 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def pivotMatrix3108 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def pivotMatrix3109 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -1, 0, -1]]

def pivotMatrix3110 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def pivotMatrix3111 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def pivotMatrix3112 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def pivotMatrix3113 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def pivotMatrix3114 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def pivotMatrix3115 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def pivotMatrix3116 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -2, 4], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def pivotMatrix3117 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -2, 0, 0]]

def pivotMatrix3118 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def pivotMatrix3119 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -2, 0, 0]]

def pivotMatrix3120 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def pivotMatrix3121 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -2, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def pivotMatrix3122 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -2, 4], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def pivotMatrix3123 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -2, 4], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def pivotMatrix3124 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, -1, 3], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def pivotMatrix3125 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def pivotMatrix3126 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def pivotMatrix3127 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def pivotMatrix3128 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def pivotMatrix3129 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def pivotMatrix3130 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def pivotMatrix3131 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def pivotMatrix3132 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def pivotMatrix3133 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def pivotMatrix3134 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def pivotMatrix3135 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix3136 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def pivotMatrix3137 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 0, 0]]

def pivotMatrix3138 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def pivotMatrix3139 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def pivotMatrix3140 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def pivotMatrix3141 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 0, 1, -2]]

def pivotMatrix3142 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def pivotMatrix3143 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def pivotMatrix3144 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def pivotMatrix3145 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 2, -2]]

def pivotMatrix3146 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def pivotMatrix3147 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def pivotMatrix3148 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 0, 0, -1]]

def pivotMatrix3149 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def pivotMatrix3150 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, -2, 0, 2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def pivotMatrix3151 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def pivotMatrix3152 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def pivotMatrix3153 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def pivotMatrix3154 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def pivotMatrix3155 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def pivotMatrix3156 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def pivotMatrix3157 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def pivotMatrix3158 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def pivotMatrix3159 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def pivotMatrix3160 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def pivotMatrix3161 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def pivotMatrix3162 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 3, -4]]

def pivotMatrix3163 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def pivotMatrix3164 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def pivotMatrix3165 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def pivotMatrix3166 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def pivotMatrix3167 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def pivotMatrix3168 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def pivotMatrix3169 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def pivotMatrix3170 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def pivotMatrix3171 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 2, -3]]

def pivotMatrix3172 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def pivotMatrix3173 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def pivotMatrix3174 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def pivotMatrix3175 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def pivotMatrix3176 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def pivotMatrix3177 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def pivotMatrix3178 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![2, -2, 0, 0]]

def pivotMatrix3179 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def pivotMatrix3180 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def pivotMatrix3181 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def pivotMatrix3182 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def pivotMatrix3183 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def pivotMatrix3184 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def pivotMatrix3185 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def pivotMatrix3186 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 1, -2]]

def pivotMatrix3187 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def pivotMatrix3188 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def pivotMatrix3189 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, -1, 0]]

def pivotMatrix3190 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def pivotMatrix3191 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def pivotMatrix3192 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def pivotMatrix3193 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def pivotMatrix3194 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def pivotMatrix3195 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def pivotMatrix3196 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def pivotMatrix3197 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def pivotMatrix3198 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 1, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def pivotMatrix3199 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 1, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix3200 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 1, 1], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def pivotMatrix3201 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 2, -3]]

def pivotMatrix3202 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def pivotMatrix3203 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def pivotMatrix3204 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def pivotMatrix3205 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def pivotMatrix3206 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 1, 1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def pivotMatrix3207 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def pivotMatrix3208 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def pivotMatrix3209 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def pivotMatrix3210 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def pivotMatrix3211 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def pivotMatrix3212 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def pivotMatrix3213 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 1, 2, -4]]

def pivotMatrix3214 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 1, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def pivotMatrix3215 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def pivotMatrix3216 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def pivotMatrix3217 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def pivotMatrix3218 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, 3, -1], ![0, -1, -3, 4], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def pivotMatrix3219 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, 3, -1], ![0, -1, -2, 3], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def pivotMatrix3220 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, 3, -1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -2, -1, 2], ![1, 0, 0, -1]]

def pivotMatrix3221 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 3, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3], ![1, 0, 0, -1]]

def pivotMatrix3222 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -3, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def pivotMatrix3223 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 0, 0]]

def pivotMatrix3224 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def pivotMatrix3225 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def pivotMatrix3226 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def pivotMatrix3227 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def pivotMatrix3228 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def pivotMatrix3229 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def pivotMatrix3230 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def pivotMatrix3231 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def pivotMatrix3232 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def pivotMatrix3233 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def pivotMatrix3234 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def pivotMatrix3235 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def pivotMatrix3236 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def pivotMatrix3237 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def pivotMatrix3238 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def pivotMatrix3239 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -2, 3], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def pivotMatrix3240 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 0, 0]]

def pivotMatrix3241 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, -1, 1]]

def pivotMatrix3242 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def pivotMatrix3243 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def pivotMatrix3244 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def pivotMatrix3245 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def pivotMatrix3246 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 1, -1], ![1, 1, 1, -3]]

def pivotMatrix3247 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def pivotMatrix3248 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def pivotMatrix3249 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def pivotMatrix3250 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def pivotMatrix3251 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -1, 2], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def pivotMatrix3252 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -1, 2], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def pivotMatrix3253 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def pivotMatrix3254 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def pivotMatrix3255 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def pivotMatrix3256 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def pivotMatrix3257 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def pivotMatrix3258 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, 0, 0]]

def pivotMatrix3259 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def pivotMatrix3260 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def pivotMatrix3261 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def pivotMatrix3262 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def pivotMatrix3263 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -1, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix3264 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -1, 2], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def pivotMatrix3265 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, -2, 2]]

def pivotMatrix3266 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def pivotMatrix3267 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def pivotMatrix3268 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def pivotMatrix3269 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def pivotMatrix3270 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def pivotMatrix3271 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def pivotMatrix3272 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def pivotMatrix3273 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def pivotMatrix3274 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 3, -4]]

def pivotMatrix3275 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def pivotMatrix3276 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def pivotMatrix3277 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def pivotMatrix3278 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def pivotMatrix3279 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def pivotMatrix3280 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def pivotMatrix3281 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def pivotMatrix3282 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def pivotMatrix3283 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def pivotMatrix3284 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def pivotMatrix3285 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def pivotMatrix3286 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![2, -2, 0, 0]]

def pivotMatrix3287 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def pivotMatrix3288 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def pivotMatrix3289 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def pivotMatrix3290 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def pivotMatrix3291 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def pivotMatrix3292 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def pivotMatrix3293 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, -2, 2]]

def pivotMatrix3294 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, -3, 3]]

def pivotMatrix3295 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -2, 2], ![1, -1, 1, -1]]

def pivotMatrix3296 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, -2, 2], ![1, -1, 0, 0]]

def pivotMatrix3297 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def pivotMatrix3298 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def pivotMatrix3299 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def pivotMatrix3300 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def pivotMatrix3301 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 1, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def pivotMatrix3302 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def pivotMatrix3303 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 3, -2], ![0, -1, -2, 3], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def pivotMatrix3304 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 1, 3, -2], ![0, -1, -1, 2], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def pivotMatrix3305 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 3, -2], ![0, -1, -1, 2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def pivotMatrix3306 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 2, -2, 2], ![0, -1, -1, 2], ![0, -1, 2, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def pivotMatrix3307 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 2, -2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def pivotMatrix3308 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 2, -2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def pivotMatrix3309 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 2, -2, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def pivotMatrix3310 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 2, -2, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def pivotMatrix3311 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 2, -2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def pivotMatrix3312 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 2, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def pivotMatrix3313 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 2, -2, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def pivotMatrix3314 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def pivotMatrix3315 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def pivotMatrix3316 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def pivotMatrix3317 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, -2, 1, -1]]

def pivotMatrix3318 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![2, -2, 0, 0]]

def pivotMatrix3319 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def pivotMatrix3320 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 2, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, -2, -1, 1]]

def pivotMatrix3321 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 2, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, -1, 1, -1]]

def pivotMatrix3322 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 2, -1, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def pivotMatrix3323 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def pivotMatrix3324 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def pivotMatrix3325 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def pivotMatrix3326 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 2, 0, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def pivotMatrix3327 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 2, 0, 0], ![0, 0, -2, 2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

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

def pivotMatrix3328 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 2, 0, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def pivotMatrix3329 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 2, 0, 0], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, -1, 2, -2]]

def pivotMatrix3330 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def pivotMatrix3331 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def pivotMatrix3332 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def pivotMatrix3333 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def pivotMatrix3334 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def pivotMatrix3335 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 2, 0, -3]]

def pivotMatrix3336 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def pivotMatrix3337 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def pivotMatrix3338 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def pivotMatrix3339 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def pivotMatrix3340 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2], ![1, 1, 0, -2]]

def pivotMatrix3341 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def pivotMatrix3342 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def pivotMatrix3343 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-1, -1, -2, 4], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def pivotMatrix3344 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -2, 4], ![-1, 0, 3, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def pivotMatrix3345 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def pivotMatrix3346 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def pivotMatrix3347 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def pivotMatrix3348 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def pivotMatrix3349 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def pivotMatrix3350 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def pivotMatrix3351 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def pivotMatrix3352 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -1, 3], ![-1, -1, 1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def pivotMatrix3353 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def pivotMatrix3354 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def pivotMatrix3355 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def pivotMatrix3356 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def pivotMatrix3357 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def pivotMatrix3358 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def pivotMatrix3359 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

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


