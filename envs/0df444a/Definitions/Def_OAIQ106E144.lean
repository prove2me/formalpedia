-- Prove2me | Definitions.Def_OAIQ106E144
-- name    : OAIQ106E144
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T18:30:48.738418+00:00
-- url     : https://prove2.me/theorems/9cb12aa8-059e-4b92-a4f0-84d9d1359dc4
-- title:
--   Definitions bundle OAIQ106E144 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 5663 declarations of OpenAI's Lean: 5663 definitions. The definitions and types are `OAI.MUB6.Certificate.PairSemantics.raw3523`, `OAI.MUB6.Certificate.PairSemantics.raw3524`, `OAI.MUB6.Certificate.PairSemantics.raw3525`, `OAI.MUB6.Certificate.PairSemantics.raw3525step0`, `OAI.MUB6.Certificate.PairSemantics.raw3525step1`, `OAI.MUB6.Certificate.PairSemantics.raw3526`, `OAI.MUB6.Certificate.PairSemantics.raw3526step0`, `OAI.MUB6.Certificate.PairSemantics.raw3526step1`, `OAI.MUB6.Certificate.PairSemantics.raw3527`, `OAI.MUB6.Certificate.PairSemantics.raw3528`, `OAI.MUB6.Certificate.PairSemantics.raw3528step0`, `OAI.MUB6.Certificate.PairSemantics.raw3528step1`, `OAI.MUB6.Certificate.PairSemantics.raw3529`, `OAI.MUB6.Certificate.PairSemantics.raw3529step0`, `OAI.MUB6.Certificate.PairSemantics.raw3529step1`, `OAI.MUB6.Certificate.PairSemantics.raw3529step2`, `OAI.MUB6.Certificate.PairSemantics.raw352step0`, `OAI.MUB6.Certificate.PairSemantics.raw353`, `OAI.MUB6.Certificate.PairSemantics.raw3530`, `OAI.MUB6.Certificate.PairSemantics.raw3531`, `OAI.MUB6.Certificate.PairSemantics.raw3531step0`, `OAI.MUB6.Certificate.PairSemantics.raw3531step1`, `OAI.MUB6.Certificate.PairSemantics.raw3532`, `OAI.MUB6.Certificate.PairSemantics.raw3532step0`, `OAI.MUB6.Certificate.PairSemantics.raw3532step1`, `OAI.MUB6.Certificate.PairSemantics.raw3533`, `OAI.MUB6.Certificate.PairSemantics.raw3533step0`, `OAI.MUB6.Certificate.PairSemantics.raw3533step1`, `OAI.MUB6.Certificate.PairSemantics.raw3533step2`, `OAI.MUB6.Certificate.PairSemantics.raw3534`, `OAI.MUB6.Certificate.PairSemantics.raw3535`, `OAI.MUB6.Certificate.PairSemantics.raw3536`, `OAI.MUB6.Certificate.PairSemantics.raw3536step0`, `OAI.MUB6.Certificate.PairSemantics.raw3537`, `OAI.MUB6.Certificate.PairSemantics.raw3537step0`, `OAI.MUB6.Certificate.PairSemantics.raw3537step1`, `OAI.MUB6.Certificate.PairSemantics.raw3537step2`, `OAI.MUB6.Certificate.PairSemantics.raw3538`, `OAI.MUB6.Certificate.PairSemantics.raw3538step0`, `OAI.MUB6.Certificate.PairSemantics.raw3538step1` and 5623 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_PairSemantics_Canonical0`, `MutuallyUnbiased_PairSemantics_Canonical1`, `MutuallyUnbiased_PairSemantics_Canonical11`, `MutuallyUnbiased_PairSemantics_Canonical110`, `MutuallyUnbiased_PairSemantics_Canonical111`, `MutuallyUnbiased_PairSemantics_Canonical112`, `MutuallyUnbiased_PairSemantics_Canonical113`, `MutuallyUnbiased_PairSemantics_Canonical114`, `MutuallyUnbiased_PairSemantics_Canonical115`, `MutuallyUnbiased_PairSemantics_Canonical116`, `MutuallyUnbiased_PairSemantics_Canonical117`, `MutuallyUnbiased_PairSemantics_Canonical118`, `MutuallyUnbiased_PairSemantics_Canonical119`, `MutuallyUnbiased_PairSemantics_Canonical12`, `MutuallyUnbiased_PairSemantics_Canonical120`, `MutuallyUnbiased_PairSemantics_Canonical121`, `MutuallyUnbiased_PairSemantics_Canonical122`, `MutuallyUnbiased_PairSemantics_Canonical123`, `MutuallyUnbiased_PairSemantics_Canonical124`, `MutuallyUnbiased_PairSemantics_Canonical125`, `MutuallyUnbiased_PairSemantics_Canonical126`, `MutuallyUnbiased_PairSemantics_Canonical127`, `MutuallyUnbiased_PairSemantics_Canonical128`, `MutuallyUnbiased_PairSemantics_Canonical129`, `MutuallyUnbiased_PairSemantics_Canonical13`, `MutuallyUnbiased_PairSemantics_Canonical130`, `MutuallyUnbiased_PairSemantics_Canonical131`, `MutuallyUnbiased_PairSemantics_Canonical132`, `MutuallyUnbiased_PairSemantics_Canonical133`, `MutuallyUnbiased_PairSemantics_Canonical134`, `MutuallyUnbiased_PairSemantics_Canonical135`, `MutuallyUnbiased_PairSemantics_Canonical136`, `MutuallyUnbiased_PairSemantics_Canonical137`, `MutuallyUnbiased_PairSemantics_Canonical138`, `MutuallyUnbiased_PairSemantics_Canonical139`, `MutuallyUnbiased_PairSemantics_Canonical14`, `MutuallyUnbiased_PairSemantics_Canonical140`, `MutuallyUnbiased_PairSemantics_Canonical141`, `MutuallyUnbiased_PairSemantics_Canonical142`, `MutuallyUnbiased_PairSemantics_Canonical143`, `MutuallyUnbiased_PairSemantics_Canonical144`, `MutuallyUnbiased_PairSemantics_Canonical145`, `MutuallyUnbiased_PairSemantics_Canonical146`, `MutuallyUnbiased_PairSemantics_Canonical147`, `MutuallyUnbiased_PairSemantics_Canonical148`, `MutuallyUnbiased_PairSemantics_Canonical149`, `MutuallyUnbiased_PairSemantics_Canonical15`, `MutuallyUnbiased_PairSemantics_Canonical150`, `MutuallyUnbiased_PairSemantics_Canonical151`, `MutuallyUnbiased_PairSemantics_Canonical152`, `MutuallyUnbiased_PairSemantics_Canonical153`, `MutuallyUnbiased_PairSemantics_Canonical154`, `MutuallyUnbiased_PairSemantics_Canonical155`, `MutuallyUnbiased_PairSemantics_Canonical156`, `MutuallyUnbiased_PairSemantics_Canonical157`, `MutuallyUnbiased_PairSemantics_Canonical158`, `MutuallyUnbiased_PairSemantics_Canonical159`, `MutuallyUnbiased_PairSemantics_Canonical16`, `MutuallyUnbiased_PairSemantics_Canonical160`, `MutuallyUnbiased_PairSemantics_Canonical161`, `MutuallyUnbiased_PairSemantics_Canonical162`, `MutuallyUnbiased_PairSemantics_Canonical163`, `MutuallyUnbiased_PairSemantics_Canonical164`, `MutuallyUnbiased_PairSemantics_Canonical165`, `MutuallyUnbiased_PairSemantics_Canonical166`, `MutuallyUnbiased_PairSemantics_Canonical167`, `MutuallyUnbiased_PairSemantics_Canonical168`, `MutuallyUnbiased_PairSemantics_Canonical169`, `MutuallyUnbiased_PairSemantics_Canonical17`, `MutuallyUnbiased_PairSemantics_Canonical170`, `MutuallyUnbiased_PairSemantics_Canonical171`, `MutuallyUnbiased_PairSemantics_Canonical172`, `MutuallyUnbiased_PairSemantics_Canonical173`, `MutuallyUnbiased_PairSemantics_Canonical174`, `MutuallyUnbiased_PairSemantics_Canonical175`, `MutuallyUnbiased_PairSemantics_Canonical176`, `MutuallyUnbiased_PairSemantics_Canonical177`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1162_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1163_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1164_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1165_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1170_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1172_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1265_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1266_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1267_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1298_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1299_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1339_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1340_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1341_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1342_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1343_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1395_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1396_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1397_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1399_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1409_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1410_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1411_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1412_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1414_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1441_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1475_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1477_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1478_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2357_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2358_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2526_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2527_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2528_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2530_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2531_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2570_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2572_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2574_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2576_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2593_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2594_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2595_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2599_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2636_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2766_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2828_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2901_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2903_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2904_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2936_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2937_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2939_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2941_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2943_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2957_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2958_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2959_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2960_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2961_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2963_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2986_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2987_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2988_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2990_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2996_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2998_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3003_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3081_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3082_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3087_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3088_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3089_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3094_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3100_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3106_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3109_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3139_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3140_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3184_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3185_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3190_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3191_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3203_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3204_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3205_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3206_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3209_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3210_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3211_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3223_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3226_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3227_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3711_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3727_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3735_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3737_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3739_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3818_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3821_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3823_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3829_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3830_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3847_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3851_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3852_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3853_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3882_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3925_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3936_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3937_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3938_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3965_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3966_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3967_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3969_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3970_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3977_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3980_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3981_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3982_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3984_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3990_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3992_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3994_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3995_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3998_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4003_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4023_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4026_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4031_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4032_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4033_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4053_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5174_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5387_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5415_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5418_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5439_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5450_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5452_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5464_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5465_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5490_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5492_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound0_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound111_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound12_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound135_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound136_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound137_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound138_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound139_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound140_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound141_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound142_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound143_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound144_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound145_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound146_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound147_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound148_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound149_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound150_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound151_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound16_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound19_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound1_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound20_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound21_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound23_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound28_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound29_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound2_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound30_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound32_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound35_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound36_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound37_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound3_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound41_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound49_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound5_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound61_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound62_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound6_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound78_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound7_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound9_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1472_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero14_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero15_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1674_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1785_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero18_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1909_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero488_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero621_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero794_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero818_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound0_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1007_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1008_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound100_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1010_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1013_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1020_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1021_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1033_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1093_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1094_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1095_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1096_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1097_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1098_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound10_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1103_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1108_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound110_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1110_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1111_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1115_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound111_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1120_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1121_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1124_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1130_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1131_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound113_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound114_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1159_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound115_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1165_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1166_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1167_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound116_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1170_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1177_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1178_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1179_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1194_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound125_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1261_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1262_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1264_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1266_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1267_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1268_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1269_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound126_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1272_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1278_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1279_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound127_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1294_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound12_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1300_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1301_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1303_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1309_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound130_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1310_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1311_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1312_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1318_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1324_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound137_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound138_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound139_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound13_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1409_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound140_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1410_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1411_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1412_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1413_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1414_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1418_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1419_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound141_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1420_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1421_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1423_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1429_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1433_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1434_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1435_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1437_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound143_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1441_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1442_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound144_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1469_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1470_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1477_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1478_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1479_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1480_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1484_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1492_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1493_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1507_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1510_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1511_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1517_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound151_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1521_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound153_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1559_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1560_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1562_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1567_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1568_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1572_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound163_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1648_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1649_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1650_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1651_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1652_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1653_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1654_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1655_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1656_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1662_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1669_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1672_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1686_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound16_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1703_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1708_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1709_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1715_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1717_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1780_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1781_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1782_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1783_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1784_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1786_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1787_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1788_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1789_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1796_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound17_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1816_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1840_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1844_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1845_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1846_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1847_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1849_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1853_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1854_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1855_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1856_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1859_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1866_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1872_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1874_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound188_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1904_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1905_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1907_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1911_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1914_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1915_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1916_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1917_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1925_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1944_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1963_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1964_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1968_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1969_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1972_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1977_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1985_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound199_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound19_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2033_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2034_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2035_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2036_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2037_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2038_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2040_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2046_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2048_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2049_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2050_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2059_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2062_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2075_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2077_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound207_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound213_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound214_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2166_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2168_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2169_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2170_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2171_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2172_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2173_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2174_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2175_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2176_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2178_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2180_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2181_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2182_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2183_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2184_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2185_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2187_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2188_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2189_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2191_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2192_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2193_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2195_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2196_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2197_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2199_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound21_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2200_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2201_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2202_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2203_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2204_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2205_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2206_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2207_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2208_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2211_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2212_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2214_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2215_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2216_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2217_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2218_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2219_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2220_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2223_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2224_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2225_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2226_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2227_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2228_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2229_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2230_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2231_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2232_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2233_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2235_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2236_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2238_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2240_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2241_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2242_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2244_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2245_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2246_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2247_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2248_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2249_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2250_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2251_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2252_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2253_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2254_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2255_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2256_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2257_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2258_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2259_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2260_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2261_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2262_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2263_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2264_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2265_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2266_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2267_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2268_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound226_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2270_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2271_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2272_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2273_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2274_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2275_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2276_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2278_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2279_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2281_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2282_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2283_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2284_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2285_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2286_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2287_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2288_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2290_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2291_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2292_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2294_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2295_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2296_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2297_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2298_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2299_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound22_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2300_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2301_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2302_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2304_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2305_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2306_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2307_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2308_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2309_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2310_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2311_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2312_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2313_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2314_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2315_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2316_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2317_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2318_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2321_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2322_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2323_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2324_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2325_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2326_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2327_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2328_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2329_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2330_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2331_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2332_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2333_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2334_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2335_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2336_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2337_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2338_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2340_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2341_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2342_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2344_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2345_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2346_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2347_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2348_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2350_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2352_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2353_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2354_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2355_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2356_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2357_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2358_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2361_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2362_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2363_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2364_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2365_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2366_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2367_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2368_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2369_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound236_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2373_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2374_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2375_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2376_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2378_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2379_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2380_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2381_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2382_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2383_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2386_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2387_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2388_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2390_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2391_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2392_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2393_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2394_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2395_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2396_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2397_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2398_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2399_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound23_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2400_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2401_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2402_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2404_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2405_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2406_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2407_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2408_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2409_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2410_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2411_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2412_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2413_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2414_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2415_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2416_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2418_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2419_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2421_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2422_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2423_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2424_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound244_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound245_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound24_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound255_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound267_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound269_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound281_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound282_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound286_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound287_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound28_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound296_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound301_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound310_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound311_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound319_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound327_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound335_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound339_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound340_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound341_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound342_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound343_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound344_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound345_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound353_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound354_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound355_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound356_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound357_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound358_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound359_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound365_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound366_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound367_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound368_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound369_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound370_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound371_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound380_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound388_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound391_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound392_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound395_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound396_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound3_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound404_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound411_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound412_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound413_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound418_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound419_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound427_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound428_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound438_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound444_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound445_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound447_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound448_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound452_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound453_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound454_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound456_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound462_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound463_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound470_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound473_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound474_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound481_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound482_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound483_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound484_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound485_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound497_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound498_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound499_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound4_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound500_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound501_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound504_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound513_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound514_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound515_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound516_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound518_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound519_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound521_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound523_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound524_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound525_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound526_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound531_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound532_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound533_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound534_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound537_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound538_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound539_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound540_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound541_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound542_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound543_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound545_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound546_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound547_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound548_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound551_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound552_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound553_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound554_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound555_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound558_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound564_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound565_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound566_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound567_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound568_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound570_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound571_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound579_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound580_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound581_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound582_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound584_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound585_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound587_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound588_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound589_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound58_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound599_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound5_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound600_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound613_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound614_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound628_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound629_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound630_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound631_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound633_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound635_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound636_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound643_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound644_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound649_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound656_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound657_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound658_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound659_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound663_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound664_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound666_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound667_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound668_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound675_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound683_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound688_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound694_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound6_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound700_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound707_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound711_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound712_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound717_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound718_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound719_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound720_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound722_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound727_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound730_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound731_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound732_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound733_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound734_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound735_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound736_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound737_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound740_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound741_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound742_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound743_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound750_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound751_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound758_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound759_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound769_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound76_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound779_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound780_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound786_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound787_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound788_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound789_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound790_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound792_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound793_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound796_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound797_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound798_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound799_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound7_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound800_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound801_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound802_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound804_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound805_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound813_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound815_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound817_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound822_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound823_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound834_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound841_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound842_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound844_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound847_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound852_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound853_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound857_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound858_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound859_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound863_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound864_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound865_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound866_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound867_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound868_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound872_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound873_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound877_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound878_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound881_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound883_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound884_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound885_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound887_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound888_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound891_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound894_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound897_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound898_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound899_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound902_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound906_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound909_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound911_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound912_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound913_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound917_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound919_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound91_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound922_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound923_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound925_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound926_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound927_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound928_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound929_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound92_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound932_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound933_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound935_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound936_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound937_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound938_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound939_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound940_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound941_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound942_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound947_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound949_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound94_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound950_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound954_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound956_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound959_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound962_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound963_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound964_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound966_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound967_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound968_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound971_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound973_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound975_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound976_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound977_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound97_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound981_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound983_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound987_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound991_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound992_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound99_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound9_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval100_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval105_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1075_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval108_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval111_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval113_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval117_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval118_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1194_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1225_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval122_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval126_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval12_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1315_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval131_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval136_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval137_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval141_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval143_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1465_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval151_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1523_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval152_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1554_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1555_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval155_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval164_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval165_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval169_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval174_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval175_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval181_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval185_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval18_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval190_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval201_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval202_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval211_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval212_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval217_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval21_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval220_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval224_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval226_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval229_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval232_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval234_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval235_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval242_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval246_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval250_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval256_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval260_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval264_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval266_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval268_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval269_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval275_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval280_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval285_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval286_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval287_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval289_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval296_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval301_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval308_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval310_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval316_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval325_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval332_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval335_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval338_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval339_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval341_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval343_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval351_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval352_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval356_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval357_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval358_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval359_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval366_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval369_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval372_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval378_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval37_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval382_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval383_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval385_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval390_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval398_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval39_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval405_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval408_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval413_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval46_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval474_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval476_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval53_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval55_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval56_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval63_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval69_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval73_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval74_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval79_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval84_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval86_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval8_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval92_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval957_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval145_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval147_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval150_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval215_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval216_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval219_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval21_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval220_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval223_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval238_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval373_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval375_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval44_e`, `OAI.MUB6.Certificate.PairSemantics.boundarySound26_e`, `OAI.MUB6.Certificate.PairSemantics.boundarySound49_e`, `OAI.MUB6.Certificate.PairSemantics.boundarySound58_e`, `OAI.MUB6.Certificate.PairSemantics.boundarySound73_e`, `OAI.MUB6.Certificate.PairSemantics.sound1379_e`, `OAI.MUB6.Certificate.PairSemantics.sound1381_e`, `OAI.MUB6.Certificate.PairSemantics.sound1383_e`, `OAI.MUB6.Certificate.PairSemantics.sound1384_e`, `OAI.MUB6.Certificate.PairSemantics.sound1387_e`, `OAI.MUB6.Certificate.PairSemantics.sound1390_e`, `OAI.MUB6.Certificate.PairSemantics.sound1391_e`, `OAI.MUB6.Certificate.PairSemantics.sound1395_e`, `OAI.MUB6.Certificate.PairSemantics.sound1399_e`, `OAI.MUB6.Certificate.PairSemantics.sound1414_e`, `OAI.MUB6.Certificate.PairSemantics.sound1419_e`, `OAI.MUB6.Certificate.PairSemantics.sound1423_e`, `OAI.MUB6.Certificate.PairSemantics.sound1424_e`, `OAI.MUB6.Certificate.PairSemantics.sound1425_e`, `OAI.MUB6.Certificate.PairSemantics.sound1434_e`, `OAI.MUB6.Certificate.PairSemantics.sound1437_e`, `OAI.MUB6.Certificate.PairSemantics.sound1443_e`, `OAI.MUB6.Certificate.PairSemantics.sound1458_e`, `OAI.MUB6.Certificate.PairSemantics.sound1486_e`, `OAI.MUB6.Certificate.PairSemantics.sound1504_e`, `OAI.MUB6.Certificate.PairSemantics.sound1506_e`, `OAI.MUB6.Certificate.PairSemantics.sound1512_e`, `OAI.MUB6.Certificate.PairSemantics.sound1518_e`, `OAI.MUB6.Certificate.PairSemantics.sound1529_e`, `OAI.MUB6.Certificate.PairSemantics.sound1530_e`, `OAI.MUB6.Certificate.PairSemantics.sound1531_e`, `OAI.MUB6.Certificate.PairSemantics.sound1535_e`, `OAI.MUB6.Certificate.PairSemantics.sound1540_e`, `OAI.MUB6.Certificate.PairSemantics.sound1548_e`, `OAI.MUB6.Certificate.PairSemantics.sound1605_e`, `OAI.MUB6.Certificate.PairSemantics.sound1614_e`, `OAI.MUB6.Certificate.PairSemantics.sound1617_e`, `OAI.MUB6.Certificate.PairSemantics.sound1624_e`, `OAI.MUB6.Certificate.PairSemantics.sound1627_e`, `OAI.MUB6.Certificate.PairSemantics.sound1628_e`, `OAI.MUB6.Certificate.PairSemantics.sound1631_e`, `OAI.MUB6.Certificate.PairSemantics.sound1634_e`, `OAI.MUB6.Certificate.PairSemantics.sound1635_e`, `OAI.MUB6.Certificate.PairSemantics.sound1637_e`, `OAI.MUB6.Certificate.PairSemantics.sound1644_e`, `OAI.MUB6.Certificate.PairSemantics.sound1646_e`, `OAI.MUB6.Certificate.PairSemantics.sound1648_e`, `OAI.MUB6.Certificate.PairSemantics.sound1685_e`, `OAI.MUB6.Certificate.PairSemantics.sound1716_e`, `OAI.MUB6.Certificate.PairSemantics.sound1736_e`, `OAI.MUB6.Certificate.PairSemantics.sound1739_e`, `OAI.MUB6.Certificate.PairSemantics.sound1768_e`, `OAI.MUB6.Certificate.PairSemantics.sound1770_e`, `OAI.MUB6.Certificate.PairSemantics.sound1793_e`, `OAI.MUB6.Certificate.PairSemantics.sound1800_e`, `OAI.MUB6.Certificate.PairSemantics.sound1828_e`, `OAI.MUB6.Certificate.PairSemantics.sound1849_e`, `OAI.MUB6.Certificate.PairSemantics.sound1858_e`, `OAI.MUB6.Certificate.PairSemantics.sound1860_e`, `OAI.MUB6.Certificate.PairSemantics.sound1865_e`, `OAI.MUB6.Certificate.PairSemantics.sound1866_e`, `OAI.MUB6.Certificate.PairSemantics.sound1867_e`, `OAI.MUB6.Certificate.PairSemantics.sound1869_e`, `OAI.MUB6.Certificate.PairSemantics.sound1870_e`, `OAI.MUB6.Certificate.PairSemantics.sound1872_e`, `OAI.MUB6.Certificate.PairSemantics.sound1875_e`, `OAI.MUB6.Certificate.PairSemantics.sound1876_e`, `OAI.MUB6.Certificate.PairSemantics.sound1879_e`, `OAI.MUB6.Certificate.PairSemantics.sound1885_e`, `OAI.MUB6.Certificate.PairSemantics.sound1978_e`, `OAI.MUB6.Certificate.PairSemantics.sound1980_e`, `OAI.MUB6.Certificate.PairSemantics.sound1986_e`, `OAI.MUB6.Certificate.PairSemantics.sound1987_e`, `OAI.MUB6.Certificate.PairSemantics.sound2041_e`, `OAI.MUB6.Certificate.PairSemantics.sound2058_e`, `OAI.MUB6.Certificate.PairSemantics.sound2071_e`, `OAI.MUB6.Certificate.PairSemantics.sound2097_e`, `OAI.MUB6.Certificate.PairSemantics.sound2106_e`, `OAI.MUB6.Certificate.PairSemantics.sound2107_e`, `OAI.MUB6.Certificate.PairSemantics.sound2108_e`, `OAI.MUB6.Certificate.PairSemantics.sound2117_e`, `OAI.MUB6.Certificate.PairSemantics.sound2122_e`, `OAI.MUB6.Certificate.PairSemantics.sound2123_e`, `OAI.MUB6.Certificate.PairSemantics.sound2128_e`, `OAI.MUB6.Certificate.PairSemantics.sound2132_e`, `OAI.MUB6.Certificate.PairSemantics.sound2152_e`, `OAI.MUB6.Certificate.PairSemantics.sound2168_e`, `OAI.MUB6.Certificate.PairSemantics.sound2175_e`, `OAI.MUB6.Certificate.PairSemantics.sound2177_e`, `OAI.MUB6.Certificate.PairSemantics.sound2189_e`, `OAI.MUB6.Certificate.PairSemantics.sound2190_e`, `OAI.MUB6.Certificate.PairSemantics.sound2197_e`, `OAI.MUB6.Certificate.PairSemantics.sound2201_e`, `OAI.MUB6.Certificate.PairSemantics.sound2202_e`, `OAI.MUB6.Certificate.PairSemantics.sound2213_e`, `OAI.MUB6.Certificate.PairSemantics.sound2228_e`, `OAI.MUB6.Certificate.PairSemantics.sound2244_e`, `OAI.MUB6.Certificate.PairSemantics.sound2262_e`, `OAI.MUB6.Certificate.PairSemantics.sound2284_e`, `OAI.MUB6.Certificate.PairSemantics.sound2286_e`, `OAI.MUB6.Certificate.PairSemantics.sound2293_e`, `OAI.MUB6.Certificate.PairSemantics.sound2294_e`, `OAI.MUB6.Certificate.PairSemantics.sound2295_e`, `OAI.MUB6.Certificate.PairSemantics.sound2296_e`, `OAI.MUB6.Certificate.PairSemantics.sound2312_e`, `OAI.MUB6.Certificate.PairSemantics.sound2324_e`, `OAI.MUB6.Certificate.PairSemantics.sound2327_e`, `OAI.MUB6.Certificate.PairSemantics.sound2338_e`, `OAI.MUB6.Certificate.PairSemantics.sound2375_e`, `OAI.MUB6.Certificate.PairSemantics.sound2382_e`, `OAI.MUB6.Certificate.PairSemantics.sound2390_e`, `OAI.MUB6.Certificate.PairSemantics.sound2391_e`, `OAI.MUB6.Certificate.PairSemantics.sound2394_e`, `OAI.MUB6.Certificate.PairSemantics.sound2399_e`, `OAI.MUB6.Certificate.PairSemantics.sound2400_e`, `OAI.MUB6.Certificate.PairSemantics.sound2401_e`, `OAI.MUB6.Certificate.PairSemantics.sound2403_e`, `OAI.MUB6.Certificate.PairSemantics.sound2415_e`, `OAI.MUB6.Certificate.PairSemantics.sound2416_e`, `OAI.MUB6.Certificate.PairSemantics.sound2420_e`, `OAI.MUB6.Certificate.PairSemantics.sound2433_e`, `OAI.MUB6.Certificate.PairSemantics.sound2434_e`, `OAI.MUB6.Certificate.PairSemantics.sound2435_e`, `OAI.MUB6.Certificate.PairSemantics.sound2436_e`, `OAI.MUB6.Certificate.PairSemantics.sound2442_e`, `OAI.MUB6.Certificate.PairSemantics.sound2444_e`, `OAI.MUB6.Certificate.PairSemantics.sound2445_e`, `OAI.MUB6.Certificate.PairSemantics.sound2454_e`, `OAI.MUB6.Certificate.PairSemantics.sound2456_e`, `OAI.MUB6.Certificate.PairSemantics.sound2457_e`, `OAI.MUB6.Certificate.PairSemantics.sound2463_e`, `OAI.MUB6.Certificate.PairSemantics.sound2464_e`, `OAI.MUB6.Certificate.PairSemantics.sound2465_e`, `OAI.MUB6.Certificate.PairSemantics.sound2472_e`, `OAI.MUB6.Certificate.PairSemantics.sound2473_e`, `OAI.MUB6.Certificate.PairSemantics.sound2477_e`, `OAI.MUB6.Certificate.PairSemantics.sound2479_e`, `OAI.MUB6.Certificate.PairSemantics.sound2489_e`, `OAI.MUB6.Certificate.PairSemantics.sound2490_e`, `OAI.MUB6.Certificate.PairSemantics.sound2491_e`, `OAI.MUB6.Certificate.PairSemantics.sound2492_e`, `OAI.MUB6.Certificate.PairSemantics.sound2507_e`, `OAI.MUB6.Certificate.PairSemantics.sound2520_e`, `OAI.MUB6.Certificate.PairSemantics.sound2521_e`, `OAI.MUB6.Certificate.PairSemantics.sound2522_e`, `OAI.MUB6.Certificate.PairSemantics.sound2524_e`, `OAI.MUB6.Certificate.PairSemantics.sound2525_e`, `OAI.MUB6.Certificate.PairSemantics.sound2527_e`, `OAI.MUB6.Certificate.PairSemantics.sound2533_e`, `OAI.MUB6.Certificate.PairSemantics.sound2540_e`, `OAI.MUB6.Certificate.PairSemantics.sound2546_e`, `OAI.MUB6.Certificate.PairSemantics.sound2547_e`, `OAI.MUB6.Certificate.PairSemantics.sound2548_e`, `OAI.MUB6.Certificate.PairSemantics.sound2557_e`, `OAI.MUB6.Certificate.PairSemantics.sound2558_e`, `OAI.MUB6.Certificate.PairSemantics.sound2559_e`, `OAI.MUB6.Certificate.PairSemantics.sound2564_e`, `OAI.MUB6.Certificate.PairSemantics.sound2565_e`, `OAI.MUB6.Certificate.PairSemantics.sound2566_e`, `OAI.MUB6.Certificate.PairSemantics.sound2573_e`, `OAI.MUB6.Certificate.PairSemantics.sound2578_e`, `OAI.MUB6.Certificate.PairSemantics.sound2580_e`, `OAI.MUB6.Certificate.PairSemantics.sound2593_e`, `OAI.MUB6.Certificate.PairSemantics.sound2602_e`, `OAI.MUB6.Certificate.PairSemantics.sound2604_e`, `OAI.MUB6.Certificate.PairSemantics.sound2606_e`, `OAI.MUB6.Certificate.PairSemantics.sound2619_e`, `OAI.MUB6.Certificate.PairSemantics.sound2620_e`, `OAI.MUB6.Certificate.PairSemantics.sound2623_e`, `OAI.MUB6.Certificate.PairSemantics.sound2627_e`, `OAI.MUB6.Certificate.PairSemantics.sound2641_e`, `OAI.MUB6.Certificate.PairSemantics.sound2657_e`, `OAI.MUB6.Certificate.PairSemantics.sound2658_e`, `OAI.MUB6.Certificate.PairSemantics.sound2661_e`, `OAI.MUB6.Certificate.PairSemantics.sound2666_e`, `OAI.MUB6.Certificate.PairSemantics.sound2669_e`, `OAI.MUB6.Certificate.PairSemantics.sound2670_e`, `OAI.MUB6.Certificate.PairSemantics.sound2671_e`, `OAI.MUB6.Certificate.PairSemantics.sound2686_e`, `OAI.MUB6.Certificate.PairSemantics.sound2690_e`, `OAI.MUB6.Certificate.PairSemantics.sound2693_e`, `OAI.MUB6.Certificate.PairSemantics.sound2698_e`, `OAI.MUB6.Certificate.PairSemantics.sound2708_e`, `OAI.MUB6.Certificate.PairSemantics.sound2710_e`, `OAI.MUB6.Certificate.PairSemantics.sound2714_e`, `OAI.MUB6.Certificate.PairSemantics.sound2729_e`, `OAI.MUB6.Certificate.PairSemantics.sound2732_e`, `OAI.MUB6.Certificate.PairSemantics.sound2733_e`, `OAI.MUB6.Certificate.PairSemantics.sound2735_e`, `OAI.MUB6.Certificate.PairSemantics.sound2754_e`, `OAI.MUB6.Certificate.PairSemantics.sound2757_e`, `OAI.MUB6.Certificate.PairSemantics.sound2788_e`, `OAI.MUB6.Certificate.PairSemantics.sound2790_e`, `OAI.MUB6.Certificate.PairSemantics.sound2793_e`, `OAI.MUB6.Certificate.PairSemantics.sound2807_e`, `OAI.MUB6.Certificate.PairSemantics.sound2817_e`, `OAI.MUB6.Certificate.PairSemantics.sound2829_e`, `OAI.MUB6.Certificate.PairSemantics.sound2836_e`, `OAI.MUB6.Certificate.PairSemantics.sound2845_e`, `OAI.MUB6.Certificate.PairSemantics.sound2853_e`, `OAI.MUB6.Certificate.PairSemantics.sound2854_e`, `OAI.MUB6.Certificate.PairSemantics.sound2858_e`, `OAI.MUB6.Certificate.PairSemantics.sound2863_e`, `OAI.MUB6.Certificate.PairSemantics.sound2864_e`, `OAI.MUB6.Certificate.PairSemantics.sound2865_e`, `OAI.MUB6.Certificate.PairSemantics.sound2866_e`, `OAI.MUB6.Certificate.PairSemantics.sound2867_e`, `OAI.MUB6.Certificate.PairSemantics.sound2868_e`, `OAI.MUB6.Certificate.PairSemantics.sound2872_e`, `OAI.MUB6.Certificate.PairSemantics.sound2873_e`, `OAI.MUB6.Certificate.PairSemantics.sound2874_e`, `OAI.MUB6.Certificate.PairSemantics.sound2875_e`, `OAI.MUB6.Certificate.PairSemantics.sound2878_e`, `OAI.MUB6.Certificate.PairSemantics.sound2879_e`, `OAI.MUB6.Certificate.PairSemantics.sound2880_e`, `OAI.MUB6.Certificate.PairSemantics.sound2882_e`, `OAI.MUB6.Certificate.PairSemantics.sound2883_e`, `OAI.MUB6.Certificate.PairSemantics.sound2884_e`, `OAI.MUB6.Certificate.PairSemantics.sound2887_e`, `OAI.MUB6.Certificate.PairSemantics.sound2888_e`, `OAI.MUB6.Certificate.PairSemantics.sound2889_e`, `OAI.MUB6.Certificate.PairSemantics.sound2890_e`, `OAI.MUB6.Certificate.PairSemantics.sound2891_e`, `OAI.MUB6.Certificate.PairSemantics.sound2892_e`, `OAI.MUB6.Certificate.PairSemantics.sound2894_e`, `OAI.MUB6.Certificate.PairSemantics.sound2895_e`, `OAI.MUB6.Certificate.PairSemantics.sound2896_e`, `OAI.MUB6.Certificate.PairSemantics.sound2897_e`, `OAI.MUB6.Certificate.PairSemantics.sound2898_e`, `OAI.MUB6.Certificate.PairSemantics.sound2899_e`, `OAI.MUB6.Certificate.PairSemantics.sound2900_e`, `OAI.MUB6.Certificate.PairSemantics.sound2901_e`, `OAI.MUB6.Certificate.PairSemantics.sound2902_e`, `OAI.MUB6.Certificate.PairSemantics.sound2904_e`, `OAI.MUB6.Certificate.PairSemantics.sound2905_e`, `OAI.MUB6.Certificate.PairSemantics.sound2906_e`, `OAI.MUB6.Certificate.PairSemantics.sound2908_e`, `OAI.MUB6.Certificate.PairSemantics.sound2909_e`, `OAI.MUB6.Certificate.PairSemantics.sound2910_e`, `OAI.MUB6.Certificate.PairSemantics.sound2912_e`, `OAI.MUB6.Certificate.PairSemantics.sound2913_e`, `OAI.MUB6.Certificate.PairSemantics.sound2914_e`, `OAI.MUB6.Certificate.PairSemantics.sound2915_e`, `OAI.MUB6.Certificate.PairSemantics.sound2916_e`, `OAI.MUB6.Certificate.PairSemantics.sound2917_e`, `OAI.MUB6.Certificate.PairSemantics.sound2919_e`, `OAI.MUB6.Certificate.PairSemantics.sound2920_e`, `OAI.MUB6.Certificate.PairSemantics.sound2922_e`, `OAI.MUB6.Certificate.PairSemantics.sound2924_e`, `OAI.MUB6.Certificate.PairSemantics.sound2925_e`, `OAI.MUB6.Certificate.PairSemantics.sound2926_e`, `OAI.MUB6.Certificate.PairSemantics.sound2927_e`, `OAI.MUB6.Certificate.PairSemantics.sound2928_e`, `OAI.MUB6.Certificate.PairSemantics.sound2929_e`, `OAI.MUB6.Certificate.PairSemantics.sound2931_e`, `OAI.MUB6.Certificate.PairSemantics.sound2933_e`, `OAI.MUB6.Certificate.PairSemantics.sound2935_e`, `OAI.MUB6.Certificate.PairSemantics.sound2936_e`, `OAI.MUB6.Certificate.PairSemantics.sound2939_e`, `OAI.MUB6.Certificate.PairSemantics.sound2940_e`, `OAI.MUB6.Certificate.PairSemantics.sound2941_e`, `OAI.MUB6.Certificate.PairSemantics.sound2942_e`, `OAI.MUB6.Certificate.PairSemantics.sound2943_e`, `OAI.MUB6.Certificate.PairSemantics.sound2944_e`, `OAI.MUB6.Certificate.PairSemantics.sound2946_e`, `OAI.MUB6.Certificate.PairSemantics.sound2949_e`, `OAI.MUB6.Certificate.PairSemantics.sound2950_e`, `OAI.MUB6.Certificate.PairSemantics.sound2951_e`, `OAI.MUB6.Certificate.PairSemantics.sound2952_e`, `OAI.MUB6.Certificate.PairSemantics.sound2953_e`, `OAI.MUB6.Certificate.PairSemantics.sound2954_e`, `OAI.MUB6.Certificate.PairSemantics.sound2956_e`, `OAI.MUB6.Certificate.PairSemantics.sound2957_e`, `OAI.MUB6.Certificate.PairSemantics.sound2959_e`, `OAI.MUB6.Certificate.PairSemantics.sound2960_e`, `OAI.MUB6.Certificate.PairSemantics.sound2961_e`, `OAI.MUB6.Certificate.PairSemantics.sound2962_e`, `OAI.MUB6.Certificate.PairSemantics.sound2963_e`, `OAI.MUB6.Certificate.PairSemantics.sound2964_e`, `OAI.MUB6.Certificate.PairSemantics.sound2965_e`, `OAI.MUB6.Certificate.PairSemantics.sound2966_e`, `OAI.MUB6.Certificate.PairSemantics.sound2967_e`, `OAI.MUB6.Certificate.PairSemantics.sound2968_e`, `OAI.MUB6.Certificate.PairSemantics.sound2969_e`, `OAI.MUB6.Certificate.PairSemantics.sound2970_e`, `OAI.MUB6.Certificate.PairSemantics.sound2972_e`, `OAI.MUB6.Certificate.PairSemantics.sound2973_e`, `OAI.MUB6.Certificate.PairSemantics.sound2974_e`, `OAI.MUB6.Certificate.PairSemantics.sound2975_e`, `OAI.MUB6.Certificate.PairSemantics.sound2976_e`, `OAI.MUB6.Certificate.PairSemantics.sound2977_e`, `OAI.MUB6.Certificate.PairSemantics.sound2979_e`, `OAI.MUB6.Certificate.PairSemantics.sound2980_e`, `OAI.MUB6.Certificate.PairSemantics.sound2984_e`, `OAI.MUB6.Certificate.PairSemantics.sound2985_e`, `OAI.MUB6.Certificate.PairSemantics.sound2986_e`, `OAI.MUB6.Certificate.PairSemantics.sound2987_e`, `OAI.MUB6.Certificate.PairSemantics.sound2989_e`, `OAI.MUB6.Certificate.PairSemantics.sound2990_e`, `OAI.MUB6.Certificate.PairSemantics.sound2991_e`, `OAI.MUB6.Certificate.PairSemantics.sound2992_e`, `OAI.MUB6.Certificate.PairSemantics.sound2994_e`, `OAI.MUB6.Certificate.PairSemantics.sound2996_e`, `OAI.MUB6.Certificate.PairSemantics.sound2997_e`, `OAI.MUB6.Certificate.PairSemantics.sound2998_e`, `OAI.MUB6.Certificate.PairSemantics.sound2999_e`, `OAI.MUB6.Certificate.PairSemantics.sound3000_e`, `OAI.MUB6.Certificate.PairSemantics.sound3001_e`, `OAI.MUB6.Certificate.PairSemantics.sound3002_e`, `OAI.MUB6.Certificate.PairSemantics.sound3004_e`, `OAI.MUB6.Certificate.PairSemantics.sound3006_e`, `OAI.MUB6.Certificate.PairSemantics.sound3007_e`, `OAI.MUB6.Certificate.PairSemantics.sound3009_e`, `OAI.MUB6.Certificate.PairSemantics.sound3011_e`, `OAI.MUB6.Certificate.PairSemantics.sound3012_e`, `OAI.MUB6.Certificate.PairSemantics.sound3013_e`, `OAI.MUB6.Certificate.PairSemantics.sound3014_e`, `OAI.MUB6.Certificate.PairSemantics.sound3015_e`, `OAI.MUB6.Certificate.PairSemantics.sound3016_e`, `OAI.MUB6.Certificate.PairSemantics.sound3017_e`, `OAI.MUB6.Certificate.PairSemantics.sound3018_e`, `OAI.MUB6.Certificate.PairSemantics.sound3019_e`, `OAI.MUB6.Certificate.PairSemantics.sound3020_e`, `OAI.MUB6.Certificate.PairSemantics.sound3021_e`, `OAI.MUB6.Certificate.PairSemantics.sound3022_e`, `OAI.MUB6.Certificate.PairSemantics.sound3023_e`, `OAI.MUB6.Certificate.PairSemantics.sound3024_e`, `OAI.MUB6.Certificate.PairSemantics.sound3025_e`, `OAI.MUB6.Certificate.PairSemantics.sound3026_e`, `OAI.MUB6.Certificate.PairSemantics.sound3027_e`, `OAI.MUB6.Certificate.PairSemantics.sound3028_e`, `OAI.MUB6.Certificate.PairSemantics.sound3029_e`, `OAI.MUB6.Certificate.PairSemantics.sound3030_e`, `OAI.MUB6.Certificate.PairSemantics.sound3032_e`, `OAI.MUB6.Certificate.PairSemantics.sound3034_e`, `OAI.MUB6.Certificate.PairSemantics.sound3035_e`, `OAI.MUB6.Certificate.PairSemantics.sound3036_e`, `OAI.MUB6.Certificate.PairSemantics.sound3037_e`, `OAI.MUB6.Certificate.PairSemantics.sound3038_e`, `OAI.MUB6.Certificate.PairSemantics.sound3039_e`, `OAI.MUB6.Certificate.PairSemantics.sound3040_e`, `OAI.MUB6.Certificate.PairSemantics.sound3041_e`, `OAI.MUB6.Certificate.PairSemantics.sound3042_e`, `OAI.MUB6.Certificate.PairSemantics.sound3045_e`, `OAI.MUB6.Certificate.PairSemantics.sound3049_e`, `OAI.MUB6.Certificate.PairSemantics.sound3050_e`, `OAI.MUB6.Certificate.PairSemantics.sound3051_e`, `OAI.MUB6.Certificate.PairSemantics.sound3052_e`, `OAI.MUB6.Certificate.PairSemantics.sound3053_e`, `OAI.MUB6.Certificate.PairSemantics.sound3054_e`, `OAI.MUB6.Certificate.PairSemantics.sound3055_e`, `OAI.MUB6.Certificate.PairSemantics.sound3057_e`, `OAI.MUB6.Certificate.PairSemantics.sound3059_e`, `OAI.MUB6.Certificate.PairSemantics.sound3060_e`, `OAI.MUB6.Certificate.PairSemantics.sound3061_e`, `OAI.MUB6.Certificate.PairSemantics.sound3062_e`, `OAI.MUB6.Certificate.PairSemantics.sound3063_e`, `OAI.MUB6.Certificate.PairSemantics.sound3065_e`, `OAI.MUB6.Certificate.PairSemantics.sound3066_e`, `OAI.MUB6.Certificate.PairSemantics.sound3067_e`, `OAI.MUB6.Certificate.PairSemantics.sound3068_e`, `OAI.MUB6.Certificate.PairSemantics.sound3069_e`, `OAI.MUB6.Certificate.PairSemantics.sound3071_e`, `OAI.MUB6.Certificate.PairSemantics.sound3072_e`, `OAI.MUB6.Certificate.PairSemantics.sound3073_e`, `OAI.MUB6.Certificate.PairSemantics.sound3074_e`, `OAI.MUB6.Certificate.PairSemantics.sound3075_e`, `OAI.MUB6.Certificate.PairSemantics.sound3076_e`, `OAI.MUB6.Certificate.PairSemantics.sound3077_e`, `OAI.MUB6.Certificate.PairSemantics.sound3078_e`, `OAI.MUB6.Certificate.PairSemantics.sound3079_e`, `OAI.MUB6.Certificate.PairSemantics.sound3081_e`, `OAI.MUB6.Certificate.PairSemantics.sound3082_e`, `OAI.MUB6.Certificate.PairSemantics.sound3084_e`, `OAI.MUB6.Certificate.PairSemantics.sound3085_e`, `OAI.MUB6.Certificate.PairSemantics.sound3086_e`, `OAI.MUB6.Certificate.PairSemantics.sound3087_e`, `OAI.MUB6.Certificate.PairSemantics.sound3088_e`, `OAI.MUB6.Certificate.PairSemantics.sound3090_e`, `OAI.MUB6.Certificate.PairSemantics.sound3091_e`, `OAI.MUB6.Certificate.PairSemantics.sound3092_e`, `OAI.MUB6.Certificate.PairSemantics.sound3093_e`, `OAI.MUB6.Certificate.PairSemantics.sound3094_e`, `OAI.MUB6.Certificate.PairSemantics.sound3095_e`, `OAI.MUB6.Certificate.PairSemantics.sound3096_e`, `OAI.MUB6.Certificate.PairSemantics.sound3098_e`, `OAI.MUB6.Certificate.PairSemantics.sound3099_e`, `OAI.MUB6.Certificate.PairSemantics.sound3100_e`, `OAI.MUB6.Certificate.PairSemantics.sound3101_e`, `OAI.MUB6.Certificate.PairSemantics.sound3105_e`, `OAI.MUB6.Certificate.PairSemantics.sound3106_e`, `OAI.MUB6.Certificate.PairSemantics.sound3107_e`, `OAI.MUB6.Certificate.PairSemantics.sound3108_e`, `OAI.MUB6.Certificate.PairSemantics.sound3110_e`, `OAI.MUB6.Certificate.PairSemantics.sound3111_e`, `OAI.MUB6.Certificate.PairSemantics.sound3112_e`, `OAI.MUB6.Certificate.PairSemantics.sound3113_e`, `OAI.MUB6.Certificate.PairSemantics.sound3114_e`, `OAI.MUB6.Certificate.PairSemantics.sound3115_e`, `OAI.MUB6.Certificate.PairSemantics.sound3118_e`, `OAI.MUB6.Certificate.PairSemantics.sound3119_e`, `OAI.MUB6.Certificate.PairSemantics.sound3120_e`, `OAI.MUB6.Certificate.PairSemantics.sound3122_e`, `OAI.MUB6.Certificate.PairSemantics.sound3123_e`, `OAI.MUB6.Certificate.PairSemantics.sound3124_e`, `OAI.MUB6.Certificate.PairSemantics.sound3125_e`, `OAI.MUB6.Certificate.PairSemantics.sound3127_e`, `OAI.MUB6.Certificate.PairSemantics.sound3128_e`, `OAI.MUB6.Certificate.PairSemantics.sound3129_e`, `OAI.MUB6.Certificate.PairSemantics.sound3130_e`, `OAI.MUB6.Certificate.PairSemantics.sound3131_e`, `OAI.MUB6.Certificate.PairSemantics.sound3132_e`, `OAI.MUB6.Certificate.PairSemantics.sound3133_e`, `OAI.MUB6.Certificate.PairSemantics.sound3135_e`, `OAI.MUB6.Certificate.PairSemantics.sound3136_e`, `OAI.MUB6.Certificate.PairSemantics.sound3137_e`, `OAI.MUB6.Certificate.PairSemantics.sound3138_e`, `OAI.MUB6.Certificate.PairSemantics.sound3139_e`, `OAI.MUB6.Certificate.PairSemantics.sound3140_e`, `OAI.MUB6.Certificate.PairSemantics.sound3141_e`, `OAI.MUB6.Certificate.PairSemantics.sound3142_e`, `OAI.MUB6.Certificate.PairSemantics.sound3144_e`, `OAI.MUB6.Certificate.PairSemantics.sound3145_e`, `OAI.MUB6.Certificate.PairSemantics.sound3146_e`, `OAI.MUB6.Certificate.PairSemantics.sound3149_e`, `OAI.MUB6.Certificate.PairSemantics.sound3150_e`, `OAI.MUB6.Certificate.PairSemantics.sound3151_e`, `OAI.MUB6.Certificate.PairSemantics.sound3152_e`, `OAI.MUB6.Certificate.PairSemantics.sound3153_e`, `OAI.MUB6.Certificate.PairSemantics.sound3154_e`, `OAI.MUB6.Certificate.PairSemantics.sound3158_e`, `OAI.MUB6.Certificate.PairSemantics.sound3159_e`, `OAI.MUB6.Certificate.PairSemantics.sound3160_e`, `OAI.MUB6.Certificate.PairSemantics.sound3161_e`, `OAI.MUB6.Certificate.PairSemantics.sound3163_e`, `OAI.MUB6.Certificate.PairSemantics.sound3164_e`, `OAI.MUB6.Certificate.PairSemantics.sound3166_e`, `OAI.MUB6.Certificate.PairSemantics.sound3167_e`, `OAI.MUB6.Certificate.PairSemantics.sound3169_e`, `OAI.MUB6.Certificate.PairSemantics.sound3170_e`, `OAI.MUB6.Certificate.PairSemantics.sound3171_e`, `OAI.MUB6.Certificate.PairSemantics.sound3172_e`, `OAI.MUB6.Certificate.PairSemantics.sound3173_e`, `OAI.MUB6.Certificate.PairSemantics.sound3174_e`, `OAI.MUB6.Certificate.PairSemantics.sound3176_e`, `OAI.MUB6.Certificate.PairSemantics.sound3178_e`, `OAI.MUB6.Certificate.PairSemantics.sound3179_e`, `OAI.MUB6.Certificate.PairSemantics.sound3180_e`, `OAI.MUB6.Certificate.PairSemantics.sound3181_e`, `OAI.MUB6.Certificate.PairSemantics.sound3183_e`, `OAI.MUB6.Certificate.PairSemantics.sound3184_e`, `OAI.MUB6.Certificate.PairSemantics.sound3185_e`, `OAI.MUB6.Certificate.PairSemantics.sound3187_e`, `OAI.MUB6.Certificate.PairSemantics.sound3188_e`, `OAI.MUB6.Certificate.PairSemantics.sound3189_e`, `OAI.MUB6.Certificate.PairSemantics.sound3191_e`, `OAI.MUB6.Certificate.PairSemantics.sound3192_e`, `OAI.MUB6.Certificate.PairSemantics.sound3193_e`, `OAI.MUB6.Certificate.PairSemantics.sound3194_e`, `OAI.MUB6.Certificate.PairSemantics.sound3195_e`, `OAI.MUB6.Certificate.PairSemantics.sound3196_e`, `OAI.MUB6.Certificate.PairSemantics.sound3197_e`, `OAI.MUB6.Certificate.PairSemantics.sound3198_e`, `OAI.MUB6.Certificate.PairSemantics.sound3199_e`, `OAI.MUB6.Certificate.PairSemantics.sound3200_e`, `OAI.MUB6.Certificate.PairSemantics.sound3201_e`, `OAI.MUB6.Certificate.PairSemantics.sound3202_e`, `OAI.MUB6.Certificate.PairSemantics.sound3203_e`, `OAI.MUB6.Certificate.PairSemantics.sound3204_e`, `OAI.MUB6.Certificate.PairSemantics.sound3205_e`, `OAI.MUB6.Certificate.PairSemantics.sound3206_e`, `OAI.MUB6.Certificate.PairSemantics.sound3208_e`, `OAI.MUB6.Certificate.PairSemantics.sound3209_e`, `OAI.MUB6.Certificate.PairSemantics.sound3211_e`, `OAI.MUB6.Certificate.PairSemantics.sound3212_e`, `OAI.MUB6.Certificate.PairSemantics.sound3213_e`, `OAI.MUB6.Certificate.PairSemantics.sound3215_e`, `OAI.MUB6.Certificate.PairSemantics.sound3216_e`, `OAI.MUB6.Certificate.PairSemantics.sound3218_e`, `OAI.MUB6.Certificate.PairSemantics.sound3220_e`, `OAI.MUB6.Certificate.PairSemantics.sound3221_e`, `OAI.MUB6.Certificate.PairSemantics.sound3222_e`, `OAI.MUB6.Certificate.PairSemantics.sound3223_e`, `OAI.MUB6.Certificate.PairSemantics.sound3224_e`, `OAI.MUB6.Certificate.PairSemantics.sound3225_e`, `OAI.MUB6.Certificate.PairSemantics.sound3226_e`, `OAI.MUB6.Certificate.PairSemantics.sound3227_e`, `OAI.MUB6.Certificate.PairSemantics.sound3228_e`, `OAI.MUB6.Certificate.PairSemantics.sound3229_e`, `OAI.MUB6.Certificate.PairSemantics.sound3230_e`, `OAI.MUB6.Certificate.PairSemantics.sound3233_e`, `OAI.MUB6.Certificate.PairSemantics.sound3234_e`, `OAI.MUB6.Certificate.PairSemantics.sound3235_e`, `OAI.MUB6.Certificate.PairSemantics.sound3237_e`, `OAI.MUB6.Certificate.PairSemantics.sound3238_e`, `OAI.MUB6.Certificate.PairSemantics.sound3240_e`, `OAI.MUB6.Certificate.PairSemantics.sound3242_e`, `OAI.MUB6.Certificate.PairSemantics.sound3243_e`, `OAI.MUB6.Certificate.PairSemantics.sound3244_e`, `OAI.MUB6.Certificate.PairSemantics.sound3246_e`, `OAI.MUB6.Certificate.PairSemantics.sound3247_e`, `OAI.MUB6.Certificate.PairSemantics.sound3248_e`, `OAI.MUB6.Certificate.PairSemantics.sound3249_e`, `OAI.MUB6.Certificate.PairSemantics.sound3253_e`, `OAI.MUB6.Certificate.PairSemantics.sound3254_e`, `OAI.MUB6.Certificate.PairSemantics.sound3255_e`, `OAI.MUB6.Certificate.PairSemantics.sound3256_e`, `OAI.MUB6.Certificate.PairSemantics.sound3258_e`, `OAI.MUB6.Certificate.PairSemantics.sound3260_e`, `OAI.MUB6.Certificate.PairSemantics.sound3262_e`, `OAI.MUB6.Certificate.PairSemantics.sound3263_e`, `OAI.MUB6.Certificate.PairSemantics.sound3264_e`, `OAI.MUB6.Certificate.PairSemantics.sound3266_e`, `OAI.MUB6.Certificate.PairSemantics.sound3267_e`, `OAI.MUB6.Certificate.PairSemantics.sound3268_e`, `OAI.MUB6.Certificate.PairSemantics.sound3269_e`, `OAI.MUB6.Certificate.PairSemantics.sound3271_e`, `OAI.MUB6.Certificate.PairSemantics.sound3272_e`, `OAI.MUB6.Certificate.PairSemantics.sound3273_e`, `OAI.MUB6.Certificate.PairSemantics.sound3274_e`, `OAI.MUB6.Certificate.PairSemantics.sound3275_e`, `OAI.MUB6.Certificate.PairSemantics.sound3276_e`, `OAI.MUB6.Certificate.PairSemantics.sound3277_e`, `OAI.MUB6.Certificate.PairSemantics.sound3278_e`, `OAI.MUB6.Certificate.PairSemantics.sound3279_e`, `OAI.MUB6.Certificate.PairSemantics.sound3280_e`, `OAI.MUB6.Certificate.PairSemantics.sound3281_e`, `OAI.MUB6.Certificate.PairSemantics.sound3282_e`, `OAI.MUB6.Certificate.PairSemantics.sound3283_e`, `OAI.MUB6.Certificate.PairSemantics.sound3284_e`, `OAI.MUB6.Certificate.PairSemantics.sound3288_e`, `OAI.MUB6.Certificate.PairSemantics.sound3289_e`, `OAI.MUB6.Certificate.PairSemantics.sound3290_e`, `OAI.MUB6.Certificate.PairSemantics.sound3291_e`, `OAI.MUB6.Certificate.PairSemantics.sound3292_e`, `OAI.MUB6.Certificate.PairSemantics.sound3293_e`, `OAI.MUB6.Certificate.PairSemantics.sound3294_e`, `OAI.MUB6.Certificate.PairSemantics.sound3295_e`, `OAI.MUB6.Certificate.PairSemantics.sound3296_e`, `OAI.MUB6.Certificate.PairSemantics.sound3297_e`, `OAI.MUB6.Certificate.PairSemantics.sound3298_e`, `OAI.MUB6.Certificate.PairSemantics.sound3299_e`, `OAI.MUB6.Certificate.PairSemantics.sound3300_e`, `OAI.MUB6.Certificate.PairSemantics.sound3301_e`, `OAI.MUB6.Certificate.PairSemantics.sound3302_e`, `OAI.MUB6.Certificate.PairSemantics.sound3303_e`, `OAI.MUB6.Certificate.PairSemantics.sound3304_e`, `OAI.MUB6.Certificate.PairSemantics.sound3305_e`, `OAI.MUB6.Certificate.PairSemantics.sound3307_e`, `OAI.MUB6.Certificate.PairSemantics.sound3308_e`, `OAI.MUB6.Certificate.PairSemantics.sound3309_e`, `OAI.MUB6.Certificate.PairSemantics.sound3310_e`, `OAI.MUB6.Certificate.PairSemantics.sound3311_e`, `OAI.MUB6.Certificate.PairSemantics.sound3313_e`, `OAI.MUB6.Certificate.PairSemantics.sound3314_e`, `OAI.MUB6.Certificate.PairSemantics.sound3315_e`, `OAI.MUB6.Certificate.PairSemantics.sound3316_e`, `OAI.MUB6.Certificate.PairSemantics.sound3317_e`, `OAI.MUB6.Certificate.PairSemantics.sound3319_e`, `OAI.MUB6.Certificate.PairSemantics.sound3322_e`, `OAI.MUB6.Certificate.PairSemantics.sound3324_e`, `OAI.MUB6.Certificate.PairSemantics.sound3325_e`, `OAI.MUB6.Certificate.PairSemantics.sound3326_e`, `OAI.MUB6.Certificate.PairSemantics.sound3327_e`, `OAI.MUB6.Certificate.PairSemantics.sound3328_e`, `OAI.MUB6.Certificate.PairSemantics.sound3331_e`, `OAI.MUB6.Certificate.PairSemantics.sound3333_e`, `OAI.MUB6.Certificate.PairSemantics.sound3334_e`, `OAI.MUB6.Certificate.PairSemantics.sound3335_e`, `OAI.MUB6.Certificate.PairSemantics.sound3336_e`, `OAI.MUB6.Certificate.PairSemantics.sound3338_e`, `OAI.MUB6.Certificate.PairSemantics.sound3339_e`, `OAI.MUB6.Certificate.PairSemantics.sound3341_e`, `OAI.MUB6.Certificate.PairSemantics.sound3343_e`, `OAI.MUB6.Certificate.PairSemantics.sound3345_e`, `OAI.MUB6.Certificate.PairSemantics.sound3346_e`, `OAI.MUB6.Certificate.PairSemantics.sound3347_e`, `OAI.MUB6.Certificate.PairSemantics.sound3348_e`, `OAI.MUB6.Certificate.PairSemantics.sound3349_e`, `OAI.MUB6.Certificate.PairSemantics.sound3350_e`, `OAI.MUB6.Certificate.PairSemantics.sound3351_e`, `OAI.MUB6.Certificate.PairSemantics.sound3352_e`, `OAI.MUB6.Certificate.PairSemantics.sound3353_e`, `OAI.MUB6.Certificate.PairSemantics.sound3354_e`, `OAI.MUB6.Certificate.PairSemantics.sound3355_e`, `OAI.MUB6.Certificate.PairSemantics.sound3356_e`, `OAI.MUB6.Certificate.PairSemantics.sound3357_e`, `OAI.MUB6.Certificate.PairSemantics.sound3358_e`, `OAI.MUB6.Certificate.PairSemantics.sound3359_e`, `OAI.MUB6.Certificate.PairSemantics.sound3360_e`, `OAI.MUB6.Certificate.PairSemantics.sound3361_e`, `OAI.MUB6.Certificate.PairSemantics.sound3362_e`, `OAI.MUB6.Certificate.PairSemantics.sound3363_e`, `OAI.MUB6.Certificate.PairSemantics.sound3364_e`, `OAI.MUB6.Certificate.PairSemantics.sound3366_e`, `OAI.MUB6.Certificate.PairSemantics.sound3367_e`, `OAI.MUB6.Certificate.PairSemantics.sound3368_e`, `OAI.MUB6.Certificate.PairSemantics.sound3369_e`, `OAI.MUB6.Certificate.PairSemantics.sound3370_e`, `OAI.MUB6.Certificate.PairSemantics.sound3371_e`, `OAI.MUB6.Certificate.PairSemantics.sound3372_e`, `OAI.MUB6.Certificate.PairSemantics.sound3375_e`, `OAI.MUB6.Certificate.PairSemantics.sound3376_e`, `OAI.MUB6.Certificate.PairSemantics.sound3377_e`, `OAI.MUB6.Certificate.PairSemantics.sound3378_e`, `OAI.MUB6.Certificate.PairSemantics.sound3380_e`, `OAI.MUB6.Certificate.PairSemantics.sound3382_e`, `OAI.MUB6.Certificate.PairSemantics.sound3383_e`, `OAI.MUB6.Certificate.PairSemantics.sound3384_e`, `OAI.MUB6.Certificate.PairSemantics.sound3385_e`, `OAI.MUB6.Certificate.PairSemantics.sound3387_e`, `OAI.MUB6.Certificate.PairSemantics.sound3388_e`, `OAI.MUB6.Certificate.PairSemantics.sound3389_e`, `OAI.MUB6.Certificate.PairSemantics.sound3390_e`, `OAI.MUB6.Certificate.PairSemantics.sound3391_e`, `OAI.MUB6.Certificate.PairSemantics.sound3392_e`, `OAI.MUB6.Certificate.PairSemantics.sound3393_e`, `OAI.MUB6.Certificate.PairSemantics.sound3394_e`, `OAI.MUB6.Certificate.PairSemantics.sound3395_e`, `OAI.MUB6.Certificate.PairSemantics.sound3396_e`, `OAI.MUB6.Certificate.PairSemantics.sound3397_e`, `OAI.MUB6.Certificate.PairSemantics.sound3399_e`, `OAI.MUB6.Certificate.PairSemantics.sound3400_e`, `OAI.MUB6.Certificate.PairSemantics.sound3401_e`, `OAI.MUB6.Certificate.PairSemantics.sound3402_e`, `OAI.MUB6.Certificate.PairSemantics.sound3405_e`, `OAI.MUB6.Certificate.PairSemantics.sound3407_e`, `OAI.MUB6.Certificate.PairSemantics.sound3408_e`, `OAI.MUB6.Certificate.PairSemantics.sound3411_e`, `OAI.MUB6.Certificate.PairSemantics.sound3412_e`, `OAI.MUB6.Certificate.PairSemantics.sound3413_e`, `OAI.MUB6.Certificate.PairSemantics.sound3414_e`, `OAI.MUB6.Certificate.PairSemantics.sound3415_e`, `OAI.MUB6.Certificate.PairSemantics.sound3416_e`, `OAI.MUB6.Certificate.PairSemantics.sound3417_e`, `OAI.MUB6.Certificate.PairSemantics.sound3418_e`, `OAI.MUB6.Certificate.PairSemantics.sound3419_e`, `OAI.MUB6.Certificate.PairSemantics.sound3420_e`, `OAI.MUB6.Certificate.PairSemantics.sound3421_e`, `OAI.MUB6.Certificate.PairSemantics.sound3422_e`, `OAI.MUB6.Certificate.PairSemantics.sound3423_e`, `OAI.MUB6.Certificate.PairSemantics.sound3424_e`, `OAI.MUB6.Certificate.PairSemantics.sound3425_e`, `OAI.MUB6.Certificate.PairSemantics.sound3428_e`, `OAI.MUB6.Certificate.PairSemantics.sound3431_e`, `OAI.MUB6.Certificate.PairSemantics.sound3433_e`, `OAI.MUB6.Certificate.PairSemantics.sound3434_e`, `OAI.MUB6.Certificate.PairSemantics.sound3435_e`, `OAI.MUB6.Certificate.PairSemantics.sound3436_e`, `OAI.MUB6.Certificate.PairSemantics.sound3437_e`, `OAI.MUB6.Certificate.PairSemantics.sound3439_e`, `OAI.MUB6.Certificate.PairSemantics.sound3440_e`, `OAI.MUB6.Certificate.PairSemantics.sound3441_e`, `OAI.MUB6.Certificate.PairSemantics.sound3442_e`, `OAI.MUB6.Certificate.PairSemantics.sound3443_e`, `OAI.MUB6.Certificate.PairSemantics.sound3444_e`, `OAI.MUB6.Certificate.PairSemantics.sound3447_e`, `OAI.MUB6.Certificate.PairSemantics.sound3449_e`, `OAI.MUB6.Certificate.PairSemantics.sound3451_e`, `OAI.MUB6.Certificate.PairSemantics.sound3454_e`, `OAI.MUB6.Certificate.PairSemantics.sound3455_e`, `OAI.MUB6.Certificate.PairSemantics.sound3456_e`, `OAI.MUB6.Certificate.PairSemantics.sound3457_e`, `OAI.MUB6.Certificate.PairSemantics.sound3458_e`, `OAI.MUB6.Certificate.PairSemantics.sound3459_e`, `OAI.MUB6.Certificate.PairSemantics.sound3460_e`, `OAI.MUB6.Certificate.PairSemantics.sound3461_e`, `OAI.MUB6.Certificate.PairSemantics.sound3462_e`, `OAI.MUB6.Certificate.PairSemantics.sound3463_e`, `OAI.MUB6.Certificate.PairSemantics.sound3467_e`, `OAI.MUB6.Certificate.PairSemantics.sound3468_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound0_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound100_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound101_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound102_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound103_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound104_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound105_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound106_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound107_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound108_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound10_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound110_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound111_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound112_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound113_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound114_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound115_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound116_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound117_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound118_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound119_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound120_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound121_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound123_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound124_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound125_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound127_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound128_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound129_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound12_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound130_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound131_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound132_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound133_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound134_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound135_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound136_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound137_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound138_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound139_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound140_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound141_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound142_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound143_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound144_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound145_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound146_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound147_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound148_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound149_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound14_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound150_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound151_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound152_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound153_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound154_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound155_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound156_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound157_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound158_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound159_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound15_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound160_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound161_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound162_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound163_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound164_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound165_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound166_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound167_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound168_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound16_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound170_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound171_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound172_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound174_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound175_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound176_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound177_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound178_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound179_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound17_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound180_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound181_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound182_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound183_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound184_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound185_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound186_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound187_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound188_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound189_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound18_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound191_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound192_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound193_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound194_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound195_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound196_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound197_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound198_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound199_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound19_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound1_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound200_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound203_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound204_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound205_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound206_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound208_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound209_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound20_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound210_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound211_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound212_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound213_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound216_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound217_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound218_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound219_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound21_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound220_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound221_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound222_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound223_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound224_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound225_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound226_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound227_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound228_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound229_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound22_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound230_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound231_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound232_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound233_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound234_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound235_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound236_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound237_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound238_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound239_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound23_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound240_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound241_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound242_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound243_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound244_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound245_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound246_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound247_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound248_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound249_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound24_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound250_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound251_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound252_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound253_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound254_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound26_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound27_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound28_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound29_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound2_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound30_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound31_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound32_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound34_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound35_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound36_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound37_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound38_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound39_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound3_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound40_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound41_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound42_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound43_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound44_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound45_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound46_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound47_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound49_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound4_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound50_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound51_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound52_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound53_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound54_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound55_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound56_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound58_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound59_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound5_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound60_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound61_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound62_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound63_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound64_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound65_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound66_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound67_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound69_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound6_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound70_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound72_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound73_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound74_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound75_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound76_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound77_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound78_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound79_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound7_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound80_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound81_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound82_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound83_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound84_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound85_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound86_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound87_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound88_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound89_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound8_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound90_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound91_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound92_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound93_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound94_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound95_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound96_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound97_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound98_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound99_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound9_e`, `OAI.MUB6.Certificate.PairTargetSemantics.expandedIdentity1_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm11_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm12_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm13_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm14_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm16_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm17_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm18_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm19_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm21_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm22_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm23_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm24_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm25_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm26_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm6_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm7_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm8_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm9_e` and `OAI.MUB6.pair_cross_certificate_e`.
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

def raw3step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]

def raw3step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

def raw4 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]

def raw4step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]

def raw4step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

def raw5 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]

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

def raw35step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![3, -3], ![2, -2]]

def raw35step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![2, -2], ![3, -3]]

def raw36 : Matrix (Fin 6) (Fin 2) ℤ := ![![-5, 5], ![0, 0], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]

def raw36step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]

def raw37 : Matrix (Fin 5) (Fin 2) ℤ := ![![-5, 5], ![0, 0], ![1, -1], ![1, -1], ![3, -3]]

def raw37step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![3, -3]]

def raw38 : Matrix (Fin 5) (Fin 2) ℤ := ![![-5, 5], ![0, 0], ![1, -1], ![2, -2], ![2, -2]]

def raw38step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![2, -2], ![2, -2]]

def raw39 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![0, 0], ![1, -1], ![4, -4]]

def raw39step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![4, -4]]

def raw40 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![0, 0], ![2, -2], ![3, -3]]

def raw40step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![2, -2], ![3, -3]]

def raw41 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![0, 0], ![5, -5]]

def raw41step0 : Matrix (Fin 2) (Fin 2) ℤ := ![![-5, 5], ![5, -5]]

def raw42 : Matrix (Fin 6) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]

def raw43 : Matrix (Fin 5) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]

def raw44 : Matrix (Fin 5) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![2, -2], ![1, -1]]

def raw44step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]

def raw45 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![3, -3]]

def raw46 : Matrix (Fin 5) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![2, -2], ![1, -1], ![1, -1]]

def raw46step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]

def raw47 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![2, -2], ![2, -2]]

def raw48 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![4, -4]]

def raw49 : Matrix (Fin 5) (Fin 2) ℤ := ![![-5, 5], ![2, -2], ![1, -1], ![1, -1], ![1, -1]]

def raw49step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]

def raw50 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![2, -2], ![1, -1], ![2, -2]]

def raw50step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![2, -2], ![2, -2]]

def raw51 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![2, -2], ![3, -3]]

def raw52 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![3, -3], ![2, -2]]

def raw52step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![2, -2], ![3, -3]]

def raw54 : Matrix (Fin 3) (Fin 4) ℤ := ![![-4, 0, 1, 3], ![1, 2, -2, -1], ![3, -2, 1, -2]]

def raw54step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]

def raw54step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 2, -1], ![-3, 1, 2]]

def raw54step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![1, -3, 2], ![2, -1, -1]]

def raw55 : Matrix (Fin 3) (Fin 4) ℤ := ![![-4, 0, 1, 3], ![2, -2, 1, -1], ![2, 2, -2, -2]]

def raw55step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 1, -2], ![3, -1, -2]]

def raw55step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 2, -2], ![-1, -1, 2], ![-3, 1, 2]]

def raw55step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 2, -3], ![2, -2, 0]]

def raw56 : Matrix (Fin 3) (Fin 4) ℤ := ![![-4, 0, 2, 2], ![1, 2, -2, -1], ![3, -2, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw352step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]

def raw353 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 1, 2], ![1, 2, -2, -1], ![2, -2, 1, -1]]

def raw353step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

def raw354 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 1, 2], ![2, -2, 1, -1], ![1, 2, -2, -1]]

def raw354step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]

def raw354step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

def raw355 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 2, 1], ![-2, 2, -1, 1], ![5, -2, -1, -2]]

def raw355step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![2, -1, -1], ![1, 1, -2]]

def raw355step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

def raw356 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 2, 1], ![-1, 2, -2, 1], ![4, -2, 0, -2]]

def raw356step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![2, -2, 0], ![1, 1, -2]]

def raw356step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

def raw357 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 2, 1], ![-1, 2, 1, -2], ![4, -2, -3, 1]]

def raw357step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![2, 1, -3], ![1, -2, 1]]

def raw357step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]

def raw358 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 2, 1], ![-1, 3, 0, -2], ![4, -3, -2, 1]]

def raw358step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![2, 0, -2], ![1, -2, 1]]

def raw358step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]

def raw359 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 2, 1], ![0, -2, 0, 2], ![3, 2, -2, -3]]

def raw359step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![2, 0, -2], ![1, 2, -3]]

def raw359step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-2, 0, 2], ![-1, -2, 3]]

def raw359step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![2, 0, -2]]

def raw360 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 2, 1], ![0, -2, 1, 1], ![3, 2, -3, -2]]

def raw360step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![2, 1, -3], ![1, 1, -2]]

def raw360step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 1, -2], ![1, 2, -3]]

def raw361 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 2, 1], ![0, 2, -2, 0], ![3, -2, 0, -1]]

def raw361step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![2, -2, 0], ![1, 0, -1]]

def raw361step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![2, -2, 0]]

def raw362 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 2, 1], ![0, 2, 0, -2], ![3, -2, -2, 1]]

def raw362step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![2, 0, -2], ![1, -2, 1]]

def raw362step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-2, 0, 2], ![-1, 2, -1]]

def raw362step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

def raw363 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 2, 1], ![0, 3, -1, -2], ![3, -3, -1, 1]]

def raw363step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![2, -1, -1], ![1, -2, 1]]

def raw363step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]

def raw364 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 2, 1], ![0, 4, -2, -2], ![3, -4, 0, 1]]

def raw364step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 4, -4], ![2, -2, 0], ![1, -2, 1]]

def raw364step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 4, -4], ![1, -2, 1], ![2, -2, 0]]

def raw365 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 2, 1], ![1, -2, 0, 1], ![2, 2, -2, -2]]

def raw365step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![2, 0, -2], ![1, 1, -2]]

def raw365step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

def raw366 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 2, 1], ![1, 2, -2, -1], ![2, -2, 0, 0]]

def raw366step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0]]

def raw366step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-2, 2, 0], ![-1, 1, 0]]

def raw366step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def raw367 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 2, 1], ![1, 2, -1, -2], ![2, -2, -1, 1]]

def raw367step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![2, -1, -1], ![1, -2, 1]]

def raw367step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

def raw368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]

def raw368step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]

def raw368step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

def raw369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]

def raw369step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]

def raw369step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

def raw370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]

def raw370step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]

def raw370step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

def raw371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]

def raw371step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]

def raw371step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def raw372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]

def raw372step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]

def raw372step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw373 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]

def raw373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]

def raw373step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]

def raw374 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]

def raw374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-3, 2, 1]]

def raw374step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]

def raw375 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]

def raw375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]

def raw376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]

def raw376step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]

def raw376step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]

def raw377step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]

def raw377step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]

def raw378 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]

def raw378step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]

def raw378step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def raw379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]

def raw379step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]

def raw379step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw380 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]

def raw380step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]

def raw380step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

def raw381 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]

def raw381step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]

def raw381step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]

def raw382 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]

def raw382step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-2, 2, 0], ![-2, -1, 3]]

def raw382step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]

def raw383 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]

def raw383step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]

def raw383step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical110
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3523 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw3524 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw3525 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -2, 3, -3]]

def raw3525step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![0, -2, -1, 3], ![2, 1, 0, -3]]

def raw3525step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, 1, 0, -2]]

def raw3526 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw3526step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 2, -1], ![0, -1, 0, 1], ![-1, 2, -2, 1], ![-1, 0, 0, 1]]

def raw3526step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw3527 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, -1, 0]]

def raw3528 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw3528step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 2, -1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 1, -2, 2]]

def raw3528step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw3529 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw3529step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![0, -2, 0, 2], ![2, 1, -1, -2]]

def raw3529step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![0, 2, 0, -2], ![-2, -1, 1, 2]]

def raw3529step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw3530 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def raw3531 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -2, 1, -1]]

def raw3531step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 2, -1], ![0, -1, -1, 2], ![-2, 2, -1, 1]]

def raw3531step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def raw3532 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw3532step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 2, -1], ![0, -1, -2, 3], ![-1, 1, 0, 0], ![-1, 1, 0, 0]]

def raw3532step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def raw3533 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![2, -2, 0, 0]]

def raw3533step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![0, -2, 2, 0], ![2, 1, -3, 0]]

def raw3533step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![0, 2, -2, 0], ![-2, -1, 3, 0]]

def raw3533step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -2, 0]]

def raw3534 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def raw3535 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw3536 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, -1, 1]]

def raw3536step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw3537 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![2, -2, -1, 1]]

def raw3537step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![0, -2, 3, -1], ![2, 1, -4, 1]]

def raw3537step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![0, 2, -3, 1], ![-2, -1, 4, -1]]

def raw3537step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, 1, -3], ![2, 0, -2, 0]]

def raw3538 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![1, -2, 0, 1], ![1, 1, 2, -4]]

def raw3538step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 2, -1], ![-1, 2, 0, -1], ![-1, -1, -2, 4]]

def raw3538step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw3539 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![1, -2, 1, 0], ![1, 1, 1, -3]]

def raw3539step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, -2, 1, 1], ![2, 1, 0, -3]]

def raw3539step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 2, -1], ![0, 2, -1, -1], ![-2, -1, 0, 3]]

def raw3539step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw3540 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![1, -2, 2, -1], ![1, 1, 0, -2]]

def raw3540step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 2, -1], ![-1, 2, -2, 1], ![-1, -1, 0, 2]]

def raw3540step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw3541 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![1, -2, 3, -2], ![1, 1, -1, -1]]

def raw3541step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, -2, 3, -1], ![2, 1, -2, -1]]

def raw3541step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 2, -2], ![1, 1, 0, -2]]

def raw3542 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![1, -1, -1, 1], ![1, 0, 3, -4]]

def raw3542step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 2, -1], ![-1, 1, 1, -1], ![-1, 0, -3, 4]]

def raw3542step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw3543 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw3543step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -2, 0, 1]]

def raw3544 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw3544step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 2, -1], ![-1, 1, -1, 1], ![-1, 0, -1, 2]]

def raw3544step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw3545 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def raw3545step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 2, -1], ![-1, 1, -2, 2], ![-1, 0, 0, 1]]

def raw3545step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw3546 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw3546step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, -2, 3, -1], ![2, 1, -3, 0]]

def raw3546step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, -2, 1]]

def raw3547 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![1, 0, -1, 0], ![1, -1, 3, -3]]

def raw3547step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 0, -1], ![0, -2, -1, 3], ![2, 1, 0, -3]]

def raw3547step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, -2, 1]]

def raw3548 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![1, 0, 3, -4], ![1, -1, -1, 1]]

def raw3548step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 2, -1], ![-1, 0, -3, 4], ![-1, 1, 1, -1]]

def raw3548step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw3549 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![1, 1, 0, -2], ![1, -2, 2, -1]]

def raw3549step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 2, -1], ![-1, -1, 0, 2], ![-1, 2, -2, 1]]

def raw3549step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw3550 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![1, 1, 2, -4], ![1, -2, 0, 1]]

def raw3550step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 2, -1], ![-1, -1, -2, 4], ![-1, 2, 0, -1]]

def raw3550step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw3551 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 0, 3, -4]]

def raw3551step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![-1, 0, -3, 4]]

def raw3551step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical111
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3552 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 0, -1, 1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw3552step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![-1, 1, -3, 3], ![-1, 0, 1, 0]]

def raw3552step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, -2, 0], ![1, -1, 3, -3]]

def raw3553 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 0, 3, -3], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw3553step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 1, 0], ![0, 0, -3, 3], ![-1, 1, 1, -1], ![-1, 0, 1, 0]]

def raw3553step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, -1, 1]]

def raw3554 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -2, 1], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def raw3554step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def raw3555 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -2, 1], ![1, -2, 2, -1], ![1, 0, 1, -2]]

def raw3555step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 1, -2]]

def raw3556 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -2, 1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw3556step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw3557 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw3557step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw3558 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -2, 1], ![2, -2, 3, -3]]

def raw3558step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![0, -1, -2, 3], ![2, 0, 1, -3]]

def raw3558step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, 1, 0, -2]]

def raw3559 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, -1, 2], ![1, 0, 3, -4]]

def raw3560 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 2, -3]]

def raw3560step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-1, 2, 0, -1], ![-1, 0, -2, 3]]

def raw3560step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw3561 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 0, 1, -2]]

def raw3561step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-1, 2, -1, 0], ![-1, 0, -1, 2]]

def raw3561step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw3562 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw3562step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw3563 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 3, -2], ![1, 0, -1, 0]]

def raw3563step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw3564 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, -1, 3, -3]]

def raw3565 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw3565step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw3566 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, -1, -1, 1]]

def raw3566step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, -1, 3, -3]]

def raw3567 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def raw3567step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![0, -1, -1, 2], ![2, 0, 0, -2]]

def raw3567step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def raw3568 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def raw3568step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw3569 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, -2, 1]]

def raw3570 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 2, -2]]

def raw3570step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 1, 1, -1], ![-1, 1, -2, 2]]

def raw3570step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw3571 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw3571step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 1, -1, 1]]

def raw3571step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw3572 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def raw3572step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 1, 0], ![0, -1, -1, 2], ![-1, 2, -1, 0], ![-1, 0, 1, 0]]

def raw3572step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -1, -1, 0]]

def raw3573 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 0, -2, 1]]

def raw3574 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw3574step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 1, 0], ![0, -1, -1, 2], ![-1, 1, 0, 0], ![-1, 1, 0, 0]]

def raw3574step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw3575 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def raw3575step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 1, 0], ![0, -1, -2, 3], ![-1, 2, 0, -1], ![-1, 0, 1, 0]]

def raw3575step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw3576 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw3576step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 1, 0], ![0, -1, -2, 3], ![-1, 1, 1, -1], ![-1, 1, 0, 0]]

def raw3576step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw3577 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, -2, -1, 1]]

def raw3577step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![0, -1, 2, -1], ![2, 0, -3, 1]]

def raw3577step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 2, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw3578 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, -1, 2], ![1, 0, -1, 0]]

def raw3579 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, 0, 1], ![1, 0, -2, 1]]

def raw3580 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -2, 2], ![1, -1, 0, 0]]

def raw3581 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, -1, 1]]

def raw3582 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![2, -2, -2, 2]]

def raw3582step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![0, -1, 3, -2], ![2, 0, -4, 2]]

def raw3582step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 2, 0], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw3583 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![1, -2, -1, 2], ![1, 1, 2, -4]]

def raw3583step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, -1, -1, 2], ![2, 0, 2, -4]]

def raw3583step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical112
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3584 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 1, 1, -3]]

def raw3584step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 1, 0], ![-1, 2, 0, -1], ![-1, -1, -1, 3]]

def raw3584step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw3585 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 1, -1, -1]]

def raw3585step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, -1, 2, -1], ![2, 0, -1, -1]]

def raw3585step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def raw3586 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![1, -1, -2, 2], ![1, 0, 3, -4]]

def raw3586step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, -1, -2, 3], ![2, 0, 2, -4]]

def raw3586step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw3587 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 2, -3]]

def raw3587step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, -1, -1, 2], ![2, 0, 1, -3]]

def raw3587step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw3588 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw3588step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, -1, 1, 0], ![2, 0, -1, -1]]

def raw3588step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw3589 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![1, 0, -2, 1], ![1, -1, 3, -3]]

def raw3589step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 0, -1], ![0, -1, -2, 3], ![2, 0, 1, -3]]

def raw3589step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def raw3590 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 1, -1, -1]]

def raw3590step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 0, 1, -1], ![2, -1, 0, -1]]

def raw3590step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw3591 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 1, -2, 0]]

def raw3591step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 0, 2, -2], ![2, -1, -1, 0]]

def raw3591step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 2, -1], ![0, 0, -2, 2], ![-2, 1, 1, 0]]

def raw3591step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw3592 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 1, -3, 1]]

def raw3592step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 0, 3, -3], ![2, -1, -2, 1]]

def raw3592step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 2, -1], ![0, 0, -3, 3], ![-2, 1, 2, -1]]

def raw3592step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 2, -1, -1], ![1, -2, -1, 2]]

def raw3593 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def raw3593step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw3594 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw3594step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 0, 1, -1], ![2, -1, -1, 0]]

def raw3594step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw3595 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -2, 1]]

def raw3595step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 0, 1], ![-1, 1, -2, 2], ![-1, 0, 2, -1]]

def raw3595step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw3596 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![0, 1, -2, 1], ![2, -2, 1, -1]]

def raw3596step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![0, -1, 2, -1], ![-2, 2, -1, 1]]

def raw3596step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def raw3597 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 1, -3, 1]]

def raw3598 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw3598step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![-1, 1, 1, -1], ![-1, 0, 0, 1]]

def raw3598step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, -1, -1]]

def raw3599 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 0, -2, 1]]

def raw3599step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![-1, 1, -1, 1], ![-1, 0, 2, -1]]

def raw3599step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw3600 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 2, -3], ![1, -2, 1, 0], ![1, 1, -3, 1]]

def raw3600step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 2, 1, -3], ![2, -3, 0, 1]]

def raw3600step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 2, -1], ![0, -2, -1, 3], ![-2, 3, 0, -1]]

def raw3600step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 2, -1, -1], ![2, -1, -1, 0]]

def raw3601 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw3601step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -2, 3], ![-1, 1, 1, -1], ![-1, 0, 1, 0]]

def raw3601step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, -1, -1]]

def raw3602 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw3602step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -2, 3], ![-1, 1, 0, 0], ![-1, 0, 2, -1]]

def raw3602step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw3603 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 0, -3, 2]]

def raw3603step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -2, 3], ![-1, 1, -1, 1], ![-1, 0, 3, -2]]

def raw3603step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 3, -2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw3604 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 3, -4], ![1, -2, -1, 2], ![1, 1, -2, 0]]

def raw3604step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 3, -1, -2], ![2, -4, 2, 0]]

def raw3604step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 2, -1], ![0, -3, 1, 2], ![-2, 4, -2, 0]]

def raw3604step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 2, 1, -3], ![2, -1, -1, 0]]

def raw3605 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 3, -4], ![1, -2, 0, 1], ![1, 1, -3, 1]]

def raw3605step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 3, 0, -3], ![2, -4, 1, 1]]

def raw3605step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 2, -1], ![0, -3, 0, 3], ![-2, 4, -1, -1]]

def raw3605step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 3, -3], ![0, 2, -1, -1], ![2, -1, -1, 0]]

def raw3606 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 3, -4], ![1, -1, -2, 2], ![1, 0, -1, 0]]

def raw3606step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -3, 4], ![-1, 1, 2, -2], ![-1, 0, 1, 0]]

def raw3606step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 2, 0, -2], ![1, -1, 2, -2]]

def raw3607 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, 0, -2, 1]]

def raw3607step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -3, 4], ![-1, 1, 1, -1], ![-1, 0, 2, -1]]

def raw3607step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw3608 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -3, 2]]

def raw3608step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -3, 4], ![-1, 1, 0, 0], ![-1, 0, 3, -2]]

def raw3608step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 3, -2], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw3609 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 3, -4], ![1, 0, -3, 2], ![1, -1, 0, 0]]

def raw3609step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -3, 4], ![-1, 0, 3, -2], ![-1, 1, 0, 0]]

def raw3609step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 3, -2], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw3610 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 3, -4], ![1, 0, -2, 1], ![1, -1, -1, 1]]

def raw3610step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -3, 4], ![-1, 0, 2, -1], ![-1, 1, 1, -1]]

def raw3610step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw3611 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, -3, 1], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def raw3611step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![0, -3, 0, 3], ![2, 1, 1, -4]]

def raw3611step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -2, 2, 0], ![0, 3, 0, -3], ![-2, -1, -1, 4]]

def raw3611step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 3, -3], ![0, 2, -2, 0], ![2, -1, 0, -1]]

def raw3612 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, -3, 1], ![1, -2, 1, 0], ![1, 0, 2, -3]]

def raw3612step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -2, 3, -1], ![-1, 2, -1, 0], ![-1, 0, -2, 3]]

def raw3612step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 2, -2, 0], ![2, -1, 0, -1]]

def raw3613 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, -3, 1], ![1, -2, 2, -1], ![1, 0, 1, -2]]

def raw3613step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -2, 3, -1], ![-1, 2, -2, 1], ![-1, 0, -1, 2]]

def raw3613step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![2, -1, 1, -2]]

def raw3614 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, -3, 1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw3614step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![0, -3, 3, 0], ![2, 1, -2, -1]]

def raw3614step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -2, 2, 0], ![0, 3, -3, 0], ![-2, -1, 2, 1]]

def raw3614step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, 0, -1], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, -2, -1, 2]]

def raw3615 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, -3, 1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw3615step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![0, -3, 0, 3], ![2, 1, 0, -3]]

def raw3615step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -3, 3], ![0, 2, 1, -3], ![1, -2, 0, 1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical113
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3616 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, -3, 1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def raw3616step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -2, 3, -1], ![-1, 1, -1, 1], ![-1, 1, -2, 2]]

def raw3616step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def raw3617 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, -2, 0], ![1, -2, -1, 2], ![1, 0, 3, -4]]

def raw3617step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![0, -2, -1, 3], ![2, 0, 2, -4]]

def raw3617step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -2, 2, 0], ![0, 2, 1, -3], ![-2, 0, -2, 4]]

def raw3617step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 2, 1, -3], ![2, 0, -1, -1]]

def raw3618 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, -2, 0], ![1, -2, 3, -2], ![1, 0, -1, 0]]

def raw3618step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![0, -2, 3, -1], ![2, 0, -2, 0]]

def raw3618step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw3619 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, -2, 0], ![1, -1, -1, 1], ![1, -1, 3, -3]]

def raw3619step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![0, -2, -1, 3], ![2, 0, 1, -3]]

def raw3619step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![2, -1, 0, -1]]

def raw3620 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw3620step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![0, -2, 0, 2], ![2, 0, 0, -2]]

def raw3620step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -2, 0, 1]]

def raw3621 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def raw3621step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def raw3622 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, -1, -1], ![1, -2, 3, -2], ![1, 0, -2, 1]]

def raw3622step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![0, -1, 3, -2], ![2, -1, -2, 1]]

def raw3622step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, 0, -2], ![1, -1, 2, -2], ![1, 0, -2, 1]]

def raw3623 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw3623step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![0, -1, 0, 1], ![2, -1, 0, -1]]

def raw3623step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -2, 1, 1], ![0, 1, 0, -1], ![-2, 1, 0, 1]]

def raw3623step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw3624 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, 0, -2], ![1, -2, 2, -1], ![1, 0, -2, 1]]

def raw3624step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -2, 0, 2], ![-1, 2, -2, 1], ![-1, 0, 2, -1]]

def raw3624step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, -1, 0, -1]]

def raw3625 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, 2, -4], ![1, -2, -1, 2], ![1, 0, -1, 0]]

def raw3625step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![0, 2, -1, -1], ![2, -4, 2, 0]]

def raw3625step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -2, 1, 0]]

def raw3626 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, 2, -4], ![1, -2, 0, 1], ![1, 0, -2, 1]]

def raw3626step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -2, -2, 4], ![-1, 2, 0, -1], ![-1, 0, 2, -1]]

def raw3626step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw3627 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, 2, -4], ![1, -1, -2, 2], ![1, -1, 0, 0]]

def raw3627step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![0, 2, -2, 0], ![2, -4, 2, 0]]

def raw3627step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -2, 1, 0]]

def raw3628 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, 2, -4], ![1, -1, -1, 1], ![1, -1, -1, 1]]

def raw3628step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -2, -2, 4], ![-1, 1, 1, -1], ![-1, 1, 1, -1]]

def raw3628step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def raw3629 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -3, 3, -1], ![1, 3, -3, -1]]

def raw3629step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 3, -3], ![2, -1, -1]]

def raw3630 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -2, -1, 2], ![0, 1, 3, -4], ![1, 1, -2, 0]]

def raw3630step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 1, 1], ![0, -1, 3, -2], ![2, 2, -4, 0]]

def raw3630step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 2, -1, -1], ![0, 1, -3, 2], ![-2, -2, 4, 0]]

def raw3630step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 2, 1, -3], ![2, -1, -1, 0]]

def raw3631 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -2, -1, 2], ![0, 2, -2, 0], ![1, 0, 3, -4]]

def raw3631step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 2, 0], ![0, -1, -2, 3], ![2, 2, 0, -4]]

def raw3631step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 2, -2, 0], ![0, 1, 2, -3], ![-2, -2, 0, 4]]

def raw3631step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 2, 1, -3], ![2, 0, -1, -1]]

def raw3632 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -2, 0, 1], ![0, 1, -2, 1], ![1, 1, 2, -4]]

def raw3632step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 2, 0, -1], ![0, -1, 2, -1], ![-1, -1, -2, 4]]

def raw3632step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw3633 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -2, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw3633step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 2, -1, 0], ![0, -1, -1, 2], ![-1, -1, 2, 0]]

def raw3633step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, -1, -1, 0]]

def raw3634 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -2, 1, 0], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def raw3634step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 2, -1, 0], ![0, -2, 2, 0], ![-1, 0, -1, 2]]

def raw3634step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw3635 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -2, 2, -1], ![0, 1, 1, -2], ![1, 1, -3, 1]]

def raw3635step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 1, -3, 1]]

def raw3636 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -2, 2, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw3636step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 2, 0], ![0, 2, -1, -1], ![2, -1, -1, 0]]

def raw3636step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw3637 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -2, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw3637step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 2, -2, 1], ![0, -2, 0, 2], ![-1, 0, 2, -1]]

def raw3637step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, -1, 0, -1]]

def raw3638 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -2, 2, -1], ![1, 2, -2, -1]]

def raw3638step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]

def raw3639 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, -3, 2], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw3639step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, 3, -2], ![0, -1, -3, 4], ![-1, 1, 0, 0]]

def raw3639step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 3, -2], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw3640 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, -2, 1], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def raw3640step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, 2, -1], ![0, -1, -3, 4], ![-1, 1, 1, -1]]

def raw3640step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw3641 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, -2, 1], ![0, 2, -1, -1], ![1, -2, 3, -2]]

def raw3641step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, -2, -1, 3], ![2, 1, -1, -2]]

def raw3641step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, 0, -2], ![1, -1, 2, -2], ![1, 0, -2, 1]]

def raw3642 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 1, -3, 1], ![0, 1, 1, -2], ![1, -2, 2, -1]]

def raw3642step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 1, -3, 1]]

def raw3643 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 1, -3, 1], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw3643step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, 1, -2], ![0, -3, 3, 0], ![2, 1, -4, 1]]

def raw3643step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, -1, -1, 2], ![0, 3, -3, 0], ![-2, -1, 4, -1]]

def raw3643step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 3, -3], ![0, 2, -1, -1], ![2, -1, -1, 0]]

def raw3644 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-3, 2, 1, 0], ![5, -2, -2, -1]]

def raw3644step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1]]

def raw3644step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def raw3645 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 2, -2, 2], ![4, -2, 1, -3]]

def raw3645step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -2, 1], ![1, 2, -3]]

def raw3646 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 2, 1, -1], ![4, -2, -2, 0]]

def raw3646step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0]]

def raw3646step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def raw3647 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 3, -2, 1], ![4, -3, 1, -2]]

def raw3647step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, -2, 1], ![1, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical114
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3648 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, -2, 1, 2], ![3, 2, -2, -3]]

def raw3648step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 1, -2], ![1, 2, -3]]

def raw3649 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, -2, 2, 1], ![3, 2, -3, -2]]

def raw3649step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 2, -3], ![1, 1, -2]]

def raw3649step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 1, -2], ![1, 2, -3]]

def raw3650 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, -2, 3, 0], ![3, 2, -4, -1]]

def raw3650step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 3, -4], ![1, 0, -1]]

def raw3650step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 3, -4]]

def raw3651 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -2, 1], ![3, -2, 1, -2]]

def raw3651step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def raw3652 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, 1, -2], ![3, -2, -2, 1]]

def raw3652step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, 1, -2], ![1, -2, 1]]

def raw3652step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def raw3653 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 3, -2, 0], ![3, -3, 1, -1]]

def raw3653step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw3654 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 4, -2, -1], ![3, -4, 1, 0]]

def raw3654step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 4, -4], ![1, -2, 1], ![1, -1, 0]]

def raw3655 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -3, 1, 2], ![2, 3, -2, -3]]

def raw3655step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 1, -2], ![1, 2, -3]]

def raw3656 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, -2, 4], ![2, 2, 1, -5]]

def raw3656step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -2, 1], ![1, 4, -5]]

def raw3657 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, -1, 3], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw3657step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw3658 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, -1, 3], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def raw3658step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 1, 1, -3]]

def raw3659 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 0, 2], ![0, 0, -1, 1], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def raw3659step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 0, -1, 1], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def raw3660 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 0, 2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw3660step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw3661 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 0, 2], ![1, 1, -2, 0], ![1, 1, 1, -3]]

def raw3661step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![1, 0, -2, 1], ![1, 2, 0, -3]]

def raw3661step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 2, -1, -1], ![-1, 0, 2, -1], ![-1, -2, 0, 3]]

def raw3661step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw3662 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw3663 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw3664 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 1, -1, -1], ![1, 0, 0, -1]]

def raw3664step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw3665 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw3665step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw3666 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def raw3666step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![1, 1, 0, -2], ![1, 1, -1, -1]]

def raw3666step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, -1, -1], ![-1, -1, 0, 2], ![-1, -1, 1, 1]]

def raw3666step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw3667 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw3667step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 2, -1, -1], ![0, -2, 2, 0], ![-1, 0, 0, 1], ![-1, 0, 0, 1]]

def raw3667step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw3668 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw3668step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw3669 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw3669step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def raw3670 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![1, 0, -1, 0], ![1, 2, -1, -2]]

def raw3670step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 0, 2], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def raw3670step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 2, 0, -2], ![-1, -1, 1, 1], ![-1, -1, 0, 2]]

def raw3670step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw3671 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![1, 0, 0, -1], ![1, 2, -2, -1]]

def raw3671step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 0, 2], ![1, 1, 0, -2], ![1, 1, -1, -1]]

def raw3671step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 2, 0, -2], ![-1, -1, 0, 2], ![-1, -1, 1, 1]]

def raw3671step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw3672 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def raw3673 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def raw3674 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![2, 2, -2, -2]]

def raw3674step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]

def raw3675 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 2, 0], ![2, 2, -3, -1]]

def raw3675step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1]]

def raw3675step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![-1, -2, 3], ![-1, 0, 1]]

def raw3675step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

def raw3676 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 3, -1], ![2, 2, -4, 0]]

def raw3676step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 3, -4], ![1, -1, 0]]

def raw3676step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

def raw3677 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -2, 3], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw3678 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -2, 3], ![1, -1, 0, 0], ![1, 2, 1, -4]]

def raw3678step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![1, -2, 0, 1], ![1, 3, 0, -4]]

def raw3678step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw3679 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -2, 3], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw3679step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 2, -3], ![-1, 0, 1, 0], ![-1, -1, -2, 4]]

def raw3679step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical115
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3680 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw3680step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 1, -2], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![-1, -1, -2, 4]]

def raw3680step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw3681 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw3682 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 1, -2, 1], ![2, 0, 2, -4]]

def raw3682step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw3683 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 2, -3]]

def raw3684 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def raw3685 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw3686 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 2, -3]]

def raw3686step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw3687 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![2, 0, 1, -3]]

def raw3687step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw3688 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw3688step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw3689 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw3689step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def raw3690 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 2, -2, 0], ![2, -1, 2, -3]]

def raw3690step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![1, -1, -2, 2], ![1, 2, 0, -3]]

def raw3690step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, -2, 1], ![-1, 1, 2, -2], ![-1, -2, 0, 3]]

def raw3690step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, 0, -2], ![1, -1, 2, -2], ![1, 0, -2, 1]]

def raw3691 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![1, -1, -1, 1], ![1, 2, 1, -4]]

def raw3691step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 1, -2], ![-1, 1, 1, -1], ![-1, -2, -1, 4]]

def raw3691step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def raw3692 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![1, -1, 0, 0], ![1, 2, 0, -3]]

def raw3692step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw3693 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![1, 0, -2, 1], ![1, 1, 2, -4]]

def raw3693step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 1, -2], ![-1, 0, 2, -1], ![-1, -1, -2, 4]]

def raw3693step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw3694 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw3694step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 1, -2], ![-1, 0, 1, 0], ![-1, -1, -1, 3]]

def raw3694step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw3695 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw3695step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 1, -2]]

def raw3696 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw3696step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw3697 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![1, 1, -1, -1], ![1, 0, 1, -2]]

def raw3697step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw3698 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, -1, -1, 2], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def raw3698step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, -1, 0, 1], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def raw3699 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw3700 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, 1, -3]]

def raw3700step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 0, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![0, -2, -1, 3]]

def raw3700step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw3701 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw3701step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 0, -1], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![-1, -1, -1, 3]]

def raw3701step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw3702 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 1, -1, -1], ![1, 0, 1, -2]]

def raw3702step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 0, -1], ![0, 0, 1, -1], ![-1, -1, 1, 1], ![-1, 0, -1, 2]]

def raw3702step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw3703 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def raw3704 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw3704step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw3705 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw3705step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 0, -1], ![0, -1, 1, 0], ![-1, 0, 0, 1], ![-1, 0, 0, 1]]

def raw3705step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw3706 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw3706step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw3707 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![1, 0, -2, 1], ![1, 1, 1, -3]]

def raw3707step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 0, -1], ![-1, 0, 2, -1], ![-1, -1, -1, 3]]

def raw3707step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw3708 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw3708step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 0, -1], ![-1, 0, 1, 0], ![-1, -1, 0, 2]]

def raw3708step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw3709 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw3709step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 0, -1], ![-1, 0, 0, 1], ![-1, -1, 1, 1]]

def raw3709step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 1, -1]]

def raw3710 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![1, 1, -2, 0], ![1, 0, 1, -2]]

def raw3710step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 0, -1], ![-1, -1, 2, 0], ![-1, 0, -1, 2]]

def raw3710step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw3711 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw3711step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, -1, 0], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![-1, -1, 0, 2]]

def raw3711step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical116
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3712 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw3712step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, -1, 0], ![0, 0, 1, -1], ![-1, 0, 0, 1], ![-1, -1, 1, 1]]

def raw3712step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw3713 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def raw3713step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw3714 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw3714step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, -1, 0], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, -1, 1, 1]]

def raw3714step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 1, -1, -1]]

def raw3715 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw3715step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, -1, 0], ![0, -1, 1, 0], ![-1, 0, 1, 0], ![-1, 0, 0, 1]]

def raw3715step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw3716 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, -1, 0]]

def raw3716step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, -1, 0], ![0, -1, 1, 0], ![-1, 0, 0, 1], ![-1, 0, 1, 0]]

def raw3716step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw3717 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def raw3717step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw3718 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw3718step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, -1, 0], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, -1, 2, 0]]

def raw3718step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw3719 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw3719step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw3720 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw3720step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def raw3721 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, -1, 0, 0]]

def raw3721step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def raw3722 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 1, 0], ![0, 2, -1, -1], ![2, -1, -1, 0]]

def raw3722step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, -1, 0], ![0, -2, 1, 1], ![-2, 1, 1, 0]]

def raw3722step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw3723 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, -1, -2, 1]]

def raw3723step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, -2, 1], ![0, -2, 1, 1], ![-2, 1, 2, -1]]

def raw3723step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def raw3724 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -3, 3], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw3724step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 3, -3], ![-1, 1, 0, 0], ![-1, -1, -2, 4]]

def raw3724step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 3, -3], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def raw3725 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -3, 3], ![1, -1, 1, -1], ![1, 1, 1, -3]]

def raw3725step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 3, -3], ![-1, 1, -1, 1], ![-1, -1, -1, 3]]

def raw3725step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw3726 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw3727 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -2, 1, -1]]

def raw3728 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 1, 2, -4]]

def raw3729 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![2, -1, 2, -3]]

def raw3729step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![1, -2, -1, 2], ![1, 2, 0, -3]]

def raw3729step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw3730 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def raw3730step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 2, -2], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-2, 2, -1, 1]]

def raw3730step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, -1, 0, -1]]

def raw3731 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 1, -1, -1]]

def raw3732 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw3732step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 2, -2], ![0, -1, 0, 1], ![-1, 1, -1, 1], ![-1, 0, 0, 1]]

def raw3732step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw3733 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![2, -1, 1, -2]]

def raw3733step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 2, -2], ![0, -1, 0, 1], ![-2, 1, -1, 2]]

def raw3733step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw3734 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def raw3734step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 2, -2], ![0, -1, -1, 2], ![-2, 1, 0, 1]]

def raw3734step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw3735 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 2, -1, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw3735step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 2, -2], ![0, -2, 1, 1], ![-1, 2, -2, 1], ![-1, 0, 0, 1]]

def raw3735step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, -1, -2, 1]]

def raw3736 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 2, -1, -1], ![2, -2, 2, -2]]

def raw3736step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![1, -2, -1, 2], ![1, 2, -1, -2]]

def raw3736step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, -1, 1, -2]]

def raw3737 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, -2, 1, -1]]

def raw3737step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 2, -2], ![0, -2, 0, 2], ![-2, 2, -1, 1]]

def raw3737step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, -1, 0, -1]]

def raw3738 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![1, -2, 0, 1], ![1, 2, 1, -4]]

def raw3738step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 2, -2], ![-1, 2, 0, -1], ![-1, -2, -1, 4]]

def raw3738step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw3739 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![1, -2, 2, -1], ![1, 2, -1, -2]]

def raw3739step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 2, -2], ![-1, 2, -2, 1], ![-1, -2, 1, 2]]

def raw3739step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, -1, -2, 1]]

def raw3740 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def raw3740step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 2, -2], ![-1, 1, 1, -1], ![-1, -1, -2, 4]]

def raw3740step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def raw3741 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw3741step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 2, -2], ![-1, 1, 0, 0], ![-1, -1, -1, 3]]

def raw3741step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw3742 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def raw3742step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 2, -2], ![-1, 1, -1, 1], ![-1, -1, 0, 2]]

def raw3742step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw3743 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![1, -1, 2, -2], ![1, 1, -1, -1]]

def raw3743step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 2, -2], ![-1, 1, -2, 2], ![-1, -1, 1, 1]]

def raw3743step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, -1, -1], ![1, -1, 2, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical117
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3744 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![2, -1, 2, -3]]

def raw3744step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-2, 1, -2, 3]]

def raw3744step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -2, 3, -2]]

def raw3745 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def raw3745step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![-1, -1, -2, 4]]

def raw3745step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def raw3746 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw3746step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, -1, -1, 3]]

def raw3746step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw3747 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, -2, 0, 1], ![1, 1, 2, -4]]

def raw3748 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 0, -1, 1], ![2, -1, 2, -3]]

def raw3748step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![0, 0, 1, -1], ![-2, 1, -2, 3]]

def raw3748step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -2, 3, -2]]

def raw3749 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def raw3749step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw3750 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def raw3750step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-2, 2, -1, 1]]

def raw3750step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw3751 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, -1, 2], ![1, 1, 2, -4]]

def raw3752 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 1, 1, -3]]

def raw3752step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw3753 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 2, -3]]

def raw3753step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-1, 1, 1, -1], ![-1, 0, -2, 3]]

def raw3753step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 3, -2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw3754 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw3754step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw3755 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw3755step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw3756 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw3756step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw3757 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw3757step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 1, -1], ![0, -1, -1, 2], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw3757step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw3758 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![1, -1, -2, 2], ![1, 1, 2, -4]]

def raw3758step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 1, -1], ![-1, 1, 2, -2], ![-1, -1, -2, 4]]

def raw3758step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 2, -2]]

def raw3759 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def raw3759step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![-1, -1, -1, 3]]

def raw3759step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def raw3760 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw3760step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 1, -1], ![-1, 1, -1, 1], ![-1, -1, 1, 1]]

def raw3760step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def raw3761 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 0, 0], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def raw3761step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![0, 0, 1, 1, -2], ![1, 0, -2, 0, 1], ![1, 0, 1, -1, -1]]

def raw3761step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, 0, -2], ![0, 0, -1, -1, 2], ![-1, 0, 2, 0, -1], ![-1, 0, -1, 1, 1]]

def raw3761step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![-1, 2, 0, -1], ![-1, -1, 1, 1]]

def raw3761step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw3762 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 0, 0], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw3762step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![1, 0, 1, -2], ![1, 0, -1, 0]]

def raw3762step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0]]

def raw3762step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]

def raw3763 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def raw3763step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, -1, 1], ![0, 0, 0, 0], ![-1, 1, 1, -1], ![-1, -1, 1, 1]]

def raw3763step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, -1, 1], ![-1, 1, 1, -1], ![-1, -1, 1, 1]]

def raw3763step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def raw3764 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw3764step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, -1, 1], ![0, 0, 0, 0], ![-1, 1, 0, 0], ![-1, -1, 2, 0]]

def raw3764step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, -1, 2, 0]]

def raw3764step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw3765 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 1, -1], ![0, 1, -3, 2], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def raw3765step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, -2, -1, 1]]

def raw3766 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def raw3766step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw3767 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -2, 0, 0]]

def raw3767step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, -1, 1], ![0, -1, 2, -1], ![0, -1, 0, 1], ![-2, 2, 0, 0]]

def raw3767step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -1, -1, 0]]

def raw3768 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw3768step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, -1, 1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw3768step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw3769 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -1, -1, 0]]

def raw3769step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw3770 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, -1, 2], ![1, 1, -1, -1]]

def raw3770step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw3771 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 0, 1], ![1, 1, -2, 0]]

def raw3771step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw3772 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw3772step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw3773 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw3773step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw3774 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def raw3774step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, -1, 1], ![0, -2, 1, 1], ![-1, 2, 0, -1], ![-1, 0, 1, 0]]

def raw3774step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -1, -1, 0]]

def raw3775 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, -1, 1]]

def raw3775step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical118
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3776 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -2, -1, 1]]

def raw3776step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![1, 1, -1, -1], ![1, -1, -1, 1]]

def raw3776step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw3777 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 1, -1], ![1, -1, -3, 3], ![1, 1, 1, -3]]

def raw3777step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, -1, 1], ![-1, 1, 3, -3], ![-1, -1, -1, 3]]

def raw3777step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 3, -3]]

def raw3778 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw3778step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, -1, 2, 0]]

def raw3778step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw3779 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, -3, 1]]

def raw3779step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, -1, 1], ![-1, 1, -1, 1], ![-1, -1, 3, -1]]

def raw3779step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def raw3780 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, -1, -1, 0]]

def raw3780step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, -2, 2], ![0, -1, 2, -1], ![-2, 1, 1, 0]]

def raw3780step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw3781 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -1, -2, 1]]

def raw3781step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, -2, 2], ![0, -1, 1, 0], ![-2, 1, 2, -1]]

def raw3781step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw3782 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, -2, -2, 2]]

def raw3782step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![1, 2, -1, -2], ![1, -2, -1, 2]]

def raw3782step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, -1, 1, -2]]

def raw3783 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 2, -2], ![1, -1, -3, 3], ![1, 1, 0, -2]]

def raw3783step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, -2, 2], ![-1, 1, 3, -3], ![-1, -1, 0, 2]]

def raw3783step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, -1, -1], ![1, -1, 3, -3]]

def raw3784 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 1, -2, 0]]

def raw3784step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, -2, 2], ![-1, 1, 1, -1], ![-1, -1, 2, 0]]

def raw3784step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw3785 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, -3, 1]]

def raw3785step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, -2, 2], ![-1, 1, 0, 0], ![-1, -1, 3, -1]]

def raw3785step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw3786 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -3, 2], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw3787 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -3, 2], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw3787step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![1, -3, 0, 2], ![1, 2, -1, -2]]

def raw3787step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![-1, 3, 0, -2], ![-1, -2, 1, 2]]

def raw3787step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 3, -2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw3788 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -3, 2], ![0, 1, 1, -2], ![2, -2, 1, -1]]

def raw3788step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![1, -3, 1, 1], ![1, 2, -2, -1]]

def raw3788step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 1, -3, 1]]

def raw3789 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -3, 2], ![1, -2, 0, 1], ![1, 1, 2, -4]]

def raw3790 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -3, 2], ![1, -2, 1, 0], ![1, 1, 1, -3]]

def raw3791 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -3, 2], ![1, -2, 2, -1], ![1, 1, 0, -2]]

def raw3792 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -3, 2], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw3792step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 3, -2], ![-1, 1, 0, 0], ![-1, 0, -2, 3]]

def raw3792step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def raw3793 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -3, 2], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw3793step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 3, -2], ![-1, 1, -1, 1], ![-1, 0, -1, 2]]

def raw3793step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def raw3794 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -3, 2], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def raw3794step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 3, -2], ![-1, 1, -2, 2], ![-1, 0, 0, 1]]

def raw3794step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, -1, 2, -2]]

def raw3795 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw3795step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw3796 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def raw3796step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![1, -2, -1, 2], ![1, 1, 0, -2]]

def raw3796step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 1, 0, -2]]

def raw3797 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 0, 0, -1]]

def raw3797step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw3798 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def raw3798step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw3799 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw3799step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 1, -1, -1]]

def raw3800 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw3801 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -2, 0, 0]]

def raw3801step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 2, -1], ![0, -1, -1, 2], ![-2, 2, 0, 0]]

def raw3801step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, -1, -1, 0]]

def raw3802 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 1, 2, -3], ![2, -2, -1, 1]]

def raw3802step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 1, -3, 1]]

def raw3803 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![1, -2, -1, 2], ![1, 1, 2, -4]]

def raw3804 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![1, -2, 0, 1], ![1, 1, 1, -3]]

def raw3805 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![1, -2, 2, -1], ![1, 1, -1, -1]]

def raw3805step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def raw3806 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw3806step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 2, -1], ![-1, 1, 0, 0], ![-1, 0, -1, 2]]

def raw3806step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw3807 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw3807step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 2, -1], ![-1, 1, -1, 1], ![-1, 0, 0, 1]]

def raw3807step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 1, -1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical119
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3808 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![1, 0, 1, -2], ![1, -1, 0, 0]]

def raw3808step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 2, -1], ![-1, 0, -1, 2], ![-1, 1, 0, 0]]

def raw3808step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw3809 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw3809step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw3810 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 0, -1, 1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw3810step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw3811 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 0, 0, 0], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw3811step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw3811step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw3812 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw3812step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw3812step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw3813 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 1, -2]]

def raw3813step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw3814 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 0, 0, -1]]

def raw3814step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-1, 2, -1, 0], ![-1, 0, 0, 1]]

def raw3814step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw3815 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw3815step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 1, -1, 1]]

def raw3815step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1]]

def raw3816 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, -1, 0, 0]]

def raw3816step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-1, 1, -1, 1], ![-1, 1, 0, 0]]

def raw3816step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1]]

def raw3817 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def raw3817step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 2, -1, 0], ![-1, 0, 1, 0]]

def raw3817step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw3818 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 1, -1]]

def raw3819 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw3819step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 1, 0, 0]]

def raw3819step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def raw3820 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, -1, -1, 1]]

def raw3820step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 1, -1]]

def raw3821 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def raw3821step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw3822 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw3822step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 1, -1, -1]]

def raw3823 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, -1, 1]]

def raw3823step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 1, -1, -1]]

def raw3824 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -2, -1, 1]]

def raw3824step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 0, -2, 1]]

def raw3824step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![-1, 1, -1, 1], ![-1, 0, 2, -1]]

def raw3824step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw3825 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, -2, -2, 2]]

def raw3825step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![1, -1, 2, -2], ![1, 0, -3, 2]]

def raw3825step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![-1, 1, -2, 2], ![-1, 0, 3, -2]]

def raw3825step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 3, -2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw3826 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![1, -2, -2, 3], ![1, 1, 2, -4]]

def raw3826step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![1, -1, -2, 2], ![1, 0, 3, -4]]

def raw3826step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 2, -1], ![-1, 1, 2, -2], ![-1, 0, -3, 4]]

def raw3826step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 4, -3], ![0, 2, -1, -1], ![1, -1, -2, 2]]

def raw3827 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![1, -2, -1, 2], ![1, 1, 1, -3]]

def raw3827step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![1, -1, -1, 1], ![1, 0, 2, -3]]

def raw3827step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 2, -1], ![-1, 1, 1, -1], ![-1, 0, -2, 3]]

def raw3827step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw3828 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 1, -1, -1]]

def raw3828step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 1, 0], ![-1, 2, -1, 0], ![-1, -1, 1, 1]]

def raw3828step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 1, -1, -1]]

def raw3829 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def raw3829step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw3830 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw3830step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw3831 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 0, -1], ![1, -2, 0, 1], ![1, 1, -1, -1]]

def raw3831step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 0, 1], ![-1, 2, 0, -1], ![-1, -1, 1, 1]]

def raw3831step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 1, -1, -1]]

def raw3832 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 1, -2, 0]]

def raw3832step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 0, 1], ![-1, 2, -1, 0], ![-1, -1, 2, 0]]

def raw3832step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw3833 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw3833step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw3834 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -2, 1]]

def raw3834step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw3835 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, -1, 1, -1]]

def raw3835step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw3836 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 1, -2], ![1, -2, 0, 1], ![1, 1, -2, 0]]

def raw3836step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![1, -2, 1, 0], ![1, 1, 0, -2]]

def raw3837 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 1, -3, 1]]

def raw3837step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![1, -2, 0, 1], ![1, 1, 1, -3]]

def raw3838 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw3838step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, -1, 2], ![-1, 1, 1, -1], ![-1, 0, 1, 0]]

def raw3838step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 1, -1, -1]]

def raw3839 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw3839step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, -1, 2], ![-1, 1, 0, 0], ![-1, 0, 2, -1]]

def raw3839step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]

def raw384step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]

def raw384step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw385 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]

def raw385step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![2, 0, -2]]

def raw386 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]

def raw386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]

def raw386step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]

def raw387 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]

def raw387step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]

def raw387step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

def raw388 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]

def raw388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]

def raw388step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

def raw389 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]

def raw389step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, -1, 2], ![-2, 2, 0], ![-2, 1, 1]]

def raw389step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

def raw390 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]

def raw390step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 3, -3], ![2, 0, -2]]

def raw391 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]

def raw391step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, 1, 1], ![-3, 1, 2]]

def raw391step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 1, -2], ![1, 2, -3]]

def raw392 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]

def raw392step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![2, 0, -2]]

def raw393 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 1, -3], ![3, -3, 0]]

def raw393step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, -1, 3], ![-3, 3, 0]]

def raw393step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![3, -1, -2]]

def raw394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]

def raw394step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]

def raw394step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]

def raw395 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]

def raw395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]

def raw395step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]

def raw396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]

def raw396step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]

def raw396step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]

def raw397 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]

def raw397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]

def raw397step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 2, -3]]

def raw398 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]

def raw398step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]

def raw398step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]

def raw399 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]

def raw399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]

def raw400 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]

def raw400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]

def raw400step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]

def raw401 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -2, 0], ![3, -1, -2]]

def raw401step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-2, 2, 0], ![-3, 1, 2]]

def raw401step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]

def raw402 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![3, -2, -1]]

def raw402step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-2, 1, 1], ![-3, 2, 1]]

def raw402step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![1, 1, -2], ![1, 2, -3]]

def raw411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]

def raw411step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def raw412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]

def raw412step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def raw413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]

def raw413step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]

def raw413step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]

def raw414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]

def raw414step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def raw415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]

def raw415step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical120
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3840 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 0, -3, 2]]

def raw3840step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, -1, 2], ![-1, 1, -1, 1], ![-1, 0, 3, -2]]

def raw3840step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw3841 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 2, -3], ![1, -2, 0, 1], ![1, 1, -3, 1]]

def raw3841step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -3, 2], ![1, -2, 1, 0], ![1, 1, 1, -3]]

def raw3842 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -3, 2]]

def raw3842step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, -2, 3], ![-1, 1, 0, 0], ![-1, 0, 3, -2]]

def raw3842step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def raw3843 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -4, 2], ![2, -2, 3, -3]]

def raw3843step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -4, 3], ![1, 2, -3]]

def raw3844 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -3, 1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw3844step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![1, -3, 2, 0], ![1, 1, -1, -1]]

def raw3844step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw3845 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -3, 1], ![2, -2, 2, -2]]

def raw3845step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

def raw3846 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw3846step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![1, -2, 0, 1], ![1, 0, 0, -1]]

def raw3846step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw3847 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![2, -2, 1, -1]]

def raw3847step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

def raw3847step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1]]

def raw3847step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

def raw3848 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def raw3848step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw3849 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, -1, 1, -1]]

def raw3850 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw3850step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 1, -2, 0]]

def raw3851 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, -1, -1, 1]]

def raw3851step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, -1, 1, -1]]

def raw3852 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 3, -4, 1], ![2, -3, 3, -2]]

def raw3852step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -4, 3], ![1, 1, -2]]

def raw3853 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 3, -2, -1], ![2, -3, 1, 0]]

def raw3853step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

def raw3854 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 4, -2, -2], ![2, -4, 1, 1]]

def raw3854step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![1, -2, 1], ![1, -2, 1]]

def raw3855 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -3, 1, 1], ![1, 3, -2, -2]]

def raw3855step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]

def raw3856 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -2, -2, 3], ![1, 2, 1, -4]]

def raw3856step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -2, 1], ![1, 3, -4]]

def raw3857 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -2, -1, 2], ![0, 1, -2, 1], ![1, 1, 2, -4]]

def raw3857step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![1, -2, -1, 2], ![1, 1, 2, -4]]

def raw3858 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -2, 1, 0], ![1, 2, -2, -1]]

def raw3858step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]

def raw3858step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw3859 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -2, 2, -1], ![1, 2, -3, 0]]

def raw3859step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 2, -3], ![1, -1, 0]]

def raw3859step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

def raw3860 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -2, 3, -2], ![1, 2, -4, 1]]

def raw3860step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 3, -4], ![1, -2, 1]]

def raw3860step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -2, 1], ![1, 3, -4]]

def raw3861 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw3861step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 2, -1], ![0, -1, -1, 2], ![-1, 1, 0, 0]]

def raw3861step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw3862 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 2, -3, 0], ![1, -2, 2, -1]]

def raw3862step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1]]

def raw3862step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

def raw3863 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 2, -2, -1], ![1, -2, 1, 0]]

def raw3863step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]

def raw3863step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw3864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]

def raw3864step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def raw3865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]

def raw3865step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def raw3867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]

def raw3867step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0], ![-2, 1, 1]]

def raw3867step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

def raw3868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]

def raw3868step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -2, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]

def raw3868step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]

def raw3869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]

def raw3869step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

def raw3870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]

def raw3870step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]

def raw3870step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw3871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]

def raw3871step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical121
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]

def raw3872step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def raw3873 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]

def raw3873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def raw3874 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]

def raw3874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def raw3875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]

def raw3875step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]

def raw3875step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

def raw3876 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]

def raw3876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

def raw3877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw3877step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]

def raw3877step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw3878 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]

def raw3878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def raw3879 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]

def raw3879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def raw3880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]

def raw3880step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

def raw3881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]

def raw3881step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

def raw3882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]

def raw3882step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]

def raw3882step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw3883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]

def raw3883step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]

def raw3883step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw3884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]

def raw3884step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]

def raw3884step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

def raw3885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw3885step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]

def raw3885step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def raw3886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]

def raw3886step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]

def raw3886step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw3887 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]

def raw3887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]

def raw3887step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def raw3888 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]

def raw3888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]

def raw3888step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]

def raw3889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def raw3889step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]

def raw3889step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw3890 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]

def raw3890step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]

def raw3890step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw3891 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]

def raw3891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]

def raw3891step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw3892 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]

def raw3892step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![2, 0, -2]]

def raw3893 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]

def raw3893step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-2, 1, 1], ![-2, 1, 1]]

def raw3893step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]

def raw3894 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

def raw3894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]

def raw3895 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

def raw3895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]

def raw3895step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def raw3896 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]

def raw3896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]

def raw3896step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def raw3897 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]

def raw3897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 2, -1], ![-2, -1, 3]]

def raw3897step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]

def raw3898 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

def raw3898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]

def raw3898step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def raw3899 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

def raw3899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]

def raw3899step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def raw3900 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

def raw3901 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![2, -2, 0], ![1, 1, -2]]

def raw3901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

def raw3902 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]

def raw3902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -3, 3], ![-1, 2, -1], ![-2, 0, 2]]

def raw3902step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

def raw3903 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]

def raw3903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -3, 3], ![-1, 0, 1], ![-2, 2, 0]]

def raw3903step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical122
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3904 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]

def raw3904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -3, 4]]

def raw3904step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

def raw3905 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 1, -2], ![1, -1, 0], ![1, 1, -2]]

def raw3905step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-1, -1, 2], ![-1, 1, 0], ![-1, -1, 2]]

def raw3905step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def raw3906 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 2, -3], ![2, -1, -1]]

def raw3906step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-1, -2, 3], ![-2, 1, 1]]

def raw3906step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def raw3907 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 3, -4], ![2, -2, 0]]

def raw3907step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-1, -3, 4], ![-2, 2, 0]]

def raw3907step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

def raw3908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]

def raw3908step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw3909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]

def raw3909step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

def raw3910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]

def raw3910step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

def raw3911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]

def raw3911step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]

def raw3911step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw3912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]

def raw3912step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]

def raw3912step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw3913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]

def raw3913step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

def raw3914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]

def raw3914step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def raw3916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]

def raw3916step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-2, -3, 5]]

def raw3916step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def raw3917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]

def raw3917step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -3, 4]]

def raw3917step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw3920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

def raw3920step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

def raw3921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]

def raw3921step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

def raw3922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]

def raw3926 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]

def raw3926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]

def raw3927 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]

def raw3927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]

def raw3927step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def raw3928 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

def raw3928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def raw3932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]

def raw3932step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]

def raw3932step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]

def raw3933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]

def raw3933step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw3934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]

def raw3934step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]

def raw3934step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw3935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]

def raw3935step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical123
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3936 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]

def raw3936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1]]

def raw3936step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]

def raw3937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]

def raw3937step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]

def raw3938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]

def raw3938step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]

def raw3938step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

def raw3939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]

def raw3939step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]

def raw3939step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw3940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]

def raw3940step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-2, -2, 4]]

def raw3940step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

def raw3941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

def raw3941step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw3942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def raw3942step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw3943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]

def raw3944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

def raw3946 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]

def raw3946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

def raw3948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]

def raw3949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]

def raw3950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]

def raw3950step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw3951 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]

def raw3951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw3952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![2, 1, -3]]

def raw3952step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![-2, -1, 3]]

def raw3952step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

def raw3953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw3953step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]

def raw3953step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw3954 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

def raw3954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]

def raw3954step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw3955 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]

def raw3955step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw3956 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

def raw3957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]

def raw3957step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

def raw3958 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]

def raw3958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def raw3959 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

def raw3959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw3960 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

def raw3960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]

def raw3960step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw3963 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]

def raw3963step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]

def raw3963step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

def raw3964 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]

def raw3964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def raw3965 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]

def raw3966 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]

def raw3966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]

def raw3966step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw3967 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]

def raw3967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical124
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3968 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]

def raw3968step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]

def raw3968step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]

def raw3969 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]

def raw3969step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

def raw3970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

def raw3971 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]

def raw3972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]

def raw3972step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]

def raw3972step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0]]

def raw3973 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]

def raw3973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]

def raw3974 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]

def raw3974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]

def raw3974step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]

def raw3975 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]

def raw3975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw3976 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]

def raw3976step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]

def raw3977 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw3977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]

def raw3977step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

def raw3978 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]

def raw3978step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]

def raw3978step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw3979 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]

def raw3979step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

def raw3980 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]

def raw3980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -3, 2], ![0, 2, -2], ![-1, 0, 1], ![-2, 1, 1]]

def raw3980step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]

def raw3981 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -3, 2], ![1, -1, 0], ![1, 1, -2]]

def raw3982 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]

def raw3982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]

def raw3983 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -3, 2], ![2, 0, -2]]

def raw3983step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]

def raw3984 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

def raw3984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -3, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]

def raw3984step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]

def raw3985 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]

def raw3985step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -3, 2], ![-1, 2, -1], ![-2, 1, 1]]

def raw3985step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

def raw3986 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![2, -4, 2], ![1, 1, -2]]

def raw3986step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -3, 2], ![-2, 4, -2], ![-1, -1, 2]]

def raw3986step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 2, -3], ![2, -2, 0]]

def raw3987 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![0, -2, 2], ![1, -1, 0], ![2, -1, -1]]

def raw3988 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![0, -2, 2], ![2, -2, 0], ![1, 0, -1]]

def raw3988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -4, 3], ![0, 2, -2], ![-2, 2, 0], ![-1, 0, 1]]

def raw3988step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 3, -4], ![2, -2, 0]]

def raw3989 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![0, -2, 2], ![3, -2, -1]]

def raw3989step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -4, 3], ![0, 2, -2], ![-3, 2, 1]]

def raw3989step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 3, -4], ![2, -2, 0]]

def raw3990 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![1, -3, 2], ![1, -1, 0], ![1, 0, -1]]

def raw3991 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![1, -3, 2], ![2, -1, -1]]

def raw3992 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![1, -2, 1], ![1, -2, 1], ![1, 0, -1]]

def raw3993 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]

def raw3993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]

def raw3994 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![1, -2, 1], ![2, -2, 0]]

def raw3994step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

def raw3995 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![2, -4, 2], ![1, 0, -1]]

def raw3995step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -4, 3], ![-2, 4, -2], ![-1, 0, 1]]

def raw3995step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 3, -4], ![2, -2, 0]]

def raw3996 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![2, -2, 0], ![1, -2, 1]]

def raw3996step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

def raw3997 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]

def raw3997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![-2, -1, 3]]

def raw3997step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![2, 0, -2]]

def raw3998 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

def raw3999 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![1, -1, 0], ![1, 3, -4]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical125
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4000 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

def raw4001 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

def raw4002 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 2, -2], ![0, 1, -1], ![2, 0, -2]]

def raw4002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

def raw4003 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def raw4004 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1]]

def raw4004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def raw4005 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 2, -2], ![2, 1, -3]]

def raw4005step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 3, -3], ![0, -2, 2], ![-2, -1, 3]]

def raw4005step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![2, 0, -2]]

def raw4006 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def raw4007 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 3, -3], ![2, 0, -2]]

def raw4008 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 4, -4], ![1, -1, 0], ![1, 0, -1]]

def raw4009 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 4, -4], ![2, -1, -1]]

def raw4010 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, -1, 0], ![1, 4, -5]]

def raw4011 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 0, -1], ![1, 3, -4]]

def raw4012 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 1, -2], ![1, 2, -3]]

def raw4013 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 2, -3], ![1, 1, -2]]

def raw4013step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 1, -2], ![1, 2, -3]]

def raw4014 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 3, -4], ![1, 0, -1]]

def raw4014step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 0, -1], ![1, 3, -4]]

def raw4015 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![2, 3, -5]]

def raw4015step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, 3, -3], ![-2, -3, 5]]

def raw4015step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 3, -3], ![2, 0, -2]]

def raw4016 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![-1, 3, -2], ![1, -1, 0], ![2, 0, -2]]

def raw4016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![1, -3, 2], ![-1, 1, 0], ![-2, 0, 2]]

def raw4016step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

def raw4017 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![-1, 3, -2], ![1, 0, -1], ![2, -1, -1]]

def raw4017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![1, -3, 2], ![-1, 0, 1], ![-2, 1, 1]]

def raw4017step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]

def raw4018 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 4, -5]]

def raw4019 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 3, -4]]

def raw4020 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 0, 0], ![0, 2, -2], ![2, 0, -2]]

def raw4020step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![2, 0, -2]]

def raw4021 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 3, -4]]

def raw4021step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

def raw4022 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 2, -3]]

def raw4022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]

def raw4022step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, -2, 3]]

def raw4022step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

def raw4023 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw4024 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def raw4025 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 3, -4]]

def raw4026 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw4027 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw4028 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1]]

def raw4028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw4029 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![2, 1, -3]]

def raw4029step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![0, -1, 1], ![-2, -1, 3]]

def raw4029step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

def raw4030 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![0, 0, 0], ![2, 0, -2]]

def raw4030step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![2, 0, -2]]

def raw4031 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![0, 1, -1], ![2, -1, -1]]

def raw4031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical126
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4032 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def raw4033 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw4033step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw4034 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![2, 0, -2]]

def raw4035 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw4036 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0]]

def raw4036step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw4037 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

def raw4038 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 4, -4], ![1, -2, 1], ![1, 0, -1]]

def raw4039 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

def raw4040 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 4, -4], ![2, -2, 0]]

def raw4041 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -2, 1], ![1, 4, -5]]

def raw4042 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

def raw4043 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 0, -1], ![1, 2, -3]]

def raw4043step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, -2, 3]]

def raw4043step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

def raw4044 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]

def raw4045 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1]]

def raw4045step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![-1, -2, 3], ![-1, 0, 1]]

def raw4045step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

def raw4046 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 3, -4], ![1, -1, 0]]

def raw4046step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

def raw4047 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 4, -5], ![1, -2, 1]]

def raw4047step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -2, 1], ![1, 4, -5]]

def raw4048 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![2, 2, -4]]

def raw4048step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![-2, -2, 4]]

def raw4048step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![2, 0, -2]]

def raw4049 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]

def raw4049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

def raw4050 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]

def raw4050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -3, 2], ![-1, 0, 1], ![-2, 2, 0]]

def raw4050step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

def raw4051 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 4, -5]]

def raw4051step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 4, -5]]

def raw4052 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 3, -4]]

def raw4052step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 3, -4]]

def raw4053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 4, -5]]

def raw4054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw4055 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 4, -5]]

def raw4056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 4, -4]]

def raw4056step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

def raw4057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![0, 3, -3]]

def raw4057step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw4058 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def raw4059 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]

def raw4059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -2, 3]]

def raw4059step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw4060 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2]]

def raw4060step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]

def raw4060step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

def raw4061 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]

def raw4061step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

def raw4062 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 3, -4]]

def raw4062step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -2, 1], ![1, 3, -4]]

def raw4063 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3]]

def raw4063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]

def raw4063step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, -2, 3]]

def raw4063step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical127
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4064 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2]]

def raw4064step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]

def raw4064step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2]]

def raw4064step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

def raw4065 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2]]

def raw4065step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]

def raw4065step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

def raw4066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw4067 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw4068 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def raw4069 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -3, 2], ![1, 3, -4]]

def raw4070 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

def raw4071 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw4072 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw4072step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw4073 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]

def raw4073step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw4074 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]

def raw4074step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

def raw4075 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]

def raw4075step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def raw4076 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def raw4077 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw4078 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]

def raw4078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw4079 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

def raw4080 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw4081 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw4082 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![2, -2, 0]]

def raw4083 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 4, -4], ![1, -3, 2], ![1, 0, -1]]

def raw4084 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 4, -4], ![1, -2, 1], ![1, -1, 0]]

def raw4085 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0], ![1, -2, 1]]

def raw4085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 4, -4], ![1, -2, 1], ![1, -1, 0]]

def raw4086 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -3, 2], ![1, 4, -5]]

def raw4087 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -2, 1], ![1, 3, -4]]

def raw4088 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]

def raw4088step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, -2, 3]]

def raw4088step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw4089 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]

def raw4089step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2]]

def raw4089step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

def raw4090 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]

def raw4090step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, -1, 2], ![-1, 0, 1]]

def raw4090step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

def raw4093 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

def raw4093step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

def raw4094 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw4094step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw4095 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw4095step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw4095step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical128
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4096 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]

def raw4096step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]

def raw4096step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -1, 0]]

def raw4097 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

def raw4097step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 0, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1]]

def raw4097step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1]]

def raw4097step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

def raw4098 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

def raw4098step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

def raw4098step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

def raw4099 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]

def raw4099step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]

def raw4100 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

def raw4100step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

def raw4101 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, -3, 2], ![1, 3, -4]]

def raw4101step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -3, 3], ![2, 0, 2, -4]]

def raw4101step1 : Matrix (Fin 3) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 3, -3], ![-2, 0, -2, 4]]

def raw4101step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![0, 3, -3], ![-2, -2, 4]]

def raw4101step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, -1, -1]]

def raw4102 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![1, 2, -3]]

def raw4102step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 0, 0], ![-1, 2, -1], ![-1, -2, 3]]

def raw4102step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![-1, -2, 3]]

def raw4102step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]

def raw4103 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]

def raw4103step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2]]

def raw4103step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![-1, -1, 2]]

def raw4103step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -1, 0]]

def raw4104 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]

def raw4104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]

def raw4105 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]

def raw4105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![1, -2, 1], ![-1, 1, 0], ![-2, 2, 0]]

def raw4105step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]

def raw4106 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]

def raw4106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw4107 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]

def raw4107step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

def raw4108 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]

def raw4108step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw4109 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]

def raw4109step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw4109step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0]]

def raw4110 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]

def raw4110step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]

def raw4110step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -1, 0]]

def raw4111 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]

def raw4111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw4112 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]

def raw4112step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

def raw4113 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]

def raw4113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 3, -1]]

def raw4113step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

def raw4114 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2]]

def raw4115 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

def raw4116 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]

def raw4117 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

def raw4118 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![0, -2, 2], ![2, -1, -1]]

def raw4118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def raw4119 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![0, -1, 1], ![2, -2, 0]]

def raw4119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def raw4120 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1]]

def raw4121 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]

def raw4122 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -2, 1]]

def raw4122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]

def raw4123 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]

def raw4123step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -2, 2], ![-2, 3, -1]]

def raw4123step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def raw4124 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 3, -3], ![1, -3, 2], ![1, -1, 0]]

def raw4125 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 3, -3], ![1, -2, 1], ![1, -2, 1]]

def raw4126 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -4, 3], ![1, 3, -4]]

def raw4127 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -3, 2], ![1, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical129
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4128 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]

def raw4128step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw4129 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]

def raw4129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]

def raw4130 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw4131 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw4131step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0]]

def raw4132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-1, 3, -2], ![1, -3, 2]]

def raw4132step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 1, -1], ![1, -3, 2], ![1, -1, 0], ![1, 0, -1]]

def raw4133 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]

def raw4133step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0]]

def raw4134 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]

def raw4134step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -1, 0]]

def raw4135 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]

def raw4135step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

def raw4136 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1]]

def raw4136step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1]]

def raw4137 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0]]

def raw4137step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]

def raw4138 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

def raw4139 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

def raw4139step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1]]

def raw4139step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

def raw4140 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

def raw4140step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

def raw4141 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]

def raw4142 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1]]

def raw4142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw4143 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -2, 2], ![2, -1, -1]]

def raw4143step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

def raw4144 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

def raw4145 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

def raw4146 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -1, 0], ![1, -2, 1]]

def raw4146step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

def raw4147 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![2, -3, 1]]

def raw4147step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, -3, 3], ![-2, 3, -1]]

def raw4147step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![2, -2, 0]]

def raw4148 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![1, -4, 3], ![1, 0, -1]]

def raw4149 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![1, -3, 2], ![1, -1, 0]]

def raw4150 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![1, -2, 1], ![1, -2, 1]]

def raw4151 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![2, -4, 2]]

def raw4151step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, -4, 4], ![-2, 4, -2]]

def raw4151step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 4, -4], ![2, -2, 0]]

def raw4152 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -4, 3], ![0, 4, -4], ![1, 0, -1]]

def raw4152step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![1, -4, 3], ![1, 0, -1]]

def raw4153 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -4, 3], ![1, 4, -5]]

def raw4153step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -4, 4], ![2, 3, -5]]

def raw4153step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![0, 4, -4], ![-2, -3, 5]]

def raw4153step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 4, -4], ![2, -1, -1]]

def raw4154 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -3, 2], ![0, 2, -2], ![1, 1, -2]]

def raw4154step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

def raw4155 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -3, 2], ![0, 3, -3], ![1, 0, -1]]

def raw4155step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

def raw4156 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -3, 2], ![0, 4, -4], ![1, -1, 0]]

def raw4156step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![1, -3, 2], ![1, -1, 0]]

def raw4157 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -3, 2], ![1, 3, -4]]

def raw4157step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![2, 2, -4]]

def raw4157step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![0, 3, -3], ![-2, -2, 4]]

def raw4157step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, -1, -1]]

def raw4158 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -2, 1], ![0, 4, -4], ![1, -2, 1]]

def raw4158step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![1, -2, 1], ![1, -2, 1]]

def raw4159 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -2, 1], ![1, 2, -3]]

def raw4159step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![-1, -2, 3]]

def raw4159step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw416 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]

def raw416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def raw417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]

def raw417step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]

def raw417step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]

def raw418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]

def raw418step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]

def raw418step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

def raw419 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]

def raw419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 2, 0], ![-3, 1, 2]]

def raw419step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]

def raw423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]

def raw423step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]

def raw425step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]

def raw426step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw427 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]

def raw427step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]

def raw428step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw429 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]

def raw429step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw430 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]

def raw430step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]

def raw430step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]

def raw431 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]

def raw431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw432 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]

def raw432step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw433 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]

def raw433step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]

def raw434 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]

def raw434step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]

def raw434step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

def raw436 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]

def raw436step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def raw437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw437step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw438 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]

def raw438step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

def raw439 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]

def raw439step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw440 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]

def raw440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw441 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]

def raw441step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw442 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]

def raw442step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

def raw443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]

def raw443step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]

def raw443step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

def raw444 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]

def raw444step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]

def raw444step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]

def raw445 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]

def raw445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]

def raw445step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]

def raw447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

def raw447step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]

def raw447step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical130
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4160 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![1, 1, -2]]

def raw4160step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![-1, -1, 2]]

def raw4160step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -1, 0]]

def raw4161 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 2, -3], ![1, -2, 1]]

def raw4161step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![-1, -2, 3], ![-1, 2, -1]]

def raw4161step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]

def raw4162 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 3, -4], ![1, -3, 2]]

def raw4162step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 3, -3], ![2, -4, 2]]

def raw4162step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![0, -3, 3], ![-2, 4, -2]]

def raw4162step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, -1, -1]]

def raw4163 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 4, -5], ![1, -4, 3]]

def raw4163step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 4, -4], ![2, -5, 3]]

def raw4163step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![0, -4, 4], ![-2, 5, -3]]

def raw4163step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 4, -4], ![2, -1, -1]]

def raw4164 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![-3, 2, -1, 2], ![5, -2, -1, -2]]

def raw4164step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![2, -1, -1], ![0, 2, -2]]

def raw4164step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 2, -2], ![2, -1, -1]]

def raw4165 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![-2, 2, -2, 2], ![4, -2, 0, -2]]

def raw4165step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![2, -2, 0], ![0, 2, -2]]

def raw4165step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 2, -2], ![2, -2, 0]]

def raw4166 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![-2, 2, -1, 1], ![4, -2, -1, -1]]

def raw4166step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![2, -1, -1], ![0, 1, -1]]

def raw4166step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def raw4167 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![-2, 2, 1, -1], ![4, -2, -3, 1]]

def raw4167step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![2, 1, -3], ![0, -1, 1]]

def raw4167step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 2, -2], ![2, 1, -3]]

def raw4168 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![-2, 3, 0, -1], ![4, -3, -2, 1]]

def raw4168step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, 0, -2], ![0, -1, 1]]

def raw4168step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 3, -3], ![2, 0, -2]]

def raw4169 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![-1, -2, 0, 3], ![3, 2, -2, -3]]

def raw4169step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![2, 0, -2], ![0, 3, -3]]

def raw4169step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![2, 0, -2]]

def raw4170 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![-1, -2, 1, 2], ![3, 2, -3, -2]]

def raw4170step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![2, 1, -3], ![0, 2, -2]]

def raw4170step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![2, 1, -3]]

def raw4171 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![-1, 2, -2, 1], ![3, -2, 0, -1]]

def raw4171step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -2, 0], ![0, 1, -1]]

def raw4171step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def raw4172 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![-1, 2, 0, -1], ![3, -2, -2, 1]]

def raw4172step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, 0, -2], ![0, -1, 1]]

def raw4172step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

def raw4173 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![-1, 2, 1, -2], ![3, -2, -3, 2]]

def raw4173step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, 1, -3], ![0, -2, 2]]

def raw4173step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![2, 1, -3]]

def raw4174 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![-1, 3, -1, -1], ![3, -3, -1, 1]]

def raw4174step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![2, -1, -1], ![0, -1, 1]]

def raw4174step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![2, -1, -1]]

def raw4175 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![-1, 3, 0, -2], ![3, -3, -2, 2]]

def raw4175step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![2, 0, -2], ![0, -2, 2]]

def raw4175step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![2, 0, -2]]

def raw4176 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![-1, 4, -2, -1], ![3, -4, 0, 1]]

def raw4176step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 4, -4], ![2, -2, 0], ![0, -1, 1]]

def raw4176step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 4, -4], ![2, -2, 0]]

def raw4177 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, -3, 0, 3], ![2, 3, -2, -3]]

def raw4177step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![2, 0, -2], ![0, 3, -3]]

def raw4177step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 3, -3], ![2, 0, -2]]

def raw4178 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, -3, 2, 1], ![2, 3, -4, -1]]

def raw4178step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![2, 2, -4], ![0, 1, -1]]

def raw4178step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 3, -3], ![-2, -2, 4], ![0, -1, 1]]

def raw4178step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 3, -3], ![2, 0, -2]]

def raw4179 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, -2, -2, 4], ![2, 2, 0, -4]]

def raw4179step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![2, -2, 0], ![0, 4, -4]]

def raw4179step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 4, -4], ![2, -2, 0]]

def raw4180 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, -2, -1, 3], ![2, 2, -1, -3]]

def raw4180step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![2, -1, -1], ![0, 3, -3]]

def raw4180step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

def raw4181 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, -2, 0, 2], ![2, 2, -2, -2]]

def raw4181step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![2, 0, -2], ![0, 2, -2]]

def raw4181step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![2, 0, -2]]

def raw4182 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, -2, 1, 1], ![2, 2, -3, -1]]

def raw4182step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![2, 1, -3], ![0, 1, -1]]

def raw4182step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![-2, -1, 3], ![0, -1, 1]]

def raw4182step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

def raw4183 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, -2, 3, -1], ![2, 2, -5, 1]]

def raw4183step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![2, 3, -5], ![0, -1, 1]]

def raw4183step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![-2, -3, 5], ![0, 1, -1]]

def raw4183step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

def raw4184 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, -1, -3, 4], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def raw4184step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -2, 2, 0], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw4185 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, -1, -3, 4], ![1, 0, 1, -2], ![1, 1, 0, -2]]

def raw4185step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -2, 0], ![0, 1, 3, -4], ![-1, 0, -1, 2], ![-1, -1, 0, 2]]

def raw4185step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 2, -2, 0], ![1, 0, 3, -4]]

def raw4186 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, -1, -1, 2], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw4186step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw4187 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, -1, -1, 2], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw4187step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def raw4188 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, 0, -2, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def raw4188step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw4189 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw4189step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw4190 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, 0, -2, 2], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def raw4190step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw4191 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw4191step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -2, 0], ![0, 0, 2, -2], ![-1, 1, 0, 0], ![-1, -1, 0, 2]]

def raw4191step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical131
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4192 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, 0, 1, -1], ![1, -1, -3, 3], ![1, 1, 0, -2]]

def raw4192step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![2, 1, -3, 0], ![0, -1, 3, -2]]

def raw4192step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 1, -1], ![-2, -1, 3, 0], ![0, 1, -3, 2]]

def raw4192step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 2, -3]]

def raw4193 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3], ![1, 0, 0, -1]]

def raw4193step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw4194 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, 2, -4, 2], ![2, -2, 2, -2]]

def raw4194step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -4, 2], ![0, 2, -2]]

def raw4194step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -2, 2], ![-2, 4, -2], ![0, -2, 2]]

def raw4194step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 2, -2], ![2, -2, 0]]

def raw4195 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, 2, -3, 1], ![2, -2, 1, -1]]

def raw4195step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -3, 1], ![0, 1, -1]]

def raw4195step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -2, 2], ![-2, 3, -1], ![0, -1, 1]]

def raw4195step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def raw4196 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, 2, -1, -1], ![2, -2, -1, 1]]

def raw4196step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -1, -1], ![0, -1, 1]]

def raw4196step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

def raw4197 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, 2, 0, -2], ![2, -2, -2, 2]]

def raw4197step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, 0, -2], ![0, -2, 2]]

def raw4197step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![2, 0, -2]]

def raw4198 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, 2, 1, -3], ![2, -2, -3, 3]]

def raw4198step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, 1, -3], ![0, -3, 3]]

def raw4198step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -2, 2], ![-2, -1, 3], ![0, 3, -3]]

def raw4198step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![2, 0, -2]]

def raw4199 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, 3, -4, 1], ![2, -3, 2, -1]]

def raw4199step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![2, -4, 2], ![0, 1, -1]]

def raw4199step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -3, 3], ![-2, 4, -2], ![0, -1, 1]]

def raw4199step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 3, -3], ![2, -2, 0]]

def raw4200 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, 3, -2, -1], ![2, -3, 0, 1]]

def raw4200step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![2, -2, 0], ![0, -1, 1]]

def raw4200step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![2, -2, 0]]

def raw4201 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, 3, -1, -2], ![2, -3, -1, 2]]

def raw4201step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![2, -1, -1], ![0, -2, 2]]

def raw4201step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

def raw4202 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, 3, 0, -3], ![2, -3, -2, 3]]

def raw4202step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![2, 0, -2], ![0, -3, 3]]

def raw4202step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 3, -3], ![2, 0, -2]]

def raw4203 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, 4, -3, -1], ![2, -4, 1, 1]]

def raw4203step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![2, -3, 1], ![0, -1, 1]]

def raw4203step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -4, 4], ![-2, 3, -1], ![0, 1, -1]]

def raw4203step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 4, -4], ![2, -2, 0]]

def raw4204 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, 4, -2, -2], ![2, -4, 0, 2]]

def raw4204step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![2, -2, 0], ![0, -2, 2]]

def raw4204step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 4, -4], ![2, -2, 0]]

def raw4205 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![1, -3, 1, 1], ![1, 3, -3, -1]]

def raw4205step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![2, 1, -3], ![0, 1, -1]]

def raw4205step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 3, -3], ![-2, -1, 3], ![0, -1, 1]]

def raw4205step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![2, -1, -1]]

def raw4206 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![1, -2, -3, 4], ![0, 1, 1, -2], ![1, 1, 0, -2]]

def raw4206step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 1, 1], ![2, -3, 1, 0], ![0, 4, -2, -2]]

def raw4206step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![1, 0, 2, -3], ![1, 1, 0, -2]]

def raw4207 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![1, -2, -1, 2], ![1, 2, -1, -2]]

def raw4207step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![2, -1, -1], ![0, 2, -2]]

def raw4207step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]

def raw4208 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![1, -2, 0, 1], ![1, 2, -2, -1]]

def raw4208step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![2, 0, -2], ![0, 1, -1]]

def raw4208step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 2, -2], ![-2, 0, 2], ![0, -1, 1]]

def raw4208step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

def raw4209 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![1, -2, 2, -1], ![1, 2, -4, 1]]

def raw4209step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![2, 2, -4], ![0, -1, 1]]

def raw4209step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 2, -2], ![-2, -2, 4], ![0, 1, -1]]

def raw4209step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def raw4210 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![1, 2, -1, -2], ![1, -2, -1, 2]]

def raw4210step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![2, -1, -1], ![0, -2, 2]]

def raw4210step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]

def raw4211 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![1, 2, 0, -3], ![1, -2, -2, 3]]

def raw4211step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![2, 0, -2], ![0, -3, 3]]

def raw4211step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, -2, 2], ![-2, 0, 2], ![0, 3, -3]]

def raw4211step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

def raw4212 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![-2, 2, -2, 2], ![4, -2, -1, -1]]

def raw4212step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![3, -2, -1], ![-1, 2, -1]]

def raw4212step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, -2, 2], ![-3, 2, 1], ![1, -2, 1]]

def raw4212step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -4, 2]]

def raw4213 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![-1, 2, -2, 1], ![3, -2, -1, 0]]

def raw4213step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![3, -2, -1], ![-1, 1, 0]]

def raw4213step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![-3, 2, 1], ![1, -1, 0]]

def raw4213step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]

def raw4214 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, -1, -3, 4], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw4215 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, -1, -3, 4], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw4215step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -2, 3, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw4216 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw4216step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -3, 1], ![0, 1, 3, -4], ![0, -2, 0, 2], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw4216step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 2, -3, 1], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw4217 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, -1, -3, 4], ![1, -1, 0, 0], ![1, 2, 0, -3]]

def raw4217step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![3, -3, 0, 0], ![-1, 4, 0, -3]]

def raw4217step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 1, -2], ![-3, 3, 0, 0], ![1, -4, 0, 3]]

def raw4217step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 0, -3, 3], ![0, 3, 1, -4], ![1, -2, 0, 1]]

def raw4218 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, -1, -3, 4], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw4218step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![3, -3, 0, 0], ![-1, 4, -1, -2]]

def raw4218step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def raw4219 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, -1, -2, 3], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def raw4220 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, -1, -2, 3], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw4220step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 3, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw4221 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, -1, -2, 3], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw4221step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -3, 1], ![0, 1, 2, -3], ![0, -2, 0, 2], ![-1, 1, 1, -1], ![-1, 0, 0, 1]]

def raw4221step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 2, -3, 1], ![1, -1, 1, -1], ![1, 0, 2, -3]]

def raw4222 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, -1, -2, 3], ![1, -1, -1, 1], ![1, 2, 0, -3]]

def raw4222step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -3, 1], ![0, 1, 2, -3], ![-1, 1, 1, -1], ![-1, -2, 0, 3]]

def raw4222step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, -3, 1], ![1, -1, 1, -1], ![1, 0, 2, -3]]

def raw4223 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, -1, -2, 3], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw4223step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -3, 1], ![0, 1, 2, -3], ![-1, 0, 1, 0], ![-1, -1, 0, 2]]

def raw4223step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, -3, 1], ![1, 0, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical132
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4224 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 0, -3, 3], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw4224step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -3, 1], ![0, 0, 3, -3], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw4224step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 3, -3], ![0, 2, -3, 1], ![1, -1, 0, 0]]

def raw4225 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 0, -3, 3], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw4225step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -3, 1], ![0, 0, 3, -3], ![-1, 1, 0, 0], ![-1, -1, 0, 2]]

def raw4225step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 2, -3, 1], ![1, -1, 0, 0]]

def raw4226 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -2, -1, 2], ![1, 1, 0, -2]]

def raw4227 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw4227step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -3, 1], ![0, 0, 2, -2], ![0, -1, 0, 1], ![-1, 1, 1, -1], ![-1, 0, 0, 1]]

def raw4227step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 2, -3, 1], ![1, -1, 1, -1]]

def raw4228 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -2, -1, 2], ![1, 0, 0, -1]]

def raw4228step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -3, 1], ![0, 0, 2, -2], ![0, -2, 0, 2], ![-1, 2, 1, -2], ![-1, 0, 0, 1]]

def raw4228step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 2, -3, 1], ![2, -1, 1, -2]]

def raw4229 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 0, -2, 2], ![1, -2, -1, 2], ![1, 2, 0, -3]]

def raw4229step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -3, 1], ![0, 0, 2, -2], ![-1, 2, 1, -2], ![-1, -2, 0, 3]]

def raw4229step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, -3, 1], ![2, -1, 1, -2]]

def raw4230 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 0, -2, 2], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def raw4230step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -3, 1], ![0, 0, 2, -2], ![-1, 1, 1, -1], ![-1, -1, 0, 2]]

def raw4230step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -3, 1], ![1, -1, 1, -1]]

def raw4231 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -2, -1, 2], ![1, 0, 0, -1]]

def raw4231step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def raw4232 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 1, -2, 1], ![1, -2, -1, 2], ![1, 1, 0, -2]]

def raw4232step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 1, -2, 0]]

def raw4233 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, -2, 3], ![1, 0, 0, -1]]

def raw4233step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, -1, 0]]

def raw4234 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -2, -2, 3], ![1, 0, 0, -1]]

def raw4234step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, -1, 0]]

def raw4235 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -3, 4], ![1, 0, 0, -1]]

def raw4236 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3], ![1, 0, -1, 0]]

def raw4236step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw4237 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 1, 0, -1], ![1, -2, -3, 4], ![1, 1, 0, -2]]

def raw4237step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![3, 0, -3, 0], ![-1, -1, 4, -2]]

def raw4237step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def raw4238 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 1, 0, -1], ![1, -1, -3, 3], ![1, 0, 0, -1]]

def raw4238step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![3, 0, -3, 0], ![-1, -1, 3, -1]]

def raw4238step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw4239 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 2, 0, -2], ![1, -2, -3, 4], ![1, 0, 0, -1]]

def raw4239step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![3, 0, -3, 0], ![-1, -2, 4, -1]]

def raw4239step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 3, -3], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw4240 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![1, -3, 1, 1], ![1, 3, -4, 0]]

def raw4240step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![3, 1, -4], ![-1, 1, 0]]

def raw4240step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 3, -3], ![-3, -1, 4], ![1, -1, 0]]

def raw4240step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]

def raw4241 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![2, -3, 1, 0], ![0, 3, -4, 1]]

def raw4241step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -3, 3], ![3, 1, -4], ![-1, 0, 1]]

def raw4241step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -2, 0], ![0, 3, -3], ![-3, -1, 4], ![1, 0, -1]]

def raw4241step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]

def raw4242 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![2, -2, 1, -1], ![0, 2, -4, 2]]

def raw4242step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![3, 1, -4], ![-1, -1, 2]]

def raw4242step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -2, 0], ![0, 2, -2], ![-3, -1, 4], ![1, 1, -2]]

def raw4242step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

def raw4243 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, -2, 2, 0], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def raw4243step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -2, 1, 0], ![-3, 2, 1, 0], ![4, 0, -2, -2]]

def raw4243step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![0, 1, 2, -3], ![2, 0, 0, -2]]

def raw4244 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw4245 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw4246 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw4247 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw4248 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def raw4248step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -1, 1, -1], ![-3, 2, 1, 0], ![4, -1, -2, -1]]

def raw4248step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 2, 0, -3]]

def raw4249 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, -1, 2, -1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw4249step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![-3, 2, 0, 1], ![4, -1, 0, -3]]

def raw4249step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -3, 4], ![0, 2, 1, -3], ![1, 0, 1, -2]]

def raw4250 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, -1, 2, -1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def raw4250step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![-3, 2, 1, 0], ![4, -1, -1, -2]]

def raw4250step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def raw4251 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, -1, 2, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw4251step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, 0, 0], ![-3, 2, 0, 1], ![4, -1, -1, -2]]

def raw4251step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 1, 0, -2]]

def raw4252 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, -1, 2, -1], ![1, 0, 1, -2], ![1, 0, 0, -1]]

def raw4252step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, 0, 0], ![-3, 2, 1, 0], ![4, -1, -2, -1]]

def raw4252step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 1, 0, -2]]

def raw4253 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw4254 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, -1, 3, -2], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw4254step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![-3, 3, 0, 0], ![4, -2, 0, -2]]

def raw4254step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![3, -3, 0, 0], ![-4, 2, 0, 2]]

def raw4254step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -3, 3], ![0, 2, 2, -4], ![1, -1, 1, -1]]

def raw4255 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, -1, 3, -2], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw4255step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, 0, 0], ![-3, 3, 0, 0], ![4, -2, -1, -1]]

def raw4255step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, -1, 1], ![0, 0, 3, -3], ![1, 1, 0, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical133
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4256 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def raw4257 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, -2, 0, 0]]

def raw4258 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, 0, 0]]

def raw4259 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw4260 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw4260step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-3, 1, 0, 2], ![4, -1, -1, -2]]

def raw4260step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 2, -3]]

def raw4261 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw4262 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, -2, 1, -1]]

def raw4262step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-3, 1, 1, 1], ![4, -1, -2, -1]]

def raw4262step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 1, 1, -3]]

def raw4263 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 1, -1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw4264 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 1, -1], ![0, 1, 2, -3], ![2, -2, 0, 0]]

def raw4264step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-3, 1, 2, 0], ![4, -1, -3, 0]]

def raw4264step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -2, 1, 1], ![0, 2, 0, -2], ![1, 0, 2, -3]]

def raw4265 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 1, -1], ![1, -2, 1, 0], ![1, 1, 1, -3]]

def raw4265step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-3, 1, 1, 1], ![4, -1, 0, -3]]

def raw4265step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 2, -1], ![3, -1, -1, -1], ![-4, 1, 0, 3]]

def raw4265step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, -1, 2], ![0, 2, -1, -1], ![1, 0, 3, -4]]

def raw4266 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 1, -1], ![1, -2, 2, -1], ![1, 1, 0, -2]]

def raw4266step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-3, 1, 2, 0], ![4, -1, -1, -2]]

def raw4266step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 2, -3]]

def raw4267 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 2, -2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 0, 0]]

def raw4267step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, 0, 0]]

def raw4268 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def raw4268step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-3, 2, 0, 1], ![4, -2, -1, -1]]

def raw4268step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw4269 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw4270 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![2, -2, 0, 0]]

def raw4270step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-3, 2, 1, 0], ![4, -2, -2, 0]]

def raw4270step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, 1, 0, -3]]

def raw4271 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 2, -2], ![1, -2, 1, 0], ![1, 1, 0, -2]]

def raw4271step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-3, 2, 1, 0], ![4, -2, 0, -2]]

def raw4271step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, 0, 1, -3]]

def raw4272 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw4272step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![-3, 2, 0, 1], ![4, -2, 0, -2]]

def raw4272step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 1, 0], ![3, -2, 0, -1], ![-4, 2, 0, 2]]

def raw4272step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -2, 3], ![0, 2, 2, -4], ![1, 0, 0, -1]]

def raw4273 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 2, -2], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw4273step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![-3, 2, 1, 0], ![4, -2, -1, -1]]

def raw4273step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, 1, -2]]

def raw4274 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 2, -2], ![1, 0, 1, -2], ![1, -1, 0, 0]]

def raw4274step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, 0, -1], ![-3, 2, 1, 0], ![4, -2, -2, 0]]

def raw4274step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 0, 1], ![3, -2, -1, 0], ![-4, 2, 2, 0]]

def raw4274step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -2, 3], ![0, 2, 2, -4], ![1, 0, 0, -1]]

def raw4275 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw4276 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 3, -3], ![0, 1, 0, -1], ![2, -2, 0, 0]]

def raw4276step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-3, 3, 0, 0], ![4, -3, -1, 0]]

def raw4276step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 3, -3], ![0, 2, 0, -2], ![1, -2, 0, 1]]

def raw4277 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 3, -3], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw4277step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![-3, 3, 0, 0], ![4, -3, 0, -1]]

def raw4277step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 1, 0], ![3, -3, 0, 0], ![-4, 3, 0, 1]]

def raw4277step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -3, 3], ![0, 1, 0, -1], ![1, 0, 3, -4]]

def raw4278 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 3, -3], ![1, 0, 0, -1], ![1, -1, 0, 0]]

def raw4278step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, 0, -1], ![-3, 3, 0, 0], ![4, -3, -1, 0]]

def raw4278step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 0, 1], ![3, -3, 0, 0], ![-4, 3, 1, 0]]

def raw4278step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -3, 3], ![0, 1, 0, -1], ![1, 0, 3, -4]]

def raw4279 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, 1, -2]]

def raw4279step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-3, 0, 2, 1], ![4, -1, -1, -2]]

def raw4279step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, 1, -2], ![0, 1, 2, -3], ![1, 0, -2, 1]]

def raw4280 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw4280step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-3, 0, 3, 0], ![4, -1, -2, -1]]

def raw4280step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, 1, -2]]

def raw4281 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw4281step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-3, 0, 0, 3], ![4, -1, 0, -3]]

def raw4281step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 3, -3], ![0, 1, 1, -2], ![1, -1, -1, 1]]

def raw4282 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def raw4282step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-3, 0, 1, 2], ![4, -1, -1, -2]]

def raw4282step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 1, 1, -2], ![0, 1, 2, -3], ![1, -1, -1, 1]]

def raw4283 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw4283step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-3, 1, 2, 0], ![4, -2, -1, -1]]

def raw4283step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, 0, 1, -2]]

def raw4284 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw4284step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-3, 1, 0, 2], ![4, -2, 0, -2]]

def raw4284step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![3, -1, 0, -2], ![-4, 2, 0, 2]]

def raw4284step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -2, 3], ![0, 2, 2, -4], ![1, -1, 1, -1]]

def raw4285 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def raw4285step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-3, 1, 1, 1], ![4, -2, -1, -1]]

def raw4285step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def raw4286 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw4286step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-3, 2, 0, 1], ![4, -3, 0, -1]]

def raw4286step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![3, -2, 0, -1], ![-4, 3, 0, 1]]

def raw4286step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -2, 3], ![0, 1, 3, -4], ![1, 1, -1, -1]]

def raw4287 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, -1, 0, 0]]

def raw4287step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-3, 2, 1, 0], ![4, -3, -1, 0]]

def raw4287step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![3, -2, -1, 0], ![-4, 3, 1, 0]]

def raw4287step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -2, 3], ![0, 1, 3, -4], ![1, 1, -1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical134
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4288 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw4288step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-3, 3, 0, 0], ![4, -4, 0, 0]]

def raw4288step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![3, -3, 0, 0], ![-4, 4, 0, 0]]

def raw4288step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -3, 3], ![0, 0, 4, -4], ![1, 1, -1, -1]]

def raw4289 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![1, -2, 2, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw4289step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, 1, 0], ![-3, 2, 1, 0], ![4, -1, -2, -1]]

def raw4289step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, 0, 1, -2]]

def raw4290 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![1, -1, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw4290step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -1, 1, -1], ![-3, 2, 1, 0], ![4, -2, -2, 0]]

def raw4290step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![-1, 1, -1, 1], ![3, -2, -1, 0], ![-4, 2, 2, 0]]

def raw4290step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -2, 3], ![0, 2, 2, -4], ![1, -1, 1, -1]]

def raw4291 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -2, 1, 1], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw4291step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -2, 0, 1], ![-2, 1, -1, 2], ![3, 1, 0, -4]]

def raw4291step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 2, 0, -1], ![2, -1, 1, -2], ![-3, -1, 0, 4]]

def raw4291step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 4, -3], ![0, 2, -1, -1], ![1, -1, -2, 2]]

def raw4292 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -2, 2, 0], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw4292step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -2, 1, 0], ![-2, 2, 1, -1], ![3, 0, -2, -1]]

def raw4292step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, 0, -2], ![1, -1, 2, -2], ![1, 0, -2, 1]]

def raw4293 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -2, 2, 0], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw4293step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -2, 0, 1], ![-2, 2, 1, -1], ![3, 0, -2, -1]]

def raw4293step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 2, -2], ![1, 1, 0, -2]]

def raw4294 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 0, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw4294step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 1, -3]]

def raw4295 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 0, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def raw4295step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw4296 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 0, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw4296step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def raw4297 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw4297step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw4298 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw4299 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 1, 0], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw4300 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw4300step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![-2, 1, 0, 1], ![3, 0, 0, -3]]

def raw4300step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -3, 3], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw4301 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 1, 0], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def raw4301step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![-2, 1, 1, 0], ![3, 0, -1, -2]]

def raw4301step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![2, -1, -1, 0], ![-3, 0, 1, 2]]

def raw4301step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, 1, -1, -1]]

def raw4302 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw4303 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw4303step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![1, -1, 0, -1, 1], ![-2, 2, 0, 0, 0], ![3, -1, 0, 0, -2]]

def raw4303step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, -1, -1], ![-1, 1, 0, 1, -1], ![2, -2, 0, 0, 0], ![-3, 1, 0, 0, 2]]

def raw4303step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![2, -2, 0, 0], ![-3, 1, 0, 2]]

def raw4303step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -1, 1, -1]]

def raw4304 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def raw4305 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def raw4306 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw4307 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw4308 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw4309 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def raw4309step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -1, 1, -1], ![-2, 2, -1, 1], ![3, -1, 0, -2]]

def raw4309step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 1, -1, 1], ![2, -2, 1, -1], ![-3, 1, 0, 2]]

def raw4309step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, -2, -1, 2]]

def raw4310 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def raw4311 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw4311step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw4312 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw4313 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def raw4313step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -1, 1, -1], ![-2, 2, 0, 0], ![3, -1, -1, -1]]

def raw4313step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw4314 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw4315 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw4316 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![2, -1, -1, 0]]

def raw4316step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -1, 1, -1], ![-2, 2, 1, -1], ![3, -1, -2, 0]]

def raw4316step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 2, -1, -2]]

def raw4317 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def raw4318 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw4318step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![-2, 2, 0, 0], ![3, -1, 0, -2]]

def raw4318step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![2, -2, 0, 0], ![-3, 1, 0, 2]]

def raw4318step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -1, 1, -1]]

def raw4319 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw4319step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![-2, 2, 1, -1], ![3, -1, -1, -1]]

def raw4319step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![2, -2, -1, 1], ![-3, 1, 1, 1]]

def raw4319step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 1, -1, -1], ![1, 1, 1, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical135
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4320 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw4320step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, 0, 0], ![-2, 2, -1, 1], ![3, -1, 0, -2]]

def raw4320step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 0, 0], ![2, -2, 1, -1], ![-3, 1, 0, 2]]

def raw4320step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -2, 2]]

def raw4321 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw4321step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, 0, 0], ![-2, 2, 0, 0], ![3, -1, -1, -1]]

def raw4321step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def raw4322 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![1, 0, 1, -2], ![1, 0, -1, 0]]

def raw4322step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, 0, 0], ![-2, 2, 1, -1], ![3, -1, -2, 0]]

def raw4322step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 0, 0], ![2, -2, -1, 1], ![-3, 1, 2, 0]]

def raw4322step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -2, 2]]

def raw4323 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![1, 1, 1, -3], ![1, -1, -1, 1]]

def raw4323step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def raw4324 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw4325 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def raw4325step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -1, 1, -1], ![-2, 3, -1, 0], ![3, -2, 0, -1]]

def raw4325step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![0, -1, -2, 3], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw4326 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw4327 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw4328 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 3, -2], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def raw4329 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 3, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw4329step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![-2, 3, 0, -1], ![3, -2, 0, -1]]

def raw4329step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![2, -3, 0, 1], ![-3, 2, 0, 1]]

def raw4329step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -3, 2], ![0, 1, 2, -3], ![1, -1, 1, -1]]

def raw4330 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 3, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw4330step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, 0, 0], ![-2, 3, -1, 0], ![3, -2, 0, -1]]

def raw4330step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 0, 0], ![2, -3, 1, 0], ![-3, 2, 0, 1]]

def raw4330step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -3, 2], ![1, 0, 2, -3]]

def raw4331 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 3, -2], ![1, 0, 0, -1], ![1, 0, -1, 0]]

def raw4331step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, 0, 0], ![-2, 3, 0, -1], ![3, -2, -1, 0]]

def raw4331step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 0, 0], ![2, -3, 0, 1], ![-3, 2, 1, 0]]

def raw4331step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -3, 2], ![1, 0, 2, -3]]

def raw4332 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, -1, 2, -1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw4332step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw4333 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, -1, 2, -1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def raw4333step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, -1, 1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def raw4334 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, -1, 3, -2], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw4334step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 3, -2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw4335 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw4336 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -2, 1, 0], ![1, 1, 1, -3]]

def raw4337 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -2, 2, -1], ![1, 1, 0, -2]]

def raw4338 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw4338step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 2, -3], ![1, -2, -2, 3]]

def raw4339 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw4339step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -2, -2, 3]]

def raw4340 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -2, 1, 0], ![1, 1, 0, -2]]

def raw4341 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw4341step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -2, -2, 3]]

def raw4342 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw4343 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 1, 3, -4], ![2, -2, 0, 0]]

def raw4343step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-2, -1, 3, 0], ![3, 1, -4, 0]]

def raw4343step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![2, 1, -3, 0], ![-3, -1, 4, 0]]

def raw4343step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -2, 2, 0], ![0, 2, -1, -1], ![1, 0, 2, -3]]

def raw4344 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def raw4344step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-2, -1, 1, 2], ![3, 1, 0, -4]]

def raw4344step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 2, -1], ![2, 1, -1, -2], ![-3, -1, 0, 4]]

def raw4344step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, -1, 2, -2]]

def raw4345 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![1, -2, 2, -1], ![1, 1, 1, -3]]

def raw4345step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-2, -1, 2, 1], ![3, 1, -1, -3]]

def raw4345step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -3, -1, 3]]

def raw4346 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw4346step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![1, 0, 1, -2, 0], ![-2, 0, 0, 2, 0], ![3, 0, -1, -1, -1]]

def raw4346step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-2, 0, 2, 0], ![3, -1, -1, -1]]

def raw4346step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 1, -2]]

def raw4347 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 0, 0], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw4347step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-2, 0, 0, 2], ![3, 0, -1, -2]]

def raw4347step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 1, -2], ![-2, 0, 2], ![3, -1, -2]]

def raw4347step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1]]

def raw4348 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 0, 0], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw4348step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![1, 0, 1, -1, -1], ![-2, 0, 1, 0, 1], ![3, 0, -2, 0, -1]]

def raw4348step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, -1, -1], ![-1, 0, -1, 1, 1], ![2, 0, -1, 0, -1], ![-3, 0, 2, 0, 1]]

def raw4348step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![2, -1, 0, -1], ![-3, 2, 0, 1]]

def raw4348step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, 1, -1, -1]]

def raw4349 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 0, 0], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw4349step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![1, 0, 1, -1, -1], ![-2, 0, 2, 0, 0], ![3, 0, -3, 0, 0]]

def raw4349step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, -1, -1], ![-1, 0, -1, 1, 1], ![2, 0, -2, 0, 0], ![-3, 0, 3, 0, 0]]

def raw4349step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![2, -2, 0, 0], ![-3, 3, 0, 0]]

def raw4349step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, 1, -1, -1]]

def raw4350 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 0, 0], ![1, -2, 1, 0], ![1, 1, 1, -3]]

def raw4350step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-2, 0, 1, 1], ![3, 0, 0, -3]]

def raw4350step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![-2, 1, 1], ![3, 0, -3]]

def raw4350step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]

def raw4351 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 0, 0], ![1, -2, 2, -1], ![1, 1, 0, -2]]

def raw4351step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-2, 0, 2, 0], ![3, 0, -1, -2]]

def raw4351step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![-2, 2, 0], ![3, -1, -2]]

def raw4351step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical136
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4352 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, -1, 1, 0], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw4352step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw4353 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, -1, 2, -1], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def raw4353step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def raw4354 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, -1, 2, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw4354step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw4355 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![2, -1, 0, -1]]

def raw4355step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![1, 0, 0, 0, -1], ![-2, 1, 1, 0, 0], ![3, -1, -1, 0, -1]]

def raw4355step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 0, -1], ![-2, 1, 1, 0], ![3, -1, -1, -1]]

def raw4355step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def raw4356 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def raw4357 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 0, 0]]

def raw4357step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw4358 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, -2, -1, 1]]

def raw4359 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -2, 1, 0], ![1, 1, -1, -1]]

def raw4360 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw4360step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

def raw4361 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw4361step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -2, 3, -2]]

def raw4362 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, 0, 0]]

def raw4363 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, -1, 1]]

def raw4364 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -2, 0, 1], ![1, 1, -1, -1]]

def raw4365 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw4365step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -2, 3, -2]]

def raw4366 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw4367 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw4368 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def raw4369 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def raw4369step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-2, 1, -1, 2], ![3, -1, 0, -2]]

def raw4369step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, 2, -2]]

def raw4370 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 0, 0, -1]]

def raw4370step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw4371 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def raw4372 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw4372step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw4373 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def raw4373step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-2, 1, 0, 1], ![3, -1, -1, -1]]

def raw4373step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 1, -2]]

def raw4374 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def raw4375 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, -1, 1, -1]]

def raw4376 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw4376step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw4377 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, -2, 0, 0]]

def raw4377step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-2, 1, 1, 0], ![3, -1, -2, 0]]

def raw4377step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def raw4378 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw4379 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, -1, 1]]

def raw4379step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw4380 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, 2, -3], ![2, -2, -1, 1]]

def raw4380step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-2, 1, 2, -1], ![3, -1, -3, 1]]

def raw4380step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -3, 1, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 2, -1, -2]]

def raw4381 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![1, -2, 0, 1], ![1, 1, 1, -3]]

def raw4381step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-2, 1, 0, 1], ![3, -1, 1, -3]]

def raw4381step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 2, -1], ![2, -1, 0, -1], ![-3, 1, -1, 3]]

def raw4381step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 2, -1, -1], ![1, -1, 3, -3]]

def raw4382 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![1, -2, 1, 0], ![1, 1, 0, -2]]

def raw4382step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-2, 1, 1, 0], ![3, -1, 0, -2]]

def raw4382step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw4383 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![1, -2, 2, -1], ![1, 1, -1, -1]]

def raw4383step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-2, 1, 2, -1], ![3, -1, -1, -1]]

def raw4383step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 2, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical137
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4384 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw4384step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![3, -1, 0, -2]]

def raw4384step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw4385 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw4385step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![-2, 1, 1, 0], ![3, -1, -1, -1]]

def raw4385step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw4386 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 0, 0]]

def raw4386step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, 0, 0]]

def raw4387 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, -1, 1]]

def raw4387step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, -1, 1]]

def raw4388 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 0, 0, -1]]

def raw4389 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw4390 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, -1, 0, 0]]

def raw4390step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw4391 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def raw4391step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-2, 2, -1, 1], ![3, -2, 0, -1]]

def raw4391step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![2, -2, 1, -1], ![-3, 2, 0, 1]]

def raw4391step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -2, -1, 2]]

def raw4392 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def raw4393 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw4393step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw4394 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, 0, 0]]

def raw4394step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-2, 2, 0, 0], ![3, -2, -1, 0]]

def raw4394step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw4395 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw4396 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, -1, 1]]

def raw4396step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw4397 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 1, 1, -2], ![2, -2, -1, 1]]

def raw4397step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-2, 2, 1, -1], ![3, -2, -2, 1]]

def raw4397step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, 1, -1, -2]]

def raw4398 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![1, -2, 0, 1], ![1, 1, 0, -2]]

def raw4398step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def raw4399 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![1, -2, 1, 0], ![1, 1, -1, -1]]

def raw4399step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-2, 2, 1, -1], ![3, -2, 0, -1]]

def raw4399step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, 1, -2]]

def raw4400 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def raw4400step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -2, -2, 3]]

def raw4401 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw4401step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![-2, 2, 0, 0], ![3, -2, 0, -1]]

def raw4401step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 1, 0], ![2, -2, 0, 0], ![-3, 2, 0, 1]]

def raw4401step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def raw4402 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw4402step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![-2, 2, 1, -1], ![3, -2, -1, 0]]

def raw4402step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 1, 0], ![2, -2, -1, 1], ![-3, 2, 1, 0]]

def raw4402step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, -1, -2, 2]]

def raw4403 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![1, 0, -1, 0], ![1, -1, 1, -1]]

def raw4403step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, 0, -1], ![-2, 2, -1, 1], ![3, -2, 0, -1]]

def raw4403step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 0, 1], ![2, -2, 1, -1], ![-3, 2, 0, 1]]

def raw4403step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, -1, -2, 2]]

def raw4404 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![1, 0, 1, -2], ![1, -1, -1, 1]]

def raw4404step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -2, -2, 3]]

def raw4405 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw4406 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 3, -3], ![0, 1, -1, 0], ![2, -2, 0, 0]]

def raw4406step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-2, 3, -1, 0], ![3, -3, 0, 0]]

def raw4406step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![0, 0, -3, 3], ![0, 2, 0, -2], ![1, -2, 0, 1]]

def raw4407 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw4408 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, -1, 1]]

def raw4408step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw4409 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 3, -3], ![0, 1, 0, -1], ![2, -2, -1, 1]]

def raw4409step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-2, 3, 0, -1], ![3, -3, -1, 1]]

def raw4409step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -3, 1, 3], ![0, 0, 2, -2], ![0, 3, -1, -2], ![1, 0, -2, 1]]

def raw4410 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 3, -3], ![1, -2, 0, 1], ![1, 1, -1, -1]]

def raw4411 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 3, -3], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw4411step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![-2, 3, -1, 0], ![3, -3, 1, -1]]

def raw4411step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 1, 0], ![2, -3, 1, 0], ![-3, 3, -1, 1]]

def raw4411step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -3, 2], ![0, 1, 0, -1], ![1, -1, 3, -3]]

def raw4412 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 3, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw4412step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![-2, 3, 0, -1], ![3, -3, 0, 0]]

def raw4412step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 1, 0], ![2, -3, 0, 1], ![-3, 3, 0, 0]]

def raw4412step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -3, 2], ![1, 0, 0, -1]]

def raw4413 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 3, -3], ![1, 0, -1, 0], ![1, -1, 0, 0]]

def raw4413step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, 0, -1], ![-2, 3, -1, 0], ![3, -3, 0, 0]]

def raw4413step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 0, 1], ![2, -3, 1, 0], ![-3, 3, 0, 0]]

def raw4413step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -3, 2], ![1, 0, 0, -1]]

def raw4414 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def raw4414step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-2, -1, 0, 3], ![3, 0, 1, -4]]

def raw4414step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -2, 1, 0]]

def raw4415 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 0, 2, -3]]

def raw4415step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-2, -1, 1, 2], ![3, 0, 0, -3]]

def raw4415step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, 0, -3, 3], ![0, 1, 1, -2], ![1, -2, 0, 1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical138
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4416 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 1, -2]]

def raw4416step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-2, -1, 2, 1], ![3, 0, -1, -2]]

def raw4416step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 2, 0], ![2, 1, -2, -1], ![-3, 0, 1, 2]]

def raw4416step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 1, -3], ![1, -1, -2, 2]]

def raw4417 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, -1, 0], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw4417step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-2, -1, 3, 0], ![3, 0, -2, -1]]

def raw4417step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, 0, 1, -2]]

def raw4418 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw4418step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-2, -1, 0, 3], ![3, 0, 0, -3]]

def raw4418step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -1, 1, -1]]

def raw4419 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def raw4419step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-2, -1, 1, 2], ![3, 0, -1, -2]]

def raw4419step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![2, 1, -1, -2], ![-3, 0, 1, 2]]

def raw4419step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, -1, -2, 2]]

def raw4420 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, -1, 0], ![1, -1, 2, -2], ![1, -1, 1, -1]]

def raw4420step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-2, -1, 2, 1], ![3, 0, -2, -1]]

def raw4420step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![2, 1, -2, -1], ![-3, 0, 2, 1]]

def raw4420step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, -1, -2, 2]]

def raw4421 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw4421step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-2, 0, 2, 0], ![3, -1, -1, -1]]

def raw4421step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 1, -2]]

def raw4422 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, -1, 0]]

def raw4422step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-2, 0, 3, -1], ![3, -1, -2, 0]]

def raw4422step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 3, -2], ![0, 1, 1, -2], ![1, 0, -2, 1]]

def raw4423 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 3, -3]]

def raw4423step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-2, 0, -1, 3], ![3, -1, 1, -3]]

def raw4423step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, -1, 3, -2], ![0, 1, 1, -2], ![1, -1, -1, 1]]

def raw4424 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw4424step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-2, 0, 0, 2], ![3, -1, 0, -2]]

def raw4424step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, -1, 1]]

def raw4425 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def raw4425step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-2, 0, 1, 1], ![3, -1, -1, -1]]

def raw4425step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -1, -1, 1]]

def raw4426 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 0, 0, -1]]

def raw4426step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-2, 1, 1, 0], ![3, -2, 0, -1]]

def raw4426step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw4427 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def raw4427step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-2, 1, 2, -1], ![3, -2, -1, 0]]

def raw4427step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 2, 0], ![2, -1, -2, 1], ![-3, 2, 1, 0]]

def raw4427step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, -1, -2, 2]]

def raw4428 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, -1, 2, -2]]

def raw4429 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw4429step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-2, 1, 0, 1], ![3, -2, 0, -1]]

def raw4429step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![2, -1, 0, -1], ![-3, 2, 0, 1]]

def raw4429step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, 1, -1, -1]]

def raw4430 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, 2, -3], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def raw4430step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-2, 2, 1, -1], ![3, -3, 0, 0]]

def raw4430step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 2, 0], ![2, -2, -1, 1], ![-3, 3, 0, 0]]

def raw4430step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 2, -1, -1], ![1, -1, -2, 2]]

def raw4431 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, -1, 1, -1]]

def raw4432 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw4432step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-2, 2, 0, 0], ![3, -3, 0, 0]]

def raw4432step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![2, -2, 0, 0], ![-3, 3, 0, 0]]

def raw4432step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, 1, -1, -1]]

def raw4433 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, 3, -4], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def raw4433step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-2, 3, 0, -1], ![3, -4, 1, 0]]

def raw4433step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 2, 0], ![2, -3, 0, 1], ![-3, 4, -1, 0]]

def raw4433step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 4, -3], ![0, 2, -1, -1], ![1, 0, -3, 2]]

def raw4434 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw4434step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-2, 3, -1, 0], ![3, -4, 1, 0]]

def raw4434step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![2, -3, 1, 0], ![-3, 4, -1, 0]]

def raw4434step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 4, -3], ![0, 1, -3, 2], ![1, 1, -1, -1]]

def raw4435 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, -1, 1]]

def raw4435step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-2, 3, 0, -1], ![3, -4, 0, 1]]

def raw4435step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![2, -3, 0, 1], ![-3, 4, 0, -1]]

def raw4435step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 4, -3], ![0, 1, -3, 2], ![1, 1, -1, -1]]

def raw4436 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![1, -2, 2, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw4436step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, 1, 0], ![-2, 2, 1, -1], ![3, -1, -2, 0]]

def raw4436step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![-1, 2, -1, 0], ![2, -2, -1, 1], ![-3, 1, 2, 0]]

def raw4436step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, -1, -2, 2]]

def raw4437 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![1, -1, 2, -2], ![0, 1, 1, -2], ![1, -1, -1, 1]]

def raw4437step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, -1, 2, -2]]

def raw4438 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -2, 0, 2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def raw4438step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, -1, 2], ![1, 0, -1, 0]]

def raw4439 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -2, 0, 2], ![0, 1, 3, -4], ![2, 0, -2, 0]]

def raw4439step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -2, 1, 0], ![-1, 0, 3, -2], ![2, 2, -4, 0]]

def raw4439step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 2, -1, 0], ![1, 0, -3, 2], ![-2, -2, 4, 0]]

def raw4439step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 2, 1, -3], ![2, 0, -1, -1]]

def raw4440 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -2, 0, 2], ![1, 0, 3, -4], ![1, 1, -2, 0]]

def raw4440step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -2, 0, 1], ![-1, 0, 3, -2], ![2, 2, -4, 0]]

def raw4440step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 2, 0, -1], ![1, 0, -3, 2], ![-2, -2, 4, 0]]

def raw4440step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 2, 1, -3], ![2, -1, -1, 0]]

def raw4441 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -2, 1, 1], ![1, 0, -2, 1], ![1, 1, 2, -4]]

def raw4441step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![1, -2, -1, 2], ![1, 1, 2, -4]]

def raw4442 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -2, 1, 1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw4442step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -2, 0, 1], ![-1, 1, -1, 1], ![2, 1, 0, -3]]

def raw4442step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 2, 0, -1], ![1, -1, 1, -1], ![-2, -1, 0, 3]]

def raw4442step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw4443 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -2, 1, 1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw4443step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def raw4444 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -2, 2, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw4444step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw4445 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -2, 2, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw4445step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -2, 1, 0], ![-1, 2, -1, 0], ![2, 0, 0, -2]]

def raw4445step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw4446 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw4446step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -2, 1, 0], ![-1, 2, 0, -1], ![2, 0, -1, -1]]

def raw4446step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw4447 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -2, 2, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw4447step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -2, 0, 1], ![-1, 2, 0, -1], ![2, 0, -1, -1]]

def raw4447step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 1, 0, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical139
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4448 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw4449 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw4450 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![2, -1, -1, 0]]

def raw4450step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -1, 1, -1], ![-1, -1, 3, -1], ![2, 2, -4, 0]]

def raw4450step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 1, -1, 1], ![1, 1, -3, 1], ![-2, -2, 4, 0]]

def raw4450step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def raw4451 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, -1, 2], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw4451step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![-1, -1, 0, 2], ![2, 2, 0, -4]]

def raw4451step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw4452 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, -1, 2], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def raw4452step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, 0, 0], ![-1, -1, -1, 3], ![2, 2, 0, -4]]

def raw4452step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw4453 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, -1, 2], ![1, 0, 3, -4], ![1, 0, -1, 0]]

def raw4453step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, 0, 0], ![-1, -1, 3, -1], ![2, 2, -4, 0]]

def raw4453step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw4454 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw4454step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 1, -2], ![0, 1, 0, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, -1, -2, 4]]

def raw4454step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -1, -2]]

def raw4455 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, -1, 1, -1], ![1, 1, 1, -3]]

def raw4455step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def raw4456 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 0, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw4456step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw4457 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 0, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw4457step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw4458 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw4458step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw4459 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw4459step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -2, -1, 2]]

def raw4460 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw4460step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw4461 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 1, 0], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def raw4461step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![-1, 1, -1, 1], ![2, 0, 1, -3]]

def raw4461step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -3, 2], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw4462 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 1, 0], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw4462step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![-1, 1, 1, -1], ![2, 0, -1, -1]]

def raw4462step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw4463 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw4464 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 0, -2, 2], ![2, 0, 1, -3]]

def raw4464step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -2, -1, 2]]

def raw4465 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def raw4466 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw4466step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw4467 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw4467step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![1, -1, 0, -1, 1], ![-1, 2, 0, 0, -1], ![2, -1, 0, 0, -1]]

def raw4467step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, -1, -1], ![-1, 1, 0, 1, -1], ![1, -2, 0, 0, 1], ![-2, 1, 0, 0, 1]]

def raw4467step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![1, -2, 0, 1], ![-2, 1, 0, 1]]

def raw4467step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw4468 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def raw4469 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw4469step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 1, -2], ![0, 1, -2, 1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, -1, 2, 0]]

def raw4469step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw4470 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw4470step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 1, -2], ![0, 1, -2, 1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw4470step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw4471 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def raw4471step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -1, 1, -1], ![-1, 2, -1, 0], ![2, -1, 0, -1]]

def raw4471step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw4472 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw4472step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw4473 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw4473step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 1, -2], ![0, 1, -2, 1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw4473step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw4474 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![1, -1, -2, 2], ![1, 1, 1, -3]]

def raw4475 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def raw4475step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def raw4476 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw4476step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![-1, 2, 0, -1], ![2, -1, 0, -1]]

def raw4476step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![1, -2, 0, 1], ![-2, 1, 0, 1]]

def raw4476step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw4477 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw4477step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 1, -2], ![0, 1, -2, 1], ![-1, 1, -1, 1], ![-1, -1, 2, 0]]

def raw4477step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def raw4478 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw4479 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![0, 1, -2, 1], ![2, -1, 0, -1]]

def raw4479step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -1, 1, -1], ![-1, 3, -2, 0], ![2, -2, 1, -1]]

def raw4479step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, -1, 2, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def raw448step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]

def raw448step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw449 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]

def raw449step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]

def raw449step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw450 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]

def raw450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]

def raw450step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw451 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]

def raw451step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]

def raw451step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

def raw452 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]

def raw452step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-3, 1, 2]]

def raw452step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 0, -1], ![1, 2, -3]]

def raw453 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]

def raw453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![2, -1, -1]]

def raw454 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]

def raw454step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![2, -1, -1]]

def raw455 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]

def raw455step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]

def raw456 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]

def raw456step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

def raw457 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]

def raw457step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]

def raw457step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]

def raw458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw458step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]

def raw458step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]

def raw459 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]

def raw459step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]

def raw459step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

def raw460 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]

def raw460step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-3, 2, 1]]

def raw460step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]

def raw461 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]

def raw461step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-2, 2, 0], ![-2, 1, 1]]

def raw461step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]

def raw462 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]

def raw463 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]

def raw464 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]

def raw464step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

def raw465 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]

def raw465step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def raw466 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]

def raw467 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]

def raw468 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]

def raw468step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

def raw469 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

def raw470 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1], ![1, 1, -2]]

def raw470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

def raw471 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![3, 0, -3]]

def raw471step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 3, -3], ![2, 0, -2]]

def raw472 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]

def raw473 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]

def raw474 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1], ![1, 0, -1]]

def raw474step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]

def raw475 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![3, -1, -2]]

def raw476 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]

def raw476step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -3, 4]]

def raw476step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]

def raw477 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]

def raw478 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![2, 3, -5]]

def raw478step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, 1, 0], ![-2, -3, 5]]

def raw478step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]

def raw479 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]

def raw479step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]

def raw479step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![2, 0, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical140
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4480 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw4481 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw4481step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def raw4482 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw4483 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw4484 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def raw4485 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw4485step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![-1, 3, 0, -2], ![2, -2, 0, 0]]

def raw4485step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![1, -3, 0, 2], ![-2, 2, 0, 0]]

def raw4485step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -3, 1], ![1, -1, 1, -1]]

def raw4486 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def raw4486step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, 0, 0], ![-1, 3, -2, 0], ![2, -2, 1, -1]]

def raw4486step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 0, 0], ![1, -3, 2, 0], ![-2, 2, -1, 1]]

def raw4486step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, -1, 2, -2]]

def raw4487 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw4487step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, 0, 0], ![-1, 3, -1, -1], ![2, -2, 0, 0]]

def raw4487step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, 1, -2, 0]]

def raw4488 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![1, 0, 0, -1], ![1, 0, -2, 1]]

def raw4488step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, 0, 0], ![-1, 3, 0, -2], ![2, -2, -1, 1]]

def raw4488step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 0, 0], ![1, -3, 0, 2], ![-2, 2, 1, -1]]

def raw4488step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, -1, 2, -2]]

def raw4489 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw4490 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw4490step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -2, 2], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -2, -1, 2]]

def raw4491 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, 0, 0, -1], ![1, -1, 0, 0]]

def raw4491step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -2, 2], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -2, -1, 2]]

def raw4492 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, 1, -2]]

def raw4493 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw4494 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![2, -2, 3, -3]]

def raw4494step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, -2, 0, 3], ![2, 2, -1, -3]]

def raw4494step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![1, 2, 0, -3], ![-2, -2, 1, 3]]

def raw4494step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 2, 1, -3], ![1, -2, -2, 3]]

def raw4495 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw4496 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, -2, 2, -2]]

def raw4497 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw4498 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 1, 3, -4], ![2, -2, 0, 0]]

def raw4498step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, -2, 3, 0], ![2, 2, -4, 0]]

def raw4498step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![1, 2, -3, 0], ![-2, -2, 4, 0]]

def raw4498step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 2, -1, -1], ![2, 0, 1, -3]]

def raw4499 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def raw4499step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-1, -2, 1, 2], ![2, 2, 0, -4]]

def raw4499step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 2, -1], ![1, 2, -1, -2], ![-2, -2, 0, 4]]

def raw4499step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, -1, 1, -2]]

def raw4500 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![1, -2, 2, -1], ![1, 1, 1, -3]]

def raw4501 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![1, -2, 3, -2], ![1, 1, 0, -2]]

def raw4501step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-1, -2, 3, 0], ![2, 2, -2, -2]]

def raw4501step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -2, 2, -2]]

def raw4502 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw4502step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![-1, -2, 0, 3], ![2, 2, 0, -4]]

def raw4502step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, -1, 3], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw4503 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![1, -1, 2, -2], ![1, 0, 1, -2]]

def raw4503step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, -2, -1, 2]]

def raw4504 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def raw4504step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![-1, -2, 3, 0], ![2, 2, -3, -1]]

def raw4504step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 1, 0], ![1, 2, -3, 0], ![-2, -2, 3, 1]]

def raw4504step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -2, -2, 3]]

def raw4505 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![1, 0, 3, -4], ![1, -1, 0, 0]]

def raw4505step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, 0, -1], ![-1, -2, 3, 0], ![2, 2, -4, 0]]

def raw4505step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, -1, 3], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw4506 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![1, 1, 1, -3], ![1, -2, 2, -1]]

def raw4506step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![1, -2, 2, -1], ![1, 1, 1, -3]]

def raw4507 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, -1, 0, 1], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw4507step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 1, -2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-1, 1, 0, 0], ![-1, -1, -2, 4]]

def raw4507step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -1, -2]]

def raw4508 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, -1, 0, 1], ![1, -1, 1, -1], ![1, 1, 1, -3]]

def raw4508step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def raw4509 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, -1, 2, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw4509step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 0, -1, 1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw4510 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, -1, 3, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw4510step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw4511 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![2, -2, 0, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical141
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4512 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def raw4513 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -2, 2, -1], ![1, 1, 1, -3]]

def raw4514 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw4514step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -2, -1, 2]]

def raw4515 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 1, -1], ![1, 0, 2, -3]]

def raw4515step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -2, -1, 2]]

def raw4516 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw4516step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![1, 0, 0, 1, -2], ![-1, -1, 0, 0, 2], ![2, 1, 0, -1, -2]]

def raw4516step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, -1, 0, 2], ![2, 1, -1, -2]]

def raw4516step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, -1, 2, -2]]

def raw4517 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def raw4518 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def raw4518step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def raw4519 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -2, 2, -1], ![1, 1, -1, -1]]

def raw4520 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw4520step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -1, -2, 2]]

def raw4521 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw4521step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw4522 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def raw4523 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -2, 1, 0], ![1, 1, -1, -1]]

def raw4524 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw4524step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw4525 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def raw4526 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw4527 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![2, -2, 3, -3]]

def raw4527step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, -1, -1, 3], ![2, 1, 0, -3]]

def raw4527step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 0, 2, -3]]

def raw4528 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw4528step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -2, -1]]

def raw4529 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw4529step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, -1, 0, 2], ![2, 1, -1, -2]]

def raw4529step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, -1, 2, -2]]

def raw4530 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw4530step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 1, -2], ![0, 0, 1, -1], ![0, -1, -2, 3], ![-1, 1, 0, 0], ![-1, 1, 0, 0]]

def raw4530step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def raw4531 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, 2, -3], ![2, -2, 0, 0]]

def raw4531step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, -1, 2, 0], ![2, 1, -3, 0]]

def raw4531step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![1, 1, -2, 0], ![-2, -1, 3, 0]]

def raw4531step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 2, 0], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw4532 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw4533 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, -1, 1]]

def raw4533step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw4534 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![2, -2, -1, 1]]

def raw4534step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, -1, 3, -1], ![2, 1, -4, 1]]

def raw4534step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![1, 1, -3, 1], ![-2, -1, 4, -1]]

def raw4534step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 1, 1, -3]]

def raw4535 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![1, -2, 0, 1], ![1, 1, 2, -4]]

def raw4535step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-1, -1, 0, 2], ![2, 1, 1, -4]]

def raw4535step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 2, -1], ![1, 1, 0, -2], ![-2, -1, -1, 4]]

def raw4535step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw4536 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![1, -2, 1, 0], ![1, 1, 1, -3]]

def raw4536step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-1, -1, 1, 1], ![2, 1, 0, -3]]

def raw4536step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 2, -1], ![1, 1, -1, -1], ![-2, -1, 0, 3]]

def raw4536step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def raw4537 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![1, -2, 2, -1], ![1, 1, 0, -2]]

def raw4537step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-1, -1, 2, 0], ![2, 1, -1, -2]]

def raw4537step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -2, 2, -1]]

def raw4538 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 0, 3, -4]]

def raw4538step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![-1, -1, -1, 3], ![2, 1, 1, -4]]

def raw4538step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 1, 0], ![1, 1, 1, -3], ![-2, -1, -1, 4]]

def raw4538step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 1, 1, -3]]

def raw4539 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw4539step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![-1, -1, 0, 2], ![2, 1, 0, -3]]

def raw4539step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 1, 0], ![1, 1, 0, -2], ![-2, -1, 0, 3]]

def raw4539step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw4540 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw4540step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, -1, -2, 2]]

def raw4541 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def raw4541step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![-1, -1, 2, 0], ![2, 1, -2, -1]]

def raw4541step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 2, -2]]

def raw4542 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def raw4542step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![1, 0, 0, 1, -2], ![-1, 0, 1, -1, 1], ![2, 0, -1, 0, -1]]

def raw4542step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, 1, -1, 1], ![2, -1, 0, -1]]

def raw4542step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, 1, -1]]

def raw4543 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 0, 0], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, 0, 0]]

def raw4543step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![1, 0, 0, 1, -2], ![-1, 0, 2, -1, 0], ![2, 0, -2, 0, 0]]

def raw4543step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, 2, -1, 0], ![2, -2, 0, 0]]

def raw4543step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -2, 0, 1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical142
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4544 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 0, 0], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw4544step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![1, 0, 1, -2, 0], ![-1, 0, -1, 2, 0], ![2, 0, 0, -1, -1]]

def raw4544step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-1, -1, 2, 0], ![2, 0, -1, -1]]

def raw4544step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 0, 1, -2]]

def raw4545 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 0, 0], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def raw4545step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, 0, -1, 2], ![2, 0, 0, -2]]

def raw4545step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 1, -2], ![-1, -1, 2], ![2, 0, -2]]

def raw4545step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

def raw4546 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def raw4546step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![1, 0, 1, -2, 0], ![-1, 0, 0, 2, -1], ![2, 0, -1, -1, 0]]

def raw4546step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-1, 0, 2, -1], ![2, -1, -1, 0]]

def raw4546step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, -2, 1]]

def raw4547 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 0, 0], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def raw4547step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![1, 0, 1, -2, 0], ![-1, 0, 1, 1, -1], ![2, 0, -2, 0, 0]]

def raw4547step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, -1, -1], ![-1, 0, -1, 2, 0], ![1, 0, -1, -1, 1], ![-2, 0, 2, 0, 0]]

def raw4547step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 2, 0], ![1, -1, -1, 1], ![-2, 2, 0, 0]]

def raw4547step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw4548 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 0, 0], ![1, -2, 2, -1], ![1, 1, -1, -1]]

def raw4548step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-1, 0, 2, -1], ![2, 0, -1, -1]]

def raw4548step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![-1, 2, -1], ![2, -1, -1]]

def raw4548step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2]]

def raw4549 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def raw4549step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![1, 0, 0, 1, -2], ![-1, 1, 0, -1, 1], ![2, -1, 0, 0, -1]]

def raw4549step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, 1, -1, 1], ![2, -1, 0, -1]]

def raw4549step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, 1, -1]]

def raw4550 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![2, -2, 1, -1]]

def raw4551 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 0, 0]]

def raw4551step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw4552 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, -1, 1]]

def raw4552step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -2, 1]]

def raw4553 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, -2, -2, 2]]

def raw4554 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, -2, 0, 0]]

def raw4555 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, -1, 1]]

def raw4556 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, -2, 2]]

def raw4557 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw4557step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 1, -2]]

def raw4558 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw4559 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def raw4560 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![2, -2, 2, -2]]

def raw4560step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, 1, -2, 2], ![2, -1, 1, -2]]

def raw4560step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, -2, -1, 2]]

def raw4561 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 0, 0, -1]]

def raw4561step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw4562 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def raw4562step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -2, -1]]

def raw4563 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw4563step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw4564 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def raw4564step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, 1, -1, 1], ![2, -1, 0, -1]]

def raw4564step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, 1, -1]]

def raw4565 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def raw4565step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw4566 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, -2, 1]]

def raw4566step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def raw4567 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def raw4567step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw4568 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 0, -2, 1]]

def raw4569 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, -2, -1, 1]]

def raw4569step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, 1, 1, -1], ![2, -1, -2, 1]]

def raw4569step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 1, -1, -1]]

def raw4570 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, 2, -3], ![2, -2, -2, 2]]

def raw4570step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, 1, 2, -2], ![2, -1, -3, 2]]

def raw4570step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -3, 2, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 2, -1, -2]]

def raw4571 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![1, -2, 1, 0], ![1, 1, -1, -1]]

def raw4571step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-1, 1, 1, -1], ![2, -1, 0, -1]]

def raw4571step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw4572 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![1, -2, 2, -1], ![1, 1, -2, 0]]

def raw4572step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-1, 1, 2, -2], ![2, -1, -1, 0]]

def raw4572step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -2, 2, -1]]

def raw4573 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, -2, 2]]

def raw4573step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, -2, 2]]

def raw4574 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw4575 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, -1, 0, 0]]

def raw4575step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical143
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4576 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, -2, 1, -1]]

def raw4577 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 0, -1]]

def raw4577step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 2, 0, -2], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def raw4578 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def raw4578step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 1, -2], ![0, 0, -2, 2], ![0, -1, 1, 0], ![-1, 2, -1, 0], ![-1, 0, 1, 0]]

def raw4578step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def raw4579 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw4579step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 1, -2], ![0, 0, -2, 2], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 1, 0, 0]]

def raw4579step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw4580 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, 0, 0]]

def raw4580step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, 2, -1, 0], ![2, -2, 0, 0]]

def raw4580step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -2, 0, 1]]

def raw4581 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def raw4581step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw4582 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 0, -2, 1]]

def raw4583 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw4583step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw4584 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, -1, 1]]

def raw4584step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, 2, 0, -1], ![2, -2, -1, 1]]

def raw4584step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, -2, 1]]

def raw4585 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, 1, -2], ![2, -2, -2, 2]]

def raw4585step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, 2, 1, -2], ![2, -2, -2, 2]]

def raw4585step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, 1, -1, -2]]

def raw4586 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![1, -2, 0, 1], ![1, 1, -1, -1]]

def raw4586step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-1, 2, 0, -1], ![2, -2, 1, -1]]

def raw4586step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def raw4587 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![1, -2, 1, 0], ![1, 1, -2, 0]]

def raw4587step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 1, -2], ![0, 0, -2, 2], ![-1, 2, -1, 0], ![-1, -1, 2, 0]]

def raw4587step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def raw4588 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw4588step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![-1, 2, -1, 0], ![2, -2, 1, -1]]

def raw4588step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw4589 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![1, -1, 1, -1], ![1, 0, -2, 1]]

def raw4589step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, -2, 2, -1]]

def raw4590 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![1, 0, -2, 1], ![1, -1, 1, -1]]

def raw4590step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, -2, 2, -1]]

def raw4591 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw4592 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![2, -2, 0, 0]]

def raw4592step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, 3, -2, 0], ![2, -3, 1, 0]]

def raw4592step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -2, 1, 0], ![1, 0, 2, -3]]

def raw4593 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def raw4594 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw4595 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, -1, 1]]

def raw4595step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw4596 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![2, -2, -1, 1]]

def raw4596step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, 3, -1, -1], ![2, -3, 0, 1]]

def raw4596step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -2, 2, 0], ![0, 2, 1, -3], ![1, 1, -2, 0]]

def raw4597 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -1, -2, 2], ![1, -1, 0, 0]]

def raw4598 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, -1, 1]]

def raw4599 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![0, 1, 0, -1], ![2, -2, -2, 2]]

def raw4599step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, 3, 0, -2], ![2, -3, -1, 2]]

def raw4599step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -3, 2, 2], ![0, 0, -2, 2], ![0, 3, -1, -2], ![1, 0, 1, -2]]

def raw4600 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![1, -2, 0, 1], ![1, 1, -2, 0]]

def raw4600step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-1, 3, 0, -2], ![2, -3, 1, 0]]

def raw4600step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 2, -3], ![1, -2, 1, 0], ![1, 1, -2, 0]]

def raw4601 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![1, -1, -2, 2], ![1, 0, 0, -1]]

def raw4601step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -2, -1, 2]]

def raw4602 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw4602step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![-1, 3, -1, -1], ![2, -3, 1, 0]]

def raw4602step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 2, -3], ![1, 1, -2, 0]]

def raw4603 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw4603step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![-1, 3, 0, -2], ![2, -3, 0, 1]]

def raw4603step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 1, 0], ![1, -3, 0, 2], ![-2, 3, 0, -1]]

def raw4603step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 2, -3, 1], ![1, 0, 0, -1]]

def raw4604 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![1, 0, -2, 1], ![1, -1, 0, 0]]

def raw4604step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, 0, -1], ![-1, 3, -2, 0], ![2, -3, 1, 0]]

def raw4604step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 0, 1], ![1, -3, 2, 0], ![-2, 3, -1, 0]]

def raw4604step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 2, -3, 1], ![1, 0, 0, -1]]

def raw4605 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![1, 0, -1, 0], ![1, -1, -1, 1]]

def raw4605step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, 0, -1], ![-1, 3, -1, -1], ![2, -3, 0, 1]]

def raw4605step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 2, -3], ![1, 1, -2, 0]]

def raw4606 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, -2, 1], ![0, 0, 3, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw4606step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw4607 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, -2, 1], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def raw4607step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-1, -2, 0, 3], ![2, 1, 1, -4]]

def raw4607step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![1, -2, 1, 0], ![1, 1, 2, -4]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical144
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4608 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, -2, 1], ![1, -2, 2, -1], ![1, 0, 1, -2]]

def raw4609 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, -2, 1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw4609step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-1, -2, 3, 0], ![2, 1, -2, -1]]

def raw4609step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 2, 0], ![1, 2, -3, 0], ![-2, -1, 2, 1]]

def raw4609step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 1, -3], ![1, -1, -2, 2]]

def raw4610 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw4610step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-1, -2, 0, 3], ![2, 1, 0, -3]]

def raw4610step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![1, 2, 0, -3], ![-2, -1, 0, 3]]

def raw4610step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -2, 3], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw4611 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def raw4612 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, -2, 1], ![1, -1, 2, -2], ![1, -1, 1, -1]]

def raw4612step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def raw4613 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, -1, 0], ![1, -2, -1, 2], ![1, 0, 3, -4]]

def raw4613step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-1, -1, -1, 3], ![2, 0, 2, -4]]

def raw4613step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -2, 1, 1], ![0, 2, 2, -4], ![1, 1, -2, 0]]

def raw4614 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 2, -3]]

def raw4614step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-1, -1, 0, 2], ![2, 0, 1, -3]]

def raw4614step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw4615 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 0, 1, -2]]

def raw4615step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-1, -1, 1, 1], ![2, 0, 0, -2]]

def raw4615step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 2, 0], ![1, 1, -1, -1], ![-2, 0, 0, 2]]

def raw4615step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw4616 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw4616step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-1, -1, 2, 0], ![2, 0, -1, -1]]

def raw4616step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 0, 1, -2]]

def raw4617 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, -1, 3, -3]]

def raw4617step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-1, -1, -1, 3], ![2, 0, 1, -3]]

def raw4617step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 1, -1]]

def raw4618 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw4618step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-1, -1, 0, 2], ![2, 0, 0, -2]]

def raw4618step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, 1, -1]]

def raw4619 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def raw4619step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-1, -1, 1, 1], ![2, 0, -1, -1]]

def raw4619step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, -1, -1, 1]]

def raw4620 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def raw4620step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-1, 0, 2, -1], ![2, -1, -1, 0]]

def raw4620step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, -2, 1]]

def raw4621 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, -2, 1]]

def raw4621step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-1, 0, 3, -2], ![2, -1, -2, 1]]

def raw4621step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 2, 0], ![1, 0, -3, 2], ![-2, 1, 2, -1]]

def raw4621step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, -1, -2, 2]]

def raw4622 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def raw4622step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-1, 1, 1, -1], ![2, -2, 0, 0]]

def raw4622step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 2, 0], ![1, -1, -1, 1], ![-2, 2, 0, 0]]

def raw4622step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw4623 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 0, -2, 1]]

def raw4624 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, -1, 1, -1]]

def raw4624step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def raw4625 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, 2, -3], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def raw4625step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-1, 2, 0, -1], ![2, -3, 1, 0]]

def raw4625step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 2, 0], ![1, -2, 0, 1], ![-2, 3, -1, 0]]

def raw4625step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, 0, -2, 1]]

def raw4626 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, 2, -3], ![1, -2, 1, 0], ![1, 0, -2, 1]]

def raw4626step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-1, 2, 1, -2], ![2, -3, 0, 1]]

def raw4626step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -3, 2], ![1, -2, 2, -1], ![1, 1, 0, -2]]

def raw4627 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw4627step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-1, 2, -1, 0], ![2, -3, 1, 0]]

def raw4627step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![1, -2, 1, 0], ![-2, 3, -1, 0]]

def raw4627step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, 1, -1, -1]]

def raw4628 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, 3, -4], ![1, -2, -1, 2], ![1, 0, -1, 0]]

def raw4628step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-1, 3, -1, -1], ![2, -4, 2, 0]]

def raw4628step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -2, 1, 1], ![0, 2, 2, -4], ![1, 1, -2, 0]]

def raw4629 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, 3, -4], ![1, -2, 0, 1], ![1, 0, -2, 1]]

def raw4629step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-1, 3, 0, -2], ![2, -4, 1, 1]]

def raw4629step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -2, 1, 1], ![1, 1, -2, 0], ![1, 1, 2, -4]]

def raw4630 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, 3, -4], ![1, -1, -2, 2], ![1, -1, 0, 0]]

def raw4630step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-1, 3, -2, 0], ![2, -4, 2, 0]]

def raw4630step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -2, -1, 3], ![0, 2, 2, -4], ![1, 1, -2, 0]]

def raw4631 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, -1, 1]]

def raw4632 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![1, -2, -1, 2], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def raw4632step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, 1, 0], ![-1, -1, 3, -1], ![2, 2, -4, 0]]

def raw4632step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -2, 1, 1], ![0, 2, 2, -4], ![1, 1, -2, 0]]

def raw4633 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![1, -2, 2, -1], ![0, 0, -2, 2], ![1, 1, 1, -3]]

def raw4633step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![1, -2, 2, -1], ![1, 1, 1, -3]]

def raw4634 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![1, -2, 3, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw4634step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, 1, 0], ![-1, 3, -2, 0], ![2, -2, 1, -1]]

def raw4634step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![-1, 2, -1, 0], ![1, -3, 2, 0], ![-2, 2, -1, 1]]

def raw4634step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 1, -3], ![1, -1, -2, 2]]

def raw4635 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![1, -1, -2, 2], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw4635step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -1, 1, -1], ![-1, -2, 3, 0], ![2, 2, -4, 0]]

def raw4635step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -2, -1, 3], ![0, 2, 2, -4], ![1, 1, -2, 0]]

def raw4636 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![1, -1, 2, -2], ![0, 1, -2, 1], ![1, -1, 1, -1]]

def raw4636step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def raw4637 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![1, -1, 3, -3], ![0, 1, -2, 1], ![1, -1, 0, 0]]

def raw4637step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -1, 1, -1], ![-1, 3, -2, 0], ![2, -3, 1, 0]]

def raw4637step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![-1, 1, -1, 1], ![1, -3, 2, 0], ![-2, 3, -1, 0]]

def raw4637step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -2, 3], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw4638 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![1, 0, -2, 1], ![0, 1, 1, -2], ![1, -2, 2, -1]]

def raw4638step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 0, -2, 1]]

def raw4639 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, -1, 3], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def raw4639step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, 0, 1], ![1, 0, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical145
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4640 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, -1, 3], ![0, 1, 3, -4], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw4640step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def raw4641 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 0, 2], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw4641step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 2, 0, -2], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![-1, -1, -2, 4]]

def raw4641step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw4642 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw4642step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 2, -1, -1], ![0, -1, 1, 0], ![-1, 0, 0, 1], ![-1, 0, 0, 1]]

def raw4642step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw4643 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 1, 1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw4643step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw4644 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 1, 1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw4644step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 2, -1, -1], ![-1, 0, 1, 0], ![-1, -1, 0, 2]]

def raw4644step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw4645 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 1, 1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw4645step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 2, -1, -1], ![-1, 0, 0, 1], ![-1, -1, 1, 1]]

def raw4645step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 1, -1, -1]]

def raw4646 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 1, 1], ![1, 0, 1, -2], ![1, 1, -2, 0]]

def raw4646step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![1, -2, 1, 0], ![1, 1, 0, -2]]

def raw4647 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 2, 0], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def raw4647step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 2, -2, 0], ![0, -1, 0, 1], ![-1, 0, 2, -1], ![-1, 0, 0, 1]]

def raw4647step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -1, -1, 0]]

def raw4648 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 2, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw4648step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 2, -2, 0], ![0, -1, 0, 1], ![-1, 0, 1, 0], ![-1, 0, 1, 0]]

def raw4648step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw4649 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 2, 0], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw4649step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 2, -2, 0], ![0, -1, 0, 1], ![-2, 0, 2, 0]]

def raw4649step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw4650 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 2, 0], ![1, 0, -2, 1], ![1, 1, 0, -2]]

def raw4650step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 2, -2, 0], ![-1, 0, 2, -1], ![-1, -1, 0, 2]]

def raw4650step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, -1, -1, 0]]

def raw4651 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 2, 0], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw4651step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -2, 0, 1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw4651step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw4652 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -2, 3], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw4653 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -2, 3], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw4654 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -2, 3], ![0, 1, 3, -4], ![2, -1, -1, 0]]

def raw4655 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -2, 3], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw4655step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![0, -2, 0, 2], ![1, 3, 0, -4]]

def raw4655step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw4656 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -2, 3], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def raw4656step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw4657 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -2, 3], ![1, 0, 3, -4], ![1, 0, -1, 0]]

def raw4657step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw4658 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, -1, 0, 1], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw4658step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 1, 1, -2], ![0, 1, 0, -1], ![-1, 0, 1, 0], ![-1, -1, -2, 4]]

def raw4658step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw4659 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw4659step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 1, 1, -2], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, -1, -2, 4]]

def raw4659step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw4660 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def raw4660step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw4661 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 0, 3, -3], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw4661step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 0, 1]]

def raw4662 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw4663 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, -2, 1], ![2, -1, 3, -4]]

def raw4663step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -1, 1, -1], ![0, -1, -2, 3], ![1, 2, 1, -4]]

def raw4663step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 1, -1, 1], ![0, 1, 2, -3], ![-1, -2, -1, 4]]

def raw4663step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 2, 0, -3]]

def raw4664 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 3, -4]]

def raw4665 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw4665step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 1, 1, -2], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, -2, 3]]

def raw4665step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw4666 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw4667 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, -1, 3, -3]]

def raw4667step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw4668 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![2, -1, 2, -3]]

def raw4668step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -1, 1, -1], ![0, -1, -1, 2], ![1, 2, 0, -3]]

def raw4668step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -1, 1, -1]]

def raw4669 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw4669step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 1, 1, -2], ![0, -1, -2, 3], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw4669step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw4670 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw4671 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -2, 1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical146
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4672 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, 0, -1, 0], ![1, -1, -1, 1]]

def raw4672step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw4673 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, 3, -4], ![2, -1, -2, 1]]

def raw4673step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -1, 1, -1], ![0, -1, 3, -2], ![1, 2, -4, 1]]

def raw4673step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 1, -1, 1], ![0, 1, -3, 2], ![-1, -2, 4, -1]]

def raw4673step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 2, -3]]

def raw4674 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def raw4674step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 1, 1, -2], ![-1, 1, 1, -1], ![-1, -1, -2, 4]]

def raw4674step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def raw4675 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw4675step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 1, 1, -2], ![-1, 1, 0, 0], ![-1, -1, -1, 3]]

def raw4675step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw4676 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![1, -1, 3, -3], ![1, 1, -2, 0]]

def raw4676step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![0, -1, 3, -2], ![1, 2, -3, 0]]

def raw4676step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![0, 1, -3, 2], ![-1, -2, 3, 0]]

def raw4676step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 2, -3]]

def raw4677 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![1, 0, -2, 1], ![1, 0, 3, -4]]

def raw4677step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw4678 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![1, 0, 2, -3], ![1, 0, -1, 0]]

def raw4678step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw4679 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![1, 0, 3, -4], ![1, 0, -2, 1]]

def raw4679step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw4680 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![1, 1, 2, -4], ![1, -1, -1, 1]]

def raw4680step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 1, 1, -2], ![-1, -1, -2, 4], ![-1, 1, 1, -1]]

def raw4680step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def raw4681 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def raw4681step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 1, 0, -1], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![-1, -1, -2, 4]]

def raw4681step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw4682 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 0, 1], ![1, -1, -2, 2], ![1, 1, 2, -4]]

def raw4682step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![0, 0, -2, 2], ![1, 1, 2, -4]]

def raw4682step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![0, 0, 2, -2], ![-1, -1, -2, 4]]

def raw4682step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def raw4683 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 1, 0], ![1, -1, -2, 2], ![1, 1, 1, -3]]

def raw4683step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![0, 1, -2, 1], ![1, 0, 2, -3]]

def raw4683step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![0, -1, 2, -1], ![-1, 0, -2, 3]]

def raw4683step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw4684 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 1, 0], ![1, -1, 2, -2], ![1, 1, -3, 1]]

def raw4684step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![0, 1, 2, -3], ![1, 0, -2, 1]]

def raw4684step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![0, -1, -2, 3], ![-1, 0, 2, -1]]

def raw4684step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def raw4685 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw4685step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw4686 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw4686step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw4687 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw4687step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw4688 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw4688step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 1, -2, 1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 2, -1]]

def raw4688step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -1, -1, 0]]

def raw4689 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 2, -1], ![1, -1, -3, 3], ![1, 1, 1, -3]]

def raw4689step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![0, 2, -3, 1], ![1, -1, 3, -3]]

def raw4689step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![0, -2, 3, -1], ![-1, 1, -3, 3]]

def raw4689step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, -1, 3, -3]]

def raw4690 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 2, -1], ![1, -1, -2, 2], ![1, 1, 0, -2]]

def raw4690step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def raw4691 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 2, -1], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def raw4691step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, -1, 1, -1]]

def raw4692 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 2, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw4692step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw4693 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw4694 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 0, -2, 2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw4694step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw4695 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 0, -2, 2], ![1, 0, 0, -1], ![1, 0, -1, 0]]

def raw4695step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw4696 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 0, -2, 2], ![2, 0, -1, -1]]

def raw4696step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -2, 1, 0]]

def raw4697 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, -3, 2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw4698 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, -3, 2], ![2, -1, 0, -1]]

def raw4699 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw4700 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw4700step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def raw4701 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, -2, 1], ![2, -1, -1, 0]]

def raw4701step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def raw4702 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, -1, -2, 2], ![1, 0, 0, -1]]

def raw4703 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw4703step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical147
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4704 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw4704step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -2, 0]]

def raw4705 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, -2, 2], ![1, 0, -1, 0]]

def raw4706 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -2, 1]]

def raw4707 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -3, 2]]

def raw4708 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![1, -1, -3, 3], ![1, 1, 0, -2]]

def raw4708step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![0, 3, -3, 0], ![1, -2, 3, -2]]

def raw4708step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 3, -3], ![1, -2, 0, 1], ![1, 1, -1, -1]]

def raw4709 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![1, -1, -2, 2], ![1, 1, -1, -1]]

def raw4710 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![1, -1, -1, 1], ![1, 1, -2, 0]]

def raw4710step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw4711 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![1, -1, 0, 0], ![1, 1, -3, 1]]

def raw4711step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![0, 3, 0, -3], ![1, -2, 0, 1]]

def raw4711step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -2, 0, 1]]

def raw4712 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![1, 0, -3, 2], ![1, 0, 0, -1]]

def raw4712step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw4713 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![1, 0, -2, 1], ![1, 0, -1, 0]]

def raw4713step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw4714 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![1, 0, -1, 0], ![1, 0, -2, 1]]

def raw4714step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw4715 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![1, 0, 0, -1], ![1, 0, -3, 2]]

def raw4715step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw4716 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![1, 1, -2, 0], ![1, -1, -1, 1]]

def raw4716step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw4717 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -3, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw4718 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -3, 3], ![0, 1, 0, -1], ![2, -2, 3, -3]]

def raw4718step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, -3, 0, 3], ![1, 3, -1, -3]]

def raw4718step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![0, 3, 0, -3], ![-1, -3, 1, 3]]

def raw4718step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 2, 0, -2], ![1, -1, -3, 3]]

def raw4719 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -3, 3], ![0, 1, 1, -2], ![2, -2, 2, -2]]

def raw4719step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, -3, 1, 2], ![1, 3, -2, -2]]

def raw4719step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -3, 2], ![1, -2, 3, -2], ![1, 1, 0, -2]]

def raw4720 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -3, 3], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw4721 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -3, 3], ![0, 1, 3, -4], ![2, -2, 0, 0]]

def raw4722 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -3, 3], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def raw4723 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -3, 3], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw4723step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -3, 3], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw4724 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -3, 3], ![1, 0, 3, -4], ![1, -1, 0, 0]]

def raw4724step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -3, 3], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw4725 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![2, -2, 0, 0]]

def raw4726 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 0, -1, 1], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def raw4727 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 0, 0, 0], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw4727step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![1, 0, 0, 1, -2], ![0, -2, 0, 0, 2], ![1, 2, 0, -1, -2]]

def raw4727step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, 0, -2], ![-1, 0, 0, -1, 2], ![0, 2, 0, 0, -2], ![-1, -2, 0, 1, 2]]

def raw4727step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![0, 2, 0, -2], ![-1, -2, 1, 2]]

def raw4727step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw4728 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def raw4729 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def raw4729step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, 2, -2], ![0, 0, -1, 1], ![0, -1, 0, 1], ![-2, 2, -1, 1]]

def raw4729step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw4730 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def raw4731 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![2, -1, 0, -1]]

def raw4731step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw4732 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def raw4733 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw4734 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![2, -2, 3, -3]]

def raw4734step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, -2, -1, 3], ![1, 2, 0, -3]]

def raw4734step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, 0, 1, -2]]

def raw4735 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw4735step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, 2, -2], ![0, -1, 0, 1], ![-1, 2, -2, 1], ![-1, 0, 0, 1]]

def raw4735step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical148
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4736 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw4736step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, -2, 0, 2], ![1, 2, -1, -2]]

def raw4736step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![0, 2, 0, -2], ![-1, -2, 1, 2]]

def raw4736step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw4737 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, -2, 1, -1]]

def raw4737step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, 2, -2], ![0, -1, -1, 2], ![-2, 2, -1, 1]]

def raw4737step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw4738 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw4738step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, 2, -2], ![0, -1, -2, 3], ![-1, 1, 0, 0], ![-1, 1, 0, 0]]

def raw4738step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw4739 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 1, 2, -3], ![2, -2, 0, 0]]

def raw4739step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, 2, -2], ![0, -1, -2, 3], ![-2, 2, 0, 0]]

def raw4739step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![2, 0, 0, -2]]

def raw4740 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw4741 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, -1, 1]]

def raw4741step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw4742 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 1, 3, -4], ![2, -2, -1, 1]]

def raw4742step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, -2, 3, -1], ![1, 2, -4, 1]]

def raw4742step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![0, 2, -3, 1], ![-1, -2, 4, -1]]

def raw4742step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, -2, 0], ![2, 0, 1, -3]]

def raw4743 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![1, -2, 0, 1], ![1, 1, 2, -4]]

def raw4743step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, 2, -2], ![-1, 2, 0, -1], ![-1, -1, -2, 4]]

def raw4743step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def raw4744 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![1, -2, 1, 0], ![1, 1, 1, -3]]

def raw4744step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![0, -2, 1, 1], ![1, 2, 0, -3]]

def raw4744step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 2, -1], ![0, 2, -1, -1], ![-1, -2, 0, 3]]

def raw4744step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw4745 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![1, -2, 3, -2], ![1, 1, -1, -1]]

def raw4745step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![0, -2, 3, -1], ![1, 2, -2, -1]]

def raw4745step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, 1, -2]]

def raw4746 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![1, -1, -1, 1], ![1, 0, 3, -4]]

def raw4746step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw4747 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw4747step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, 0, 2], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw4748 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw4748step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![0, -2, 3, -1], ![1, 2, -3, 0]]

def raw4748step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw4749 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![1, 0, -1, 0], ![1, -1, 3, -3]]

def raw4749step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, 0, -1], ![0, -2, -1, 3], ![1, 2, 0, -3]]

def raw4749step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw4750 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![1, 0, 3, -4], ![1, -1, -1, 1]]

def raw4750step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw4751 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, -1, 0, 1], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def raw4751step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-1, 1, 1, -1], ![-1, -1, -2, 4]]

def raw4751step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw4752 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -2, 2], ![0, 1, 3, -4], ![2, -2, 0, 0]]

def raw4752step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![2, -2, 0, 0]]

def raw4753 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -2, 2], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def raw4753step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 0, -1, 1], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def raw4754 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![2, -2, 0, 0]]

def raw4754step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, -2, 3], ![-2, 2, 0, 0]]

def raw4754step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw4755 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![2, -2, -1, 1]]

def raw4756 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -2, 0, 1], ![1, 1, 2, -4]]

def raw4756step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 2, 0, -1], ![-1, -1, -2, 4]]

def raw4756step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw4757 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -2, 1, 0], ![1, 1, 1, -3]]

def raw4757step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![1, 1, -2, 0], ![1, 1, 1, -3]]

def raw4758 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 0, 3, -4]]

def raw4758step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw4759 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw4759step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw4760 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def raw4760step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![1, 0, 0, 1, -2], ![0, -1, 0, -1, 2], ![1, 1, 0, 0, -2]]

def raw4760step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, -1, -1, 2], ![1, 1, 0, -2]]

def raw4760step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw4761 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![2, -2, 2, -2]]

def raw4762 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def raw4762step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, 1, -1], ![0, 0, -1, 1], ![0, -1, 1, 0], ![-2, 2, -1, 1]]

def raw4762step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw4763 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, -2, 1, -1]]

def raw4764 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, 0, 0]]

def raw4764step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, 1, -1], ![0, 0, -2, 2], ![0, -1, 1, 0], ![-2, 2, 0, 0]]

def raw4764step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw4765 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, 3, -3], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw4765step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -2, 0, 1]]

def raw4766 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def raw4767 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical149
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4768 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, -2, 1], ![2, -2, 3, -3]]

def raw4768step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, -1, -2, 3], ![1, 1, 1, -3]]

def raw4768step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 1, 1, -3]]

def raw4769 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, -1, 2], ![1, 0, 3, -4]]

def raw4769step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def raw4770 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 2, -3]]

def raw4770step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-1, 2, 0, -1], ![-1, 0, -2, 3]]

def raw4770step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw4771 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 3, -2], ![1, 0, -1, 0]]

def raw4771step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw4772 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, -1, 3, -3]]

def raw4773 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw4773step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw4774 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, -1, -1, 1]]

def raw4774step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, -1, 3, -3]]

def raw4775 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def raw4775step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, -1, -1, 2], ![1, 1, 0, -2]]

def raw4775step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw4776 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw4776step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, 1, -1], ![0, -1, -2, 3], ![-1, 1, 1, -1], ![-1, 1, 0, 0]]

def raw4776step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw4777 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![2, -2, -1, 1]]

def raw4777step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, -1, 2, -1], ![1, 1, -3, 1]]

def raw4777step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![0, 1, -2, 1], ![-1, -1, 3, -1]]

def raw4777step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def raw4778 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -2, -1, 2], ![1, 0, -1, 0]]

def raw4778step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def raw4779 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, -2, 2], ![1, -1, 0, 0]]

def raw4780 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, -1, 1]]

def raw4781 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![2, -2, -2, 2]]

def raw4781step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, -1, 3, -2], ![1, 1, -4, 2]]

def raw4781step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![0, 1, -3, 2], ![-1, -1, 4, -2]]

def raw4781step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 2, -3]]

def raw4782 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![1, -2, -1, 2], ![1, 1, 2, -4]]

def raw4782step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![0, -1, -1, 2], ![1, 1, 2, -4]]

def raw4782step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 2, -1], ![0, 1, 1, -2], ![-1, -1, -2, 4]]

def raw4782step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw4783 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![1, -2, 3, -2], ![1, 1, -2, 0]]

def raw4783step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![0, -1, 3, -2], ![1, 1, -2, 0]]

def raw4783step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw4784 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![1, -1, -2, 2], ![1, 0, 3, -4]]

def raw4784step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![0, -1, -2, 3], ![1, 1, 2, -4]]

def raw4784step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 1, 0], ![0, 1, 2, -3], ![-1, -1, -2, 4]]

def raw4784step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, 2, -3]]

def raw4785 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![1, -1, 3, -3], ![1, 0, -2, 1]]

def raw4785step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![0, -1, 3, -2], ![1, 1, -3, 1]]

def raw4785step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 1, 1, -3]]

def raw4786 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 0, 0], ![0, 1, -2, 1], ![2, -2, 2, -2]]

def raw4786step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, 0, -2, 2], ![1, 0, 1, -2]]

def raw4786step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 1, -2], ![0, -2, 2], ![1, 1, -2]]

def raw4786step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]

def raw4787 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 0, 0], ![0, 1, 2, -3], ![2, -2, -2, 2]]

def raw4787step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, 0, 2, -2], ![1, 0, -3, 2]]

def raw4787step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 1, -2], ![0, 2, -2], ![1, -3, 2]]

def raw4787step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

def raw4788 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, -1, 1]]

def raw4788step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -1, 1, 0], ![-2, 2, 1, -1]]

def raw4788step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def raw4789 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, -2, 2]]

def raw4789step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw4790 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, -2, -3, 3]]

def raw4791 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, -2, 2]]

def raw4792 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, -3, 3]]

def raw4793 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 1, -3, 2], ![2, -2, 2, -2]]

def raw4793step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, 1, -3, 2], ![1, -1, 2, -2]]

def raw4793step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![0, -1, 3, -2], ![-1, 1, -2, 2]]

def raw4793step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw4794 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw4794step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw4795 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![2, -2, 1, -1]]

def raw4795step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, 1, -2, 1], ![1, -1, 1, -1]]

def raw4795step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![0, -1, 2, -1], ![-1, 1, -1, 1]]

def raw4795step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw4796 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -2, 2], ![1, -1, 2, -2]]

def raw4797 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, -1, 1, -1]]

def raw4797step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw4798 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -2, 2], ![1, -1, 1, -1]]

def raw4798step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw4799 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, -2, -2, 2]]

def raw4799step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, 1, 1, -2], ![1, -1, -2, 2]]

def raw4799step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 1, 0, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw480 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![2, 2, -4]]

def raw480step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, 0, 1], ![-2, -2, 4]]

def raw480step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 3, -3], ![2, 0, -2]]

def raw481 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, 1, -2]]

def raw481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

def raw482 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 1, -2], ![2, 1, -3]]

def raw482step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 1, -2], ![1, 2, -3]]

def raw483 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1], ![1, 0, -1]]

def raw483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, -2, 3], ![-1, 0, 1], ![-1, 0, 1]]

def raw483step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![2, 0, -2]]

def raw484 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]

def raw484step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, -2, 3], ![-2, 0, 2]]

def raw484step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![2, 0, -2]]

def raw485 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 3, -4], ![2, -1, -1]]

def raw485step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, -3, 4], ![-2, 1, 1]]

def raw485step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]

def raw486 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![2, 0, -2], ![1, 2, -3]]

def raw486step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-2, 0, 2], ![-1, -2, 3]]

def raw486step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![2, 0, -2]]

def raw487 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![3, -1, -2]]

def raw487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![-3, 1, 2]]

def raw487step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-3, 1, 2]]

def raw487step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

def raw488 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]

def raw488step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]

def raw488step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 1, 0], ![-2, -2, 4]]

def raw488step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw489 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 0, 0], ![1, 2, -3], ![2, -1, -1]]

def raw489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 0, 0], ![-1, -2, 3], ![-2, 1, 1]]

def raw489step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, -2, 3], ![-2, 1, 1]]

def raw489step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw490 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]

def raw490step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]

def raw490step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

def raw491 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]

def raw492 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]

def raw493 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

def raw493step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]

def raw493step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw494 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]

def raw494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]

def raw494step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw495 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]

def raw496 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

def raw496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]

def raw496step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw497 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

def raw497step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]

def raw497step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw498 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

def raw499 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]

def raw499step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-3, 1, 2]]

def raw499step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

def raw500 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]

def raw501 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]

def raw502 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![3, -2, -1]]

def raw503 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]

def raw503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -3, 4]]

def raw503step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw504 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

def raw504step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]

def raw504step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw505 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]

def raw505step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 1, 0], ![-2, -2, 4]]

def raw505step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw506 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]

def raw506step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, -2, 3], ![-2, 1, 1]]

def raw506step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw507 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]

def raw507step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]

def raw507step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 0, -1], ![1, 2, -3]]

def raw508 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]

def raw508step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]

def raw508step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![2, -2, 0]]

def raw509 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]

def raw509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 0, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3]]

def raw509step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3]]

def raw509step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![2, -1, -1]]

def raw510 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]

def raw510step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 0, 0], ![-1, 2, -1], ![-2, -2, 4]]

def raw510step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 2, -1], ![-2, -2, 4]]

def raw510step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, -1, -1]]

def raw511 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

def raw511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]

def raw511step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]

def raw511step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical150
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4800 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 1, 2, -3], ![2, -2, -3, 3]]

def raw4800step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, 1, 2, -3], ![1, -1, -3, 3]]

def raw4800step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![0, -1, -2, 3], ![-1, 1, 3, -3]]

def raw4800step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, -1, 3, -3]]

def raw4801 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![1, -2, -2, 3], ![1, 1, 1, -3]]

def raw4801step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![0, 1, -2, 1], ![1, -1, 3, -3]]

def raw4801step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 2, -1], ![0, -1, 2, -1], ![-1, 1, -3, 3]]

def raw4801step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 2, -1, -1], ![1, -1, 3, -3]]

def raw4802 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![1, -2, 2, -1], ![1, 1, -3, 1]]

def raw4802step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![0, 1, 2, -3], ![1, -1, -1, 1]]

def raw4802step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 2, -1], ![0, -1, -2, 3], ![-1, 1, 1, -1]]

def raw4802step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def raw4803 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![1, -1, -3, 3], ![1, 0, 2, -3]]

def raw4803step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![0, 1, -3, 2], ![1, -1, 3, -3]]

def raw4803step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 1, 0], ![0, -1, 3, -2], ![-1, 1, -3, 3]]

def raw4803step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 0, 1], ![0, 2, -1, -1], ![1, -1, 3, -3]]

def raw4804 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![1, -1, 2, -2], ![1, 0, -3, 2]]

def raw4804step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![0, 1, 2, -3], ![1, -1, -2, 2]]

def raw4804step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 1, 0], ![0, -1, -2, 3], ![-1, 1, 2, -2]]

def raw4804step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, -1, 2, -2]]

def raw4805 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw4805step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, 0, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw4806 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, -2, 2]]

def raw4806step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, -2, 2]]

def raw4807 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, -3, 3]]

def raw4807step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, -3, 3]]

def raw4808 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, 1, -3, 2], ![2, -2, 1, -1]]

def raw4808step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, 2, -3, 1], ![1, -2, 2, -1]]

def raw4808step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![0, -2, 3, -1], ![-1, 2, -2, 1]]

def raw4808step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![2, -1, 1, -2]]

def raw4809 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw4809step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, -2, 2], ![0, -1, 2, -1], ![-1, 1, 0, 0], ![-1, 1, 0, 0]]

def raw4809step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw4810 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, -2, 0, 0]]

def raw4810step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, -2, 2], ![0, -1, 2, -1], ![-2, 2, 0, 0]]

def raw4810step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw4811 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def raw4811step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, -2, 2], ![0, -1, 1, 0], ![-1, 2, 0, -1], ![-1, 0, 1, 0]]

def raw4811step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw4812 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, -2, 2], ![1, -1, 1, -1]]

def raw4813 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw4813step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw4814 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, -1, 1]]

def raw4814step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, 2, -1, -1], ![1, -2, 0, 1]]

def raw4814step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![0, -2, 1, 1], ![-1, 2, 0, -1]]

def raw4814step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw4815 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -2, 2], ![1, -1, 0, 0]]

def raw4815step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw4816 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, -2, 2]]

def raw4816step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, 2, 0, -2], ![1, -2, -1, 2]]

def raw4816step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw4817 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, 1, 1, -2], ![2, -2, -3, 3]]

def raw4817step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, 2, 1, -3], ![1, -2, -2, 3]]

def raw4817step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, 1, 0, -3]]

def raw4818 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![1, -2, -2, 3], ![1, 1, 0, -2]]

def raw4818step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def raw4819 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![1, -1, -3, 3], ![1, 0, 1, -2]]

def raw4819step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -2, 0, 1]]

def raw4820 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![1, -1, -2, 2], ![1, 0, 0, -1]]

def raw4820step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw4821 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![1, 0, -3, 2], ![1, -1, 1, -1]]

def raw4821step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw4822 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 3, -3], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw4822step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -3, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw4823 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, -2, 2], ![1, -1, 0, 0]]

def raw4824 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![2, -2, -2, 2]]

def raw4824step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, 3, -1, -2], ![1, -3, 0, 2]]

def raw4824step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![0, -3, 1, 2], ![-1, 3, 0, -2]]

def raw4824step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 2, 0, -2], ![1, 0, -3, 2]]

def raw4825 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 3, -3], ![0, 1, 0, -1], ![2, -2, -3, 3]]

def raw4825step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, 3, 0, -3], ![1, -3, -1, 3]]

def raw4825step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![0, -3, 0, 3], ![-1, 3, 1, -3]]

def raw4825step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -3, 3], ![0, 2, 0, -2], ![1, -1, 3, -3]]

def raw4826 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 3, -3], ![1, -1, -2, 2], ![1, 0, -1, 0]]

def raw4826step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![0, 3, -2, -1], ![1, -3, 2, 0]]

def raw4826step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw4827 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 3, -3], ![1, -1, -1, 1], ![1, 0, -2, 1]]

def raw4827step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -2, 0, 1]]

def raw4828 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 3, -3], ![1, -1, 0, 0], ![1, 0, -3, 2]]

def raw4828step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -3, 3], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw4829 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 3, -3], ![1, 0, -3, 2], ![1, -1, 0, 0]]

def raw4829step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -3, 3], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw4830 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, -3, 2], ![0, 0, 2, -2], ![2, -2, 1, -1]]

def raw4830step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 1, 0, -2], ![0, -3, 2, 1], ![1, 2, -2, -1]]

def raw4830step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, -1, 0, 2], ![0, 3, -2, -1], ![-1, -2, 2, 1]]

def raw4830step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![2, -1, 1, -2]]

def raw4831 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, -3, 2], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def raw4831step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![0, -3, 0, 3], ![1, 2, 1, -4]]

def raw4831step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -3, 3], ![1, -2, 1, 0], ![1, 1, 2, -4]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical151
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4832 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, -3, 2], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw4832step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![0, -3, 3, 0], ![1, 2, -2, -1]]

def raw4832step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, 0, -3, 3], ![0, 1, 1, -2], ![1, -2, 0, 1]]

def raw4833 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, -3, 2], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw4833step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![0, -3, 0, 3], ![1, 2, 0, -3]]

def raw4833step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 0, -3, 3], ![0, 1, 2, -3], ![1, -2, 0, 1]]

def raw4834 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, -2, 1], ![1, -2, -1, 2], ![1, 0, 3, -4]]

def raw4834step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![0, -2, -1, 3], ![1, 1, 2, -4]]

def raw4834step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -2, 1, 1], ![1, 1, -2, 0], ![1, 1, 2, -4]]

def raw4835 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, -2, 1], ![1, -2, 0, 1], ![1, 0, 2, -3]]

def raw4835step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, -1, 2, -1], ![-1, 2, 0, -1], ![-1, 0, -2, 3]]

def raw4835step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw4836 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, -2, 1], ![1, -2, 3, -2], ![1, 0, -1, 0]]

def raw4836step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![0, -2, 3, -1], ![1, 1, -2, 0]]

def raw4836step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, 0, -2, 1]]

def raw4837 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, -2, 1], ![1, -1, -1, 1], ![1, -1, 3, -3]]

def raw4837step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![0, -2, -1, 3], ![1, 1, 1, -3]]

def raw4837step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 1, 1, -3]]

def raw4838 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw4838step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![0, -2, 0, 2], ![1, 1, 0, -2]]

def raw4838step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![0, 2, 0, -2], ![-1, -1, 0, 2]]

def raw4838step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw4839 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def raw4839step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def raw4840 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, -1, 0], ![1, -1, -2, 2], ![1, -1, 3, -3]]

def raw4840step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![0, -1, -2, 3], ![1, 0, 2, -3]]

def raw4840step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![0, 1, 2, -3], ![-1, 0, -2, 3]]

def raw4840step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 2, -1, -1], ![1, 0, 2, -3]]

def raw4841 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, -1, 2, -2]]

def raw4841step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![0, -1, -1, 2], ![1, 0, 1, -2]]

def raw4841step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw4842 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, 0, -1], ![1, -1, -2, 2], ![1, -1, 2, -2]]

def raw4842step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![0, 0, -2, 2], ![1, -1, 2, -2]]

def raw4842step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![0, 0, 2, -2], ![-1, 1, -2, 2]]

def raw4842step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, -1, -1], ![1, -1, 2, -2]]

def raw4843 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 1, -1]]

def raw4843step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, -1, 0, 1], ![-1, 1, 1, -1], ![-1, 1, -1, 1]]

def raw4843step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def raw4844 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 0, -2, 1]]

def raw4844step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![1, -2, 1, 0], ![1, 1, 0, -2]]

def raw4845 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, 1, -2], ![1, -1, -2, 2], ![1, -1, 1, -1]]

def raw4845step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def raw4846 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, 2, -3], ![1, -1, -2, 2], ![1, -1, 0, 0]]

def raw4846step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![0, 2, -2, 0], ![1, -3, 2, 0]]

def raw4846step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw4847 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, -1, -1, 1]]

def raw4847step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, -1, -2, 3], ![-1, 1, 1, -1], ![-1, 1, 1, -1]]

def raw4847step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def raw4848 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, 3, -4], ![1, -1, -3, 3], ![1, -1, 0, 0]]

def raw4848step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![0, 3, -3, 0], ![1, -4, 3, 0]]

def raw4848step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -3, 3], ![0, 1, 3, -4], ![1, -2, 1, 0]]

def raw4849 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, 3, -4], ![1, -1, -2, 2], ![1, -1, -1, 1]]

def raw4850 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, -2, 2]]

def raw4850step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, 3, -4], ![1, -1, -2, 2], ![1, -1, -1, 1]]

def raw4851 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, -2, 3], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def raw4851step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, 1, 0], ![0, -2, 3, -1], ![1, 3, -4, 0]]

def raw4851step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -2, 1, 0]]

def raw4852 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, -1, 2], ![0, 1, -2, 1], ![1, 0, 3, -4]]

def raw4852step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, 1, 0], ![0, -1, -2, 3], ![1, 2, 1, -4]]

def raw4852step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -2, 1, 1], ![1, 1, -2, 0], ![1, 1, 2, -4]]

def raw4853 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, -1, 2], ![0, 1, 3, -4], ![1, 0, -2, 1]]

def raw4853step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, 1, 0], ![0, -1, 3, -2], ![1, 2, -4, 1]]

def raw4853step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def raw4854 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, 3, -2], ![0, 0, -2, 2], ![1, 1, -1, -1]]

def raw4854step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, 0, 1], ![0, 3, -2, -1], ![1, -2, 2, -1]]

def raw4854step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, 1, -2]]

def raw4855 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, 3, -2], ![0, 1, -3, 2], ![1, 0, 0, -1]]

def raw4855step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, 1, 0], ![0, 3, -3, 0], ![1, -2, 2, -1]]

def raw4855step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, 0, -3, 3], ![0, 1, 1, -2], ![1, -2, 0, 1]]

def raw4856 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -1, -3, 3], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw4856step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -1, 1, -1], ![0, -3, 3, 0], ![1, 3, -4, 0]]

def raw4856step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -3, 3], ![0, 1, 3, -4], ![1, -2, 1, 0]]

def raw4857 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -1, -2, 2], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def raw4857step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, 3, -4], ![1, -1, -2, 2], ![1, -1, -1, 1]]

def raw4858 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -1, 3, -3], ![0, 1, -2, 1], ![1, -1, -1, 1]]

def raw4858step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -1, 1, -1], ![0, 3, -2, -1], ![1, -3, 1, 1]]

def raw4858step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 1, 1, -3]]

def raw4859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def raw4859step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]

def raw4859step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw4860 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]

def raw4860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]

def raw4860step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw4861 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![2, -1, -1]]

def raw4861step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![1, 1, -2], ![1, 1, -2]]

def raw4862 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]

def raw4863 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![1, -1, 0], ![2, 2, -4]]

def raw4863step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![1, 2, -3], ![-1, 1, 0], ![-2, -2, 4]]

def raw4863step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical152
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4864 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![2, -2, 0], ![1, 3, -4]]

def raw4864step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![1, 2, -3], ![-2, 2, 0], ![-1, -3, 4]]

def raw4864step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![1, -3, 2], ![2, -1, -1]]

def raw4865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]

def raw4865step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]

def raw4865step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw4867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def raw4867step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

def raw4868 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

def raw4868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

def raw4869 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def raw4869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]

def raw4869step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw4870 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]

def raw4870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]

def raw4870step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]

def raw4871 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]

def raw4871step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]

def raw4872 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

def raw4872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

def raw4873 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 3, -4]]

def raw4874 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -2, 1], ![2, 2, -4]]

def raw4874step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-1, 2, -1], ![-2, -2, 4]]

def raw4874step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]

def raw4875 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -2, 1], ![1, 3, -4]]

def raw4875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 3, -4]]

def raw4876 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

def raw4876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]

def raw4878 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]

def raw4878step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2]]

def raw4879 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![2, -3, 1], ![1, 3, -4]]

def raw4879step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-2, 3, -1], ![-1, -3, 4]]

def raw4879step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 4, -3], ![1, -2, 1], ![2, -1, -1]]

def raw4880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]

def raw4880step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw4882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw4882step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]

def raw4882step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw4884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw4884step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]

def raw4884step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw4885 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

def raw4885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw4887 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

def raw4887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw4888 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

def raw4888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]

def raw4891 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]

def raw4891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]

def raw4892 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

def raw4892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw4893 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]

def raw4893step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2]]

def raw4894 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 3, -2], ![1, -3, 2], ![1, -1, 0], ![1, 0, -1]]

def raw4894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]

def raw4895 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw4895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]

def raw4895step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![2, -1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical153
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4896 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw4897 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw4898 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1]]

def raw4898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw4899 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def raw4900 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw4901 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 2, -2], ![2, 0, -2]]

def raw4901step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 3, -3], ![0, -2, 2], ![-2, 0, 2]]

def raw4901step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

def raw4902 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw4903 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 3, -3], ![2, -1, -1]]

def raw4904 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, -1, 0], ![1, 3, -4]]

def raw4905 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 0, -1], ![1, 2, -3]]

def raw4906 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]

def raw4907 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 2, -3], ![1, 0, -1]]

def raw4907step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 0, -1], ![1, 2, -3]]

def raw4908 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![2, 2, -4]]

def raw4908step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![0, 3, -3], ![-2, -2, 4]]

def raw4908step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, -1, -1]]

def raw4909 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def raw4910 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]

def raw4911 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2]]

def raw4911step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]

def raw4911step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw4912 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw4913 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw4914 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw4914step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

def raw4915 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]

def raw4915step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 2, -2], ![0, -1, 1], ![-2, 0, 2]]

def raw4915step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

def raw4916 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw4917 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]

def raw4917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw4918 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]

def raw4919 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw4919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw4921 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -2, 1], ![1, 3, -4]]

def raw4922 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

def raw4923 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]

def raw4923step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw4924 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]

def raw4924step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw4925 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![2, 1, -3]]

def raw4925step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![0, 2, -2], ![-2, -1, 3]]

def raw4925step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]

def raw4926 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

def raw4926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def raw4927 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 2, -3]]

def raw4927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical154
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 3, -5]]

def raw4928step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, -3, 5]]

def raw4928step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw4931 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 3, -4]]

def raw4932 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]

def raw4933 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]

def raw4934 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]

def raw4934step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]

def raw4935 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]

def raw4935step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]

def raw4936 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]

def raw4936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1]]

def raw4936step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1]]

def raw4936step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw4937 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]

def raw4937step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]

def raw4939 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

def raw4939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]

def raw4939step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw4940 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw4941 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw4942 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]

def raw4942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw4943 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]

def raw4944 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -3, 2], ![1, 3, -4]]

def raw4945 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

def raw4946 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]

def raw4947 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

def raw4947step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1]]

def raw4947step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw4948 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]

def raw4948step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]

def raw4949 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]

def raw4949step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1]]

def raw4949step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1]]

def raw4949step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![1, 0, -1]]

def raw4950 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![2, -1, -1]]

def raw4950step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![1, 0, -1]]

def raw4950step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw4951 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1]]

def raw4951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]

def raw4952 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0]]

def raw4952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]

def raw4953 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2]]

def raw4953step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

def raw4954 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

def raw4954step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]

def raw4955 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]

def raw4955step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0]]

def raw4955step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw4956 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![2, -2, 0]]

def raw4956step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![0, -1, 1], ![-2, 2, 0]]

def raw4956step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -1, 0]]

def raw4957 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1]]

def raw4957step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

def raw4958 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]

def raw4958step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw4959 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 3, -3], ![1, -3, 2], ![1, -1, 0]]

def raw4959step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 0, -1], ![1, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical155
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4960 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 3, -3], ![1, -2, 1], ![1, -2, 1]]

def raw4960step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]

def raw4961 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -4, 3], ![0, 2, -2], ![1, 1, -2]]

def raw4961step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -2, 1], ![1, 3, -4]]

def raw4962 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -4, 3], ![0, 3, -3], ![1, 0, -1]]

def raw4962step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, -1, 0], ![1, 3, -4]]

def raw4963 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -4, 3], ![1, 3, -4]]

def raw4964 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -3, 2], ![0, 2, -2], ![1, 0, -1]]

def raw4964step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

def raw4965 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -3, 2], ![1, 2, -3]]

def raw4966 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]

def raw4967 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![1, 0, -1]]

def raw4967step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1]]

def raw4967step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![1, 0, -1]]

def raw4968 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![-2, -2, 1, 3], ![4, 1, -2, -3]]

def raw4968step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![1, -2, 1], ![1, 1, -2], ![0, 3, -3]]

def raw4968step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, -2, 1], ![1, 1, -2]]

def raw4969 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![-2, -2, 2, 2], ![4, 1, -3, -2]]

def raw4969step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![1, -2, 1], ![1, 2, -3], ![0, 2, -2]]

def raw4969step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -2, 1], ![1, 2, -3]]

def raw4970 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![-2, 1, 2, -1], ![4, -2, -3, 1]]

def raw4970step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![1, 1, -2], ![1, 2, -3], ![0, -1, 1]]

def raw4970step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![1, 1, -2], ![1, 2, -3]]

def raw4971 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![-1, -2, 1, 2], ![3, 1, -2, -2]]

def raw4971step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -2, 1], ![1, 1, -2], ![0, 2, -2]]

def raw4971step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def raw4972 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![-1, -2, 2, 1], ![3, 1, -3, -1]]

def raw4972step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -2, 1], ![1, 2, -3], ![0, 1, -1]]

def raw4972step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

def raw4973 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![-1, 1, 1, -1], ![3, -2, -2, 1]]

def raw4973step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![1, 1, -2], ![1, 1, -2], ![0, -1, 1]]

def raw4973step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]

def raw4974 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![-1, 1, 2, -2], ![3, -2, -3, 2]]

def raw4974step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![1, 1, -2], ![1, 2, -3], ![0, -2, 2]]

def raw4974step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 1, -2], ![1, 2, -3]]

def raw4975 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -3, 1, 2], ![2, 2, -2, -2]]

def raw4975step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -3, 2], ![1, 1, -2], ![0, 2, -2]]

def raw4975step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

def raw4976 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -3, 2, 1], ![2, 2, -3, -1]]

def raw4976step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -3, 2], ![1, 2, -3], ![0, 1, -1]]

def raw4976step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -3, 2], ![1, 2, -3]]

def raw4977 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -2, -2, 4], ![2, 1, 1, -4]]

def raw4977step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -2, 1], ![1, -2, 1], ![0, 4, -4]]

def raw4977step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![1, -2, 1], ![1, -2, 1]]

def raw4978 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -2, -1, 3], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw4978step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def raw4979 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -2, -1, 3], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw4979step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -2, 0, 1], ![1, -1, -1, 1], ![0, 3, 0, -3]]

def raw4979step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -2, 0, 1]]

def raw4980 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -2, 0, 2], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw4980step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, -1, 1, 0], ![1, 1, -2, 0], ![1, 1, 1, -3]]

def raw4981 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -2, 1, 1], ![2, 1, -2, -1]]

def raw4981step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -2, 1], ![1, 1, -2], ![0, 1, -1]]

def raw4981step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw4982 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -2, 3, -1], ![2, 1, -4, 1]]

def raw4982step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -2, 1], ![1, 3, -4], ![0, -1, 1]]

def raw4982step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -2, 1], ![1, 3, -4]]

def raw4983 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw4984 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def raw4985 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw4985step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -2, 1, 0]]

def raw4986 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw4987 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 0, 2, -2], ![2, 0, 0, -2]]

def raw4987step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -2, 1, 0]]

def raw4988 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw4989 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw4990 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 1, 1, -2], ![2, -1, 1, -2]]

def raw4990step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -1, 1, -1], ![1, -3, 1, 1], ![0, 4, -2, -2]]

def raw4990step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def raw4991 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical156
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4992 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 1, 2, -3], ![2, -1, 0, -1]]

def raw4992step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, -1, 0], ![0, 1, 3, -4], ![0, -1, -2, 3], ![-2, 1, 0, 1]]

def raw4992step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -2, 3], ![0, 1, 3, -4], ![2, -1, -1, 0]]

def raw4993 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw4993step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![1, -3, 0, 2], ![0, 4, 0, -4]]

def raw4993step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 4, -4], ![0, 1, -3, 2], ![1, -2, 0, 1]]

def raw4994 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![1, -1, 1, -1], ![1, 1, 1, -3]]

def raw4995 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![1, -1, 2, -2], ![1, 1, 0, -2]]

def raw4995step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![1, -3, 2, 0], ![0, 4, -2, -2]]

def raw4995step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 2, -3], ![1, -2, 1, 0], ![1, 1, -1, -1]]

def raw4996 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![1, 0, 1, -2], ![1, 0, 1, -2]]

def raw4996step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -2, 1, 0]]

def raw4997 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![1, 0, 2, -3], ![1, 0, 0, -1]]

def raw4997step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw4998 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![1, 1, 1, -3], ![1, -1, 1, -1]]

def raw4998step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![1, -1, 1, -1], ![1, 1, 1, -3]]

def raw4999 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -2, 3], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw5000 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -2, 3], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw5000step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw5001 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -2, 3], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw5001step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def raw5002 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -2, 3], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def raw5002step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![1, -2, -1, 2], ![0, 3, 1, -4]]

def raw5002step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, 3, -4], ![1, -1, -2, 2], ![1, -1, -1, 1]]

def raw5003 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -2, 3], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw5003step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![1, -2, 0, 1], ![0, 3, 0, -3]]

def raw5003step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -2, 0, 1]]

def raw5004 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -2, 3], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def raw5004step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw5005 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, -1, -1, 2], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw5006 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, -1, -1, 2], ![2, 1, 1, -4]]

def raw5006step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -1, -1, 1], ![1, -1, -1, 1], ![0, 2, 2, -4]]

def raw5006step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 1, 1, -1], ![-1, 1, 1, -1], ![0, -2, -2, 4]]

def raw5006step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def raw5007 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw5008 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, 0, -2, 2], ![2, 0, 2, -4]]

def raw5008step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -2, 1, 0]]

def raw5009 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def raw5010 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw5010step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, -1, 0, 1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw5011 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 0, 2, -3]]

def raw5011step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw5012 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![1, -1, -2, 2], ![1, 1, 2, -4]]

def raw5012step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![1, -1, -2, 2], ![0, 2, 2, -4]]

def raw5012step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![-1, 1, 2, -2], ![0, -2, -2, 4]]

def raw5012step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def raw5013 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def raw5013step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![1, -1, -1, 1], ![0, 2, 1, -3]]

def raw5013step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![-1, 1, 1, -1], ![0, -2, -1, 3]]

def raw5013step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def raw5014 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw5014step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw5015 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, 0, 1], ![0, -1, -1, 2], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw5015step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, -1, 0, 1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw5016 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def raw5017 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw5017step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, -1, 0], ![0, 1, 0, -1], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![-1, 0, -1, 2]]

def raw5017step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw5018 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, 1, 0], ![1, -1, -3, 3], ![1, 1, 1, -3]]

def raw5018step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![1, 1, -3, 1], ![0, 0, 3, -3]]

def raw5018step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![-1, -1, 3, -1], ![0, 0, -3, 3]]

def raw5018step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw5019 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, 2, -1], ![1, -1, -3, 3], ![1, 1, 0, -2]]

def raw5019step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![1, 2, -3, 0], ![0, -1, 3, -2]]

def raw5019step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![-1, -2, 3, 0], ![0, 1, -3, 2]]

def raw5019step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 2, -3]]

def raw5020 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, -3, 3], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw5020step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![1, -3, 0, 2], ![0, 3, -1, -2]]

def raw5020step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![-1, 3, 0, -2], ![0, -3, 1, 2]]

def raw5020step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 2, 0, -2], ![1, 0, -3, 2]]

def raw5021 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, -2, 2], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def raw5021step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![1, -2, -1, 2], ![0, 2, 0, -2]]

def raw5021step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw5022 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, -2, 2], ![1, -2, 2, -1], ![1, 1, -1, -1]]

def raw5022step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![1, -2, 2, -1], ![0, 2, -1, -1]]

def raw5022step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def raw5023 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, -1, 1], ![0, -1, -1, 2], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def raw5023step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 1, 2, -4]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical157
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5024 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -2, -1, 2], ![1, 1, 2, -4]]

def raw5024step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def raw5025 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 0, 2, -3]]

def raw5025step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw5026 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, -1, 1], ![1, -2, -1, 2], ![1, 1, 1, -3]]

def raw5026step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![1, -1, -1, 1], ![0, 1, 2, -3]]

def raw5026step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 2, -1], ![-1, 1, 1, -1], ![0, -1, -2, 3]]

def raw5026step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def raw5027 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def raw5027step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, -1, 0], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![-1, 0, -1, 2]]

def raw5027step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 1, -1, -1]]

def raw5028 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, -2, 2]]

def raw5028step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, -1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -1, 1, 0], ![-2, 2, 2, -2]]

def raw5028step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw5029 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, -3, 3]]

def raw5029step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![2, -2, 3, -3]]

def raw5030 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -2, 2], ![1, -1, 1, -1]]

def raw5030step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, -1, 0], ![0, 0, -1, 1], ![0, -1, 1, 0], ![-1, 1, 2, -2], ![-1, 1, -1, 1]]

def raw5030step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw5031 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, -2, -3, 3]]

def raw5031step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![1, 1, 1, -3], ![0, -1, -2, 3]]

def raw5031step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 1, 1, -3]]

def raw5032 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, 1, -1], ![1, -2, -3, 4], ![1, 1, 1, -3]]

def raw5032step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![1, 1, -3, 1], ![0, -1, 4, -3]]

def raw5032step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 2, -1], ![-1, -1, 3, -1], ![0, 1, -4, 3]]

def raw5032step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, -1, 2], ![0, 2, -1, -1], ![1, 0, 3, -4]]

def raw5033 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, 1, -1], ![1, -1, -3, 3], ![1, 0, 1, -2]]

def raw5033step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![1, 1, -3, 1], ![0, -1, 3, -2]]

def raw5033step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 1, 1, -3]]

def raw5034 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, -2, 2], ![1, -1, 0, 0]]

def raw5034step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, -1, 0], ![0, 0, -2, 2], ![0, -1, 1, 0], ![-1, 1, 2, -2], ![-1, 1, 0, 0]]

def raw5034step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def raw5035 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, -2, 2]]

def raw5035step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![1, 2, -1, -2], ![0, -2, 0, 2]]

def raw5035step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![-1, -2, 1, 2], ![0, 2, 0, -2]]

def raw5035step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw5036 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, -3, 3]]

def raw5036step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![1, 2, 0, -3], ![0, -2, -1, 3]]

def raw5036step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, 0, 1, -2]]

def raw5037 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, 2, -2], ![1, -2, -3, 4], ![1, 1, 0, -2]]

def raw5037step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![1, 2, -3, 0], ![0, -2, 4, -2]]

def raw5037step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, 0, 1, -3]]

def raw5038 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, 2, -2], ![1, -1, -3, 3], ![1, 0, 0, -1]]

def raw5038step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![1, 2, -3, 0], ![0, -2, 3, -1]]

def raw5038step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw5039 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 1, -3, 2], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw5039step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![1, -3, 2, 0], ![0, 2, -1, -1]]

def raw5039step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw5040 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 1, -1, 0], ![1, -1, -2, 2], ![1, -1, 2, -2]]

def raw5040step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![1, -1, -2, 2], ![0, 0, 2, -2]]

def raw5040step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![-1, 1, 2, -2], ![0, 0, -2, 2]]

def raw5040step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, -1, -1], ![1, -1, 2, -2]]

def raw5041 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 1, 1, -2], ![2, -2, -2, 2]]

def raw5041step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 1, -2], ![1, 1, -2], ![0, -2, 2]]

def raw5041step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]

def raw5042 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 1, 2, -3], ![2, -2, -3, 3]]

def raw5042step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 1, -2], ![1, 2, -3], ![0, -3, 3]]

def raw5042step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 1, -2], ![1, 2, -3]]

def raw5043 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![1, -4, 2, 1], ![1, 3, -3, -1]]

def raw5043step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -4, 3], ![1, 2, -3], ![0, 1, -1]]

def raw5043step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -3, 2], ![1, 3, -4]]

def raw5044 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![1, -3, 1, 1], ![1, 2, -2, -1]]

def raw5044step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -3, 2], ![1, 1, -2], ![0, 1, -1]]

def raw5044step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

def raw5045 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![1, -2, -3, 4], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def raw5045step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, 0, 1], ![1, -3, 2, 0], ![0, 4, -2, -2]]

def raw5045step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, 0, 1, -3]]

def raw5046 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![1, -2, -3, 4], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw5046step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, 1, 0], ![1, -3, 1, 1], ![0, 4, -2, -2]]

def raw5046step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![1, 0, 1, -2], ![1, 1, 1, -3]]

def raw5047 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![1, -2, -3, 4], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def raw5047step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, 1, 0], ![1, -3, 2, 0], ![0, 4, -3, -1]]

def raw5047step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 1, -2], ![0, 1, 2, -3], ![1, -2, 0, 1]]

def raw5048 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![1, -2, -1, 2], ![0, 0, -2, 2], ![1, 1, 2, -4]]

def raw5048step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, 0, 1], ![1, -1, -2, 2], ![0, 2, 2, -4]]

def raw5048step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![-1, 2, 0, -1], ![-1, 1, 2, -2], ![0, -2, -2, 4]]

def raw5048step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, -1, 1, -2]]

def raw5049 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![1, -2, 3, -2], ![1, 1, -4, 2]]

def raw5049step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 3, -4], ![0, -2, 2]]

def raw5049step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -2, 1], ![1, 3, -4]]

def raw5050 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![1, -1, -3, 3], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw5050step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -1, 1, -1], ![1, -3, 1, 1], ![0, 3, -2, -1]]

def raw5050step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 1, 1, -3]]

def raw5051 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![1, -1, -2, 2], ![0, -1, -1, 2], ![1, 1, 2, -4]]

def raw5051step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -1, -1, 1], ![1, -2, -1, 2], ![0, 2, 2, -4]]

def raw5051step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![-1, 1, 1, -1], ![-1, 2, 1, -2], ![0, -2, -2, 4]]

def raw5051step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def raw5052 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![1, 1, 1, -3], ![1, -2, -2, 3]]

def raw5052step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, 1, -2], ![1, 1, -2], ![0, -3, 3]]

def raw5052step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]

def raw5053 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, -3, 2, 1], ![2, 2, -4, 0]]

def raw5053step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -3, 2], ![2, 2, -4], ![-1, 1, 0]]

def raw5053step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]

def raw5054 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, -2, 2, 0], ![2, 1, -4, 1]]

def raw5054step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -2, 1], ![2, 2, -4], ![-1, 0, 1]]

def raw5054step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![-2, -2, 4], ![1, 0, -1]]

def raw5054step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def raw5055 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, -1, -3, 4], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical158
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5056 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, -1, -3, 4], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw5057 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, -1, -3, 4], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def raw5057step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -1, 1, -1], ![2, -3, 1, 0], ![-1, 4, -2, -1]]

def raw5057step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 2, -3]]

def raw5058 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, -1, -3, 4], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw5058step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![2, -3, 0, 1], ![-1, 4, 0, -3]]

def raw5058step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![-2, 3, 0, -1], ![1, -4, 0, 3]]

def raw5058step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -2, 3], ![0, 3, 1, -4], ![1, -1, -1, 1]]

def raw5059 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, -1, -3, 4], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def raw5059step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![2, -3, 1, 0], ![-1, 4, -1, -2]]

def raw5059step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw5060 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, -1, -3, 4], ![1, 0, 1, -2], ![1, 0, 0, -1]]

def raw5060step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, 0, 0], ![2, -3, 1, 0], ![-1, 4, -2, -1]]

def raw5060step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, 2, -3], ![1, 1, -2, 0]]

def raw5061 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, -1, -2, 3], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw5061step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def raw5062 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, -1, -2, 3], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw5062step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![2, -2, 0, 0], ![-1, 3, 0, -2]]

def raw5062step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![-2, 2, 0, 0], ![1, -3, 0, 2]]

def raw5062step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -3, 1], ![1, -1, 1, -1]]

def raw5063 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, -1, -1, 2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw5063step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, -2, 1], ![0, 1, 1, -2], ![0, -1, 0, 1], ![-1, 1, 1, -1], ![-1, 0, 0, 1]]

def raw5063step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def raw5064 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, -1, 1, 0], ![1, -1, -3, 3], ![1, 1, 0, -2]]

def raw5064step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![2, 1, -3, 0], ![-1, 0, 3, -2]]

def raw5064step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![-2, -1, 3, 0], ![1, 0, -3, 2]]

def raw5064step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw5065 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, 0, 1, -1], ![1, -2, -3, 4], ![1, 1, 0, -2]]

def raw5065step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![2, 1, -3, 0], ![-1, -1, 4, -2]]

def raw5065step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 2, -3]]

def raw5066 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, 0, 1, -1], ![1, -1, -3, 3], ![1, 0, 0, -1]]

def raw5066step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![2, 1, -3, 0], ![-1, -1, 3, -1]]

def raw5066step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 2, -3]]

def raw5067 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, 1, -3, 2], ![2, -2, 1, -1]]

def raw5067step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 1, -2], ![2, -3, 1], ![-1, 2, -1]]

def raw5067step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

def raw5068 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, 2, -2, 0], ![2, -3, 0, 1]]

def raw5068step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 2, -3], ![2, -2, 0], ![-1, 0, 1]]

def raw5068step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![-1, -2, 3], ![-2, 2, 0], ![1, 0, -1]]

def raw5068step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def raw5069 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, 3, -3, 0], ![2, -4, 1, 1]]

def raw5069step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 3, -4], ![2, -3, 1], ![-1, 0, 1]]

def raw5069step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![-1, -3, 4], ![-2, 3, -1], ![1, 0, -1]]

def raw5069step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]

def raw5070 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, 3, -2, -1], ![2, -4, 0, 2]]

def raw5070step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 3, -4], ![2, -2, 0], ![-1, -1, 2]]

def raw5070step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![-1, -3, 4], ![-2, 2, 0], ![1, 1, -2]]

def raw5070step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

def raw5071 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![1, -3, 2, 0], ![1, 2, -4, 1]]

def raw5071step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -3, 2], ![2, 2, -4], ![-1, 0, 1]]

def raw5071step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]

def raw5072 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![1, -2, -3, 4], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw5072step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, 1, 0], ![2, -3, 1, 0], ![-1, 4, -2, -1]]

def raw5072step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, 1, -2], ![0, 1, 2, -3], ![1, 0, -2, 1]]

def raw5073 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![1, -2, 2, -1], ![1, 1, -4, 2]]

def raw5073step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![2, 2, -4], ![-1, -1, 2]]

def raw5073step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![-1, 2, -1], ![-2, -2, 4], ![1, 1, -2]]

def raw5073step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]

def raw5074 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![1, 1, -3, 1], ![1, -2, 1, 0]]

def raw5074step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, 1, -2], ![2, -3, 1], ![-1, 1, 0]]

def raw5074step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

def raw5075 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![1, 2, -2, -1], ![1, -3, 0, 2]]

def raw5075step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, 2, -3], ![2, -2, 0], ![-1, -1, 2]]

def raw5075step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

def raw5076 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -3, 4], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw5077 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -3, 4], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw5077step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![3, -3, 0, 0], ![-2, 4, 0, -2]]

def raw5077step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![-3, 3, 0, 0], ![2, -4, 0, 2]]

def raw5077step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 2, -4, 2], ![1, -1, 1, -1]]

def raw5078 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -3, 4], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw5078step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, 0, 0], ![3, -3, 0, 0], ![-2, 4, -1, -1]]

def raw5078step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 3, -3], ![1, 1, -2, 0]]

def raw5079 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -2, 3], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw5079step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw5080 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -2, 3], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw5081 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -2, 3], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw5081step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw5082 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -2, 3], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def raw5083 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -2, 3], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw5083step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, 0, 0], ![3, -2, -1, 0], ![-2, 3, 0, -1]]

def raw5083step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 0, 0], ![-3, 2, 1, 0], ![2, -3, 0, 1]]

def raw5083step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -3, 2], ![1, 0, 2, -3]]

def raw5084 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -1, 2], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw5085 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -1, 2], ![0, 0, -2, 2], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw5085step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, 3, -2]]

def raw5086 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -1, 2], ![0, 0, -2, 2], ![2, 0, 0, -2]]

def raw5086step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -2, 3, -2]]

def raw5087 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -1, 2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw5087step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical159
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5088 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw5088step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw5089 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -1, 2], ![0, 1, 0, -1], ![1, -1, -2, 2], ![1, 0, 0, -1]]

def raw5090 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -1, 2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw5090step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw5091 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -1, 2], ![1, -1, -2, 2], ![1, 1, 0, -2]]

def raw5092 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -1, 2], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def raw5092step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, 0, 0], ![3, -1, -2, 0], ![-2, 2, 1, -1]]

def raw5092step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 0, 0], ![-3, 1, 2, 0], ![2, -2, -1, 1]]

def raw5092step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -2, 2]]

def raw5093 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, 0, -3, 3], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw5093step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![3, -3, 0, 0], ![-2, 3, 0, -1]]

def raw5093step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 1, 0], ![-3, 3, 0, 0], ![2, -3, 0, 1]]

def raw5093step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -3, 2], ![1, 0, 0, -1]]

def raw5094 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -2, -1, 2], ![1, 0, 0, -1]]

def raw5094step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw5095 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, 0, -2, 2], ![1, -2, -1, 2], ![1, 1, 0, -2]]

def raw5095step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![3, -2, -1, 0], ![-2, 2, 2, -2]]

def raw5095step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -2, 2, -2]]

def raw5096 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, 0, -2, 2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw5096step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![3, -2, -1, 0], ![-2, 2, 1, -1]]

def raw5096step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 1, 0], ![-3, 2, 1, 0], ![2, -2, -1, 1]]

def raw5096step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, -1, -2, 2]]

def raw5097 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, 0, -1, 1], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw5097step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -2, 3, -2]]

def raw5098 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, 0, -1, 1], ![1, -1, -2, 2], ![1, 0, 0, -1]]

def raw5098step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![3, -1, -2, 0], ![-2, 1, 2, -1]]

def raw5098step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -1, 2, -2]]

def raw5099 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, 1, 0, -1], ![1, -2, -3, 4], ![1, 0, 0, -1]]

def raw5099step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![3, 0, -3, 0], ![-2, -1, 4, -1]]

def raw5099step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, 1, -2]]

def raw5100 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![1, -2, -1, 2], ![0, 0, -2, 2], ![1, 1, 0, -2]]

def raw5100step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, 0, 1], ![3, -1, -2, 0], ![-2, 2, 2, -2]]

def raw5100step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -2, 2, -2]]

def raw5101 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-3, 3], ![1, -1], ![2, -2], ![2, -2]]

def raw5101step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![2, -2], ![2, -2]]

def raw5102 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]

def raw5103 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![-1, 1], ![2, -2], ![1, -1], ![2, -2]]

def raw5103step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]

def raw5104 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![0, 0], ![0, 0], ![2, -2], ![2, -2]]

def raw5104step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![0, 0], ![2, -2], ![2, -2]]

def raw5104step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![2, -2]]

def raw5105 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![0, 0], ![1, -1], ![1, -1], ![2, -2]]

def raw5105step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]

def raw5106 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![0, 0], ![2, -2], ![2, -2]]

def raw5106step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![2, -2]]

def raw5107 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![0, 0], ![1, -1], ![2, -2]]

def raw5107step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]

def raw5108 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![0, 0], ![2, -2]]

def raw5108step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]

def raw5109 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]

def raw5110 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]

def raw5111 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![2, -2], ![1, -1]]

def raw5111step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]

def raw5112 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![3, -3]]

def raw5112step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]

def raw5113 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![0, 0], ![1, -1], ![1, -1]]

def raw5113step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![1, -1], ![1, -1]]

def raw5113step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]

def raw5114 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![0, 0], ![2, -2]]

def raw5114step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![2, -2]]

def raw5115 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![1, -1], ![1, -1]]

def raw5115step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]

def raw5116 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![2, -2]]

def raw5117 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![4, -4]]

def raw5117step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]

def raw5118 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![3, -3]]

def raw5118step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]

def raw5119 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![0, 0], ![2, -2], ![2, -2]]

def raw5119step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![2, -2], ![2, -2]]

def raw5119step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]

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

def raw512 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]

def raw512step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 0, 0], ![-1, -2, 3], ![-2, 2, 0]]

def raw512step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, -2, 3], ![-2, 2, 0]]

def raw512step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![2, -2, 0]]

def raw513 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]

def raw513step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]

def raw513step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 0, -1], ![1, 2, -3]]

def raw514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]

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

def raw5120 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]

def raw5122 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![2, -2], ![2, -2]]

def raw5122step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]

def raw5123 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![0, 0], ![1, -1], ![2, -2]]

def raw5123step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![1, -1], ![2, -2]]

def raw5123step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw5124 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![0, 0], ![2, -2], ![1, -1]]

def raw5124step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![2, -2], ![1, -1]]

def raw5124step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]

def raw5124step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw5125 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![0, 0], ![3, -3]]

def raw5125step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![3, -3]]

def raw5125step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]

def raw5125step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw5126 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![1, -1], ![0, 0], ![2, -2]]

def raw5126step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![1, -1], ![2, -2]]

def raw5126step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw5127 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![1, -1], ![1, -1], ![1, -1]]

def raw5127step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw5128 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![1, -1], ![2, -2]]

def raw5128step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw5129 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![1, -1], ![2, -2], ![0, 0]]

def raw5129step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![1, -1], ![2, -2]]

def raw5129step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw5130 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![2, -2], ![0, 0], ![1, -1]]

def raw5130step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![2, -2], ![1, -1]]

def raw5130step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]

def raw5130step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw5131 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![2, -2], ![1, -1]]

def raw5131step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]

def raw5131step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw5132 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![3, -3]]

def raw5132step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]

def raw5132step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw5133 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![3, -3], ![0, 0]]

def raw5133step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![3, -3]]

def raw5133step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]

def raw5133step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw5134 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![0, 0], ![0, 0], ![2, -2]]

def raw5134step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![0, 0], ![2, -2]]

def raw5134step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw5135 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![0, 0], ![1, -1], ![1, -1]]

def raw5135step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw5136 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![0, 0], ![2, -2]]

def raw5136step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw5137 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![0, 0], ![2, -2], ![0, 0]]

def raw5137step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![0, 0], ![2, -2]]

def raw5137step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw5138 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![0, 0], ![1, -1]]

def raw5138step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw5139 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw5140 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![0, 0]]

def raw5140step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw5141 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw5142 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2], ![0, 0]]

def raw5142step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw5143 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2], ![0, 0], ![0, 0]]

def raw5143step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2], ![0, 0]]

def raw5143step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

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

def raw5487 : Matrix (Fin 2) (Fin 3) ℤ := ![![-1, -4, 5], ![1, 4, -5]]

def raw5487step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-4, 4], ![5, -5]]

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

end MUB6.Certificate.PairSemantics

end OAI
end


