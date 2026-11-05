-- Prove2me | Definitions.Def_OAIQ106E146
-- name    : OAIQ106E146
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T18:30:58.985292+00:00
-- url     : https://prove2.me/theorems/2087609c-5c20-49d6-9780-f6ba054c3a24
-- title:
--   Definitions bundle OAIQ106E146 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 5383 declarations of OpenAI's Lean: 5383 definitions. The definitions and types are `OAI.MUB6.Certificate.PairSemantics.raw7844step2`, `OAI.MUB6.Certificate.PairSemantics.raw7845`, `OAI.MUB6.Certificate.PairSemantics.raw7846`, `OAI.MUB6.Certificate.PairSemantics.raw7847`, `OAI.MUB6.Certificate.PairSemantics.raw7848step0`, `OAI.MUB6.Certificate.PairSemantics.raw7848step1`, `OAI.MUB6.Certificate.PairSemantics.raw7849`, `OAI.MUB6.Certificate.PairSemantics.raw7849step0`, `OAI.MUB6.Certificate.PairSemantics.raw784step0`, `OAI.MUB6.Certificate.PairSemantics.raw784step1`, `OAI.MUB6.Certificate.PairSemantics.raw785`, `OAI.MUB6.Certificate.PairSemantics.raw7850`, `OAI.MUB6.Certificate.PairSemantics.raw7851`, `OAI.MUB6.Certificate.PairSemantics.raw7852`, `OAI.MUB6.Certificate.PairSemantics.raw7853`, `OAI.MUB6.Certificate.PairSemantics.raw7854`, `OAI.MUB6.Certificate.PairSemantics.raw7854step0`, `OAI.MUB6.Certificate.PairSemantics.raw7854step1`, `OAI.MUB6.Certificate.PairSemantics.raw7855`, `OAI.MUB6.Certificate.PairSemantics.raw7856`, `OAI.MUB6.Certificate.PairSemantics.raw7856step0`, `OAI.MUB6.Certificate.PairSemantics.raw7856step1`, `OAI.MUB6.Certificate.PairSemantics.raw7857`, `OAI.MUB6.Certificate.PairSemantics.raw7857step0`, `OAI.MUB6.Certificate.PairSemantics.raw7857step1`, `OAI.MUB6.Certificate.PairSemantics.raw7858`, `OAI.MUB6.Certificate.PairSemantics.raw7858step0`, `OAI.MUB6.Certificate.PairSemantics.raw7858step1`, `OAI.MUB6.Certificate.PairSemantics.raw7859`, `OAI.MUB6.Certificate.PairSemantics.raw7859step0`, `OAI.MUB6.Certificate.PairSemantics.raw7859step1`, `OAI.MUB6.Certificate.PairSemantics.raw7859step2`, `OAI.MUB6.Certificate.PairSemantics.raw785step0`, `OAI.MUB6.Certificate.PairSemantics.raw786`, `OAI.MUB6.Certificate.PairSemantics.raw7860`, `OAI.MUB6.Certificate.PairSemantics.raw7860step0`, `OAI.MUB6.Certificate.PairSemantics.raw7860step1`, `OAI.MUB6.Certificate.PairSemantics.raw7860step2`, `OAI.MUB6.Certificate.PairSemantics.raw7861`, `OAI.MUB6.Certificate.PairSemantics.raw7861step0` and 5343 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_PairSemantics_Canonical0`, `MutuallyUnbiased_PairSemantics_Canonical2`, `MutuallyUnbiased_PairSemantics_Canonical24`, `MutuallyUnbiased_PairSemantics_Canonical245`, `MutuallyUnbiased_PairSemantics_Canonical246`, `MutuallyUnbiased_PairSemantics_Canonical247`, `MutuallyUnbiased_PairSemantics_Canonical248`, `MutuallyUnbiased_PairSemantics_Canonical249`, `MutuallyUnbiased_PairSemantics_Canonical25`, `MutuallyUnbiased_PairSemantics_Canonical250`, `MutuallyUnbiased_PairSemantics_Canonical251`, `MutuallyUnbiased_PairSemantics_Canonical252`, `MutuallyUnbiased_PairSemantics_Canonical253`, `MutuallyUnbiased_PairSemantics_Canonical254`, `MutuallyUnbiased_PairSemantics_Canonical255`, `MutuallyUnbiased_PairSemantics_Canonical256`, `MutuallyUnbiased_PairSemantics_Canonical257`, `MutuallyUnbiased_PairSemantics_Canonical258`, `MutuallyUnbiased_PairSemantics_Canonical259`, `MutuallyUnbiased_PairSemantics_Canonical26`, `MutuallyUnbiased_PairSemantics_Canonical260`, `MutuallyUnbiased_PairSemantics_Canonical261`, `MutuallyUnbiased_PairSemantics_Canonical262`, `MutuallyUnbiased_PairSemantics_Canonical263`, `MutuallyUnbiased_PairSemantics_Canonical264`, `MutuallyUnbiased_PairSemantics_Canonical265`, `MutuallyUnbiased_PairSemantics_Canonical266`, `MutuallyUnbiased_PairSemantics_Canonical267`, `MutuallyUnbiased_PairSemantics_Canonical268`, `MutuallyUnbiased_PairSemantics_Canonical269`, `MutuallyUnbiased_PairSemantics_Canonical27`, `MutuallyUnbiased_PairSemantics_Canonical270`, `MutuallyUnbiased_PairSemantics_Canonical271`, `MutuallyUnbiased_PairSemantics_Canonical272`, `MutuallyUnbiased_PairSemantics_Canonical273`, `MutuallyUnbiased_PairSemantics_Canonical274`, `MutuallyUnbiased_PairSemantics_Canonical275`, `MutuallyUnbiased_PairSemantics_Canonical276`, `MutuallyUnbiased_PairSemantics_Canonical277`, `MutuallyUnbiased_PairSemantics_Canonical278`, `MutuallyUnbiased_PairSemantics_Canonical279`, `MutuallyUnbiased_PairSemantics_Canonical28`, `MutuallyUnbiased_PairSemantics_Canonical280`, `MutuallyUnbiased_PairSemantics_Canonical281`, `MutuallyUnbiased_PairSemantics_Canonical282`, `MutuallyUnbiased_PairSemantics_Canonical283`, `MutuallyUnbiased_PairSemantics_Canonical284`, `MutuallyUnbiased_PairSemantics_Canonical285`, `MutuallyUnbiased_PairSemantics_Canonical286`, `MutuallyUnbiased_PairSemantics_Canonical287`, `MutuallyUnbiased_PairSemantics_Canonical288`, `MutuallyUnbiased_PairSemantics_Canonical289`, `MutuallyUnbiased_PairSemantics_Canonical29`, `MutuallyUnbiased_PairSemantics_Canonical290`, `MutuallyUnbiased_PairSemantics_Canonical291`, `MutuallyUnbiased_PairSemantics_Canonical292`, `MutuallyUnbiased_PairSemantics_Canonical293`, `MutuallyUnbiased_PairSemantics_Canonical294`, `MutuallyUnbiased_PairSemantics_Canonical295`, `MutuallyUnbiased_PairSemantics_Canonical296`, `MutuallyUnbiased_PairSemantics_Canonical297`, `MutuallyUnbiased_PairSemantics_Canonical298`, `MutuallyUnbiased_PairSemantics_Canonical299`, `MutuallyUnbiased_PairSemantics_Canonical3`, `MutuallyUnbiased_PairSemantics_Canonical30`, `MutuallyUnbiased_PairSemantics_Canonical300`, `MutuallyUnbiased_PairSemantics_Canonical301`, `MutuallyUnbiased_PairSemantics_Canonical302`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1162_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1163_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1164_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1165_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1170_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1172_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1265_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1266_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1267_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1298_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1299_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1339_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1340_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1341_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1342_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1343_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1395_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1396_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1397_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1399_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1409_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1410_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1411_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1412_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1414_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1441_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1475_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1477_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1478_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2357_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2358_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2526_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2527_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2528_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2530_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2531_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2570_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2572_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2574_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2576_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2593_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2594_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2595_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2599_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2636_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2766_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2828_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2901_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2903_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2904_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2936_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2937_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2939_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2941_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2943_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2957_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2958_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2959_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2960_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2961_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2963_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2986_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2987_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2988_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2990_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2996_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2998_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3003_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3081_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3082_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3087_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3088_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3089_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3094_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3100_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3106_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3109_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3139_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3140_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3184_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3185_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3190_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3191_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3203_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3204_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3205_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3206_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3209_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3210_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3211_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3223_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3226_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3227_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3711_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3727_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3735_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3737_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3739_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3818_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3821_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3823_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3829_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3830_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3847_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3851_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3852_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3853_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3882_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3925_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3936_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3937_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3938_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3965_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3966_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3967_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3969_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3970_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3977_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3980_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3981_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3982_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3984_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3990_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3992_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3994_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3995_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3998_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4003_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4023_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4026_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4031_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4032_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4033_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4053_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5174_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5387_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5415_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5418_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5439_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5450_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5452_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5464_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5465_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5490_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5492_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound0_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound111_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound12_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound135_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound136_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound137_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound138_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound139_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound140_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound141_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound142_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound143_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound144_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound145_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound146_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound147_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound148_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound149_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound150_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound151_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound16_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound19_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound1_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound20_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound21_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound23_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound28_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound29_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound2_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound30_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound32_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound35_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound36_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound37_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound3_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound41_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound49_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound5_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound61_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound62_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound6_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound78_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound7_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound9_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1472_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero14_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero15_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1674_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1785_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero18_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1909_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero488_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero621_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero794_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero818_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound0_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1007_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1008_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound100_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1010_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1013_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1020_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1021_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1033_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1093_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1094_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1095_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1096_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1097_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1098_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound10_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1103_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1108_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound110_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1110_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1111_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1115_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound111_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1120_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1121_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1124_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1130_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1131_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound113_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound114_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1159_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound115_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1165_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1166_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1167_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound116_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1170_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1177_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1178_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1179_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1194_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound125_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1261_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1262_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1264_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1266_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1267_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1268_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1269_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound126_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1272_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1278_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1279_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound127_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1294_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound12_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1300_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1301_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1303_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1309_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound130_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1310_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1311_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1312_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1318_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1324_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound137_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound138_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound139_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound13_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1409_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound140_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1410_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1411_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1412_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1413_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1414_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1418_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1419_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound141_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1420_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1421_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1423_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1429_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1433_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1434_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1435_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1437_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound143_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1441_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1442_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound144_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1469_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1470_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1477_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1478_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1479_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1480_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1484_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1492_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1493_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1507_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1510_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1511_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1517_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound151_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1521_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound153_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1559_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1560_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1562_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1567_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1568_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1572_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound163_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1648_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1649_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1650_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1651_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1652_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1653_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1654_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1655_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1656_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1662_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1669_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1672_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1686_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound16_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1703_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1708_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1709_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1715_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1717_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1780_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1781_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1782_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1783_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1784_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1786_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1787_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1788_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1789_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1796_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound17_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1816_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1840_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1844_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1845_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1846_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1847_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1849_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1853_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1854_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1855_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1856_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1859_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1866_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1872_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1874_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound188_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1904_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1905_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1907_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1911_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1914_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1915_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1916_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1917_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1925_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1944_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1963_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1964_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1968_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1969_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1972_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1977_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1985_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound199_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound19_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2033_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2034_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2035_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2036_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2037_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2038_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2040_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2046_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2048_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2049_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2050_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2059_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2062_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2075_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2077_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound207_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound213_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound214_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2166_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2168_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2169_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2170_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2171_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2172_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2173_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2174_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2175_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2176_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2177_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2178_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2179_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2180_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2181_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2182_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2183_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2184_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2185_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2187_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2188_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2189_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2191_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2192_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2193_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2195_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2196_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2197_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2199_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound21_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2200_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2201_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2202_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2203_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2204_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2205_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2206_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2207_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2208_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2211_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2212_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2214_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2215_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2216_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2217_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2218_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2219_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2220_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2223_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2224_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2225_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2226_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2227_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2228_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2229_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2230_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2231_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2232_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2233_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2235_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2236_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2238_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2240_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2241_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2242_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2244_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2245_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2246_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2247_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2248_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2249_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2250_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2251_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2252_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2253_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2254_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2255_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2256_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2257_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2258_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2259_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2260_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2261_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2262_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2263_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2264_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2265_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2266_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2267_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2268_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound226_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2270_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2271_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2272_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2273_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2274_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2275_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2276_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2277_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2278_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2279_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2281_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2282_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2283_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2284_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2285_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2286_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2287_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2288_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2289_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2290_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2291_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2292_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2293_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2294_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2295_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2296_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2297_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2298_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2299_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound22_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2300_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2301_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2302_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2304_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2305_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2306_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2307_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2308_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2309_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2310_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2311_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2312_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2313_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2314_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2315_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2316_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2317_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2318_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2321_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2322_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2323_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2324_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2325_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2326_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2327_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2328_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2329_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2330_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2331_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2332_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2333_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2334_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2335_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2336_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2337_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2338_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2340_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2341_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2342_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2344_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2345_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2346_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2347_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2348_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2350_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2352_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2353_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2354_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2355_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2356_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2357_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2358_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2361_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2362_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2363_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2364_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2365_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2366_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2367_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2368_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2369_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound236_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2371_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2373_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2374_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2375_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2376_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2377_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2378_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2379_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2380_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2381_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2382_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2383_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2384_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2385_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2386_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2387_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2388_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2390_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2391_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2392_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2393_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2394_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2395_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2396_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2397_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2398_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2399_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound23_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2400_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2401_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2402_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2404_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2405_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2406_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2407_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2408_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2409_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2410_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2411_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2412_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2413_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2414_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2415_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2416_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2418_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2419_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2421_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2422_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2423_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2424_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound244_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound245_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound24_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound255_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound267_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound269_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound281_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound282_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound286_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound287_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound28_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound296_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound301_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound310_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound311_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound319_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound327_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound335_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound339_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound340_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound341_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound342_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound343_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound344_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound345_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound353_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound354_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound355_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound356_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound357_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound358_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound359_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound365_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound366_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound367_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound368_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound369_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound370_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound371_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound380_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound388_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound391_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound392_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound395_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound396_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound3_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound404_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound411_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound412_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound413_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound418_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound419_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound427_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound428_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound438_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound444_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound445_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound447_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound448_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound452_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound453_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound454_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound456_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound462_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound463_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound470_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound473_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound474_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound481_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound482_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound483_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound484_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound485_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound497_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound498_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound499_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound4_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound500_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound501_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound504_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound513_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound514_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound515_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound516_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound518_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound519_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound521_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound523_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound524_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound525_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound526_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound531_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound532_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound533_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound534_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound537_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound538_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound539_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound540_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound541_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound542_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound543_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound545_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound546_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound547_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound548_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound551_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound552_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound553_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound554_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound555_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound558_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound564_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound565_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound566_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound567_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound568_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound570_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound571_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound579_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound580_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound581_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound582_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound584_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound585_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound587_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound588_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound589_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound58_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound599_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound5_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound600_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound613_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound614_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound628_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound629_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound630_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound631_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound633_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound635_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound636_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound643_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound644_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound649_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound656_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound657_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound658_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound659_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound663_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound664_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound666_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound667_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound668_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound675_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound683_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound688_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound694_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound6_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound700_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound707_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound711_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound712_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound717_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound718_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound719_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound720_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound722_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound727_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound730_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound731_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound732_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound733_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound734_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound735_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound736_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound737_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound740_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound741_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound742_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound743_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound750_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound751_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound758_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound759_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound769_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound76_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound779_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound780_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound786_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound787_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound788_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound789_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound790_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound792_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound793_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound796_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound797_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound798_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound799_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound7_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound800_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound801_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound802_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound804_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound805_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound813_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound815_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound817_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound822_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound823_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound834_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound841_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound842_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound844_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound847_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound852_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound853_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound857_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound858_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound859_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound863_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound864_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound865_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound866_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound867_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound868_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound872_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound873_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound877_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound878_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound881_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound883_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound884_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound885_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound887_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound888_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound891_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound894_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound897_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound898_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound899_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound902_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound906_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound909_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound911_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound912_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound913_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound917_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound919_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound91_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound922_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound923_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound925_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound926_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound927_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound928_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound929_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound92_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound932_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound933_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound935_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound936_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound937_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound938_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound939_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound940_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound941_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound942_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound947_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound949_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound94_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound950_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound954_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound956_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound959_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound962_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound963_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound964_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound966_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound967_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound968_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound971_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound973_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound975_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound976_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound977_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound97_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound981_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound983_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound987_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound991_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound992_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound99_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound9_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval100_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval105_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1075_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval108_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval111_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval113_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval117_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval118_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1194_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1225_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval122_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval126_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval12_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1315_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval131_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval136_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval137_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval141_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval143_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1465_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval151_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1523_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval152_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1554_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1555_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval155_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval164_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval165_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval169_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval174_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval175_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval181_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval185_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval18_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval190_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval201_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval202_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval211_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval212_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval217_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval21_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval220_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval224_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval226_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval229_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval232_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval234_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval235_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval242_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval246_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval250_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval256_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval260_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval264_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval266_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval268_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval269_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval275_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval280_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval285_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval286_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval287_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval289_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval296_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval301_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval308_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval310_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval316_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval325_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval332_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval335_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval338_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval339_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval341_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval343_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval351_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval352_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval356_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval357_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval358_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval359_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval366_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval369_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval372_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval378_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval37_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval382_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval383_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval385_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval390_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval398_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval39_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval405_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval408_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval413_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval46_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval474_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval476_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval53_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval55_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval56_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval63_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval69_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval73_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval74_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval79_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval84_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval86_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval8_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval92_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval957_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval145_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval147_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval150_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval215_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval216_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval219_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval21_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval220_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval223_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval238_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval373_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval375_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval44_e`, `OAI.MUB6.Certificate.PairSemantics.boundarySound26_e`, `OAI.MUB6.Certificate.PairSemantics.boundarySound49_e`, `OAI.MUB6.Certificate.PairSemantics.boundarySound58_e`, `OAI.MUB6.Certificate.PairSemantics.boundarySound73_e`, `OAI.MUB6.Certificate.PairSemantics.sound1379_e`, `OAI.MUB6.Certificate.PairSemantics.sound1381_e`, `OAI.MUB6.Certificate.PairSemantics.sound1383_e`, `OAI.MUB6.Certificate.PairSemantics.sound1384_e`, `OAI.MUB6.Certificate.PairSemantics.sound1387_e`, `OAI.MUB6.Certificate.PairSemantics.sound1390_e`, `OAI.MUB6.Certificate.PairSemantics.sound1391_e`, `OAI.MUB6.Certificate.PairSemantics.sound1395_e`, `OAI.MUB6.Certificate.PairSemantics.sound1399_e`, `OAI.MUB6.Certificate.PairSemantics.sound1414_e`, `OAI.MUB6.Certificate.PairSemantics.sound1419_e`, `OAI.MUB6.Certificate.PairSemantics.sound1423_e`, `OAI.MUB6.Certificate.PairSemantics.sound1424_e`, `OAI.MUB6.Certificate.PairSemantics.sound1425_e`, `OAI.MUB6.Certificate.PairSemantics.sound1434_e`, `OAI.MUB6.Certificate.PairSemantics.sound1437_e`, `OAI.MUB6.Certificate.PairSemantics.sound1443_e`, `OAI.MUB6.Certificate.PairSemantics.sound1458_e`, `OAI.MUB6.Certificate.PairSemantics.sound1486_e`, `OAI.MUB6.Certificate.PairSemantics.sound1504_e`, `OAI.MUB6.Certificate.PairSemantics.sound1506_e`, `OAI.MUB6.Certificate.PairSemantics.sound1512_e`, `OAI.MUB6.Certificate.PairSemantics.sound1518_e`, `OAI.MUB6.Certificate.PairSemantics.sound1529_e`, `OAI.MUB6.Certificate.PairSemantics.sound1530_e`, `OAI.MUB6.Certificate.PairSemantics.sound1531_e`, `OAI.MUB6.Certificate.PairSemantics.sound1535_e`, `OAI.MUB6.Certificate.PairSemantics.sound1540_e`, `OAI.MUB6.Certificate.PairSemantics.sound1548_e`, `OAI.MUB6.Certificate.PairSemantics.sound1605_e`, `OAI.MUB6.Certificate.PairSemantics.sound1614_e`, `OAI.MUB6.Certificate.PairSemantics.sound1617_e`, `OAI.MUB6.Certificate.PairSemantics.sound1624_e`, `OAI.MUB6.Certificate.PairSemantics.sound1627_e`, `OAI.MUB6.Certificate.PairSemantics.sound1628_e`, `OAI.MUB6.Certificate.PairSemantics.sound1631_e`, `OAI.MUB6.Certificate.PairSemantics.sound1634_e`, `OAI.MUB6.Certificate.PairSemantics.sound1635_e`, `OAI.MUB6.Certificate.PairSemantics.sound1637_e`, `OAI.MUB6.Certificate.PairSemantics.sound1644_e`, `OAI.MUB6.Certificate.PairSemantics.sound1646_e`, `OAI.MUB6.Certificate.PairSemantics.sound1648_e`, `OAI.MUB6.Certificate.PairSemantics.sound1685_e`, `OAI.MUB6.Certificate.PairSemantics.sound1716_e`, `OAI.MUB6.Certificate.PairSemantics.sound1736_e`, `OAI.MUB6.Certificate.PairSemantics.sound1739_e`, `OAI.MUB6.Certificate.PairSemantics.sound1768_e`, `OAI.MUB6.Certificate.PairSemantics.sound1770_e`, `OAI.MUB6.Certificate.PairSemantics.sound1793_e`, `OAI.MUB6.Certificate.PairSemantics.sound1800_e`, `OAI.MUB6.Certificate.PairSemantics.sound1828_e`, `OAI.MUB6.Certificate.PairSemantics.sound1849_e`, `OAI.MUB6.Certificate.PairSemantics.sound1858_e`, `OAI.MUB6.Certificate.PairSemantics.sound1860_e`, `OAI.MUB6.Certificate.PairSemantics.sound1865_e`, `OAI.MUB6.Certificate.PairSemantics.sound1866_e`, `OAI.MUB6.Certificate.PairSemantics.sound1867_e`, `OAI.MUB6.Certificate.PairSemantics.sound1869_e`, `OAI.MUB6.Certificate.PairSemantics.sound1870_e`, `OAI.MUB6.Certificate.PairSemantics.sound1872_e`, `OAI.MUB6.Certificate.PairSemantics.sound1875_e`, `OAI.MUB6.Certificate.PairSemantics.sound1876_e`, `OAI.MUB6.Certificate.PairSemantics.sound1879_e`, `OAI.MUB6.Certificate.PairSemantics.sound1885_e`, `OAI.MUB6.Certificate.PairSemantics.sound1978_e`, `OAI.MUB6.Certificate.PairSemantics.sound1980_e`, `OAI.MUB6.Certificate.PairSemantics.sound1986_e`, `OAI.MUB6.Certificate.PairSemantics.sound1987_e`, `OAI.MUB6.Certificate.PairSemantics.sound2041_e`, `OAI.MUB6.Certificate.PairSemantics.sound2058_e`, `OAI.MUB6.Certificate.PairSemantics.sound2071_e`, `OAI.MUB6.Certificate.PairSemantics.sound2097_e`, `OAI.MUB6.Certificate.PairSemantics.sound2106_e`, `OAI.MUB6.Certificate.PairSemantics.sound2107_e`, `OAI.MUB6.Certificate.PairSemantics.sound2108_e`, `OAI.MUB6.Certificate.PairSemantics.sound2117_e`, `OAI.MUB6.Certificate.PairSemantics.sound2122_e`, `OAI.MUB6.Certificate.PairSemantics.sound2123_e`, `OAI.MUB6.Certificate.PairSemantics.sound2128_e`, `OAI.MUB6.Certificate.PairSemantics.sound2132_e`, `OAI.MUB6.Certificate.PairSemantics.sound2152_e`, `OAI.MUB6.Certificate.PairSemantics.sound2168_e`, `OAI.MUB6.Certificate.PairSemantics.sound2175_e`, `OAI.MUB6.Certificate.PairSemantics.sound2177_e`, `OAI.MUB6.Certificate.PairSemantics.sound2189_e`, `OAI.MUB6.Certificate.PairSemantics.sound2190_e`, `OAI.MUB6.Certificate.PairSemantics.sound2197_e`, `OAI.MUB6.Certificate.PairSemantics.sound2201_e`, `OAI.MUB6.Certificate.PairSemantics.sound2202_e`, `OAI.MUB6.Certificate.PairSemantics.sound2213_e`, `OAI.MUB6.Certificate.PairSemantics.sound2228_e`, `OAI.MUB6.Certificate.PairSemantics.sound2244_e`, `OAI.MUB6.Certificate.PairSemantics.sound2262_e`, `OAI.MUB6.Certificate.PairSemantics.sound2284_e`, `OAI.MUB6.Certificate.PairSemantics.sound2286_e`, `OAI.MUB6.Certificate.PairSemantics.sound2293_e`, `OAI.MUB6.Certificate.PairSemantics.sound2294_e`, `OAI.MUB6.Certificate.PairSemantics.sound2295_e`, `OAI.MUB6.Certificate.PairSemantics.sound2296_e`, `OAI.MUB6.Certificate.PairSemantics.sound2312_e`, `OAI.MUB6.Certificate.PairSemantics.sound2324_e`, `OAI.MUB6.Certificate.PairSemantics.sound2327_e`, `OAI.MUB6.Certificate.PairSemantics.sound2338_e`, `OAI.MUB6.Certificate.PairSemantics.sound2375_e`, `OAI.MUB6.Certificate.PairSemantics.sound2382_e`, `OAI.MUB6.Certificate.PairSemantics.sound2390_e`, `OAI.MUB6.Certificate.PairSemantics.sound2391_e`, `OAI.MUB6.Certificate.PairSemantics.sound2394_e`, `OAI.MUB6.Certificate.PairSemantics.sound2399_e`, `OAI.MUB6.Certificate.PairSemantics.sound2400_e`, `OAI.MUB6.Certificate.PairSemantics.sound2401_e`, `OAI.MUB6.Certificate.PairSemantics.sound2403_e`, `OAI.MUB6.Certificate.PairSemantics.sound2415_e`, `OAI.MUB6.Certificate.PairSemantics.sound2416_e`, `OAI.MUB6.Certificate.PairSemantics.sound2420_e`, `OAI.MUB6.Certificate.PairSemantics.sound2433_e`, `OAI.MUB6.Certificate.PairSemantics.sound2434_e`, `OAI.MUB6.Certificate.PairSemantics.sound2435_e`, `OAI.MUB6.Certificate.PairSemantics.sound2436_e`, `OAI.MUB6.Certificate.PairSemantics.sound2442_e`, `OAI.MUB6.Certificate.PairSemantics.sound2444_e`, `OAI.MUB6.Certificate.PairSemantics.sound2445_e`, `OAI.MUB6.Certificate.PairSemantics.sound2454_e`, `OAI.MUB6.Certificate.PairSemantics.sound2456_e`, `OAI.MUB6.Certificate.PairSemantics.sound2457_e`, `OAI.MUB6.Certificate.PairSemantics.sound2463_e`, `OAI.MUB6.Certificate.PairSemantics.sound2464_e`, `OAI.MUB6.Certificate.PairSemantics.sound2465_e`, `OAI.MUB6.Certificate.PairSemantics.sound2472_e`, `OAI.MUB6.Certificate.PairSemantics.sound2473_e`, `OAI.MUB6.Certificate.PairSemantics.sound2477_e`, `OAI.MUB6.Certificate.PairSemantics.sound2479_e`, `OAI.MUB6.Certificate.PairSemantics.sound2489_e`, `OAI.MUB6.Certificate.PairSemantics.sound2490_e`, `OAI.MUB6.Certificate.PairSemantics.sound2491_e`, `OAI.MUB6.Certificate.PairSemantics.sound2492_e`, `OAI.MUB6.Certificate.PairSemantics.sound2507_e`, `OAI.MUB6.Certificate.PairSemantics.sound2520_e`, `OAI.MUB6.Certificate.PairSemantics.sound2521_e`, `OAI.MUB6.Certificate.PairSemantics.sound2522_e`, `OAI.MUB6.Certificate.PairSemantics.sound2524_e`, `OAI.MUB6.Certificate.PairSemantics.sound2525_e`, `OAI.MUB6.Certificate.PairSemantics.sound2527_e`, `OAI.MUB6.Certificate.PairSemantics.sound2533_e`, `OAI.MUB6.Certificate.PairSemantics.sound2540_e`, `OAI.MUB6.Certificate.PairSemantics.sound2546_e`, `OAI.MUB6.Certificate.PairSemantics.sound2547_e`, `OAI.MUB6.Certificate.PairSemantics.sound2548_e`, `OAI.MUB6.Certificate.PairSemantics.sound2557_e`, `OAI.MUB6.Certificate.PairSemantics.sound2558_e`, `OAI.MUB6.Certificate.PairSemantics.sound2559_e`, `OAI.MUB6.Certificate.PairSemantics.sound2564_e`, `OAI.MUB6.Certificate.PairSemantics.sound2565_e`, `OAI.MUB6.Certificate.PairSemantics.sound2566_e`, `OAI.MUB6.Certificate.PairSemantics.sound2573_e`, `OAI.MUB6.Certificate.PairSemantics.sound2578_e`, `OAI.MUB6.Certificate.PairSemantics.sound2580_e`, `OAI.MUB6.Certificate.PairSemantics.sound2593_e`, `OAI.MUB6.Certificate.PairSemantics.sound2602_e`, `OAI.MUB6.Certificate.PairSemantics.sound2604_e`, `OAI.MUB6.Certificate.PairSemantics.sound2606_e`, `OAI.MUB6.Certificate.PairSemantics.sound2619_e`, `OAI.MUB6.Certificate.PairSemantics.sound2620_e`, `OAI.MUB6.Certificate.PairSemantics.sound2623_e`, `OAI.MUB6.Certificate.PairSemantics.sound2627_e`, `OAI.MUB6.Certificate.PairSemantics.sound2641_e`, `OAI.MUB6.Certificate.PairSemantics.sound2657_e`, `OAI.MUB6.Certificate.PairSemantics.sound2658_e`, `OAI.MUB6.Certificate.PairSemantics.sound2661_e`, `OAI.MUB6.Certificate.PairSemantics.sound2666_e`, `OAI.MUB6.Certificate.PairSemantics.sound2669_e`, `OAI.MUB6.Certificate.PairSemantics.sound2670_e`, `OAI.MUB6.Certificate.PairSemantics.sound2671_e`, `OAI.MUB6.Certificate.PairSemantics.sound2686_e`, `OAI.MUB6.Certificate.PairSemantics.sound2690_e`, `OAI.MUB6.Certificate.PairSemantics.sound2693_e`, `OAI.MUB6.Certificate.PairSemantics.sound2698_e`, `OAI.MUB6.Certificate.PairSemantics.sound2708_e`, `OAI.MUB6.Certificate.PairSemantics.sound2710_e`, `OAI.MUB6.Certificate.PairSemantics.sound2714_e`, `OAI.MUB6.Certificate.PairSemantics.sound2729_e`, `OAI.MUB6.Certificate.PairSemantics.sound2732_e`, `OAI.MUB6.Certificate.PairSemantics.sound2733_e`, `OAI.MUB6.Certificate.PairSemantics.sound2735_e`, `OAI.MUB6.Certificate.PairSemantics.sound2754_e`, `OAI.MUB6.Certificate.PairSemantics.sound2757_e`, `OAI.MUB6.Certificate.PairSemantics.sound2788_e`, `OAI.MUB6.Certificate.PairSemantics.sound2790_e`, `OAI.MUB6.Certificate.PairSemantics.sound2793_e`, `OAI.MUB6.Certificate.PairSemantics.sound2807_e`, `OAI.MUB6.Certificate.PairSemantics.sound2817_e`, `OAI.MUB6.Certificate.PairSemantics.sound2829_e`, `OAI.MUB6.Certificate.PairSemantics.sound2836_e`, `OAI.MUB6.Certificate.PairSemantics.sound2845_e`, `OAI.MUB6.Certificate.PairSemantics.sound2853_e`, `OAI.MUB6.Certificate.PairSemantics.sound2854_e`, `OAI.MUB6.Certificate.PairSemantics.sound2858_e`, `OAI.MUB6.Certificate.PairSemantics.sound2863_e`, `OAI.MUB6.Certificate.PairSemantics.sound2864_e`, `OAI.MUB6.Certificate.PairSemantics.sound2865_e`, `OAI.MUB6.Certificate.PairSemantics.sound2866_e`, `OAI.MUB6.Certificate.PairSemantics.sound2867_e`, `OAI.MUB6.Certificate.PairSemantics.sound2868_e`, `OAI.MUB6.Certificate.PairSemantics.sound2872_e`, `OAI.MUB6.Certificate.PairSemantics.sound2873_e`, `OAI.MUB6.Certificate.PairSemantics.sound2874_e`, `OAI.MUB6.Certificate.PairSemantics.sound2875_e`, `OAI.MUB6.Certificate.PairSemantics.sound2878_e`, `OAI.MUB6.Certificate.PairSemantics.sound2879_e`, `OAI.MUB6.Certificate.PairSemantics.sound2880_e`, `OAI.MUB6.Certificate.PairSemantics.sound2882_e`, `OAI.MUB6.Certificate.PairSemantics.sound2883_e`, `OAI.MUB6.Certificate.PairSemantics.sound2884_e`, `OAI.MUB6.Certificate.PairSemantics.sound2887_e`, `OAI.MUB6.Certificate.PairSemantics.sound2888_e`, `OAI.MUB6.Certificate.PairSemantics.sound2889_e`, `OAI.MUB6.Certificate.PairSemantics.sound2890_e`, `OAI.MUB6.Certificate.PairSemantics.sound2891_e`, `OAI.MUB6.Certificate.PairSemantics.sound2892_e`, `OAI.MUB6.Certificate.PairSemantics.sound2894_e`, `OAI.MUB6.Certificate.PairSemantics.sound2895_e`, `OAI.MUB6.Certificate.PairSemantics.sound2896_e`, `OAI.MUB6.Certificate.PairSemantics.sound2897_e`, `OAI.MUB6.Certificate.PairSemantics.sound2898_e`, `OAI.MUB6.Certificate.PairSemantics.sound2899_e`, `OAI.MUB6.Certificate.PairSemantics.sound2900_e`, `OAI.MUB6.Certificate.PairSemantics.sound2901_e`, `OAI.MUB6.Certificate.PairSemantics.sound2902_e`, `OAI.MUB6.Certificate.PairSemantics.sound2904_e`, `OAI.MUB6.Certificate.PairSemantics.sound2905_e`, `OAI.MUB6.Certificate.PairSemantics.sound2906_e`, `OAI.MUB6.Certificate.PairSemantics.sound2908_e`, `OAI.MUB6.Certificate.PairSemantics.sound2909_e`, `OAI.MUB6.Certificate.PairSemantics.sound2910_e`, `OAI.MUB6.Certificate.PairSemantics.sound2912_e`, `OAI.MUB6.Certificate.PairSemantics.sound2913_e`, `OAI.MUB6.Certificate.PairSemantics.sound2914_e`, `OAI.MUB6.Certificate.PairSemantics.sound2915_e`, `OAI.MUB6.Certificate.PairSemantics.sound2916_e`, `OAI.MUB6.Certificate.PairSemantics.sound2917_e`, `OAI.MUB6.Certificate.PairSemantics.sound2919_e`, `OAI.MUB6.Certificate.PairSemantics.sound2920_e`, `OAI.MUB6.Certificate.PairSemantics.sound2922_e`, `OAI.MUB6.Certificate.PairSemantics.sound2924_e`, `OAI.MUB6.Certificate.PairSemantics.sound2925_e`, `OAI.MUB6.Certificate.PairSemantics.sound2926_e`, `OAI.MUB6.Certificate.PairSemantics.sound2927_e`, `OAI.MUB6.Certificate.PairSemantics.sound2928_e`, `OAI.MUB6.Certificate.PairSemantics.sound2929_e`, `OAI.MUB6.Certificate.PairSemantics.sound2931_e`, `OAI.MUB6.Certificate.PairSemantics.sound2933_e`, `OAI.MUB6.Certificate.PairSemantics.sound2935_e`, `OAI.MUB6.Certificate.PairSemantics.sound2936_e`, `OAI.MUB6.Certificate.PairSemantics.sound2939_e`, `OAI.MUB6.Certificate.PairSemantics.sound2940_e`, `OAI.MUB6.Certificate.PairSemantics.sound2941_e`, `OAI.MUB6.Certificate.PairSemantics.sound2942_e`, `OAI.MUB6.Certificate.PairSemantics.sound2943_e`, `OAI.MUB6.Certificate.PairSemantics.sound2944_e`, `OAI.MUB6.Certificate.PairSemantics.sound2946_e`, `OAI.MUB6.Certificate.PairSemantics.sound2949_e`, `OAI.MUB6.Certificate.PairSemantics.sound2950_e`, `OAI.MUB6.Certificate.PairSemantics.sound2951_e`, `OAI.MUB6.Certificate.PairSemantics.sound2952_e`, `OAI.MUB6.Certificate.PairSemantics.sound2953_e`, `OAI.MUB6.Certificate.PairSemantics.sound2954_e`, `OAI.MUB6.Certificate.PairSemantics.sound2956_e`, `OAI.MUB6.Certificate.PairSemantics.sound2957_e`, `OAI.MUB6.Certificate.PairSemantics.sound2959_e`, `OAI.MUB6.Certificate.PairSemantics.sound2960_e`, `OAI.MUB6.Certificate.PairSemantics.sound2961_e`, `OAI.MUB6.Certificate.PairSemantics.sound2962_e`, `OAI.MUB6.Certificate.PairSemantics.sound2963_e`, `OAI.MUB6.Certificate.PairSemantics.sound2964_e`, `OAI.MUB6.Certificate.PairSemantics.sound2965_e`, `OAI.MUB6.Certificate.PairSemantics.sound2966_e`, `OAI.MUB6.Certificate.PairSemantics.sound2967_e`, `OAI.MUB6.Certificate.PairSemantics.sound2968_e`, `OAI.MUB6.Certificate.PairSemantics.sound2969_e`, `OAI.MUB6.Certificate.PairSemantics.sound2970_e`, `OAI.MUB6.Certificate.PairSemantics.sound2972_e`, `OAI.MUB6.Certificate.PairSemantics.sound2973_e`, `OAI.MUB6.Certificate.PairSemantics.sound2974_e`, `OAI.MUB6.Certificate.PairSemantics.sound2975_e`, `OAI.MUB6.Certificate.PairSemantics.sound2976_e`, `OAI.MUB6.Certificate.PairSemantics.sound2977_e`, `OAI.MUB6.Certificate.PairSemantics.sound2979_e`, `OAI.MUB6.Certificate.PairSemantics.sound2980_e`, `OAI.MUB6.Certificate.PairSemantics.sound2984_e`, `OAI.MUB6.Certificate.PairSemantics.sound2985_e`, `OAI.MUB6.Certificate.PairSemantics.sound2986_e`, `OAI.MUB6.Certificate.PairSemantics.sound2987_e`, `OAI.MUB6.Certificate.PairSemantics.sound2989_e`, `OAI.MUB6.Certificate.PairSemantics.sound2990_e`, `OAI.MUB6.Certificate.PairSemantics.sound2991_e`, `OAI.MUB6.Certificate.PairSemantics.sound2992_e`, `OAI.MUB6.Certificate.PairSemantics.sound2994_e`, `OAI.MUB6.Certificate.PairSemantics.sound2996_e`, `OAI.MUB6.Certificate.PairSemantics.sound2997_e`, `OAI.MUB6.Certificate.PairSemantics.sound2998_e`, `OAI.MUB6.Certificate.PairSemantics.sound2999_e`, `OAI.MUB6.Certificate.PairSemantics.sound3000_e`, `OAI.MUB6.Certificate.PairSemantics.sound3001_e`, `OAI.MUB6.Certificate.PairSemantics.sound3002_e`, `OAI.MUB6.Certificate.PairSemantics.sound3004_e`, `OAI.MUB6.Certificate.PairSemantics.sound3006_e`, `OAI.MUB6.Certificate.PairSemantics.sound3007_e`, `OAI.MUB6.Certificate.PairSemantics.sound3009_e`, `OAI.MUB6.Certificate.PairSemantics.sound3011_e`, `OAI.MUB6.Certificate.PairSemantics.sound3012_e`, `OAI.MUB6.Certificate.PairSemantics.sound3013_e`, `OAI.MUB6.Certificate.PairSemantics.sound3014_e`, `OAI.MUB6.Certificate.PairSemantics.sound3015_e`, `OAI.MUB6.Certificate.PairSemantics.sound3016_e`, `OAI.MUB6.Certificate.PairSemantics.sound3017_e`, `OAI.MUB6.Certificate.PairSemantics.sound3018_e`, `OAI.MUB6.Certificate.PairSemantics.sound3019_e`, `OAI.MUB6.Certificate.PairSemantics.sound3020_e`, `OAI.MUB6.Certificate.PairSemantics.sound3021_e`, `OAI.MUB6.Certificate.PairSemantics.sound3022_e`, `OAI.MUB6.Certificate.PairSemantics.sound3023_e`, `OAI.MUB6.Certificate.PairSemantics.sound3024_e`, `OAI.MUB6.Certificate.PairSemantics.sound3025_e`, `OAI.MUB6.Certificate.PairSemantics.sound3026_e`, `OAI.MUB6.Certificate.PairSemantics.sound3027_e`, `OAI.MUB6.Certificate.PairSemantics.sound3028_e`, `OAI.MUB6.Certificate.PairSemantics.sound3029_e`, `OAI.MUB6.Certificate.PairSemantics.sound3030_e`, `OAI.MUB6.Certificate.PairSemantics.sound3032_e`, `OAI.MUB6.Certificate.PairSemantics.sound3034_e`, `OAI.MUB6.Certificate.PairSemantics.sound3035_e`, `OAI.MUB6.Certificate.PairSemantics.sound3036_e`, `OAI.MUB6.Certificate.PairSemantics.sound3037_e`, `OAI.MUB6.Certificate.PairSemantics.sound3038_e`, `OAI.MUB6.Certificate.PairSemantics.sound3039_e`, `OAI.MUB6.Certificate.PairSemantics.sound3040_e`, `OAI.MUB6.Certificate.PairSemantics.sound3041_e`, `OAI.MUB6.Certificate.PairSemantics.sound3042_e`, `OAI.MUB6.Certificate.PairSemantics.sound3045_e`, `OAI.MUB6.Certificate.PairSemantics.sound3049_e`, `OAI.MUB6.Certificate.PairSemantics.sound3050_e`, `OAI.MUB6.Certificate.PairSemantics.sound3051_e`, `OAI.MUB6.Certificate.PairSemantics.sound3052_e`, `OAI.MUB6.Certificate.PairSemantics.sound3053_e`, `OAI.MUB6.Certificate.PairSemantics.sound3054_e`, `OAI.MUB6.Certificate.PairSemantics.sound3055_e`, `OAI.MUB6.Certificate.PairSemantics.sound3057_e`, `OAI.MUB6.Certificate.PairSemantics.sound3059_e`, `OAI.MUB6.Certificate.PairSemantics.sound3060_e`, `OAI.MUB6.Certificate.PairSemantics.sound3061_e`, `OAI.MUB6.Certificate.PairSemantics.sound3062_e`, `OAI.MUB6.Certificate.PairSemantics.sound3063_e`, `OAI.MUB6.Certificate.PairSemantics.sound3065_e`, `OAI.MUB6.Certificate.PairSemantics.sound3066_e`, `OAI.MUB6.Certificate.PairSemantics.sound3067_e`, `OAI.MUB6.Certificate.PairSemantics.sound3068_e`, `OAI.MUB6.Certificate.PairSemantics.sound3069_e`, `OAI.MUB6.Certificate.PairSemantics.sound3071_e`, `OAI.MUB6.Certificate.PairSemantics.sound3072_e`, `OAI.MUB6.Certificate.PairSemantics.sound3073_e`, `OAI.MUB6.Certificate.PairSemantics.sound3074_e`, `OAI.MUB6.Certificate.PairSemantics.sound3075_e`, `OAI.MUB6.Certificate.PairSemantics.sound3076_e`, `OAI.MUB6.Certificate.PairSemantics.sound3077_e`, `OAI.MUB6.Certificate.PairSemantics.sound3078_e`, `OAI.MUB6.Certificate.PairSemantics.sound3079_e`, `OAI.MUB6.Certificate.PairSemantics.sound3081_e`, `OAI.MUB6.Certificate.PairSemantics.sound3082_e`, `OAI.MUB6.Certificate.PairSemantics.sound3084_e`, `OAI.MUB6.Certificate.PairSemantics.sound3085_e`, `OAI.MUB6.Certificate.PairSemantics.sound3086_e`, `OAI.MUB6.Certificate.PairSemantics.sound3087_e`, `OAI.MUB6.Certificate.PairSemantics.sound3088_e`, `OAI.MUB6.Certificate.PairSemantics.sound3090_e`, `OAI.MUB6.Certificate.PairSemantics.sound3091_e`, `OAI.MUB6.Certificate.PairSemantics.sound3092_e`, `OAI.MUB6.Certificate.PairSemantics.sound3093_e`, `OAI.MUB6.Certificate.PairSemantics.sound3094_e`, `OAI.MUB6.Certificate.PairSemantics.sound3095_e`, `OAI.MUB6.Certificate.PairSemantics.sound3096_e`, `OAI.MUB6.Certificate.PairSemantics.sound3098_e`, `OAI.MUB6.Certificate.PairSemantics.sound3099_e`, `OAI.MUB6.Certificate.PairSemantics.sound3100_e`, `OAI.MUB6.Certificate.PairSemantics.sound3101_e`, `OAI.MUB6.Certificate.PairSemantics.sound3105_e`, `OAI.MUB6.Certificate.PairSemantics.sound3106_e`, `OAI.MUB6.Certificate.PairSemantics.sound3107_e`, `OAI.MUB6.Certificate.PairSemantics.sound3108_e`, `OAI.MUB6.Certificate.PairSemantics.sound3110_e`, `OAI.MUB6.Certificate.PairSemantics.sound3111_e`, `OAI.MUB6.Certificate.PairSemantics.sound3112_e`, `OAI.MUB6.Certificate.PairSemantics.sound3113_e`, `OAI.MUB6.Certificate.PairSemantics.sound3114_e`, `OAI.MUB6.Certificate.PairSemantics.sound3115_e`, `OAI.MUB6.Certificate.PairSemantics.sound3118_e`, `OAI.MUB6.Certificate.PairSemantics.sound3119_e`, `OAI.MUB6.Certificate.PairSemantics.sound3120_e`, `OAI.MUB6.Certificate.PairSemantics.sound3122_e`, `OAI.MUB6.Certificate.PairSemantics.sound3123_e`, `OAI.MUB6.Certificate.PairSemantics.sound3124_e`, `OAI.MUB6.Certificate.PairSemantics.sound3125_e`, `OAI.MUB6.Certificate.PairSemantics.sound3127_e`, `OAI.MUB6.Certificate.PairSemantics.sound3128_e`, `OAI.MUB6.Certificate.PairSemantics.sound3129_e`, `OAI.MUB6.Certificate.PairSemantics.sound3130_e`, `OAI.MUB6.Certificate.PairSemantics.sound3131_e`, `OAI.MUB6.Certificate.PairSemantics.sound3132_e`, `OAI.MUB6.Certificate.PairSemantics.sound3133_e`, `OAI.MUB6.Certificate.PairSemantics.sound3135_e`, `OAI.MUB6.Certificate.PairSemantics.sound3136_e`, `OAI.MUB6.Certificate.PairSemantics.sound3137_e`, `OAI.MUB6.Certificate.PairSemantics.sound3138_e`, `OAI.MUB6.Certificate.PairSemantics.sound3139_e`, `OAI.MUB6.Certificate.PairSemantics.sound3140_e`, `OAI.MUB6.Certificate.PairSemantics.sound3141_e`, `OAI.MUB6.Certificate.PairSemantics.sound3142_e`, `OAI.MUB6.Certificate.PairSemantics.sound3144_e`, `OAI.MUB6.Certificate.PairSemantics.sound3145_e`, `OAI.MUB6.Certificate.PairSemantics.sound3146_e`, `OAI.MUB6.Certificate.PairSemantics.sound3149_e`, `OAI.MUB6.Certificate.PairSemantics.sound3150_e`, `OAI.MUB6.Certificate.PairSemantics.sound3151_e`, `OAI.MUB6.Certificate.PairSemantics.sound3152_e`, `OAI.MUB6.Certificate.PairSemantics.sound3153_e`, `OAI.MUB6.Certificate.PairSemantics.sound3154_e`, `OAI.MUB6.Certificate.PairSemantics.sound3158_e`, `OAI.MUB6.Certificate.PairSemantics.sound3159_e`, `OAI.MUB6.Certificate.PairSemantics.sound3160_e`, `OAI.MUB6.Certificate.PairSemantics.sound3161_e`, `OAI.MUB6.Certificate.PairSemantics.sound3163_e`, `OAI.MUB6.Certificate.PairSemantics.sound3164_e`, `OAI.MUB6.Certificate.PairSemantics.sound3166_e`, `OAI.MUB6.Certificate.PairSemantics.sound3167_e`, `OAI.MUB6.Certificate.PairSemantics.sound3169_e`, `OAI.MUB6.Certificate.PairSemantics.sound3170_e`, `OAI.MUB6.Certificate.PairSemantics.sound3171_e`, `OAI.MUB6.Certificate.PairSemantics.sound3172_e`, `OAI.MUB6.Certificate.PairSemantics.sound3173_e`, `OAI.MUB6.Certificate.PairSemantics.sound3174_e`, `OAI.MUB6.Certificate.PairSemantics.sound3176_e`, `OAI.MUB6.Certificate.PairSemantics.sound3178_e`, `OAI.MUB6.Certificate.PairSemantics.sound3179_e`, `OAI.MUB6.Certificate.PairSemantics.sound3180_e`, `OAI.MUB6.Certificate.PairSemantics.sound3181_e`, `OAI.MUB6.Certificate.PairSemantics.sound3183_e`, `OAI.MUB6.Certificate.PairSemantics.sound3184_e`, `OAI.MUB6.Certificate.PairSemantics.sound3185_e`, `OAI.MUB6.Certificate.PairSemantics.sound3187_e`, `OAI.MUB6.Certificate.PairSemantics.sound3188_e`, `OAI.MUB6.Certificate.PairSemantics.sound3189_e`, `OAI.MUB6.Certificate.PairSemantics.sound3191_e`, `OAI.MUB6.Certificate.PairSemantics.sound3192_e`, `OAI.MUB6.Certificate.PairSemantics.sound3193_e`, `OAI.MUB6.Certificate.PairSemantics.sound3194_e`, `OAI.MUB6.Certificate.PairSemantics.sound3195_e`, `OAI.MUB6.Certificate.PairSemantics.sound3196_e`, `OAI.MUB6.Certificate.PairSemantics.sound3197_e`, `OAI.MUB6.Certificate.PairSemantics.sound3198_e`, `OAI.MUB6.Certificate.PairSemantics.sound3199_e`, `OAI.MUB6.Certificate.PairSemantics.sound3200_e`, `OAI.MUB6.Certificate.PairSemantics.sound3201_e`, `OAI.MUB6.Certificate.PairSemantics.sound3202_e`, `OAI.MUB6.Certificate.PairSemantics.sound3203_e`, `OAI.MUB6.Certificate.PairSemantics.sound3204_e`, `OAI.MUB6.Certificate.PairSemantics.sound3205_e`, `OAI.MUB6.Certificate.PairSemantics.sound3206_e`, `OAI.MUB6.Certificate.PairSemantics.sound3208_e`, `OAI.MUB6.Certificate.PairSemantics.sound3209_e`, `OAI.MUB6.Certificate.PairSemantics.sound3211_e`, `OAI.MUB6.Certificate.PairSemantics.sound3212_e`, `OAI.MUB6.Certificate.PairSemantics.sound3213_e`, `OAI.MUB6.Certificate.PairSemantics.sound3215_e`, `OAI.MUB6.Certificate.PairSemantics.sound3216_e`, `OAI.MUB6.Certificate.PairSemantics.sound3218_e`, `OAI.MUB6.Certificate.PairSemantics.sound3220_e`, `OAI.MUB6.Certificate.PairSemantics.sound3221_e`, `OAI.MUB6.Certificate.PairSemantics.sound3222_e`, `OAI.MUB6.Certificate.PairSemantics.sound3223_e`, `OAI.MUB6.Certificate.PairSemantics.sound3224_e`, `OAI.MUB6.Certificate.PairSemantics.sound3225_e`, `OAI.MUB6.Certificate.PairSemantics.sound3226_e`, `OAI.MUB6.Certificate.PairSemantics.sound3227_e`, `OAI.MUB6.Certificate.PairSemantics.sound3228_e`, `OAI.MUB6.Certificate.PairSemantics.sound3229_e`, `OAI.MUB6.Certificate.PairSemantics.sound3230_e`, `OAI.MUB6.Certificate.PairSemantics.sound3233_e`, `OAI.MUB6.Certificate.PairSemantics.sound3234_e`, `OAI.MUB6.Certificate.PairSemantics.sound3235_e`, `OAI.MUB6.Certificate.PairSemantics.sound3237_e`, `OAI.MUB6.Certificate.PairSemantics.sound3238_e`, `OAI.MUB6.Certificate.PairSemantics.sound3240_e`, `OAI.MUB6.Certificate.PairSemantics.sound3242_e`, `OAI.MUB6.Certificate.PairSemantics.sound3243_e`, `OAI.MUB6.Certificate.PairSemantics.sound3244_e`, `OAI.MUB6.Certificate.PairSemantics.sound3246_e`, `OAI.MUB6.Certificate.PairSemantics.sound3247_e`, `OAI.MUB6.Certificate.PairSemantics.sound3248_e`, `OAI.MUB6.Certificate.PairSemantics.sound3249_e`, `OAI.MUB6.Certificate.PairSemantics.sound3253_e`, `OAI.MUB6.Certificate.PairSemantics.sound3254_e`, `OAI.MUB6.Certificate.PairSemantics.sound3255_e`, `OAI.MUB6.Certificate.PairSemantics.sound3256_e`, `OAI.MUB6.Certificate.PairSemantics.sound3258_e`, `OAI.MUB6.Certificate.PairSemantics.sound3260_e`, `OAI.MUB6.Certificate.PairSemantics.sound3262_e`, `OAI.MUB6.Certificate.PairSemantics.sound3263_e`, `OAI.MUB6.Certificate.PairSemantics.sound3264_e`, `OAI.MUB6.Certificate.PairSemantics.sound3266_e`, `OAI.MUB6.Certificate.PairSemantics.sound3267_e`, `OAI.MUB6.Certificate.PairSemantics.sound3268_e`, `OAI.MUB6.Certificate.PairSemantics.sound3269_e`, `OAI.MUB6.Certificate.PairSemantics.sound3271_e`, `OAI.MUB6.Certificate.PairSemantics.sound3272_e`, `OAI.MUB6.Certificate.PairSemantics.sound3273_e`, `OAI.MUB6.Certificate.PairSemantics.sound3274_e`, `OAI.MUB6.Certificate.PairSemantics.sound3275_e`, `OAI.MUB6.Certificate.PairSemantics.sound3276_e`, `OAI.MUB6.Certificate.PairSemantics.sound3277_e`, `OAI.MUB6.Certificate.PairSemantics.sound3278_e`, `OAI.MUB6.Certificate.PairSemantics.sound3279_e`, `OAI.MUB6.Certificate.PairSemantics.sound3280_e`, `OAI.MUB6.Certificate.PairSemantics.sound3281_e`, `OAI.MUB6.Certificate.PairSemantics.sound3282_e`, `OAI.MUB6.Certificate.PairSemantics.sound3283_e`, `OAI.MUB6.Certificate.PairSemantics.sound3284_e`, `OAI.MUB6.Certificate.PairSemantics.sound3288_e`, `OAI.MUB6.Certificate.PairSemantics.sound3289_e`, `OAI.MUB6.Certificate.PairSemantics.sound3290_e`, `OAI.MUB6.Certificate.PairSemantics.sound3291_e`, `OAI.MUB6.Certificate.PairSemantics.sound3292_e`, `OAI.MUB6.Certificate.PairSemantics.sound3293_e`, `OAI.MUB6.Certificate.PairSemantics.sound3294_e`, `OAI.MUB6.Certificate.PairSemantics.sound3295_e`, `OAI.MUB6.Certificate.PairSemantics.sound3296_e`, `OAI.MUB6.Certificate.PairSemantics.sound3297_e`, `OAI.MUB6.Certificate.PairSemantics.sound3298_e`, `OAI.MUB6.Certificate.PairSemantics.sound3299_e`, `OAI.MUB6.Certificate.PairSemantics.sound3300_e`, `OAI.MUB6.Certificate.PairSemantics.sound3301_e`, `OAI.MUB6.Certificate.PairSemantics.sound3302_e`, `OAI.MUB6.Certificate.PairSemantics.sound3303_e`, `OAI.MUB6.Certificate.PairSemantics.sound3304_e`, `OAI.MUB6.Certificate.PairSemantics.sound3305_e`, `OAI.MUB6.Certificate.PairSemantics.sound3307_e`, `OAI.MUB6.Certificate.PairSemantics.sound3308_e`, `OAI.MUB6.Certificate.PairSemantics.sound3309_e`, `OAI.MUB6.Certificate.PairSemantics.sound3310_e`, `OAI.MUB6.Certificate.PairSemantics.sound3311_e`, `OAI.MUB6.Certificate.PairSemantics.sound3313_e`, `OAI.MUB6.Certificate.PairSemantics.sound3314_e`, `OAI.MUB6.Certificate.PairSemantics.sound3315_e`, `OAI.MUB6.Certificate.PairSemantics.sound3316_e`, `OAI.MUB6.Certificate.PairSemantics.sound3317_e`, `OAI.MUB6.Certificate.PairSemantics.sound3319_e`, `OAI.MUB6.Certificate.PairSemantics.sound3322_e`, `OAI.MUB6.Certificate.PairSemantics.sound3324_e`, `OAI.MUB6.Certificate.PairSemantics.sound3325_e`, `OAI.MUB6.Certificate.PairSemantics.sound3326_e`, `OAI.MUB6.Certificate.PairSemantics.sound3327_e`, `OAI.MUB6.Certificate.PairSemantics.sound3328_e`, `OAI.MUB6.Certificate.PairSemantics.sound3331_e`, `OAI.MUB6.Certificate.PairSemantics.sound3333_e`, `OAI.MUB6.Certificate.PairSemantics.sound3334_e`, `OAI.MUB6.Certificate.PairSemantics.sound3335_e`, `OAI.MUB6.Certificate.PairSemantics.sound3336_e`, `OAI.MUB6.Certificate.PairSemantics.sound3338_e`, `OAI.MUB6.Certificate.PairSemantics.sound3339_e`, `OAI.MUB6.Certificate.PairSemantics.sound3341_e`, `OAI.MUB6.Certificate.PairSemantics.sound3343_e`, `OAI.MUB6.Certificate.PairSemantics.sound3345_e`, `OAI.MUB6.Certificate.PairSemantics.sound3346_e`, `OAI.MUB6.Certificate.PairSemantics.sound3347_e`, `OAI.MUB6.Certificate.PairSemantics.sound3348_e`, `OAI.MUB6.Certificate.PairSemantics.sound3349_e`, `OAI.MUB6.Certificate.PairSemantics.sound3350_e`, `OAI.MUB6.Certificate.PairSemantics.sound3351_e`, `OAI.MUB6.Certificate.PairSemantics.sound3352_e`, `OAI.MUB6.Certificate.PairSemantics.sound3353_e`, `OAI.MUB6.Certificate.PairSemantics.sound3354_e`, `OAI.MUB6.Certificate.PairSemantics.sound3355_e`, `OAI.MUB6.Certificate.PairSemantics.sound3356_e`, `OAI.MUB6.Certificate.PairSemantics.sound3357_e`, `OAI.MUB6.Certificate.PairSemantics.sound3358_e`, `OAI.MUB6.Certificate.PairSemantics.sound3359_e`, `OAI.MUB6.Certificate.PairSemantics.sound3360_e`, `OAI.MUB6.Certificate.PairSemantics.sound3361_e`, `OAI.MUB6.Certificate.PairSemantics.sound3362_e`, `OAI.MUB6.Certificate.PairSemantics.sound3363_e`, `OAI.MUB6.Certificate.PairSemantics.sound3364_e`, `OAI.MUB6.Certificate.PairSemantics.sound3366_e`, `OAI.MUB6.Certificate.PairSemantics.sound3367_e`, `OAI.MUB6.Certificate.PairSemantics.sound3368_e`, `OAI.MUB6.Certificate.PairSemantics.sound3369_e`, `OAI.MUB6.Certificate.PairSemantics.sound3370_e`, `OAI.MUB6.Certificate.PairSemantics.sound3371_e`, `OAI.MUB6.Certificate.PairSemantics.sound3372_e`, `OAI.MUB6.Certificate.PairSemantics.sound3375_e`, `OAI.MUB6.Certificate.PairSemantics.sound3376_e`, `OAI.MUB6.Certificate.PairSemantics.sound3377_e`, `OAI.MUB6.Certificate.PairSemantics.sound3378_e`, `OAI.MUB6.Certificate.PairSemantics.sound3380_e`, `OAI.MUB6.Certificate.PairSemantics.sound3382_e`, `OAI.MUB6.Certificate.PairSemantics.sound3383_e`, `OAI.MUB6.Certificate.PairSemantics.sound3384_e`, `OAI.MUB6.Certificate.PairSemantics.sound3385_e`, `OAI.MUB6.Certificate.PairSemantics.sound3387_e`, `OAI.MUB6.Certificate.PairSemantics.sound3388_e`, `OAI.MUB6.Certificate.PairSemantics.sound3389_e`, `OAI.MUB6.Certificate.PairSemantics.sound3390_e`, `OAI.MUB6.Certificate.PairSemantics.sound3391_e`, `OAI.MUB6.Certificate.PairSemantics.sound3392_e`, `OAI.MUB6.Certificate.PairSemantics.sound3393_e`, `OAI.MUB6.Certificate.PairSemantics.sound3394_e`, `OAI.MUB6.Certificate.PairSemantics.sound3395_e`, `OAI.MUB6.Certificate.PairSemantics.sound3396_e`, `OAI.MUB6.Certificate.PairSemantics.sound3397_e`, `OAI.MUB6.Certificate.PairSemantics.sound3399_e`, `OAI.MUB6.Certificate.PairSemantics.sound3400_e`, `OAI.MUB6.Certificate.PairSemantics.sound3401_e`, `OAI.MUB6.Certificate.PairSemantics.sound3402_e`, `OAI.MUB6.Certificate.PairSemantics.sound3405_e`, `OAI.MUB6.Certificate.PairSemantics.sound3407_e`, `OAI.MUB6.Certificate.PairSemantics.sound3408_e`, `OAI.MUB6.Certificate.PairSemantics.sound3411_e`, `OAI.MUB6.Certificate.PairSemantics.sound3412_e`, `OAI.MUB6.Certificate.PairSemantics.sound3413_e`, `OAI.MUB6.Certificate.PairSemantics.sound3414_e`, `OAI.MUB6.Certificate.PairSemantics.sound3415_e`, `OAI.MUB6.Certificate.PairSemantics.sound3416_e`, `OAI.MUB6.Certificate.PairSemantics.sound3417_e`, `OAI.MUB6.Certificate.PairSemantics.sound3418_e`, `OAI.MUB6.Certificate.PairSemantics.sound3419_e`, `OAI.MUB6.Certificate.PairSemantics.sound3420_e`, `OAI.MUB6.Certificate.PairSemantics.sound3421_e`, `OAI.MUB6.Certificate.PairSemantics.sound3422_e`, `OAI.MUB6.Certificate.PairSemantics.sound3423_e`, `OAI.MUB6.Certificate.PairSemantics.sound3424_e`, `OAI.MUB6.Certificate.PairSemantics.sound3425_e`, `OAI.MUB6.Certificate.PairSemantics.sound3428_e`, `OAI.MUB6.Certificate.PairSemantics.sound3431_e`, `OAI.MUB6.Certificate.PairSemantics.sound3433_e`, `OAI.MUB6.Certificate.PairSemantics.sound3434_e`, `OAI.MUB6.Certificate.PairSemantics.sound3435_e`, `OAI.MUB6.Certificate.PairSemantics.sound3436_e`, `OAI.MUB6.Certificate.PairSemantics.sound3437_e`, `OAI.MUB6.Certificate.PairSemantics.sound3439_e`, `OAI.MUB6.Certificate.PairSemantics.sound3440_e`, `OAI.MUB6.Certificate.PairSemantics.sound3441_e`, `OAI.MUB6.Certificate.PairSemantics.sound3442_e`, `OAI.MUB6.Certificate.PairSemantics.sound3443_e`, `OAI.MUB6.Certificate.PairSemantics.sound3444_e`, `OAI.MUB6.Certificate.PairSemantics.sound3447_e`, `OAI.MUB6.Certificate.PairSemantics.sound3449_e`, `OAI.MUB6.Certificate.PairSemantics.sound3451_e`, `OAI.MUB6.Certificate.PairSemantics.sound3454_e`, `OAI.MUB6.Certificate.PairSemantics.sound3455_e`, `OAI.MUB6.Certificate.PairSemantics.sound3456_e`, `OAI.MUB6.Certificate.PairSemantics.sound3457_e`, `OAI.MUB6.Certificate.PairSemantics.sound3458_e`, `OAI.MUB6.Certificate.PairSemantics.sound3459_e`, `OAI.MUB6.Certificate.PairSemantics.sound3460_e`, `OAI.MUB6.Certificate.PairSemantics.sound3461_e`, `OAI.MUB6.Certificate.PairSemantics.sound3462_e`, `OAI.MUB6.Certificate.PairSemantics.sound3463_e`, `OAI.MUB6.Certificate.PairSemantics.sound3467_e`, `OAI.MUB6.Certificate.PairSemantics.sound3468_e`, `OAI.MUB6.Certificate.PairSourceBridge.allRowsSound_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound0_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound100_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound101_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound102_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound103_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound104_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound105_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound106_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound107_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound108_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound10_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound110_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound111_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound112_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound113_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound114_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound115_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound116_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound117_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound118_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound119_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound120_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound121_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound123_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound124_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound125_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound127_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound128_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound129_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound12_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound130_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound131_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound132_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound133_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound134_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound135_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound136_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound137_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound138_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound139_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound140_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound141_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound142_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound143_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound144_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound145_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound146_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound147_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound148_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound149_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound14_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound150_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound151_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound152_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound153_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound154_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound155_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound156_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound157_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound158_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound159_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound15_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound160_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound161_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound162_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound163_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound164_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound165_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound166_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound167_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound168_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound16_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound170_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound171_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound172_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound174_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound175_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound176_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound177_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound178_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound179_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound17_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound180_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound181_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound182_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound183_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound184_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound185_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound186_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound187_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound188_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound189_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound18_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound190_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound191_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound192_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound193_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound194_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound195_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound196_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound197_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound198_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound199_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound19_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound1_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound200_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound202_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound203_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound204_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound205_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound206_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound207_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound208_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound209_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound20_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound210_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound211_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound212_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound213_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound214_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound215_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound216_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound217_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound218_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound219_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound21_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound220_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound221_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound222_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound223_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound224_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound225_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound226_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound227_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound228_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound229_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound22_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound230_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound231_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound232_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound233_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound234_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound235_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound236_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound237_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound238_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound239_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound23_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound240_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound241_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound242_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound243_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound244_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound245_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound246_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound247_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound248_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound249_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound24_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound250_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound251_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound252_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound253_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound254_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound26_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound27_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound28_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound29_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound2_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound30_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound31_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound32_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound34_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound35_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound36_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound37_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound38_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound39_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound3_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound40_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound41_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound42_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound43_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound44_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound45_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound46_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound47_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound49_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound4_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound50_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound51_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound52_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound53_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound54_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound55_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound56_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound58_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound59_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound5_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound60_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound61_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound62_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound63_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound64_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound65_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound66_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound67_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound69_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound6_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound70_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound72_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound73_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound74_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound75_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound76_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound77_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound78_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound79_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound7_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound80_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound81_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound82_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound83_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound84_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound85_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound86_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound87_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound88_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound89_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound8_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound90_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound91_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound92_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound93_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound94_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound95_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound96_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound97_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound98_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound99_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound9_e`, `OAI.MUB6.Certificate.PairTargetSemantics.expandedIdentity1_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm11_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm12_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm13_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm14_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm16_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm17_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm18_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm19_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm21_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm22_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm23_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm24_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm25_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm26_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm6_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm7_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm8_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm9_e` and `OAI.MUB6.pair_cross_certificate_e`.
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

def raw7step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]

def raw7step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw8 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]

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

def raw78step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2], ![-3, 3, 0]]

def raw78step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]

def raw79 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]

def raw79step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]

def raw79step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw80 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]

def raw80step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]

def raw80step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def raw81 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]

def raw81step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]

def raw81step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw82 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]

def raw82step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]

def raw82step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

def raw83 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]

def raw83step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 3, -4]]

def raw84 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]

def raw84step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 3, -4]]

def raw85 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]

def raw85step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]

def raw85step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]

def raw86 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]

def raw86step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 3, -4]]

def raw87 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]

def raw87step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]

def raw87step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

def raw88 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]

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

def raw94step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-2, 0, 2], ![-3, 3, 0]]

def raw94step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]

def raw95 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]

def raw95step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]

def raw95step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw784step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]

def raw784step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -2, 1]]

def raw785 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]

def raw785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]

def raw786 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]

def raw787 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

def raw788 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0]]

def raw788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

def raw789 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

def raw790 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1]]

def raw790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

def raw791 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]

def raw791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]

def raw791step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

def raw792 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]

def raw792step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]

def raw792step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def raw793 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]

def raw793step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]

def raw794 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![2, -3, 1], ![1, 0, -1]]

def raw794step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]

def raw795 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]

def raw795step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-3, 3, 0]]

def raw795step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![2, -2, 0]]

def raw796 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]

def raw797 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![0, 2, -2], ![2, 0, -2]]

def raw797step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]

def raw798 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![1, -1, 0], ![1, 3, -4]]

def raw799 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![1, 0, -1], ![1, 2, -3]]

def raw799step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical245
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7844step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, -1, -2, 2]]

def raw7845 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, -2, 2, -1]]

def raw7846 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw7847 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw7848step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![-1, -2, 3], ![1, 2, -3]]

def raw7848step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![2, 1, -3]]

def raw7849 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw7849step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw7850 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 3, -3], ![1, -1, 0, 0]]

def raw7851 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -2, 3, -2]]

def raw7852 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw7853 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw7854 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0]]

def raw7854step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 0, -1], ![-1, -1, 2, 0], ![1, 1, -2, 0]]

def raw7854step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw7855 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, 3, -3], ![1, -1, -1, 1]]

def raw7856 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 3, -2]]

def raw7856step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-1, -1, -1, 3], ![1, 1, 0, -2]]

def raw7856step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw7857 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -2, 2, -1]]

def raw7857step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-1, -1, 0, 2], ![1, 1, -1, -1]]

def raw7857step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw7858 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -2, 1, 0]]

def raw7858step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 1, -1], ![0, 0, 1, -1], ![0, -1, -1, 2], ![-1, 2, -1, 0]]

def raw7858step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 1, -1, -1]]

def raw7859 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -2, 0, 1]]

def raw7859step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-1, -1, 2, 0], ![1, 1, -3, 1]]

def raw7859step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, 0, -1, 2], ![1, 1, -2, 0], ![-1, -1, 3, -1]]

def raw7859step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw7860 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -2, -1, 2]]

def raw7860step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-1, -1, 3, -1], ![1, 1, -4, 2]]

def raw7860step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, 0, -1, 2], ![1, 1, -3, 1], ![-1, -1, 4, -2]]

def raw7860step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 1, 1, -3]]

def raw7861 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 0, 0], ![0, 0, 1, -1], ![1, -1, 0, 0]]

def raw7861step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 0, -1], ![-1, 0, 1, 0], ![1, 0, -1, 0]]

def raw7861step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0]]

def raw7861step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]

def raw7862 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 0, 0], ![1, -1, 1, -1]]

def raw7862step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![-1, 0, 1], ![1, 0, -1]]

def raw7862step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![1, -1]]

def raw7862step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw7863 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![1, -1, 0, 0]]

def raw7863step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 0, -1], ![-1, 1, 0, 0], ![1, -1, 0, 0]]

def raw7863step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0]]

def raw7863step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]

def raw7864 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, -1, 1]]

def raw7864step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 0, -1], ![-1, 1, 1, -1], ![1, -1, -1, 1]]

def raw7864step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 1, -1, -1]]

def raw7865 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 1, -1], ![0, 1, 2, -3], ![1, -2, -2, 3]]

def raw7865step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-1, 1, 2, -2], ![1, -1, -3, 3]]

def raw7865step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, -1, 2, -2]]

def raw7866 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0]]

def raw7866step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0]]

def raw7866step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]

def raw7867 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -2, 0, 1]]

def raw7867step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-1, 2, -1, 0], ![1, -2, 0, 1]]

def raw7867step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw7868 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -2, -2, 3]]

def raw7869 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 2, -2], ![1, -1, -1, 1]]

def raw7869step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![-1, 2, -1], ![1, -2, 1]]

def raw7869step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]

def raw7870 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -2, 0, 1]]

def raw7871 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -2, -1, 2]]

def raw7871step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-1, 3, -1, -1], ![1, -3, 0, 2]]

def raw7871step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 2, -3], ![1, 1, -2, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical246
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7872 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 3, -3], ![1, -1, -2, 2]]

def raw7872step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![-1, 3, -2], ![1, -3, 2]]

def raw7872step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3]]

def raw7873 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![1, -2, -2, 3], ![0, 1, 3, -4]]

def raw7873step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3], ![1, 3, -4]]

def raw7873step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-1, 2, -1], ![1, 2, -3], ![-1, -3, 4]]

def raw7873step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 2, -3]]

def raw7874 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![1, -1, -2, 2], ![0, 0, 3, -3]]

def raw7874step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![1, -1, 0], ![-1, -2, 3], ![1, 2, -3]]

def raw7874step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3]]

def raw7876 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw7876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw7877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 3, -5]]

def raw7877step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, -3, 5]]

def raw7877step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw7878 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw7878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]

def raw7878step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw7880 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -3, 3], ![0, 2, -2], ![1, 0, -1]]

def raw7880step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0]]

def raw7883 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -3, 3], ![1, 2, -3]]

def raw7883step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -1, 0], ![0, 3, -3], ![-1, -2, 3]]

def raw7883step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 3, -3], ![1, -1, 0]]

def raw7884 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -2, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1]]

def raw7884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1]]

def raw7884step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw7885 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1]]

def raw7885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def raw7886 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0]]

def raw7886step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0]]

def raw7886step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

def raw7887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![2, 3, -5]]

def raw7887step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![0, 1, -1], ![0, 1, -1], ![-2, -3, 5]]

def raw7887step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw7888 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw7888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw7889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![0, -1, 1], ![2, 3, -5]]

def raw7889step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![0, 1, -1], ![-2, -3, 5]]

def raw7889step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw7890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![2, 3, -5]]

def raw7890step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![-2, -3, 5]]

def raw7890step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw7891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 3, -4]]

def raw7891step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, -3, 4]]

def raw7891step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw7892 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1]]

def raw7892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw7893 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0]]

def raw7893step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0]]

def raw7893step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]

def raw7894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-1, -2, 3]]

def raw7894step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw7895 : Matrix (Fin 2) (Fin 3) ℤ := ![![-1, 1, 0], ![1, -1, 0]]

def raw7895step0 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

def raw7896 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, -1, -3, 4], ![0, 0, 2, -2], ![1, 0, 1, -2]]

def raw7896step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw7897 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, -1, -1, 2], ![0, -1, -1, 2], ![1, 1, 2, -4]]

def raw7897step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 0, 0], ![0, 1, 1, -2], ![0, 1, 1, -2], ![-1, -1, -2, 4]]

def raw7897step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw7898 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, -1, -1, 1]]

def raw7898step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 0, 0], ![0, 1, -3, 2], ![0, -1, 2, -1], ![-1, 1, 1, -1]]

def raw7898step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw7899 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -2, -1, 2]]

def raw7899step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![0, -1, 2, -1], ![0, 1, -3, 2]]

def raw7899step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, -1, 3, -2]]

def raw7899step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw7900 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -2, -2, 3]]

def raw7900step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![0, 1, 1, -2], ![0, -1, -2, 3]]

def raw7900step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw7901 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 1, 2, -3], ![1, -2, -2, 3]]

def raw7901step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 1, -2], ![0, 2, -2], ![0, -3, 3]]

def raw7901step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, -1, 2], ![0, -2, 2], ![0, 3, -3]]

def raw7901step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

def raw7902 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![-3, 1, 1, 1], ![4, -2, -2, 0]]

def raw7902step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![1, 1, -2], ![1, 1, -2], ![-1, 1, 0]]

def raw7902step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2]]

def raw7903 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![-3, 1, 2, 0], ![4, -2, -3, 1]]

def raw7903step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![1, 1, -2], ![1, 2, -3], ![-1, 0, 1]]

def raw7903step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 0, 1], ![1, 1, -2], ![1, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical247
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7904 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![-2, -2, 1, 3], ![3, 1, -2, -2]]

def raw7904step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![1, -2, 1], ![1, 1, -2], ![-1, 3, -2]]

def raw7904step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![1, -2, 1], ![1, 1, -2]]

def raw7905 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![-2, -2, 2, 2], ![3, 1, -3, -1]]

def raw7905step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![1, -2, 1], ![1, 2, -3], ![-1, 2, -1]]

def raw7905step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 2, -3]]

def raw7906 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![-2, -2, 3, 1], ![3, 1, -4, 0]]

def raw7906step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![1, -2, 1], ![1, 3, -4], ![-1, 1, 0]]

def raw7906step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![-1, -3, 4], ![1, -1, 0]]

def raw7906step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 2, -3]]

def raw7907 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![-2, 1, 1, 0], ![3, -2, -2, 1]]

def raw7907step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![1, 1, -2], ![1, 1, -2], ![-1, 0, 1]]

def raw7907step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]

def raw7908 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![-2, 1, 2, -1], ![3, -2, -3, 2]]

def raw7908step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![1, 1, -2], ![1, 2, -3], ![-1, -1, 2]]

def raw7908step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![1, 1, -2], ![1, 2, -3]]

def raw7909 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![-1, -3, 1, 3], ![2, 2, -2, -2]]

def raw7909step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -3, 2], ![1, 1, -2], ![-1, 3, -2]]

def raw7909step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 2, -3]]

def raw7910 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![-1, -3, 2, 2], ![2, 2, -3, -1]]

def raw7910step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -3, 2], ![1, 2, -3], ![-1, 2, -1]]

def raw7910step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 3, -2], ![-1, -2, 3], ![1, -2, 1]]

def raw7910step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![1, -2, 1], ![1, 1, -2]]

def raw7911 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![-1, -3, 3, 1], ![2, 2, -4, 0]]

def raw7911step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -3, 2], ![1, 3, -4], ![-1, 1, 0]]

def raw7911step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 3, -2], ![-1, -3, 4], ![1, -1, 0]]

def raw7911step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![1, -1, 0], ![1, 1, -2]]

def raw7912 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![-1, -2, -2, 5], ![2, 1, 1, -4]]

def raw7912step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -2, 1], ![1, -2, 1], ![-1, 5, -4]]

def raw7912step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -4, 5], ![-1, 2, -1], ![1, 1, -2], ![1, 1, -2]]

def raw7913 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![-1, -2, 1, 2], ![2, 1, -2, -1]]

def raw7913step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![-1, 2, -1]]

def raw7913step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2]]

def raw7914 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![-1, -2, 2, 1], ![2, 1, -3, 0]]

def raw7914step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -2, 1], ![1, 2, -3], ![-1, 1, 0]]

def raw7914step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![-1, -2, 3], ![1, -1, 0]]

def raw7914step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

def raw7915 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![-1, -2, 3, 0], ![2, 1, -4, 1]]

def raw7915step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -2, 1], ![1, 3, -4], ![-1, 0, 1]]

def raw7915step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![-1, -3, 4], ![1, 0, -1]]

def raw7915step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2]]

def raw7916 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![-1, 1, 1, -1], ![2, -2, -2, 2]]

def raw7916step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![1, 1, -2], ![1, 1, -2], ![-1, -1, 2]]

def raw7916step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![1, 1, -2], ![1, 1, -2]]

def raw7917 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![-1, 1, 2, -2], ![2, -2, -3, 3]]

def raw7917step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![1, 1, -2], ![1, 2, -3], ![-1, -2, 3]]

def raw7917step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![1, 1, -2], ![1, 2, -3]]

def raw7918 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -4, 2, 2], ![1, 3, -3, -1]]

def raw7918step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, -4, 3], ![1, 2, -3], ![-1, 2, -1]]

def raw7918step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, 4, -3], ![-1, -2, 3], ![1, -2, 1]]

def raw7918step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![1, -1, 0], ![1, 1, -2]]

def raw7919 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -3, 1, 2], ![1, 2, -2, -1]]

def raw7919step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, -3, 2], ![1, 1, -2], ![-1, 2, -1]]

def raw7919step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, 3, -2], ![-1, -1, 2], ![1, -2, 1]]

def raw7919step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

def raw7920 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -3, 2, 1], ![1, 2, -3, 0]]

def raw7920step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, -3, 2], ![1, 2, -3], ![-1, 1, 0]]

def raw7920step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, 3, -2], ![-1, -2, 3], ![1, -1, 0]]

def raw7920step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1]]

def raw7921 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -2, -2, 4], ![1, 1, 1, -3]]

def raw7921step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, -2, 1], ![1, -2, 1], ![-1, 4, -3]]

def raw7921step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2]]

def raw7922 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -2, 1, 1], ![1, 1, -2, 0]]

def raw7922step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![-1, 1, 0]]

def raw7922step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]

def raw7923 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -2, 3, -1], ![1, 1, -4, 2]]

def raw7923step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, -2, 1], ![1, 3, -4], ![-1, -1, 2]]

def raw7923step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, 2, -1], ![-1, -3, 4], ![1, 1, -2]]

def raw7923step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2]]

def raw7924 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, -3, 4], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw7924step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, -1, 1], ![0, 1, 3, -4], ![0, -1, -1, 2], ![-1, 1, -1, 1]]

def raw7924step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def raw7925 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, -1, 2], ![0, 1, 0, -1], ![1, -1, 0, 0]]

def raw7925step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 1, -1]]

def raw7926 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, -1, -1, 1]]

def raw7927 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, 0, 1], ![0, 1, 0, -1], ![1, -1, -1, 1]]

def raw7927step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1]]

def raw7928 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw7928step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, -1, 1, -1], ![1, 1, 0, -2], ![-1, 0, -1, 2]]

def raw7928step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw7929 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, -2, -1, 2]]

def raw7930 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -2, -1, 2]]

def raw7930step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, -1, -2, 2]]

def raw7931 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -2, -2, 3]]

def raw7932 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 0, 0, 0], ![0, 1, 1, -2], ![1, -2, -2, 3]]

def raw7932step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![1, 0, 1, -2], ![-1, 0, -2, 3]]

def raw7932step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![-1, -2, 3]]

def raw7932step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]

def raw7933 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![1, -1, -2, 2]]

def raw7933step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 0, -1], ![1, 1, 0, -2], ![-1, -1, 0, 2]]

def raw7933step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![-1, -1, 2]]

def raw7933step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

def raw7934 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

def raw7934step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![1, 1, 0, -2], ![-1, -1, -1, 3]]

def raw7934step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw7935 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -2, -3, 4]]

def raw7935step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![1, 1, 1, -3], ![-1, -1, -2, 4]]

def raw7935step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 1, 1, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical248
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7936 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 0, 1, -1], ![1, -1, -2, 2]]

def raw7936step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![-1, -1, 2]]

def raw7936step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

def raw7937 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 0, 2, -2], ![1, -1, -3, 3]]

def raw7937step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![-1, -2, 3]]

def raw7937step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![2, 1, -3]]

def raw7938 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 1, 1, -2], ![1, -2, -2, 3]]

def raw7938step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![-1, -2, 3]]

def raw7938step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]

def raw7939 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 1, 2, -3], ![1, -2, -3, 4]]

def raw7939step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 1, -2], ![1, 2, -3], ![-1, -3, 4]]

def raw7939step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 0, 1], ![1, 1, -2], ![1, 2, -3]]

def raw7940 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![1, -4, 2, 1], ![0, 3, -3, 0]]

def raw7940step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![1, -4, 3], ![1, 2, -3], ![-1, 1, 0]]

def raw7940step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-1, 4, -3], ![-1, -2, 3], ![1, -1, 0]]

def raw7940step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1]]

def raw7941 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![1, -3, 1, 1], ![0, 2, -2, 0]]

def raw7941step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![1, -3, 2], ![1, 1, -2], ![-1, 1, 0]]

def raw7941step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-1, 3, -2], ![-1, -1, 2], ![1, -1, 0]]

def raw7941step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw7942 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![1, 1, 1, -3], ![0, -2, -2, 4]]

def raw7942step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![-1, -3, 4]]

def raw7942step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2]]

def raw7943 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![-1, -3, 2, 2], ![2, 2, -4, 0]]

def raw7943step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -3, 2], ![2, 2, -4], ![-2, 2, 0]]

def raw7943step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 3, -2], ![-2, -2, 4], ![2, -2, 0]]

def raw7943step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![1, 1, -2], ![2, -2, 0]]

def raw7944 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![-1, 3, -3, 1], ![2, -4, 1, 1]]

def raw7944step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![1, 3, -4], ![2, -3, 1], ![-2, 1, 1]]

def raw7944step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, -3, 4], ![-2, 3, -1], ![2, -1, -1]]

def raw7944step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 4, -3], ![1, -2, 1], ![2, -1, -1]]

def raw7945 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![-1, 3, -2, 0], ![2, -4, 0, 2]]

def raw7945step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![1, 3, -4], ![2, -2, 0], ![-2, 0, 2]]

def raw7945step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, -3, 4], ![-2, 2, 0], ![2, 0, -2]]

def raw7945step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

def raw7946 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, -3, 2, 1], ![1, 2, -4, 1]]

def raw7946step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, -3, 2], ![2, 2, -4], ![-2, 1, 1]]

def raw7946step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]

def raw7947 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, -2, 0, 2], ![0, 1, 0, -1], ![1, 0, -2, 1]]

def raw7947step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, -2, 2], ![0, 2, 0, -2], ![0, -1, 0, 1], ![-1, 0, 2, -1]]

def raw7947step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw7948 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, -2, 2, 0], ![1, 1, -4, 2]]

def raw7948step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, -2, 1], ![2, 2, -4], ![-2, 0, 2]]

def raw7948step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, 2, -1], ![-2, -2, 4], ![2, 0, -2]]

def raw7948step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def raw7949 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, -1, -1, 2], ![0, 1, 0, -1], ![1, -1, -1, 1]]

def raw7949step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, -2, 2], ![0, 1, 1, -2], ![0, -1, 0, 1], ![-1, 1, 1, -1]]

def raw7949step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, -1, -2, 2]]

def raw7950 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, 1, 0, -1], ![1, -2, -2, 3]]

def raw7950step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 1, -2], ![2, 0, -2], ![-2, -1, 3]]

def raw7950step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2]]

def raw7951 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, 1, 1, -2], ![1, -2, -3, 4]]

def raw7951step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 1, -2], ![2, 1, -3], ![-2, -2, 4]]

def raw7951step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![1, 1, -2], ![1, 2, -3]]

def raw7952 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, 3, -3, 0], ![1, -4, 1, 2]]

def raw7952step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 3, -4], ![2, -3, 1], ![-2, 0, 2]]

def raw7952step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, -3, 4], ![-2, 3, -1], ![2, 0, -2]]

def raw7952step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]

def raw7953 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, 3, -2, -1], ![1, -4, 0, 3]]

def raw7953step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 3, -4], ![2, -2, 0], ![-2, -1, 3]]

def raw7953step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, -3, 4], ![-2, 2, 0], ![2, 1, -3]]

def raw7953step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]

def raw7954 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![1, -3, 2, 0], ![0, 2, -4, 2]]

def raw7954step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![1, -3, 2], ![2, 2, -4], ![-2, 0, 2]]

def raw7954step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]

def raw7955 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![1, -2, 2, -1], ![0, 1, -4, 3]]

def raw7955step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![1, -2, 1], ![2, 2, -4], ![-2, -1, 3]]

def raw7955step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-1, 2, -1], ![-2, -2, 4], ![2, 1, -3]]

def raw7955step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]

def raw7956 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, -3, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -2, 1, 0]]

def raw7956step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![2, 0, 0, -2], ![-3, 1, 1, 1], ![2, -1, -1, 0]]

def raw7956step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, 0, 0, 2], ![3, -1, -1, -1], ![-2, 1, 1, 0]]

def raw7956step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def raw7957 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, -3, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -2, 0, 1]]

def raw7957step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![2, 0, 0, -2], ![-3, 1, 2, 0], ![2, -1, -2, 1]]

def raw7957step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, 0, 0, 2], ![3, -1, -2, 0], ![-2, 1, 2, -1]]

def raw7957step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 2, -1, -2]]

def raw7958 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, -3, 2], ![0, 0, 2, -2], ![0, 0, 1, -1], ![1, -2, 0, 1]]

def raw7958step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![2, 0, 0, -2], ![-3, 2, 1, 0], ![2, -2, -1, 1]]

def raw7958step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, 0, 0, 2], ![3, -2, -1, 0], ![-2, 2, 1, -1]]

def raw7958step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 2, -1, -2]]

def raw7959 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, -2, 1], ![0, -1, -1, 2], ![0, -1, 2, -1], ![1, 0, 1, -2]]

def raw7959step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -2, 2, -1], ![0, 1, 1, -2], ![0, 1, -2, 1], ![-1, 0, -1, 2]]

def raw7959step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -2, 2, -1]]

def raw7960 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, -2, 1], ![0, -1, -1, 2], ![0, -1, 3, -2], ![1, 0, 0, -1]]

def raw7960step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -2, 2, -1], ![0, 1, 1, -2], ![0, 1, -3, 2], ![-1, 0, 0, 1]]

def raw7960step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, -3, 2], ![0, 1, 1, -2], ![1, -2, 2, -1]]

def raw7961 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 2, -2, 1], ![0, -1, 3, -2], ![1, -1, -1, 1]]

def raw7961step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![2, -1, -1], ![-2, 3, -1], ![1, -2, 1]]

def raw7961step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

def raw7962 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, -2, 1], ![0, 0, -1, 1], ![0, 0, 3, -3], ![1, -2, 0, 1]]

def raw7962step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![2, 0, 0, -2], ![-2, -1, 3, 0], ![1, 1, -3, 1]]

def raw7962step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, 0, 0, 2], ![2, 1, -3, 0], ![-1, -1, 3, -1]]

def raw7962step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 2, -2, 0], ![1, 0, 2, -3]]

def raw7963 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, -2, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -2, 0, 1]]

def raw7963step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![2, 0, 0, -2], ![-2, 1, 1, 0], ![1, -1, -1, 1]]

def raw7963step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, 0, 0, 2], ![2, -1, -1, 0], ![-1, 1, 1, -1]]

def raw7963step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, -1, -1]]

def raw7964 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 2, -2, 1], ![0, 0, 3, -3], ![1, -2, -1, 2]]

def raw7964step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![2, 0, -2], ![-2, 3, -1], ![1, -3, 2]]

def raw7964step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]

def raw7965 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, -1, 0], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, -2, 0, 1]]

def raw7966 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, -1, 0], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -2, 0, 1]]

def raw7966step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def raw7967 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, -1, 0], ![0, 0, -1, 1], ![0, 0, 3, -3], ![1, -2, -1, 2]]

def raw7967step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![2, 0, 0, -2], ![-1, -1, 3, -1], ![0, 1, -3, 2]]

def raw7967step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 2, -2, 0], ![1, 0, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical249
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7968 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, 0, -1], ![0, -1, -3, 4], ![0, -1, 2, -1], ![1, 0, 1, -2]]

def raw7968step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -2, 0, 1], ![0, 1, 3, -4], ![0, 1, -2, 1], ![-1, 0, -1, 2]]

def raw7968step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw7969 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, 0, -1], ![0, -1, -3, 4], ![0, 0, 2, -2], ![1, -1, 1, -1]]

def raw7969step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -2, 0, 1], ![0, 1, 3, -4], ![0, 0, -2, 2], ![-1, 1, -1, 1]]

def raw7969step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw7970 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -2, -2, 3]]

def raw7970step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![2, 0, 0, -2], ![0, 1, 1, -2], ![-1, -1, -1, 3]]

def raw7970step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def raw7971 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, 0, -1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -2, -3, 4]]

def raw7971step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![2, 0, 0, -2], ![0, 1, 2, -3], ![-1, -1, -2, 4]]

def raw7971step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 2, 0, -3]]

def raw7972 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, 0, -1], ![0, 0, 2, -2], ![0, 0, 1, -1], ![1, -2, -3, 4]]

def raw7972step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![2, 0, 0, -2], ![0, 2, 1, -3], ![-1, -2, -1, 4]]

def raw7972step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 2, 0, -3]]

def raw7973 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 2, 0, -1], ![0, 0, 2, -2], ![1, -2, -2, 3]]

def raw7973step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![2, 0, -2], ![0, 2, -2], ![-1, -2, 3]]

def raw7973step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

def raw7974 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, 1, -2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -2, -3, 4]]

def raw7974step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![2, 0, 0, -2], ![1, 1, 1, -3], ![-2, -1, -1, 4]]

def raw7974step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, 1, -3]]

def raw7975 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 2, 1, -2], ![0, 0, 1, -1], ![1, -2, -2, 3]]

def raw7975step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![2, 0, -2], ![1, 1, -2], ![-2, -1, 3]]

def raw7975step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2]]

def raw7976 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 2, 1, -2], ![0, 0, 2, -2], ![1, -2, -3, 4]]

def raw7976step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![2, 0, -2], ![1, 2, -3], ![-2, -2, 4]]

def raw7976step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 2, -2], ![2, 1, -3]]

def raw7977 : Matrix (Fin 2) (Fin 3) ℤ := ![![-1, 3, -2], ![1, -3, 2]]

def raw7977step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![3, -3], ![-2, 2]]

def raw7977step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw7978 : Matrix (Fin 2) (Fin 1) ℤ := ![![0], ![0]]

def raw7978step0 : Matrix (Fin 1) (Fin 1) ℤ := ![![0]]

def raw7978step1 : Matrix (Fin 0) (Fin 1) ℤ := ![]

def raw7978step2 : Matrix (Fin 0) (Fin 0) ℤ := ![]

def raw7979 : Matrix (Fin 3) (Fin 1) ℤ := ![![0], ![0], ![0]]

def raw7979step0 : Matrix (Fin 2) (Fin 1) ℤ := ![![0], ![0]]

def raw7979step1 : Matrix (Fin 1) (Fin 1) ℤ := ![![0]]

def raw7979step2 : Matrix (Fin 0) (Fin 1) ℤ := ![]

def raw7979step3 : Matrix (Fin 0) (Fin 0) ℤ := ![]

def raw7980 : Matrix (Fin 4) (Fin 1) ℤ := ![![0], ![0], ![0], ![0]]

def raw7980step0 : Matrix (Fin 3) (Fin 1) ℤ := ![![0], ![0], ![0]]

def raw7980step1 : Matrix (Fin 2) (Fin 1) ℤ := ![![0], ![0]]

def raw7980step2 : Matrix (Fin 1) (Fin 1) ℤ := ![![0]]

def raw7980step3 : Matrix (Fin 0) (Fin 1) ℤ := ![]

def raw7980step4 : Matrix (Fin 0) (Fin 0) ℤ := ![]

def raw7981 : Matrix (Fin 5) (Fin 1) ℤ := ![![0], ![0], ![0], ![0], ![0]]

def raw7981step0 : Matrix (Fin 4) (Fin 1) ℤ := ![![0], ![0], ![0], ![0]]

def raw7981step1 : Matrix (Fin 3) (Fin 1) ℤ := ![![0], ![0], ![0]]

def raw7981step2 : Matrix (Fin 2) (Fin 1) ℤ := ![![0], ![0]]

def raw7981step3 : Matrix (Fin 1) (Fin 1) ℤ := ![![0]]

def raw7981step4 : Matrix (Fin 0) (Fin 1) ℤ := ![]

def raw7981step5 : Matrix (Fin 0) (Fin 0) ℤ := ![]

def raw7982 : Matrix (Fin 6) (Fin 1) ℤ := ![![0], ![0], ![0], ![0], ![0], ![0]]

def raw7982step0 : Matrix (Fin 5) (Fin 1) ℤ := ![![0], ![0], ![0], ![0], ![0]]

def raw7982step1 : Matrix (Fin 4) (Fin 1) ℤ := ![![0], ![0], ![0], ![0]]

def raw7982step2 : Matrix (Fin 3) (Fin 1) ℤ := ![![0], ![0], ![0]]

def raw7982step3 : Matrix (Fin 2) (Fin 1) ℤ := ![![0], ![0]]

def raw7982step4 : Matrix (Fin 1) (Fin 1) ℤ := ![![0]]

def raw7982step5 : Matrix (Fin 0) (Fin 1) ℤ := ![]

def raw7982step6 : Matrix (Fin 0) (Fin 0) ℤ := ![]

def raw7983 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![-1, 2, -1], ![0, 2, -2], ![1, 0, -1]]

def raw7983step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 4, -4], ![1, -1, 0]]

def raw7984 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -4, 4], ![-1, 2, -1], ![1, 2, -3]]

def raw7984step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 4, -4], ![1, -2, 1], ![-1, -2, 3]]

def raw7984step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 4, -4], ![1, -2, 1]]

def raw7985 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -4, 4], ![-1, 3, -2], ![1, 1, -2]]

def raw7985step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 4, -4], ![1, -2, 1]]

def raw7986 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -4, 4], ![-1, 4, -3], ![1, 0, -1]]

def raw7986step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 4, -4], ![1, -1, 0]]

def raw7987 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -4, 4], ![0, 2, -2], ![0, 2, -2]]

def raw7987step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![2, -2]]

def raw7988 : Matrix (Fin 2) (Fin 3) ℤ := ![![0, -4, 4], ![0, 4, -4]]

def raw7988step0 : Matrix (Fin 2) (Fin 2) ℤ := ![![-4, 4], ![4, -4]]

def raw7989 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 2, -3]]

def raw7989step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 1, -2], ![0, -2, 2], ![-1, -2, 3]]

def raw7989step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -2, 2], ![0, 3, -3], ![1, 1, -2]]

def raw7990 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-1, -1, 2], ![0, 3, -3], ![1, 1, -2]]

def raw7990step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -3, 3], ![0, 3, -3], ![1, 1, -2]]

def raw7991 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-1, -1, 2], ![0, 4, -4], ![1, 0, -1]]

def raw7991step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -3, 3], ![0, 4, -4], ![1, 0, -1]]

def raw7992 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw7992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

def raw7993 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1]]

def raw7993step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0]]

def raw7995 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -3, 3], ![-1, 2, -1], ![1, 1, -2]]

def raw7995step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -2, 1]]

def raw7996 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -3, 3], ![-1, 3, -2], ![1, 0, -1]]

def raw7996step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 3, -3], ![1, -1, 0]]

def raw7997 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -3, 3], ![-1, 4, -3], ![1, -1, 0]]

def raw7997step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 3, -3], ![1, 0, -1]]

def raw7998 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1]]

def raw7998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

def raw7999 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1]]

def raw7999step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw800 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]

def raw801 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![2, 2, -4]]

def raw802 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]

def raw802step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

def raw803 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -2, 1], ![1, 3, -4]]

def raw804 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]

def raw804step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

def raw805 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

def raw805step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

def raw806 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]

def raw806step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -3, 2], ![1, 2, -3]]

def raw807 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -2, 1], ![1, 2, -3]]

def raw807step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

def raw808 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

def raw808step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]

def raw808step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw812 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![1, -2, 1], ![1, 0, -1]]

def raw812step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

def raw813 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]

def raw813step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, -1, 2], ![-2, 2, 0]]

def raw813step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]

def raw814 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]

def raw815 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![2, -4, 2], ![1, 3, -4]]

def raw815step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 3, -4], ![2, -4, 2]]

def raw817 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 1, 2, 0], ![1, -2, -1, 2], ![2, 1, -1, -2]]

def raw817step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, -1, -1], ![0, 2, -2]]

def raw817step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

def raw818 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 1, 2, 0], ![1, -2, 2, -1], ![2, 1, -4, 1]]

def raw818step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 2, -4], ![0, -1, 1]]

def raw818step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]

def raw819 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 1, 2, 0], ![1, 1, -3, 1], ![2, -2, 1, -1]]

def raw819step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -3, 1], ![0, 1, -1]]

def raw819step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

def raw820 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 1, 2, 0], ![1, 2, -2, -1], ![2, -3, 0, 1]]

def raw820step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -2, 0], ![0, -1, 1]]

def raw820step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]

def raw821 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 1, 2, 0], ![2, -2, -1, 1], ![1, 1, -1, -1]]

def raw821step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![2, -1, -1], ![0, 1, -1]]

def raw821step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![-1, 2, -1], ![-2, 1, 1], ![0, -1, 1]]

def raw821step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

def raw822 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -3, 3], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]

def raw822step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]

def raw823 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -3, 3], ![1, 0, -1], ![2, 1, -3]]

def raw823step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]

def raw824 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -3, 3], ![1, 1, -2], ![2, 0, -2]]

def raw824step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]

def raw825 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]

def raw825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]

def raw825step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 0, 1], ![-2, 0, 2]]

def raw825step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def raw826 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

def raw826step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

def raw827 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def raw827step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]

def raw828 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![3, -1, -2]]

def raw828step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]

def raw829 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw829step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

def raw830 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]

def raw830step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]

def raw831 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]

def raw831step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 0, 1], ![-2, 0, 2]]

def raw831step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical250
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8001 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1]]

def raw8001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

def raw8002 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0]]

def raw8002step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]

def raw8002step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

def raw8003 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![0, 1, -1], ![0, 2, -2], ![0, 0, 0]]

def raw8003step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -3, 3], ![0, 1, -1], ![0, 2, -2]]

def raw8003step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw8005 : Matrix (Fin 2) (Fin 3) ℤ := ![![0, -3, 3], ![0, 3, -3]]

def raw8005step0 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]

def raw8006 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -3, 3], ![0, 3, -3], ![0, 0, 0]]

def raw8006step0 : Matrix (Fin 2) (Fin 3) ℤ := ![![0, -3, 3], ![0, 3, -3]]

def raw8006step1 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]

def raw8007 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -3, 3], ![0, 4, -4], ![0, -1, 1]]

def raw8007step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![4, -4], ![-1, 1]]

def raw8007step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]

def raw8008 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -2, 4], ![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw8008step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, 2, -4], ![1, 0, -1, 0], ![0, 0, -1, 1], ![0, -2, 0, 2], ![-1, 0, 0, 1]]

def raw8008step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw8009 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -2, 4], ![-1, 0, 1, 0], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw8009step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 2, 0], ![-2, 1, 1, 0], ![4, 0, -3, -1]]

def raw8009step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw8010 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -2, 4], ![-1, 0, 2, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw8010step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, 2, -4], ![1, 0, -2, 1], ![0, 0, -1, 1], ![0, -2, 0, 2], ![-1, 0, 1, 0]]

def raw8010step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw8011 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -2, 4], ![-1, 0, 2, -1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw8011step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, 2, -4], ![1, 0, -2, 1], ![0, -1, -1, 2], ![-1, -1, 1, 1]]

def raw8011step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw8012 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -2, 4], ![-1, 0, 3, -2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw8012step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, 2, -4], ![1, 0, -3, 2], ![0, -2, 0, 2], ![-1, 0, 1, 0]]

def raw8012step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, 0, 2], ![0, 2, 2, -4], ![1, 0, -3, 2]]

def raw8013 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -2, 4], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw8013step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, 2, -4], ![0, 0, -1, 1], ![1, 0, -1, 0], ![0, -2, 0, 2], ![-1, 0, 0, 1]]

def raw8013step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw8014 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -2, 4], ![0, 0, 1, -1], ![-1, 0, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw8014step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, 2, -4], ![0, 0, -1, 1], ![1, 0, -2, 1], ![0, -2, 0, 2], ![-1, 0, 1, 0]]

def raw8014step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw8015 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -2, 4], ![0, 0, 1, -1], ![-1, 2, 1, -2], ![1, 0, 0, -1]]

def raw8015step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 2, 0], ![-2, 1, 1, 0], ![4, -1, -2, -1]]

def raw8015step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw8016 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 2, 0, -1], ![1, 0, 0, -1]]

def raw8016step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, 2, -4], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -2, 0, 1], ![-1, 0, 0, 1]]

def raw8016step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw8017 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 2, 1, -2], ![1, 0, -1, 0]]

def raw8017step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, 2, -4], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -2, -1, 2], ![-1, 0, 1, 0]]

def raw8017step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -2, -1, 2]]

def raw8018 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![0, 0, 0, 0]]

def raw8018step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2]]

def raw8018step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw8019 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -2, 4], ![0, 0, 1, -1], ![0, 2, 1, -3], ![0, 0, 0, 0]]

def raw8019step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 0, 0], ![-2, 0, 2, 0], ![-2, 1, 1, 0], ![4, -1, -3, 0]]

def raw8019step1 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![-2, 1, 1, 0], ![4, -1, -3, 0]]

def raw8019step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![4, -1, -3]]

def raw8019step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![1, 1, -2]]

def raw8020 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -2, 4], ![0, 0, 2, -2], ![-1, 2, 1, -2], ![1, 0, -1, 0]]

def raw8020step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, 2, -4], ![0, 0, -2, 2], ![1, -2, -1, 2], ![-1, 0, 1, 0]]

def raw8020step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -2, -1, 2]]

def raw8021 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, -2, 4], ![0, 0, 2, -2], ![0, 2, 0, -2]]

def raw8021step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![2, 0, -2]]

def raw8022 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -2, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![0, 0, 0, 0]]

def raw8022step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, -2, 4], ![0, 0, 2, -2], ![0, 2, 0, -2]]

def raw8022step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![2, 0, -2]]

def raw8023 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, -2, 4], ![0, 0, 3, -3], ![0, 2, -1, -1]]

def raw8023step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, -1, -1]]

def raw8024 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, -2, 4], ![0, 1, 1, -2], ![0, 1, 1, -2]]

def raw8024step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![1, 1, -2], ![1, 1, -2]]

def raw8025 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -1, 3], ![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw8025step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, 1, -3], ![1, 0, -1, 0], ![0, 0, -1, 1], ![0, -2, 1, 1], ![-1, 0, 0, 1]]

def raw8025step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw8026 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -1, 3], ![-1, 0, 1, 0], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw8026step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 2, 0], ![-1, 1, 1, -1], ![3, 0, -3, 0]]

def raw8026step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, -1, 0, 0]]

def raw8027 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -1, 3], ![-1, 0, 2, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw8027step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, 1, -3], ![1, 0, -2, 1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 0, 0, 1]]

def raw8027step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw8028 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -1, 3], ![-1, 0, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw8028step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, 1, -3], ![1, 0, -2, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 0, 1, 0]]

def raw8028step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw8029 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -1, 3], ![-1, 0, 2, -1], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw8029step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, 1, -3], ![1, 0, -2, 1], ![0, -1, -1, 2], ![-1, -1, 2, 0]]

def raw8029step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -3, 1], ![1, 0, 1, -2]]

def raw8030 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -1, 3], ![-1, 0, 3, -2], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def raw8030step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, 1, -3], ![1, 0, -3, 2], ![0, -1, 2, -1], ![-1, -1, 0, 2]]

def raw8030step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, 0, -3, 2]]

def raw8031 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -1, 3], ![-1, 1, -1, 1], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def raw8031step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 2, 1, -3], ![1, 0, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical251
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8032 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -1, 3], ![-1, 1, -1, 1], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def raw8032step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 1, 1, 0], ![-1, -1, 3, -1], ![3, 1, -4, 0]]

def raw8032step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw8033 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -1, 3], ![-1, 1, 1, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw8033step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, 1, -3], ![1, -1, -1, 1], ![0, -1, -1, 2], ![-1, 0, 1, 0]]

def raw8033step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -1, 2], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw8034 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, -1, 3], ![-1, 2, 3, -4], ![1, 0, -2, 1]]

def raw8034step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 2, 0], ![-1, 3, -2], ![3, -4, 1]]

def raw8034step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 3, -4]]

def raw8035 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw8035step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, 1, -3], ![0, 0, -1, 1], ![1, 0, -1, 0], ![0, -2, 1, 1], ![-1, 0, 0, 1]]

def raw8035step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw8036 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw8036step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, 1, -3], ![0, 0, -1, 1], ![1, -1, -1, 1], ![0, -1, 0, 1], ![-1, 0, 1, 0]]

def raw8036step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw8037 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 0, 1, -1], ![-1, 2, 1, -2], ![1, 0, -1, 0]]

def raw8037step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 2, 0], ![-1, 1, 1, -1], ![3, -1, -2, 0]]

def raw8037step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 1, -1]]

def raw8038 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 2, -1, 0], ![1, 0, 0, -1]]

def raw8038step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -2, 3], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw8039 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![0, 0, 0, 0]]

def raw8039step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1]]

def raw8039step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw8040 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-1, 1, 1, -1], ![1, 0, -1, 0]]

def raw8040step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, 1, -3], ![0, 0, -1, 1], ![0, -1, 0, 1], ![1, -1, -1, 1], ![-1, 0, 1, 0]]

def raw8040step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw8041 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![0, 0, 0, 0]]

def raw8041step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1]]

def raw8041step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw8041step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw8042 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 0, 1, -1], ![0, 2, 1, -3], ![0, 0, -1, 1]]

def raw8042step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![2, 1, -3], ![0, -1, 1]]

def raw8042step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![2, 1, -3]]

def raw8043 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 0, 2, -2], ![-1, 1, -1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw8043step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw8044 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![-1, 1, 0, 0], ![1, 0, 0, -1]]

def raw8044step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, 1, -3], ![0, 0, -2, 2], ![0, -1, 1, 0], ![1, -1, 0, 0], ![-1, 0, 0, 1]]

def raw8044step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw8045 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![0, 0, 0, 0]]

def raw8045step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1]]

def raw8045step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw8046 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 0, 2, -2], ![0, 2, -1, -1]]

def raw8046step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]

def raw8047 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 0, 3, -3], ![0, 2, -2, 0]]

def raw8047step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![2, -2, 0]]

def raw8048 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 1, -2, 1], ![0, 1, 3, -4]]

def raw8048step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -2, 1], ![1, 3, -4]]

def raw8049 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 1, -1, 0], ![-1, 1, 2, -2], ![1, 0, 0, -1]]

def raw8049step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 1, 0], ![-1, -1, 2, 0], ![3, 0, -2, -1]]

def raw8049step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw8050 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![0, 0, 0, 0]]

def raw8050step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 0, 0], ![-2, 1, 1, 0], ![-1, -1, 2, 0], ![3, 0, -3, 0]]

def raw8050step1 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![-1, -1, 2, 0], ![3, 0, -3, 0]]

def raw8050step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![3, 0, -3]]

def raw8050step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -2, 1]]

def raw8051 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 1, 0, -1], ![-1, 1, 2, -2], ![1, 0, -1, 0]]

def raw8051step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 1, 0], ![-1, 0, 2, -1], ![3, -1, -2, 0]]

def raw8051step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw8052 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 1, 0, -1], ![0, 1, 1, -2], ![0, 0, 0, 0]]

def raw8052step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 1, 0, -1], ![0, 1, 1, -2]]

def raw8052step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, 0, -1], ![1, 1, -2]]

def raw8052step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![1, 1, -2]]

def raw8053 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 2, 2, -4], ![0, 0, -1, 1]]

def raw8053step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 0, 0], ![-2, 2, 0], ![-1, 2, -1], ![3, -4, 1]]

def raw8053step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 0, 0], ![2, -2, 0], ![1, -2, 1], ![-3, 4, -1]]

def raw8053step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -2, 0], ![1, -2, 1], ![-3, 4, -1]]

def raw8053step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![1, 1, -2]]

def raw8054 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 0, 2], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def raw8054step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def raw8055 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![-1, 0, -1, 2], ![0, 1, 3, -4], ![1, 1, -2, 0]]

def raw8055step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, 0, -2], ![1, 0, 1, -2], ![0, -1, -3, 4], ![-1, -1, 2, 0]]

def raw8055step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw8056 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![-1, 0, -1, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw8056step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -1, 0, 0]]

def raw8057 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![-1, 0, 0, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw8057step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 2, 0], ![0, 0, 2, -2], ![2, 1, -4, 1]]

def raw8057step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![2, 0, -2, 0], ![0, 0, -2, 2], ![-2, -1, 4, -1]]

def raw8057step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw8058 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 0, 2], ![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw8058step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw8059 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 0, 2], ![-1, 0, 2, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw8059step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw8060 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![-1, 0, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw8060step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw8061 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 0, 2], ![-1, 0, 3, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def raw8061step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw8062 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![-1, 1, -2, 2], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def raw8062step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 1, 1, 0], ![0, -2, 3, -1], ![2, 2, -4, 0]]

def raw8062step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw8063 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![-1, 1, -1, 1], ![0, 1, -2, 1], ![1, 0, 3, -4]]

def raw8063step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, 0, -2], ![1, -1, 1, -1], ![0, -1, 2, -1], ![-1, 0, -3, 4]]

def raw8063step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical252
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8064 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![-1, 1, -1, 1], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw8064step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 1, 1, 0], ![0, -1, 2, -1], ![2, 1, -3, 0]]

def raw8064step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw8065 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![-1, 1, -1, 1], ![0, 1, 3, -4], ![1, 0, -2, 1]]

def raw8065step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, 0, -2], ![1, -1, 1, -1], ![0, -1, -3, 4], ![-1, 0, 2, -1]]

def raw8065step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw8066 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![-1, 1, 1, -1], ![0, 1, 1, -2], ![1, 0, -2, 1]]

def raw8066step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, 0, -2], ![1, -1, -1, 1], ![0, -1, -1, 2], ![-1, 0, 2, -1]]

def raw8066step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw8067 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 0, 2], ![-1, 2, 2, -3], ![1, 0, -2, 1]]

def raw8067step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 2, 0], ![0, 2, -2], ![2, -3, 1]]

def raw8067step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![2, -2, 0], ![0, -2, 2], ![-2, 3, -1]]

def raw8067step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

def raw8068 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 0, 2], ![-1, 2, 3, -4], ![1, 0, -3, 2]]

def raw8068step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 2, 0], ![0, 3, -3], ![2, -4, 2]]

def raw8068step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![2, -2, 0], ![0, -3, 3], ![-2, 4, -2]]

def raw8068step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 3, -3], ![2, 0, -2]]

def raw8069 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, -2, 2], ![0, 2, 2, -4]]

def raw8069step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, 0, 2, -2], ![0, -2, -2, 4]]

def raw8069step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![-2, -2, 4]]

def raw8069step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![2, 0, -2]]

def raw8070 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, -1, 1], ![-1, 1, -1, 1], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def raw8070step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, 0, 1, -1], ![1, -1, 1, -1], ![0, -1, -3, 4], ![-1, 0, 1, 0]]

def raw8070step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw8071 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, -1, 1], ![-1, 2, 2, -3], ![1, 0, -1, 0]]

def raw8071step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 2, 0], ![0, -1, 2, -1], ![2, 1, -3, 0]]

def raw8071step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def raw8072 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, -1, 1], ![-1, 2, 3, -4], ![1, 0, -2, 1]]

def raw8072step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 2, 0], ![0, -1, 3, -2], ![2, 1, -4, 1]]

def raw8072step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![2, 0, -2, 0], ![0, 1, -3, 2], ![-2, -1, 4, -1]]

def raw8072step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, 2, -3]]

def raw8073 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-2, 0, 2, 0], ![2, 1, 1, -4]]

def raw8073step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![2, 0, -2, 0], ![-2, -1, -1, 4]]

def raw8073step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, 0, -2, 0]]

def raw8074 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 0, 2, 0], ![1, 2, 1, -4]]

def raw8074step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![2, 0, -2, 0], ![-1, -2, -1, 4]]

def raw8074step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, 0, 0, -2]]

def raw8075 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 1, 1, 0], ![1, 1, 2, -4]]

def raw8075step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def raw8076 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 2, 0, 0], ![1, 0, 3, -4]]

def raw8076step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![2, -2, 0, 0]]

def raw8077 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-1, 1, 3, -3], ![1, 0, -1, 0]]

def raw8077step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, 0, 1, -1], ![0, -1, 1, 0], ![1, -1, -3, 3], ![-1, 0, 1, 0]]

def raw8077step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, -2, 0], ![1, -1, 3, -3]]

def raw8078 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, 0, 1, 1], ![2, 0, 2, -4]]

def raw8078step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, 0, 1, -1], ![0, -1, 1, 0], ![0, -1, 1, 0], ![2, 0, -1, -1], ![-2, 0, -2, 4]]

def raw8078step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw8079 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![0, 0, -1, 1]]

def raw8079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4], ![0, -1, 1]]

def raw8079step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def raw8080 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![1, 1, 2, -4]]

def raw8080step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw8081 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![1, 0, 3, -4]]

def raw8081step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def raw8082 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![0, 0, -1, 1]]

def raw8082step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, 0, 1, -1], ![0, -2, -2, 4], ![0, 0, 1, -1]]

def raw8082step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-2, -2, 4], ![0, 1, -1]]

def raw8082step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw8083 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![0, 2, 2, -4]]

def raw8083step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![-1, 0, 1, 0], ![2, 0, -1, -1], ![0, -2, -2, 4]]

def raw8083step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def raw8084 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![0, 1, 3, -4]]

def raw8084step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def raw8085 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw8085step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw8086 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, 1, -1], ![-1, 2, 1, -2], ![1, 0, -2, 1]]

def raw8086step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, 0, -1, 1], ![1, -2, -1, 2], ![-1, 0, 2, -1]]

def raw8086step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -2, -1, 2]]

def raw8087 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 2, -2, 1], ![1, 0, 0, -1]]

def raw8087step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw8088 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![0, 0, 0, 0]]

def raw8088step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0]]

def raw8088step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

def raw8089 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![0, 0, -1, 1]]

def raw8089step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, 0, -2], ![0, -1, 1]]

def raw8089step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

def raw8090 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, 2, -2], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw8090step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 1, 0], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw8091 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![-1, 1, -1, 1], ![1, 0, 0, -1]]

def raw8091step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 1, 0], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw8092 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![0, 0, 0, 0]]

def raw8092step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0]]

def raw8092step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

def raw8092step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

def raw8093 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, 2, -2], ![0, 2, -2, 0]]

def raw8093step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]

def raw8094 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, 3, -3], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def raw8094step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, 0, -3, 3], ![1, -1, 1, -1], ![0, -1, 1, 0], ![-1, 0, 1, 0]]

def raw8094step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, -1, 1]]

def raw8095 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![-1, 1, -1, 1], ![1, 0, -1, 0]]

def raw8095step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, 0, -3, 3], ![0, -1, 1, 0], ![1, -1, 1, -1], ![-1, 0, 1, 0]]

def raw8095step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, -1, 1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical253
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8096 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![0, 0, -1, 1]]

def raw8096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1]]

def raw8096step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw8097 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, 3, -3], ![0, 2, -3, 1]]

def raw8097step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, 0, -3, 3], ![0, -2, 3, -1]]

def raw8097step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, -3, 3], ![-2, 3, -1]]

def raw8097step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![2, -2, 0]]

def raw8098 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 1, -3, 2], ![0, 1, 3, -4]]

def raw8098step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 0, 0], ![-2, 1, 1], ![0, -3, 3], ![2, 2, -4]]

def raw8098step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 0, 0], ![2, -1, -1], ![0, 3, -3], ![-2, -2, 4]]

def raw8098step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![0, 3, -3], ![-2, -2, 4]]

def raw8098step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, -1, -1]]

def raw8099 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 1, -2, 1], ![0, 1, 2, -3]]

def raw8099step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, -1, 2, -1], ![0, -1, -2, 3]]

def raw8099step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![-1, -2, 3]]

def raw8099step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]

def raw8100 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 1, -1, 0], ![-1, 1, 2, -2], ![1, 0, -1, 0]]

def raw8100step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 1, 0], ![0, -1, 2, -1], ![2, 0, -2, 0]]

def raw8100step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw8101 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![1, 0, 3, -4]]

def raw8101step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def raw8102 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![0, 0, -1, 1]]

def raw8102step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, -1, 1, 0], ![0, -1, -2, 3], ![0, 0, 1, -1]]

def raw8102step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![-1, -2, 3], ![0, 1, -1]]

def raw8102step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw8103 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 1, 3, -4]]

def raw8103step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def raw8104 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 1, 0, -1], ![-1, 1, 2, -2], ![1, 0, -2, 1]]

def raw8104step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, -1, 0, 1], ![1, -1, -2, 2], ![-1, 0, 2, -1]]

def raw8104step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw8105 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![0, 0, -1, 1]]

def raw8105step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, -1, 0, 1], ![0, -1, -1, 2], ![0, 0, 1, -1]]

def raw8105step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1]]

def raw8105step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

def raw8106 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 2, 1, -3], ![0, 0, -1, 1]]

def raw8106step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, -2, -1, 3], ![0, 0, 1, -1]]

def raw8106step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![-2, -1, 3], ![0, 1, -1]]

def raw8106step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![1, 0, -1]]

def raw8107 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 2, 2, -4], ![0, 0, -2, 2]]

def raw8107step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, -2, -2, 4], ![0, 0, 2, -2]]

def raw8107step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![-2, -2, 4], ![0, 2, -2]]

def raw8107step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![2, 0, -2]]

def raw8108 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 1, 1], ![-1, 0, -2, 3], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw8108step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw8109 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw8109step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw8110 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw8110step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw8111 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw8111step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw8112 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 1, 1], ![-1, 0, -1, 2], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw8112step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw8113 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, 0, 0, -1]]

def raw8113step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw8114 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![-1, 0, 1, 0], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw8114step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw8115 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![-1, 0, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw8115step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, -1, -1], ![1, 0, -1, 0], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-1, 0, 0, 1]]

def raw8115step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw8116 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![-1, 0, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw8116step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, -1, -1], ![1, 0, -1, 0], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 0, 1, 0]]

def raw8116step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw8117 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 1, 1], ![-1, 0, 1, 0], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw8117step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, -1, -1], ![1, 0, -1, 0], ![0, -2, 2, 0], ![-1, 0, 0, 1]]

def raw8117step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw8118 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 1, 1], ![-1, 1, -1, 1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw8118step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw8119 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -2, 2], ![-1, 2, 2, -3], ![1, 0, -1, 0]]

def raw8119step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 2, 0], ![1, -2, 2, -1], ![1, 2, -3, 0]]

def raw8119step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw8120 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -2, 2], ![0, 2, 1, -3]]

def raw8120step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, 2, -2], ![0, -2, -1, 3]]

def raw8120step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![0, 2, -2], ![-2, -1, 3]]

def raw8120step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]

def raw8121 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -2, 2], ![0, 2, 2, -4], ![0, 0, -1, 1]]

def raw8121step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, 2, -2], ![0, -2, -2, 4], ![0, 0, 1, -1]]

def raw8121step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 2, -2], ![-2, -2, 4], ![0, 1, -1]]

def raw8121step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def raw8122 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![-1, 0, -1, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw8122step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw8123 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![-1, 1, -1, 1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw8123step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw8124 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![-1, 1, -1, 1], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw8124step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![0, -1, -2, 3], ![-1, 0, 1, 0]]

def raw8124step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 3, -2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw8125 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![-1, 2, 1, -2], ![1, 0, -1, 0]]

def raw8125step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 2, 0], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw8125step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw8126 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 2, 2, -3], ![1, 0, -1, 0]]

def raw8126step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -2, -2, 3], ![-1, 0, 1, 0]]

def raw8126step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -2, 3, -2]]

def raw8127 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-2, 2, 0, 0], ![2, 0, 2, -4]]

def raw8127step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, -2, 0, 0], ![-2, 0, -2, 4]]

def raw8127step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -2, 0, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical254
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8128 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-2, 0, 1, 1], ![2, 1, 1, -4]]

def raw8128step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![2, 0, -1, -1], ![-2, -1, -1, 4]]

def raw8128step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw8129 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-2, 1, 0, 1], ![2, 0, 2, -4]]

def raw8129step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![2, -1, 0, -1], ![-2, 0, -2, 4]]

def raw8129step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -1, 0, -1]]

def raw8130 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![0, 0, -1, 1]]

def raw8130step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -2, -2, 4], ![0, 0, 1, -1]]

def raw8130step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, -2, 4], ![0, 1, -1]]

def raw8130step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw8131 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![1, 2, 1, -4]]

def raw8131step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![2, 0, -1, -1], ![-1, -2, -1, 4]]

def raw8131step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw8132 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![1, 1, 2, -4]]

def raw8132step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 1, 2, -4]]

def raw8133 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-1, 1, 1, -1], ![1, 0, 0, -1]]

def raw8133step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw8134 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-1, 1, 2, -2], ![1, 0, -1, 0]]

def raw8134step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw8135 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, 0, 0, 2], ![2, 0, 2, -4]]

def raw8135step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![0, -1, 1, 0], ![2, 0, 0, -2], ![-2, 0, -2, 4]]

def raw8135step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def raw8136 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![0, 0, 0, 0]]

def raw8136step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2]]

def raw8136step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]

def raw8137 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![0, 0, -1, 1]]

def raw8137step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![0, -1, 1]]

def raw8137step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]

def raw8138 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![1, 1, 2, -4]]

def raw8138step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw8139 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![0, 0, -1, 1]]

def raw8139step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, 1, -1], ![0, -2, -1, 3], ![0, 0, 1, -1]]

def raw8139step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-2, -1, 3], ![0, 1, -1]]

def raw8139step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw8140 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 2, 2, -4]]

def raw8140step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![-1, 0, 1, 0], ![2, 0, 0, -2], ![0, -2, -2, 4]]

def raw8140step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw8141 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![0, 2, -3, 1], ![1, 0, 0, -1]]

def raw8141step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw8142 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, 1, -1], ![-1, 1, -2, 2], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw8142step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw8143 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, 1, -1], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw8143step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw8144 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, 1, -1], ![-1, 1, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw8144step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw8145 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, 1, -1], ![-1, 2, -2, 1], ![1, 0, 0, -1]]

def raw8145step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 2, 0], ![1, 1, -2, 0], ![1, -1, 1, -1]]

def raw8145step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw8146 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 2, -3, 2], ![1, 0, 0, -1]]

def raw8146step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -2, 3, -2], ![-1, 0, 0, 1]]

def raw8146step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -2, 3, -2]]

def raw8147 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -3, 1], ![0, 0, 0, 0]]

def raw8147step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -2, 3, -1], ![0, 0, 0, 0]]

def raw8147step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -2, 3, -1]]

def raw8147step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 3, -1]]

def raw8147step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw8148 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![-1, 1, 0, 0], ![1, 0, 0, -1]]

def raw8148step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw8149 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![0, 0, 0, 0]]

def raw8149step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1]]

def raw8149step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

def raw8149step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]

def raw8150 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![-1, 1, -1, 1], ![1, 0, 0, -1]]

def raw8150step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw8151 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![-1, 1, 0, 0], ![1, 0, -1, 0]]

def raw8151step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, -1, 1], ![0, -1, 1, 0], ![1, -1, 0, 0], ![-1, 0, 1, 0]]

def raw8151step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw8152 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![0, 0, 0, 0]]

def raw8152step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, -1, 1], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 0, 0, 0]]

def raw8152step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, -1, 1], ![0, -1, 1, 0], ![0, -1, 1, 0]]

def raw8152step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0]]

def raw8152step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw8153 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![0, 0, -1, 1]]

def raw8153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![0, -1, 1]]

def raw8153step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8154 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![0, 0, 0, 0]]

def raw8154step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, -1, 1], ![0, -2, 2, 0], ![0, 0, 0, 0]]

def raw8154step1 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, -1, 1], ![0, -2, 2, 0]]

def raw8154step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![0, -1, 1], ![-2, 2, 0]]

def raw8154step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -1, 0]]

def raw8155 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, 2, -2], ![0, 2, -3, 1]]

def raw8155step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, -2, 2], ![0, -2, 3, -1]]

def raw8155step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![0, -2, 2], ![-2, 3, -1]]

def raw8155step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]

def raw8156 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 1, -3, 2], ![0, 1, 2, -3]]

def raw8156step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -3, 2], ![1, 2, -3]]

def raw8157 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 1, -2, 1], ![0, 1, 1, -2]]

def raw8157step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]

def raw8158 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 1, -1, 0], ![-1, 1, 1, -1], ![1, 0, -1, 0]]

def raw8158step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw8159 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![0, 0, -1, 1]]

def raw8159step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![0, -1, 1]]

def raw8159step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical255
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8160 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2]]

def raw8160step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

def raw8161 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1]]

def raw8161step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

def raw8162 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, -1, 2], ![0, 4, -4], ![1, -1, 0]]

def raw8162step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 4, -4], ![1, -1, 0]]

def raw8164 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1]]

def raw8164step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0]]

def raw8165 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0]]

def raw8165step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

def raw8166 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 2, -1], ![0, 2, -2], ![1, -2, 1]]

def raw8166step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

def raw8167 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 2, -1], ![1, 0, -1]]

def raw8167step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -1, 0]]

def raw8168 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 3, -2], ![0, -2, 2], ![1, 1, -2]]

def raw8168step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1]]

def raw8169 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 3, -2], ![1, -1, 0]]

def raw8169step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![1, 0, -1]]

def raw8170 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 4, -3], ![0, -2, 2], ![1, 0, -1]]

def raw8170step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0]]

def raw8171 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![0, 4, -4]]

def raw8171step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![4, -4]]

def raw8171step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![2, -2]]

def raw8172 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![-1, 4, -3], ![1, -1, 0]]

def raw8172step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

def raw8173 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![-2, 2, 0], ![2, 1, -3]]

def raw8173step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![-2, -1, 3]]

def raw8173step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def raw8174 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-2, 4, -2]]

def raw8174step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

def raw8175 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-3, 1, 2], ![3, 0, -3]]

def raw8175step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2], ![-3, 0, 3]]

def raw8175step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]

def raw8176 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 0, 2], ![2, 1, -3]]

def raw8176step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![-2, -1, 3]]

def raw8176step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

def raw8177 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![2, 0, -2]]

def raw8177step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![-2, 0, 2]]

def raw8177step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def raw8178 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![1, 3, -4]]

def raw8178step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 3, -4]]

def raw8179 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-3, 1, 2], ![2, 1, -3]]

def raw8179step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]

def raw8180 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-2, 0, 2], ![1, 2, -3]]

def raw8180step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

def raw8181 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, 2, 0]]

def raw8181step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

def raw8182 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2], ![-3, 2, 1]]

def raw8182step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]

def raw8183 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 4, -4], ![0, -1, 1]]

def raw8183step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![4, -4], ![-1, 1]]

def raw8183step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]

def raw8184 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-2, 0, 2], ![0, 4, -4]]

def raw8184step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0], ![1, 0, -1]]

def raw8185 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1], ![0, 3, -3]]

def raw8185step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw8186 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-3, 1, 2], ![1, 2, -3]]

def raw8186step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]

def raw8187 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-2, 0, 2], ![0, 3, -3]]

def raw8187step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def raw8188 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![-1, 4, -3]]

def raw8188step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 4, -3], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

def raw8189 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![-3, 3, 0]]

def raw8189step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![3, -3, 0]]

def raw8189step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]

def raw8191 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1]]

def raw8191step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical256
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8192 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0]]

def raw8192step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

def raw8193 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![-1, -1, 2], ![3, 0, -3]]

def raw8193step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2], ![-3, 0, 3]]

def raw8193step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

def raw8195 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0]]

def raw8195step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![0, 1, -1]]

def raw8195step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw8197 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-3, 0, 3], ![2, 1, -3]]

def raw8197step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

def raw8198 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-2, -1, 3], ![1, 2, -3]]

def raw8198step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw8199 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1]]

def raw8199step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8200 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![-3, 1, 2]]

def raw8200step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

def raw8201 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, 0, 2]]

def raw8201step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw8202 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![-2, -1, 3]]

def raw8202step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw8203 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![-3, 1, 2]]

def raw8203step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def raw8204 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![0, -1, 1]]

def raw8204step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![2, -2], ![-1, 1]]

def raw8204step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw8205 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, 3, -3]]

def raw8205step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw8206 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-3, 0, 3], ![1, 2, -3]]

def raw8206step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

def raw8207 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, -1, 3], ![0, 3, -3]]

def raw8207step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw8208 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-1, -1, 2], ![-1, 3, -2]]

def raw8208step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw8209 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-3, 2, 1]]

def raw8209step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw8210 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![-3, 1, 2]]

def raw8210step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw8211 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![-2, 0, 2], ![-1, 2, -1], ![2, -1, -1]]

def raw8211step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def raw8212 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![-2, 2, 0], ![-1, -1, 2], ![2, 0, -2]]

def raw8212step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

def raw8213 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![-1, 2, -1], ![2, 0, -2], ![-2, -1, 3]]

def raw8213step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]

def raw8214 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, -2, 3], ![-1, 3, -2]]

def raw8214step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw8215 : Matrix (Fin 2) (Fin 3) ℤ := ![![0, -2, 2], ![0, 2, -2]]

def raw8215step0 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

def raw8216 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -2, 2], ![0, 2, -2], ![0, 0, 0]]

def raw8216step0 : Matrix (Fin 2) (Fin 3) ℤ := ![![0, -2, 2], ![0, 2, -2]]

def raw8216step1 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

def raw8217 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -2, 2], ![0, 3, -3], ![0, -1, 1]]

def raw8217step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![3, -3], ![-1, 1]]

def raw8217step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw8218 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![-2, 0, 2], ![-1, 4, -3]]

def raw8218step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw8219 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-2, 1, 1], ![-1, 2, -1]]

def raw8219step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]

def raw8220 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![-2, 4, -2]]

def raw8220step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw8221 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-4, 1, 0, 3], ![4, 1, -2, -3]]

def raw8221step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![-2, 1, 1], ![2, 0, -2], ![0, 3, -3]]

def raw8221step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -1, -1], ![-2, 0, 2], ![0, -3, 3]]

def raw8221step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 4, -4], ![2, -1, -1]]

def raw8222 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-4, 2, -1, 3], ![4, 0, -1, -3]]

def raw8222step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![-2, 2, 0], ![2, -1, -1], ![0, 3, -3]]

def raw8222step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 4, -4], ![2, -1, -1]]

def raw8223 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-4, 2, 0, 2], ![4, 0, -2, -2]]

def raw8223step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![-2, 2, 0], ![2, 0, -2], ![0, 2, -2]]

def raw8223step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 4, -4], ![2, -2, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical257
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8224 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-4, 3, -1, 2], ![4, -1, -1, -2]]

def raw8224step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![-2, 3, -1], ![2, -1, -1], ![0, 2, -2]]

def raw8224step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 4, -4], ![2, -1, -1]]

def raw8225 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-3, 1, -1, 3], ![3, 1, -1, -3]]

def raw8225step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-2, 1, 1], ![2, -1, -1], ![0, 3, -3]]

def raw8225step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 3, -3], ![2, -1, -1]]

def raw8226 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-3, 1, 0, 2], ![3, 1, -2, -2]]

def raw8226step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-2, 1, 1], ![2, 0, -2], ![0, 2, -2]]

def raw8226step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-2, 0, 2], ![0, -2, 2]]

def raw8226step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

def raw8227 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-3, 2, -1, 2], ![3, 0, -1, -2]]

def raw8227step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-2, 2, 0], ![2, -1, -1], ![0, 2, -2]]

def raw8227step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

def raw8228 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-3, 2, 0, 1], ![3, 0, -2, -1]]

def raw8228step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-2, 2, 0], ![2, 0, -2], ![0, 1, -1]]

def raw8228step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![2, -2, 0]]

def raw8229 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-3, 2, 2, -1], ![3, 0, -4, 1]]

def raw8229step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-2, 2, 0], ![2, 2, -4], ![0, -1, 1]]

def raw8229step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-2, -2, 4], ![0, 1, -1]]

def raw8229step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 3, -3], ![2, -2, 0]]

def raw8230 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-3, 3, -1, 1], ![3, -1, -1, -1]]

def raw8230step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-2, 3, -1], ![2, -1, -1], ![0, 1, -1]]

def raw8230step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![2, -1, -1]]

def raw8231 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-3, 4, 0, -1], ![3, -2, -2, 1]]

def raw8231step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-2, 4, -2], ![2, 0, -2], ![0, -1, 1]]

def raw8231step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 3, -3], ![2, -2, 0]]

def raw8232 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-2, 0, 3, -1], ![2, 2, -5, 1]]

def raw8232step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-2, 0, 2], ![2, 3, -5], ![0, -1, 1]]

def raw8232step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-2, -3, 5], ![0, 1, -1]]

def raw8232step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

def raw8233 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-2, 1, -1, 2], ![2, 1, -1, -2]]

def raw8233step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-2, 1, 1], ![2, -1, -1], ![0, 2, -2]]

def raw8233step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]

def raw8234 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-2, 1, 2, -1], ![2, 1, -4, 1]]

def raw8234step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-2, 1, 1], ![2, 2, -4], ![0, -1, 1]]

def raw8234step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, -2, 4], ![0, 1, -1]]

def raw8234step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def raw8235 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-2, 2, -1, 1], ![2, 0, -1, -1]]

def raw8235step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-2, 2, 0], ![2, -1, -1], ![0, 1, -1]]

def raw8235step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

def raw8236 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-2, 2, 1, -1], ![2, 0, -3, 1]]

def raw8236step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-2, 2, 0], ![2, 1, -3], ![0, -1, 1]]

def raw8236step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![2, -2, 0], ![-2, -1, 3], ![0, 1, -1]]

def raw8236step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def raw8237 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-2, 2, 2, -2], ![2, 0, -4, 2]]

def raw8237step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-2, 2, 0], ![2, 2, -4], ![0, -2, 2]]

def raw8237step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![2, -2, 0], ![-2, -2, 4], ![0, 2, -2]]

def raw8237step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 2, -2], ![2, -2, 0]]

def raw8238 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-2, 4, 0, -2], ![2, -2, -2, 2]]

def raw8238step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-2, 4, -2], ![2, 0, -2], ![0, -2, 2]]

def raw8238step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 2, -2], ![2, -2, 0]]

def raw8239 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw8239step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw8240 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw8240step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw8241 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-1, 0, -1, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw8241step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw8242 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-1, 0, -1, 2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw8242step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw8243 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-1, 0, 1, 0], ![0, 1, -3, 2], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw8243step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw8244 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-1, 0, 3, -2], ![1, 2, -5, 2]]

def raw8244step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![2, 3, -5], ![0, -2, 2]]

def raw8244step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![2, 0, -2], ![-2, -3, 5], ![0, 2, -2]]

def raw8244step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

def raw8245 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-1, 1, 2, -2], ![1, 1, -4, 2]]

def raw8245step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 1, 1], ![2, 2, -4], ![0, -2, 2]]

def raw8245step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![2, -1, -1], ![-2, -2, 4], ![0, 2, -2]]

def raw8245step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def raw8246 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-1, 2, 1, -2], ![1, 0, -3, 2]]

def raw8246step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 2, 0], ![2, 1, -3], ![0, -2, 2]]

def raw8246step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![2, -2, 0], ![-2, -1, 3], ![0, 2, -2]]

def raw8246step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def raw8247 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![0, 0, -2, 2], ![0, 2, 0, -2]]

def raw8247step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![2, 0, -2]]

def raw8247step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]

def raw8248 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 2, 0], ![0, 0, -1, 1], ![-1, 0, -1, 2], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw8248step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw8249 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 2, 0], ![0, 0, -1, 1], ![-1, 1, -1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw8249step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw8250 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 2, 0], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw8250step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def raw8251 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 2, 0], ![0, 0, -1, 1], ![-1, 2, 0, -1], ![1, 0, -1, 0]]

def raw8251step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def raw8252 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 2, 1, -2], ![1, 0, -1, 0]]

def raw8252step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw8253 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![0, 0, -1, 1]]

def raw8253step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, -2, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -2, -1, 3], ![0, 0, 1, -1]]

def raw8253step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![0, 1, -1], ![0, 1, -1], ![-2, -1, 3], ![0, 1, -1]]

def raw8253step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

def raw8254 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-1, 1, 0, 0], ![1, 0, 0, -1]]

def raw8254step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw8255 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![0, 0, 0, 0]]

def raw8255step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1]]

def raw8255step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]

def raw8255step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical258
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8256 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 1, 0, -1], ![-1, 1, 0, 0], ![1, 0, -1, 0]]

def raw8256step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def raw8257 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![0, 0, -1, 1]]

def raw8257step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]

def raw8257step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]

def raw8258 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 2, 0, -2], ![0, 0, -1, 1]]

def raw8258step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![0, -1, 1]]

def raw8258step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

def raw8259 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 2, 0], ![0, 0, 1, -1], ![-1, 1, -3, 3], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw8259step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, -2, 0], ![0, 0, -1, 1], ![1, -1, 3, -3], ![0, -1, 0, 1], ![-1, 0, 0, 1]]

def raw8259step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, -2, 0], ![1, -1, 3, -3]]

def raw8260 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 2, 0], ![0, 0, 1, -1], ![0, 1, -3, 2], ![-1, 1, 0, 0], ![1, 0, 0, -1]]

def raw8260step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, -2, 0], ![0, 0, -1, 1], ![0, -1, 3, -2], ![1, -1, 0, 0], ![-1, 0, 0, 1]]

def raw8260step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -2, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw8261 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 2, 0], ![0, 0, 1, -1], ![0, 1, -3, 2], ![0, 1, 0, -1], ![0, 0, 0, 0]]

def raw8261step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, -2, 0], ![0, 0, -1, 1], ![0, -1, 3, -2], ![0, -1, 0, 1], ![0, 0, 0, 0]]

def raw8261step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, -2, 0], ![0, 0, -1, 1], ![0, -1, 3, -2], ![0, -1, 0, 1]]

def raw8261step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-1, 3, -2], ![-1, 0, 1]]

def raw8261step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw8262 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![1, -1, 1, -1], ![-1, 3, -3, 1]]

def raw8262step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![2, 1, -3], ![0, -1, 1]]

def raw8262step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![2, 1, -3]]

def raw8263 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![1, 0, 0, -1], ![-1, 2, -2, 1]]

def raw8263step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![2, 0, -2], ![0, -1, 1]]

def raw8263step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

def raw8264 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![1, 0, 1, -2], ![-1, 2, -3, 2]]

def raw8264step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![2, 1, -3], ![0, -2, 2]]

def raw8264step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![2, 0, -2], ![-2, -1, 3], ![0, 2, -2]]

def raw8264step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

def raw8265 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![1, 1, 1, -3], ![-1, 1, -3, 3]]

def raw8265step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 1, 1], ![2, 1, -3], ![0, -3, 3]]

def raw8265step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![2, -1, -1], ![-2, -1, 3], ![0, 3, -3]]

def raw8265step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![2, -1, -1]]

def raw8266 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![2, -1, 1, -2], ![-2, 3, -3, 2]]

def raw8266step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![-2, -1, 3], ![2, 1, -3], ![0, -2, 2]]

def raw8266step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![2, 1, -3]]

def raw8267 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![2, 0, 0, -2], ![-2, 2, -2, 2]]

def raw8267step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![-2, 0, 2], ![2, 0, -2], ![0, -2, 2]]

def raw8267step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![2, 0, -2]]

def raw8268 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![2, 0, 1, -3], ![-2, 2, -3, 3]]

def raw8268step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![-2, 0, 2], ![2, 1, -3], ![0, -3, 3]]

def raw8268step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![2, 0, -2], ![-2, -1, 3], ![0, 3, -3]]

def raw8268step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![2, 0, -2]]

def raw8269 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 3, -1], ![-1, 1, -3, 3], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw8269step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 1, 1, 0], ![3, -3, 0, 0], ![-1, 3, -1, -1]]

def raw8269step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw8270 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 3, -1], ![0, 1, -3, 2], ![-1, 1, 0, 0], ![1, 0, 0, -1]]

def raw8270step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 1, 0], ![3, -3, 0, 0], ![-1, 2, 0, -1]]

def raw8270step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -1, 0, 0]]

def raw8271 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 3, -1], ![0, 1, -3, 2], ![0, 1, 0, -1], ![0, 0, 0, 0]]

def raw8271step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 0, 0], ![-2, 1, 1, 0], ![3, -3, 0, 0], ![-1, 2, -1, 0]]

def raw8271step1 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![3, -3, 0, 0], ![-1, 2, -1, 0]]

def raw8271step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![3, -3, 0], ![-1, 2, -1]]

def raw8271step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -2, 1]]

def raw8272 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, -3, 4], ![-1, 0, 2, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw8272step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw8273 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -3, 4], ![-1, 0, 2, -1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw8273step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw8274 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -3, 4], ![-1, 0, 3, -2], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw8274step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![-3, 3, 0, 0], ![4, -2, -2, 0]]

def raw8274step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, 0, -2, 1], ![3, -3, 0, 0], ![-4, 2, 2, 0]]

def raw8274step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -3, 3], ![0, 2, 2, -4], ![1, -2, 0, 1]]

def raw8275 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -3, 4], ![-1, 1, 1, -1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw8275step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 3, -4], ![1, -1, -1, 1], ![0, -1, -1, 2], ![-1, 1, -1, 1]]

def raw8275step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def raw8276 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -3, 4], ![-1, 1, 1, -1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw8276step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 3, -4], ![1, -1, -1, 1], ![0, -1, -2, 3], ![-1, 1, 0, 0]]

def raw8276step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, -1, -2, 3], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def raw8277 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -3, 4], ![-1, 1, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw8277step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, 1, -1], ![-3, 2, 1, 0], ![4, -2, -2, 0]]

def raw8277step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, -1, -1, 1], ![3, -2, -1, 0], ![-4, 2, 2, 0]]

def raw8277step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -2, 3], ![0, 2, 2, -4], ![1, -1, -1, 1]]

def raw8278 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, -3, 4], ![0, -1, 2, -1], ![0, 2, 1, -3]]

def raw8278step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 3, -4], ![0, 1, -2, 1], ![0, -2, -1, 3]]

def raw8278step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![1, -2, 1], ![-2, -1, 3]]

def raw8278step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -2, 1], ![1, 3, -4]]

def raw8279 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, -3, 4], ![0, -1, 3, -2], ![0, 2, 0, -2]]

def raw8279step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 0, 0], ![-1, -1, 2], ![-3, 3, 0], ![4, -2, -2]]

def raw8279step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![4, -2, -2]]

def raw8279step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, -1, -1]]

def raw8280 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, -3, 4], ![0, 0, 1, -1], ![-1, 0, 2, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw8280step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw8281 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -3, 4], ![0, 0, 1, -1], ![-1, 2, 1, -2], ![1, -1, 1, -1]]

def raw8281step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![-3, 1, 1, 1], ![4, -1, -2, -1]]

def raw8281step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 1, 1, -3]]

def raw8282 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 2, 1, -2], ![1, -1, 0, 0]]

def raw8282step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 3, -4], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -2, -1, 2], ![-1, 1, 0, 0]]

def raw8282step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -2, -1, 2]]

def raw8283 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![0, -1, 1, 0]]

def raw8283step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 3, -4], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -2, 0, 2], ![0, 1, -1, 0]]

def raw8283step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2], ![1, -1, 0]]

def raw8283step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def raw8284 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![0, -1, 2, -1]]

def raw8284step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 3, -4], ![0, 0, -1, 1], ![0, -2, 0, 2], ![0, 1, -2, 1]]

def raw8284step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![-2, 0, 2], ![1, -2, 1]]

def raw8284step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -2, 1], ![1, 3, -4]]

def raw8285 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -3, 4], ![0, 0, 2, -2], ![-1, 2, 1, -2], ![1, -1, 0, 0]]

def raw8285step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![-3, 2, 1, 0], ![4, -2, -2, 0]]

def raw8285step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, 0, -2, 1], ![3, -2, -1, 0], ![-4, 2, 2, 0]]

def raw8285step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, -1, 3], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw8286 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, -3, 4], ![0, 0, 2, -2], ![0, 1, 1, -2]]

def raw8286step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![1, 1, -2]]

def raw8287 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -3, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![0, -1, 1, 0]]

def raw8287step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 3, -4], ![0, 0, -2, 2], ![0, -2, 0, 2], ![0, 1, -1, 0]]

def raw8287step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, -2, 2], ![-2, 0, 2], ![1, -1, 0]]

def raw8287step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical259
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8288 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -3, 4], ![0, 1, 1, -2], ![-1, 1, 2, -2], ![1, -1, 0, 0]]

def raw8288step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 1, -1], ![-3, 1, 2, 0], ![4, -2, -2, 0]]

def raw8288step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, -1, -1, 1], ![3, -1, -2, 0], ![-4, 2, 2, 0]]

def raw8288step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -2, 3], ![0, 2, 2, -4], ![1, -1, -1, 1]]

def raw8289 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -3, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![0, -1, 1, 0]]

def raw8289step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![1, 1, -2], ![1, 1, -2], ![-1, 1, 0]]

def raw8289step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2]]

def raw8290 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, -2, 3], ![-1, 0, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0]]

def raw8290step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 2, -3], ![1, 0, -2, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 1, 0, 0]]

def raw8290step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -2, 0, 1]]

def raw8291 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -2, 3], ![-1, 0, 2, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw8291step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 2, -3], ![1, 0, -2, 1], ![0, -2, 0, 2], ![-1, 1, 0, 0]]

def raw8291step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -2, 0, 1]]

def raw8292 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -2, 3], ![-1, 1, -1, 1], ![0, 1, 1, -2], ![1, -1, 2, -2]]

def raw8292step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 2, -3], ![1, -1, 1, -1], ![0, -1, -1, 2], ![-1, 1, -2, 2]]

def raw8292step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, -1, 1, -1]]

def raw8293 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -2, 3], ![-1, 1, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw8293step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 2, -3], ![1, -1, -1, 1], ![0, -1, -1, 2], ![-1, 1, 0, 0]]

def raw8293step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -1, 2], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw8294 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, -2, 3], ![-1, 2, 3, -4], ![1, -1, -1, 1]]

def raw8294step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 2, -1], ![-2, 3, -1], ![3, -4, 1]]

def raw8294step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![1, -2, 1], ![2, -3, 1], ![-3, 4, -1]]

def raw8294step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 0, 1], ![1, 1, -2], ![1, 2, -3]]

def raw8295 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, -2, 3], ![0, -1, 2, -1], ![0, 2, 0, -2]]

def raw8295step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![2, 0, -2]]

def raw8295step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]

def raw8296 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, -2, 3], ![0, -1, 3, -2], ![0, 2, -1, -1]]

def raw8296step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 2, -3], ![0, 1, -3, 2], ![0, -2, 1, 1]]

def raw8296step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![1, -3, 2], ![-2, 1, 1]]

def raw8296step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -3, 2], ![1, 2, -3]]

def raw8297 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, -2, 3], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0]]

def raw8297step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 2, -3], ![0, 0, -1, 1], ![1, -1, -1, 1], ![0, -1, 0, 1], ![-1, 1, 0, 0]]

def raw8297step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw8298 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -2, 3], ![0, 0, 1, -1], ![-1, 2, 1, -2], ![1, -1, 0, 0]]

def raw8298step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![-2, 1, 1, 0], ![3, -1, -2, 0]]

def raw8298step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw8299 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, -2, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-1, 1, 1, -1], ![1, -1, 0, 0]]

def raw8299step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 2, -3], ![0, 0, -1, 1], ![0, -1, 0, 1], ![1, -1, -1, 1], ![-1, 1, 0, 0]]

def raw8299step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw8300 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, -2, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![0, -1, 1, 0]]

def raw8300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0]]

def raw8300step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8301 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -2, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![0, -1, 1, 0]]

def raw8301step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![2, 0, -2], ![-1, 1, 0]]

def raw8301step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw8302 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, -2, 3], ![0, 0, 4, -4], ![0, 1, -2, 1]]

def raw8302step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 4, -4], ![1, -2, 1]]

def raw8303 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -2, 3], ![0, 1, 0, -1], ![-1, 1, 2, -2], ![1, -1, 0, 0]]

def raw8303step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 1, -1], ![-2, 0, 2, 0], ![3, -1, -2, 0]]

def raw8303step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 1, -1]]

def raw8304 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -2, 3], ![0, 1, 0, -1], ![0, 1, 1, -2], ![0, -1, 1, 0]]

def raw8304step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![1, 0, -1], ![1, 1, -2], ![-1, 1, 0]]

def raw8304step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw8305 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, -2, 3], ![0, 1, 3, -4], ![0, 0, -1, 1]]

def raw8305step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 2, -3], ![0, -1, -3, 4], ![0, 0, 1, -1]]

def raw8305step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![-1, -3, 4], ![0, 1, -1]]

def raw8305step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![1, 2, -3]]

def raw8306 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, -2, 3], ![0, 2, 2, -4], ![0, -1, 0, 1]]

def raw8306step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 2, -1], ![-2, 2, 0], ![3, -4, 1]]

def raw8306step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 0, 0], ![1, -2, 1], ![2, -2, 0], ![-3, 4, -1]]

def raw8306step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -2, 1], ![2, -2, 0], ![-3, 4, -1]]

def raw8306step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![1, 1, -2]]

def raw8307 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -1, 2], ![-1, -1, 0, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw8307step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw8308 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -1, 2], ![-1, -1, 1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw8308step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw8309 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -1, 2], ![-1, 1, 3, -3], ![0, 1, -2, 1], ![1, -1, 0, 0]]

def raw8309step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, 1, -1], ![-1, 3, -2, 0], ![2, -3, 1, 0]]

def raw8309step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw8310 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, -1, 2], ![-1, 2, 2, -3], ![1, -1, -1, 1]]

def raw8310step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 2, -1], ![-1, 2, -1], ![2, -3, 1]]

def raw8310step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![-2, 3, -1]]

def raw8310step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]

def raw8311 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, -1, -1, 2], ![0, 2, 2, -4]]

def raw8311step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 1, -2], ![0, 1, 1, -2], ![0, -2, -2, 4]]

def raw8311step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-2, -2, 4]]

def raw8311step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![1, 1, -2], ![1, 1, -2]]

def raw8312 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, -1, 0, 1], ![-1, 2, 2, -3], ![1, 0, -1, 0]]

def raw8312step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 2, 0], ![-1, 0, 2, -1], ![2, 1, -3, 0]]

def raw8312step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, 1, -2, 0], ![1, 0, -2, 1], ![-2, -1, 3, 0]]

def raw8312step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw8313 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, -1, 0, 1], ![0, 2, 2, -4], ![0, 0, -1, 1]]

def raw8313step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 1, -2], ![0, 1, 0, -1], ![0, -2, -2, 4], ![0, 0, 1, -1]]

def raw8313step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-2, -2, 4], ![0, 1, -1]]

def raw8313step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw8314 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, -1, 1, 0], ![-1, 2, 1, -2], ![1, 0, -1, 0]]

def raw8314step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 2, 0], ![-1, 1, 1, -1], ![2, 0, -2, 0]]

def raw8314step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1]]

def raw8315 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, -1, 1, 0], ![0, 2, 1, -3], ![0, 0, -1, 1]]

def raw8315step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 1, -2], ![0, 1, -1, 0], ![0, -2, -1, 3], ![0, 0, 1, -1]]

def raw8315step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-2, -1, 3], ![0, 1, -1]]

def raw8315step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw8316 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, -1, 2, -1], ![0, 2, -1, -1]]

def raw8316step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 1, -2], ![0, 1, -2, 1], ![0, -2, 1, 1]]

def raw8316step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 1, -2], ![1, -2, 1], ![-2, 1, 1]]

def raw8316step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]

def raw8317 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, -1, 3, -2], ![0, 2, -2, 0]]

def raw8317step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![2, -2, 0]]

def raw8317step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]

def raw8318 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-2, 0, 2, 0], ![1, 2, 1, -4]]

def raw8318step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 1, -2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![2, 0, -2, 0], ![-1, -2, -1, 4]]

def raw8318step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw8319 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-2, 1, 1, 0], ![1, 1, 2, -4]]

def raw8319step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 2, -4]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw832 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]

def raw832step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

def raw833 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]

def raw833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

def raw834 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]

def raw834step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]

def raw835 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

def raw835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]

def raw835step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw836 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]

def raw836step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]

def raw836step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

def raw837 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]

def raw837step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

def raw838 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![2, 1, -3]]

def raw838step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]

def raw839 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]

def raw839step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

def raw840 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 1, -2], ![2, -3, 1]]

def raw840step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -3, 2], ![1, 2, -3]]

def raw841 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, 2, 1], ![3, -2, -1]]

def raw841step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]

def raw841step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw842 : Matrix (Fin 2) (Fin 4) ℤ := ![![-3, 2, 2, -1], ![3, -2, -2, 1]]

def raw842step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![2, -2], ![-1, 1]]

def raw842step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]

def raw843 : Matrix (Fin 2) (Fin 4) ℤ := ![![-3, 2, 3, -2], ![3, -2, -3, 2]]

def raw843step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![3, -3], ![-2, 2]]

def raw843step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![2, -2], ![3, -3]]

def raw844 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![0, 0], ![1, -1], ![1, -1], ![3, -3]]

def raw844step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![3, -3]]

def raw845 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![0, 0], ![1, -1], ![2, -2], ![2, -2]]

def raw845step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![2, -2], ![2, -2]]

def raw846 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![0, 0], ![2, -2], ![3, -3]]

def raw846step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![2, -2], ![3, -3]]

def raw847 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]

def raw848 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![3, -3]]

def raw849 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![2, -2], ![2, -2]]

def raw850 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![4, -4]]

def raw850step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![2, -2], ![3, -3]]

def raw851 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![2, -2], ![1, -1], ![2, -2]]

def raw851step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![2, -2], ![2, -2]]

def raw852 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![2, -2], ![3, -3]]

def raw853 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![3, -3], ![2, -2]]

def raw853step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![2, -2], ![3, -3]]

def raw854 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![3, -3]]

def raw855 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]

def raw856 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![2, -2], ![3, -3]]

def raw856step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![3, -3]]

def raw857 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![0, 0], ![0, 0], ![1, -1], ![3, -3]]

def raw857step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![0, 0], ![1, -1], ![3, -3]]

def raw857step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]

def raw858 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![0, 0], ![0, 0], ![2, -2], ![2, -2]]

def raw858step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![0, 0], ![2, -2], ![2, -2]]

def raw858step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]

def raw859 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![0, 0], ![1, -1], ![1, -1], ![2, -2]]

def raw859step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]

def raw860 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![0, 0], ![1, -1], ![3, -3]]

def raw860step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]

def raw861 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![0, 0], ![2, -2], ![2, -2]]

def raw861step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]

def raw863 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![0, 0], ![1, -1], ![2, -2]]

def raw863step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical260
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8320 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-2, 2, 0, 0], ![1, 0, 3, -4]]

def raw8320step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 1, -2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![2, -2, 0, 0], ![-1, 0, -3, 4]]

def raw8320step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw8321 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, -1, 1, 2], ![2, 1, 0, -3]]

def raw8321step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 1, -2], ![0, 0, 1, -1], ![0, 0, -1, 1], ![0, -1, 0, 1], ![2, 1, -1, -2], ![-2, -1, 0, 3]]

def raw8321step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, 1, -1, -2]]

def raw8322 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -1, 1, -2]]

def raw8322step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 1, -2], ![0, 0, 1, -1], ![0, 0, -1, 1], ![0, -1, 0, 1], ![2, -1, 0, -1], ![-2, 1, -1, 2]]

def raw8322step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw8323 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 2, 1, -1]]

def raw8323step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 1, -2], ![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![2, -2, -1, 1]]

def raw8323step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw8324 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, 0, 1, 1], ![1, 1, 2, -4]]

def raw8324step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw8325 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, 1, 0, 1], ![1, 0, 3, -4]]

def raw8325step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw8326 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, 3, -2]]

def raw8326step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw8327 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, 2, -1]]

def raw8327step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 1, -2], ![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![2, -1, -2, 1]]

def raw8327step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw8328 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![1, -1, 2, -2]]

def raw8328step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 1, -2], ![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 0, 0, 1], ![2, -1, 0, -1], ![-1, 1, -2, 2]]

def raw8328step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw8329 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![0, 2, 2, -4]]

def raw8329step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 1, -2], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![2, 0, -1, -1], ![0, -2, -2, 4]]

def raw8329step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw8330 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![0, 1, 3, -4]]

def raw8330step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw8331 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![-2, -1, 0, 3], ![2, 1, 0, -3]]

def raw8331step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, -1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, 0, -3]]

def raw8332 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 2, 0, 0]]

def raw8332step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 1, -2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![2, -2, 0, 0]]

def raw8332step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw8333 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, 1, 0]]

def raw8333step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw8334 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 1, 1, 0]]

def raw8334step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw8335 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 2, 1, -3]]

def raw8335step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 1, -2], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![2, 0, 0, -2], ![0, -2, -1, 3]]

def raw8335step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw8336 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1], ![0, -1, 2, -1], ![-2, 2, -2, 2]]

def raw8336step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, -1, 2], ![0, -1, 2, -1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw8337 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, 3, -3], ![0, 1, -2, 1]]

def raw8337step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -2, 1]]

def raw8338 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, 4, -4], ![0, 1, -3, 2]]

def raw8338step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 1, -2], ![0, 0, -4, 4], ![0, -1, 3, -2]]

def raw8338step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 1, -2], ![0, -4, 4], ![-1, 3, -2]]

def raw8338step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 4, -4], ![1, -2, 1]]

def raw8339 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![1, 0, 3, -4]]

def raw8339step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw8340 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 0, 2, 0]]

def raw8340step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 1, -2], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![2, 0, -2, 0]]

def raw8340step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw8341 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 1, 3, -4]]

def raw8341step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw8342 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 2, 1, -3], ![0, -1, 0, 1]]

def raw8342step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 1, -2], ![0, -2, -1, 3], ![0, 1, 0, -1]]

def raw8342step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 1, -2], ![-2, -1, 3], ![1, 0, -1]]

def raw8342step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![1, 1, -2]]

def raw8343 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw8343step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw8344 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw8344step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw8345 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 0, 2], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw8345step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 2, 0], ![0, 0, 2, -2], ![1, 2, -4, 1]]

def raw8345step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, 1, -2, 0], ![0, 0, -2, 2], ![-1, -2, 4, -1]]

def raw8345step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

def raw8346 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw8346step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw8347 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw8347step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw8348 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-1, 0, -1, 2], ![1, 1, 2, -4]]

def raw8348step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, 1, -1, -1], ![0, -1, 1, 0], ![-1, 0, 1, 0], ![1, 0, 1, -2], ![-1, -1, -2, 4]]

def raw8348step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 0, 1, 0], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw8349 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 1, 1], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw8349step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 2, 0], ![0, 1, 1, -2], ![1, 1, -3, 1]]

def raw8349step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, 1, -2, 0], ![0, -1, -1, 2], ![-1, -1, 3, -1]]

def raw8349step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw8350 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 1, 1], ![0, 2, 2, -4], ![1, 0, -3, 2]]

def raw8350step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 2, 0], ![0, 1, 2, -3], ![1, 1, -4, 2]]

def raw8350step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, 1, -2, 0], ![0, -1, -2, 3], ![-1, -1, 4, -2]]

def raw8350step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

def raw8351 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 2, 0], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw8351step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, -2, 0], ![1, 0, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical261
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8352 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 2, 0], ![0, 2, 1, -3], ![1, 0, -3, 2]]

def raw8352step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, -3, 1], ![1, 0, 2, -3]]

def raw8353 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-1, -1, 2, 0], ![2, 1, 1, -4]]

def raw8353step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, 0, 1, -2], ![0, 0, 1, -1], ![0, -1, 1, 0], ![1, 1, -2, 0], ![-2, -1, -1, 4]]

def raw8353step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -2, 0]]

def raw8354 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, -1, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-1, 2, -1, 0], ![1, 0, 3, -4]]

def raw8354step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, 0, 1, -2], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![1, -2, 1, 0], ![-1, 0, -3, 4]]

def raw8354step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw8355 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw8355step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 0, 1], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw8356 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-1, -1, 1, 1], ![2, 0, 2, -4]]

def raw8356step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, 0, 1, -2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![1, 1, -1, -1], ![-2, 0, -2, 4]]

def raw8356step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw8357 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, -1, 2], ![0, 2, -2, 0], ![1, -1, 3, -3]]

def raw8357step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![0, -1, -2, 3], ![1, 2, 0, -3]]

def raw8357step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, 0, -2, 1], ![0, 1, 2, -3], ![-1, -2, 0, 3]]

def raw8357step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, -2, 1]]

def raw8358 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, -1, 2], ![0, 2, 2, -4], ![1, -1, -1, 1]]

def raw8358step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![0, -1, 2, -1], ![1, 2, -4, 1]]

def raw8358step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, 0, -2, 1], ![0, 1, -2, 1], ![-1, -2, 4, -1]]

def raw8358step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw8359 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 0, 1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw8359step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![0, 0, 1, -1], ![1, 1, -3, 1]]

def raw8359step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, 0, -2, 1], ![0, 0, -1, 1], ![-1, -1, 3, -1]]

def raw8359step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw8360 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw8360step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw8361 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw8361step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw8362 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 1, 0], ![0, 2, -3, 1], ![1, -1, 2, -2]]

def raw8362step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![0, 1, -3, 2], ![1, 0, 1, -2]]

def raw8362step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, 0, -2, 1], ![0, -1, 3, -2], ![-1, 0, -1, 2]]

def raw8362step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw8363 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw8363step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw8364 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def raw8364step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw8365 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw8365step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw8366 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![0, 2, -3, 1], ![1, -1, 1, -1]]

def raw8366step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1]]

def raw8367 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw8367step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 1, -1, -1]]

def raw8368 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw8368step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw8369 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![0, 2, 1, -3], ![1, -1, -3, 3]]

def raw8369step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 2, 1, -3], ![1, -1, -3, 3]]

def raw8370 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 3, -2], ![0, 2, -3, 1], ![1, -1, 0, 0]]

def raw8370step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![0, 3, -3, 0], ![1, -2, 1, 0]]

def raw8370step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, -1, 0]]

def raw8371 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 3, -2], ![0, 2, -2, 0], ![1, -1, -1, 1]]

def raw8371step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, -1, -1]]

def raw8372 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 3, -2], ![0, 2, 0, -2], ![1, -1, -3, 3]]

def raw8372step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![0, -1, 0, 1], ![0, 2, 0, -2], ![1, -1, -3, 3]]

def raw8373 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, -3, 3], ![0, 1, 2, -3], ![1, -1, 1, -1]]

def raw8373step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, 1, -1], ![0, -3, 2, 1], ![1, 3, -3, -1]]

def raw8373step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, -1, -3, 3]]

def raw8374 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, -3, 3], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw8374step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, 1, -1], ![0, -3, 3, 0], ![1, 3, -4, 0]]

def raw8374step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -3, 3], ![0, 1, -1, 0], ![1, 0, 3, -4]]

def raw8375 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, -1, 1], ![0, 1, -2, 1], ![1, -1, 3, -3]]

def raw8375step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, 1, -1], ![0, -1, -2, 3], ![1, 1, 1, -3]]

def raw8375step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, -1, -1, 1], ![0, 1, 2, -3], ![-1, -1, -1, 3]]

def raw8375step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw8376 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, -1, 1], ![0, 1, 2, -3], ![1, -1, -1, 1]]

def raw8376step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, 1, -1], ![0, -1, 2, -1], ![1, 1, -3, 1]]

def raw8376step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, -1, -1, 1], ![0, 1, -2, 1], ![-1, -1, 3, -1]]

def raw8376step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw8377 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, 1, -1], ![0, 1, 1, -2], ![1, -1, -2, 2]]

def raw8377step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, -1, -2, 2]]

def raw8378 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, -2, 3], ![0, 2, 2, -4]]

def raw8378step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 0, 0], ![-1, -1, 2], ![0, -2, 2], ![1, 3, -4]]

def raw8378step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 0, 0], ![1, 1, -2], ![0, 2, -2], ![-1, -3, 4]]

def raw8378step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-1, -3, 4]]

def raw8378step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![1, 1, -2]]

def raw8379 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-2, 0, 2, 0], ![2, 1, 1, -4]]

def raw8379step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 1, -2], ![0, 0, 1, -1], ![0, -1, 1, 0], ![2, 0, -2, 0], ![-2, -1, -1, 4]]

def raw8379step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

def raw8380 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 0, 2, 0], ![1, 2, 1, -4]]

def raw8380step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 1, -2], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![2, 0, -2, 0], ![-1, -2, -1, 4]]

def raw8380step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw8381 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 1, 1, 0], ![1, 1, 2, -4]]

def raw8381step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw8382 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 2, 0, 0], ![1, 0, 3, -4]]

def raw8382step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 1, -2], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![2, -2, 0, 0], ![-1, 0, -3, 4]]

def raw8382step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw8383 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, 0, 1, 1], ![2, 0, 2, -4]]

def raw8383step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 1, -2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![2, 0, -1, -1], ![-2, 0, -2, 4]]

def raw8383step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical262
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8384 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![1, 1, 2, -4]]

def raw8384step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw8385 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![1, 0, 3, -4]]

def raw8385step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def raw8386 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, -1, 2], ![0, 2, 1, -3]]

def raw8386step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 1, -2], ![0, -2, -1, 3]]

def raw8386step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 0, -1], ![1, 1, -2], ![-2, -1, 3]]

def raw8386step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![1, 1, -2]]

def raw8387 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, -1, 2], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![0, 2, 2, -4]]

def raw8387step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 1, -2], ![-1, 0, 1, 0], ![-1, 0, 1, 0], ![2, 0, -1, -1], ![0, -2, -2, 4]]

def raw8387step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw8388 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, -1, 2], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![0, 1, 3, -4]]

def raw8388step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, -1, 0, 1], ![0, 1, 3, -4], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw8389 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 0, -1, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw8389step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, 0, 0]]

def raw8390 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 1, -1, 1], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw8390step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, 0, 0]]

def raw8391 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 2, 2, -3], ![1, 0, -2, 1]]

def raw8391step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 2, 0], ![0, 0, 2, -2], ![1, 1, -3, 1]]

def raw8391step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, 1, -2, 0], ![0, 0, -2, 2], ![-1, -1, 3, -1]]

def raw8391step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def raw8392 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![-1, 2, 2, -3], ![1, 0, -1, 0]]

def raw8392step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![0, 0, 1, -1], ![1, -2, -2, 3], ![-1, 0, 1, 0]]

def raw8392step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

def raw8393 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![0, 0, -1, 1]]

def raw8393step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![0, 0, 1, -1], ![0, -2, -2, 4], ![0, 0, 1, -1]]

def raw8393step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![-2, -2, 4], ![0, 1, -1]]

def raw8393step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw8394 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![-1, 1, 2, -2], ![1, 0, -1, 0]]

def raw8394step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw8395 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![0, 0, -1, 1]]

def raw8395step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![0, -1, 1, 0], ![0, -1, -2, 3], ![0, 0, 1, -1]]

def raw8395step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, -2, 3], ![0, 1, -1]]

def raw8395step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8396 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 2, 1, -3], ![0, 0, -1, 1]]

def raw8396step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![0, -2, -1, 3], ![0, 0, 1, -1]]

def raw8396step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![-2, -1, 3], ![0, 1, -1]]

def raw8396step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw8397 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 2, 2, -4], ![0, 0, -2, 2]]

def raw8397step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![0, -2, -2, 4], ![0, 0, 2, -2]]

def raw8397step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![-2, -2, 4], ![0, 2, -2]]

def raw8397step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw8398 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![-1, 0, -1, 2], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw8398step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw8399 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![-1, 1, -1, 1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw8399step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw8400 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![-1, 1, -1, 1], ![1, 0, -1, 0], ![-1, 0, -1, 2], ![1, 1, 2, -4]]

def raw8400step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![-1, 0, 1, 0], ![1, 0, 1, -2], ![-1, -1, -2, 4]]

def raw8400step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 0, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw8401 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![-1, 2, 1, -2], ![1, 0, -2, 1]]

def raw8401step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 2, 0], ![0, 1, 1, -2], ![1, 0, -2, 1]]

def raw8401step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 1, -2]]

def raw8402 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![-1, 2, 2, -3], ![1, 0, -3, 2]]

def raw8402step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 2, 0], ![0, 1, 2, -3], ![1, 0, -3, 2]]

def raw8402step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -3, 2], ![1, 0, 2, -3]]

def raw8403 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![-1, 2, 1, -2], ![1, 0, -1, 0]]

def raw8403step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw8404 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 1, -3], ![0, 0, -1, 1]]

def raw8404step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, -1, 0], ![0, 0, 1, -1], ![0, -2, -1, 3], ![0, 0, 1, -1]]

def raw8404step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, -1, 0], ![0, 1, -1], ![-2, -1, 3], ![0, 1, -1]]

def raw8404step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8405 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![-1, 1, 1, -1], ![1, 0, -1, 0]]

def raw8405step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw8406 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 0, -1, 1], ![-1, 0, -1, 2], ![1, 1, 2, -4]]

def raw8406step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, -1, 0], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, 1, -2], ![-1, -1, -2, 4]]

def raw8406step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw8407 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 1, -2], ![0, 0, -1, 1]]

def raw8407step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![0, -1, 1]]

def raw8407step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8408 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 0, -1, 3], ![1, 1, 2, -4]]

def raw8408step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw8409 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-1, 0, -1, 2], ![0, 1, 2, -3]]

def raw8409step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw8410 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 2, 1, -3], ![0, 0, -2, 2]]

def raw8410step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, -1, 0], ![0, -2, -1, 3], ![0, 0, 2, -2]]

def raw8410step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -1, 0], ![-2, -1, 3], ![0, 2, -2]]

def raw8410step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw8411 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 2, 2, -4], ![0, 0, -3, 3]]

def raw8411step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, -1, 0], ![0, -2, -2, 4], ![0, 0, 3, -3]]

def raw8411step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -1, 0], ![-2, -2, 4], ![0, 3, -3]]

def raw8411step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw8412 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 2, -1], ![-1, 2, 0, -1], ![1, 0, -2, 1]]

def raw8412step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, -2, 1], ![1, -2, 0, 1], ![-1, 0, 2, -1]]

def raw8412step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw8413 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 2, -1], ![-1, 2, 1, -2], ![1, 0, -3, 2]]

def raw8413step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 2, 0], ![0, 2, 1, -3], ![1, -1, -2, 2]]

def raw8413step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, -1, 2, -2]]

def raw8414 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 2, -1], ![0, 2, -2, 0]]

def raw8414step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![2, -2, 0]]

def raw8414step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -1, 0]]

def raw8415 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 2, -1], ![0, 2, 0, -2], ![0, 0, -2, 2]]

def raw8415step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![0, -2, 2]]

def raw8415step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical263
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8416 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 2, -1], ![0, 2, 1, -3], ![0, 0, -3, 3]]

def raw8416step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, -2, 1], ![0, -2, -1, 3], ![0, 0, 3, -3]]

def raw8416step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -2, 1], ![-2, -1, 3], ![0, 3, -3]]

def raw8416step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw8417 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 3, -2], ![0, 2, -3, 1]]

def raw8417step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 0, 0], ![-1, -1, 2], ![0, 3, -3], ![1, -2, 1]]

def raw8417step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -2, 1]]

def raw8418 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![-1, -1, 2, 0], ![2, 1, 1, -4]]

def raw8418step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![1, 0, 1, -2], ![0, -1, 1, 0], ![1, 1, -2, 0], ![-2, -1, -1, 4]]

def raw8418step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -2, 0]]

def raw8419 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![-1, 0, -1, 2], ![1, -1, 0, 0], ![-1, 2, -1, 0], ![1, 0, 3, -4]]

def raw8419step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![1, 0, 1, -2], ![-1, 1, 0, 0], ![1, -2, 1, 0], ![-1, 0, -3, 4]]

def raw8419step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw8420 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![-1, 0, 3, -2], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw8420step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw8421 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![-1, -1, 1, 1], ![2, 0, 2, -4]]

def raw8421step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![0, -1, 1, 0], ![1, 1, -1, -1], ![-2, 0, -2, 4]]

def raw8421step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw8422 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![-1, 2, -2, 1], ![1, -1, 3, -3]]

def raw8422step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![0, -1, -2, 3], ![1, 1, 1, -3]]

def raw8422step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, 0, -2, 1], ![0, 1, 2, -3], ![-1, -1, -1, 3]]

def raw8422step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 2, -3]]

def raw8423 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![-1, 2, 2, -3], ![1, -1, -1, 1]]

def raw8423step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![0, -1, 2, -1], ![1, 1, -3, 1]]

def raw8423step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, 0, -2, 1], ![0, 1, -2, 1], ![-1, -1, 3, -1]]

def raw8423step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw8424 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![-2, 0, 2, 0], ![2, 1, 1, -4]]

def raw8424step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![0, -1, 1, 0], ![2, 0, -2, 0], ![-2, -1, -1, 4]]

def raw8424step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

def raw8425 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, -1, -1, 2], ![1, 0, -1, 0], ![-2, 0, 2, 0], ![1, 2, 1, -4]]

def raw8425step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![-1, 0, 1, 0], ![2, 0, -2, 0], ![-1, -2, -1, 4]]

def raw8425step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw8426 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, -1, -1, 2], ![1, 0, -1, 0], ![-2, 1, 1, 0], ![1, 1, 2, -4]]

def raw8426step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw8427 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, -1, -1, 2], ![1, 0, -1, 0], ![-2, 2, 0, 0], ![1, 0, 3, -4]]

def raw8427step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![-1, 0, 1, 0], ![2, -2, 0, 0], ![-1, 0, -3, 4]]

def raw8427step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw8428 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 1, -1, 1], ![-1, -1, 2, 0], ![2, 1, 1, -4]]

def raw8428step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, -2, 0], ![-2, -1, -1, 4]]

def raw8428step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw8429 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -1, 0, 1], ![-1, 2, -1, 0], ![1, 0, 3, -4]]

def raw8429step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 1, 0], ![-1, 0, -3, 4]]

def raw8429step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw8430 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-2, 0, 2, 0], ![2, 1, 1, -4]]

def raw8430step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, 0, -2, 0], ![-2, -1, -1, 4]]

def raw8430step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw8431 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-2, -1, 2, 1], ![2, 1, 1, -4]]

def raw8431step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![2, 1, -2, -1], ![-2, -1, -1, 4]]

def raw8431step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def raw8432 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-2, 0, 1, 1], ![2, 0, 2, -4]]

def raw8432step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw8433 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-2, 0, 2, 0], ![2, 0, 1, -3]]

def raw8433step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw8434 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-1, -1, 2, 0], ![1, 1, 1, -3]]

def raw8434step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![1, 1, -2, 0], ![-1, -1, -1, 3]]

def raw8434step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def raw8435 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![-2, 0, 2, 0], ![1, 2, 1, -4]]

def raw8435step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![2, 0, -2, 0], ![-1, -2, -1, 4]]

def raw8435step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw8436 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![-2, 1, 1, 0], ![1, 1, 2, -4]]

def raw8436step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def raw8437 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![-2, 2, 0, 0], ![1, 0, 3, -4]]

def raw8437step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![2, -2, 0, 0], ![-1, 0, -3, 4]]

def raw8437step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw8438 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-2, 2, -1, 1], ![1, 0, 3, -4]]

def raw8438step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw8439 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-1, 2, -1, 0], ![0, 0, 3, -3]]

def raw8439step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![1, -2, 1, 0], ![0, 0, -3, 3]]

def raw8439step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -3, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw8440 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, -1, 2, 1], ![1, 2, 1, -4]]

def raw8440step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![2, 1, -2, -1], ![-1, -2, -1, 4]]

def raw8440step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -2, -1]]

def raw8441 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![1, 1, 2, -4]]

def raw8441step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![2, 0, -1, -1], ![-1, -1, -2, 4]]

def raw8441step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw8442 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 0, 2, 0], ![1, 1, 1, -3]]

def raw8442step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![2, 0, -2, 0], ![-1, -1, -1, 3]]

def raw8442step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw8443 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![1, 0, 3, -4]]

def raw8443step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw8444 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 1, 1, 0], ![1, 0, 2, -3]]

def raw8444step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw8445 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 2, 0, 0], ![1, -1, 3, -3]]

def raw8445step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw8446 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, 3, -3], ![-1, 2, -2, 1], ![1, -1, 0, 0]]

def raw8446step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 0, -3, 3], ![1, -2, 2, -1], ![-1, 1, 0, 0]]

def raw8446step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -3, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 2, -1]]

def raw8447 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 2, -2, 0], ![0, -1, 0, 1]]

def raw8447step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 0, -3, 3], ![0, -2, 2, 0], ![0, 1, 0, -1]]

def raw8447step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![0, 1, -1], ![0, -3, 3], ![-2, 2, 0], ![1, 0, -1]]

def raw8447step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical264
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8448 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-1, 1, -1, 1], ![-1, -1, 1, 1], ![2, 0, 2, -4]]

def raw8448step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![1, -1, 1, -1], ![1, 1, -1, -1], ![-2, 0, -2, 4]]

def raw8448step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw8449 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 0, -1, 1], ![-2, 0, 1, 1], ![2, 0, 2, -4]]

def raw8449step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw8450 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, -1, 1, 2], ![2, 0, 2, -4]]

def raw8450step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 2, -4]]

def raw8451 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, 0, 1, 1], ![2, -1, 2, -3]]

def raw8451step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 2, -3]]

def raw8452 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-1, -1, 1, 1], ![1, 0, 2, -3]]

def raw8452step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def raw8453 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![-2, 0, 1, 1], ![1, 1, 2, -4]]

def raw8453step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def raw8454 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![-2, 1, 0, 1], ![1, 0, 3, -4]]

def raw8454step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 3, -4]]

def raw8455 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, -1, 1, 2], ![1, 1, 2, -4]]

def raw8455step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw8456 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![1, 0, 3, -4]]

def raw8456step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def raw8457 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![1, 0, 2, -3]]

def raw8457step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw8458 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![1, -1, 3, -3]]

def raw8458step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw8459 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, -2, 0], ![0, -1, 3, -2]]

def raw8459step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![-1, 3, -2]]

def raw8459step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw8460 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![0, -1, 0, 1]]

def raw8460step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, -2, -1, 3], ![0, 1, 0, -1]]

def raw8460step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 1, -1], ![-2, -1, 3], ![1, 0, -1]]

def raw8460step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw8461 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![0, -1, -1, 2]]

def raw8461step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, -2, -2, 4], ![0, 1, 1, -2]]

def raw8461step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 1, -1], ![-2, -2, 4], ![1, 1, -2]]

def raw8461step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw8462 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![0, 2, 2, -4]]

def raw8462step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![-1, 0, 1, 0], ![2, 0, -1, -1], ![0, -2, -2, 4]]

def raw8462step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw8463 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![0, 1, 3, -4]]

def raw8463step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw8464 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, -1, -1, 1], ![-2, 0, 1, 1], ![0, 2, 2, -4]]

def raw8464step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![-1, 1, 1, -1], ![2, 0, -1, -1], ![0, -2, -2, 4]]

def raw8464step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw8465 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, -1, -1, 1], ![-2, 1, 0, 1], ![0, 1, 3, -4]]

def raw8465step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw8466 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, -1, 1, 2], ![0, 2, 2, -4]]

def raw8466step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw8467 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 1, 3, -4]]

def raw8467step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![-1, 0, 1, 0], ![2, 0, 0, -2], ![0, -1, -3, 4]]

def raw8467step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw8468 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![0, 1, 2, -3]]

def raw8468step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![-1, 0, 1, 0], ![2, 0, -1, -1], ![0, -1, -2, 3]]

def raw8468step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw8469 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![0, 0, 3, -3]]

def raw8469step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 0, 1]]

def raw8470 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw8470step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw8471 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![-1, 1, -1, 1], ![1, 0, 0, -1]]

def raw8471step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw8472 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw8472step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw8473 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![-1, 2, -3, 2], ![1, -1, 2, -2]]

def raw8473step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![0, 1, -3, 2], ![1, -1, 2, -2]]

def raw8473step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, 0, -2, 1], ![0, -1, 3, -2], ![-1, 1, -2, 2]]

def raw8473step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -1, 2, -2]]

def raw8474 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![-1, 2, 1, -2], ![1, -1, -2, 2]]

def raw8474step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![0, 1, 1, -2], ![1, -1, -2, 2]]

def raw8474step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 2, -2]]

def raw8475 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![-1, 2, 2, -3], ![1, -1, -3, 3]]

def raw8475step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![0, 1, 2, -3], ![1, -1, -3, 3]]

def raw8475step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, 0, -2, 1], ![0, -1, -2, 3], ![-1, 1, 3, -3]]

def raw8475step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 3, -3]]

def raw8476 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 2, 0, -1], ![1, -1, -2, 2]]

def raw8476step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -1, 2]]

def raw8477 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![0, -1, -2, 3]]

def raw8477step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2], ![-1, -2, 3]]

def raw8477step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw8478 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 0, 0, 0]]

def raw8478step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0]]

def raw8478step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![1, -1, 0]]

def raw8479 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-1, 1, 1, -1], ![1, -1, -2, 2]]

def raw8479step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical265
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8480 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![0, -1, -1, 2]]

def raw8480step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2]]

def raw8480step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw8481 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, -3, 1], ![0, -1, 2, -1]]

def raw8481step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, -1, 1], ![0, -2, 3, -1], ![0, 1, -2, 1]]

def raw8481step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -1, 1], ![-2, 3, -1], ![1, -2, 1]]

def raw8481step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw8482 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![0, -1, -1, 2]]

def raw8482step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![-1, -1, 2]]

def raw8482step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

def raw8483 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, 1, -3], ![0, -1, -2, 3]]

def raw8483step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![2, 1, -3], ![-1, -2, 3]]

def raw8483step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]

def raw8484 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![-1, 1, -2, 2], ![1, 0, 0, -1]]

def raw8484step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, -2, 2], ![1, -1, 2, -2], ![-1, 0, 0, 1]]

def raw8484step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 2, -2]]

def raw8485 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![-1, 1, -1, 1], ![1, 0, -1, 0]]

def raw8485step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 1, 0], ![0, 2, -1, -1], ![1, -2, 1, 0]]

def raw8485step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw8486 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![-1, 1, 0, 0], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw8486step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -2, -1, 2]]

def raw8487 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![-1, 2, -3, 2], ![1, -1, 1, -1]]

def raw8487step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![0, 2, -3, 1], ![1, -2, 2, -1]]

def raw8487step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, -1, -2, 2]]

def raw8488 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![-1, 2, -1, 0], ![1, -1, -1, 1]]

def raw8488step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![0, 2, -1, -1], ![1, -2, 0, 1]]

def raw8488step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, 0, -2, 1], ![0, -2, 1, 1], ![-1, 2, 0, -1]]

def raw8488step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw8489 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![-1, 2, 0, -1], ![1, -1, -2, 2]]

def raw8489step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -2, -1, 2]]

def raw8490 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![-1, 2, 1, -2], ![1, -1, -3, 3]]

def raw8490step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![0, 2, 1, -3], ![1, -2, -2, 3]]

def raw8490step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -2, -2, 3]]

def raw8491 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -2, 1]]

def raw8491step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, -2, 2], ![0, -1, 2, -1]]

def raw8491step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 0, -1], ![0, -2, 2], ![-1, 2, -1]]

def raw8491step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -1, 0]]

def raw8492 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -2, 1], ![0, 0, 0, 0]]

def raw8492step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, -2, 2], ![0, -1, 2, -1], ![0, 0, 0, 0]]

def raw8492step1 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, -2, 2], ![0, -1, 2, -1]]

def raw8492step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 0, -1], ![0, -2, 2], ![-1, 2, -1]]

def raw8492step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -1, 0]]

def raw8493 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 0, -1, 1]]

def raw8493step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![0, -1, 1]]

def raw8493step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0]]

def raw8494 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![-1, 1, 0, 0], ![1, -1, -2, 2]]

def raw8494step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -2, -1, 2]]

def raw8495 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![0, -1, -2, 3]]

def raw8495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![-1, -2, 3]]

def raw8495step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw8496 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 2, -3, 1], ![0, -1, 1, 0]]

def raw8496step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, -2, 2], ![0, -2, 3, -1], ![0, 1, -1, 0]]

def raw8496step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -2, 2], ![-2, 3, -1], ![1, -1, 0]]

def raw8496step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw8497 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 2, -1, -1], ![0, -1, -1, 2]]

def raw8497step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, -2, 2], ![0, -2, 1, 1], ![0, 1, 1, -2]]

def raw8497step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -2, 2], ![-2, 1, 1], ![1, 1, -2]]

def raw8497step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw8498 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 2, 0, -2], ![0, -1, -2, 3]]

def raw8498step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![2, 0, -2], ![-1, -2, 3]]

def raw8498step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

def raw8499 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 3, -3], ![-1, 2, -3, 2], ![1, -1, 0, 0]]

def raw8499step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![0, 3, -3, 0], ![1, -3, 2, 0]]

def raw8499step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -3, 2], ![1, 0, 0, -1]]

def raw8500 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 3, -3], ![-1, 2, -2, 1], ![1, -1, -1, 1]]

def raw8500step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![0, 3, -2, -1], ![1, -3, 1, 1]]

def raw8500step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, 0, -2, 1], ![0, -3, 2, 1], ![-1, 3, -1, -1]]

def raw8500step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 2, -3], ![1, 1, -2, 0]]

def raw8501 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 3, -3], ![0, 1, -3, 2]]

def raw8501step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, -3, 3], ![0, -1, 3, -2]]

def raw8501step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 0, -1], ![0, -3, 3], ![-1, 3, -2]]

def raw8501step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 3, -3], ![1, -1, 0]]

def raw8502 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 3, -3], ![0, 2, -3, 1], ![0, -1, 0, 1]]

def raw8502step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, -3, 3], ![0, -2, 3, -1], ![0, 1, 0, -1]]

def raw8502step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -3, 3], ![-2, 3, -1], ![1, 0, -1]]

def raw8502step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw8503 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 3, -3], ![0, 2, -2, 0], ![0, -1, -1, 2]]

def raw8503step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, -3, 3], ![0, -2, 2, 0], ![0, 1, 1, -2]]

def raw8503step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -3, 3], ![-2, 2, 0], ![1, 1, -2]]

def raw8503step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

def raw8504 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, -3, 2], ![-1, 1, 2, -2], ![1, -1, 1, -1]]

def raw8504step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 1, -1], ![0, -3, 2, 1], ![1, 2, -2, -1]]

def raw8504step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -3, 2], ![0, 1, 0, -1], ![1, -1, 2, -2]]

def raw8505 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, -3, 2], ![-1, 1, 3, -3], ![1, -1, 0, 0]]

def raw8505step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 1, -1], ![0, -3, 3, 0], ![1, 2, -3, 0]]

def raw8505step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -3, 3], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def raw8506 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, -3, 2], ![0, 1, 2, -3], ![0, -1, 1, 0]]

def raw8506step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, -1, 3, -2], ![0, -1, -2, 3], ![0, 1, -1, 0]]

def raw8506step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, 3, -2], ![-1, -2, 3], ![1, -1, 0]]

def raw8506step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1]]

def raw8507 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, -3, 2], ![0, 1, 3, -4], ![0, -1, 0, 1]]

def raw8507step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, -1, 3, -2], ![0, -1, -3, 4], ![0, 1, 0, -1]]

def raw8507step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, 3, -2], ![-1, -3, 4], ![1, 0, -1]]

def raw8507step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1]]

def raw8508 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, -1, 0], ![-1, 1, 2, -2], ![1, -1, -1, 1]]

def raw8508step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 1, -1], ![0, -1, 2, -1], ![1, 0, -2, 1]]

def raw8508step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, -1, -1, 1], ![0, 1, -2, 1], ![-1, 0, 2, -1]]

def raw8508step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw8509 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![1, 0, 3, -4]]

def raw8509step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def raw8510 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![-2, 0, 0, 2], ![1, 0, 3, -4]]

def raw8510step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 3, -4]]

def raw8511 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, -1, 0, 3], ![1, 0, 3, -4]]

def raw8511step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 3, -4]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical266
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8512 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![1, -1, 3, -3]]

def raw8512step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw8513 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![0, -1, -1, 2]]

def raw8513step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, -1, 1, 0], ![0, -1, -2, 3], ![0, 1, 1, -2]]

def raw8513step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, 1, 0], ![-1, -2, 3], ![1, 1, -2]]

def raw8513step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw8514 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 1, 3, -4]]

def raw8514step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw8515 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, -1, -1, 1], ![-2, 0, 0, 2], ![0, 1, 3, -4]]

def raw8515step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw8516 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, -1, 0, 3], ![0, 1, 3, -4]]

def raw8516step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw8517 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 0, 3, -3]]

def raw8517step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def raw8518 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, 0, -1], ![-1, 1, 2, -2], ![1, -1, -2, 2]]

def raw8518step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 1, -1], ![0, 0, 2, -2], ![1, -1, -2, 2]]

def raw8518step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -1, 1, -1]]

def raw8519 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![0, -1, -1, 2]]

def raw8519step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![-1, -1, 2]]

def raw8519step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

def raw8520 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![2, 1, -3]]

def raw8520step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![1, 1, -2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![-2, -1, 3]]

def raw8520step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2]]

def raw8521 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0]]

def raw8521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0]]

def raw8522 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![-2, 3, -1], ![2, 1, -3]]

def raw8522step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -3, 1], ![-2, -1, 3]]

def raw8522step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

def raw8523 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-1, 4, -3]]

def raw8523step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8524 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-1, 3, -2]]

def raw8524step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

def raw8525 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![-2, 4, -2]]

def raw8525step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

def raw8526 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw8526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw8527 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def raw8527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def raw8528 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![2, 2, -4]]

def raw8528step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![2, 0, -2], ![-2, -2, 4]]

def raw8528step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw8529 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-1, 2, -1]]

def raw8529step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8530 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![-1, -1, 2], ![1, 2, -3]]

def raw8530step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![-1, -2, 3]]

def raw8530step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

def raw8531 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0]]

def raw8531step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

def raw8532 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, 4, -4], ![1, -2, 1]]

def raw8532step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 4, -4], ![1, -2, 1]]

def raw8533 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![1, 3, -4]]

def raw8533step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]

def raw8534 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![-1, -1, 2], ![0, 4, -4]]

def raw8534step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0], ![1, 0, -1]]

def raw8536 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![0, 3, -3]]

def raw8536step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def raw8537 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0]]

def raw8537step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]

def raw8538 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![-2, -1, 3], ![2, 1, -3]]

def raw8538step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

def raw8539 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![-1, -2, 3], ![1, 2, -3]]

def raw8539step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw8540 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2]]

def raw8540step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8541 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![-1, -2, 3], ![0, 3, -3]]

def raw8541step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw8542 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 1, 0], ![1, 0, -1]]

def raw8542step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![1, -1, 0]]

def raw8543 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![-2, 3, -1], ![1, -3, 2]]

def raw8543step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical267
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8544 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![-1, 3, -2], ![0, -3, 3]]

def raw8544step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw8545 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 2, -1], ![1, -1, 0]]

def raw8545step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![1, 0, -1]]

def raw8546 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 3, -2], ![0, -2, 2], ![1, 0, -1]]

def raw8546step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def raw8547 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 4, -3], ![0, -3, 3], ![1, 0, -1]]

def raw8547step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0]]

def raw8548 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -1, 1], ![0, -3, 3], ![0, 4, -4]]

def raw8548step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-3, 3], ![4, -4]]

def raw8548step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]

def raw8549 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![-2, 2, 0], ![2, 1, -3]]

def raw8549step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![-2, -1, 3]]

def raw8549step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def raw8550 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-2, 4, -2]]

def raw8550step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

def raw8551 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![-3, 1, 2], ![3, 0, -3]]

def raw8551step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2], ![-3, 0, 3]]

def raw8551step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]

def raw8552 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![-2, 0, 2], ![2, 1, -3]]

def raw8552step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![-2, -1, 3]]

def raw8552step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

def raw8553 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![2, 0, -2]]

def raw8553step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![-2, 0, 2]]

def raw8553step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def raw8555 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![1, 3, -4]]

def raw8555step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 3, -4]]

def raw8556 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![-3, 1, 2], ![2, 1, -3]]

def raw8556step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]

def raw8557 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![-2, 0, 2], ![1, 2, -3]]

def raw8557step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

def raw8558 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, 2, 0]]

def raw8558step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

def raw8559 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2], ![-3, 2, 1]]

def raw8559step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]

def raw8560 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![0, 3, -3]]

def raw8560step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![3, -3]]

def raw8560step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw8561 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![-2, 0, 2], ![0, 4, -4]]

def raw8561step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0], ![1, 0, -1]]

def raw8562 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1], ![0, 3, -3]]

def raw8562step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw8563 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![-3, 1, 2], ![1, 2, -3]]

def raw8563step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]

def raw8564 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![-2, 0, 2], ![0, 3, -3]]

def raw8564step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def raw8565 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![-1, 4, -3]]

def raw8565step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 4, -3], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

def raw8566 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![-3, 3, 0]]

def raw8566step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![3, -3, 0]]

def raw8566step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]

def raw8567 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![0, -1, 1], ![-1, 3, -2], ![2, 1, -3]]

def raw8567step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![0, 1, -1], ![1, -3, 2], ![-2, -1, 3]]

def raw8567step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2]]

def raw8568 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![0, 4, -4], ![1, -1, 0]]

def raw8568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0]]

def raw8569 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![1, -1, 0], ![-2, 3, -1], ![2, 1, -3]]

def raw8569step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![-1, 1, 0], ![2, -3, 1], ![-2, -1, 3]]

def raw8569step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

def raw8570 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![-1, 4, -3]]

def raw8570step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8571 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![-1, 3, -2]]

def raw8571step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

def raw8572 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![-2, 4, -2]]

def raw8572step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

def raw8573 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1]]

def raw8573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw8574 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0]]

def raw8574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw8575 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![2, 2, -4]]

def raw8575step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![-2, -2, 4]]

def raw8575step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical268
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8576 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![-1, 2, -1]]

def raw8576step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8577 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![-1, -1, 2], ![1, 2, -3]]

def raw8577step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![-1, -2, 3]]

def raw8577step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw8578 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0]]

def raw8578step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw8579 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![-2, 2, 0], ![2, 1, -3]]

def raw8579step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![0, -1, 1], ![2, -2, 0], ![-2, -1, 3]]

def raw8579step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def raw8580 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![-2, 4, -2]]

def raw8580step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

def raw8581 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-1, 3, -2], ![2, 1, -3]]

def raw8581step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![1, -3, 2], ![-2, -1, 3]]

def raw8581step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2]]

def raw8582 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 4, -3], ![1, -1, 0]]

def raw8582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw8583 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 3, -1], ![2, 1, -3]]

def raw8583step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]

def raw8584 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![1, 1, -2]]

def raw8584step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1]]

def raw8585 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![-1, 4, -3]]

def raw8585step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw8586 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![-2, 2, 0], ![2, 1, -3]]

def raw8586step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]

def raw8586step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![-2, -1, 3]]

def raw8586step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

def raw8587 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![-1, 3, -2]]

def raw8587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![-1, 3, -2]]

def raw8587step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw8588 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![-2, 4, -2]]

def raw8588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![-2, 4, -2]]

def raw8588step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw8589 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![-2, 1, 1], ![2, 1, -3]]

def raw8589step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![-2, -1, 3]]

def raw8589step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw8590 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![-2, 2, 0], ![2, 0, -2]]

def raw8590step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

def raw8592 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 4, -4], ![0, -1, 1]]

def raw8592step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![4, -4], ![-1, 1]]

def raw8592step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]

def raw8593 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![-3, 3, 0], ![2, 1, -3]]

def raw8593step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]

def raw8594 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![-2, 1, 1], ![1, 3, -4]]

def raw8594step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def raw8595 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![-2, 3, -1], ![1, 1, -2]]

def raw8595step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

def raw8596 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 4, -3]]

def raw8596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 4, -3]]

def raw8596step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw8597 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-2, 4, -2]]

def raw8597step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8598 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![-1, -1, 2], ![0, 4, -4]]

def raw8598step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 4, -4], ![1, 0, -1]]

def raw8599 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![-1, 3, -2]]

def raw8599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![-1, 3, -2]]

def raw8599step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw8600 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![-2, 4, -2]]

def raw8600step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8601 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-2, 3, -1]]

def raw8601step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]

def raw8602 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![-3, 4, -1]]

def raw8602step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

def raw8603 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![-3, 1, 2], ![3, 0, -3]]

def raw8603step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![-3, 1, 2], ![3, 0, -3]]

def raw8603step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

def raw8604 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![-2, 0, 2], ![2, 1, -3]]

def raw8604step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![-2, -1, 3]]

def raw8604step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2], ![-2, -1, 3]]

def raw8604step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw8605 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![-2, 1, 1], ![2, 0, -2]]

def raw8605step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![-2, 0, 2]]

def raw8605step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![-2, 0, 2]]

def raw8605step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw8607 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![1, 3, -4]]

def raw8607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![-2, 0, 2], ![1, 3, -4]]

def raw8607step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical269
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8608 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![-3, 1, 2], ![2, 1, -3]]

def raw8608step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![-2, -1, 3]]

def raw8608step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![3, -1, -2], ![-2, -1, 3]]

def raw8608step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

def raw8609 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![-2, 0, 2], ![1, 2, -3]]

def raw8609step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![-1, -2, 3]]

def raw8609step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![2, 0, -2], ![-1, -2, 3]]

def raw8609step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw8610 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![-1, -1, 2], ![0, 3, -3]]

def raw8610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![-1, -1, 2], ![0, 3, -3]]

def raw8610step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1]]

def raw8611 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![-2, 2, 0]]

def raw8611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-2, 2, 0]]

def raw8611step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]

def raw8612 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2], ![-3, 2, 1]]

def raw8612step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2], ![3, -2, -1]]

def raw8612step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2], ![3, -2, -1]]

def raw8612step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

def raw8613 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1]]

def raw8613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw8614 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0]]

def raw8614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw8615 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![-2, 0, 2], ![2, 2, -4]]

def raw8615step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![-2, -2, 4]]

def raw8615step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw8616 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![-1, 2, -1]]

def raw8616step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw8617 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![-3, 1, 2], ![3, 0, -3]]

def raw8617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![-3, 1, 2], ![3, 0, -3]]

def raw8617step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

def raw8618 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![-2, 0, 2], ![2, 1, -3]]

def raw8618step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2], ![-2, -1, 3]]

def raw8618step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2], ![-2, -1, 3]]

def raw8618step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw8619 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![-2, 1, 1], ![2, 0, -2]]

def raw8619step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![-2, 0, 2]]

def raw8619step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![-2, 0, 2]]

def raw8619step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw8620 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![1, 2, -3]]

def raw8620step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![-1, -2, 3]]

def raw8620step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![-1, -2, 3]]

def raw8620step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]

def raw8621 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-3, 0, 3], ![3, 0, -3]]

def raw8621step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -3, 3], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def raw8622 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-3, 1, 2], ![3, -1, -2]]

def raw8622step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]

def raw8623 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, -1, 3], ![2, 1, -3]]

def raw8623step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]

def raw8624 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 0, 2], ![2, 0, -2]]

def raw8624step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw8625 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![2, -1, -1]]

def raw8625step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw8626 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0]]

def raw8626step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1]]

def raw8626step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw8628 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![0, -1, 1]]

def raw8628step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![2, -2], ![-1, 1]]

def raw8628step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw8629 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![-2, 0, 2], ![1, 3, -4]]

def raw8629step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 3, -4]]

def raw8630 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![-3, 0, 3], ![2, 2, -4]]

def raw8630step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]

def raw8631 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![-3, 1, 2], ![2, 1, -3]]

def raw8631step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

def raw8632 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![-2, -1, 3], ![1, 3, -4]]

def raw8632step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 3, -4]]

def raw8633 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![1, 2, -3]]

def raw8633step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw8634 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1]]

def raw8634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![-1, 2, -1]]

def raw8634step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw8635 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, 2, 0]]

def raw8635step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8636 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![-3, 2, 1]]

def raw8636step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]

def raw8637 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-3, 0, 3], ![2, 1, -3]]

def raw8637step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3], ![-2, -1, 3]]

def raw8637step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def raw8638 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-3, 1, 2], ![2, 0, -2]]

def raw8638step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1]]

def raw8639 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-2, -1, 3], ![1, 2, -3]]

def raw8639step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

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

def raw864 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![0, 0], ![3, -3]]

def raw864step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]

def raw866 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]

def raw867 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]

def raw868 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![2, -2], ![1, -1]]

def raw868step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]

def raw869 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]

def raw872 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]

def raw873 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![4, -4]]

def raw873step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]

def raw877 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![-1, 1], ![2, -2], ![2, -2]]

def raw877step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]

def raw879 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![0, 0], ![1, -1], ![2, -2]]

def raw879step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![1, -1], ![2, -2]]

def raw879step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![2, -2]]

def raw879step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw880 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![0, 0], ![2, -2], ![1, -1]]

def raw880step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![2, -2], ![1, -1]]

def raw880step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![2, -2], ![1, -1]]

def raw880step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]

def raw880step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw881 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![0, 0], ![3, -3]]

def raw881step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![3, -3]]

def raw881step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![3, -3]]

def raw881step2 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]

def raw882 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![1, -1], ![0, 0], ![2, -2]]

def raw882step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![1, -1], ![2, -2]]

def raw882step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![2, -2]]

def raw882step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw883 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![1, -1], ![1, -1], ![1, -1]]

def raw883step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![1, -1], ![1, -1]]

def raw883step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

def raw884 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![1, -1], ![2, -2]]

def raw884step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![2, -2]]

def raw884step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw885 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![1, -1], ![2, -2], ![0, 0]]

def raw885step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![1, -1], ![2, -2]]

def raw885step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![2, -2]]

def raw885step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw886 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![2, -2], ![1, -1]]

def raw886step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![2, -2], ![1, -1]]

def raw886step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]

def raw886step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw887 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![3, -3]]

def raw887step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![3, -3]]

def raw887step1 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]

def raw889 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![0, 0], ![0, 0], ![2, -2]]

def raw889step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![0, 0], ![2, -2]]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical270
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8640 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-2, 0, 2], ![1, 1, -2]]

def raw8640step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw8641 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-1, -1, 2], ![0, 2, -2]]

def raw8641step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

def raw8642 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![-2, 2, 0]]

def raw8642step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8643 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, 1, 1]]

def raw8643step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw8644 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![-3, 2, 1]]

def raw8644step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

def raw8645 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2], ![-3, 1, 2]]

def raw8645step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1]]

def raw8646 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![0, -1, 1]]

def raw8646step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![3, -3], ![-1, 1]]

def raw8646step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

def raw8647 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![-2, 0, 2], ![0, 4, -4]]

def raw8647step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 4, -4], ![1, -2, 1], ![1, 0, -1]]

def raw8648 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![-2, 1, 1], ![0, 3, -3]]

def raw8648step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw8649 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![1, 3, -4]]

def raw8649step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def raw8650 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, 4, -4]]

def raw8650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![-1, -1, 2], ![0, 4, -4]]

def raw8650step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0]]

def raw8651 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![-3, 1, 2], ![1, 3, -4]]

def raw8651step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]

def raw8652 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, 4, -4]]

def raw8652step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

def raw8653 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, 3, -3]]

def raw8653step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw8654 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-3, 1, 2], ![1, 2, -3]]

def raw8654step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

def raw8655 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-2, -1, 3], ![0, 4, -4]]

def raw8655step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0], ![1, 0, -1]]

def raw8656 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-2, 0, 2], ![0, 3, -3]]

def raw8656step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw8657 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1], ![0, 2, -2]]

def raw8657step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8658 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-1, -1, 2], ![-1, 4, -3]]

def raw8658step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8659 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-3, 3, 0]]

def raw8659step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw8660 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![-1, -1, 2], ![0, 3, -3]]

def raw8660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![-1, -1, 2], ![0, 3, -3]]

def raw8660step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1]]

def raw8662 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![-3, 1, 2], ![1, 2, -3]]

def raw8662step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

def raw8663 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![0, 3, -3]]

def raw8663step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw8664 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![-1, -1, 2], ![-1, 4, -3]]

def raw8664step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8665 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![-3, 3, 0]]

def raw8665step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw8666 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-3, 0, 3], ![1, 2, -3]]

def raw8666step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![3, 0, -3], ![-1, -2, 3]]

def raw8666step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def raw8667 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-3, 1, 2], ![1, 1, -2]]

def raw8667step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![3, -1, -2], ![-1, -1, 2]]

def raw8667step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

def raw8668 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-2, -1, 3], ![0, 3, -3]]

def raw8668step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def raw8669 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-2, 0, 2], ![0, 2, -2]]

def raw8669step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw8670 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-1, -2, 3], ![-1, 4, -3]]

def raw8670step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 4, -3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

def raw8671 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![-1, 3, -2]]

def raw8671step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical271
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8672 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![-3, 3, 0]]

def raw8672step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw8673 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![-3, 2, 1]]

def raw8673step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![3, -2, -1]]

def raw8673step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]

def raw8674 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![-2, 1, 1], ![-1, -1, 2], ![3, 0, -3]]

def raw8674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![-2, 1, 1], ![-1, -1, 2], ![3, 0, -3]]

def raw8674step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw8675 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![-3, 0, 3], ![2, 1, -3]]

def raw8675step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![-1, 1, 0], ![3, 0, -3], ![-2, -1, 3]]

def raw8675step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![3, 0, -3], ![-2, -1, 3]]

def raw8675step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw8676 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![-2, -1, 3], ![1, 2, -3]]

def raw8676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![-2, -1, 3], ![1, 2, -3]]

def raw8676step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw8677 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1]]

def raw8677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1]]

def raw8677step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8678 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![-3, 1, 2]]

def raw8678step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2], ![3, -1, -2]]

def raw8678step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2], ![3, -1, -2]]

def raw8678step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw8679 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, 0, 2]]

def raw8679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, 0, 2]]

def raw8679step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw8680 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![-2, -1, 3]]

def raw8680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![-2, -1, 3]]

def raw8680step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw8681 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![-3, 1, 2]]

def raw8681step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1], ![3, -1, -2]]

def raw8681step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1], ![3, -1, -2]]

def raw8681step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw8682 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, 3, -3]]

def raw8682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, 3, -3]]

def raw8682step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw8683 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![-3, 0, 3], ![1, 2, -3]]

def raw8683step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![3, 0, -3], ![-1, -2, 3]]

def raw8683step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![3, 0, -3], ![-1, -2, 3]]

def raw8683step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw8684 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![-2, -1, 3], ![0, 3, -3]]

def raw8684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-2, -1, 3], ![0, 3, -3]]

def raw8684step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw8685 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![-1, -1, 2], ![-1, 3, -2]]

def raw8685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-1, -1, 2], ![-1, 3, -2]]

def raw8685step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8686 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-3, 2, 1]]

def raw8686step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![3, -2, -1]]

def raw8686step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![3, -2, -1]]

def raw8686step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8687 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![-3, 1, 2]]

def raw8687step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![3, -1, -2]]

def raw8687step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![3, -1, -2]]

def raw8687step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8688 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![-2, 0, 2], ![-1, 2, -1], ![2, -1, -1]]

def raw8688step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![1, -2, 1], ![-2, 1, 1]]

def raw8688step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 0, 1], ![2, 0, -2], ![1, -2, 1], ![-2, 1, 1]]

def raw8688step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw8689 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![-2, 2, 0], ![-1, -1, 2], ![2, 0, -2]]

def raw8689step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![1, 1, -2], ![-2, 0, 2]]

def raw8689step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 0, 1], ![2, -2, 0], ![1, 1, -2], ![-2, 0, 2]]

def raw8689step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]

def raw8690 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![2, 0, -2], ![-2, -1, 3]]

def raw8690step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2], ![2, 1, -3]]

def raw8690step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2], ![2, 1, -3]]

def raw8690step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]

def raw8691 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![-1, -2, 3], ![-1, 3, -2]]

def raw8691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-1, -2, 3], ![-1, 3, -2]]

def raw8691step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

def raw8692 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0]]

def raw8692step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]

def raw8693 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3], ![2, 1, -3]]

def raw8693step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

def raw8694 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, -2, 3], ![1, 2, -3]]

def raw8694step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw8695 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2]]

def raw8695step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8696 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![-1, -2, 3], ![0, 3, -3]]

def raw8696step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 3, -3], ![1, 0, -1]]

def raw8697 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 0, 0]]

def raw8697step0 : Matrix (Fin 2) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1]]

def raw8697step1 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

def raw8698 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2], ![3, 0, -3]]

def raw8698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![-2, 1, 1], ![-1, -1, 2], ![3, 0, -3]]

def raw8698step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw8699 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3], ![2, 1, -3]]

def raw8699step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![3, 0, -3], ![-2, -1, 3]]

def raw8699step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![3, 0, -3], ![-2, -1, 3]]

def raw8699step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw8700 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3], ![1, 2, -3]]

def raw8700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![-2, -1, 3], ![1, 2, -3]]

def raw8700step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw8701 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1]]

def raw8701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1]]

def raw8701step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8702 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![-3, 1, 2]]

def raw8702step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![3, -1, -2]]

def raw8702step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2], ![3, -1, -2]]

def raw8702step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw8703 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![-2, 3, -1], ![1, -3, 2]]

def raw8703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-2, 3, -1], ![1, -3, 2]]

def raw8703step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical272
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8704 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![-1, 3, -2], ![0, -3, 3]]

def raw8704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-1, 3, -2], ![0, -3, 3]]

def raw8704step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0]]

def raw8705 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![-2, 0, 2]]

def raw8705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, 0, 2]]

def raw8705step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw8706 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![-2, -1, 3]]

def raw8706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![-2, -1, 3]]

def raw8706step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw8707 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![-3, 1, 2]]

def raw8707step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![3, -1, -2]]

def raw8707step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1], ![3, -1, -2]]

def raw8707step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw8708 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 0, 2], ![-1, -1, 2], ![3, 0, -3]]

def raw8708step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def raw8709 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![-1, -2, 3], ![3, 0, -3]]

def raw8709step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 2, -3], ![-3, 0, 3]]

def raw8709step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]

def raw8710 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![-1, -1, 2], ![3, -1, -2]]

def raw8710step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2], ![-3, 1, 2]]

def raw8710step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]

def raw8711 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1]]

def raw8711step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![1, -1], ![-1, 1]]

def raw8711step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw8712 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-2, -1, 3], ![2, 1, -3]]

def raw8712step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]

def raw8713 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -2, 3], ![1, 2, -3]]

def raw8713step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 2, -3]]

def raw8714 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![-1, -1, 2]]

def raw8714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![-1, -1, 2]]

def raw8714step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw8715 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![-3, 0, 3], ![2, 1, -3]]

def raw8715step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]

def raw8716 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![-2, -1, 3], ![1, 2, -3]]

def raw8716step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

def raw8717 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![-2, 1, 1]]

def raw8717step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw8718 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2], ![-3, 1, 2]]

def raw8718step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]

def raw8719 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-3, -1, 4], ![2, 1, -3]]

def raw8719step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

def raw8720 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-3, 0, 3], ![2, 0, -2]]

def raw8720step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![3, 0, -3], ![-2, 0, 2]]

def raw8720step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw8721 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-2, -2, 4], ![1, 2, -3]]

def raw8721step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw8722 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-2, -1, 3], ![1, 1, -2]]

def raw8722step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw8723 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-1, -2, 3], ![0, 2, -2]]

def raw8723step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def raw8724 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1]]

def raw8724step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw8725 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, 0, 2]]

def raw8725step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8726 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![-2, -1, 3]]

def raw8726step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw8727 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![-3, 1, 2]]

def raw8727step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

def raw8728 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![-3, 0, 3]]

def raw8728step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2], ![3, 0, -3]]

def raw8728step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw8729 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![-1, -1, 2]]

def raw8729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![-1, -1, 2]]

def raw8729step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw8730 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2]]

def raw8730step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8731 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, -1, 3]]

def raw8731step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw8732 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![-2, -2, 4]]

def raw8732step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw8733 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![-3, 1, 2]]

def raw8733step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]

def raw8734 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![-3, 0, 3]]

def raw8734step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1], ![3, 0, -3]]

def raw8734step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw8735 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![-2, 0, 2], ![0, 3, -3]]

def raw8735step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical273
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8736 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![-3, 0, 3], ![1, 2, -3]]

def raw8736step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]

def raw8737 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![-2, -1, 3], ![0, 3, -3]]

def raw8737step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw8738 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![-1, -1, 2], ![-1, 3, -2]]

def raw8738step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw8739 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![-3, 2, 1]]

def raw8739step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

def raw8740 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2], ![-3, 1, 2]]

def raw8740step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

def raw8741 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, 2, -1], ![2, -1, -1]]

def raw8741step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![2, 0, -2], ![1, -2, 1], ![-2, 1, 1]]

def raw8741step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]

def raw8742 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![-2, 2, 0], ![-1, -1, 2], ![2, 0, -2]]

def raw8742step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![1, 1, -2], ![-2, 0, 2]]

def raw8742step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]

def raw8743 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![-1, 2, -1], ![2, 0, -2], ![-2, -1, 3]]

def raw8743step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

def raw8744 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, -2, 3], ![0, 3, -3]]

def raw8744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![-1, -2, 3], ![0, 3, -3]]

def raw8744step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0]]

def raw8745 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2], ![0, 3, -3]]

def raw8745step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

def raw8746 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3], ![1, 2, -3]]

def raw8746step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

def raw8747 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3], ![0, 3, -3]]

def raw8747step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw8748 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, 2, -2]]

def raw8748step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

def raw8749 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, 3, -2]]

def raw8749step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw8750 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![-3, 2, 1]]

def raw8750step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![3, -2, -1]]

def raw8750step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8751 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![-3, 1, 2]]

def raw8751step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

def raw8752 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-3, -1, 4], ![1, 2, -3]]

def raw8752step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

def raw8753 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-3, 0, 3], ![1, 1, -2]]

def raw8753step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![3, 0, -3], ![-1, -1, 2]]

def raw8753step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw8754 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, -2, 4], ![0, 3, -3]]

def raw8754step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw8755 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, -1, 3], ![0, 2, -2]]

def raw8755step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw8756 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-1, -2, 3], ![-1, 3, -2]]

def raw8756step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8757 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-1, -1, 2], ![-1, 2, -1]]

def raw8757step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8758 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![-3, 2, 1]]

def raw8758step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 1, 0], ![3, -2, -1]]

def raw8758step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8759 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-3, 1, 2]]

def raw8759step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![3, -1, -2]]

def raw8759step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8760 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![-3, 0, 3]]

def raw8760step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![3, 0, -3]]

def raw8760step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw8761 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-2, -1, 3], ![-1, 2, -1], ![2, -1, -1]]

def raw8761step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def raw8762 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-2, 0, 2], ![-1, 1, 0], ![2, -1, -1]]

def raw8762step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw8763 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-2, 0, 2], ![-1, 2, -1], ![2, -2, 0]]

def raw8763step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![1, -2, 1], ![-2, 2, 0]]

def raw8763step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]

def raw8764 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-2, 1, 1], ![-1, -1, 2], ![2, 0, -2]]

def raw8764step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

def raw8765 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-2, 2, 0], ![-1, -2, 3], ![2, 0, -2]]

def raw8765step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

def raw8766 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-2, 2, 0], ![-1, -1, 2], ![2, -1, -1]]

def raw8766step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![2, -2, 0], ![1, 1, -2], ![-2, 1, 1]]

def raw8766step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]

def raw8767 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![-2, -1, 3]]

def raw8767step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical274
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8768 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-1, 2, -1], ![2, -1, -1], ![-2, -1, 3]]

def raw8768step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def raw8769 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-1, 2, -1], ![2, 0, -2], ![-2, -2, 4]]

def raw8769step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

def raw8770 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![-2, 3, -1], ![1, -3, 2]]

def raw8770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-2, 3, -1], ![1, -3, 2]]

def raw8770step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw8771 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![-1, 3, -2], ![0, -3, 3]]

def raw8771step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-1, 3, -2], ![0, -3, 3]]

def raw8771step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0]]

def raw8772 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![-1, -2, 3], ![-1, 3, -2]]

def raw8772step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8773 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-3, 3, 0], ![1, -3, 2]]

def raw8773step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

def raw8774 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, 3, -1], ![0, -3, 3]]

def raw8774step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw8775 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, -3, 4], ![-1, 3, -2]]

def raw8775step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw8776 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, -2, 3], ![-1, 2, -1]]

def raw8776step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw8777 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, 3, -2], ![-1, -3, 4]]

def raw8777step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw8778 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -1, 1], ![0, 2, -2], ![0, -1, 1]]

def raw8778step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1]]

def raw8778step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw8781 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![-2, 0, 2], ![-1, 4, -3]]

def raw8781step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

def raw8782 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![-2, 1, 1], ![-1, 2, -1]]

def raw8782step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -2, 1]]

def raw8782step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

def raw8783 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![-2, 4, -2]]

def raw8783step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

def raw8784 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1], ![-2, 0, 2], ![-1, 4, -3]]

def raw8784step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

def raw8785 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, 4, -3]]

def raw8785step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]

def raw8786 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![-2, -1, 3], ![-1, 4, -3]]

def raw8786step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 4, -3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw8787 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![-2, 0, 2], ![-1, 3, -2]]

def raw8787step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![2, 0, -2], ![1, -3, 2]]

def raw8787step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw8788 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1], ![-1, 2, -1]]

def raw8788step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

def raw8789 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![-1, -1, 2], ![-2, 4, -2]]

def raw8789step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def raw8790 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, 2, -1]]

def raw8790step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

def raw8791 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![-1, -1, 2], ![-2, 4, -2]]

def raw8791step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def raw8792 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-2, 0, 2], ![-1, 2, -1]]

def raw8792step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, 0, -2], ![1, -2, 1]]

def raw8792step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8793 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-2, 1, 1], ![-1, 1, 0]]

def raw8793step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -1, 0]]

def raw8793step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8794 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-1, -2, 3], ![-2, 4, -2]]

def raw8794step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw8795 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![-2, 3, -1]]

def raw8795step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -3, 1]]

def raw8795step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

def raw8796 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-5, 2, 1, 2], ![5, -1, -2, -2]]

def raw8796step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -5, 5], ![-1, 2, -1], ![1, 1, -2], ![0, 2, -2]]

def raw8796step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 5, -5], ![1, -2, 1]]

def raw8797 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-4, 2, 1, 1], ![4, -1, -2, -1]]

def raw8797step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![-1, 2, -1], ![1, 1, -2], ![0, 1, -1]]

def raw8797step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 4, -4], ![1, -2, 1]]

def raw8798 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-3, -1, 1, 3], ![3, 2, -2, -3]]

def raw8798step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-1, -1, 2], ![1, 1, -2], ![0, 3, -3]]

def raw8798step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -3, 3], ![0, 3, -3], ![1, 1, -2]]

def raw8799 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-3, 2, -2, 3], ![3, -1, 1, -3]]

def raw8799step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-1, 2, -1], ![1, -2, 1], ![0, 3, -3]]

def raw8799step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -3, 3], ![0, 3, -3], ![1, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical275
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8800 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-3, 3, -2, 2], ![3, -2, 1, -2]]

def raw8800step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-1, 3, -2], ![1, -2, 1], ![0, 2, -2]]

def raw8800step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -2, 2], ![0, 3, -3], ![1, 1, -2]]

def raw8801 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-3, 3, 1, -1], ![3, -2, -2, 1]]

def raw8801step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-1, 3, -2], ![1, 1, -2], ![0, -1, 1]]

def raw8801step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 3, -3], ![1, -2, 1]]

def raw8802 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![2, 2, -2, -2]]

def raw8802step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, -1, 2], ![1, 1, -2], ![0, 2, -2]]

def raw8802step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

def raw8803 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 2, 1], ![2, 2, -3, -1]]

def raw8803step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, -1, 2], ![1, 2, -3], ![0, 1, -1]]

def raw8803step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![-1, -2, 3], ![0, -1, 1]]

def raw8803step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2]]

def raw8804 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 2, -2, 2], ![2, -1, 1, -2]]

def raw8804step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 2, -1], ![1, -2, 1], ![0, 2, -2]]

def raw8804step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

def raw8805 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 2, 1, -1], ![2, -1, -2, 1]]

def raw8805step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 2, -1], ![1, 1, -2], ![0, -1, 1]]

def raw8805step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1]]

def raw8806 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 3, -2, 1], ![2, -2, 1, -1]]

def raw8806step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 3, -2], ![1, -2, 1], ![0, 1, -1]]

def raw8806step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2]]

def raw8807 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 3, 1, -2], ![2, -2, -2, 2]]

def raw8807step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 3, -2], ![1, 1, -2], ![0, -2, 2]]

def raw8807step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1]]

def raw8808 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -2, 2, 1], ![1, 3, -3, -1]]

def raw8808step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -2, 3], ![1, 2, -3], ![0, 1, -1]]

def raw8808step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3]]

def raw8809 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, 1, 1], ![1, 2, -2, -1]]

def raw8809step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![1, 1, -2], ![0, 1, -1]]

def raw8809step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

def raw8810 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, 3, -1], ![1, 2, -4, 1]]

def raw8810step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![1, 3, -4], ![0, -1, 1]]

def raw8810step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![1, 1, -2], ![-1, -3, 4], ![0, 1, -1]]

def raw8810step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]

def raw8811 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -1, 2], ![0, 2, 2, -4], ![1, -1, -2, 2]]

def raw8811step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 2, 2, -4], ![1, -1, -2, 2]]

def raw8812 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw8812step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![1, 0, -1, 0], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 1, 2, -2]]

def raw8812step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw8813 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, 1, 0], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw8813step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![1, 1, 0, -2], ![0, 0, -2, 2]]

def raw8813step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, 0, -2, 1], ![-1, -1, 0, 2], ![0, 0, 2, -2]]

def raw8813step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw8814 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, 1, 0], ![0, 2, 1, -3], ![1, -1, -3, 3]]

def raw8814step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![1, 1, 1, -3], ![0, 0, -3, 3]]

def raw8814step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, 0, -2, 1], ![-1, -1, -1, 3], ![0, 0, 3, -3]]

def raw8814step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw8815 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, 2, -1], ![0, 2, 0, -2], ![1, -1, -3, 3]]

def raw8815step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![1, 2, 0, -3], ![0, -1, -2, 3]]

def raw8815step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, 0, -2, 1], ![-1, -2, 0, 3], ![0, 1, 2, -3]]

def raw8815step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, -2, 1]]

def raw8816 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 1, -3, 3], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw8816step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, 1, -1], ![1, -3, 1, 1], ![0, 3, -2, -1]]

def raw8816step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, -1, -1, 1], ![-1, 3, -1, -1], ![0, -3, 2, 1]]

def raw8816step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 0, 1], ![0, 1, 2, -3], ![1, 1, -1, -1]]

def raw8817 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 1, -3, 3], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw8817step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, 1, -1], ![1, -3, 2, 0], ![0, 3, -3, 0]]

def raw8817step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -3, 3], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def raw8818 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 1, -2, 2], ![0, 1, 2, -3], ![1, -1, -1, 1]]

def raw8818step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, 1, -1], ![1, -2, 2, -1], ![0, 2, -3, 1]]

def raw8818step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -3, 2], ![0, 1, 0, -1], ![1, -1, 2, -2]]

def raw8819 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 1, 0, 0], ![1, 0, -1, 0]]

def raw8819step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 1, 0], ![1, 0, -1]]

def raw8819step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![1, -1, 0]]

def raw8820 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 2, -2, 1], ![1, -1, 1, -1]]

def raw8820step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 2, -1], ![1, -2, 1], ![0, 1, -1]]

def raw8820step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

def raw8821 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 2, 1, -2], ![1, -1, -2, 2]]

def raw8821step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![0, -2, 2]]

def raw8821step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1]]

def raw8822 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, -1, -2, 3], ![0, 2, 1, -3]]

def raw8822step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 0, 0], ![-1, -1, 2], ![1, -2, 1], ![0, 3, -3]]

def raw8822step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -2, 1], ![0, 3, -3]]

def raw8822step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -2, 1]]

def raw8823 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-2, 2, 0, 0], ![2, 0, 2, -4]]

def raw8823step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 1, -2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, -2, 0, 0], ![-2, 0, -2, 4]]

def raw8823step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -2, 0, 0]]

def raw8824 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-2, 0, 1, 1], ![2, 1, 1, -4]]

def raw8824step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 1, -2], ![0, 0, 1, -1], ![0, -1, 1, 0], ![2, 0, -1, -1], ![-2, -1, -1, 4]]

def raw8824step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw8825 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-2, 1, 0, 1], ![2, 0, 2, -4]]

def raw8825step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 1, -2], ![0, 0, 1, -1], ![0, -1, 1, 0], ![2, -1, 0, -1], ![-2, 0, -2, 4]]

def raw8825step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def raw8826 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![1, 2, 1, -4]]

def raw8826step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 1, -2], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![2, 0, -1, -1], ![-1, -2, -1, 4]]

def raw8826step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw8827 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![1, 1, 2, -4]]

def raw8827step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw8828 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, 0, 0, 2], ![2, 0, 2, -4]]

def raw8828step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 1, -2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![2, 0, 0, -2], ![-2, 0, -2, 4]]

def raw8828step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def raw8829 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![1, 1, 2, -4]]

def raw8829step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw8830 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, -1, -1, 2], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 2, 2, -4]]

def raw8830step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 1, -2], ![-1, 0, 1, 0], ![-1, 0, 1, 0], ![2, 0, 0, -2], ![0, -2, -2, 4]]

def raw8830step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw8831 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![-1, 2, 2, -3], ![1, -1, -2, 2]]

def raw8831step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![1, -1, 2, -2], ![0, 1, -3, 2]]

def raw8831step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, 0, -2, 1], ![-1, 1, -2, 2], ![0, -1, 3, -2]]

def raw8831step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -1, 2, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical276
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8832 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![-2, 2, 0, 0], ![2, 0, 2, -4]]

def raw8832step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![0, 1, 1, -2], ![0, 0, 1, -1], ![2, -2, 0, 0], ![-2, 0, -2, 4]]

def raw8832step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -2, 0, 0]]

def raw8833 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![-2, 0, 1, 1], ![2, 1, 1, -4]]

def raw8833step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![0, 1, 1, -2], ![0, -1, 1, 0], ![2, 0, -1, -1], ![-2, -1, -1, 4]]

def raw8833step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw8834 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![-2, 1, 0, 1], ![2, 0, 2, -4]]

def raw8834step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![0, 1, 1, -2], ![0, -1, 1, 0], ![2, -1, 0, -1], ![-2, 0, -2, 4]]

def raw8834step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def raw8835 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, -1, -1, 2], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![1, 2, 1, -4]]

def raw8835step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![0, 1, 1, -2], ![-1, 0, 1, 0], ![2, 0, -1, -1], ![-1, -2, -1, 4]]

def raw8835step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw8836 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, -1, -1, 2], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![1, 1, 2, -4]]

def raw8836step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw8837 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -1, -1, 2], ![-2, 2, 0, 0], ![2, 0, 2, -4]]

def raw8837step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, -2, 0, 0], ![-2, 0, -2, 4]]

def raw8837step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -2, 0, 0]]

def raw8838 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-2, 0, 1, 1], ![2, 1, 1, -4]]

def raw8838step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, 0, -1, -1], ![-2, -1, -1, 4]]

def raw8838step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw8839 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-2, 1, 0, 1], ![2, 0, 2, -4]]

def raw8839step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -2, 0, 1]]

def raw8840 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-2, 2, 0, 0], ![2, -1, 2, -3]]

def raw8840step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, -2, 0, 0], ![-2, 1, -2, 3]]

def raw8840step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 0, 0]]

def raw8841 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-2, -1, 1, 2], ![2, 1, 1, -4]]

def raw8841step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![2, 1, -1, -2], ![-2, -1, -1, 4]]

def raw8841step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, -1, -2]]

def raw8842 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-2, 0, 0, 2], ![2, 0, 2, -4]]

def raw8842step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![2, 0, 0, -2], ![-2, 0, -2, 4]]

def raw8842step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw8843 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-2, 0, 1, 1], ![2, 0, 1, -3]]

def raw8843step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, 0, 0, -1]]

def raw8844 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-2, 1, 0, 1], ![2, -1, 2, -3]]

def raw8844step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![2, -1, 0, -1], ![-2, 1, -2, 3]]

def raw8844step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def raw8845 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![-2, 0, 1, 1], ![1, 2, 1, -4]]

def raw8845step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![2, 0, -1, -1], ![-1, -2, -1, 4]]

def raw8845step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw8846 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![-2, 1, 0, 1], ![1, 1, 2, -4]]

def raw8846step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def raw8847 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, -1, 1, 2], ![1, 2, 1, -4]]

def raw8847step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![2, 1, -1, -2], ![-1, -2, -1, 4]]

def raw8847step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, -1, -2]]

def raw8848 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![1, 1, 2, -4]]

def raw8848step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![2, 0, 0, -2], ![-1, -1, -2, 4]]

def raw8848step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw8849 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![1, 1, 1, -3]]

def raw8849step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![2, 0, -1, -1], ![-1, -1, -1, 3]]

def raw8849step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw8850 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![1, 0, 2, -3]]

def raw8850step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -3, 2], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw8851 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 0, -1, 1], ![-2, 0, 0, 2], ![2, 0, 2, -4]]

def raw8851step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![0, -1, 1, 0], ![0, 0, 1, -1], ![2, 0, 0, -2], ![-2, 0, -2, 4]]

def raw8851step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw8852 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, -1, 0, 3], ![2, 0, 2, -4]]

def raw8852step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 2, -4]]

def raw8853 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, 0, 0, 2], ![2, -1, 2, -3]]

def raw8853step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 2, -3]]

def raw8854 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![-2, 0, 0, 2], ![1, 1, 2, -4]]

def raw8854step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def raw8855 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, -1, 0, 3], ![1, 1, 2, -4]]

def raw8855step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw8856 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![1, 0, 2, -3]]

def raw8856step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 0, 1, -1], ![0, 1, -3, 2], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw8857 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 2, -4], ![0, -1, -2, 3]]

def raw8857step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![0, -2, -2, 4], ![0, 1, 2, -3]]

def raw8857step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, 1, -1], ![-2, -2, 4], ![1, 2, -3]]

def raw8857step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw8858 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 2, 2, -4]]

def raw8858step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![-1, 0, 1, 0], ![2, 0, 0, -2], ![0, -2, -2, 4]]

def raw8858step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw8859 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, -1, -1, 1], ![-2, 0, 0, 2], ![0, 2, 2, -4]]

def raw8859step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![-1, 1, 1, -1], ![2, 0, 0, -2], ![0, -2, -2, 4]]

def raw8859step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw8860 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, -1, 0, 3], ![0, 2, 2, -4]]

def raw8860step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw8861 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 1, 2, -3]]

def raw8861step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![-1, 0, 1, 0], ![2, 0, 0, -2], ![0, -1, -2, 3]]

def raw8861step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw8862 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw8862step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, -1, 1], ![1, -1, 0, 0], ![0, -1, 0, 1], ![-1, 1, 2, -2]]

def raw8862step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw8863 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, 1, -1], ![-1, 2, 0, -1], ![1, -1, -2, 2]]

def raw8863step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![1, 1, 0, -2], ![0, -1, -1, 2]]

def raw8863step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, 0, -2, 1], ![-1, -1, 0, 2], ![0, 1, 1, -2]]

def raw8863step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical277
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8864 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, 1, -1], ![-1, 2, 1, -2], ![1, -1, -3, 3]]

def raw8864step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![1, 1, 1, -3], ![0, -1, -2, 3]]

def raw8864step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, 0, -2, 1], ![-1, -1, -1, 3], ![0, 1, 2, -3]]

def raw8864step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 2, -3]]

def raw8865 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, -1, 2]]

def raw8865step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw8866 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-1, 1, 0, 0], ![1, -1, -2, 2]]

def raw8866step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, -1, 1], ![0, -1, 0, 1], ![1, -1, 0, 0], ![-1, 1, 2, -2]]

def raw8866step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw8867 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![0, -1, -2, 3]]

def raw8867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, -2, 3]]

def raw8867step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8868 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![0, -1, -2, 3]]

def raw8868step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![-1, -2, 3]]

def raw8868step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw8869 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 1, -3], ![0, -1, -3, 4]]

def raw8869step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, -1, 1], ![0, -2, -1, 3], ![0, 1, 3, -4]]

def raw8869step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, -1, 1], ![-2, -1, 3], ![1, 3, -4]]

def raw8869step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def raw8870 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, 2, -2], ![-1, 2, 0, -1], ![1, -1, -3, 3]]

def raw8870step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![1, 2, 0, -3], ![0, -2, -1, 3]]

def raw8870step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, 0, -2, 1], ![-1, -2, 0, 3], ![0, 2, 1, -3]]

def raw8870step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw8871 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, 2, -2], ![0, 2, 0, -2], ![0, -1, -3, 4]]

def raw8871step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, -2, 2], ![0, -2, 0, 2], ![0, 1, 3, -4]]

def raw8871step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, -2, 2], ![-2, 0, 2], ![1, 3, -4]]

def raw8871step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

def raw8872 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 1, -3, 2], ![-1, 1, 1, -1], ![1, -1, 1, -1]]

def raw8872step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 1, -1], ![1, -3, 1, 1], ![0, 2, -1, -1]]

def raw8872step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, -1, -1, 1], ![-1, 3, -1, -1], ![0, -2, 1, 1]]

def raw8872step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw8873 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 1, -3, 2], ![-1, 1, 2, -2], ![1, -1, 0, 0]]

def raw8873step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 1, -1], ![1, -3, 2, 0], ![0, 2, -2, 0]]

def raw8873step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def raw8874 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 1, -3, 2], ![0, 1, 1, -2], ![0, -1, 1, 0]]

def raw8874step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, -1, 3, -2], ![0, -1, -1, 2], ![0, 1, -1, 0]]

def raw8874step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-1, 3, -2], ![-1, -1, 2], ![1, -1, 0]]

def raw8874step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw8875 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 1, -3, 2], ![0, 1, 2, -3], ![0, -1, 0, 1]]

def raw8875step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, -1, 3, -2], ![0, -1, -2, 3], ![0, 1, 0, -1]]

def raw8875step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-1, 3, -2], ![-1, -2, 3], ![1, 0, -1]]

def raw8875step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1]]

def raw8876 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 1, -2, 1], ![-1, 1, 2, -2], ![1, -1, -1, 1]]

def raw8876step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw8877 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 1, -2, 1], ![0, 1, 2, -3], ![0, -1, -1, 2]]

def raw8877step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, -1, 2, -1], ![0, -1, -2, 3], ![0, 1, 1, -2]]

def raw8877step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-1, 2, -1], ![-1, -2, 3], ![1, 1, -2]]

def raw8877step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

def raw8878 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-2, -1, 1, 2]]

def raw8878step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw8879 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 0, -1, 1]]

def raw8879step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 1, 0], ![1, 0, -1], ![0, -1, 1]]

def raw8879step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![1, -1, 0]]

def raw8880 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![1, -2, 2, -1], ![-1, 3, -3, 1]]

def raw8880step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -2, 3], ![1, 2, -3], ![0, -1, 1]]

def raw8880step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3]]

def raw8881 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![1, -1, 1, -1], ![-1, 2, -2, 1]]

def raw8881step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -1, 2], ![1, 1, -2], ![0, -1, 1]]

def raw8881step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

def raw8882 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![1, -1, 2, -2], ![-1, 2, -3, 2]]

def raw8882step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -1, 2], ![1, 2, -3], ![0, -2, 2]]

def raw8882step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![1, 1, -2], ![-1, -2, 3], ![0, 2, -2]]

def raw8882step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2]]

def raw8883 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![2, -1, 1, -2], ![-2, 2, -2, 2]]

def raw8883step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![-1, -1, 2], ![1, 1, -2], ![0, -2, 2]]

def raw8883step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

def raw8884 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-4, 2, -1, 3], ![4, -1, -1, -2]]

def raw8884step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![-1, 2, -1], ![2, -1, -1], ![-1, 3, -2]]

def raw8884step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -2, 1], ![-2, 1, 1], ![1, -3, 2]]

def raw8884step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -4, 4], ![1, 1, -2], ![1, 2, -3]]

def raw8885 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-4, 2, 0, 2], ![4, -1, -2, -1]]

def raw8885step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![-1, 2, -1], ![2, 0, -2], ![-1, 2, -1]]

def raw8885step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -2, 1], ![-2, 0, 2], ![1, -2, 1]]

def raw8885step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![1, -2, 1], ![1, -2, 1]]

def raw8886 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-3, -1, 0, 4], ![3, 2, -2, -3]]

def raw8886step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-1, -1, 2], ![2, 0, -2], ![-1, 4, -3]]

def raw8886step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 1, -2], ![-2, 0, 2], ![1, -4, 3]]

def raw8886step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -4, 3], ![1, 1, -2]]

def raw8887 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-3, 2, -1, 2], ![3, -1, -1, -1]]

def raw8887step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-1, 2, -1], ![2, -1, -1], ![-1, 2, -1]]

def raw8887step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -2, 1], ![-2, 1, 1], ![1, -2, 1]]

def raw8887step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]

def raw8888 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-3, 2, 0, 1], ![3, -1, -2, 0]]

def raw8888step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-1, 2, -1], ![2, 0, -2], ![-1, 1, 0]]

def raw8888step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -2, 1], ![-2, 0, 2], ![1, -1, 0]]

def raw8888step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

def raw8889 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-3, 2, 1, 0], ![3, -1, -3, 1]]

def raw8889step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-1, 2, -1], ![2, 1, -3], ![-1, 0, 1]]

def raw8889step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -2, 1], ![-2, -1, 3], ![1, 0, -1]]

def raw8889step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw8890 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-3, 3, 0, 0], ![3, -2, -2, 1]]

def raw8890step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-1, 3, -2], ![2, 0, -2], ![-1, 0, 1]]

def raw8890step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -3, 2], ![-2, 0, 2], ![1, 0, -1]]

def raw8890step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

def raw8891 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-2, -2, 2, 2], ![2, 3, -4, -1]]

def raw8891step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, -2, 3], ![2, 2, -4], ![-1, 2, -1]]

def raw8891step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, 2, -3], ![-2, -2, 4], ![1, -2, 1]]

def raw8891step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -2, 1], ![1, 2, -3]]

def raw8892 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-2, -1, -2, 5], ![2, 2, 0, -4]]

def raw8892step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, -1, 2], ![2, -2, 0], ![-1, 5, -4]]

def raw8892step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![-2, 2, 0], ![1, -5, 4]]

def raw8892step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -2, 1], ![1, 4, -5]]

def raw8893 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-2, -1, -1, 4], ![2, 2, -1, -3]]

def raw8893step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, -1, 2], ![2, -1, -1], ![-1, 4, -3]]

def raw8893step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![-2, 1, 1], ![1, -4, 3]]

def raw8893step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -2, 1], ![1, 3, -4]]

def raw8894 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-2, -1, 0, 3], ![2, 2, -2, -2]]

def raw8894step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, -1, 2], ![2, 0, -2], ![-1, 3, -2]]

def raw8894step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![-2, 0, 2], ![1, -3, 2]]

def raw8894step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

def raw8895 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-2, -1, 3, 0], ![2, 2, -5, 1]]

def raw8895step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, -1, 2], ![2, 3, -5], ![-1, 0, 1]]

def raw8895step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![-2, -3, 5], ![1, 0, -1]]

def raw8895step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

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

def raw8896 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-2, 2, -1, 1], ![2, -1, -1, 0]]

def raw8896step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 2, -1], ![2, -1, -1], ![-1, 1, 0]]

def raw8896step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, -2, 1], ![-2, 1, 1], ![1, -1, 0]]

def raw8896step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw8897 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-2, 2, 1, -1], ![2, -1, -3, 2]]

def raw8897step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 2, -1], ![2, 1, -3], ![-1, -1, 2]]

def raw8897step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, -2, 1], ![-2, -1, 3], ![1, 1, -2]]

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

def raw949 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw950 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 1, -1], ![2, 0, -2]]

def raw950step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

def raw951 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 2, -2], ![2, -1, -1]]

def raw952 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![1, -1, 0], ![1, 2, -3]]

def raw953 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def raw954 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1]]

def raw954step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def raw955 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![2, 1, -3]]

def raw956 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 3, -3], ![1, -1, 0], ![1, 1, -2]]

def raw957 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def raw958 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 3, -3], ![2, 0, -2]]

def raw959 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 4, -4], ![1, -1, 0], ![1, 0, -1]]

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

def raw9484step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw9485 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, -1, -1, 4], ![2, -1, 1, -2]]

def raw9485step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -1, -2]]

def raw9486 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, -1, 0, 3], ![2, -1, 0, -1]]

def raw9486step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw9487 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, -1, 3], ![2, -2, 1, -1]]

def raw9487step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def raw9488 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, 0, 2], ![2, -2, 0, 0]]

def raw9488step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw9489 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, 1, 1], ![2, -2, -1, 1]]

def raw9489step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9490 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, 2, 0], ![2, -2, -2, 2]]

def raw9490step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def raw9491 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -2, 1], ![-2, -1, 2, 1]]

def raw9491step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def raw9492 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0], ![-2, -1, 1, 2]]

def raw9492step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw9493 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, 0, -1], ![-2, -1, 0, 3]]

def raw9493step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw9494 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0], ![-2, -2, 2, 2]]

def raw9494step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw9495 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1], ![-2, -2, 1, 3]]

def raw9495step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw9496 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, 0, -2], ![-2, -2, 0, 4]]

def raw9496step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw9497 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 0, 1], ![1, 0, -1, 0], ![-2, 1, 1, 0]]

def raw9497step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw9498 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![-2, 1, 0, 1], ![1, -1, 1, -1]]

def raw9498step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def raw9499 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 0, 0], ![-2, 1, 1, 0]]

def raw9499step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw9500 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 1, -1, 2], ![1, -1, 1, -1]]

def raw9500step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw9501 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 1, 0, 1], ![1, -1, 0, 0]]

def raw9501step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw9502 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, -1, 1], ![-2, 1, 1, 0]]

def raw9502step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw9503 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, 0, 1]]

def raw9503step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical297
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9504 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 0, 1, 1]]

def raw9504step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw9505 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![-2, 1, 0, 1], ![1, -2, 2, -1]]

def raw9505step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def raw9506 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![-2, 1, -1, 2], ![1, -2, 2, -1]]

def raw9506step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def raw9507 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![1, -2, 1, 0]]

def raw9507step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw9508 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 1, -2, 3], ![1, -2, 2, -1]]

def raw9508step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw9509 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 1, -1, 2], ![1, -2, 1, 0]]

def raw9509step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw9510 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![1, -2, 0, 1]]

def raw9510step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw9511 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 2, -3], ![0, -1, -2, 3]]

def raw9511step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![-1, -2, 3]]

def raw9511step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3]]

def raw9512 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![0, -2, 0, 2]]

def raw9512step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![-2, 0, 2]]

def raw9512step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

def raw9513 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -2, 0, 1], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 2, 1, -3]]

def raw9513step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 2, 0, -1], ![-1, 0, 1, 0], ![2, 0, 0, -2], ![0, -2, -1, 3]]

def raw9513step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw9514 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![0, 2, 1, -3]]

def raw9514step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 1, -1], ![-1, 1, 0, 0], ![2, 0, 0, -2], ![0, -2, -1, 3]]

def raw9514step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw9515 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, -1, 0, 0], ![-1, 0, -1, 2], ![-1, 2, 2, -3]]

def raw9515step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 1, -1], ![-1, 1, 0, 0], ![1, 0, 1, -2], ![1, -2, -2, 3]]

def raw9515step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw9516 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 0, -1, 0], ![-2, -1, 1, 2], ![0, 2, 1, -3]]

def raw9516step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw9517 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 0, -1, 0], ![-1, -1, 0, 2], ![-1, 2, 2, -3]]

def raw9517step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 1, -1], ![-1, 0, 1, 0], ![1, 1, 0, -2], ![1, -2, -2, 3]]

def raw9517step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def raw9518 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 0, -1, 0], ![-1, -1, 1, 1], ![-1, 2, 1, -2]]

def raw9518step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 1, -1], ![-1, 0, 1, 0], ![1, 1, -1, -1], ![1, -2, -1, 2]]

def raw9518step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw9519 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 0, -1, 0], ![0, 2, 0, -2], ![-2, -1, 2, 1]]

def raw9519step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw9520 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 0, 0, -1], ![-1, -1, 0, 2], ![-1, 2, 1, -2]]

def raw9520step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 1, -1], ![-1, 0, 0, 1], ![1, 1, 0, -2], ![1, -2, -1, 2]]

def raw9520step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw9521 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 0, 0, -1], ![0, -1, -1, 2], ![-2, 2, 2, -2]]

def raw9521step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 1, -1], ![-1, 0, 0, 1], ![0, 1, 1, -2], ![2, -2, -2, 2]]

def raw9521step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw9522 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 0, 0, -1], ![0, 2, 0, -2], ![-2, -1, 1, 2]]

def raw9522step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw9523 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, -1, 1], ![-2, 0, 0, 2], ![0, 2, 1, -3]]

def raw9523step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 1, 1, -1], ![2, 0, 0, -2], ![0, -2, -1, 3]]

def raw9523step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw9524 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, -1, 1], ![-1, 0, -1, 2], ![-1, 2, 2, -3]]

def raw9524step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 1, 1, -1], ![1, 0, 1, -2], ![1, -2, -2, 3]]

def raw9524step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw9525 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, -1, 3], ![0, 2, 1, -3]]

def raw9525step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw9526 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![0, 2, 0, -2]]

def raw9526step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw9527 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 0, -2, 3], ![-1, 2, 2, -3]]

def raw9527step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![1, 0, 2, -3], ![1, -2, -2, 3]]

def raw9527step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw9528 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 0, -1, 2], ![-1, 2, 1, -2]]

def raw9528step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![1, 0, 1, -2], ![1, -2, -1, 2]]

def raw9528step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw9529 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -2, 1], ![-2, -1, 1, 2], ![0, 2, 1, -3]]

def raw9529step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw9530 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -2, 1], ![-1, -1, 0, 2], ![-1, 2, 2, -3]]

def raw9530step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 2, -1], ![1, 1, 0, -2], ![1, -2, -2, 3]]

def raw9530step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw9531 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -2, 1], ![-1, -1, 1, 1], ![-1, 2, 1, -2]]

def raw9531step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 2, -1], ![1, 1, -1, -1], ![1, -2, -1, 2]]

def raw9531step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw9532 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -2, 1], ![0, 2, 0, -2], ![-2, -1, 2, 1]]

def raw9532step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw9533 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 0, 3], ![0, 2, 1, -3]]

def raw9533step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![2, 1, 0, -3], ![0, -2, -1, 3]]

def raw9533step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 2, -3]]

def raw9534 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 1, 2], ![0, 2, 0, -2]]

def raw9534step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw9535 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 1, 1, -2]]

def raw9535step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![2, 0, 0, -2], ![0, -1, -1, 2]]

def raw9535step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical298
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9536 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, -1, 3], ![-1, 2, 2, -3]]

def raw9536step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, 1, 1, -3], ![1, -2, -2, 3]]

def raw9536step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw9537 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 0, 2], ![-1, 2, 1, -2]]

def raw9537step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, 1, 0, -2], ![1, -2, -1, 2]]

def raw9537step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw9538 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 1, 1], ![-1, 2, 0, -1]]

def raw9538step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, 1, -1, -1], ![1, -2, 0, 1]]

def raw9538step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw9539 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, -1, -1, 2], ![-2, 2, 2, -2]]

def raw9539step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![0, 1, 1, -2], ![2, -2, -2, 2]]

def raw9539step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw9540 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, -1, -1], ![-2, -1, 2, 1]]

def raw9540step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw9541 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, 0, -2], ![-2, -1, 1, 2]]

def raw9541step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw9542 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, -1, 3], ![-1, 2, 1, -2]]

def raw9542step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![1, 1, 1, -3], ![1, -2, -1, 2]]

def raw9542step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw9543 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, 0, 2], ![-1, 2, 0, -1]]

def raw9543step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![1, 1, 0, -2], ![1, -2, 0, 1]]

def raw9543step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw9544 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, -1, -2, 3], ![-2, 2, 2, -2]]

def raw9544step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![0, 1, 2, -3], ![2, -2, -2, 2]]

def raw9544step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw9545 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, -1, -1, 2], ![-2, 2, 1, -1]]

def raw9545step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![0, 1, 1, -2], ![2, -2, -1, 1]]

def raw9545step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw9546 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, -1, 2, -1], ![-2, 2, -2, 2]]

def raw9546step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![0, 1, -2, 1], ![2, -2, 2, -2]]

def raw9546step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw9547 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, 2, -1, -1], ![-2, -1, 1, 2]]

def raw9547step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw9548 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, 2, 0, -2], ![-2, -1, 0, 3]]

def raw9548step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw9549 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, -1, 0, 0], ![0, -1, 2, -1], ![-2, 2, -2, 2]]

def raw9549step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 0, 0, 1], ![-1, 1, 0, 0], ![0, 1, -2, 1], ![2, -2, 2, -2]]

def raw9549step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw9550 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1], ![0, -2, 2, 0], ![-2, 2, -2, 2]]

def raw9550step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def raw9551 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1], ![0, -1, 2, -1], ![-2, 1, -2, 3]]

def raw9551step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

def raw9552 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 2, -2], ![-1, 1, -1, 1], ![1, -1, 0, 0]]

def raw9552step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![-1, 2, -1, 0], ![1, -2, 1, 0]]

def raw9552step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw9553 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 2, -2], ![-1, 2, 1, -2], ![1, -2, -2, 3]]

def raw9553step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, 1, -2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -2, -2, 3]]

def raw9554 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, -1, 0, 1]]

def raw9554step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![-1, 0, 1]]

def raw9554step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0]]

def raw9555 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, 1, -2], ![0, -1, -2, 3]]

def raw9555step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![-1, -2, 3]]

def raw9555step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2]]

def raw9556 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 3, -3], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, -2, 0, 1]]

def raw9556step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -2, 0, 1]]

def raw9557 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![-1, 1, -1, 1], ![1, -2, 0, 1]]

def raw9557step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -2, 0, 1]]

def raw9558 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![0, -2, 0, 2]]

def raw9558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2]]

def raw9558step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw9559 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![0, 1, 3, -4]]

def raw9559step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw9560 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![0, -1, 3, -2]]

def raw9560step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw9561 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, 0, 2], ![-1, 1, 3, -3]]

def raw9561step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 3, -3], ![1, 0, -2, 1]]

def raw9562 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![-1, 1, -1, 1], ![1, -1, 0, 0], ![-1, -1, 0, 2], ![1, 0, 3, -4]]

def raw9562step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw9563 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, -1, 0, 1], ![1, -1, 0, 0], ![-1, 0, -1, 2], ![0, 1, 3, -4]]

def raw9563step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw9564 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, -1, 0, 1], ![1, 0, -1, 0], ![-1, -1, 0, 2], ![0, 1, 3, -4]]

def raw9564step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def raw9565 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![1, 0, 3, -4]]

def raw9565step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 1, 0], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![2, 0, 0, -2], ![-1, 0, -3, 4]]

def raw9565step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw9566 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 0, 2, 0]]

def raw9566step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 0, 2, 0]]

def raw9566step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def raw9567 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![0, -1, 0, 1], ![-1, -1, 0, 2], ![1, 0, 3, -4]]

def raw9567step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 3, -4]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical299
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9568 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 0, 1], ![-2, 0, 0, 2], ![1, 0, 3, -4]]

def raw9568step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def raw9569 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, -1, 0, 3], ![1, 0, 3, -4]]

def raw9569step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw9570 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![1, -1, 3, -3]]

def raw9570step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw9571 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-1, -1, 0, 2], ![0, 0, 3, -3]]

def raw9571step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw9572 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 0, 1], ![1, 0, 0, -1], ![-2, 0, 2, 0]]

def raw9572step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw9573 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, -1, 0, 3], ![1, 0, 2, -3]]

def raw9573step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![2, 1, 0, -3], ![-1, 0, -2, 3]]

def raw9573step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw9574 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![1, -1, 2, -2]]

def raw9574step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![2, 0, 0, -2], ![-1, 1, -2, 2]]

def raw9574step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw9575 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 2, 0]]

def raw9575step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw9576 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, -1, 2, 1]]

def raw9576step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw9577 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, -2, 0, 1], ![-2, 0, 3, -1]]

def raw9577step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw9578 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, -1, 1, -1], ![-2, -1, 2, 1]]

def raw9578step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw9579 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, -1, 0, 3], ![1, -1, 2, -2]]

def raw9579step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def raw9580 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 0, 3, -1], ![1, -2, -1, 2]]

def raw9580step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def raw9581 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, -1, 1, -1], ![-2, -1, 1, 2]]

def raw9581step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw9582 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1], ![-2, -2, 2, 2]]

def raw9582step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9583 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 1, 3, -4]]

def raw9583step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def raw9584 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![0, 1, 3, -4]]

def raw9584step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw9585 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![0, -1, 3, -2]]

def raw9585step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw9586 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 0, -1], ![-1, -1, 0, 2], ![-1, 1, 3, -3]]

def raw9586step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw9587 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![0, -1, 0, 1], ![-1, 0, -1, 2], ![0, 1, 3, -4]]

def raw9587step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw9588 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![0, 0, -1, 1], ![-1, -1, 0, 2], ![0, 1, 3, -4]]

def raw9588step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw9589 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, -1, 1], ![-2, 0, 0, 2], ![0, 1, 3, -4]]

def raw9589step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw9590 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, -1, 3], ![0, 1, 3, -4]]

def raw9590step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw9591 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![0, 1, 2, -3]]

def raw9591step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![2, 0, 0, -2], ![0, -1, -2, 3]]

def raw9591step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw9592 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, -1, 2], ![0, 0, 3, -3]]

def raw9592step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw9593 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 0, -1, 2], ![-1, 1, 3, -3]]

def raw9593step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, 3, -3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw9594 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 0, 3], ![0, 1, 3, -4]]

def raw9594step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw9595 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 0, 3, -3]]

def raw9595step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![2, 0, 0, -2], ![0, 0, -3, 3]]

def raw9595step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw9596 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![0, -1, 3, -2]]

def raw9596step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw9597 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 0, 2], ![-1, 1, 3, -3]]

def raw9597step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw9598 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, -1, 0, 3], ![0, 1, 2, -3]]

def raw9598step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw9599 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, -1, 2], ![0, -1, 3, -2]]

def raw9599step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw96 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw960 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 4, -4], ![2, -1, -1]]

def raw961 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![1, -1, 0], ![1, 4, -5]]

def raw961step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, -1, 4], ![5, 0, -5]]

def raw961step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 5, -5], ![1, -2, 1]]

def raw962 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![1, 0, -1], ![1, 3, -4]]

def raw962step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 0, 3], ![5, -1, -4]]

def raw962step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 3, -3], ![1, 1, -2]]

def raw963 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![1, 1, -2], ![1, 2, -3]]

def raw964 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![1, 2, -3], ![1, 1, -2]]

def raw964step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![1, 1, -2], ![1, 2, -3]]

def raw965 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![1, 3, -4], ![1, 0, -1]]

def raw965step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 3, 0], ![5, -4, -1]]

def raw965step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 3, -3], ![1, 1, -2]]

def raw966 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, 0, -3]]

def raw967 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -1, -2]]

def raw968 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, 0, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical300
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9600 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![0, -1, 2, -1]]

def raw9600step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw9601 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, -1, 3], ![-1, 1, 3, -3]]

def raw9601step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw9602 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, 0, 2], ![-1, 1, 2, -2]]

def raw9602step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![1, 1, 0, -2], ![1, -1, -2, 2]]

def raw9602step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw9603 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, -1, -1, 2], ![-2, 1, 3, -2]]

def raw9603step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw9604 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![0, -2, 3, -1]]

def raw9604step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw9605 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-1, 1, 1, -1], ![-1, -2, 2, 1]]

def raw9605step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw9606 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -2, 0, 2], ![-2, 1, 3, -2]]

def raw9606step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, -1, 0]]

def raw9607 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -2, 1, 1], ![-2, 1, 2, -1]]

def raw9607step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw9608 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![-1, 1, 2, -2], ![1, -2, -1, 2]]

def raw9608step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 1, -2], ![-1, 0, 2, -1], ![1, -1, -2, 2]]

def raw9608step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 2, -2]]

def raw9609 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, -1, 0, 3], ![1, 0, 2, -3]]

def raw9609step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![2, 1, 0, -3], ![-1, 0, -2, 3]]

def raw9609step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw9610 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![1, -1, 2, -2]]

def raw9610step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![2, 0, 0, -2], ![-1, 1, -2, 2]]

def raw9610step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw9611 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 2, 0]]

def raw9611step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw9612 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, -1, 2, 1]]

def raw9612step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw9613 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, -2, 0, 1], ![-2, 0, 3, -1]]

def raw9613step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw9614 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, -1, 1, -1], ![-2, -1, 2, 1]]

def raw9614step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw9615 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![-2, -1, 0, 3], ![1, -1, 2, -2]]

def raw9615step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def raw9616 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![-2, 0, 3, -1], ![1, -2, -1, 2]]

def raw9616step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def raw9617 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, -1, 1, -1], ![-2, -1, 1, 2]]

def raw9617step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw9618 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1], ![-2, -2, 2, 2]]

def raw9618step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9619 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![-2, -1, 0, 3], ![1, 0, 2, -3]]

def raw9619step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 1, 1, -1], ![2, 1, 0, -3], ![-1, 0, -2, 3]]

def raw9619step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw9620 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![-2, 0, 0, 2], ![1, -1, 2, -2]]

def raw9620step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 1, 1, -1], ![2, 0, 0, -2], ![-1, 1, -2, 2]]

def raw9620step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw9621 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 0, 0], ![-2, 0, 2, 0]]

def raw9621step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw9622 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1], ![-2, -1, 2, 1]]

def raw9622step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw9623 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, -1, -1, 4], ![1, 0, 2, -3]]

def raw9623step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, 0, -3]]

def raw9624 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, -1, 0, 3], ![1, 0, 1, -2]]

def raw9624step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![2, 1, 0, -3], ![-1, 0, -1, 2]]

def raw9624step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw9625 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 0, -1, 3], ![1, -1, 2, -2]]

def raw9625step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, -1, -2]]

def raw9626 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![1, -1, 1, -1]]

def raw9626step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![2, 0, 0, -2], ![-1, 1, -1, 1]]

def raw9626step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw9627 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, -1, 1], ![-2, 0, 2, 0]]

def raw9627step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw9628 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 1, 1]]

def raw9628step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![2, 0, -1, -1]]

def raw9628step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw9629 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 2, 1]]

def raw9629step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw9630 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, -1, 1, 2]]

def raw9630step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw9631 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, -2, 0, 1], ![-2, 0, 3, -1]]

def raw9631step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 0, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical301
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9632 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, -1, 1, -1], ![-2, -1, 2, 1]]

def raw9632step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def raw9633 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![-2, -1, 0, 3], ![1, -1, 2, -2]]

def raw9633step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw9634 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![-2, 0, 3, -1], ![1, -2, -1, 2]]

def raw9634step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw9635 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, -2, -1, 2], ![-2, 0, 3, -1]]

def raw9635step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw9636 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, -2, 0, 1], ![-2, 0, 2, 0]]

def raw9636step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw9637 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, -1, 0, 0], ![-2, -1, 2, 1]]

def raw9637step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw9638 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, -1, 1, -1], ![-2, -1, 1, 2]]

def raw9638step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw9639 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-2, -2, 2, 2]]

def raw9639step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9640 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, -1, -1, 4], ![1, -1, 2, -2]]

def raw9640step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -1, -2]]

def raw9641 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, -1, 0, 3], ![1, -1, 1, -1]]

def raw9641step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 0, 0, 1], ![2, 1, 0, -3], ![-1, 1, -1, 1]]

def raw9641step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw9642 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 0, 2, 0], ![1, -2, -1, 2]]

def raw9642step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9643 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 0, 3, -1], ![1, -2, -2, 3]]

def raw9643step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3], ![1, 0, 0, -1]]

def raw9644 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, -1, 0, 0], ![-2, -1, 1, 2]]

def raw9644step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw9645 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, -1, 1, -1], ![-2, -1, 0, 3]]

def raw9645step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 0, 0, 1], ![-1, 1, -1, 1], ![2, 1, 0, -3]]

def raw9645step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw9646 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, -1, 0], ![-2, -2, 2, 2]]

def raw9646step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9647 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1], ![-2, -2, 1, 3]]

def raw9647step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

def raw9648 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![0, -2, 0, 2]]

def raw9648step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![0, -1, -1, 2], ![0, 2, 0, -2]]

def raw9648step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![2, 0, -2]]

def raw9648step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

def raw9649 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![0, 1, 2, -3]]

def raw9649step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 1, 1, -1], ![-1, 1, 0, 0], ![2, 0, 0, -2], ![0, -1, -2, 3]]

def raw9649step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw9650 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 0, 0], ![-2, 1, -1, 2], ![0, 0, 3, -3]]

def raw9650step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw9651 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![0, -1, 3, -2]]

def raw9651step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw9652 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0], ![-1, -1, 0, 2], ![-1, 1, 3, -3]]

def raw9652step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def raw9653 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1], ![-2, -1, 0, 3], ![0, 1, 2, -3]]

def raw9653step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 1, 1, -1], ![-1, 0, 0, 1], ![2, 1, 0, -3], ![0, -1, -2, 3]]

def raw9653step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw9654 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1], ![-1, -1, 0, 2], ![-1, 1, 2, -2]]

def raw9654step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 1, 1, -1], ![-1, 0, 0, 1], ![1, 1, 0, -2], ![1, -1, -2, 2]]

def raw9654step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw9655 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1], ![0, -1, -1, 2], ![-2, 1, 3, -2]]

def raw9655step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw9656 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, -1, 1], ![-2, 0, 0, 2], ![0, 1, 2, -3]]

def raw9656step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 1, 1, -1], ![2, 0, 0, -2], ![0, -1, -2, 3]]

def raw9656step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw9657 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, -1, 1], ![-2, 1, -1, 2], ![0, 0, 3, -3]]

def raw9657step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw9658 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, -1, 3], ![0, 1, 2, -3]]

def raw9658step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw9659 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![0, 1, 1, -2]]

def raw9659step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![2, 0, 0, -2], ![0, -1, -1, 2]]

def raw9659step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw9660 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, -2, 3], ![0, 0, 3, -3]]

def raw9660step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw9661 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, -1, 2], ![0, 0, 2, -2]]

def raw9661step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw9662 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -2, 1], ![-2, 1, 0, 1], ![0, -1, 3, -2]]

def raw9662step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw9663 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -2, 1], ![-1, -1, 0, 2], ![-1, 1, 3, -3]]

def raw9663step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, -1, 3, -3], ![1, 0, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical302
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9664 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 0, 3], ![0, 1, 2, -3]]

def raw9664step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![2, 1, 0, -3], ![0, -1, -2, 3]]

def raw9664step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw9665 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 1, -1, 2], ![0, -1, 3, -2]]

def raw9665step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw9666 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![0, -1, 2, -1]]

def raw9666step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw9667 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, -1, 3], ![-1, 1, 3, -3]]

def raw9667step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def raw9668 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 0, 2], ![-1, 1, 2, -2]]

def raw9668step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, 1, 0, -2], ![1, -1, -2, 2]]

def raw9668step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw9669 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, -1, -1, 2], ![-2, 1, 3, -2]]

def raw9669step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw9670 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, -1, -1, 4], ![0, 1, 2, -3]]

def raw9670step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw9671 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, -1, 0, 3], ![0, 1, 1, -2]]

def raw9671step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![2, 1, 0, -3], ![0, -1, -1, 2]]

def raw9671step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def raw9672 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, -1, 3], ![-1, 1, 2, -2]]

def raw9672step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![1, 1, 1, -3], ![1, -1, -2, 2]]

def raw9672step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 1, -3]]

def raw9673 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, 0, 2], ![-1, 1, 1, -1]]

def raw9673step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![1, 1, 0, -2], ![1, -1, -1, 1]]

def raw9673step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw9674 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, -1, -2, 3], ![-2, 1, 3, -2]]

def raw9674step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -2, 3], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw9675 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, -1, -1, 2], ![-2, 1, 2, -1]]

def raw9675step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![0, 1, 1, -2], ![2, -1, -2, 1]]

def raw9675step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw9676 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![0, -2, 3, -1]]

def raw9676step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def raw9677 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1], ![-1, 1, 1, -1], ![-1, -2, 2, 1]]

def raw9677step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw9678 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1], ![0, -2, 0, 2], ![-2, 1, 3, -2]]

def raw9678step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end


