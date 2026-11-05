-- Prove2me | Definitions.Def_OAIQ106E145
-- name    : OAIQ106E145
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T18:30:58.361824+00:00
-- url     : https://prove2.me/theorems/2f589a8c-ef59-483a-9159-2dd107b61193
-- title:
--   Definitions bundle OAIQ106E145 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 5775 declarations of OpenAI's Lean: 5775 definitions. The definitions and types are `OAI.MUB6.Certificate.PairSemantics.raw5677`, `OAI.MUB6.Certificate.PairSemantics.raw5677step0`, `OAI.MUB6.Certificate.PairSemantics.raw5678`, `OAI.MUB6.Certificate.PairSemantics.raw5678step0`, `OAI.MUB6.Certificate.PairSemantics.raw5679`, `OAI.MUB6.Certificate.PairSemantics.raw5679step0`, `OAI.MUB6.Certificate.PairSemantics.raw567step0`, `OAI.MUB6.Certificate.PairSemantics.raw568`, `OAI.MUB6.Certificate.PairSemantics.raw5680`, `OAI.MUB6.Certificate.PairSemantics.raw5680step0`, `OAI.MUB6.Certificate.PairSemantics.raw5680step1`, `OAI.MUB6.Certificate.PairSemantics.raw5681`, `OAI.MUB6.Certificate.PairSemantics.raw5682`, `OAI.MUB6.Certificate.PairSemantics.raw5683`, `OAI.MUB6.Certificate.PairSemantics.raw5683step0`, `OAI.MUB6.Certificate.PairSemantics.raw5683step1`, `OAI.MUB6.Certificate.PairSemantics.raw5684`, `OAI.MUB6.Certificate.PairSemantics.raw5684step0`, `OAI.MUB6.Certificate.PairSemantics.raw5685`, `OAI.MUB6.Certificate.PairSemantics.raw5686`, `OAI.MUB6.Certificate.PairSemantics.raw5686step0`, `OAI.MUB6.Certificate.PairSemantics.raw5686step1`, `OAI.MUB6.Certificate.PairSemantics.raw5687`, `OAI.MUB6.Certificate.PairSemantics.raw5688`, `OAI.MUB6.Certificate.PairSemantics.raw5689`, `OAI.MUB6.Certificate.PairSemantics.raw568step0`, `OAI.MUB6.Certificate.PairSemantics.raw568step1`, `OAI.MUB6.Certificate.PairSemantics.raw569`, `OAI.MUB6.Certificate.PairSemantics.raw5690`, `OAI.MUB6.Certificate.PairSemantics.raw5691`, `OAI.MUB6.Certificate.PairSemantics.raw5691step0`, `OAI.MUB6.Certificate.PairSemantics.raw5691step1`, `OAI.MUB6.Certificate.PairSemantics.raw5692`, `OAI.MUB6.Certificate.PairSemantics.raw5693`, `OAI.MUB6.Certificate.PairSemantics.raw5694`, `OAI.MUB6.Certificate.PairSemantics.raw5695`, `OAI.MUB6.Certificate.PairSemantics.raw5695step0`, `OAI.MUB6.Certificate.PairSemantics.raw5695step1`, `OAI.MUB6.Certificate.PairSemantics.raw5696`, `OAI.MUB6.Certificate.PairSemantics.raw5697` and 5735 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_PairSemantics_Canonical0`, `MutuallyUnbiased_PairSemantics_Canonical1`, `MutuallyUnbiased_PairSemantics_Canonical17`, `MutuallyUnbiased_PairSemantics_Canonical177`, `MutuallyUnbiased_PairSemantics_Canonical178`, `MutuallyUnbiased_PairSemantics_Canonical179`, `MutuallyUnbiased_PairSemantics_Canonical18`, `MutuallyUnbiased_PairSemantics_Canonical180`, `MutuallyUnbiased_PairSemantics_Canonical181`, `MutuallyUnbiased_PairSemantics_Canonical182`, `MutuallyUnbiased_PairSemantics_Canonical183`, `MutuallyUnbiased_PairSemantics_Canonical184`, `MutuallyUnbiased_PairSemantics_Canonical185`, `MutuallyUnbiased_PairSemantics_Canonical186`, `MutuallyUnbiased_PairSemantics_Canonical187`, `MutuallyUnbiased_PairSemantics_Canonical188`, `MutuallyUnbiased_PairSemantics_Canonical189`, `MutuallyUnbiased_PairSemantics_Canonical19`, `MutuallyUnbiased_PairSemantics_Canonical190`, `MutuallyUnbiased_PairSemantics_Canonical191`, `MutuallyUnbiased_PairSemantics_Canonical192`, `MutuallyUnbiased_PairSemantics_Canonical193`, `MutuallyUnbiased_PairSemantics_Canonical194`, `MutuallyUnbiased_PairSemantics_Canonical195`, `MutuallyUnbiased_PairSemantics_Canonical196`, `MutuallyUnbiased_PairSemantics_Canonical197`, `MutuallyUnbiased_PairSemantics_Canonical198`, `MutuallyUnbiased_PairSemantics_Canonical199`, `MutuallyUnbiased_PairSemantics_Canonical2`, `MutuallyUnbiased_PairSemantics_Canonical20`, `MutuallyUnbiased_PairSemantics_Canonical200`, `MutuallyUnbiased_PairSemantics_Canonical201`, `MutuallyUnbiased_PairSemantics_Canonical202`, `MutuallyUnbiased_PairSemantics_Canonical203`, `MutuallyUnbiased_PairSemantics_Canonical204`, `MutuallyUnbiased_PairSemantics_Canonical205`, `MutuallyUnbiased_PairSemantics_Canonical206`, `MutuallyUnbiased_PairSemantics_Canonical207`, `MutuallyUnbiased_PairSemantics_Canonical208`, `MutuallyUnbiased_PairSemantics_Canonical209`, `MutuallyUnbiased_PairSemantics_Canonical21`, `MutuallyUnbiased_PairSemantics_Canonical210`, `MutuallyUnbiased_PairSemantics_Canonical211`, `MutuallyUnbiased_PairSemantics_Canonical212`, `MutuallyUnbiased_PairSemantics_Canonical213`, `MutuallyUnbiased_PairSemantics_Canonical214`, `MutuallyUnbiased_PairSemantics_Canonical215`, `MutuallyUnbiased_PairSemantics_Canonical216`, `MutuallyUnbiased_PairSemantics_Canonical217`, `MutuallyUnbiased_PairSemantics_Canonical218`, `MutuallyUnbiased_PairSemantics_Canonical219`, `MutuallyUnbiased_PairSemantics_Canonical22`, `MutuallyUnbiased_PairSemantics_Canonical220`, `MutuallyUnbiased_PairSemantics_Canonical221`, `MutuallyUnbiased_PairSemantics_Canonical222`, `MutuallyUnbiased_PairSemantics_Canonical223`, `MutuallyUnbiased_PairSemantics_Canonical224`, `MutuallyUnbiased_PairSemantics_Canonical225`, `MutuallyUnbiased_PairSemantics_Canonical226`, `MutuallyUnbiased_PairSemantics_Canonical227`, `MutuallyUnbiased_PairSemantics_Canonical228`, `MutuallyUnbiased_PairSemantics_Canonical229`, `MutuallyUnbiased_PairSemantics_Canonical23`, `MutuallyUnbiased_PairSemantics_Canonical230`, `MutuallyUnbiased_PairSemantics_Canonical231`, `MutuallyUnbiased_PairSemantics_Canonical232`, `MutuallyUnbiased_PairSemantics_Canonical233`, `MutuallyUnbiased_PairSemantics_Canonical234`, `MutuallyUnbiased_PairSemantics_Canonical235`, `MutuallyUnbiased_PairSemantics_Canonical236`, `MutuallyUnbiased_PairSemantics_Canonical237`, `MutuallyUnbiased_PairSemantics_Canonical238`, `MutuallyUnbiased_PairSemantics_Canonical239`, `MutuallyUnbiased_PairSemantics_Canonical24`, `MutuallyUnbiased_PairSemantics_Canonical240`, `MutuallyUnbiased_PairSemantics_Canonical241`, `MutuallyUnbiased_PairSemantics_Canonical242`, `MutuallyUnbiased_PairSemantics_Canonical243`, `MutuallyUnbiased_PairSemantics_Canonical244`, `MutuallyUnbiased_PairSemantics_Canonical245`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1162_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1163_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1164_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1165_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1170_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1172_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1265_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1266_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1267_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1298_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1299_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1339_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1340_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1341_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1342_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1343_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1395_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1396_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1397_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1399_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1409_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1410_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1411_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1412_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1414_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1441_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1475_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1477_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1478_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2357_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2358_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2526_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2527_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2528_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2530_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2531_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2570_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2572_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2574_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2576_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2593_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2594_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2595_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2599_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2636_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2766_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2828_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2901_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2903_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2904_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2936_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2937_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2939_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2941_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2943_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2957_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2958_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2959_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2960_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2961_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2963_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2986_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2987_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2988_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2990_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2996_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2998_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3003_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3081_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3082_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3087_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3088_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3089_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3094_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3100_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3106_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3109_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3139_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3140_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3184_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3185_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3190_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3191_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3203_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3204_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3205_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3206_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3209_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3210_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3211_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3223_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3226_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3227_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3711_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3727_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3735_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3737_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3739_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3818_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3821_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3823_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3829_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3830_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3847_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3851_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3852_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3853_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3882_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3925_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3936_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3937_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3938_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3965_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3966_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3967_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3969_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3970_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3977_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3980_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3981_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3982_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3984_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3990_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3992_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3994_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3995_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3998_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4003_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4023_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4026_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4031_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4032_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4033_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4053_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5174_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5387_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5415_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5418_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5439_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5450_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5452_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5464_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5465_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5490_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5492_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound0_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound111_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound12_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound135_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound136_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound137_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound138_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound139_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound140_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound141_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound142_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound143_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound144_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound145_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound146_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound147_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound148_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound149_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound150_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound151_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound16_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound19_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound1_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound20_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound21_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound23_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound28_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound29_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound2_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound30_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound32_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound35_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound36_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound37_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound3_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound41_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound49_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound5_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound61_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound62_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound6_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound78_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound7_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1472_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero14_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero15_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1674_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1785_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero18_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1909_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero488_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero621_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero794_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero818_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound0_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1007_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1008_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound100_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1010_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1013_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1020_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1021_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1093_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1094_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1095_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1096_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1097_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1098_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound10_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1103_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1108_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound110_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1110_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1111_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1115_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound111_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1120_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1121_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1124_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1130_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1131_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound113_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound114_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1159_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound115_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1165_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1166_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1167_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound116_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1170_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1177_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1178_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1179_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1194_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound125_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1261_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1262_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1264_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1266_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1267_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1269_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound126_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1272_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1278_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1279_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound127_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1294_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound12_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1300_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1301_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1303_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1309_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound130_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1310_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1311_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1312_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1318_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1324_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound137_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound138_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound139_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound13_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1409_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound140_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1410_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1411_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1412_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1413_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1414_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1418_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1419_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound141_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1420_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1421_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1423_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1429_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1433_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1434_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1435_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1437_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound143_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1441_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1442_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound144_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1469_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1470_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1477_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1478_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1479_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1480_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1484_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1492_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1493_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1507_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1510_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1511_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1517_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound151_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1521_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound153_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1559_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1560_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1562_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1567_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1568_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1572_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound163_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1648_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1649_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1650_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1651_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1652_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1653_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1654_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1655_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1656_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1662_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1669_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1672_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1686_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound16_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1703_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1708_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1709_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1715_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1717_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1780_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1781_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1782_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1783_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1784_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1786_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1787_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1788_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1789_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1796_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound17_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1816_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1840_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1844_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1845_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1846_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1847_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1849_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1853_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1854_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1855_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1856_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1859_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1866_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1872_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1874_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound188_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1904_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1905_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1907_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1911_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1914_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1915_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1916_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1917_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1925_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1944_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1963_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1964_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1968_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1969_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1972_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1977_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1985_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound199_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound19_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2033_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2034_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2035_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2036_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2037_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2038_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2040_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2046_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2048_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2049_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2050_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2059_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2062_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2075_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2077_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound207_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound213_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound214_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2166_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2168_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2169_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2170_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2171_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2172_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2173_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2174_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2175_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2176_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2178_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2180_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2181_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2182_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2183_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2184_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2185_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2187_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2188_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2189_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2191_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2192_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2193_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2195_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2196_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2197_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2198_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2199_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound21_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2200_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2201_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2202_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2203_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2204_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2205_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2206_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2207_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2208_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2211_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2212_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2214_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2215_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2216_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2217_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2218_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2219_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2220_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2223_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2224_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2225_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2226_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2227_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2228_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2229_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2230_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2231_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2232_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2233_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2235_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2236_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2238_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2240_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2241_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2242_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2244_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2245_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2246_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2247_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2248_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2249_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2250_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2251_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2252_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2253_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2254_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2255_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2256_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2257_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2258_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2259_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2260_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2261_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2262_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2263_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2264_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2265_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2266_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2267_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2268_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound226_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2270_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2271_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2272_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2273_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2274_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2275_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2276_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2278_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2279_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2281_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2282_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2283_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2284_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2285_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2286_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2287_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2288_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2290_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2291_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2292_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2294_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2295_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2296_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2297_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2298_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2299_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound22_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2300_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2301_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2302_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2304_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2305_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2306_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2307_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2308_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2309_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2310_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2311_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2312_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2313_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2314_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2315_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2316_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2317_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2318_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2321_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2322_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2323_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2324_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2325_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2326_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2327_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2328_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2329_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2330_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2331_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2332_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2333_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2334_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2335_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2336_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2337_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2338_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2340_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2341_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2342_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2344_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2345_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2346_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2347_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2348_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2350_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2352_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2353_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2354_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2355_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2356_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2357_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2358_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2361_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2362_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2363_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2364_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2365_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2366_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2367_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2368_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2369_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound236_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2373_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2374_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2375_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2376_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2378_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2379_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2380_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2381_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2382_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2383_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2386_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2387_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2388_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2390_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2391_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2392_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2393_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2394_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2395_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2396_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2397_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2398_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2399_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound23_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2400_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2401_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2402_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2404_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2405_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2406_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2407_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2408_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2409_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2410_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2411_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2412_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2413_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2414_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2415_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2416_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2418_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2419_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2421_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2422_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2423_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2424_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound244_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound245_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound24_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound255_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound267_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound269_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound281_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound282_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound286_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound287_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound28_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound296_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound301_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound310_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound311_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound319_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound327_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound335_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound339_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound340_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound341_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound342_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound343_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound344_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound345_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound353_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound354_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound355_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound356_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound357_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound358_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound359_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound365_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound366_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound367_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound368_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound369_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound370_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound371_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound380_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound388_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound391_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound392_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound395_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound396_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound3_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound404_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound411_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound412_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound413_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound418_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound419_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound427_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound428_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound438_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound444_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound445_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound447_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound448_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound452_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound453_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound454_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound456_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound462_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound463_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound470_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound473_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound474_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound481_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound482_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound483_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound484_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound485_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound497_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound498_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound499_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound4_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound500_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound501_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound504_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound513_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound514_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound515_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound516_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound518_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound519_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound521_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound523_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound524_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound525_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound526_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound531_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound532_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound533_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound534_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound537_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound538_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound539_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound540_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound541_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound542_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound543_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound545_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound546_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound547_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound548_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound551_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound552_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound553_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound554_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound555_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound558_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound564_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound565_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound566_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound567_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound568_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound570_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound571_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound579_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound580_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound581_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound582_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound584_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound585_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound587_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound588_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound589_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound58_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound599_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound5_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound600_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound613_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound614_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound628_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound629_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound630_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound631_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound633_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound635_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound636_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound643_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound644_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound649_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound656_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound657_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound658_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound659_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound663_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound664_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound666_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound667_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound668_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound675_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound683_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound688_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound694_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound6_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound700_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound707_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound711_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound712_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound717_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound718_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound719_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound720_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound722_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound727_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound730_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound731_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound732_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound733_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound734_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound735_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound736_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound737_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound740_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound741_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound742_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound743_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound750_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound751_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound758_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound759_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound769_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound76_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound779_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound780_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound786_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound787_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound788_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound789_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound790_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound792_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound793_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound796_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound797_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound798_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound799_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound7_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound800_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound801_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound802_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound804_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound805_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound813_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound815_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound817_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound822_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound823_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound834_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound841_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound842_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound844_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound847_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound852_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound853_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound857_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound858_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound859_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound863_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound864_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound865_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound866_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound867_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound868_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound872_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound873_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound877_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound878_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound881_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound883_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound884_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound885_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound887_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound888_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound891_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound894_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound897_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound898_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound899_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound902_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound906_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound909_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound911_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound912_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound913_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound917_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound919_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound91_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound922_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound923_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound925_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound926_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound927_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound928_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound929_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound92_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound932_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound933_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound935_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound936_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound937_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound938_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound939_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound940_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound941_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound942_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound947_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound949_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound94_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound950_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound954_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound956_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound959_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound962_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound963_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound964_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound966_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound967_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound968_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound971_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound973_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound975_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound976_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound977_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound97_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound981_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound983_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound987_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound991_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound992_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound99_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound9_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval100_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval105_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1075_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval108_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval111_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval113_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval117_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval118_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1194_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1225_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval122_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval126_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval12_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1315_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval131_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval136_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval137_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval141_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval143_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1465_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval151_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1523_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval152_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1554_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1555_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval155_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval164_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval165_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval169_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval174_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval175_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval181_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval185_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval18_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval190_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval201_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval202_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval211_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval212_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval217_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval21_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval220_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval224_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval226_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval229_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval232_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval234_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval235_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval242_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval246_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval250_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval256_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval260_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval264_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval266_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval268_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval269_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval275_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval280_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval285_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval286_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval287_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval289_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval296_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval301_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval308_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval310_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval316_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval325_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval332_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval335_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval338_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval339_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval341_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval343_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval351_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval352_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval356_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval357_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval358_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval359_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval366_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval369_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval372_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval378_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval37_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval382_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval383_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval385_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval390_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval398_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval39_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval405_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval408_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval413_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval46_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval474_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval476_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval53_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval55_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval56_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval63_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval69_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval73_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval74_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval79_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval84_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval86_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval8_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval92_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval957_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval145_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval147_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval150_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval215_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval216_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval219_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval21_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval220_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval223_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval238_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval373_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval375_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval44_e`, `OAI.MUB6.Certificate.PairSemantics.boundarySound26_e`, `OAI.MUB6.Certificate.PairSemantics.boundarySound49_e`, `OAI.MUB6.Certificate.PairSemantics.boundarySound58_e`, `OAI.MUB6.Certificate.PairSemantics.boundarySound73_e`, `OAI.MUB6.Certificate.PairSemantics.sound1379_e`, `OAI.MUB6.Certificate.PairSemantics.sound1381_e`, `OAI.MUB6.Certificate.PairSemantics.sound1383_e`, `OAI.MUB6.Certificate.PairSemantics.sound1384_e`, `OAI.MUB6.Certificate.PairSemantics.sound1387_e`, `OAI.MUB6.Certificate.PairSemantics.sound1390_e`, `OAI.MUB6.Certificate.PairSemantics.sound1391_e`, `OAI.MUB6.Certificate.PairSemantics.sound1395_e`, `OAI.MUB6.Certificate.PairSemantics.sound1399_e`, `OAI.MUB6.Certificate.PairSemantics.sound1414_e`, `OAI.MUB6.Certificate.PairSemantics.sound1419_e`, `OAI.MUB6.Certificate.PairSemantics.sound1423_e`, `OAI.MUB6.Certificate.PairSemantics.sound1424_e`, `OAI.MUB6.Certificate.PairSemantics.sound1425_e`, `OAI.MUB6.Certificate.PairSemantics.sound1434_e`, `OAI.MUB6.Certificate.PairSemantics.sound1437_e`, `OAI.MUB6.Certificate.PairSemantics.sound1443_e`, `OAI.MUB6.Certificate.PairSemantics.sound1458_e`, `OAI.MUB6.Certificate.PairSemantics.sound1486_e`, `OAI.MUB6.Certificate.PairSemantics.sound1504_e`, `OAI.MUB6.Certificate.PairSemantics.sound1506_e`, `OAI.MUB6.Certificate.PairSemantics.sound1512_e`, `OAI.MUB6.Certificate.PairSemantics.sound1518_e`, `OAI.MUB6.Certificate.PairSemantics.sound1529_e`, `OAI.MUB6.Certificate.PairSemantics.sound1530_e`, `OAI.MUB6.Certificate.PairSemantics.sound1531_e`, `OAI.MUB6.Certificate.PairSemantics.sound1535_e`, `OAI.MUB6.Certificate.PairSemantics.sound1540_e`, `OAI.MUB6.Certificate.PairSemantics.sound1548_e`, `OAI.MUB6.Certificate.PairSemantics.sound1605_e`, `OAI.MUB6.Certificate.PairSemantics.sound1614_e`, `OAI.MUB6.Certificate.PairSemantics.sound1617_e`, `OAI.MUB6.Certificate.PairSemantics.sound1624_e`, `OAI.MUB6.Certificate.PairSemantics.sound1627_e`, `OAI.MUB6.Certificate.PairSemantics.sound1628_e`, `OAI.MUB6.Certificate.PairSemantics.sound1631_e`, `OAI.MUB6.Certificate.PairSemantics.sound1634_e`, `OAI.MUB6.Certificate.PairSemantics.sound1635_e`, `OAI.MUB6.Certificate.PairSemantics.sound1637_e`, `OAI.MUB6.Certificate.PairSemantics.sound1644_e`, `OAI.MUB6.Certificate.PairSemantics.sound1646_e`, `OAI.MUB6.Certificate.PairSemantics.sound1648_e`, `OAI.MUB6.Certificate.PairSemantics.sound1685_e`, `OAI.MUB6.Certificate.PairSemantics.sound1716_e`, `OAI.MUB6.Certificate.PairSemantics.sound1736_e`, `OAI.MUB6.Certificate.PairSemantics.sound1739_e`, `OAI.MUB6.Certificate.PairSemantics.sound1768_e`, `OAI.MUB6.Certificate.PairSemantics.sound1770_e`, `OAI.MUB6.Certificate.PairSemantics.sound1793_e`, `OAI.MUB6.Certificate.PairSemantics.sound1800_e`, `OAI.MUB6.Certificate.PairSemantics.sound1828_e`, `OAI.MUB6.Certificate.PairSemantics.sound1849_e`, `OAI.MUB6.Certificate.PairSemantics.sound1858_e`, `OAI.MUB6.Certificate.PairSemantics.sound1860_e`, `OAI.MUB6.Certificate.PairSemantics.sound1865_e`, `OAI.MUB6.Certificate.PairSemantics.sound1866_e`, `OAI.MUB6.Certificate.PairSemantics.sound1867_e`, `OAI.MUB6.Certificate.PairSemantics.sound1869_e`, `OAI.MUB6.Certificate.PairSemantics.sound1870_e`, `OAI.MUB6.Certificate.PairSemantics.sound1872_e`, `OAI.MUB6.Certificate.PairSemantics.sound1875_e`, `OAI.MUB6.Certificate.PairSemantics.sound1876_e`, `OAI.MUB6.Certificate.PairSemantics.sound1879_e`, `OAI.MUB6.Certificate.PairSemantics.sound1885_e`, `OAI.MUB6.Certificate.PairSemantics.sound1978_e`, `OAI.MUB6.Certificate.PairSemantics.sound1980_e`, `OAI.MUB6.Certificate.PairSemantics.sound1986_e`, `OAI.MUB6.Certificate.PairSemantics.sound1987_e`, `OAI.MUB6.Certificate.PairSemantics.sound2041_e`, `OAI.MUB6.Certificate.PairSemantics.sound2058_e`, `OAI.MUB6.Certificate.PairSemantics.sound2071_e`, `OAI.MUB6.Certificate.PairSemantics.sound2097_e`, `OAI.MUB6.Certificate.PairSemantics.sound2106_e`, `OAI.MUB6.Certificate.PairSemantics.sound2107_e`, `OAI.MUB6.Certificate.PairSemantics.sound2108_e`, `OAI.MUB6.Certificate.PairSemantics.sound2117_e`, `OAI.MUB6.Certificate.PairSemantics.sound2122_e`, `OAI.MUB6.Certificate.PairSemantics.sound2123_e`, `OAI.MUB6.Certificate.PairSemantics.sound2128_e`, `OAI.MUB6.Certificate.PairSemantics.sound2132_e`, `OAI.MUB6.Certificate.PairSemantics.sound2152_e`, `OAI.MUB6.Certificate.PairSemantics.sound2168_e`, `OAI.MUB6.Certificate.PairSemantics.sound2175_e`, `OAI.MUB6.Certificate.PairSemantics.sound2177_e`, `OAI.MUB6.Certificate.PairSemantics.sound2189_e`, `OAI.MUB6.Certificate.PairSemantics.sound2190_e`, `OAI.MUB6.Certificate.PairSemantics.sound2197_e`, `OAI.MUB6.Certificate.PairSemantics.sound2201_e`, `OAI.MUB6.Certificate.PairSemantics.sound2202_e`, `OAI.MUB6.Certificate.PairSemantics.sound2213_e`, `OAI.MUB6.Certificate.PairSemantics.sound2228_e`, `OAI.MUB6.Certificate.PairSemantics.sound2244_e`, `OAI.MUB6.Certificate.PairSemantics.sound2262_e`, `OAI.MUB6.Certificate.PairSemantics.sound2284_e`, `OAI.MUB6.Certificate.PairSemantics.sound2286_e`, `OAI.MUB6.Certificate.PairSemantics.sound2293_e`, `OAI.MUB6.Certificate.PairSemantics.sound2294_e`, `OAI.MUB6.Certificate.PairSemantics.sound2295_e`, `OAI.MUB6.Certificate.PairSemantics.sound2296_e`, `OAI.MUB6.Certificate.PairSemantics.sound2312_e`, `OAI.MUB6.Certificate.PairSemantics.sound2324_e`, `OAI.MUB6.Certificate.PairSemantics.sound2327_e`, `OAI.MUB6.Certificate.PairSemantics.sound2338_e`, `OAI.MUB6.Certificate.PairSemantics.sound2375_e`, `OAI.MUB6.Certificate.PairSemantics.sound2382_e`, `OAI.MUB6.Certificate.PairSemantics.sound2390_e`, `OAI.MUB6.Certificate.PairSemantics.sound2391_e`, `OAI.MUB6.Certificate.PairSemantics.sound2394_e`, `OAI.MUB6.Certificate.PairSemantics.sound2399_e`, `OAI.MUB6.Certificate.PairSemantics.sound2400_e`, `OAI.MUB6.Certificate.PairSemantics.sound2401_e`, `OAI.MUB6.Certificate.PairSemantics.sound2403_e`, `OAI.MUB6.Certificate.PairSemantics.sound2415_e`, `OAI.MUB6.Certificate.PairSemantics.sound2416_e`, `OAI.MUB6.Certificate.PairSemantics.sound2420_e`, `OAI.MUB6.Certificate.PairSemantics.sound2433_e`, `OAI.MUB6.Certificate.PairSemantics.sound2434_e`, `OAI.MUB6.Certificate.PairSemantics.sound2435_e`, `OAI.MUB6.Certificate.PairSemantics.sound2436_e`, `OAI.MUB6.Certificate.PairSemantics.sound2442_e`, `OAI.MUB6.Certificate.PairSemantics.sound2444_e`, `OAI.MUB6.Certificate.PairSemantics.sound2445_e`, `OAI.MUB6.Certificate.PairSemantics.sound2454_e`, `OAI.MUB6.Certificate.PairSemantics.sound2456_e`, `OAI.MUB6.Certificate.PairSemantics.sound2457_e`, `OAI.MUB6.Certificate.PairSemantics.sound2463_e`, `OAI.MUB6.Certificate.PairSemantics.sound2464_e`, `OAI.MUB6.Certificate.PairSemantics.sound2465_e`, `OAI.MUB6.Certificate.PairSemantics.sound2472_e`, `OAI.MUB6.Certificate.PairSemantics.sound2473_e`, `OAI.MUB6.Certificate.PairSemantics.sound2477_e`, `OAI.MUB6.Certificate.PairSemantics.sound2479_e`, `OAI.MUB6.Certificate.PairSemantics.sound2489_e`, `OAI.MUB6.Certificate.PairSemantics.sound2490_e`, `OAI.MUB6.Certificate.PairSemantics.sound2491_e`, `OAI.MUB6.Certificate.PairSemantics.sound2492_e`, `OAI.MUB6.Certificate.PairSemantics.sound2507_e`, `OAI.MUB6.Certificate.PairSemantics.sound2520_e`, `OAI.MUB6.Certificate.PairSemantics.sound2521_e`, `OAI.MUB6.Certificate.PairSemantics.sound2522_e`, `OAI.MUB6.Certificate.PairSemantics.sound2524_e`, `OAI.MUB6.Certificate.PairSemantics.sound2525_e`, `OAI.MUB6.Certificate.PairSemantics.sound2527_e`, `OAI.MUB6.Certificate.PairSemantics.sound2533_e`, `OAI.MUB6.Certificate.PairSemantics.sound2540_e`, `OAI.MUB6.Certificate.PairSemantics.sound2546_e`, `OAI.MUB6.Certificate.PairSemantics.sound2547_e`, `OAI.MUB6.Certificate.PairSemantics.sound2548_e`, `OAI.MUB6.Certificate.PairSemantics.sound2557_e`, `OAI.MUB6.Certificate.PairSemantics.sound2558_e`, `OAI.MUB6.Certificate.PairSemantics.sound2559_e`, `OAI.MUB6.Certificate.PairSemantics.sound2564_e`, `OAI.MUB6.Certificate.PairSemantics.sound2565_e`, `OAI.MUB6.Certificate.PairSemantics.sound2566_e`, `OAI.MUB6.Certificate.PairSemantics.sound2573_e`, `OAI.MUB6.Certificate.PairSemantics.sound2578_e`, `OAI.MUB6.Certificate.PairSemantics.sound2580_e`, `OAI.MUB6.Certificate.PairSemantics.sound2593_e`, `OAI.MUB6.Certificate.PairSemantics.sound2602_e`, `OAI.MUB6.Certificate.PairSemantics.sound2604_e`, `OAI.MUB6.Certificate.PairSemantics.sound2606_e`, `OAI.MUB6.Certificate.PairSemantics.sound2619_e`, `OAI.MUB6.Certificate.PairSemantics.sound2620_e`, `OAI.MUB6.Certificate.PairSemantics.sound2623_e`, `OAI.MUB6.Certificate.PairSemantics.sound2627_e`, `OAI.MUB6.Certificate.PairSemantics.sound2641_e`, `OAI.MUB6.Certificate.PairSemantics.sound2657_e`, `OAI.MUB6.Certificate.PairSemantics.sound2658_e`, `OAI.MUB6.Certificate.PairSemantics.sound2661_e`, `OAI.MUB6.Certificate.PairSemantics.sound2666_e`, `OAI.MUB6.Certificate.PairSemantics.sound2669_e`, `OAI.MUB6.Certificate.PairSemantics.sound2670_e`, `OAI.MUB6.Certificate.PairSemantics.sound2671_e`, `OAI.MUB6.Certificate.PairSemantics.sound2686_e`, `OAI.MUB6.Certificate.PairSemantics.sound2690_e`, `OAI.MUB6.Certificate.PairSemantics.sound2693_e`, `OAI.MUB6.Certificate.PairSemantics.sound2698_e`, `OAI.MUB6.Certificate.PairSemantics.sound2708_e`, `OAI.MUB6.Certificate.PairSemantics.sound2710_e`, `OAI.MUB6.Certificate.PairSemantics.sound2714_e`, `OAI.MUB6.Certificate.PairSemantics.sound2729_e`, `OAI.MUB6.Certificate.PairSemantics.sound2732_e`, `OAI.MUB6.Certificate.PairSemantics.sound2733_e`, `OAI.MUB6.Certificate.PairSemantics.sound2735_e`, `OAI.MUB6.Certificate.PairSemantics.sound2754_e`, `OAI.MUB6.Certificate.PairSemantics.sound2757_e`, `OAI.MUB6.Certificate.PairSemantics.sound2788_e`, `OAI.MUB6.Certificate.PairSemantics.sound2790_e`, `OAI.MUB6.Certificate.PairSemantics.sound2793_e`, `OAI.MUB6.Certificate.PairSemantics.sound2807_e`, `OAI.MUB6.Certificate.PairSemantics.sound2817_e`, `OAI.MUB6.Certificate.PairSemantics.sound2829_e`, `OAI.MUB6.Certificate.PairSemantics.sound2836_e`, `OAI.MUB6.Certificate.PairSemantics.sound2845_e`, `OAI.MUB6.Certificate.PairSemantics.sound2853_e`, `OAI.MUB6.Certificate.PairSemantics.sound2854_e`, `OAI.MUB6.Certificate.PairSemantics.sound2858_e`, `OAI.MUB6.Certificate.PairSemantics.sound2863_e`, `OAI.MUB6.Certificate.PairSemantics.sound2864_e`, `OAI.MUB6.Certificate.PairSemantics.sound2865_e`, `OAI.MUB6.Certificate.PairSemantics.sound2866_e`, `OAI.MUB6.Certificate.PairSemantics.sound2867_e`, `OAI.MUB6.Certificate.PairSemantics.sound2868_e`, `OAI.MUB6.Certificate.PairSemantics.sound2872_e`, `OAI.MUB6.Certificate.PairSemantics.sound2873_e`, `OAI.MUB6.Certificate.PairSemantics.sound2874_e`, `OAI.MUB6.Certificate.PairSemantics.sound2875_e`, `OAI.MUB6.Certificate.PairSemantics.sound2878_e`, `OAI.MUB6.Certificate.PairSemantics.sound2879_e`, `OAI.MUB6.Certificate.PairSemantics.sound2880_e`, `OAI.MUB6.Certificate.PairSemantics.sound2882_e`, `OAI.MUB6.Certificate.PairSemantics.sound2883_e`, `OAI.MUB6.Certificate.PairSemantics.sound2884_e`, `OAI.MUB6.Certificate.PairSemantics.sound2887_e`, `OAI.MUB6.Certificate.PairSemantics.sound2888_e`, `OAI.MUB6.Certificate.PairSemantics.sound2889_e`, `OAI.MUB6.Certificate.PairSemantics.sound2890_e`, `OAI.MUB6.Certificate.PairSemantics.sound2891_e`, `OAI.MUB6.Certificate.PairSemantics.sound2892_e`, `OAI.MUB6.Certificate.PairSemantics.sound2894_e`, `OAI.MUB6.Certificate.PairSemantics.sound2895_e`, `OAI.MUB6.Certificate.PairSemantics.sound2896_e`, `OAI.MUB6.Certificate.PairSemantics.sound2897_e`, `OAI.MUB6.Certificate.PairSemantics.sound2898_e`, `OAI.MUB6.Certificate.PairSemantics.sound2899_e`, `OAI.MUB6.Certificate.PairSemantics.sound2900_e`, `OAI.MUB6.Certificate.PairSemantics.sound2901_e`, `OAI.MUB6.Certificate.PairSemantics.sound2902_e`, `OAI.MUB6.Certificate.PairSemantics.sound2904_e`, `OAI.MUB6.Certificate.PairSemantics.sound2905_e`, `OAI.MUB6.Certificate.PairSemantics.sound2906_e`, `OAI.MUB6.Certificate.PairSemantics.sound2908_e`, `OAI.MUB6.Certificate.PairSemantics.sound2909_e`, `OAI.MUB6.Certificate.PairSemantics.sound2910_e`, `OAI.MUB6.Certificate.PairSemantics.sound2912_e`, `OAI.MUB6.Certificate.PairSemantics.sound2913_e`, `OAI.MUB6.Certificate.PairSemantics.sound2914_e`, `OAI.MUB6.Certificate.PairSemantics.sound2915_e`, `OAI.MUB6.Certificate.PairSemantics.sound2916_e`, `OAI.MUB6.Certificate.PairSemantics.sound2917_e`, `OAI.MUB6.Certificate.PairSemantics.sound2919_e`, `OAI.MUB6.Certificate.PairSemantics.sound2920_e`, `OAI.MUB6.Certificate.PairSemantics.sound2922_e`, `OAI.MUB6.Certificate.PairSemantics.sound2924_e`, `OAI.MUB6.Certificate.PairSemantics.sound2925_e`, `OAI.MUB6.Certificate.PairSemantics.sound2926_e`, `OAI.MUB6.Certificate.PairSemantics.sound2927_e`, `OAI.MUB6.Certificate.PairSemantics.sound2928_e`, `OAI.MUB6.Certificate.PairSemantics.sound2929_e`, `OAI.MUB6.Certificate.PairSemantics.sound2931_e`, `OAI.MUB6.Certificate.PairSemantics.sound2933_e`, `OAI.MUB6.Certificate.PairSemantics.sound2935_e`, `OAI.MUB6.Certificate.PairSemantics.sound2936_e`, `OAI.MUB6.Certificate.PairSemantics.sound2939_e`, `OAI.MUB6.Certificate.PairSemantics.sound2940_e`, `OAI.MUB6.Certificate.PairSemantics.sound2941_e`, `OAI.MUB6.Certificate.PairSemantics.sound2942_e`, `OAI.MUB6.Certificate.PairSemantics.sound2943_e`, `OAI.MUB6.Certificate.PairSemantics.sound2944_e`, `OAI.MUB6.Certificate.PairSemantics.sound2946_e`, `OAI.MUB6.Certificate.PairSemantics.sound2949_e`, `OAI.MUB6.Certificate.PairSemantics.sound2950_e`, `OAI.MUB6.Certificate.PairSemantics.sound2951_e`, `OAI.MUB6.Certificate.PairSemantics.sound2952_e`, `OAI.MUB6.Certificate.PairSemantics.sound2953_e`, `OAI.MUB6.Certificate.PairSemantics.sound2954_e`, `OAI.MUB6.Certificate.PairSemantics.sound2956_e`, `OAI.MUB6.Certificate.PairSemantics.sound2957_e`, `OAI.MUB6.Certificate.PairSemantics.sound2959_e`, `OAI.MUB6.Certificate.PairSemantics.sound2960_e`, `OAI.MUB6.Certificate.PairSemantics.sound2961_e`, `OAI.MUB6.Certificate.PairSemantics.sound2962_e`, `OAI.MUB6.Certificate.PairSemantics.sound2963_e`, `OAI.MUB6.Certificate.PairSemantics.sound2964_e`, `OAI.MUB6.Certificate.PairSemantics.sound2965_e`, `OAI.MUB6.Certificate.PairSemantics.sound2966_e`, `OAI.MUB6.Certificate.PairSemantics.sound2967_e`, `OAI.MUB6.Certificate.PairSemantics.sound2968_e`, `OAI.MUB6.Certificate.PairSemantics.sound2969_e`, `OAI.MUB6.Certificate.PairSemantics.sound2970_e`, `OAI.MUB6.Certificate.PairSemantics.sound2972_e`, `OAI.MUB6.Certificate.PairSemantics.sound2973_e`, `OAI.MUB6.Certificate.PairSemantics.sound2974_e`, `OAI.MUB6.Certificate.PairSemantics.sound2975_e`, `OAI.MUB6.Certificate.PairSemantics.sound2976_e`, `OAI.MUB6.Certificate.PairSemantics.sound2977_e`, `OAI.MUB6.Certificate.PairSemantics.sound2979_e`, `OAI.MUB6.Certificate.PairSemantics.sound2980_e`, `OAI.MUB6.Certificate.PairSemantics.sound2984_e`, `OAI.MUB6.Certificate.PairSemantics.sound2985_e`, `OAI.MUB6.Certificate.PairSemantics.sound2986_e`, `OAI.MUB6.Certificate.PairSemantics.sound2987_e`, `OAI.MUB6.Certificate.PairSemantics.sound2989_e`, `OAI.MUB6.Certificate.PairSemantics.sound2990_e`, `OAI.MUB6.Certificate.PairSemantics.sound2991_e`, `OAI.MUB6.Certificate.PairSemantics.sound2992_e`, `OAI.MUB6.Certificate.PairSemantics.sound2994_e`, `OAI.MUB6.Certificate.PairSemantics.sound2996_e`, `OAI.MUB6.Certificate.PairSemantics.sound2997_e`, `OAI.MUB6.Certificate.PairSemantics.sound2998_e`, `OAI.MUB6.Certificate.PairSemantics.sound2999_e`, `OAI.MUB6.Certificate.PairSemantics.sound3000_e`, `OAI.MUB6.Certificate.PairSemantics.sound3001_e`, `OAI.MUB6.Certificate.PairSemantics.sound3002_e`, `OAI.MUB6.Certificate.PairSemantics.sound3004_e`, `OAI.MUB6.Certificate.PairSemantics.sound3006_e`, `OAI.MUB6.Certificate.PairSemantics.sound3007_e`, `OAI.MUB6.Certificate.PairSemantics.sound3009_e`, `OAI.MUB6.Certificate.PairSemantics.sound3011_e`, `OAI.MUB6.Certificate.PairSemantics.sound3012_e`, `OAI.MUB6.Certificate.PairSemantics.sound3013_e`, `OAI.MUB6.Certificate.PairSemantics.sound3014_e`, `OAI.MUB6.Certificate.PairSemantics.sound3015_e`, `OAI.MUB6.Certificate.PairSemantics.sound3016_e`, `OAI.MUB6.Certificate.PairSemantics.sound3017_e`, `OAI.MUB6.Certificate.PairSemantics.sound3018_e`, `OAI.MUB6.Certificate.PairSemantics.sound3019_e`, `OAI.MUB6.Certificate.PairSemantics.sound3020_e`, `OAI.MUB6.Certificate.PairSemantics.sound3021_e`, `OAI.MUB6.Certificate.PairSemantics.sound3022_e`, `OAI.MUB6.Certificate.PairSemantics.sound3023_e`, `OAI.MUB6.Certificate.PairSemantics.sound3024_e`, `OAI.MUB6.Certificate.PairSemantics.sound3025_e`, `OAI.MUB6.Certificate.PairSemantics.sound3026_e`, `OAI.MUB6.Certificate.PairSemantics.sound3027_e`, `OAI.MUB6.Certificate.PairSemantics.sound3028_e`, `OAI.MUB6.Certificate.PairSemantics.sound3029_e`, `OAI.MUB6.Certificate.PairSemantics.sound3030_e`, `OAI.MUB6.Certificate.PairSemantics.sound3032_e`, `OAI.MUB6.Certificate.PairSemantics.sound3034_e`, `OAI.MUB6.Certificate.PairSemantics.sound3035_e`, `OAI.MUB6.Certificate.PairSemantics.sound3036_e`, `OAI.MUB6.Certificate.PairSemantics.sound3037_e`, `OAI.MUB6.Certificate.PairSemantics.sound3038_e`, `OAI.MUB6.Certificate.PairSemantics.sound3039_e`, `OAI.MUB6.Certificate.PairSemantics.sound3040_e`, `OAI.MUB6.Certificate.PairSemantics.sound3041_e`, `OAI.MUB6.Certificate.PairSemantics.sound3042_e`, `OAI.MUB6.Certificate.PairSemantics.sound3045_e`, `OAI.MUB6.Certificate.PairSemantics.sound3049_e`, `OAI.MUB6.Certificate.PairSemantics.sound3050_e`, `OAI.MUB6.Certificate.PairSemantics.sound3051_e`, `OAI.MUB6.Certificate.PairSemantics.sound3052_e`, `OAI.MUB6.Certificate.PairSemantics.sound3053_e`, `OAI.MUB6.Certificate.PairSemantics.sound3054_e`, `OAI.MUB6.Certificate.PairSemantics.sound3055_e`, `OAI.MUB6.Certificate.PairSemantics.sound3057_e`, `OAI.MUB6.Certificate.PairSemantics.sound3059_e`, `OAI.MUB6.Certificate.PairSemantics.sound3060_e`, `OAI.MUB6.Certificate.PairSemantics.sound3061_e`, `OAI.MUB6.Certificate.PairSemantics.sound3062_e`, `OAI.MUB6.Certificate.PairSemantics.sound3063_e`, `OAI.MUB6.Certificate.PairSemantics.sound3065_e`, `OAI.MUB6.Certificate.PairSemantics.sound3066_e`, `OAI.MUB6.Certificate.PairSemantics.sound3067_e`, `OAI.MUB6.Certificate.PairSemantics.sound3068_e`, `OAI.MUB6.Certificate.PairSemantics.sound3069_e`, `OAI.MUB6.Certificate.PairSemantics.sound3071_e`, `OAI.MUB6.Certificate.PairSemantics.sound3072_e`, `OAI.MUB6.Certificate.PairSemantics.sound3073_e`, `OAI.MUB6.Certificate.PairSemantics.sound3074_e`, `OAI.MUB6.Certificate.PairSemantics.sound3075_e`, `OAI.MUB6.Certificate.PairSemantics.sound3076_e`, `OAI.MUB6.Certificate.PairSemantics.sound3077_e`, `OAI.MUB6.Certificate.PairSemantics.sound3078_e`, `OAI.MUB6.Certificate.PairSemantics.sound3079_e`, `OAI.MUB6.Certificate.PairSemantics.sound3081_e`, `OAI.MUB6.Certificate.PairSemantics.sound3082_e`, `OAI.MUB6.Certificate.PairSemantics.sound3084_e`, `OAI.MUB6.Certificate.PairSemantics.sound3085_e`, `OAI.MUB6.Certificate.PairSemantics.sound3086_e`, `OAI.MUB6.Certificate.PairSemantics.sound3087_e`, `OAI.MUB6.Certificate.PairSemantics.sound3088_e`, `OAI.MUB6.Certificate.PairSemantics.sound3090_e`, `OAI.MUB6.Certificate.PairSemantics.sound3091_e`, `OAI.MUB6.Certificate.PairSemantics.sound3092_e`, `OAI.MUB6.Certificate.PairSemantics.sound3093_e`, `OAI.MUB6.Certificate.PairSemantics.sound3094_e`, `OAI.MUB6.Certificate.PairSemantics.sound3095_e`, `OAI.MUB6.Certificate.PairSemantics.sound3096_e`, `OAI.MUB6.Certificate.PairSemantics.sound3098_e`, `OAI.MUB6.Certificate.PairSemantics.sound3099_e`, `OAI.MUB6.Certificate.PairSemantics.sound3100_e`, `OAI.MUB6.Certificate.PairSemantics.sound3101_e`, `OAI.MUB6.Certificate.PairSemantics.sound3105_e`, `OAI.MUB6.Certificate.PairSemantics.sound3106_e`, `OAI.MUB6.Certificate.PairSemantics.sound3107_e`, `OAI.MUB6.Certificate.PairSemantics.sound3108_e`, `OAI.MUB6.Certificate.PairSemantics.sound3110_e`, `OAI.MUB6.Certificate.PairSemantics.sound3111_e`, `OAI.MUB6.Certificate.PairSemantics.sound3112_e`, `OAI.MUB6.Certificate.PairSemantics.sound3113_e`, `OAI.MUB6.Certificate.PairSemantics.sound3114_e`, `OAI.MUB6.Certificate.PairSemantics.sound3115_e`, `OAI.MUB6.Certificate.PairSemantics.sound3118_e`, `OAI.MUB6.Certificate.PairSemantics.sound3119_e`, `OAI.MUB6.Certificate.PairSemantics.sound3120_e`, `OAI.MUB6.Certificate.PairSemantics.sound3122_e`, `OAI.MUB6.Certificate.PairSemantics.sound3123_e`, `OAI.MUB6.Certificate.PairSemantics.sound3124_e`, `OAI.MUB6.Certificate.PairSemantics.sound3125_e`, `OAI.MUB6.Certificate.PairSemantics.sound3127_e`, `OAI.MUB6.Certificate.PairSemantics.sound3128_e`, `OAI.MUB6.Certificate.PairSemantics.sound3129_e`, `OAI.MUB6.Certificate.PairSemantics.sound3130_e`, `OAI.MUB6.Certificate.PairSemantics.sound3131_e`, `OAI.MUB6.Certificate.PairSemantics.sound3132_e`, `OAI.MUB6.Certificate.PairSemantics.sound3133_e`, `OAI.MUB6.Certificate.PairSemantics.sound3135_e`, `OAI.MUB6.Certificate.PairSemantics.sound3136_e`, `OAI.MUB6.Certificate.PairSemantics.sound3137_e`, `OAI.MUB6.Certificate.PairSemantics.sound3138_e`, `OAI.MUB6.Certificate.PairSemantics.sound3139_e`, `OAI.MUB6.Certificate.PairSemantics.sound3140_e`, `OAI.MUB6.Certificate.PairSemantics.sound3141_e`, `OAI.MUB6.Certificate.PairSemantics.sound3142_e`, `OAI.MUB6.Certificate.PairSemantics.sound3144_e`, `OAI.MUB6.Certificate.PairSemantics.sound3145_e`, `OAI.MUB6.Certificate.PairSemantics.sound3146_e`, `OAI.MUB6.Certificate.PairSemantics.sound3149_e`, `OAI.MUB6.Certificate.PairSemantics.sound3150_e`, `OAI.MUB6.Certificate.PairSemantics.sound3151_e`, `OAI.MUB6.Certificate.PairSemantics.sound3152_e`, `OAI.MUB6.Certificate.PairSemantics.sound3153_e`, `OAI.MUB6.Certificate.PairSemantics.sound3154_e`, `OAI.MUB6.Certificate.PairSemantics.sound3158_e`, `OAI.MUB6.Certificate.PairSemantics.sound3159_e`, `OAI.MUB6.Certificate.PairSemantics.sound3160_e`, `OAI.MUB6.Certificate.PairSemantics.sound3161_e`, `OAI.MUB6.Certificate.PairSemantics.sound3163_e`, `OAI.MUB6.Certificate.PairSemantics.sound3164_e`, `OAI.MUB6.Certificate.PairSemantics.sound3166_e`, `OAI.MUB6.Certificate.PairSemantics.sound3167_e`, `OAI.MUB6.Certificate.PairSemantics.sound3169_e`, `OAI.MUB6.Certificate.PairSemantics.sound3170_e`, `OAI.MUB6.Certificate.PairSemantics.sound3171_e`, `OAI.MUB6.Certificate.PairSemantics.sound3172_e`, `OAI.MUB6.Certificate.PairSemantics.sound3173_e`, `OAI.MUB6.Certificate.PairSemantics.sound3174_e`, `OAI.MUB6.Certificate.PairSemantics.sound3176_e`, `OAI.MUB6.Certificate.PairSemantics.sound3178_e`, `OAI.MUB6.Certificate.PairSemantics.sound3179_e`, `OAI.MUB6.Certificate.PairSemantics.sound3180_e`, `OAI.MUB6.Certificate.PairSemantics.sound3181_e`, `OAI.MUB6.Certificate.PairSemantics.sound3183_e`, `OAI.MUB6.Certificate.PairSemantics.sound3184_e`, `OAI.MUB6.Certificate.PairSemantics.sound3185_e`, `OAI.MUB6.Certificate.PairSemantics.sound3187_e`, `OAI.MUB6.Certificate.PairSemantics.sound3188_e`, `OAI.MUB6.Certificate.PairSemantics.sound3189_e`, `OAI.MUB6.Certificate.PairSemantics.sound3191_e`, `OAI.MUB6.Certificate.PairSemantics.sound3192_e`, `OAI.MUB6.Certificate.PairSemantics.sound3193_e`, `OAI.MUB6.Certificate.PairSemantics.sound3194_e`, `OAI.MUB6.Certificate.PairSemantics.sound3195_e`, `OAI.MUB6.Certificate.PairSemantics.sound3196_e`, `OAI.MUB6.Certificate.PairSemantics.sound3197_e`, `OAI.MUB6.Certificate.PairSemantics.sound3198_e`, `OAI.MUB6.Certificate.PairSemantics.sound3199_e`, `OAI.MUB6.Certificate.PairSemantics.sound3200_e`, `OAI.MUB6.Certificate.PairSemantics.sound3201_e`, `OAI.MUB6.Certificate.PairSemantics.sound3202_e`, `OAI.MUB6.Certificate.PairSemantics.sound3203_e`, `OAI.MUB6.Certificate.PairSemantics.sound3204_e`, `OAI.MUB6.Certificate.PairSemantics.sound3205_e`, `OAI.MUB6.Certificate.PairSemantics.sound3206_e`, `OAI.MUB6.Certificate.PairSemantics.sound3208_e`, `OAI.MUB6.Certificate.PairSemantics.sound3209_e`, `OAI.MUB6.Certificate.PairSemantics.sound3211_e`, `OAI.MUB6.Certificate.PairSemantics.sound3212_e`, `OAI.MUB6.Certificate.PairSemantics.sound3213_e`, `OAI.MUB6.Certificate.PairSemantics.sound3215_e`, `OAI.MUB6.Certificate.PairSemantics.sound3216_e`, `OAI.MUB6.Certificate.PairSemantics.sound3218_e`, `OAI.MUB6.Certificate.PairSemantics.sound3220_e`, `OAI.MUB6.Certificate.PairSemantics.sound3221_e`, `OAI.MUB6.Certificate.PairSemantics.sound3222_e`, `OAI.MUB6.Certificate.PairSemantics.sound3223_e`, `OAI.MUB6.Certificate.PairSemantics.sound3224_e`, `OAI.MUB6.Certificate.PairSemantics.sound3225_e`, `OAI.MUB6.Certificate.PairSemantics.sound3226_e`, `OAI.MUB6.Certificate.PairSemantics.sound3227_e`, `OAI.MUB6.Certificate.PairSemantics.sound3228_e`, `OAI.MUB6.Certificate.PairSemantics.sound3229_e`, `OAI.MUB6.Certificate.PairSemantics.sound3230_e`, `OAI.MUB6.Certificate.PairSemantics.sound3233_e`, `OAI.MUB6.Certificate.PairSemantics.sound3234_e`, `OAI.MUB6.Certificate.PairSemantics.sound3235_e`, `OAI.MUB6.Certificate.PairSemantics.sound3237_e`, `OAI.MUB6.Certificate.PairSemantics.sound3238_e`, `OAI.MUB6.Certificate.PairSemantics.sound3240_e`, `OAI.MUB6.Certificate.PairSemantics.sound3242_e`, `OAI.MUB6.Certificate.PairSemantics.sound3243_e`, `OAI.MUB6.Certificate.PairSemantics.sound3244_e`, `OAI.MUB6.Certificate.PairSemantics.sound3246_e`, `OAI.MUB6.Certificate.PairSemantics.sound3247_e`, `OAI.MUB6.Certificate.PairSemantics.sound3248_e`, `OAI.MUB6.Certificate.PairSemantics.sound3249_e`, `OAI.MUB6.Certificate.PairSemantics.sound3253_e`, `OAI.MUB6.Certificate.PairSemantics.sound3254_e`, `OAI.MUB6.Certificate.PairSemantics.sound3255_e`, `OAI.MUB6.Certificate.PairSemantics.sound3256_e`, `OAI.MUB6.Certificate.PairSemantics.sound3258_e`, `OAI.MUB6.Certificate.PairSemantics.sound3260_e`, `OAI.MUB6.Certificate.PairSemantics.sound3262_e`, `OAI.MUB6.Certificate.PairSemantics.sound3263_e`, `OAI.MUB6.Certificate.PairSemantics.sound3264_e`, `OAI.MUB6.Certificate.PairSemantics.sound3266_e`, `OAI.MUB6.Certificate.PairSemantics.sound3267_e`, `OAI.MUB6.Certificate.PairSemantics.sound3268_e`, `OAI.MUB6.Certificate.PairSemantics.sound3269_e`, `OAI.MUB6.Certificate.PairSemantics.sound3271_e`, `OAI.MUB6.Certificate.PairSemantics.sound3272_e`, `OAI.MUB6.Certificate.PairSemantics.sound3273_e`, `OAI.MUB6.Certificate.PairSemantics.sound3274_e`, `OAI.MUB6.Certificate.PairSemantics.sound3275_e`, `OAI.MUB6.Certificate.PairSemantics.sound3276_e`, `OAI.MUB6.Certificate.PairSemantics.sound3277_e`, `OAI.MUB6.Certificate.PairSemantics.sound3278_e`, `OAI.MUB6.Certificate.PairSemantics.sound3279_e`, `OAI.MUB6.Certificate.PairSemantics.sound3280_e`, `OAI.MUB6.Certificate.PairSemantics.sound3281_e`, `OAI.MUB6.Certificate.PairSemantics.sound3282_e`, `OAI.MUB6.Certificate.PairSemantics.sound3283_e`, `OAI.MUB6.Certificate.PairSemantics.sound3284_e`, `OAI.MUB6.Certificate.PairSemantics.sound3288_e`, `OAI.MUB6.Certificate.PairSemantics.sound3289_e`, `OAI.MUB6.Certificate.PairSemantics.sound3290_e`, `OAI.MUB6.Certificate.PairSemantics.sound3291_e`, `OAI.MUB6.Certificate.PairSemantics.sound3292_e`, `OAI.MUB6.Certificate.PairSemantics.sound3293_e`, `OAI.MUB6.Certificate.PairSemantics.sound3294_e`, `OAI.MUB6.Certificate.PairSemantics.sound3295_e`, `OAI.MUB6.Certificate.PairSemantics.sound3296_e`, `OAI.MUB6.Certificate.PairSemantics.sound3297_e`, `OAI.MUB6.Certificate.PairSemantics.sound3298_e`, `OAI.MUB6.Certificate.PairSemantics.sound3299_e`, `OAI.MUB6.Certificate.PairSemantics.sound3300_e`, `OAI.MUB6.Certificate.PairSemantics.sound3301_e`, `OAI.MUB6.Certificate.PairSemantics.sound3302_e`, `OAI.MUB6.Certificate.PairSemantics.sound3303_e`, `OAI.MUB6.Certificate.PairSemantics.sound3304_e`, `OAI.MUB6.Certificate.PairSemantics.sound3305_e`, `OAI.MUB6.Certificate.PairSemantics.sound3307_e`, `OAI.MUB6.Certificate.PairSemantics.sound3308_e`, `OAI.MUB6.Certificate.PairSemantics.sound3309_e`, `OAI.MUB6.Certificate.PairSemantics.sound3310_e`, `OAI.MUB6.Certificate.PairSemantics.sound3311_e`, `OAI.MUB6.Certificate.PairSemantics.sound3313_e`, `OAI.MUB6.Certificate.PairSemantics.sound3314_e`, `OAI.MUB6.Certificate.PairSemantics.sound3315_e`, `OAI.MUB6.Certificate.PairSemantics.sound3316_e`, `OAI.MUB6.Certificate.PairSemantics.sound3317_e`, `OAI.MUB6.Certificate.PairSemantics.sound3319_e`, `OAI.MUB6.Certificate.PairSemantics.sound3322_e`, `OAI.MUB6.Certificate.PairSemantics.sound3324_e`, `OAI.MUB6.Certificate.PairSemantics.sound3325_e`, `OAI.MUB6.Certificate.PairSemantics.sound3326_e`, `OAI.MUB6.Certificate.PairSemantics.sound3327_e`, `OAI.MUB6.Certificate.PairSemantics.sound3328_e`, `OAI.MUB6.Certificate.PairSemantics.sound3331_e`, `OAI.MUB6.Certificate.PairSemantics.sound3333_e`, `OAI.MUB6.Certificate.PairSemantics.sound3334_e`, `OAI.MUB6.Certificate.PairSemantics.sound3335_e`, `OAI.MUB6.Certificate.PairSemantics.sound3336_e`, `OAI.MUB6.Certificate.PairSemantics.sound3338_e`, `OAI.MUB6.Certificate.PairSemantics.sound3339_e`, `OAI.MUB6.Certificate.PairSemantics.sound3341_e`, `OAI.MUB6.Certificate.PairSemantics.sound3343_e`, `OAI.MUB6.Certificate.PairSemantics.sound3345_e`, `OAI.MUB6.Certificate.PairSemantics.sound3346_e`, `OAI.MUB6.Certificate.PairSemantics.sound3347_e`, `OAI.MUB6.Certificate.PairSemantics.sound3348_e`, `OAI.MUB6.Certificate.PairSemantics.sound3349_e`, `OAI.MUB6.Certificate.PairSemantics.sound3350_e`, `OAI.MUB6.Certificate.PairSemantics.sound3351_e`, `OAI.MUB6.Certificate.PairSemantics.sound3352_e`, `OAI.MUB6.Certificate.PairSemantics.sound3353_e`, `OAI.MUB6.Certificate.PairSemantics.sound3354_e`, `OAI.MUB6.Certificate.PairSemantics.sound3355_e`, `OAI.MUB6.Certificate.PairSemantics.sound3356_e`, `OAI.MUB6.Certificate.PairSemantics.sound3357_e`, `OAI.MUB6.Certificate.PairSemantics.sound3358_e`, `OAI.MUB6.Certificate.PairSemantics.sound3359_e`, `OAI.MUB6.Certificate.PairSemantics.sound3360_e`, `OAI.MUB6.Certificate.PairSemantics.sound3361_e`, `OAI.MUB6.Certificate.PairSemantics.sound3362_e`, `OAI.MUB6.Certificate.PairSemantics.sound3363_e`, `OAI.MUB6.Certificate.PairSemantics.sound3364_e`, `OAI.MUB6.Certificate.PairSemantics.sound3366_e`, `OAI.MUB6.Certificate.PairSemantics.sound3367_e`, `OAI.MUB6.Certificate.PairSemantics.sound3368_e`, `OAI.MUB6.Certificate.PairSemantics.sound3369_e`, `OAI.MUB6.Certificate.PairSemantics.sound3370_e`, `OAI.MUB6.Certificate.PairSemantics.sound3371_e`, `OAI.MUB6.Certificate.PairSemantics.sound3372_e`, `OAI.MUB6.Certificate.PairSemantics.sound3375_e`, `OAI.MUB6.Certificate.PairSemantics.sound3376_e`, `OAI.MUB6.Certificate.PairSemantics.sound3377_e`, `OAI.MUB6.Certificate.PairSemantics.sound3378_e`, `OAI.MUB6.Certificate.PairSemantics.sound3380_e`, `OAI.MUB6.Certificate.PairSemantics.sound3382_e`, `OAI.MUB6.Certificate.PairSemantics.sound3383_e`, `OAI.MUB6.Certificate.PairSemantics.sound3384_e`, `OAI.MUB6.Certificate.PairSemantics.sound3385_e`, `OAI.MUB6.Certificate.PairSemantics.sound3387_e`, `OAI.MUB6.Certificate.PairSemantics.sound3388_e`, `OAI.MUB6.Certificate.PairSemantics.sound3389_e`, `OAI.MUB6.Certificate.PairSemantics.sound3390_e`, `OAI.MUB6.Certificate.PairSemantics.sound3391_e`, `OAI.MUB6.Certificate.PairSemantics.sound3392_e`, `OAI.MUB6.Certificate.PairSemantics.sound3393_e`, `OAI.MUB6.Certificate.PairSemantics.sound3394_e`, `OAI.MUB6.Certificate.PairSemantics.sound3395_e`, `OAI.MUB6.Certificate.PairSemantics.sound3396_e`, `OAI.MUB6.Certificate.PairSemantics.sound3397_e`, `OAI.MUB6.Certificate.PairSemantics.sound3399_e`, `OAI.MUB6.Certificate.PairSemantics.sound3400_e`, `OAI.MUB6.Certificate.PairSemantics.sound3401_e`, `OAI.MUB6.Certificate.PairSemantics.sound3402_e`, `OAI.MUB6.Certificate.PairSemantics.sound3405_e`, `OAI.MUB6.Certificate.PairSemantics.sound3407_e`, `OAI.MUB6.Certificate.PairSemantics.sound3408_e`, `OAI.MUB6.Certificate.PairSemantics.sound3411_e`, `OAI.MUB6.Certificate.PairSemantics.sound3412_e`, `OAI.MUB6.Certificate.PairSemantics.sound3413_e`, `OAI.MUB6.Certificate.PairSemantics.sound3414_e`, `OAI.MUB6.Certificate.PairSemantics.sound3415_e`, `OAI.MUB6.Certificate.PairSemantics.sound3416_e`, `OAI.MUB6.Certificate.PairSemantics.sound3417_e`, `OAI.MUB6.Certificate.PairSemantics.sound3418_e`, `OAI.MUB6.Certificate.PairSemantics.sound3419_e`, `OAI.MUB6.Certificate.PairSemantics.sound3420_e`, `OAI.MUB6.Certificate.PairSemantics.sound3421_e`, `OAI.MUB6.Certificate.PairSemantics.sound3422_e`, `OAI.MUB6.Certificate.PairSemantics.sound3423_e`, `OAI.MUB6.Certificate.PairSemantics.sound3424_e`, `OAI.MUB6.Certificate.PairSemantics.sound3425_e`, `OAI.MUB6.Certificate.PairSemantics.sound3428_e`, `OAI.MUB6.Certificate.PairSemantics.sound3431_e`, `OAI.MUB6.Certificate.PairSemantics.sound3433_e`, `OAI.MUB6.Certificate.PairSemantics.sound3434_e`, `OAI.MUB6.Certificate.PairSemantics.sound3435_e`, `OAI.MUB6.Certificate.PairSemantics.sound3436_e`, `OAI.MUB6.Certificate.PairSemantics.sound3437_e`, `OAI.MUB6.Certificate.PairSemantics.sound3439_e`, `OAI.MUB6.Certificate.PairSemantics.sound3440_e`, `OAI.MUB6.Certificate.PairSemantics.sound3441_e`, `OAI.MUB6.Certificate.PairSemantics.sound3442_e`, `OAI.MUB6.Certificate.PairSemantics.sound3443_e`, `OAI.MUB6.Certificate.PairSemantics.sound3444_e`, `OAI.MUB6.Certificate.PairSemantics.sound3447_e`, `OAI.MUB6.Certificate.PairSemantics.sound3449_e`, `OAI.MUB6.Certificate.PairSemantics.sound3451_e`, `OAI.MUB6.Certificate.PairSemantics.sound3454_e`, `OAI.MUB6.Certificate.PairSemantics.sound3455_e`, `OAI.MUB6.Certificate.PairSemantics.sound3456_e`, `OAI.MUB6.Certificate.PairSemantics.sound3457_e`, `OAI.MUB6.Certificate.PairSemantics.sound3458_e`, `OAI.MUB6.Certificate.PairSemantics.sound3459_e`, `OAI.MUB6.Certificate.PairSemantics.sound3460_e`, `OAI.MUB6.Certificate.PairSemantics.sound3461_e`, `OAI.MUB6.Certificate.PairSemantics.sound3462_e`, `OAI.MUB6.Certificate.PairSemantics.sound3463_e`, `OAI.MUB6.Certificate.PairSemantics.sound3467_e`, `OAI.MUB6.Certificate.PairSemantics.sound3468_e`, `OAI.MUB6.Certificate.PairSourceBridge.allRowsSound_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound0_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound100_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound101_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound102_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound103_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound104_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound105_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound106_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound107_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound108_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound10_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound110_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound111_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound112_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound113_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound114_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound115_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound116_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound117_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound118_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound119_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound120_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound121_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound123_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound124_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound125_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound127_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound128_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound129_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound12_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound130_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound131_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound132_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound133_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound134_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound135_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound136_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound137_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound138_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound139_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound140_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound141_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound142_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound143_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound144_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound145_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound146_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound147_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound148_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound149_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound14_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound150_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound151_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound152_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound153_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound154_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound155_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound156_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound157_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound158_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound159_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound15_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound160_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound161_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound162_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound163_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound164_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound165_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound166_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound167_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound168_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound16_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound170_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound171_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound172_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound174_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound175_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound176_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound177_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound178_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound179_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound17_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound180_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound181_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound182_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound183_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound184_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound185_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound186_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound187_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound188_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound189_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound18_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound191_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound192_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound193_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound194_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound195_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound196_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound197_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound198_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound199_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound19_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound1_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound200_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound203_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound204_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound205_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound206_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound208_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound209_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound20_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound210_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound211_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound212_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound213_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound216_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound217_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound218_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound219_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound21_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound220_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound221_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound222_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound223_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound224_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound225_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound226_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound227_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound228_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound229_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound22_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound230_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound231_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound232_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound233_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound234_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound235_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound236_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound237_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound238_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound239_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound23_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound240_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound241_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound242_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound243_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound244_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound245_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound246_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound247_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound248_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound249_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound24_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound250_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound251_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound252_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound253_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound254_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound26_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound27_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound28_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound29_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound2_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound30_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound31_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound32_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound34_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound35_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound36_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound37_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound38_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound39_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound3_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound40_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound41_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound42_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound43_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound44_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound45_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound46_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound47_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound49_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound4_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound50_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound51_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound52_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound53_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound54_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound55_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound56_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound58_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound59_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound5_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound60_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound61_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound62_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound63_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound64_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound65_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound66_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound67_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound69_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound6_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound70_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound72_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound73_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound74_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound75_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound76_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound77_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound78_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound79_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound7_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound80_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound81_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound82_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound83_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound84_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound85_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound86_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound87_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound88_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound89_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound8_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound90_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound91_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound92_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound93_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound94_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound95_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound96_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound97_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound98_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound99_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound9_e`, `OAI.MUB6.Certificate.PairTargetSemantics.expandedIdentity1_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm11_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm12_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm13_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm14_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm16_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm17_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm18_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm19_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm21_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm22_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm23_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm24_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm25_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm26_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm6_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm7_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm8_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm9_e` and `OAI.MUB6.pair_cross_certificate_e`.
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

def raw6step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]

def raw6step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def raw7 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]

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

def raw60step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

def raw61 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]

def raw61step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

def raw63 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]

def raw63step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical177
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

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

def raw605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]

def raw606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]

def raw606step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]

def raw606step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]

def raw607 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]

def raw607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]

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

def raw6052step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-2, 1, 1], ![4, -2, -2]]

def raw6052step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw6053 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw6053step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 1, 1, -1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw6054 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![-1, 1, 2, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw6054step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 1, 0, 0], ![0, 0, 1, -1], ![1, -1, 2, -2], ![1, 1, -1, -1]]

def raw6055 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![-1, 2, 0, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw6055step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 2, -4], ![0, 0, -1, 1], ![1, -2, 0, 1], ![-1, 1, -2, 2], ![-1, 0, 1, 0]]

def raw6055step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![1, -1, -2, 2], ![1, 1, 2, -4]]

def raw6056 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def raw6056step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def raw6057 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw6057step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw6058 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw6058step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw6059 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw6059step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw6060 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 1, -1, -1]]

def raw6061 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw6062 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw6062step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw6063 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def raw6064 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw6064step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw6065 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![0, 2, -1, -1]]

def raw6065step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def raw6066 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 1, 0, -2]]

def raw6067 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def raw6068 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, 1, -1, -1]]

def raw6069 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 0, 1, -1], ![1, 0, 1, -2]]

def raw6069step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw6070 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 2, -2]]

def raw6071 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def raw6072 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 0, 2, -2], ![1, 0, -1, 0]]

def raw6072step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw6073 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![0, 1, -1, 0]]

def raw6073step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 2, -2]]

def raw6074 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw6075 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![0, -1, 1, 0], ![1, 1, -1, -1]]

def raw6075step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw6076 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![0, 1, 0, -1]]

def raw6076step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw6077 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw6077step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw6078 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw6078step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def raw6079 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 2, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw608 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]

def raw608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 2, -1], ![-2, 1, 1], ![-2, 0, 2]]

def raw608step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]

def raw609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]

def raw609step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]

def raw609step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw610 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]

def raw610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]

def raw610step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]

def raw611 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]

def raw611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]

def raw611step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

def raw612 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]

def raw612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]

def raw612step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

def raw613 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]

def raw613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, 1, 1]]

def raw613step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

def raw614 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]

def raw614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]

def raw615 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]

def raw615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]

def raw615step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def raw616 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -2, 0], ![3, -1, -2]]

def raw616step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![2, 1, -3]]

def raw617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]

def raw617step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

def raw618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]

def raw618step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]

def raw618step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]

def raw619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]

def raw619step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]

def raw619step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def raw620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]

def raw620step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

def raw621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]

def raw621step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

def raw622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]

def raw622step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0], ![-2, 1, 1]]

def raw622step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

def raw623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]

def raw623step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]

def raw623step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]

def raw624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]

def raw624step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]

def raw624step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

def raw625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]

def raw625step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

def raw626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]

def raw626step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]

def raw626step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

def raw627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]

def raw627step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]

def raw627step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]

def raw628step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]

def raw628step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw629 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]

def raw629step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]

def raw630step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw631 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]

def raw631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw632 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]

def raw632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw633 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]

def raw633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]

def raw633step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]

def raw634 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]

def raw634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]

def raw635 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]

def raw635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]

def raw635step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

def raw636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw636step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]

def raw636step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw637 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]

def raw637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]

def raw637step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

def raw638 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]

def raw638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]

def raw638step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]

def raw639 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]

def raw639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]

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

def raw6080 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw6080step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![-2, 1, 0, 1], ![4, -1, -2, -1]]

def raw6080step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw6081 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, 0, 0]]

def raw6081step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![-2, 1, 1, 0], ![4, -1, -3, 0]]

def raw6081step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw6082 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![1, -1, 2, -2], ![0, 2, -1, -1]]

def raw6082step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 2, -2]]

def raw6083 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![1, 1, 1, -3]]

def raw6083step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1], ![4, -1, -3]]

def raw6083step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]

def raw6084 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 0, 0, 0], ![1, 1, 0, -2]]

def raw6084step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![-2, 2, 0, 0], ![4, -2, 0, -2]]

def raw6084step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0], ![4, -2, -2]]

def raw6084step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw6085 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def raw6085step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def raw6086 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 0, 1, -1], ![1, 1, -1, -1]]

def raw6086step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, 1, -1, -1]]

def raw6087 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw6088 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw6089 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def raw6090 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw6090step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw6091 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def raw6091step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0], ![4, -2, -2]]

def raw6091step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw6092 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw6093 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 3, -3], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def raw6094 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 3, -3], ![1, 1, -1, -1]]

def raw6094step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-2, 3, -1], ![4, -3, -1]]

def raw6094step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1]]

def raw6095 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 4, -4], ![1, 1, -2, 0]]

def raw6095step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-2, 4, -2], ![4, -4, 0]]

def raw6095step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

def raw6096 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 1, -1, 0], ![-1, 1, 1, -1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw6096step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 1, 1, -1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw6097 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 1, -1, 0], ![0, 0, 2, -2], ![1, 0, 1, -2]]

def raw6097step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw6098 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 1, -1, 0], ![0, 1, 0, -1], ![0, -1, 2, -1], ![1, 0, 1, -2]]

def raw6098step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw6099 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![0, 0, 2, -2]]

def raw6099step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1]]

def raw6100 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 3, -3]]

def raw6100step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![-2, -1, 0, 3], ![4, 0, -1, -3]]

def raw6100step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, -1, -1, 1], ![2, 1, 0, -3], ![-4, 0, 1, 3]]

def raw6100step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -3, 2], ![1, 0, 3, -4]]

def raw6101 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 2, -2]]

def raw6102 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw6102step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![-2, -1, 3, 0], ![4, 0, -4, 0]]

def raw6102step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 4, -4], ![0, 1, -1, 0], ![1, -1, -1, 1]]

def raw6103 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 1, -1, 0], ![1, 0, 3, -4]]

def raw6103step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-2, -1, 3], ![4, 0, -4]]

def raw6103step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0]]

def raw6104 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 2, -2]]

def raw6104step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![-2, 0, 0, 2], ![4, -1, -1, -2]]

def raw6104step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, 1, -1, -1]]

def raw6105 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def raw6105step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-2, 0, 2], ![4, -1, -3]]

def raw6105step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

def raw6106 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 1, 1, -2], ![0, -1, 2, -1], ![1, 1, -1, -1]]

def raw6106step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw6107 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 1, 1, -2], ![0, 1, 0, -1], ![1, -1, 1, -1]]

def raw6107step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw6108 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw6108step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw6109 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 1, 1, -2], ![1, -1, 1, -1], ![0, 1, 0, -1]]

def raw6109step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw6110 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw6110step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-2, 1, 1], ![4, -2, -2]]

def raw6110step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw6111 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def raw6111step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-2, 2, 0], ![4, -3, -1]]

def raw6111step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical191
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6112 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 2, -1, -1], ![1, -1, 3, -3]]

def raw6112step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![-2, -1, 3], ![4, -1, -3]]

def raw6112step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -2, 1], ![2, 1, -3], ![-4, 1, 3]]

def raw6112step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -3, 2], ![1, 3, -4]]

def raw6113 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 2, 0, -2], ![1, -1, 2, -2]]

def raw6113step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![-2, 0, 2], ![4, -2, -2]]

def raw6113step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def raw6114 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 2, 1, -3], ![1, -1, 1, -1]]

def raw6114step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![-2, 1, 1], ![4, -3, -1]]

def raw6114step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2]]

def raw6115 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![1, -1, 1, -1], ![0, 2, 1, -3]]

def raw6115step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1], ![4, -1, -3]]

def raw6115step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2]]

def raw6116 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![1, -1, 2, -2], ![0, 2, 0, -2]]

def raw6116step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0], ![4, -2, -2]]

def raw6116step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def raw6117 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![1, -1, 3, -3], ![0, 2, -1, -1]]

def raw6117step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-2, 3, -1], ![4, -3, -1]]

def raw6117step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![1, 1, -2], ![2, -3, 1], ![-4, 3, 1]]

def raw6117step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -3, 2], ![1, 3, -4]]

def raw6118 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, -1, 1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw6118step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -1, -1, 1]]

def raw6119 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, -1, 1, 1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw6120 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, -1, 1, 1], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw6120step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, -1, 1, 1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw6121 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, -1, 1, 1], ![1, 0, 1, -2], ![1, 2, -1, -2]]

def raw6121step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 1, -3], ![1, 1, -1, -1], ![-1, 0, -1, 2], ![-1, -2, 1, 2]]

def raw6121step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def raw6122 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, -1, 1, 1], ![1, 1, 1, -3], ![1, 1, -1, -1]]

def raw6122step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, -1, 1, 1], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def raw6123 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, -1, 2, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw6123step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 1, -3], ![1, 1, -2, 0], ![0, -1, 1, 0], ![-1, 0, 0, 1], ![-1, -1, 0, 2]]

def raw6123step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, -1, 0, 1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw6124 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, -1, 2, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw6124step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 1, -3], ![1, 1, -2, 0], ![0, -1, 0, 1], ![-1, 0, 0, 1], ![-1, -1, 1, 1]]

def raw6124step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def raw6125 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, -1, 2, 0], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def raw6125step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, -1, 1, 1], ![-1, 2, -1, 0], ![3, 0, -1, -2]]

def raw6125step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def raw6126 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 1, 0], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw6126step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw6127 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw6127step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 1, -3], ![1, 0, -2, 1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, -1, 0, 2]]

def raw6127step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw6128 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw6129 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw6129step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw6130 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw6130step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw6131 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw6131step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 1, -3], ![1, 0, -2, 1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, -1, 1, 1]]

def raw6131step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def raw6132 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw6133 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, -1, 0]]

def raw6133step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw6134 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw6135 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw6135step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw6136 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

def raw6136step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def raw6137 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw6137step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 1, -3], ![1, 0, -2, 1], ![0, -2, 2, 0], ![-1, 1, 0, 0], ![-1, 0, -1, 2]]

def raw6137step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -3, 1]]

def raw6138 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw6138step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 1, -3], ![1, 0, -2, 1], ![0, -2, 2, 0], ![-1, 1, -1, 1], ![-1, 0, 0, 1]]

def raw6138step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -3, 1]]

def raw6139 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw6139step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 1, -3], ![1, 0, -2, 1], ![0, -2, 1, 1], ![-1, 1, -1, 1], ![-1, 0, 1, 0]]

def raw6139step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -3, 1]]

def raw6140 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw6140step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 1, -3], ![1, 0, -2, 1], ![0, -2, 0, 2], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw6140step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw6141 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![1, -1, 1, -1], ![1, 2, -2, -1]]

def raw6141step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 1, -3], ![1, 0, -2, 1], ![-1, 1, -1, 1], ![-1, -2, 2, 1]]

def raw6141step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -3, 1]]

def raw6142 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw6142step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def raw6143 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![1, 0, 1, -2], ![1, 1, -2, 0]]

def raw6143step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 1, -2, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical192
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6144 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw6145 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw6145step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1]]

def raw6146 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 1, -2, 1], ![2, 0, 0, -2]]

def raw6146step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw6147 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw6148 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw6148step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw6149 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def raw6150 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw6151 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def raw6151step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw6152 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw6152step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw6153 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw6153step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 1, -3], ![1, 0, -3, 2], ![0, -2, 2, 0], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw6153step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 1, -3, 1]]

def raw6154 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw6154step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 1, -3], ![1, 0, -3, 2], ![0, -2, 1, 1], ![-1, 1, 1, -1], ![-1, 0, 0, 1]]

def raw6154step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, -3, 2], ![1, -1, 1, -1], ![1, 1, 1, -3]]

def raw6155 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw6155step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 1, -3], ![1, 0, -3, 2], ![0, -2, 1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw6155step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 1, -3, 1]]

def raw6156 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![1, -1, -1, 1], ![1, 2, -1, -2]]

def raw6156step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 1, -3], ![1, 0, -3, 2], ![-1, 1, 1, -1], ![-1, -2, 1, 2]]

def raw6156step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -3, 2], ![1, -1, 1, -1], ![1, 1, 1, -3]]

def raw6157 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![1, -1, 0, 0], ![1, 2, -2, -1]]

def raw6157step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 0, -1, 2], ![-1, 3, 0, -2], ![3, -2, 0, -1]]

def raw6157step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 3, -2, -1], ![1, -1, -1, 1]]

def raw6158 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![1, 0, -2, 1], ![1, 1, 0, -2]]

def raw6158step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def raw6159 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw6159step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, 1, -1, -1]]

def raw6160 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw6160step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def raw6161 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw6162 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def raw6163 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, -1, 1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def raw6163step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 1, -3], ![1, -1, 1, -1], ![0, -1, 0, 1], ![-1, 1, -2, 2], ![-1, 0, 0, 1]]

def raw6163step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def raw6164 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, -1, 1], ![0, 1, 0, -1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw6165 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, -1, 1], ![0, 1, 1, -2], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw6166 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, -1, 1], ![0, 1, 1, -2], ![2, -1, 1, -2]]

def raw6166step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 1, -3], ![1, -1, 1, -1], ![0, -1, -1, 2], ![-2, 1, -1, 2]]

def raw6166step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def raw6167 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, -1, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw6168 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, -1, 1], ![0, 1, 3, -4], ![2, -1, -1, 0]]

def raw6168step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 1, -3], ![1, -1, 1, -1], ![0, -1, -3, 4], ![-2, 1, 1, 0]]

def raw6168step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![1, -1, 1, -1], ![1, 1, 1, -3]]

def raw6169 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, -1, 1], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw6169step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 1, -1, 1], ![-1, -1, 0, 2], ![3, 1, 0, -4]]

def raw6169step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def raw6170 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, -1, 1], ![1, -1, 3, -3], ![1, 1, -1, -1]]

def raw6171 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, -1, 1], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def raw6171step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def raw6172 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, -1, 1], ![1, 0, 2, -3], ![1, 0, 0, -1]]

def raw6172step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw6173 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, -1, 1], ![1, 0, 3, -4], ![1, 0, -1, 0]]

def raw6173step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def raw6174 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, -1, 1], ![1, 1, 0, -2], ![1, -1, 2, -2]]

def raw6174step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 1, -3], ![1, -1, 1, -1], ![-1, -1, 0, 2], ![-1, 1, -2, 2]]

def raw6174step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def raw6175 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 0, 0], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw6175step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 1, -3], ![1, -1, 0, 0], ![0, -1, 0, 1], ![-1, 1, -2, 2], ![-1, 0, 1, 0]]

def raw6175step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical193
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6176 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 0, 0], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def raw6176step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw6177 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw6177step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def raw6178 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 1, -1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw6178step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw6179 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 1, -1], ![0, 1, -1, 0], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw6180 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 1, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw6180step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw6181 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 1, -1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -2, 1]]

def raw6182 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw6182step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 1, 0], ![0, -1, 1, 0], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def raw6183 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 1, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw6184 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 1, -1], ![1, -1, 2, -2], ![1, 1, -2, 0]]

def raw6184step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 1, -1, 1], ![-1, 1, 2, -2], ![3, -1, -2, 0]]

def raw6184step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def raw6185 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 1, -1], ![1, 0, 1, -2], ![1, 0, -1, 0]]

def raw6185step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw6186 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 1, -1], ![1, 0, 2, -3], ![1, 0, -2, 1]]

def raw6186step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 1, -1]]

def raw6187 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw6187step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 1, -3], ![1, -1, -2, 2], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw6187step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw6188 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw6188step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 1, -3], ![1, -1, -2, 2], ![0, -1, 0, 1], ![-1, 1, 1, -1], ![-1, 0, 0, 1]]

def raw6188step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def raw6189 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 2, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw6189step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 1, -3], ![1, -1, -2, 2], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw6189step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw6190 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 2, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw6190step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 1, -1, 1], ![-1, 2, 0, -1], ![3, -2, 0, -1]]

def raw6190step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![1, -1, 1, -1], ![1, -2, 0, 1], ![-3, 2, 0, 1]]

def raw6190step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -3, 2], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw6191 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 2, -2], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw6191step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 1, -1, 1], ![-1, 2, 1, -2], ![3, -2, -1, 0]]

def raw6191step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def raw6192 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 3, -3], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw6192step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 0, 0], ![0, 1, 0, -1], ![1, -1, 3, -3], ![1, 0, -2, 1]]

def raw6193 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 3, -3], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def raw6193step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, -1, 1], ![1, -1, 3, -3], ![1, 1, -1, -1]]

def raw6194 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 3, -3], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw6194step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 1, -1, 1], ![-1, 3, 0, -2], ![3, -3, 0, 0]]

def raw6194step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![1, -1, 1, -1], ![1, -3, 0, 2], ![-3, 3, 0, 0]]

def raw6194step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -3, 3], ![0, 2, 1, -3], ![1, -1, 1, -1]]

def raw6195 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 2, -2, 1], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw6195step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 2, -1, 0], ![-1, -2, 0, 3], ![3, 1, 0, -4]]

def raw6195step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -2, 3], ![0, 3, 1, -4], ![1, -1, -1, 1]]

def raw6196 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 2, -2, 1], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def raw6196step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 2, -1, 0], ![-1, -2, 3, 0], ![3, 1, -3, -1]]

def raw6196step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![1, -2, 1, 0], ![1, 2, -3, 0], ![-3, -1, 3, 1]]

def raw6196step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -2, 1, 1], ![0, 2, 1, -3], ![1, -1, -3, 3]]

def raw6197 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 2, -1, 0], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw6197step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 2, -1, 0], ![-1, -1, 3, -1], ![3, 0, -3, 0]]

def raw6197step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw6198 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 2, 0, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw6198step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 2, -1, 0], ![-1, 0, 2, -1], ![3, -1, -2, 0]]

def raw6198step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw6199 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 2, 0, -1], ![1, -1, 3, -3], ![1, 0, -2, 1]]

def raw6199step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 2, -1, 0], ![-1, 0, 3, -2], ![3, -1, -3, 1]]

def raw6199step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, -1, 3, -3]]

def raw6200 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 2, 1, -2], ![1, -1, 2, -2], ![1, 0, -2, 1]]

def raw6200step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 1, -3], ![1, -2, -1, 2], ![-1, 1, -2, 2], ![-1, 0, 2, -1]]

def raw6200step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![1, -1, -2, 2], ![1, 1, 1, -3]]

def raw6201 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 0, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw6201step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![-1, 0, 2, -1], ![3, 1, -4, 0]]

def raw6201step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 1, -2, 0], ![1, 0, -2, 1], ![-3, -1, 4, 0]]

def raw6201step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw6202 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw6202step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw6203 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![-1, 1, 1, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw6203step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw6204 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw6205 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw6206 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 0, 1, -1], ![1, 1, 0, -2]]

def raw6206step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 1, 0, -2]]

def raw6207 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical194
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6208 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![0, 1, 1, -2]]

def raw6208step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw6209 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 0, 1, -1], ![1, 1, -1, -1]]

def raw6209step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def raw6210 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![0, 1, 0, -1]]

def raw6210step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw6211 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 1, 0, -2]]

def raw6211step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw6212 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw6212step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![-1, 1, 1, -1], ![3, 0, -3, 0]]

def raw6212step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, -1, 1]]

def raw6213 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![1, 1, -1, -1], ![0, 1, 1, -2]]

def raw6213step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw6214 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def raw6215 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw6216 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw6217 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw6217step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw6218 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 1, 0, -2]]

def raw6218step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw6219 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw6220 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def raw6221 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw6222 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def raw6223 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw6224 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw6225 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![1, 2, -1, -2]]

def raw6225step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, 2, -1], ![3, -1, -2]]

def raw6225step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 1, -2], ![1, -2, 1], ![-3, 1, 2]]

def raw6225step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

def raw6226 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def raw6227 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, 1, -1, -1]]

def raw6228 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def raw6229 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw6230 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw6231 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw6232 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![1, 2, -2, -1]]

def raw6232step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, 3, -2], ![3, -2, -1]]

def raw6232step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 1, -2], ![1, -3, 2], ![-3, 2, 1]]

def raw6232step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

def raw6233 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![-1, 2, -1, 0], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def raw6233step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 1, -3], ![0, 0, 1, -1], ![1, -2, 1, 0], ![-1, 1, -3, 3], ![-1, 0, 0, 1]]

def raw6233step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, 0, 1], ![0, 0, 1, -1], ![1, -1, -3, 3], ![1, 1, 1, -3]]

def raw6234 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![-1, 2, 0, -1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw6234step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 1, -3], ![0, 0, 1, -1], ![1, -2, 0, 1], ![-1, 1, -3, 3], ![-1, 0, 1, 0]]

def raw6234step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, -1, -3, 3], ![1, 1, 1, -3]]

def raw6235 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 0, 3, -3], ![1, 0, 0, -1]]

def raw6235step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw6236 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw6237 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 3, -3], ![0, 1, 0, -1]]

def raw6237step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 3, -3]]

def raw6238 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 3, -4]]

def raw6239 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 0, 3, -3], ![1, 0, -1, 0]]

def raw6239step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, 0, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical195
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6240 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 3, -3], ![0, 1, -1, 0]]

def raw6240step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 3, -3]]

def raw6241 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def raw6242 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def raw6242step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 3, -4]]

def raw6243 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, 1, -1]]

def raw6243step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 0, 1], ![0, 1, 2, -3], ![1, 1, -1, -1]]

def raw6244 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, 0, 0]]

def raw6244step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![-1, -1, 2, 0], ![3, 1, -4, 0]]

def raw6244step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 0, -2, 1], ![1, 1, -2, 0], ![-3, -1, 4, 0]]

def raw6244step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw6245 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 0, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw6245step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 1, 0], ![-1, 0, 1, 0], ![3, 0, -2, -1]]

def raw6245step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 1, 0], ![3, -2, -1]]

def raw6245step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw6246 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 0, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw6246step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 1, 0], ![-1, 0, 2, -1], ![3, 0, -3, 0]]

def raw6246step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 2, -1], ![3, -3, 0]]

def raw6246step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

def raw6247 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw6247step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw6248 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw6248step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw6249 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![-1, 2, -1, 0], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw6249step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 1, -3], ![0, 0, -1, 1], ![1, -2, 1, 0], ![-1, 1, -2, 2], ![-1, 0, 1, 0]]

def raw6249step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![1, -1, 2, -2], ![1, 1, -3, 1]]

def raw6250 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![-1, 2, 0, -1], ![1, -1, 2, -2], ![1, 0, -2, 1]]

def raw6250step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 1, -3], ![0, 0, -1, 1], ![1, -2, 0, 1], ![-1, 1, -2, 2], ![-1, 0, 2, -1]]

def raw6250step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 2, -1], ![0, 0, -1, 1], ![1, -1, -2, 2], ![1, 1, 1, -3]]

def raw6251 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def raw6251step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def raw6252 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw6252step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw6253 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw6253step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw6254 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw6254step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw6255 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 0, 0], ![1, 1, 0, -2]]

def raw6255step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![-1, 1, 0, 0], ![3, -1, 0, -2]]

def raw6255step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![3, -1, -2]]

def raw6255step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw6256 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 1, -2, 0]]

def raw6257 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw6258 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw6258step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw6259 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 1, -1]]

def raw6260 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def raw6260step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw6261 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 1, -1, -1]]

def raw6262 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw6263 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, 1, -2, 0]]

def raw6264 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, -1, 1, 0], ![1, 1, 0, -2]]

def raw6264step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 1, 0, -2]]

def raw6265 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 0, 1, -1], ![1, 0, 0, -1]]

def raw6265step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw6266 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 0, 2, -2], ![1, 0, -1, 0]]

def raw6266step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def raw6267 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1]]

def raw6267step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def raw6268 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![0, 1, 1, -2]]

def raw6268step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw6269 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 2, -2], ![0, 1, -1, 0]]

def raw6269step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 2, -2]]

def raw6270 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw6271 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, -1, 1, 0], ![1, 1, -1, -1]]

def raw6271step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical196
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6272 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 0, 1, -1], ![1, 0, -1, 0]]

def raw6272step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw6273 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 0, 2, -2], ![1, 0, -2, 1]]

def raw6273step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw6274 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0]]

def raw6274step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw6275 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![0, 1, 0, -1]]

def raw6275step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw6276 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![0, 1, -2, 1]]

def raw6276step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 2, -2]]

def raw6277 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw6278 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw6278step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw6279 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 2, -2]]

def raw6280 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def raw6280step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def raw6281 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw6281step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw6282 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw6283 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![1, 1, 0, -2]]

def raw6283step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![3, -1, -2]]

def raw6283step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw6284 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw6284step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw6285 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 0, 1, -1], ![1, 1, -2, 0]]

def raw6285step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, 1, -2, 0]]

def raw6286 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 1, -2]]

def raw6287 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw6288 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw6288step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw6289 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 1, -1]]

def raw6290 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def raw6290step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw6291 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw6292 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![1, 1, -1, -1]]

def raw6292step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 2, -1], ![3, -2, -1]]

def raw6292step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw6293 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw6294 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw6295 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def raw6296 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, 0, -2, 1]]

def raw6296step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw6297 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw6298 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![1, 1, -2, 0]]

def raw6298step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 3, -2], ![3, -3, 0]]

def raw6298step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw6299 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 4, -4], ![1, 1, -3, 1]]

def raw6299step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 4, -3], ![3, -4, 1]]

def raw6299step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]

def raw6300 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 3, -3]]

def raw6301 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 2, -2]]

def raw6302 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 1, -1]]

def raw6303 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, 0, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical197
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6304 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -2, 1], ![1, 0, 3, -4]]

def raw6304step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, -2, 3], ![3, 1, -4]]

def raw6304step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def raw6305 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -1, 0], ![0, -1, 2, -1], ![1, 1, 0, -2]]

def raw6305step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw6306 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -1, 0], ![0, 0, 2, -2], ![1, 0, 0, -1]]

def raw6306step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw6307 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -1, 0], ![0, 0, 3, -3], ![1, 0, -1, 0]]

def raw6307step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def raw6308 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 3, -3]]

def raw6308step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![-1, -1, -1, 3], ![3, 0, 0, -3]]

def raw6308step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 3, -3], ![1, 1, -1, -1]]

def raw6309 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 2, -2]]

def raw6309step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![-1, -1, 0, 2], ![3, 0, -1, -2]]

def raw6309step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, -1, -1, 1], ![1, 1, 0, -2], ![-3, 0, 1, 2]]

def raw6309step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, 0, 2, -3]]

def raw6310 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw6310step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw6311 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw6311step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![-1, -1, 2, 0], ![3, 0, -3, 0]]

def raw6311step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, -1, 1]]

def raw6312 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def raw6313 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -1, 0], ![1, -1, 1, -1], ![0, 1, 1, -2]]

def raw6313step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw6314 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -1, 0], ![1, -1, 3, -3], ![0, 1, -1, 0]]

def raw6314step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-1, 1, -1, 1], ![-1, -1, 3, -1], ![3, 0, -3, 0]]

def raw6314step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 3, -3], ![1, 1, -1, -1]]

def raw6315 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def raw6315step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, -1, 2], ![3, 0, -3]]

def raw6315step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

def raw6316 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, 0, -1], ![0, -1, 2, -1], ![1, 1, -1, -1]]

def raw6316step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def raw6317 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, 0, -1], ![0, 0, 2, -2], ![1, 0, -1, 0]]

def raw6317step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw6318 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, 0, -1], ![0, 0, 3, -3], ![1, 0, -2, 1]]

def raw6318step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw6319 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 2, -2]]

def raw6319step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![-1, 0, -1, 2], ![3, -1, 0, -2]]

def raw6319step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, -1, -1, 1], ![1, 0, 1, -2], ![-3, 1, 0, 2]]

def raw6319step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, 0, 2, -3]]

def raw6320 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw6320step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw6321 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, -1, -1, 1]]

def raw6321step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw6322 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, 0, -1], ![1, -1, 1, -1], ![0, 1, 0, -1]]

def raw6322step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 1, -1, -1]]

def raw6323 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, 0, -1], ![1, -1, 3, -3], ![0, 1, -2, 1]]

def raw6323step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 3, -3]]

def raw6324 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw6324step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 0, 1], ![3, -1, -2]]

def raw6324step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw6325 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -1, -1, 1]]

def raw6326 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw6326step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 1, 0], ![3, -2, -1]]

def raw6326step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw6327 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, 2, -3], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw6327step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![-1, 2, -1, 0], ![3, -3, 0, 0]]

def raw6327step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, -1, 1]]

def raw6328 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw6328step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 2, -1], ![3, -3, 0]]

def raw6328step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

def raw6329 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, 3, -4], ![1, 0, -2, 1]]

def raw6329step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 3, -2], ![3, -4, 1]]

def raw6329step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def raw6330 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 2, -2, 0], ![1, -1, 3, -3]]

def raw6330step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![-1, -2, 3], ![3, 0, -3]]

def raw6330step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![2, -1, -1]]

def raw6331 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 2, -1, -1], ![1, -1, 2, -2]]

def raw6331step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![-1, -1, 2], ![3, -1, -2]]

def raw6331step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -2, 1], ![1, 1, -2], ![-3, 1, 2]]

def raw6331step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

def raw6332 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 2, 1, -3], ![1, -1, 0, 0]]

def raw6332step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![-1, 1, 0], ![3, -3, 0]]

def raw6332step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

def raw6333 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 2, 2, -4], ![1, -1, -1, 1]]

def raw6333step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![-1, 2, -1], ![3, -4, 1]]

def raw6333step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -2, 1], ![1, -2, 1], ![-3, 4, -1]]

def raw6333step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2]]

def raw6334 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![1, -1, 1, -1], ![0, 2, 0, -2]]

def raw6334step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 1, 0], ![3, -1, -2]]

def raw6334step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw6335 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![1, -1, 2, -2], ![0, 2, -1, -1]]

def raw6335step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 2, -1], ![3, -2, -1]]

def raw6335step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![1, 1, -2], ![1, -2, 1], ![-3, 2, 1]]

def raw6335step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical198
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6336 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![1, -1, 3, -3], ![0, 2, -2, 0]]

def raw6336step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 3, -2], ![3, -3, 0]]

def raw6336step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![2, -1, -1]]

def raw6337 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![1, 0, -2, 1], ![0, 1, 3, -4]]

def raw6337step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3], ![3, 1, -4]]

def raw6337step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def raw6338 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![1, 0, 3, -4], ![0, 1, -2, 1]]

def raw6338step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 3, -2], ![3, -4, 1]]

def raw6338step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def raw6339 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, -1, 1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw6339step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, -1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -1, 1]]

def raw6340 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw6340step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 0, -2], ![1, 0, 1, -2], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, -1, -2, 4]]

def raw6340step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw6341 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def raw6341step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def raw6342 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 0, -1, 2], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw6343 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 0, -1, 2], ![0, 1, 3, -4], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw6343step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 3, -4]]

def raw6344 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 0, -1, 2], ![0, 1, 3, -4], ![2, 0, -2, 0]]

def raw6344step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 2, -2, 0], ![1, 0, 3, -4]]

def raw6345 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 0, -1, 2], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw6345step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 0, -2], ![1, 0, 1, -2], ![0, -2, 2, 0], ![-1, 1, 0, 0], ![-1, 0, -3, 4]]

def raw6345step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, -1, -3, 4], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw6346 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 0, -1, 2], ![0, 2, 2, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw6346step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 0, -2], ![1, 0, 1, -2], ![0, -2, -2, 4], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw6346step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw6347 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 0, -1, 2], ![1, 0, 3, -4], ![1, 1, -2, 0]]

def raw6347step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, 1, -2, 0]]

def raw6348 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -2, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw6349 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -2, 2], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def raw6350 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -2, 2], ![0, 1, 0, -1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw6351 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -2, 2], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw6352 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -2, 2], ![0, 1, 3, -4], ![2, -1, -1, 0]]

def raw6352step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, 1, -1], ![0, -2, 3, -1], ![2, 2, -4, 0]]

def raw6352step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 0, -2], ![1, -1, -1, 1], ![0, 2, -3, 1], ![-2, -2, 4, 0]]

def raw6352step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 2, -3], ![1, -2, 1, 0], ![1, 1, -1, -1]]

def raw6353 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -2, 2], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw6353step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 1, -1, 1], ![0, -2, 0, 2], ![2, 2, 0, -4]]

def raw6353step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -1, -1, 1]]

def raw6354 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -2, 2], ![1, -1, 3, -3], ![1, 1, -1, -1]]

def raw6354step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 1, -1, 1], ![0, -2, 3, -1], ![2, 2, -3, -1]]

def raw6354step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![1, -1, 1, -1], ![0, 2, -3, 1], ![-2, -2, 3, 1]]

def raw6354step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, -1, 1, -1]]

def raw6355 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -2, 2], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def raw6355step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -2, 2]]

def raw6356 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -2, 2], ![1, 0, 2, -3], ![1, 0, 0, -1]]

def raw6356step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, -1, -2, 2]]

def raw6357 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -2, 2], ![1, 0, 3, -4], ![1, 0, -1, 0]]

def raw6357step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -2, 2]]

def raw6358 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw6359 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 1, -2, 1], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def raw6360 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 1, -2, 1], ![2, -1, 3, -4]]

def raw6360step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, 1, -1], ![0, -1, -2, 3], ![2, 1, 1, -4]]

def raw6360step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 0, -2], ![1, -1, -1, 1], ![0, 1, 2, -3], ![-2, -1, -1, 4]]

def raw6360step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def raw6361 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 3, -4]]

def raw6362 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw6362step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 0, -2], ![1, -1, 1, -1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, -2, 3]]

def raw6362step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw6363 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def raw6363step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 0, -2], ![1, -1, 1, -1], ![0, -1, 1, 0], ![-1, 1, -2, 2], ![-1, 0, 0, 1]]

def raw6363step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw6364 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw6365 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw6365step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 0, -2], ![1, -1, 1, -1], ![0, -1, 0, 1], ![-1, 1, -2, 2], ![-1, 0, 1, 0]]

def raw6365step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw6366 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 1, 0, -1], ![1, -1, 3, -3], ![1, 0, -2, 1]]

def raw6367 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw6367step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 0, -2], ![1, -1, 1, -1], ![0, -1, -2, 3], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw6367step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical199
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6368 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw6368step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 3, -4]]

def raw6369 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw6370 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 1, 3, -4], ![2, -1, -2, 1]]

def raw6370step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, 1, -1], ![0, -1, 3, -2], ![2, 1, -4, 1]]

def raw6370step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 0, -2], ![1, -1, -1, 1], ![0, 1, -3, 2], ![-2, -1, 4, -1]]

def raw6370step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw6371 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def raw6371step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 0, -2], ![1, -1, 1, -1], ![-1, 1, 1, -1], ![-1, -1, -2, 4]]

def raw6371step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw6372 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![1, -1, 3, -3], ![1, 1, -2, 0]]

def raw6372step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 1, -1, 1], ![0, -1, 3, -2], ![2, 1, -3, 0]]

def raw6372step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def raw6373 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![1, 0, -2, 1], ![1, 0, 3, -4]]

def raw6373step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def raw6374 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![1, 0, 2, -3], ![1, 0, -1, 0]]

def raw6374step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1]]

def raw6375 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![1, 0, 3, -4], ![1, 0, -2, 1]]

def raw6375step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def raw6376 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![1, 1, -2, 0], ![1, -1, 3, -3]]

def raw6376step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 1, 1, -1], ![0, -1, -2, 3], ![2, 1, 0, -3]]

def raw6376step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def raw6377 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, 2, -2], ![1, -1, 1, -1], ![1, 1, -3, 1]]

def raw6377step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 1, -1, 1], ![0, 2, 1, -3], ![2, -2, -1, 1]]

def raw6377step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![1, -1, 1, -1], ![0, -2, -1, 3], ![-2, 2, 1, -1]]

def raw6377step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def raw6378 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, 3, -3], ![1, -1, 0, 0], ![1, 1, -3, 1]]

def raw6378step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 1, -1, 1], ![0, 3, 0, -3], ![2, -3, 0, 1]]

def raw6378step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -3, 3], ![0, 2, 1, -3], ![1, -1, 1, -1]]

def raw6379 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 2, -3, 2], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw6379step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 2, -1, 0], ![0, -3, 0, 3], ![2, 2, 0, -4]]

def raw6379step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 2, -4, 2], ![1, -1, 1, -1]]

def raw6380 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 2, -3, 2], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def raw6380step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 2, -1, 0], ![0, -3, 3, 0], ![2, 2, -3, -1]]

def raw6380step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![1, -2, 1, 0], ![0, 3, -3, 0], ![-2, -2, 3, 1]]

def raw6380step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -3, 3], ![0, 1, 1, -2], ![1, -2, 3, -2]]

def raw6381 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 2, -2, 1], ![1, -1, -1, 1], ![1, 0, 3, -4]]

def raw6381step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 2, -1, 0], ![0, -2, -1, 3], ![2, 1, 1, -4]]

def raw6381step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![1, -2, 1, 0], ![0, 2, 1, -3], ![-2, -1, -1, 4]]

def raw6381step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw6382 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 2, -2, 1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw6382step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 2, -1, 0], ![0, -2, 3, -1], ![2, 1, -3, 0]]

def raw6382step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw6383 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 2, -1, 0], ![1, -1, 3, -3], ![1, 0, -2, 1]]

def raw6383step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 2, -1, 0], ![0, -1, 3, -2], ![2, 0, -3, 1]]

def raw6383step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 2, -3]]

def raw6384 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -2, 3], ![0, 1, 2, -3], ![1, 1, 0, -2]]

def raw6385 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -2, 3], ![0, 2, 2, -4], ![1, 0, 0, -1]]

def raw6386 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -2, 3], ![1, 2, 2, -5]]

def raw6386step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, -2, 2], ![2, 3, -5]]

def raw6386step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 1, -2], ![0, 2, -2], ![-2, -3, 5]]

def raw6386step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def raw6387 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 3, -4]]

def raw6388 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def raw6389 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def raw6390 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, 1, 2, -4]]

def raw6390step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 0, -2], ![0, 1, 1, -2], ![0, -1, 1, 0], ![-1, -1, -2, 4]]

def raw6390step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw6391 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, 1, -1, -1]]

def raw6392 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, 1, -2, 0]]

def raw6393 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 2, -2, 0], ![1, 0, 3, -4]]

def raw6394 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw6394step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 0, -2], ![0, 1, 1, -2], ![0, -2, 0, 2], ![-1, 0, -1, 2]]

def raw6394step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw6395 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw6395step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 0, -2], ![0, 1, 1, -2], ![0, -2, -1, 3], ![-1, 0, 0, 1]]

def raw6395step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw6396 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw6397 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![1, 2, 1, -4]]

def raw6397step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![2, 2, -4]]

def raw6397step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 1, -2], ![0, 1, -1], ![-2, -2, 4]]

def raw6397step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw6398 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw6398step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 0, -2], ![0, 1, 0, -1], ![0, 0, 1, -1], ![0, -2, -1, 3], ![-1, 0, 0, 1]]

def raw6398step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw6399 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

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

def raw64 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]

def raw64step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

def raw65 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]

def raw65step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

def raw66 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]

def raw66step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 4, -4], ![1, -2, 1], ![1, -1, 0]]

def raw67 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]

def raw67step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 4, -4], ![1, -2, 1], ![1, -1, 0]]

def raw69 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]

def raw69step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![1, -3, 2], ![1, -1, 0]]

def raw72 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]

def raw72step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]

def raw72step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![1, -2, 1], ![1, -2, 1]]

def raw74 : Matrix (Fin 3) (Fin 4) ℤ := ![![-4, 1, 1, 2], ![2, -2, 1, -1], ![2, 1, -2, -1]]

def raw74step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]

def raw74step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]

def raw74step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]

def raw75 : Matrix (Fin 3) (Fin 4) ℤ := ![![-4, 1, 2, 1], ![2, -2, -1, 1], ![2, 1, -1, -2]]

def raw75step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![2, -1, -1], ![1, 1, -2]]

def raw75step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 2, -1], ![-2, 1, 1], ![-1, -1, 2]]

def raw75step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]

def raw76 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]

def raw76step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]

def raw76step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def raw77 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]

def raw77step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]

def raw78 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw640 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]

def raw640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

def raw641 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]

def raw641step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

def raw642 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]

def raw642step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -3, 2], ![1, 2, -3]]

def raw644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]

def raw644step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]

def raw644step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

def raw645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]

def raw645step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]

def raw645step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def raw646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]

def raw646step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

def raw647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]

def raw647step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]

def raw647step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]

def raw648step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]

def raw648step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]

def raw649step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]

def raw649step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

def raw650 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]

def raw650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]

def raw650step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]

def raw651 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]

def raw651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

def raw652 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]

def raw652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]

def raw652step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def raw653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]

def raw653step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]

def raw653step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]

def raw654step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

def raw655 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]

def raw655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

def raw656 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]

def raw656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]

def raw656step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def raw657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw657step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]

def raw657step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def raw658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]

def raw658step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]

def raw659 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]

def raw659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]

def raw660 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]

def raw660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]

def raw660step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]

def raw662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def raw662step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]

def raw662step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw663 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]

def raw663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]

def raw663step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw664 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]

def raw664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]

def raw664step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw665 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]

def raw665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]

def raw665step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def raw666 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]

def raw666step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![2, 1, -3]]

def raw667 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]

def raw667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]

def raw667step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw668 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]

def raw668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]

def raw669 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]

def raw669step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]

def raw670 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]

def raw670step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]

def raw671 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]

def raw671step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-2, 2, 0], ![-2, 0, 2]]

def raw671step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical200
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6400 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw6401 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw6401step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![0, 0, 1, -1], ![2, 1, -3, 0]]

def raw6401step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 1, -2, 0], ![0, 0, -1, 1], ![-2, -1, 3, 0]]

def raw6401step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw6402 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw6402step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![0, 0, 2, -2], ![2, 1, -4, 1]]

def raw6402step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 1, -2, 0], ![0, 0, -2, 2], ![-2, -1, 4, -1]]

def raw6402step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

def raw6403 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw6404 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw6405 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-1, 0, -1, 2], ![1, 1, 2, -4]]

def raw6405step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 1, 0, -2], ![0, 1, -1, 0], ![0, -1, 1, 0], ![-1, 0, 1, 0], ![1, 0, 1, -2], ![-1, -1, -2, 4]]

def raw6405step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 0, 1, 0], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2], ![1, 1, 0, -2]]

def raw6406 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw6407 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, 2, -4], ![1, 0, -3, 2]]

def raw6408 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def raw6409 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw6410 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw6411 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 1, -1, -1]]

def raw6412 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def raw6412step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 0, -2], ![0, 1, -2, 1], ![0, -1, 0, 1], ![-1, -1, 2, 0]]

def raw6412step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw6413 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 1, -3, 1]]

def raw6413step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 0, -2], ![0, 1, -2, 1], ![0, -1, -1, 2], ![-1, -1, 3, -1]]

def raw6413step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw6414 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw6415 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw6416 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw6417 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, 0, -3, 2]]

def raw6418 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![1, 2, -2, -1]]

def raw6418step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![2, -1, -1]]

def raw6418step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 1, -2], ![0, -2, 2], ![-2, 1, 1]]

def raw6418step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw6419 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![1, 2, -3, 0]]

def raw6419step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![2, -2, 0]]

def raw6419step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 1, -2], ![0, -3, 3], ![-2, 2, 0]]

def raw6419step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

def raw6420 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -3, 3], ![1, 1, 3, -5]]

def raw6420step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -3, 3], ![2, 3, -5]]

def raw6420step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, 3, -3], ![-2, -3, 5]]

def raw6420step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def raw6421 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![-1, 2, -1, 0], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def raw6421step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 0, -2], ![0, 0, 2, -2], ![1, -2, 1, 0], ![-1, 1, -3, 3], ![-1, 0, 0, 1]]

def raw6421step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, 0, 1], ![0, 0, 2, -2], ![1, -1, -3, 3], ![1, 1, 0, -2]]

def raw6422 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![-1, 2, 0, -1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw6422step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 0, -2], ![0, 0, 2, -2], ![1, -2, 0, 1], ![-1, 1, -3, 3], ![-1, 0, 1, 0]]

def raw6422step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 1, 0], ![0, 0, 2, -2], ![1, -1, -3, 3], ![1, 1, 0, -2]]

def raw6423 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, 1, -1, -1]]

def raw6424 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![0, 0, 3, -3], ![1, 0, 0, -1]]

def raw6424step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw6425 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw6426 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, -1, 3, -3], ![0, 1, 0, -1]]

def raw6426step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 3, -3]]

def raw6427 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, 0, 3, -4]]

def raw6428 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 0, 3, -3], ![1, 0, -1, 0]]

def raw6428step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw6429 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 3, -3], ![0, 1, -1, 0]]

def raw6429step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 3, -3]]

def raw6430 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def raw6431 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def raw6431step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical201
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6432 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def raw6432step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, 0, 3, -4]]

def raw6433 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, -1, -1], ![1, -1, 3, -3]]

def raw6434 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -1, 2, -2]]

def raw6434step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 0, -2], ![0, 0, 2, -2], ![0, -2, 0, 2], ![-1, 1, -2, 2]]

def raw6434step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw6435 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -1, 1, -1]]

def raw6436 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -1, 0, 0]]

def raw6437 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![1, 1, 2, -4]]

def raw6437step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2], ![2, 2, -4]]

def raw6437step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, 2, -2], ![-2, -2, 4]]

def raw6437step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw6438 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![-1, 2, -2, 1], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def raw6438step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 0, -2], ![0, 0, 1, -1], ![1, -2, 2, -1], ![-1, 1, -3, 3], ![-1, 0, 0, 1]]

def raw6438step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![1, -1, -3, 3], ![1, 1, 0, -2]]

def raw6439 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![-1, 2, -1, 0], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw6439step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 0, -2], ![0, 0, 1, -1], ![1, -2, 1, 0], ![-1, 1, -3, 3], ![-1, 0, 1, 0]]

def raw6439step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, -1, 3, -3], ![1, 1, -2, 0]]

def raw6440 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![-1, 2, 0, -1], ![1, -1, 3, -3], ![1, 0, -2, 1]]

def raw6440step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 0, -2], ![0, 0, 1, -1], ![1, -2, 0, 1], ![-1, 1, -3, 3], ![-1, 0, 2, -1]]

def raw6440step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 2, -1], ![0, 0, 1, -1], ![1, -1, -3, 3], ![1, 1, 0, -2]]

def raw6441 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, -1, 0, 1], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw6441step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 0, -2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, -2, -1, 3], ![-1, 0, 0, 1]]

def raw6441step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw6442 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-1, -1, 2, 0], ![2, 1, 1, -4]]

def raw6442step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 1, 0, -2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![1, 1, -2, 0], ![-2, -1, -1, 4]]

def raw6442step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def raw6443 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 3, -4]]

def raw6444 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def raw6444step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def raw6445 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def raw6445step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 3, -4]]

def raw6446 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, 1, -1]]

def raw6447 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, 0, 0]]

def raw6448 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-1, 2, -1, 0], ![1, 0, 3, -4]]

def raw6448step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 1, 0, -2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![1, -2, 1, 0], ![-1, 0, -3, 4]]

def raw6448step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw6449 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw6450 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![0, 0, 3, -3], ![1, 0, 0, -1]]

def raw6450step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw6451 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw6452 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, -1, 3, -3], ![0, 1, 0, -1]]

def raw6452step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 3, -3]]

def raw6453 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, 0, 3, -4]]

def raw6454 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 0, -1, 1], ![1, 0, 3, -4]]

def raw6454step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 3, -4]]

def raw6455 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 0, 2, -2], ![1, 0, 0, -1]]

def raw6455step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw6456 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 0, 3, -3], ![1, 0, -1, 0]]

def raw6456step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def raw6457 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-1, -1, 1, 1], ![2, 0, 2, -4]]

def raw6457step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 1, 0, -2], ![0, 0, 1, -1], ![0, -1, 1, 0], ![0, -1, 1, 0], ![1, 1, -1, -1], ![-2, 0, -2, 4]]

def raw6457step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def raw6458 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 3, -3]]

def raw6459 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw6460 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def raw6461 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 3, -3], ![0, 1, -1, 0]]

def raw6461step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 3, -3]]

def raw6462 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def raw6463 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 0, 3, -3], ![1, 0, -2, 1]]

def raw6463step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical202
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6464 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 3, -3], ![0, 1, -2, 1]]

def raw6464step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 3, -3]]

def raw6465 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw6466 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw6466step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw6467 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw6467step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def raw6468 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, 0, -2, 1]]

def raw6468step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, 0, 3, -4]]

def raw6469 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 2, -2, 0], ![1, -1, 3, -3]]

def raw6469step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![0, -1, -2, 3], ![2, 1, 0, -3]]

def raw6469step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 2, -3]]

def raw6470 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw6470step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 0, -2], ![0, 0, 1, -1], ![0, -2, 0, 2], ![-1, 1, -1, 1]]

def raw6470step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw6471 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, 0, 0]]

def raw6471step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 0, -2], ![0, 0, 1, -1], ![0, -2, -1, 3], ![-1, 1, 0, 0]]

def raw6471step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw6472 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, -1, 1]]

def raw6472step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![0, -1, 2, -1], ![2, 1, -4, 1]]

def raw6472step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 0, -2, 1], ![0, 1, -2, 1], ![-2, -1, 4, -1]]

def raw6472step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw6473 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 0, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw6473step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 1, 0], ![0, 0, 1, -1], ![2, 0, -2, 0]]

def raw6473step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0]]

def raw6473step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0]]

def raw6474 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 0, 0], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw6474step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![0, 0, 1, -1], ![2, 0, -3, 1]]

def raw6474step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 0, -2, 1], ![0, 0, -1, 1], ![-2, 0, 3, -1]]

def raw6474step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -2, 1], ![0, -1, 1], ![-2, 3, -1]]

def raw6474step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw6475 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 0, 0], ![1, 1, 0, -2]]

def raw6475step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![2, 0, -2]]

def raw6475step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![2, 0, -2]]

def raw6475step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw6475step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw6476 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw6476step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw6477 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 0, 0], ![1, 1, -1, -1]]

def raw6477step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def raw6477step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1]]

def raw6477step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw6478 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, -1, 1, -1]]

def raw6479 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw6480 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw6481 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 1, -2, 0]]

def raw6482 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 2, -3, 1], ![1, -1, 0, 0]]

def raw6483 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 0, 0, 0], ![1, 0, 0, -1]]

def raw6483step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw6484 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1]]

def raw6485 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0]]

def raw6485step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw6486 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw6487 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw6487step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw6488 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw6488step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw6489 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, -1, 2, -2]]

def raw6490 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 1, -1]]

def raw6490step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![0, 1, -2, 1], ![2, -1, 0, -1]]

def raw6490step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 0, -2, 1], ![0, -1, 2, -1], ![-2, 1, 0, 1]]

def raw6490step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw6491 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def raw6491step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw6492 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw6492step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1]]

def raw6493 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -2, 2]]

def raw6494 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![1, 1, -1, -1]]

def raw6494step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1]]

def raw6494step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw6495 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw6495step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical203
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6496 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw6496step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw6497 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, -1, 0, 0]]

def raw6497step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 2, -3, 1], ![1, -1, 0, 0]]

def raw6498 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw6499 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 0, -1, 1], ![1, 0, 0, -1]]

def raw6499step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw6500 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 0, 0, 0], ![1, 0, -1, 0]]

def raw6500step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def raw6501 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw6502 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1]]

def raw6503 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def raw6504 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw6505 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, -2, 1]]

def raw6505step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw6506 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -3, 1], ![1, -1, 1, -1]]

def raw6507 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw6508 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw6509 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw6510 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![1, 1, -2, 0]]

def raw6510step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0]]

def raw6510step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

def raw6511 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -3, 2], ![1, 0, 0, -1]]

def raw6512 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw6513 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, -1, 0]]

def raw6514 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![0, 1, -2, 1], ![1, -1, 0, 0]]

def raw6514step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw6515 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1]]

def raw6516 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, 0, -2, 1]]

def raw6516step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, -1, 0]]

def raw6517 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 2, -3, 1], ![1, -1, 0, 0]]

def raw6518 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, -1, 1]]

def raw6519 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![1, 1, -3, 1]]

def raw6519step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![2, -3, 1]]

def raw6519step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -3, 3], ![-2, 3, -1]]

def raw6519step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw6520 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 4, -4], ![1, 1, -4, 2]]

def raw6520step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 4, -4], ![2, -4, 2]]

def raw6520step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -4, 4], ![-2, 4, -2]]

def raw6520step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

def raw6521 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -3, 2], ![0, 0, 3, -3], ![1, 0, 0, -1]]

def raw6521step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -3, 2], ![1, 0, 0, -1]]

def raw6522 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -3, 2], ![0, 1, 0, -1], ![1, -1, 3, -3]]

def raw6523 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -3, 2], ![0, 1, 2, -3], ![1, -1, 1, -1]]

def raw6524 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -3, 2], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw6525 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -3, 2], ![1, 0, 3, -4]]

def raw6525step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -3, 3], ![2, 2, -4]]

def raw6525step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -1, 0], ![0, 3, -3], ![-2, -2, 4]]

def raw6525step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw6526 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 0, 2, -2], ![1, 0, 0, -1]]

def raw6526step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw6527 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -1, 3, -3]]

def raw6527step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![0, -2, -1, 3], ![2, 1, 0, -3]]

def raw6527step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 1, -1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical204
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6528 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 2, -2]]

def raw6528step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 0, -2], ![0, -1, 2, -1], ![0, -1, 0, 1], ![-1, 1, -2, 2]]

def raw6528step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw6529 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw6530 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw6531 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def raw6532 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![1, 0, 2, -3]]

def raw6532step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -2, 2], ![2, 1, -3]]

def raw6532step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -1, 0], ![0, 2, -2], ![-2, -1, 3]]

def raw6532step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw6533 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 0, 2, -2], ![1, 0, -1, 0]]

def raw6533step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def raw6534 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, -2, 1], ![1, -1, 3, -3]]

def raw6534step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![0, -1, -2, 3], ![2, 0, 1, -3]]

def raw6534step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 1, -1, -1]]

def raw6535 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 2, -2]]

def raw6535step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![0, -1, -1, 2], ![2, 0, 0, -2]]

def raw6535step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, -1, -1]]

def raw6536 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1]]

def raw6536step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 0, -2], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 1, -1, 1]]

def raw6536step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw6537 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw6537step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw6538 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1]]

def raw6539 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -2, 2]]

def raw6540 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw6540step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2]]

def raw6540step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0]]

def raw6541 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 1, -1]]

def raw6541step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 0, -2], ![0, -1, 0, 1], ![0, -1, 1, 0], ![-1, 1, -1, 1]]

def raw6541step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw6542 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -1, -1, 1]]

def raw6542step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 0, -2], ![0, -1, 0, 1], ![0, -1, -1, 2], ![-1, 1, 1, -1]]

def raw6542step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw6543 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw6543step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![1, 0, -1]]

def raw6544 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 1, -2], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw6544step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw6545 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 1, -2], ![0, 1, 0, -1], ![1, -1, -1, 1]]

def raw6545step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 0, -2], ![0, -1, -1, 2], ![0, -1, 0, 1], ![-1, 1, 1, -1]]

def raw6545step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw6546 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw6546step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0]]

def raw6546step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0]]

def raw6547 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 2, -3], ![0, -1, 1, 0], ![1, 1, -3, 1]]

def raw6547step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 0, -2], ![0, -1, -2, 3], ![0, 1, -1, 0], ![-1, -1, 3, -1]]

def raw6547step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def raw6548 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 2, -3], ![0, 1, -2, 1], ![1, -1, 0, 0]]

def raw6548step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw6549 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 2, -3], ![0, 1, -1, 0], ![1, -1, -1, 1]]

def raw6549step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1]]

def raw6550 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 2, -3], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw6550step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, -1, -2, 2]]

def raw6551 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 2, -3], ![1, -1, 1, -1], ![0, 1, -3, 2]]

def raw6551step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -3, 2], ![0, 1, 2, -3], ![1, -1, 1, -1]]

def raw6552 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 2, -3], ![1, 0, -2, 1]]

def raw6552step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1]]

def raw6552step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 3, -1]]

def raw6552step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw6553 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 3, -4], ![0, -1, 0, 1], ![1, 1, -3, 1]]

def raw6553step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, -1, 1], ![0, 3, 0, -3], ![2, -4, 1, 1]]

def raw6553step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, -1, 1, -1], ![0, -3, 0, 3], ![-2, 4, -1, -1]]

def raw6553step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, 1, -1, -1]]

def raw6554 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 3, -4], ![1, -1, 0, 0], ![0, 1, -3, 2]]

def raw6554step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -3, 2], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw6555 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 3, -4], ![1, 0, -3, 2]]

def raw6555step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 3, -3], ![2, -4, 2]]

def raw6555step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -1, 0], ![0, -3, 3], ![-2, 4, -2]]

def raw6555step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw6556 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 2, -3, 1], ![1, -1, 3, -3]]

def raw6556step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, -3, 3], ![2, 1, -3]]

def raw6556step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -2, 1], ![0, 3, -3], ![-2, -1, 3]]

def raw6556step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw6557 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 2, -2, 0], ![1, -1, 2, -2]]

def raw6557step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, -2, 2], ![2, 0, -2]]

def raw6557step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

def raw6558 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def raw6558step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1]]

def raw6558step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1]]

def raw6558step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]

def raw6559 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw6559step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1]]

def raw6559step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -2, 1], ![0, -1, 1], ![-2, 3, -1]]

def raw6559step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical205
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6560 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 2, 2, -4], ![1, -1, -2, 2]]

def raw6560step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, 2, -2], ![2, -4, 2]]

def raw6560step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -2, 1], ![0, -2, 2], ![-2, 4, -2]]

def raw6560step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def raw6561 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![1, -1, -2, 2], ![0, 2, 2, -4]]

def raw6561step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2], ![2, 2, -4]]

def raw6561step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![1, 1, -2], ![0, 2, -2], ![-2, -2, 4]]

def raw6561step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def raw6562 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![1, -1, 1, -1], ![0, 2, -1, -1]]

def raw6562step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1]]

def raw6562step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![1, 1, -2], ![0, -1, 1], ![-2, 1, 1]]

def raw6562step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]

def raw6563 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![1, -1, 2, -2], ![0, 2, -2, 0]]

def raw6563step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 2, -2], ![2, -2, 0]]

def raw6563step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

def raw6564 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![1, -1, 3, -3], ![0, 2, -3, 1]]

def raw6564step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 3, -3], ![2, -3, 1]]

def raw6564step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![1, 1, -2], ![0, -3, 3], ![-2, 3, -1]]

def raw6564step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw6565 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![1, 0, -3, 2], ![0, 1, 3, -4]]

def raw6565step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3], ![2, 2, -4]]

def raw6565step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![1, 0, -1], ![0, 3, -3], ![-2, -2, 4]]

def raw6565step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw6566 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![1, 0, -2, 1], ![0, 1, 2, -3]]

def raw6566step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![2, 1, -3]]

def raw6566step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![1, 0, -1], ![0, 2, -2], ![-2, -1, 3]]

def raw6566step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw6567 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![1, 0, 2, -3], ![0, 1, -2, 1]]

def raw6567step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 2, -2], ![2, -3, 1]]

def raw6567step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![1, 0, -1], ![0, -2, 2], ![-2, 3, -1]]

def raw6567step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw6568 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![1, 0, 3, -4], ![0, 1, -3, 2]]

def raw6568step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 3, -3], ![2, -4, 2]]

def raw6568step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![1, 0, -1], ![0, -3, 3], ![-2, 4, -2]]

def raw6568step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw6569 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-4, 2, 1, 1], ![5, -1, -2, -2]]

def raw6569step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -4, 5], ![-1, 2, -1], ![1, 1, -2], ![1, 1, -2]]

def raw6570 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-3, 2, 1, 0], ![4, -1, -2, -1]]

def raw6570step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, 1, -2], ![1, 0, -1]]

def raw6570step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2]]

def raw6571 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-3, 3, 1, -1], ![4, -2, -2, 0]]

def raw6571step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![1, 1, -2], ![1, -1, 0]]

def raw6571step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![1, -1, 0], ![1, 1, -2]]

def raw6572 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-2, -1, 1, 2], ![3, 2, -2, -3]]

def raw6572step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![1, 1, -2], ![1, 2, -3]]

def raw6573 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-2, -1, 2, 1], ![3, 2, -3, -2]]

def raw6573step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![1, 2, -3], ![1, 1, -2]]

def raw6573step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![1, 1, -2], ![1, 2, -3]]

def raw6574 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-2, 2, -2, 2], ![3, -1, 1, -3]]

def raw6574step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 2, -3]]

def raw6575 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-2, 2, 1, -1], ![3, -1, -2, 0]]

def raw6575step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, 1, -2], ![1, -1, 0]]

def raw6575step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

def raw6576 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-2, 3, -2, 1], ![3, -2, 1, -2]]

def raw6576step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![1, -2, 1], ![1, 1, -2]]

def raw6577 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-2, 3, 1, -2], ![3, -2, -2, 1]]

def raw6577step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![1, 1, -2], ![1, -2, 1]]

def raw6577step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![1, -2, 1], ![1, 1, -2]]

def raw6578 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, -2, 2, 1], ![2, 3, -3, -2]]

def raw6578step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![1, 2, -3], ![1, 1, -2]]

def raw6578step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![1, 1, -2], ![1, 2, -3]]

def raw6579 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, -2, 3, 0], ![2, 3, -4, -1]]

def raw6579step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![1, 3, -4], ![1, 0, -1]]

def raw6579step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 2, -3], ![-1, -3, 4], ![-1, 0, 1]]

def raw6579step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 0, 1], ![1, 1, -2], ![1, 2, -3]]

def raw6580 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, -1, 1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw6581 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, -1, 1, 1], ![0, 1, -1, 0], ![1, 1, -1, -1], ![1, 0, 0, -1]]

def raw6581step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, -1, 1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw6582 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, -1, 1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw6582step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, -1, 1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw6583 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, -1, 1, 1], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw6583step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def raw6584 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, -1, 1, 1], ![1, 0, 0, -1], ![1, 2, -2, -1]]

def raw6584step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, -1, 0, 2], ![1, 1, 0, -2], ![1, 1, -1, -1]]

def raw6584step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, -1, -1, 1]]

def raw6585 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, -1, 1, 1], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def raw6586 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, -1, 1, 1], ![2, 2, -2, -2]]

def raw6586step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![1, 1, -2], ![1, 1, -2]]

def raw6587 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, -1, 2, 0], ![2, 2, -3, -1]]

def raw6587step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![1, 2, -3], ![1, 0, -1]]

def raw6587step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-1, -2, 3], ![-1, 0, 1]]

def raw6587step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]

def raw6588 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, -1, 3, -1], ![2, 2, -4, 0]]

def raw6588step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![1, 3, -4], ![1, -1, 0]]

def raw6588step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-1, -3, 4], ![-1, 1, 0]]

def raw6588step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2]]

def raw6589 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 0, 0, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw6589step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0]]

def raw6590 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 0, 0, 1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw6590step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1]]

def raw6591 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 2, -2, 1], ![2, -1, 1, -2]]

def raw6591step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical206
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6592 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 2, 1, -2], ![2, -1, -2, 1]]

def raw6592step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![1, 1, -2], ![1, -2, 1]]

def raw6592step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2]]

def raw6593 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 3, -3, 1], ![2, -2, 2, -2]]

def raw6593step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![1, -3, 2], ![1, 1, -2]]

def raw6593step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 2, -3]]

def raw6594 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 3, -2, 0], ![2, -2, 1, -1]]

def raw6594step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![1, -2, 1], ![1, 0, -1]]

def raw6594step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

def raw6595 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 4, -3, 0], ![2, -3, 2, -1]]

def raw6595step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 4, -3], ![1, -3, 2], ![1, 0, -1]]

def raw6595step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 2, -3]]

def raw6596 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -2, 2, 0], ![1, 3, -3, -1]]

def raw6596step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![1, 2, -3], ![1, 0, -1]]

def raw6596step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![2, 1, -3]]

def raw6597 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -2, 3, -1], ![1, 3, -4, 0]]

def raw6597step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![1, 3, -4], ![1, -1, 0]]

def raw6597step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 2, -3], ![-1, -3, 4], ![-1, 1, 0]]

def raw6597step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3]]

def raw6598 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 1, 1, -2], ![1, 1, 0, -2]]

def raw6598step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![0, 1, 2, -3], ![0, -1, -1, 2], ![-1, -1, 0, 2]]

def raw6598step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, 1, -1, -1]]

def raw6599 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw6599step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![0, 1, 2, -3], ![0, -2, 0, 2], ![-1, 0, -1, 2]]

def raw6599step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -1, 1, -1]]

def raw6600 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw6601 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw6602 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![1, 2, 1, -4]]

def raw6602step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 3, -4]]

def raw6602step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 1, -2], ![-1, 2, -1], ![-1, -3, 4]]

def raw6602step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2]]

def raw6603 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw6604 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw6605 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 1, -2, 1], ![1, 1, 2, -4]]

def raw6605step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![0, 1, 1, -2], ![0, -1, 2, -1], ![-1, -1, -2, 4]]

def raw6605step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw6606 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def raw6607 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw6608 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, 1, 1, -3]]

def raw6608step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![0, 1, 1, -2], ![0, -1, 1, 0], ![-1, -1, -1, 3]]

def raw6608step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw6609 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw6610 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, -2, 0], ![1, 0, 2, -3]]

def raw6611 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw6611step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![0, 1, 1, -2], ![0, -2, 1, 1], ![-1, 0, -1, 2]]

def raw6611step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw6612 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw6612step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1]]

def raw6613 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw6614 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw6615 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![1, 2, 0, -3]]

def raw6615step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3]]

def raw6615step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, -2, 3]]

def raw6615step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw6616 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw6616step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, -1, -1], ![0, 1, 0, -1], ![0, 0, 1, -1], ![0, -2, 0, 2], ![-1, 0, 0, 1]]

def raw6616step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 1, -1]]

def raw6617 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw6617step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 1, -1]]

def raw6618 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw6618step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![1, 0, 1, -2], ![1, 1, -3, 1]]

def raw6618step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 1, -2, 0], ![-1, 0, -1, 2], ![-1, -1, 3, -1]]

def raw6618step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw6619 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw6619step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 1, -1, -1]]

def raw6620 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw6620step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0]]

def raw6621 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 1, -1, -1]]

def raw6621step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1]]

def raw6622 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 0, -1, 1], ![1, 1, -1, -1]]

def raw6622step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 1, -1, -1]]

def raw6623 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![0, 1, -1, 0]]

def raw6623step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical207
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6624 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 1, 0], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw6624step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![1, 1, -2, 0], ![1, 0, 0, -1]]

def raw6624step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw6625 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw6625step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 1, -1]]

def raw6626 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 1, 0], ![1, 2, -2, -1]]

def raw6626step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1]]

def raw6626step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

def raw6627 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 2, -1], ![1, 2, -3, 0]]

def raw6627step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![1, 2, -3], ![1, -1, 0]]

def raw6627step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 1, -2], ![-1, -2, 3], ![-1, 1, 0]]

def raw6627step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw6628 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 3, -2], ![1, 2, -4, 1]]

def raw6628step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![1, 3, -4], ![1, -2, 1]]

def raw6628step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 1, -2], ![-1, -3, 4], ![-1, 2, -1]]

def raw6628step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2]]

def raw6629 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -3, 3], ![0, 2, 2, -4], ![1, -1, 0, 0]]

def raw6629step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![1, -3, 2, 0], ![1, 3, -4, 0]]

def raw6629step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -3, 2], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw6630 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -3, 3], ![1, 1, 2, -4]]

def raw6630step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2], ![1, 3, -4]]

def raw6630step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![-1, 3, -2], ![-1, -3, 4]]

def raw6630step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1]]

def raw6631 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, 0, 0]]

def raw6632 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw6633 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def raw6634 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw6635 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw6635step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw6636 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw6636step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def raw6637 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw6638 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -1, 0, 0]]

def raw6638step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![1, -2, 1, 0], ![1, 2, -3, 0]]

def raw6638step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw6639 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -1, -1, 1]]

def raw6640 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![1, 1, 1, -3]]

def raw6640step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 2, -3]]

def raw6640step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, -2, 3]]

def raw6640step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw6641 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, -1, -1, 2], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw6641step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw6642 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw6642step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw6643 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, -1, 0, 1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw6643step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, -1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, -2, 0, 2], ![-1, 0, 0, 1]]

def raw6643step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 1, -1]]

def raw6644 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -1, 0, 0]]

def raw6644step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, 0, 0]]

def raw6645 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def raw6646 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw6646step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw6647 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw6647step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def raw6648 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw6648step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, -1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -2, 0, 2], ![-1, 1, -1, 1]]

def raw6648step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 1, -1]]

def raw6649 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, 0, 0]]

def raw6650 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, -1, 1]]

def raw6651 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw6652 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, 0, 2, -3]]

def raw6653 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 0, -1, 1], ![1, 0, 2, -3]]

def raw6653step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def raw6654 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 0, 1, -1], ![1, 0, 0, -1]]

def raw6654step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw6655 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 2, -2]]

def raw6655step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical208
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6656 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw6657 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1]]

def raw6658 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw6659 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw6660 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw6660step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw6661 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw6661step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw6661step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw6662 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw6662step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![1, -1, 1, -1], ![1, 1, -3, 1]]

def raw6662step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 0, -2, 1], ![-1, 1, -1, 1], ![-1, -1, 3, -1]]

def raw6662step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw6663 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, -2, 2]]

def raw6663step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![1, -1, 2, -2], ![1, 1, -4, 2]]

def raw6663step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 0, -2, 1], ![-1, 1, -2, 2], ![-1, -1, 4, -2]]

def raw6663step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 2, -2]]

def raw6664 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw6664step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 1, 0], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw6664step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw6664step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]

def raw6665 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 0, 0], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw6665step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![1, 0, 0, -1], ![1, 0, -2, 1]]

def raw6665step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, -2, 1]]

def raw6665step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]

def raw6666 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 0, 0], ![1, 1, -1, -1]]

def raw6666step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]

def raw6666step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw6667 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 1, -1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw6667step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw6668 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 1, -1], ![0, 0, -1, 1], ![1, 1, -1, -1]]

def raw6668step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 1, -1, -1]]

def raw6669 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, -1, 0, 0]]

def raw6669step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, 0, 0]]

def raw6670 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw6670step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw6671 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 0, -1, 1], ![1, 0, 0, -1]]

def raw6671step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw6672 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw6672step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -1, 1]]

def raw6673 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def raw6673step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw6674 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw6675 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, -1, 1, -1]]

def raw6675step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![1, 1, -3, 1], ![1, -1, 1, -1]]

def raw6675step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 0, -2, 1], ![-1, -1, 3, -1], ![-1, 1, -1, 1]]

def raw6675step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw6676 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw6676step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![1, 1, -2, 0], ![1, -1, 0, 0]]

def raw6676step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw6677 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw6677step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def raw6678 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw6678step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![1, 1, 0, -2], ![1, -1, -2, 2]]

def raw6678step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw6679 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -3, 3]]

def raw6679step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![1, 1, 1, -3], ![1, -1, -3, 3]]

def raw6679step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 0, -2, 1], ![-1, -1, -1, 3], ![-1, 1, 3, -3]]

def raw6679step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 3, -3]]

def raw6680 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 1, -1], ![1, 1, -2, 0]]

def raw6680step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0]]

def raw6680step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![-1, 1, 0]]

def raw6680step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw6681 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, -1, 0]]

def raw6681step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw6682 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 2, -2], ![0, 2, -3, 1], ![1, -1, 0, 0]]

def raw6682step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![1, 2, -3, 0], ![1, -2, 1, 0]]

def raw6682step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw6683 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, -1, 1]]

def raw6683step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw6684 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -3, 3]]

def raw6685 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -4, 3], ![1, 0, 3, -4]]

def raw6685step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -4, 3], ![1, 3, -4]]

def raw6685step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -1, 0], ![-1, 4, -3], ![-1, -3, 4]]

def raw6685step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 4, -3], ![1, -1, 0], ![1, 0, -1]]

def raw6686 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -3, 2], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw6687 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -3, 2], ![0, 1, 2, -3], ![1, -1, 0, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical209
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6688 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -3, 2], ![1, 0, 2, -3]]

def raw6688step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -3, 2], ![1, 2, -3]]

def raw6688step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -1, 0], ![-1, 3, -2], ![-1, -2, 3]]

def raw6688step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1]]

def raw6689 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -2, 1], ![0, 0, 1, -1], ![1, 0, 0, -1]]

def raw6689step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw6690 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 1, -1]]

def raw6690step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![0, -1, 2, -1], ![0, -1, 0, 1], ![-1, 1, -1, 1]]

def raw6690step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def raw6691 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw6692 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, -1, 1]]

def raw6692step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -3, 2], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw6693 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -2, 1], ![1, 0, 1, -2]]

def raw6693step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2]]

def raw6693step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]

def raw6694 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -1, 0], ![0, 0, 1, -1], ![1, 0, -1, 0]]

def raw6694step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw6695 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1]]

def raw6695step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw6695step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 1, -1, -1]]

def raw6696 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0]]

def raw6696step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 1, 0, 0]]

def raw6696step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw6697 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, -1, 1]]

def raw6697step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![0, -1, 1, 0], ![0, -1, -1, 2], ![-1, 1, 1, -1]]

def raw6697step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def raw6698 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -2, 2]]

def raw6698step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -3, 2], ![0, 1, 0, -1], ![1, -1, 2, -2]]

def raw6699 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw6699step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw6699step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]

def raw6700 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1]]

def raw6700step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![1, 0, 0, -1], ![1, -1, -1, 1]]

def raw6700step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 1, -1, -1]]

def raw6701 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -1, -2, 2]]

def raw6701step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![1, 0, 1, -2], ![1, -1, -2, 2]]

def raw6701step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw6702 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw6702step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0]]

def raw6702step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]

def raw6703 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, 1, -2], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw6703step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![1, 1, 0, -2], ![1, -2, -1, 2]]

def raw6703step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw6704 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, 2, -3], ![1, 0, -3, 2]]

def raw6704step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, 2, -3], ![1, -3, 2]]

def raw6704step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -1, 0], ![-1, -2, 3], ![-1, 3, -2]]

def raw6704step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1]]

def raw6705 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 2, -3, 1], ![1, -1, 2, -2]]

def raw6705step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![1, -3, 2], ![1, 1, -2]]

def raw6705step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -2, 1], ![-1, 3, -2], ![-1, -1, 2]]

def raw6705step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

def raw6706 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 2, -2, 0], ![1, -1, 1, -1]]

def raw6706step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1]]

def raw6706step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]

def raw6707 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def raw6707step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0]]

def raw6707step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw6708 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 2, 1, -3], ![1, -1, -2, 2]]

def raw6708step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![1, 1, -2], ![1, -3, 2]]

def raw6708step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -2, 1], ![-1, -1, 2], ![-1, 3, -2]]

def raw6708step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

def raw6709 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 2, 2, -4], ![1, -1, -3, 3]]

def raw6709step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![1, 2, -3], ![1, -4, 3]]

def raw6709step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -2, 1], ![-1, -2, 3], ![-1, 4, -3]]

def raw6709step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![1, -1, 0], ![1, 1, -2]]

def raw6710 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 3, -3, 0], ![1, -2, 2, -1]]

def raw6710step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 3, -2], ![1, -3, 2], ![1, 0, -1]]

def raw6710step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3]]

def raw6711 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 3, -2, -1], ![1, -2, 1, 0]]

def raw6711step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0]]

def raw6711step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw6712 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 4, -3, -1], ![1, -3, 2, 0]]

def raw6712step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 4, -3], ![1, -3, 2], ![1, -1, 0]]

def raw6712step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3]]

def raw6713 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, -2, 2, -1], ![0, 3, -3, 0]]

def raw6713step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![1, 2, -3], ![1, -1, 0]]

def raw6713step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3]]

def raw6714 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, -1, -3, 3], ![0, 2, 2, -4]]

def raw6714step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![1, -3, 2], ![1, 3, -4]]

def raw6714step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![1, 1, -2], ![-1, 3, -2], ![-1, -3, 4]]

def raw6714step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![1, -1, 0], ![1, 1, -2]]

def raw6715 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, -1, -2, 2], ![0, 2, 1, -3]]

def raw6715step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 2, -3]]

def raw6715step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![1, 1, -2], ![-1, 2, -1], ![-1, -2, 3]]

def raw6715step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

def raw6716 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, -1, 1, -1], ![0, 2, -2, 0]]

def raw6716step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![1, 1, -2], ![1, -1, 0]]

def raw6716step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]

def raw6717 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, 0, -3, 2], ![0, 1, 2, -3]]

def raw6717step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2], ![1, 2, -3]]

def raw6717step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![1, 0, -1], ![-1, 3, -2], ![-1, -2, 3]]

def raw6717step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1]]

def raw6718 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, 0, -2, 1], ![0, 1, 1, -2]]

def raw6718step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2]]

def raw6718step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]

def raw6719 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def raw6719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw672 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]

def raw672step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1]]

def raw672step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]

def raw673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]

def raw673step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]

def raw673step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]

def raw674 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]

def raw674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-2, 2, 0], ![-2, 0, 2]]

def raw674step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]

def raw675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def raw675step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]

def raw675step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]

def raw676 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]

def raw676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]

def raw676step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]

def raw677 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]

def raw677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]

def raw677step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

def raw678 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![3, -1, -2]]

def raw678step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![2, 1, -3]]

def raw679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw679step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]

def raw679step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

def raw680 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]

def raw680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]

def raw680step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw681 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]

def raw681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]

def raw681step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

def raw682 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]

def raw682step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]

def raw683 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]

def raw683step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-2, 2, 0], ![-2, 1, 1]]

def raw683step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def raw684 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -3, 3], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]

def raw684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 2, -3]]

def raw685 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -3, 3], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]

def raw685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]

def raw686 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]

def raw686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]

def raw687 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -3, 3], ![1, 0, -1], ![2, 2, -4]]

def raw687step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]

def raw688 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -3, 3], ![1, 2, -3], ![2, 0, -2]]

def raw688step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]

def raw689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]

def raw690 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![2, 1, -3]]

def raw690step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]

def raw690step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -3, 2], ![1, 2, -3]]

def raw691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

def raw692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def raw693 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]

def raw694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw695 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

def raw696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]

def raw696step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1]]

def raw697 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]

def raw697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1]]

def raw698 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]

def raw699 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![3, 0, -3]]

def raw699step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

def raw700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def raw701 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

def raw702 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

def raw703 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1], ![1, 0, -1]]

def raw703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical210
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6720 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def raw6720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def raw6721 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 4, -4], ![1, -1, 0], ![1, 0, -1]]

def raw6721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 4, -4], ![1, -1, 0], ![1, 0, -1]]

def raw6722 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw6722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, -2, 3]]

def raw6722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]

def raw6723 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw6724 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1]]

def raw6724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw6725 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def raw6726 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw6726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1]]

def raw6726step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]

def raw6727 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 2, -2], ![2, 0, -2]]

def raw6727step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, -2, 2], ![-2, 0, 2]]

def raw6727step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]

def raw6728 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw6729 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0]]

def raw6729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw6730 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![2, -1, -1]]

def raw6730step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, -3, 3], ![-2, 1, 1]]

def raw6730step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]

def raw6731 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 4, -4], ![1, -2, 1], ![1, 0, -1]]

def raw6732 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

def raw6733 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 4, -4], ![2, -2, 0]]

def raw6733step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, -4, 4], ![-2, 2, 0]]

def raw6733step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![1, -2, 1], ![1, -2, 1]]

def raw6734 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 2, -3]]

def raw6734step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-1, 0, 1], ![-1, -2, 3]]

def raw6734step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]

def raw6735 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![1, 1, -2], ![1, 1, -2]]

def raw6736 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![1, 2, -3], ![1, 0, -1]]

def raw6736step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-1, -2, 3], ![-1, 0, 1]]

def raw6736step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]

def raw6737 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![1, 3, -4], ![1, -1, 0]]

def raw6737step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-1, -3, 4], ![-1, 1, 0]]

def raw6737step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2]]

def raw6738 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![1, 4, -5], ![1, -2, 1]]

def raw6738step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-1, -4, 5], ![-1, 2, -1]]

def raw6738step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -4, 5], ![-1, 2, -1], ![1, 1, -2], ![1, 1, -2]]

def raw6740 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw6740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw6741 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw6741step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]

def raw6741step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw6742 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2]]

def raw6742step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

def raw6743 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw6744 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw6744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]

def raw6744step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw6745 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

def raw6746 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

def raw6746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw6747 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2]]

def raw6747step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]

def raw6748 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]

def raw6748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -2, 1], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2]]

def raw6748step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def raw6749 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]

def raw6749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -2, 1], ![0, 2, -2], ![-1, -1, 2], ![-1, 0, 1]]

def raw6749step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def raw6750 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

def raw6750step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1]]

def raw6750step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]

def raw6751 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]

def raw6751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1]]

def raw6751step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1]]

def raw6751step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical211
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6752 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

def raw6752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1]]

def raw6752step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw6753 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]

def raw6753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0]]

def raw6753step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]

def raw6754 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2]]

def raw6755 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1]]

def raw6755step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1]]

def raw6755step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]

def raw6756 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![0, -3, 3], ![1, 0, -1], ![1, 1, -2]]

def raw6756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -3, 2], ![0, 3, -3], ![-1, 0, 1], ![-1, -1, 2]]

def raw6756step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -3, 2], ![1, 1, -2]]

def raw6757 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![0, -3, 3], ![1, 1, -2], ![1, 0, -1]]

def raw6757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -3, 2], ![0, 3, -3], ![-1, -1, 2], ![-1, 0, 1]]

def raw6757step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -3, 2], ![1, 1, -2]]

def raw6758 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]

def raw6759 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![0, -2, 2], ![2, 0, -2]]

def raw6759step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -3, 2], ![0, 2, -2], ![-2, 0, 2]]

def raw6759step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

def raw6760 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]

def raw6760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw6761 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]

def raw6761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw6762 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![1, -3, 2], ![1, 1, -2]]

def raw6762step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 2, -3]]

def raw6763 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![1, -2, 1], ![1, 0, -1]]

def raw6763step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

def raw6764 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0]]

def raw6764step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw6765 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 4, -3], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1]]

def raw6766 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 4, -3], ![0, -3, 3], ![2, 0, -2]]

def raw6766step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -4, 3], ![0, 3, -3], ![-2, 0, 2]]

def raw6766step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -4, 3], ![1, 1, -2]]

def raw6767 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 4, -3], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1]]

def raw6767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw6768 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 4, -3], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]

def raw6768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw6769 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 4, -3], ![0, -2, 2], ![2, -1, -1]]

def raw6769step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -4, 3], ![0, 2, -2], ![-2, 1, 1]]

def raw6769step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -2, 1], ![1, 3, -4]]

def raw6770 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 4, -3], ![1, -3, 2], ![1, 0, -1]]

def raw6770step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 2, -3]]

def raw6771 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 4, -3], ![1, -2, 1], ![1, -1, 0]]

def raw6771step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2]]

def raw6772 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -3, 3], ![0, 4, -4], ![1, 0, -1]]

def raw6773 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -3, 3], ![1, 4, -5]]

def raw6773step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 1, -2], ![0, 3, -3], ![-1, -4, 5]]

def raw6773step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 3, -3], ![1, 1, -2]]

def raw6774 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2]]

def raw6774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]

def raw6774step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def raw6775 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1]]

def raw6775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]

def raw6777 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 4, -4], ![1, 0, -1]]

def raw6778 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

def raw6779 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 2, -3]]

def raw6779step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, -2, 3]]

def raw6779step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2]]

def raw6780 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2]]

def raw6780step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

def raw6781 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1]]

def raw6781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

def raw6782 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![0, 1, -1]]

def raw6782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

def raw6783 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical212
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6784 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1]]

def raw6784step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

def raw6786 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

def raw6787 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![0, 0, 0]]

def raw6787step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

def raw6788 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 4, -4], ![1, -1, 0]]

def raw6789 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![1, 3, -4]]

def raw6789step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-1, -3, 4]]

def raw6789step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![1, 1, -2]]

def raw6791 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw6791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw6793 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

def raw6793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2]]

def raw6793step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw6794 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1]]

def raw6794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw6795 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![-1, 4, -3], ![1, -1, 0], ![1, -1, 0]]

def raw6795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw6796 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, -2, 2], ![0, 4, -4], ![1, 0, -1]]

def raw6796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 4, -4], ![1, 0, -1]]

def raw6797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![2, 1, -3]]

def raw6797step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![-2, -1, 3]]

def raw6797step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2]]

def raw6798 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1]]

def raw6799 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0]]

def raw6800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![-2, 3, -1], ![2, 1, -3]]

def raw6800step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![2, -3, 1], ![-2, -1, 3]]

def raw6800step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

def raw6801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-1, 4, -3]]

def raw6801step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw6802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-1, 3, -2]]

def raw6802step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

def raw6803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![-2, 4, -2]]

def raw6803step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

def raw6805 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1]]

def raw6805step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

def raw6806 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2]]

def raw6806step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

def raw6807 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw6808 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def raw6809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![2, 2, -4]]

def raw6809step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![2, 0, -2], ![-2, -2, 4]]

def raw6809step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw6811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-1, 2, -1]]

def raw6811step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw6812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-1, -1, 2], ![1, 2, -3]]

def raw6812step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![-1, -2, 3]]

def raw6812step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

def raw6813 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1]]

def raw6813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw6814 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

def raw6815 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2]]

def raw6815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, -2, 2], ![0, 1, -1], ![-1, -1, 2]]

def raw6815step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical213
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6816 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1]]

def raw6816step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

def raw6817 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![0, 1, -1]]

def raw6817step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def raw6818 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

def raw6819 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1]]

def raw6819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1]]

def raw6820 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

def raw6821 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![0, 0, 0]]

def raw6821step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

def raw6822 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 4, -4], ![0, -1, 1], ![1, -1, 0]]

def raw6822step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0]]

def raw6823 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 4, -4], ![1, -2, 1]]

def raw6824 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0], ![0, -1, 1]]

def raw6824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0]]

def raw6825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![1, 3, -4]]

def raw6825step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]

def raw6826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-1, -1, 2], ![0, 4, -4]]

def raw6826step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0], ![1, 0, -1]]

def raw6828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![0, 3, -3]]

def raw6828step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def raw6829 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw6829step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw6830 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1]]

def raw6830step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![1, 0, -1]]

def raw6831 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0]]

def raw6831step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -1, 0]]

def raw6832 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![1, 1, -2]]

def raw6832step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![2, 0, -2]]

def raw6832step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw6832step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw6833 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2]]

def raw6833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw6834 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw6834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1]]

def raw6834step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw6835 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1]]

def raw6835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, -1, 1], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1]]

def raw6835step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw6836 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0]]

def raw6836step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, -1, 1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0]]

def raw6836step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]

def raw6837 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2]]

def raw6837step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

def raw6838 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0]]

def raw6838step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw6839 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1]]

def raw6839step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![1, 0, -1]]

def raw6840 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![1, 1, -2]]

def raw6840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]

def raw6841 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1]]

def raw6841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw6842 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0]]

def raw6842step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw6843 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1]]

def raw6844 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![0, 1, -1]]

def raw6844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1]]

def raw6845 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw6846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-2, -1, 3], ![2, 1, -3]]

def raw6846step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

def raw6847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-1, -2, 3], ![1, 2, -3]]

def raw6847step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical214
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6848 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0]]

def raw6848step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw6849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2]]

def raw6849step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw6850 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![0, -2, 2], ![1, 0, -1]]

def raw6850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

def raw6851 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0]]

def raw6851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def raw6852 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1]]

def raw6853 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![0, 0, 0]]

def raw6853step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1]]

def raw6854 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![0, -1, 1]]

def raw6854step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def raw6855 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![0, 2, -2]]

def raw6855step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1]]

def raw6856 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1]]

def raw6856step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw6857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-1, -2, 3], ![0, 3, -3]]

def raw6857step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw6858 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![1, 0, -1]]

def raw6859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, 3, -1], ![1, -3, 2]]

def raw6859step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

def raw6860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, 3, -2], ![0, -3, 3]]

def raw6860step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![0, -3, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw6861 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![0, -2, 2], ![1, 1, -2]]

def raw6861step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

def raw6862 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1]]

def raw6862step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

def raw6863 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1]]

def raw6863step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1]]

def raw6864 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -2, 1], ![0, 1, -1]]

def raw6864step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1]]

def raw6865 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -1, 0]]

def raw6866 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![0, -3, 3], ![1, 1, -2]]

def raw6866step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -3, 3], ![0, 3, -3], ![1, 1, -2]]

def raw6867 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![0, -2, 2], ![1, 0, -1]]

def raw6867step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

def raw6868 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0]]

def raw6868step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

def raw6869 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -3, 2], ![0, 1, -1]]

def raw6869step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, -3, 3], ![-1, 3, -2], ![0, -1, 1]]

def raw6869step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 3, -3], ![1, -2, 1]]

def raw6870 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -2, 1]]

def raw6871 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -2, 1], ![0, 0, 0]]

def raw6871step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -2, 1]]

def raw6872 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![0, -1, 1]]

def raw6872step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

def raw6873 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 4, -4], ![0, -3, 3], ![1, 0, -1]]

def raw6873step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -3, 3], ![0, 4, -4], ![1, 0, -1]]

def raw6874 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 4, -4], ![0, -2, 2], ![1, -1, 0]]

def raw6874step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 4, -4], ![1, -1, 0]]

def raw6875 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 4, -4], ![1, -3, 2]]

def raw6875step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 1, -2], ![0, -4, 4], ![-1, 3, -2]]

def raw6875step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 4, -4], ![1, -2, 1]]

def raw6876 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 4, -4], ![1, -2, 1], ![0, -1, 1]]

def raw6876step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 4, -4], ![1, -2, 1]]

def raw6877 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -3, 2], ![0, 4, -4]]

def raw6877step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 3, -2], ![0, -4, 4]]

def raw6877step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 4, -4], ![1, -2, 1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical215
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6880 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -2, 1], ![0, 3, -3]]

def raw6880step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -2, 1]]

def raw6885 : Matrix (Fin 2) (Fin 3) ℤ := ![![-1, -1, 2], ![1, 1, -2]]

def raw6885step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw6885step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw6887 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-4, 2, 0, 2], ![5, -1, -2, -2]]

def raw6887step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -4, 5], ![-1, 2, -1], ![2, 0, -2], ![0, 2, -2]]

def raw6887step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![1, -2, 1], ![-2, 0, 2], ![0, -2, 2]]

def raw6887step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -2, 1], ![1, 4, -5]]

def raw6888 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-3, 2, -2, 3], ![4, -1, 0, -3]]

def raw6888step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![2, -2, 0], ![0, 3, -3]]

def raw6888step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -2, 1], ![-2, 2, 0], ![0, -3, 3]]

def raw6888step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -4, 3], ![1, 1, -2]]

def raw6889 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-3, 2, -1, 2], ![4, -1, -1, -2]]

def raw6889step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![2, -1, -1], ![0, 2, -2]]

def raw6889step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -2, 1], ![-2, 1, 1], ![0, -2, 2]]

def raw6889step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -2, 1], ![1, 3, -4]]

def raw6890 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-3, 2, 0, 1], ![4, -1, -2, -1]]

def raw6890step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![2, 0, -2], ![0, 1, -1]]

def raw6890step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -2, 1], ![-2, 0, 2], ![0, -1, 1]]

def raw6890step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -2, 1], ![1, 3, -4]]

def raw6891 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-3, 3, -2, 2], ![4, -2, 0, -2]]

def raw6891step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![2, -2, 0], ![0, 2, -2]]

def raw6891step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -3, 2], ![-2, 2, 0], ![0, -2, 2]]

def raw6891step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -4, 3], ![1, 2, -3]]

def raw6892 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-2, -1, -1, 4], ![3, 2, -1, -4]]

def raw6892step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![2, -1, -1], ![0, 4, -4]]

def raw6892step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![-2, 1, 1], ![0, -4, 4]]

def raw6892step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -4, 4], ![1, 1, -2], ![1, 2, -3]]

def raw6893 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-2, -1, 0, 3], ![3, 2, -2, -3]]

def raw6893step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![2, 0, -2], ![0, 3, -3]]

def raw6893step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![-2, 0, 2], ![0, -3, 3]]

def raw6893step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 1, -2], ![1, 2, -3]]

def raw6894 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-2, 2, -2, 2], ![3, -1, 0, -2]]

def raw6894step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![2, -2, 0], ![0, 2, -2]]

def raw6894step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -2, 1], ![-2, 2, 0], ![0, -2, 2]]

def raw6894step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

def raw6895 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-2, 2, -1, 1], ![3, -1, -1, -1]]

def raw6895step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![2, -1, -1], ![0, 1, -1]]

def raw6895step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -2, 1], ![-2, 1, 1], ![0, -1, 1]]

def raw6895step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

def raw6896 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-2, 2, 1, -1], ![3, -1, -3, 1]]

def raw6896step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![2, 1, -3], ![0, -1, 1]]

def raw6896step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -2, 1], ![-2, -1, 3], ![0, 1, -1]]

def raw6896step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

def raw6897 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-2, 3, -2, 1], ![3, -2, 0, -1]]

def raw6897step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![2, -2, 0], ![0, 1, -1]]

def raw6897step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -3, 2], ![-2, 2, 0], ![0, -1, 1]]

def raw6897step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -3, 2], ![1, 2, -3]]

def raw6898 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-2, 3, 0, -1], ![3, -2, -2, 1]]

def raw6898step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![2, 0, -2], ![0, -1, 1]]

def raw6898step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -3, 2], ![-2, 0, 2], ![0, 1, -1]]

def raw6898step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -3, 2], ![1, 2, -3]]

def raw6899 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-2, 4, -1, -1], ![3, -3, -1, 1]]

def raw6899step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 4, -3], ![2, -1, -1], ![0, -1, 1]]

def raw6899step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -4, 3], ![-2, 1, 1], ![0, 1, -1]]

def raw6899step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -3, 2], ![1, 3, -4]]

def raw6900 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-1, -2, 1, 2], ![2, 3, -3, -2]]

def raw6900step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![2, 1, -3], ![0, 2, -2]]

def raw6900step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 2, -3], ![-2, -1, 3], ![0, -2, 2]]

def raw6900step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 1, -2], ![1, 2, -3]]

def raw6901 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-1, -2, 2, 1], ![2, 3, -4, -1]]

def raw6901step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![2, 2, -4], ![0, 1, -1]]

def raw6901step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 2, -3], ![-2, -2, 4], ![0, -1, 1]]

def raw6901step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![1, 1, -2], ![1, 2, -3]]

def raw6902 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-1, -1, -2, 4], ![2, 2, 0, -4]]

def raw6902step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![2, -2, 0], ![0, 4, -4]]

def raw6902step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-2, 2, 0], ![0, -4, 4]]

def raw6902step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![1, -2, 1], ![1, -2, 1]]

def raw6903 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-1, -1, -1, 3], ![2, 2, -1, -3]]

def raw6903step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![2, -1, -1], ![0, 3, -3]]

def raw6903step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-2, 1, 1], ![0, -3, 3]]

def raw6903step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]

def raw6904 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-1, -1, 3, -1], ![2, 2, -5, 1]]

def raw6904step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![2, 3, -5], ![0, -1, 1]]

def raw6904step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-2, -3, 5], ![0, 1, -1]]

def raw6904step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

def raw6905 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-1, 2, -3, 2], ![2, -1, 1, -2]]

def raw6905step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![2, -3, 1], ![0, 2, -2]]

def raw6905step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -2, 1], ![-2, 3, -1], ![0, -2, 2]]

def raw6905step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def raw6906 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-1, 2, -2, 1], ![2, -1, 0, -1]]

def raw6906step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![2, -2, 0], ![0, 1, -1]]

def raw6906step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -2, 1], ![-2, 2, 0], ![0, -1, 1]]

def raw6906step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw6907 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-1, 2, 0, -1], ![2, -1, -2, 1]]

def raw6907step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![2, 0, -2], ![0, -1, 1]]

def raw6907step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -2, 1], ![-2, 0, 2], ![0, 1, -1]]

def raw6907step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw6908 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-1, 2, 1, -2], ![2, -1, -3, 2]]

def raw6908step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![2, 1, -3], ![0, -2, 2]]

def raw6908step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -2, 1], ![-2, -1, 3], ![0, 2, -2]]

def raw6908step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def raw6909 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-1, 3, -4, 2], ![2, -2, 2, -2]]

def raw6909step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![2, -4, 2], ![0, 2, -2]]

def raw6909step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -3, 2], ![-2, 4, -2], ![0, -2, 2]]

def raw6909step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -2, 1], ![1, 2, -3]]

def raw6910 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-1, 3, -1, -1], ![2, -2, -1, 1]]

def raw6910step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![2, -1, -1], ![0, -1, 1]]

def raw6910step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -3, 2], ![-2, 1, 1], ![0, 1, -1]]

def raw6910step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

def raw6911 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-1, 3, 0, -2], ![2, -2, -2, 2]]

def raw6911step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![2, 0, -2], ![0, -2, 2]]

def raw6911step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -3, 2], ![-2, 0, 2], ![0, 2, -2]]

def raw6911step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical216
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6912 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-1, 4, -1, -2], ![2, -3, -1, 2]]

def raw6912step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 4, -3], ![2, -1, -1], ![0, -2, 2]]

def raw6912step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -4, 3], ![-2, 1, 1], ![0, 2, -2]]

def raw6912step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -2, 1], ![1, 3, -4]]

def raw6913 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -3, 1, 2], ![1, 4, -3, -2]]

def raw6913step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![2, 1, -3], ![0, 2, -2]]

def raw6913step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 3, -4], ![-2, -1, 3], ![0, -2, 2]]

def raw6913step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 3, -4]]

def raw6914 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -2, -1, 3], ![1, 3, -1, -3]]

def raw6914step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![2, -1, -1], ![0, 3, -3]]

def raw6914step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 2, -3], ![-2, 1, 1], ![0, -3, 3]]

def raw6914step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 0, -1], ![1, 2, -3]]

def raw6915 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -2, 1, 1], ![1, 3, -3, -1]]

def raw6915step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![2, 1, -3], ![0, 1, -1]]

def raw6915step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]

def raw6916 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -3, 4], ![0, 1, 1, -2], ![1, 1, 0, -2]]

def raw6916step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -2, 0], ![0, 1, 3, -4], ![0, -1, -1, 2], ![-1, -1, 0, 2]]

def raw6916step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, 1, -2, 0]]

def raw6917 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -3, 4], ![1, 2, 1, -4]]

def raw6917step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![2, -3, 1], ![0, 4, -4]]

def raw6917step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 1, -2], ![-2, 3, -1], ![0, -4, 4]]

def raw6917step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 4, -4], ![1, -2, 1], ![1, -1, 0]]

def raw6918 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -2, 3], ![0, 1, 0, -1], ![1, 1, 0, -2]]

def raw6918step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 1, 1], ![2, -2, 0, 0], ![0, 3, -1, -2]]

def raw6918step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, -1, -1]]

def raw6919 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -2, 3], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw6919step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![2, -2, 0, 0], ![0, 3, -2, -1]]

def raw6919step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw6920 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -2, 3], ![1, 2, 0, -3]]

def raw6920step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![2, -2, 0], ![0, 3, -3]]

def raw6920step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 1, -2], ![-2, 2, 0], ![0, -3, 3]]

def raw6920step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

def raw6921 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -1, 2], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw6921step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw6922 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, 0, 1], ![0, 2, 1, -3], ![1, 0, -3, 2]]

def raw6922step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, -3, 1], ![1, 0, 2, -3]]

def raw6923 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, 2, -1], ![1, 2, -4, 1]]

def raw6923step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![2, 2, -4], ![0, -1, 1]]

def raw6923step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 1, -2], ![-2, -2, 4], ![0, 1, -1]]

def raw6923step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw6924 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, 3, -2], ![1, 2, -5, 2]]

def raw6924step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![2, 3, -5], ![0, -2, 2]]

def raw6924step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 1, -2], ![-2, -3, 5], ![0, 2, -2]]

def raw6924step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def raw6925 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 0, -3, 3], ![0, 2, 1, -3], ![1, -1, 0, 0]]

def raw6925step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 2, -3, 1], ![1, -1, 0, 0]]

def raw6926 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw6926step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def raw6927 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw6927step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw6928 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 0, -2, 2], ![1, 1, 0, -2]]

def raw6928step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![2, -2, 0], ![0, 2, -2]]

def raw6928step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

def raw6929 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw6929step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![2, -1, 0, -1], ![0, 1, -2, 1]]

def raw6929step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 0, -2, 1], ![-2, 1, 0, 1], ![0, -1, 2, -1]]

def raw6929step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw6930 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, -2, 2]]

def raw6930step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, -1, 2, -2]]

def raw6931 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -3, 3]]

def raw6931step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![2, 1, 0, -3], ![0, -1, -2, 3]]

def raw6931step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 2, -3]]

def raw6932 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 1, -3, 2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw6932step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw6933 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw6933step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![2, 0, 0, -2], ![0, -1, -1, 2]]

def raw6933step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, -1, -1]]

def raw6934 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 2, -3, 1], ![1, -1, 1, -1]]

def raw6934step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![2, -3, 1], ![0, 1, -1]]

def raw6934step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -2, 1], ![-2, 3, -1], ![0, -1, 1]]

def raw6934step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw6935 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw6935step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![0, -2, 2]]

def raw6935step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

def raw6936 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 2, 1, -3], ![1, -1, -3, 3]]

def raw6936step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![2, 1, -3], ![0, -3, 3]]

def raw6936step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -2, 1], ![-2, -1, 3], ![0, 3, -3]]

def raw6936step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw6937 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 3, -4, 1], ![1, -2, 2, -1]]

def raw6937step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 3, -2], ![2, -4, 2], ![0, 1, -1]]

def raw6937step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -3, 2], ![-2, 4, -2], ![0, -1, 1]]

def raw6937step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw6938 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 3, -1, -2], ![1, -2, -1, 2]]

def raw6938step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 3, -2], ![2, -1, -1], ![0, -2, 2]]

def raw6938step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -3, 2], ![-2, 1, 1], ![0, 2, -2]]

def raw6938step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

def raw6939 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 3, 0, -3], ![1, -2, -2, 3]]

def raw6939step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 3, -2], ![2, 0, -2], ![0, -3, 3]]

def raw6939step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -3, 2], ![-2, 0, 2], ![0, 3, -3]]

def raw6939step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

def raw6940 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 4, -1, -3], ![1, -3, -1, 3]]

def raw6940step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 4, -3], ![2, -1, -1], ![0, -3, 3]]

def raw6940step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -4, 3], ![-2, 1, 1], ![0, 3, -3]]

def raw6940step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, -1, 0], ![1, 3, -4]]

def raw6941 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![1, -3, 0, 2], ![0, 4, -2, -2]]

def raw6941step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![2, 0, -2], ![0, 2, -2]]

def raw6941step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![1, 3, -4], ![-2, 0, 2], ![0, -2, 2]]

def raw6941step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

def raw6942 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![1, -3, 1, 1], ![0, 4, -3, -1]]

def raw6942step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![2, 1, -3], ![0, 1, -1]]

def raw6942step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![1, 3, -4], ![-2, -1, 3], ![0, -1, 1]]

def raw6942step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def raw6943 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![1, -2, -1, 2], ![0, 3, -1, -2]]

def raw6943step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![2, -1, -1], ![0, 2, -2]]

def raw6943step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![1, 2, -3], ![-2, 1, 1], ![0, -2, 2]]

def raw6943step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical217
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6944 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![1, -1, -3, 3], ![0, 2, 1, -3]]

def raw6944step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![2, -3, 1], ![0, 3, -3]]

def raw6944step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![1, 1, -2], ![-2, 3, -1], ![0, -3, 3]]

def raw6944step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw6945 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![1, -1, -2, 2], ![0, 2, 0, -2]]

def raw6945step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![2, -2, 0], ![0, 2, -2]]

def raw6945step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

def raw6946 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![1, -1, 2, -2], ![0, 2, -4, 2]]

def raw6946step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![2, 2, -4], ![0, -2, 2]]

def raw6946step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![1, 1, -2], ![-2, -2, 4], ![0, 2, -2]]

def raw6946step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def raw6947 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![2, -3, 0, 1], ![-1, 4, -2, -1]]

def raw6947step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -3, 4], ![2, 0, -2], ![0, 1, -1]]

def raw6947step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![1, 3, -4], ![-2, 0, 2], ![0, -1, 1]]

def raw6947step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -2, 1], ![1, 3, -4]]

def raw6948 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![2, -2, 1, -1], ![-1, 3, -3, 1]]

def raw6948step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![2, 1, -3], ![0, -1, 1]]

def raw6948step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![1, 2, -3], ![-2, -1, 3], ![0, 1, -1]]

def raw6948step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

def raw6949 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![2, -1, 0, -1], ![-1, 2, -2, 1]]

def raw6949step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![2, 0, -2], ![0, -1, 1]]

def raw6949step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![1, 1, -2], ![-2, 0, 2], ![0, 1, -1]]

def raw6949step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw6950 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![2, -1, 1, -2], ![-1, 2, -3, 2]]

def raw6950step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![2, 1, -3], ![0, -2, 2]]

def raw6950step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![1, 1, -2], ![-2, -1, 3], ![0, 2, -2]]

def raw6950step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def raw6951 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![3, -2, 0, -1], ![-2, 3, -2, 1]]

def raw6951step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -2, 3], ![2, 0, -2], ![0, -1, 1]]

def raw6951step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 2, -3], ![-2, 0, 2], ![0, 1, -1]]

def raw6951step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -3, 2], ![1, 2, -3]]

def raw6952 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![3, -1, 0, -2], ![-2, 2, -2, 2]]

def raw6952step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![2, 0, -2], ![0, -2, 2]]

def raw6952step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 1, -2], ![-2, 0, 2], ![0, 2, -2]]

def raw6952step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

def raw6953 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![-1, 0, -3, 4], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw6953step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, -3, 1], ![1, 0, 3, -4], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, -1, 0, 2]]

def raw6953step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 0, 0, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 1, -3, 1]]

def raw6954 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![-1, 0, -3, 4], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw6954step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![0, -1, -3, 4], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw6955 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![-1, 0, -3, 4], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw6955step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, -3, 1], ![1, 0, 3, -4], ![0, -2, 0, 2], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw6955step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 1, -3, 1]]

def raw6956 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![-1, 0, -2, 3], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def raw6956step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, -3, 1], ![1, 0, 2, -3], ![0, -1, 0, 1], ![-1, 1, 1, -1], ![-1, -1, 0, 2]]

def raw6956step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 0, 0, 1], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 1, -3, 1]]

def raw6957 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![-1, 0, -2, 3], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw6957step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw6958 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![-1, 0, -2, 3], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw6958step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, -3, 1], ![1, 0, 2, -3], ![0, -2, 0, 2], ![-1, 1, 1, -1], ![-1, 0, 0, 1]]

def raw6958step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 1, -3, 1]]

def raw6959 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![-1, 1, -3, 3], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw6959step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 0, 0], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw6960 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![-1, 1, -2, 2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw6960step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 1, -1], ![0, 1, -1, 0], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw6961 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![-1, 3, -2, 0], ![2, -2, -1, 1]]

def raw6961step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![3, -2, -1], ![-1, 0, 1]]

def raw6961step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -3, 2], ![-3, 2, 1], ![1, 0, -1]]

def raw6961step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

def raw6962 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![0, -1, -3, 4], ![0, 1, 0, -1], ![1, 1, 0, -2]]

def raw6962step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 1, 1], ![3, -3, 0, 0], ![-1, 4, -1, -2]]

def raw6962step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, 1, -1, -1]]

def raw6963 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw6963step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![3, -3, 0, 0], ![-1, 4, -2, -1]]

def raw6963step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 3, -3], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw6964 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![0, 0, -3, 3], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw6964step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def raw6965 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def raw6965step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw6966 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw6966step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def raw6967 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![0, 2, -1, -1], ![1, -1, -2, 2]]

def raw6967step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![3, -1, -2], ![-1, -1, 2]]

def raw6967step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -2, 1], ![-3, 1, 2], ![1, 1, -2]]

def raw6967step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

def raw6968 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![0, 2, 0, -2], ![1, -1, -3, 3]]

def raw6968step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![3, 0, -3], ![-1, -2, 3]]

def raw6968step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![2, -1, -1]]

def raw6969 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![0, 3, -2, -1], ![1, -2, -1, 2]]

def raw6969step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 3, -2], ![3, -2, -1], ![-1, -1, 2]]

def raw6969step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -3, 2], ![-3, 2, 1], ![1, 1, -2]]

def raw6969step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

def raw6970 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![1, -2, 1, 0], ![0, 3, -4, 1]]

def raw6970step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![3, 1, -4], ![-1, 0, 1]]

def raw6970step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def raw6971 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![2, -2, 1, -1], ![-1, 3, -4, 2]]

def raw6971step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![3, 1, -4], ![-1, -1, 2]]

def raw6971step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![1, 2, -3], ![-3, -1, 4], ![1, 1, -2]]

def raw6971step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]

def raw6972 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, -1, 2, 0], ![1, 0, 1, -2], ![1, 1, 0, -2]]

def raw6972step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 3, -4], ![1, 1, -2, 0], ![-1, 0, -1, 2], ![-1, -1, 0, 2]]

def raw6972step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, 1, -2, 0]]

def raw6973 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 0, 3, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw6973step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 3, -4], ![1, 0, -3, 2], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw6973step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 1, -3, 2], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw6974 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 1, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw6975 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 1, 1, -1], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, -1, 0, 0]]

def raw6975step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 1, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical218
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6976 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 1, 1, -1], ![0, 1, 1, -2], ![2, -2, 1, -1]]

def raw6976step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 1, -2], ![-3, 1, 1, 1], ![4, -1, -2, -1]]

def raw6976step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 1, -2, 0], ![1, 1, 1, -3]]

def raw6977 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 1, 1, -1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw6978 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 1, 1, -1], ![0, 1, 2, -3], ![2, -2, 0, 0]]

def raw6978step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 1, -2], ![-3, 1, 2, 0], ![4, -1, -3, 0]]

def raw6978step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 0, -2], ![0, -1, -1, 2], ![3, -1, -2, 0], ![-4, 1, 3, 0]]

def raw6978step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -2, 3], ![0, 1, 3, -4], ![2, -1, -1, 0]]

def raw6979 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 1, 1, -1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw6979step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 3, -4], ![1, -1, -1, 1], ![-1, 1, -1, 1], ![-1, 0, -1, 2]]

def raw6979step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def raw6980 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 1, 1, -1], ![1, 0, 1, -2], ![1, -1, 1, -1]]

def raw6980step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 3, -4], ![1, -1, -1, 1], ![-1, 0, -1, 2], ![-1, 1, -1, 1]]

def raw6980step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def raw6981 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 1, 1, -1], ![1, 0, 2, -3], ![1, -1, 0, 0]]

def raw6981step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 3, -4], ![1, -1, -1, 1], ![-1, 0, -2, 3], ![-1, 1, 0, 0]]

def raw6981step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, -2, 3], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw6982 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 1, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw6983 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 1, 2, -2], ![0, 1, 1, -2], ![2, -2, 0, 0]]

def raw6983step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 1, -2], ![-3, 2, 1, 0], ![4, -2, -2, 0]]

def raw6983step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -2, 1, 0], ![1, 0, 2, -3]]

def raw6984 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 1, 2, -2], ![1, 0, 1, -2], ![1, -1, 0, 0]]

def raw6984step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, 0, -1], ![-3, 2, 1, 0], ![4, -2, -2, 0]]

def raw6984step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![0, -1, 0, 1], ![3, -2, -1, 0], ![-4, 2, 2, 0]]

def raw6984step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw6985 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -2, 2, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw6986 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -2, 2, 0], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw6987 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -2, 2, 0], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw6988 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -2, 2, 0], ![1, 2, 1, -4]]

def raw6988step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![-3, 2, 1], ![4, 0, -4]]

def raw6988step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 2, -2], ![3, -2, -1], ![-4, 0, 4]]

def raw6988step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 4, -4], ![2, -2, 0]]

def raw6989 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -2, 3, -1], ![0, 1, 0, -1], ![1, 1, 0, -2]]

def raw6989step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![-3, 3, 0, 0], ![4, -1, -1, -2]]

def raw6989step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def raw6990 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -2, 3, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw6990step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![-3, 3, 0, 0], ![4, -1, -2, -1]]

def raw6990step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw6991 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw6992 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw6993 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw6994 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw6995 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 2, 0, -2], ![1, -1, 2, -2]]

def raw6996 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw6997 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw6998 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw6999 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw7000 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, -1, 0, 0]]

def raw7000step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![-3, 2, 1, 0], ![4, -1, -3, 0]]

def raw7000step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -3, 4], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw7001 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![1, 1, 1, -3]]

def raw7001step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-3, 2, 1], ![4, -1, -3]]

def raw7001step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 1, -1], ![3, -2, -1], ![-4, 1, 3]]

def raw7001step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def raw7002 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw7002step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![-3, 3, 0, 0], ![4, -2, -1, -1]]

def raw7002step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw7003 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 3, -2], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw7004 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 3, -2], ![1, 1, 0, -2]]

def raw7004step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-3, 3, 0], ![4, -2, -2]]

def raw7004step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw7005 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw7005step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw7006 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw7007 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -2, 1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical219
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7008 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, 0, 0, -1]]

def raw7008step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

def raw7009 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, 2, -1]]

def raw7010 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -2, 1, 0]]

def raw7011 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw7011step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -2, 1, 0]]

def raw7012 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw7013 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw7013step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![-3, 1, 2, 0], ![4, -1, -3, 0]]

def raw7013step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def raw7014 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -2, 2, -1]]

def raw7014step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![-3, 1, 0, 2], ![4, -1, -2, -1]]

def raw7014step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 2, -3]]

def raw7015 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -2, 1, 0]]

def raw7015step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![-3, 1, 1, 1], ![4, -1, -3, 0]]

def raw7015step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, -2, 2], ![3, -1, -1, -1], ![-4, 1, 3, 0]]

def raw7015step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 0, 1], ![0, 2, -2, 0], ![1, 0, 3, -4]]

def raw7016 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![1, 0, 2, -3]]

def raw7016step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![1, 2, -3]]

def raw7017 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw7018 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 1, -1]]

def raw7019 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw7020 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -2, 1, 0]]

def raw7021 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![1, 0, 1, -2]]

def raw7021step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![1, 1, -2]]

def raw7022 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 3, -3], ![1, 0, 0, -1]]

def raw7022step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 3, -3], ![1, 0, -1]]

def raw7023 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, 3, -2]]

def raw7023step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![-3, 0, 0, 3], ![4, -1, -1, -2]]

def raw7023step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 3, -3], ![1, 1, -2, 0]]

def raw7024 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -2, 2, -1]]

def raw7024step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![-3, 0, 1, 2], ![4, -1, -2, -1]]

def raw7024step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, 2, -3], ![1, 1, -2, 0]]

def raw7025 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw7026 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 0, -1], ![1, -1, 3, -3]]

def raw7026step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-3, 0, 3], ![4, -1, -3]]

def raw7026step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0]]

def raw7027 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 1, -2], ![-1, 1, 2, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw7027step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 1, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw7028 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 1, -2], ![0, 0, 2, -2], ![1, -1, 0, 0]]

def raw7028step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw7029 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 1, -2], ![0, 1, 0, -1], ![1, -2, 2, -1]]

def raw7029step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![-3, 1, 0, 2], ![4, -2, -1, -1]]

def raw7029step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, 2, -3], ![1, 1, -2, 0]]

def raw7030 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![0, -1, 1, 0], ![1, -1, 0, 0]]

def raw7030step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw7031 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -2, 1, 0]]

def raw7032 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -1, 0, 0], ![0, -1, 1, 0]]

def raw7032step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw7033 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 1, -2], ![1, -1, 2, -2]]

def raw7033step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-3, 1, 2], ![4, -2, -2]]

def raw7033step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw7034 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 2, -3], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw7034step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw7035 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 2, -3], ![1, -1, 1, -1]]

def raw7035step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-3, 2, 1], ![4, -3, -1]]

def raw7035step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3]]

def raw7036 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw7036step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-3, 3, 0], ![4, -4, 0]]

def raw7036step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 4, -4], ![1, -1, 0]]

def raw7037 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 2, 0, -2], ![1, -2, 3, -2]]

def raw7037step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![-3, 0, 3], ![4, -2, -2]]

def raw7037step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 3, -3], ![2, -2, 0]]

def raw7038 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 2, 2, -4], ![1, -2, 1, 0]]

def raw7038step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![-3, 2, 1], ![4, -4, 0]]

def raw7038step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![1, -3, 2], ![1, -1, 0]]

def raw7039 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![1, -2, 2, -1], ![0, 2, 1, -3]]

def raw7039step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -2, 2], ![-3, 2, 1], ![4, -1, -3]]

def raw7039step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw704 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]

def raw705 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]

def raw706 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

def raw707 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]

def raw708 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]

def raw709 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0], ![1, 2, -3]]

def raw709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

def raw710 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]

def raw710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2]]

def raw711 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]

def raw711step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -3, 2], ![1, 2, -3]]

def raw712 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]

def raw712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2]]

def raw713 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]

def raw713step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

def raw714 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]

def raw715 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 3, -4], ![2, -2, 0]]

def raw716 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![2, -2, 0], ![1, 3, -4]]

def raw716step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 3, -4], ![2, -2, 0]]

def raw717 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![2, -1, -1], ![1, 2, -3]]

def raw717step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]

def raw718 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![2, 0, -2], ![1, 1, -2]]

def raw718step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

def raw719 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![3, 1, -4]]

def raw719step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![2, 2, -4]]

def raw719step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 2, -1], ![-2, -2, 4]]

def raw719step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, -1, -1]]

def raw720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]

def raw720step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1]]

def raw721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]

def raw721step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]

def raw721step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

def raw722 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]

def raw722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]

def raw722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]

def raw723 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]

def raw723step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]

def raw723step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3]]

def raw724 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]

def raw724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![-2, -1, 3]]

def raw724step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-2, -1, 3]]

def raw724step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1]]

def raw725 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]

def raw725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![-2, 1, 1]]

def raw725step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]

def raw725step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

def raw726 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2]]

def raw726step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]

def raw726step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3]]

def raw727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]

def raw728 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]

def raw729 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]

def raw731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def raw731step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]

def raw731step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw732 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

def raw732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]

def raw732step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw733 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def raw733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]

def raw733step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw734 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]

def raw735 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]

def raw735step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical220
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7040 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![1, -2, 3, -2], ![0, 2, 0, -2]]

def raw7040step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -2, 2], ![-3, 3, 0], ![4, -2, -2]]

def raw7040step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 3, -3], ![2, -2, 0]]

def raw7041 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![1, -1, 2, -2], ![0, 1, 1, -2]]

def raw7041step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![-3, 2, 1], ![4, -2, -2]]

def raw7041step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw7042 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, -1, 2, 0], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw7042step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, 1, -1, -1]]

def raw7043 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, 0, 2, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw7043step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 2, -3], ![1, 0, -2, 1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, -1, 2]]

def raw7043step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![0, 1, -3, 2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw7044 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, 0, 2, -1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw7044step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 2, -3], ![1, 0, -2, 1], ![0, -1, 1, 0], ![-1, 1, -1, 1], ![-1, 0, 0, 1]]

def raw7044step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 1, -3, 2], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw7045 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, 0, 2, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw7045step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 2, -3], ![1, 0, -2, 1], ![0, -1, 0, 1], ![-1, 1, -1, 1], ![-1, 0, 1, 0]]

def raw7045step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, -1, 1]]

def raw7046 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, 0, 2, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw7046step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 2, -3], ![1, 0, -2, 1], ![0, -1, -1, 2], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw7046step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw7047 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, 0, 2, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw7047step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 2, -3], ![1, 0, -2, 1], ![-1, 1, -1, 1], ![-1, -1, 1, 1]]

def raw7047step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -3, 2], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw7048 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, 0, 3, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw7048step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 2, -3], ![1, 0, -3, 2], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw7048step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 1, -3, 2], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw7049 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, 0, 3, -2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw7049step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 2, -3], ![1, 0, -3, 2], ![0, -1, 0, 1], ![-1, 1, 1, -1], ![-1, 0, 0, 1]]

def raw7049step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 1, -3, 2], ![0, 1, 2, -3], ![1, -1, 1, -1]]

def raw7050 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, 0, 3, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw7050step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 2, -3], ![1, 0, -3, 2], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw7050step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 1, -3, 2], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw7051 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, 0, 3, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw7051step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 2, -3], ![1, 0, -3, 2], ![-1, 1, 0, 0], ![-1, -1, 1, 1]]

def raw7051step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -3, 2], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw7052 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, 1, -1, 1], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw7052step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, -1, -2, 3], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def raw7053 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, 1, -1, 1], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def raw7053step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 2, -3], ![1, -1, 1, -1], ![-1, 1, -3, 3], ![-1, 0, 0, 1]]

def raw7053step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, 0, 1], ![0, 1, 2, -3], ![1, -1, -3, 3]]

def raw7054 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, 1, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw7054step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw7055 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, 1, 1, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw7055step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, -1, 1]]

def raw7056 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, 1, 3, -3], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw7057 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, 1, 3, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw7057step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -1, 0], ![-2, 3, 0, -1], ![3, -3, 0, 0]]

def raw7057step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![0, -1, 1, 0], ![2, -3, 0, 1], ![-3, 3, 0, 0]]

def raw7057step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -3, 3], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def raw7058 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, 1, 3, -3], ![1, 0, -1, 0], ![1, -1, 0, 0]]

def raw7058step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, 0, -1], ![-2, 3, -1, 0], ![3, -3, 0, 0]]

def raw7058step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![0, -1, 0, 1], ![2, -3, 1, 0], ![-3, 3, 0, 0]]

def raw7058step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -3, 3], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def raw7059 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, 2, 2, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw7059step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 2, -1, -1], ![-2, 2, 0, 0], ![3, -3, 0, 0]]

def raw7059step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, 1, -1, -1]]

def raw7060 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw7061 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 1, 1], ![1, 2, 1, -4]]

def raw7061step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![-2, 1, 1], ![3, 1, -4]]

def raw7061step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -2, 1], ![1, 3, -4]]

def raw7062 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 2, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw7063 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 2, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw7064 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 2, 0], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw7065 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 2, 0], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw7065step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw7066 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 2, 0], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw7067 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 2, 0], ![1, 2, 0, -3]]

def raw7067step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![-2, 2, 0], ![3, 0, -3]]

def raw7067step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![2, -2, 0]]

def raw7068 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 3, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def raw7068step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![-2, 3, 0, -1], ![3, -1, -1, -1]]

def raw7068step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def raw7069 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 3, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw7069step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![-2, 3, -1, 0], ![3, -1, -1, -1]]

def raw7069step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw7070 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 3, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw7071 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 3, -1], ![1, 2, -1, -2]]

def raw7071step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![-2, 3, -1], ![3, -1, -2]]

def raw7071step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 2, -2], ![2, -3, 1], ![-3, 1, 2]]

def raw7071step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical221
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7072 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw7073 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw7074 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw7075 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw7076 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def raw7077 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw7077step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw7078 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw7079 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def raw7080 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw7081 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw7081step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![-2, 2, 0, 0], ![3, -1, -1, -1]]

def raw7081step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw7082 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw7083 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def raw7084 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw7084step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw7085 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![1, 1, 0, -2]]

def raw7085step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-2, 2, 0], ![3, -1, -2]]

def raw7085step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw7086 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw7087 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw7088 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def raw7089 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 3, -2], ![1, 1, -1, -1]]

def raw7089step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-2, 3, -1], ![3, -2, -1]]

def raw7089step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1]]

def raw7090 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 0, 0], ![1, 0, 2, -3]]

def raw7090step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![-2, 0, 2], ![3, 0, -3]]

def raw7090step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![3, 0, -3]]

def raw7090step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![3, -3]]

def raw7090step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw7091 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 1, -1], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def raw7091step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def raw7092 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0]]

def raw7093 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -2, 1, 0]]

def raw7094 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, 0, -1]]

def raw7094step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw7095 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, 0, -1, 0]]

def raw7095step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def raw7096 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw7096step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def raw7097 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 1, -1]]

def raw7097step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![-2, 1, 0, 1], ![3, -1, -1, -1]]

def raw7097step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw7098 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw7098step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![-2, 1, 1, 0], ![3, -1, -2, 0]]

def raw7098step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw7099 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -2, 2, -1]]

def raw7099step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![-2, 1, -1, 2], ![3, -1, -1, -1]]

def raw7099step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 2, -2]]

def raw7100 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -2, 1, 0]]

def raw7100step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![-2, 1, 0, 1], ![3, -1, -2, 0]]

def raw7100step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def raw7101 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 1, -1], ![1, 0, 1, -2]]

def raw7101step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![1, 1, -2]]

def raw7102 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 0, 0, 0], ![1, 0, 0, -1]]

def raw7102step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![1, 0, 0, -1]]

def raw7102step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![1, 0, -1]]

def raw7103 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 0, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical222
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7104 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, -1, 1]]

def raw7105 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -2, 1, 0]]

def raw7106 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![1, 0, 0, -1]]

def raw7106step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![1, 0, -1]]

def raw7107 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw7108 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 3, -3], ![1, 0, -1, 0]]

def raw7108step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 3, -3], ![1, -1, 0]]

def raw7109 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 4, -4], ![1, 0, -2, 1]]

def raw7109step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 4, -4], ![1, -2, 1]]

def raw7110 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, -2, 1], ![1, -1, 4, -4]]

def raw7110step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-2, -2, 4], ![3, 1, -4]]

def raw7110step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![1, 0, -1], ![1, 3, -4]]

def raw7111 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 3, -2]]

def raw7111step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![-2, -1, 0, 3], ![3, 0, -1, -2]]

def raw7111step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, -1, -1, 2], ![2, 1, 0, -3], ![-3, 0, 1, 2]]

def raw7111step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -3, 2], ![1, 0, 2, -3]]

def raw7112 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw7113 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw7114 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, -1, 0], ![1, -1, 3, -3]]

def raw7114step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-2, -1, 3], ![3, 0, -3]]

def raw7114step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1]]

def raw7115 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, 2, -1]]

def raw7115step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![-2, 0, 0, 2], ![3, -1, -1, -1]]

def raw7115step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, 1, -2, 0]]

def raw7116 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -2, 1, 0]]

def raw7116step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw7117 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, 0, -1], ![1, -1, 2, -2]]

def raw7117step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-2, 0, 2], ![3, -1, -2]]

def raw7117step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def raw7118 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, 1, -2], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw7118step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw7119 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw7119step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-2, 1, 1], ![3, -2, -1]]

def raw7119step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw7120 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw7120step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-2, 2, 0], ![3, -3, 0]]

def raw7120step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0]]

def raw7121 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def raw7121step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-2, 3, -1], ![3, -4, 1]]

def raw7121step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -1, 1], ![2, -3, 1], ![-3, 4, -1]]

def raw7121step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3]]

def raw7122 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 2, -1, -1], ![1, -2, 3, -2]]

def raw7122step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![-2, -1, 3], ![3, -1, -2]]

def raw7122step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -2, 2], ![2, 1, -3], ![-3, 1, 2]]

def raw7122step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -3, 2], ![1, 2, -3]]

def raw7123 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 2, 1, -3], ![1, -2, 1, 0]]

def raw7123step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![-2, 1, 1], ![3, -3, 0]]

def raw7123step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

def raw7124 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 2, 2, -4], ![1, -2, 0, 1]]

def raw7124step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![-2, 2, 0], ![3, -4, 1]]

def raw7124step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

def raw7125 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![1, -2, 0, 1], ![0, 2, 2, -4]]

def raw7125step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2], ![3, 1, -4]]

def raw7125step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

def raw7126 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![1, -2, 1, 0], ![0, 2, 1, -3]]

def raw7126step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -2, 2], ![-2, 1, 1], ![3, 0, -3]]

def raw7126step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

def raw7127 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![1, -2, 2, -1], ![0, 2, 0, -2]]

def raw7127step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -2, 2], ![-2, 2, 0], ![3, -1, -2]]

def raw7127step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def raw7128 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![1, -2, 3, -2], ![0, 2, -1, -1]]

def raw7128step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -2, 2], ![-2, 3, -1], ![3, -2, -1]]

def raw7128step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, 2, -2], ![2, -3, 1], ![-3, 2, 1]]

def raw7128step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -3, 2], ![1, 2, -3]]

def raw7129 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![1, -1, 1, -1], ![0, 1, 1, -2]]

def raw7129step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![-2, 1, 1], ![3, -1, -2]]

def raw7129step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw7130 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![1, -1, 4, -4], ![0, 1, -2, 1]]

def raw7130step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![-2, 4, -2], ![3, -4, 1]]

def raw7130step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![1, 0, -1], ![1, 3, -4]]

def raw7131 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, -1, 1, 1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw7131step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw7132 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw7132step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 1, -2], ![1, 0, 1, -2], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, -3, 4]]

def raw7132step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -3, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw7133 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 0, -1, 2], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw7133step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 1, -2], ![1, 0, 1, -2], ![0, -1, -3, 4], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw7133step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw7134 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 0, 2, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw7134step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![1, 0, -2, 1], ![-1, 1, -1, 1], ![-1, -1, 2, 0]]

def raw7134step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw7135 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 0, 3, -2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw7135step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 1, -2], ![1, 0, -3, 2], ![0, -1, 2, -1], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw7135step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical223
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7136 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 0, 3, -2], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def raw7136step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![1, 0, -3, 2], ![-1, 1, 1, -1], ![-1, -1, 1, 1]]

def raw7136step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -3, 2], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw7137 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 0, 3, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw7137step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![1, 0, -3, 2], ![-1, 1, 0, 0], ![-1, -1, 2, 0]]

def raw7137step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw7138 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, -2, 2], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw7138step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -1, 0], ![-1, -2, 0, 3], ![2, 2, 0, -4]]

def raw7138step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -2, 3], ![0, 2, 2, -4], ![1, -1, -1, 1]]

def raw7139 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, -2, 2], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def raw7139step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -1, 0], ![-1, -2, 3, 0], ![2, 2, -3, -1]]

def raw7139step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![0, -1, 1, 0], ![1, 2, -3, 0], ![-2, -2, 3, 1]]

def raw7139step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -2, -2, 3]]

def raw7140 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, -1, 1], ![1, -1, -1, 1], ![1, 0, 3, -4]]

def raw7140step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def raw7141 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, -1, 1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw7141step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, -1, -1, 1]]

def raw7142 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, -1, 1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw7142step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -1, 0], ![-1, -1, 3, -1], ![2, 1, -3, 0]]

def raw7142step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw7143 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, -1, 1], ![1, 0, 0, -1], ![1, -1, 2, -2]]

def raw7143step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![1, -1, 1, -1], ![-1, 0, 0, 1], ![-1, 1, -2, 2]]

def raw7143step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, -1, -2, 2]]

def raw7144 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, 1, -1], ![1, -1, 2, -2], ![1, 0, -2, 1]]

def raw7144step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, -1, -1, 1]]

def raw7145 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw7145step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def raw7146 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, 3, -3], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw7147 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, 3, -3], ![0, 1, -2, 1], ![2, -2, 0, 0]]

def raw7147step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 1, -2], ![-1, 3, -2, 0], ![2, -3, 1, 0]]

def raw7147step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 0, -2, 1], ![1, 2, 0, -3]]

def raw7148 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, 3, -3], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw7149 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, 3, -3], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, -1, 1]]

def raw7149step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, 3, -3], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw7150 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, 3, -3], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw7150step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -1, 0], ![-1, 3, -1, -1], ![2, -3, 1, 0]]

def raw7150step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 0, 1], ![0, 1, 2, -3], ![1, 1, -1, -1]]

def raw7151 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, 3, -3], ![1, 0, -2, 1], ![1, -1, 0, 0]]

def raw7151step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, 0, -1], ![-1, 3, -2, 0], ![2, -3, 1, 0]]

def raw7151step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![0, -1, 0, 1], ![1, -3, 2, 0], ![-2, 3, -1, 0]]

def raw7151step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw7152 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 2, -2, 1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def raw7152step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![1, -2, 2, -1], ![-1, 1, -1, 1], ![-1, 1, -2, 2]]

def raw7152step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def raw7153 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 2, 2, -3], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw7153step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 2, -1, -1], ![-1, 2, -1, 0], ![2, -3, 1, 0]]

def raw7153step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, 1, -1, -1]]

def raw7154 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 0, 2], ![0, 1, 3, -4], ![1, 1, -2, 0]]

def raw7154step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 2, 0, -2], ![0, -1, -3, 4], ![-1, -1, 2, 0]]

def raw7154step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw7155 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 0, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw7155step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -1, 0, 0]]

def raw7156 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 1, -2, 1], ![1, 1, 2, -4]]

def raw7156step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 2, -1, -1], ![0, -1, 2, -1], ![-1, -1, -2, 4]]

def raw7156step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw7157 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw7158 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 1, 2, -3], ![1, 1, -2, 0]]

def raw7158step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 2, -1, -1], ![0, -1, -2, 3], ![-1, -1, 2, 0]]

def raw7158step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, 0, -2, 1]]

def raw7159 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw7159step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw7160 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw7161 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 2, 0], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw7161step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw7162 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 2, 0], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw7162step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw7163 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 2, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw7164 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 3, -1], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def raw7164step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 2, -3, 1], ![0, -1, 2, -1], ![-1, -1, 0, 2]]

def raw7164step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -3, 1], ![1, 0, 1, -2]]

def raw7165 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 3, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw7165step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 2, -3, 1], ![0, -2, 2, 0], ![-1, 0, 0, 1]]

def raw7165step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, 0, 2], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw7166 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw7167 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, 0, 3, -4]]

def raw7167step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 1, 1, -2], ![0, -1, 1, 0], ![-1, 0, -3, 4]]

def raw7167step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical224
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7168 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def raw7168step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 1, 1, -2], ![0, -1, -2, 3], ![-1, 0, 0, 1]]

def raw7168step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw7169 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def raw7169step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 1, 1, -2], ![0, -1, -3, 4], ![-1, 0, 1, 0]]

def raw7169step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw7170 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, -1, 0, 0]]

def raw7170step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw7171 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 0, 1], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw7171step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 1, 0, -1], ![0, -1, -2, 3], ![-1, 0, 1, 0]]

def raw7171step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw7172 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 0, 1], ![0, 2, 2, -4], ![1, -1, -1, 1]]

def raw7172step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![-1, 0, 2, -1], ![2, 1, -4, 1]]

def raw7172step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, -2, 1], ![1, 0, -2, 1], ![-2, -1, 4, -1]]

def raw7172step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw7173 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw7173step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 1, -1, 0], ![0, 0, 1, -1], ![0, -1, -2, 3], ![-1, 0, 1, 0]]

def raw7173step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw7174 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 0, 2, -2], ![1, 0, -1, 0]]

def raw7174step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 1, -1, 0], ![0, -1, 1, 0], ![0, 0, -2, 2], ![-1, 0, 1, 0]]

def raw7174step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw7175 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1]]

def raw7176 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 0, -2, 2], ![1, 1, 1, -3]]

def raw7176step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 1, -2, 1], ![0, 0, 2, -2], ![-1, -1, -1, 3]]

def raw7176step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 1, -2]]

def raw7177 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw7178 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw7179 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, -1, 1, -1]]

def raw7179step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw7180 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def raw7180step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw7181 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![1, 1, -1, -1]]

def raw7181step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 2, -1], ![2, -1, -1]]

def raw7181step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![-2, 1, 1]]

def raw7181step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]

def raw7182 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw7182step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw7183 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, 0, -2, 1]]

def raw7183step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw7184 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 3, -2], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw7184step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 1, -3, 2], ![0, -2, 2, 0], ![-1, 1, 0, 0]]

def raw7184step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -2, 0, 1]]

def raw7185 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw7186 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 3, -2], ![1, 1, -2, 0]]

def raw7186step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 3, -2], ![2, -2, 0]]

def raw7186step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw7187 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, 0, 0, -1]]

def raw7187step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

def raw7188 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 3, -3]]

def raw7189 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw7189step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 0, 2, -2], ![0, -1, -3, 4], ![-1, 1, 0, 0]]

def raw7189step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw7190 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -2, 3, -2]]

def raw7191 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![1, 0, 3, -4]]

def raw7191step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 0, 2, -2], ![-1, 0, -3, 4]]

def raw7191step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-1, -3, 4]]

def raw7191step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![1, 1, -2]]

def raw7192 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw7192step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, -3, 4], ![-1, 1, 0, 0]]

def raw7192step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw7193 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-1, -1, 2, 0], ![1, 2, 1, -4]]

def raw7193step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![1, 1, -2, 0], ![-1, -2, -1, 4]]

def raw7193step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw7194 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 0, 3, -3], ![1, -1, 0, 0]]

def raw7194step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw7195 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw7196 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw7197 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-1, -1, 1, 1], ![1, 1, 2, -4]]

def raw7197step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![1, 1, -1, -1], ![-1, -1, -2, 4]]

def raw7197step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw7198 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 2, -2]]

def raw7199 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw7199step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![-1, -1, 2, 0], ![2, 1, -3, 0]]

def raw7199step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, -1, 1], ![1, 1, -2, 0], ![-2, -1, 3, 0]]

def raw7199step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical225
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7200 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def raw7200step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 0, 1, -1], ![0, -1, -3, 4], ![-1, 1, 1, -1]]

def raw7200step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw7201 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -2, 3, -2]]

def raw7201step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![-1, -1, -1, 3], ![2, 1, -1, -2]]

def raw7201step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, -2, 2], ![1, 1, 1, -3], ![-2, -1, 1, 2]]

def raw7201step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 1, 1, -3]]

def raw7202 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -2, 0, 1]]

def raw7202step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![-1, -1, 2, 0], ![2, 1, -4, 1]]

def raw7202step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, -2, 2], ![1, 1, -2, 0], ![-2, -1, 4, -1]]

def raw7202step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

def raw7203 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 1, -1, 1], ![0, 1, 3, -4]]

def raw7203step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![1, -1, 1, -1], ![0, -1, -3, 4]]

def raw7203step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 1, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw7204 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 1, 1], ![0, 2, 2, -4]]

def raw7204step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, 1, -1, -1], ![0, -2, -2, 4]]

def raw7204step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw7205 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 0, 0], ![0, 1, 2, -3], ![1, -1, -1, 1]]

def raw7205step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![-1, 0, 2, -1], ![2, 0, -3, 1]]

def raw7205step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, -1, 1], ![1, 0, -2, 1], ![-2, 0, 3, -1]]

def raw7205step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -1, 1], ![1, -2, 1], ![-2, 3, -1]]

def raw7205step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw7206 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 0, 0], ![1, 0, 1, -2]]

def raw7206step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2]]

def raw7206step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![2, 0, -2]]

def raw7206step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw7206step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw7207 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 0, 0, 0], ![1, 0, 0, -1]]

def raw7207step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![1, 0, 0, -1]]

def raw7207step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![1, 0, -1]]

def raw7208 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw7209 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, -1, 0]]

def raw7209step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw7210 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 1, -1]]

def raw7211 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0]]

def raw7211step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw7212 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -2, 1, 0]]

def raw7212step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 0, -1, 1], ![0, -2, 1, 1], ![-1, 2, -1, 0]]

def raw7212step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw7213 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![1, 0, 0, -1]]

def raw7213step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![1, 0, -1]]

def raw7214 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, 1, -1]]

def raw7215 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw7216 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1]]

def raw7217 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -2, 1, 0]]

def raw7217step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -2, 0, 1]]

def raw7218 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![1, 0, -1, 0]]

def raw7218step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -1, 0]]

def raw7219 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -1, 0, 0]]

def raw7220 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 0, 1]]

def raw7221 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, -1, 1]]

def raw7222 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -2, 0, 1]]

def raw7223 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![1, 0, -2, 1]]

def raw7223step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -2, 1]]

def raw7224 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 0, 1, -1], ![1, -1, 2, -2]]

def raw7224step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 2, -2]]

def raw7225 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 0, 3, -3], ![1, -1, 0, 0]]

def raw7225step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -1, 0, 0]]

def raw7226 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -2, 3, -2]]

def raw7226step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![-1, -2, 0, 3], ![2, 1, -1, -2]]

def raw7226step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, -1, -1, 2], ![1, 2, 0, -3], ![-2, -1, 1, 2]]

def raw7226step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -2, 2]]

def raw7227 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -2, 2, -1]]

def raw7228 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw7229 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw7230 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![1, -1, 1, -1], ![0, 0, 2, -2]]

def raw7230step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, 1, -1]]

def raw7231 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![1, -1, 3, -3]]

def raw7231step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-1, -2, 3], ![2, 1, -3]]

def raw7231step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical226
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7232 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 0, 3, -3], ![1, -1, -1, 1]]

def raw7232step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, -1, 1]]

def raw7233 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 3, -2]]

def raw7233step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![-1, -1, -1, 3], ![2, 0, 0, -2]]

def raw7233step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def raw7234 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-1, -1, 0, 2], ![1, 0, 3, -4]]

def raw7234step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw7235 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 2, -1]]

def raw7235step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![-1, -1, 0, 2], ![2, 0, -1, -1]]

def raw7235step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, -1, -1, 2], ![1, 1, 0, -2], ![-2, 0, 1, 1]]

def raw7235step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 1, -2]]

def raw7236 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -2, 1, 0]]

def raw7236step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw7237 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -2, 0, 1]]

def raw7237step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw7238 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, -1, 2]]

def raw7238step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![-1, -1, 3, -1], ![2, 0, -4, 2]]

def raw7238step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw7239 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 0, -1, 2], ![0, 1, 3, -4]]

def raw7239step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![1, 0, 1, -2], ![0, -1, -3, 4]]

def raw7239step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 0, 1, 0], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw7240 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 0, 2], ![0, 1, 3, -4]]

def raw7240step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw7241 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -1, 0], ![1, -1, 2, -2]]

def raw7241step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-1, -1, 2], ![2, 0, -2]]

def raw7241step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

def raw7242 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, 0, -1], ![1, -1, 1, -1]]

def raw7242step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![2, -1, -1]]

def raw7242step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw7243 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw7243step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0]]

def raw7243step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0]]

def raw7244 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, 2, -3], ![0, 1, -1, 0], ![1, -2, 0, 1]]

def raw7244step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw7245 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, 2, -3], ![1, -1, -1, 1]]

def raw7245step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1], ![2, -3, 1]]

def raw7245step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -1, 1], ![1, -2, 1], ![-2, 3, -1]]

def raw7245step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw7246 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, 3, -4], ![1, -1, -2, 2]]

def raw7246step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-1, 3, -2], ![2, -4, 2]]

def raw7246step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -1, 1], ![1, -3, 2], ![-2, 4, -2]]

def raw7246step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw7247 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 2, 1, -3], ![1, -2, 0, 1]]

def raw7247step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![-1, 1, 0], ![2, -3, 1]]

def raw7247step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -2, 2], ![1, -1, 0], ![-2, 3, -1]]

def raw7247step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw7248 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 2, 2, -4], ![1, -2, -1, 2]]

def raw7248step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![-1, 2, -1], ![2, -4, 2]]

def raw7248step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -2, 2], ![1, -2, 1], ![-2, 4, -2]]

def raw7248step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def raw7249 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![1, -1, 3, -3], ![0, 1, -2, 1]]

def raw7249step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![-1, 3, -2], ![2, -3, 1]]

def raw7249step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]

def raw7250 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-3, 2, 2, -1], ![4, -2, -2, 0]]

def raw7250step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0]]

def raw7251 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, -2, 2, 2], ![3, 2, -2, -3]]

def raw7251step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -2, 2], ![0, 2, -2], ![1, 2, -3]]

def raw7252 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, -2, 3, 1], ![3, 2, -3, -2]]

def raw7252step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -2, 2], ![0, 3, -3], ![1, 1, -2]]

def raw7253 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, -2, 4, 0], ![3, 2, -4, -1]]

def raw7253step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -2, 2], ![0, 4, -4], ![1, 0, -1]]

def raw7254 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 2, 2, -2], ![3, -2, -2, 1]]

def raw7254step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1]]

def raw7255 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -3, 3, 1], ![2, 3, -3, -2]]

def raw7255step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -3, 3], ![0, 3, -3], ![1, 1, -2]]

def raw7256 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -3, 4, 0], ![2, 3, -4, -1]]

def raw7256step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -3, 3], ![0, 4, -4], ![1, 0, -1]]

def raw7257 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -2, 2, 1], ![2, 2, -2, -2]]

def raw7257step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

def raw7258 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -2, 3, 0], ![2, 2, -3, -1]]

def raw7258step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

def raw7259 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -2, 4, -1], ![2, 2, -4, 0]]

def raw7259step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 4, -4], ![1, -1, 0]]

def raw7260 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw7260step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 1, 0, -2], ![0, 1, 0, -1], ![0, -1, 1, 0], ![-1, 0, 1, 0], ![-1, -1, -2, 4]]

def raw7260step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw7261 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![2, 1, 1, -4]]

def raw7261step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 1, 0, -2], ![0, 1, -1, 0], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-2, -1, -1, 4]]

def raw7261step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw7262 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 1, -3]]

def raw7262step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 1, 0, -2], ![0, 1, -1, 0], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-2, 0, -1, 3]]

def raw7262step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw7263 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw7263step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 1, 0, -2], ![0, 1, -1, 0], ![0, -1, 1, 0], ![-1, 0, 1, 0], ![-1, -1, -1, 3]]

def raw7263step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 1, 0], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical227
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7264 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 2, 2, -5]]

def raw7264step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 1, 0, -2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, -2, -2, 5]]

def raw7264step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw7265 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw7265step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 1, 0, -2], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, -1, -2, 4]]

def raw7265step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw7266 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 0, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, 2, -4]]

def raw7266step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 1, 0, -2], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![0, -2, -2, 4]]

def raw7266step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw7267 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw7267step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 1, 0, -2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, -2, 3]]

def raw7267step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw7268 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 0, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 1, 2, -3]]

def raw7268step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 1, 0, -2], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![0, -1, -2, 3]]

def raw7268step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw7269 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw7269step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0]]

def raw7270 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 1, 1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw7270step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1]]

def raw7271 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, -1, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![0, 2, 2, -4]]

def raw7271step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 0, 1, -2], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![0, -2, -2, 4]]

def raw7271step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw7272 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![0, 1, 2, -3]]

def raw7272step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 0, 1, -2], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![0, -1, -2, 3]]

def raw7272step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw7273 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw7273step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw7274 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, -2, 2], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw7274step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -1, 0], ![0, -2, 3, -1], ![1, 2, -3, 0]]

def raw7274step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![0, -1, 1, 0], ![0, 2, -3, 1], ![-1, -2, 3, 0]]

def raw7274step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -1, 1, -1]]

def raw7275 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, -1, 1], ![1, -1, 3, -3], ![1, 0, -2, 1]]

def raw7275step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -1, 0], ![0, -1, 3, -2], ![1, 1, -3, 1]]

def raw7275step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![0, -1, 1, 0], ![0, 1, -3, 2], ![-1, -1, 3, -1]]

def raw7275step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 0, 1], ![0, 1, 2, -3], ![1, 1, -1, -1]]

def raw7276 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -3, 3, 0], ![1, 3, -3, -1]]

def raw7276step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 3, -3], ![1, 0, -1]]

def raw7277 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -3, 4, -1], ![1, 3, -4, 0]]

def raw7277step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 4, -4], ![1, -1, 0]]

def raw7278 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw7278step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 2, -1, -1], ![0, -1, -1, 2], ![-1, -1, 2, 0]]

def raw7278step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw7279 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def raw7279step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 2, -1, -1], ![0, -2, 2, 0], ![-1, 0, -1, 2]]

def raw7279step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw7280 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw7280step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 2, -2, 0], ![0, -2, 0, 2], ![-1, 0, 2, -1]]

def raw7280step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw7281 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![1, 2, -2, -1]]

def raw7281step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

def raw7282 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 3, -1], ![1, 2, -3, 0]]

def raw7282step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0]]

def raw7283 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 4, -2], ![1, 2, -4, 1]]

def raw7283step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 4, -4], ![1, -2, 1]]

def raw7283step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 2, -2], ![0, -4, 4], ![-1, 2, -1]]

def raw7283step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 4, -4], ![1, -1, 0]]

def raw7284 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, -2, 3], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def raw7284step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 0, 1], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def raw7285 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, -2, 3], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def raw7285step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 2, -3], ![0, -1, -3, 4], ![-1, 0, 1, 0]]

def raw7285step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def raw7286 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, -1, 2], ![0, 1, -2, 1], ![1, 0, 3, -4]]

def raw7286step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 1, -2], ![0, -1, 2, -1], ![-1, 0, -3, 4]]

def raw7286step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw7287 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def raw7287step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 1, -2], ![0, -1, 1, 0], ![-1, 0, -2, 3]]

def raw7287step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw7288 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw7288step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 1, 0, -2]]

def raw7289 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, 0, -2, 1]]

def raw7289step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 1, -2], ![0, -1, -3, 4], ![-1, 0, 2, -1]]

def raw7289step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw7290 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![-1, -1, 0, 2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw7290step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![1, 1, 0, -2], ![0, -1, 1, 0], ![-1, 0, 1, 0], ![-1, -1, -2, 4]]

def raw7290step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw7291 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![2, 1, 1, -4]]

def raw7291step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![1, 1, -1, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-2, -1, -1, 4]]

def raw7291step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw7292 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![-1, -1, 1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 1, -3]]

def raw7292step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![1, 1, -1, -1], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-2, 0, -1, 3]]

def raw7292step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw7293 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![-1, -1, 1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw7293step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![1, 1, -1, -1], ![0, -1, 1, 0], ![-1, 0, 1, 0], ![-1, -1, -1, 3]]

def raw7293step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 1, 0], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw7294 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![-1, 0, -1, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 2, 2, -5]]

def raw7294step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, -2, -2, 5]]

def raw7294step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw7295 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw7295step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, -1, -2, 4]]

def raw7295step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical228
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7296 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![-1, 0, -1, 2], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, 2, -4]]

def raw7296step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![0, -2, -2, 4]]

def raw7296step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw7297 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw7297step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, -2, 3]]

def raw7297step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw7298 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![-1, 1, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 1, 2, -3]]

def raw7298step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![0, -1, -2, 3]]

def raw7298step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw7299 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 1, -1, 1], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw7299step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![-1, 0, 1, 0], ![-1, -1, -2, 4]]

def raw7299step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw7300 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 0, -1, 1], ![1, 1, 2, -4]]

def raw7300step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![0, -1, 1, 0], ![0, 0, 1, -1], ![-1, -1, -2, 4]]

def raw7300step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw7301 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![0, 1, 2, -3]]

def raw7301step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw7302 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![2, 1, 1, -4]]

def raw7302step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, 0, 1, -2], ![0, -1, 1, 0], ![-2, -1, -1, 4]]

def raw7302step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw7303 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![2, 0, 1, -3]]

def raw7303step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![0, -1, 1, 0], ![-2, 0, -1, 3]]

def raw7303step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw7304 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![-1, 1, -1, 1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw7304step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![-1, 0, 1, 0], ![-1, -1, -1, 3]]

def raw7304step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw7305 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![-1, 1, -1, 1], ![2, 1, 1, -4]]

def raw7305step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![0, 0, 1, -1], ![1, -1, 1, -1], ![-2, -1, -1, 4]]

def raw7305step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw7306 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 1, 1, -3]]

def raw7306step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-1, -1, -1, 3]]

def raw7306step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw7307 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![-1, 1, -1, 1], ![2, 0, 1, -3]]

def raw7307step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![0, -1, 1, 0], ![1, -1, 1, -1], ![-2, 0, -1, 3]]

def raw7307step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw7308 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 0, -1, 1], ![1, 1, 1, -3]]

def raw7308step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![0, -1, 1, 0], ![0, 0, 1, -1], ![-1, -1, -1, 3]]

def raw7308step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw7309 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw7309step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-1, 0, -1, 2]]

def raw7309step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw7310 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![0, 1, 1, -2]]

def raw7310step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw7311 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![-1, 0, -1, 2], ![1, -1, 0, 0], ![1, 2, 2, -5]]

def raw7311step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, 0, 1, -1], ![1, 0, 1, -2], ![-1, 1, 0, 0], ![-1, -2, -2, 5]]

def raw7311step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw7312 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![-1, 1, -1, 1], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw7312step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![-1, 1, 0, 0], ![-1, -1, -2, 4]]

def raw7312step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw7313 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, -1, 0, 1], ![1, 0, -1, 0], ![0, 2, 2, -4]]

def raw7313step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw7314 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -1, 0, 1], ![1, 2, 2, -5]]

def raw7314step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-1, -2, -2, 5]]

def raw7314step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw7315 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![0, 2, 2, -4]]

def raw7315step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw7316 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, -1, 0, 1], ![1, 1, 2, -4]]

def raw7316step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![0, 1, 0, -1], ![-1, -1, -2, 4]]

def raw7316step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw7317 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![0, 1, 2, -3]]

def raw7317step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw7318 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![0, 0, -1, 1], ![0, 2, 2, -4]]

def raw7318step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw7319 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, 2, 2, -3]]

def raw7319step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, -2, -2, 3]]

def raw7319step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw7320 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![-1, 1, -1, 1], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw7320step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, -1, 1, 0], ![1, -1, 1, -1], ![-1, 1, 0, 0], ![-1, 0, -2, 3]]

def raw7320step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw7321 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, -1, 0, 1], ![1, 0, -1, 0], ![0, 1, 2, -3]]

def raw7321step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw7322 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![0, -1, 0, 1], ![1, 0, 2, -3]]

def raw7322step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, 0, -1], ![-1, 0, -2, 3]]

def raw7322step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw7323 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![0, 0, 2, -2]]

def raw7323step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, 0, -1], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![0, 0, -2, 2]]

def raw7323step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw7324 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![0, 0, -1, 1], ![0, 1, 2, -3]]

def raw7324step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw7325 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, 1, 2, -2]]

def raw7325step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw7326 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 3, -2], ![0, 0, -2, 2], ![1, 1, -1, -1]]

def raw7326step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, -3, 2], ![0, 0, 2, -2], ![-1, -1, 1, 1]]

def raw7326step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def raw7327 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 3, -2], ![0, 1, -3, 2], ![1, 0, 0, -1]]

def raw7327step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical229
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7328 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -3, 3], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw7328step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, 3, -3], ![0, -1, -3, 4], ![-1, 1, 0, 0]]

def raw7328step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -1, 0, 0]]

def raw7329 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -3, 3], ![1, 0, 3, -4]]

def raw7329step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, 3, -3], ![-1, 0, -3, 4]]

def raw7329step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 0, -1], ![0, 3, -3], ![-1, -3, 4]]

def raw7329step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 3, -3], ![1, 0, -1]]

def raw7330 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw7330step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, 2, -2], ![0, -1, -2, 3], ![-1, 1, 0, 0]]

def raw7330step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 0, 0]]

def raw7331 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def raw7331step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, 2, -2], ![0, -1, -3, 4], ![-1, 1, 1, -1]]

def raw7331step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 1, -1]]

def raw7332 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -2, 2], ![0, 2, -1, -1], ![1, -2, 3, -2]]

def raw7332step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![0, -2, -1, 3], ![1, 2, -1, -2]]

def raw7332step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, -2, 2], ![0, 2, 1, -3], ![-1, -2, 1, 2]]

def raw7332step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw7333 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -2, 2], ![1, 0, 2, -3]]

def raw7333step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, 2, -2], ![-1, 0, -2, 3]]

def raw7333step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 0, -1], ![0, 2, -2], ![-1, -2, 3]]

def raw7333step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![1, 0, -1]]

def raw7334 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![-1, 0, -1, 2], ![1, -1, 0, 0], ![1, -1, 0, 0], ![0, 2, 2, -4]]

def raw7334step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, 1, -1], ![1, 0, 1, -2], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![0, -2, -2, 4]]

def raw7334step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw7335 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![-1, 1, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![0, 1, 2, -3]]

def raw7335step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![0, -1, -2, 3]]

def raw7335step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw7336 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -1, 0, 1], ![1, -1, 0, 0], ![0, 2, 2, -4]]

def raw7336step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw7337 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -2, 0, 1]]

def raw7337step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw7338 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![0, -1, 0, 1], ![0, 2, 2, -4]]

def raw7338step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw7339 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 2, 2, -3]]

def raw7339step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![1, -2, -2, 3]]

def raw7339step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw7340 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, -1, 0, 1], ![1, -1, 0, 0], ![0, 1, 2, -3]]

def raw7340step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw7341 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![0, -1, 0, 1], ![0, 1, 2, -3]]

def raw7341step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw7342 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 1, 2, -2]]

def raw7342step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw7343 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -2, 0, 1]]

def raw7343step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![0, -1, 1, 0], ![1, 1, -3, 1]]

def raw7343step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![-1, -1, 3, -1]]

def raw7343step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw7344 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -2, -1, 2]]

def raw7344step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![0, -1, 2, -1], ![1, 1, -4, 2]]

def raw7344step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, -2, 2], ![0, 1, -2, 1], ![-1, -1, 4, -2]]

def raw7344step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw7345 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw7345step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw7346 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![-1, 1, -1, 1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw7346step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw7347 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![0, -1, 0, 1], ![1, -1, 1, -1]]

def raw7347step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, -1, 1], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, 0, -1], ![-1, 1, -1, 1]]

def raw7347step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw7348 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![0, -1, 1, 0]]

def raw7348step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw7349 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw7349step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw7350 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -2, -1, 2]]

def raw7350step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, -1, 1], ![0, -2, 0, 2], ![-1, 2, 1, -2]]

def raw7350step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 2, -2]]

def raw7351 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw7351step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, -2, 2], ![0, -1, 0, 1], ![-1, 1, 2, -2]]

def raw7351step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 2, -2]]

def raw7352 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, -3, 2], ![1, -1, 3, -3]]

def raw7352step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![0, -3, 3], ![1, 2, -3]]

def raw7352step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -1, 1], ![0, 3, -3], ![-1, -2, 3]]

def raw7352step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1]]

def raw7353 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, -2, 1], ![1, -1, 2, -2]]

def raw7353step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![1, 1, -2]]

def raw7353step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -1, 1], ![0, 2, -2], ![-1, -1, 2]]

def raw7353step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

def raw7354 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, -1, 0], ![1, -1, 1, -1]]

def raw7354step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1]]

def raw7354step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]

def raw7355 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -2, -1, 2]]

def raw7355step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, -1, 0, 1], ![0, -1, -1, 2], ![-1, 2, 1, -2]]

def raw7355step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 2, -2]]

def raw7356 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 2, -3], ![1, -1, -2, 2]]

def raw7356step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2]]

def raw7356step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 3, -2]]

def raw7356step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def raw7357 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, -3, 3, -1], ![0, 3, -3, 0]]

def raw7357step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -3, 3], ![0, 3, -3], ![1, -1, 0]]

def raw7357step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 3, -3], ![1, 0, -1]]

def raw7358 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, -2, 2, -1], ![0, 2, -2, 0]]

def raw7358step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0]]

def raw7358step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

def raw7359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]

def raw7359step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![2, 0, -2], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-2, -3, 5]]

def raw7359step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]

def raw737 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]

def raw738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw739 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]

def raw740 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

def raw741 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]

def raw742 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 3, -4]]

def raw743 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]

def raw744 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]

def raw745 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -2, 1], ![1, 3, -4]]

def raw745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 3, -4]]

def raw746 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

def raw747 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]

def raw747step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw748 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]

def raw748step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-2, -1, 3]]

def raw748step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1]]

def raw750 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]

def raw750step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]

def raw750step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

def raw751 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]

def raw752 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]

def raw752step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]

def raw752step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

def raw753 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

def raw753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 0, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]

def raw753step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]

def raw753step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw754 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]

def raw754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]

def raw754step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]

def raw754step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw755 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]

def raw755step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 0, 3], ![1, 0, 1, -2], ![2, 0, -1, -1]]

def raw755step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]

def raw755step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -2, 1]]

def raw756 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

def raw756step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

def raw756step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

def raw757 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]

def raw757step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]

def raw757step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -3, 2], ![1, 2, -3]]

def raw758 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

def raw758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]

def raw758step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]

def raw758step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw759 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]

def raw759step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 0, 0], ![-1, -1, 2], ![-2, 2, 0]]

def raw759step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, -1, 2], ![-2, 2, 0]]

def raw759step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]

def raw760 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]

def raw760step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]

def raw760step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

def raw761 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]

def raw761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1]]

def raw761step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]

def raw761step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw762 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]

def raw762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![-2, 2, 0]]

def raw762step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]

def raw762step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw763 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]

def raw763step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 0, 3], ![1, 1, 0, -2], ![2, -1, 0, -1]]

def raw763step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]

def raw763step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -2, 1]]

def raw764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]

def raw765 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]

def raw766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

def raw767 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical230
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]

def raw7360step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -3, 4]]

def raw7360step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw7361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]

def raw7361step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-2, -2, 4]]

def raw7361step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def raw7362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![2, 1, -3]]

def raw7362step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![-2, -1, 3]]

def raw7362step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

def raw7363 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def raw7363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def raw7364 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw7364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw7365 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

def raw7365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

def raw7366 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 3, -4]]

def raw7366step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 2, -3], ![-1, 1, 0], ![-1, -3, 4]]

def raw7366step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3]]

def raw7367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 4, -5]]

def raw7367step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, 1, -2], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -4, 5]]

def raw7367step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -4, 5], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw7368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw7368step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, 1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -2, 3]]

def raw7368step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw7369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 4, -4]]

def raw7369step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

def raw7370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![0, 3, -3]]

def raw7370step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw7371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw7371step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw7372 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw7372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw7373 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw7373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]

def raw7373step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw7374 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw7374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw7375 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw7375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw7376 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 3, -4]]

def raw7376step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 1, -2], ![-1, 2, -1], ![-1, -3, 4]]

def raw7376step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2]]

def raw7377 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2]]

def raw7377step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

def raw7378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]

def raw7378step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-2, -3, 5]]

def raw7378step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw7379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]

def raw7379step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -3, 4]]

def raw7379step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

def raw7380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2], ![1, -1, 0], ![2, 3, -5]]

def raw7380step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, 1, -2], ![-1, 1, 0], ![-2, -3, 5]]

def raw7380step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw7381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 3, -5]]

def raw7381step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, -3, 5]]

def raw7381step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw7382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def raw7382step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -3, 4]]

def raw7382step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw7383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![0, -1, 1], ![1, 3, -4]]

def raw7383step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, -3, 4]]

def raw7383step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw7384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 3, -3]]

def raw7384step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw7385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]

def raw7387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]

def raw7387step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-2, -2, 4]]

def raw7387step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw7388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![2, 1, -3]]

def raw7388step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]

def raw7389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2], ![1, -1, 0], ![2, 2, -4]]

def raw7389step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![-1, 1, 0], ![-2, -2, 4]]

def raw7389step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw7390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 2, -4]]

def raw7390step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, -2, 4]]

def raw7390step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw7391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]

def raw7391step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -2, 3]]

def raw7391step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical231
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw7393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]

def raw7393step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![-2, -1, 3]]

def raw7393step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw7394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![-1, -2, 3], ![2, 1, -3]]

def raw7394step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

def raw7395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2]]

def raw7395step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![-1, -1, 2]]

def raw7395step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw7396 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]

def raw7396step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw7397 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1]]

def raw7397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, -1, 0], ![0, -2, 2], ![-1, 3, -2], ![-1, 0, 1]]

def raw7397step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw7398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![-1, 3, -2], ![1, -3, 2]]

def raw7398step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

def raw7399 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]

def raw7399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw7400 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 3, -2], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1]]

def raw7400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, -3, 2], ![0, 3, -3], ![-1, 0, 1], ![-1, 0, 1]]

def raw7400step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

def raw7401 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 3, -2], ![1, -3, 2], ![1, 0, -1]]

def raw7401step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3]]

def raw7402 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 4, -3], ![1, -2, 1], ![1, -2, 1]]

def raw7402step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2]]

def raw7403 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1]]

def raw7403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![0, 3, -3], ![1, -3, 2], ![-1, 0, 1], ![-1, 0, 1]]

def raw7403step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

def raw7404 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 2, -2], ![1, 1, -2]]

def raw7404step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 3, -3], ![0, -2, 2], ![-1, -1, 2]]

def raw7404step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

def raw7405 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1]]

def raw7405step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 3, -3], ![1, 0, -1]]

def raw7406 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 3, -3], ![1, 0, -1]]

def raw7407 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 3, -3], ![1, 0, -1], ![0, 0, 0]]

def raw7407step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 3, -3], ![1, 0, -1]]

def raw7408 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![1, 3, -4]]

def raw7408step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 0, -1], ![0, 3, -3], ![-1, -3, 4]]

def raw7408step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 3, -3], ![1, 0, -1]]

def raw7409 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1]]

def raw7409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw7410 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![-1, 4, -3], ![1, -1, 0], ![1, -1, 0]]

def raw7410step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw7411 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2]]

def raw7411step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2]]

def raw7411step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

def raw7412 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

def raw7413 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1]]

def raw7413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![0, 2, -2], ![0, -3, 3], ![0, 1, -1], ![-1, 0, 1]]

def raw7413step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

def raw7415 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![0, 0, 0]]

def raw7415step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0]]

def raw7416 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 4, -4], ![0, -1, 1], ![1, -1, 0]]

def raw7416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0]]

def raw7417 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 4, -4], ![1, -2, 1]]

def raw7417step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 2, -2], ![0, -4, 4], ![-1, 2, -1]]

def raw7417step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 4, -4], ![1, -1, 0]]

def raw7418 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 4, -4], ![1, -1, 0], ![0, -1, 1]]

def raw7418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0]]

def raw7419 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![1, 2, -3]]

def raw7419step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 0, -1], ![0, 2, -2], ![-1, -2, 3]]

def raw7419step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![1, 0, -1]]

def raw7420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 4, -5]]

def raw7420step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![0, 1, -1], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, -4, 5]]

def raw7420step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -4, 5], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw7421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw7421step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![0, 1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, -2, 3]]

def raw7421step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw7422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![0, 4, -4]]

def raw7422step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

def raw7423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![0, 3, -3]]

def raw7423step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical232
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw7424step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw7425 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 3, -2], ![1, -2, 1], ![1, 0, -1]]

def raw7425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw7426 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0]]

def raw7426step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw7427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 4, -5]]

def raw7427step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, -4, 5]]

def raw7427step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -4, 5], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw7428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3]]

def raw7428step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]

def raw7428step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw7429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 4, -5]]

def raw7429step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, -4, 5]]

def raw7429step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw7430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 4, -4]]

def raw7430step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0]]

def raw7431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 3, -3]]

def raw7431step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![0, -3, 3]]

def raw7431step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw7432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3]]

def raw7432step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![-1, -2, 3]]

def raw7432step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw7433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 2, -2]]

def raw7433step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def raw7434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![0, -1, 1], ![0, 4, -4]]

def raw7434step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0]]

def raw7435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 3, -3]]

def raw7435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 3, -3]]

def raw7435step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

def raw7436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![-1, 4, -3]]

def raw7436step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw7437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-1, 3, -2]]

def raw7437step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw7438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw7438step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw7439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1]]

def raw7439step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw7440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0]]

def raw7440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw7441 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![0, -2, 2], ![1, 0, -1]]

def raw7441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![0, 1, -1], ![0, -3, 3], ![0, 2, -2], ![-1, 0, 1]]

def raw7441step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

def raw7442 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0]]

def raw7442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

def raw7443 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![1, -2, 1], ![0, 0, 0]]

def raw7443step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![0, 1, -1], ![0, -3, 3], ![-1, 2, -1], ![0, 0, 0]]

def raw7443step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 1, -1], ![0, -3, 3], ![-1, 2, -1]]

def raw7443step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

def raw7444 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![0, -1, 1]]

def raw7444step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

def raw7445 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]

def raw7445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw7446 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1], ![1, -3, 2], ![1, 0, -1]]

def raw7446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![0, -1, 1], ![1, -2, 1], ![-1, 3, -2], ![-1, 0, 1]]

def raw7446step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw7447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![-1, 3, -2], ![1, -3, 2]]

def raw7447step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw7448 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0]]

def raw7448step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw7449 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1]]

def raw7449step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1]]

def raw7449step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw7450 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1]]

def raw7450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw7451 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![0, -3, 3], ![1, 0, -1]]

def raw7451step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

def raw7452 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![0, 0, 0]]

def raw7452step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 3, -2], ![0, 0, 0]]

def raw7452step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 3, -2]]

def raw7452step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def raw7453 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![1, -1, 0]]

def raw7454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 3, -2], ![1, -3, 2]]

def raw7454step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![-1, 3, -2]]

def raw7454step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![1, -3, 2], ![-1, 3, -2]]

def raw7454step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw7455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, 3, -1], ![1, -3, 2]]

def raw7455step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical233
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-1, 3, -2], ![0, -3, 3]]

def raw7456step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw7457 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![1, -2, 1]]

def raw7457step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 0, -1], ![0, -2, 2], ![-1, 2, -1]]

def raw7457step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -1, 0]]

def raw7458 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 3, -3], ![0, -3, 3], ![1, 0, -1]]

def raw7458step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 3, -3], ![1, 0, -1]]

def raw7459 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 3, -3], ![1, -3, 2]]

def raw7459step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 0, -1], ![0, -3, 3], ![-1, 3, -2]]

def raw7459step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 3, -3], ![1, -1, 0]]

def raw7460 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 3, -3], ![1, -3, 2], ![0, 0, 0]]

def raw7460step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -3, 3], ![-1, 3, -2], ![0, 0, 0]]

def raw7460step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 0, -1], ![0, -3, 3], ![-1, 3, -2]]

def raw7460step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 3, -3], ![1, -1, 0]]

def raw7461 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 4, -4], ![1, -4, 3]]

def raw7461step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 0, -1], ![0, -4, 4], ![-1, 4, -3]]

def raw7461step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 4, -4], ![1, -1, 0]]

def raw7462 : Matrix (Fin 2) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1]]

def raw7462step0 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

def raw7463 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-4, 2, 1, 1], ![5, -2, -2, -1]]

def raw7463step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 2, -2], ![1, 1, -2], ![0, 1, -1]]

def raw7463step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 1, -1], ![0, 2, -2], ![1, 1, -2]]

def raw7464 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-3, 2, -2, 3], ![4, -2, 1, -3]]

def raw7464step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![1, -2, 1], ![0, 3, -3]]

def raw7464step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![0, 3, -3], ![1, -2, 1]]

def raw7465 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-3, 3, -2, 2], ![4, -3, 1, -2]]

def raw7465step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 3, -3], ![1, -2, 1], ![0, 2, -2]]

def raw7465step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![0, 3, -3], ![1, -2, 1]]

def raw7466 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-3, 3, 1, -1], ![4, -3, -2, 1]]

def raw7466step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 3, -3], ![1, 1, -2], ![0, -1, 1]]

def raw7466step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, -1, 1], ![0, 3, -3], ![1, 1, -2]]

def raw7467 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-2, -2, 1, 3], ![3, 2, -2, -3]]

def raw7467step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -2, 2], ![1, 1, -2], ![0, 3, -3]]

def raw7467step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -2, 2], ![0, 3, -3], ![1, 1, -2]]

def raw7468 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-2, 2, -2, 2], ![3, -2, 1, -2]]

def raw7468step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![1, -2, 1], ![0, 2, -2]]

def raw7468step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1]]

def raw7469 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-2, 2, 1, -1], ![3, -2, -2, 1]]

def raw7469step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![1, 1, -2], ![0, -1, 1]]

def raw7469step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2]]

def raw7470 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-2, 3, -2, 1], ![3, -3, 1, -1]]

def raw7470step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 3, -3], ![1, -2, 1], ![0, 1, -1]]

def raw7470step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 3, -3], ![1, -2, 1]]

def raw7471 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-1, -3, 1, 3], ![2, 3, -2, -3]]

def raw7471step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -3, 3], ![1, 1, -2], ![0, 3, -3]]

def raw7471step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -3, 3], ![0, 3, -3], ![1, 1, -2]]

def raw7472 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-1, -2, -2, 5], ![2, 2, 1, -5]]

def raw7472step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![1, -2, 1], ![0, 5, -5]]

def raw7472step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 5, -5], ![1, -2, 1]]

def raw7473 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-1, -2, 1, 2], ![2, 2, -2, -2]]

def raw7473step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![1, 1, -2], ![0, 2, -2]]

def raw7473step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

def raw7474 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw7474step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, -1, 0], ![1, 1, 0, -2], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, -1, -1, 3]]

def raw7474step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw7475 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-1, -1, 0, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, 1, -3]]

def raw7475step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, -1, 0], ![1, 1, 0, -2], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![0, -2, -1, 3]]

def raw7475step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw7476 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-1, 2, -4, 3], ![2, -2, 3, -3]]

def raw7476step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -4, 3], ![0, 3, -3]]

def raw7476step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, -2, 2], ![-1, 4, -3], ![0, -3, 3]]

def raw7476step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![0, 3, -3], ![1, -2, 1]]

def raw7477 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-1, 2, -3, 2], ![2, -2, 2, -2]]

def raw7477step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -3, 2], ![0, 2, -2]]

def raw7477step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, -2, 2], ![-1, 3, -2], ![0, -2, 2]]

def raw7477step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1]]

def raw7478 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-1, 2, -2, 1], ![2, -2, 1, -1]]

def raw7478step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -2, 1], ![0, 1, -1]]

def raw7478step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1]]

def raw7479 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-1, 3, -4, 2], ![2, -3, 3, -2]]

def raw7479step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -4, 3], ![0, 2, -2]]

def raw7479step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, -3, 3], ![-1, 4, -3], ![0, -2, 2]]

def raw7479step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![0, 3, -3], ![1, -2, 1]]

def raw7480 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-1, 4, -2, -1], ![2, -4, 1, 1]]

def raw7480step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 4, -4], ![1, -2, 1], ![0, -1, 1]]

def raw7480step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 4, -4], ![1, -2, 1]]

def raw7481 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -3, 1, 2], ![1, 3, -2, -2]]

def raw7481step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![1, 1, -2], ![0, 2, -2]]

def raw7481step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 3, -3], ![-1, -1, 2], ![0, -2, 2]]

def raw7481step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

def raw7482 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, -2, 4], ![1, 2, 1, -4]]

def raw7482step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![1, -2, 1], ![0, 4, -4]]

def raw7482step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 2, -2], ![-1, 2, -1], ![0, -4, 4]]

def raw7482step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 4, -4], ![1, -1, 0]]

def raw7483 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, 1, 1], ![1, 2, -2, -1]]

def raw7483step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![1, 1, -2], ![0, 1, -1]]

def raw7483step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 2, -2], ![-1, -1, 2], ![0, -1, 1]]

def raw7483step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

def raw7484 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -3, 4], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def raw7484step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![0, 1, 3, -4], ![0, 0, -2, 2], ![-1, -1, 0, 2]]

def raw7484step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, 0, 3, -4]]

def raw7485 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -3, 4], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw7485step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw7486 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -3, 4], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def raw7486step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def raw7487 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -2, 3], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw7487step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical234
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7488 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -1, 2], ![0, 0, -2, 2], ![1, 1, 2, -4]]

def raw7488step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![0, 1, 1, -2], ![0, 0, 2, -2], ![-1, -1, -2, 4]]

def raw7488step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw7489 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw7489step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, -1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, -1, -1, 3]]

def raw7489step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw7490 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![-1, 0, -1, 2], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, 1, -3]]

def raw7490step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, -1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![0, -2, -1, 3]]

def raw7490step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw7491 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![-1, 1, -1, 1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw7491step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, -1, 0], ![0, 1, 0, -1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![-1, 1, 0, 0], ![-1, -1, -1, 3]]

def raw7491step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw7492 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, -1, 0, 1], ![1, 0, -1, 0], ![0, 2, 1, -3]]

def raw7492step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, -1, 0], ![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-1, 0, 1, 0], ![0, -2, -1, 3]]

def raw7492step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, -1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw7493 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, -1, 0, 1], ![1, 1, 1, -3]]

def raw7493step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, -1, 0], ![0, 1, 0, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![0, 1, 0, -1], ![-1, -1, -1, 3]]

def raw7493step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw7494 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![0, 1, 1, -2]]

def raw7494step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw7495 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![0, 0, -1, 1], ![0, 2, 1, -3]]

def raw7495step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, -1, 0], ![0, 1, 0, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![0, 0, 1, -1], ![0, -2, -1, 3]]

def raw7495step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -2, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0]]

def raw7496 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, 2, 1, -2]]

def raw7496step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw7497 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -3, 3], ![1, 0, 2, -3]]

def raw7497step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, -1, 0], ![0, 0, 3, -3], ![-1, 0, -2, 3]]

def raw7497step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -1, 0], ![0, 3, -3], ![-1, -2, 3]]

def raw7497step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 3, -3], ![1, -1, 0]]

def raw7498 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 1, -1]]

def raw7498step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![1, -2, 0, 1], ![0, 2, -1, -1]]

def raw7498step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw7499 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -2, 2], ![1, 0, 1, -2]]

def raw7499step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, -1, 0], ![0, 0, 2, -2], ![-1, 0, -1, 2]]

def raw7499step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -1, 0], ![0, 2, -2], ![-1, -1, 2]]

def raw7499step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -1, 0]]

def raw7500 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, -3, 2], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw7500step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw7501 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -1, 1]]

def raw7501step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![0, 0, -1, 1], ![0, -1, 1, 0], ![-1, 1, 1, -1]]

def raw7501step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw7502 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

def raw7503 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw7503step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![1, 1, 0, -2], ![0, -1, -1, 2]]

def raw7503step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw7504 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -2, -2, 3]]

def raw7504step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![1, 1, 0, -2], ![0, -1, -2, 3]]

def raw7504step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, -2, 2], ![-1, -1, 0, 2], ![0, 1, 2, -3]]

def raw7504step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def raw7505 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 1, -3, 2], ![1, -1, 2, -2]]

def raw7505step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![1, -3, 2], ![0, 2, -2]]

def raw7505step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -1, 1], ![-1, 3, -2], ![0, -2, 2]]

def raw7505step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def raw7506 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -1, 2]]

def raw7506step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![1, 0, 0, -1], ![0, -1, -1, 2]]

def raw7506step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 1, 0, -2]]

def raw7507 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 1, 1, -2], ![1, -1, -2, 2]]

def raw7507step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![0, -2, 2]]

def raw7507step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![0, 2, -2]]

def raw7507step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

def raw7508 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 1, 2, -3], ![1, -1, -3, 3]]

def raw7508step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![0, -3, 3]]

def raw7508step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -1, 1], ![-1, -2, 3], ![0, 3, -3]]

def raw7508step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1]]

def raw7509 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 2, -4, 2], ![1, -2, 3, -2]]

def raw7509step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![1, -4, 3], ![0, 2, -2]]

def raw7509step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -2, 2], ![-1, 4, -3], ![0, -2, 2]]

def raw7509step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0]]

def raw7510 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 2, -3, 1], ![1, -2, 2, -1]]

def raw7510step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![1, -3, 2], ![0, 1, -1]]

def raw7510step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -2, 2], ![-1, 3, -2], ![0, -1, 1]]

def raw7510step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def raw7511 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 2, 0, -2], ![1, -2, -1, 2]]

def raw7511step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![0, -2, 2]]

def raw7511step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

def raw7512 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 2, 1, -3], ![1, -2, -2, 3]]

def raw7512step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![0, -3, 3]]

def raw7512step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![0, 3, -3]]

def raw7512step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

def raw7513 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 3, -4, 1], ![1, -3, 3, -1]]

def raw7513step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 3, -3], ![1, -4, 3], ![0, 1, -1]]

def raw7513step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -3, 3], ![-1, 4, -3], ![0, -1, 1]]

def raw7513step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0]]

def raw7514 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 4, -2, -2], ![1, -4, 1, 2]]

def raw7514step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 4, -4], ![1, -2, 1], ![0, -2, 2]]

def raw7514step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -4, 4], ![-1, 2, -1], ![0, 2, -2]]

def raw7514step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 4, -4], ![1, -1, 0]]

def raw7515 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![1, -3, 1, 1], ![0, 3, -2, -1]]

def raw7515step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -3, 3], ![1, 1, -2], ![0, 1, -1]]

def raw7515step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, 3, -3], ![-1, -1, 2], ![0, -1, 1]]

def raw7515step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

def raw7516 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![1, -2, -2, 3], ![0, 2, 1, -3]]

def raw7516step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -2, 2], ![1, -2, 1], ![0, 3, -3]]

def raw7516step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, 2, -2], ![-1, 2, -1], ![0, -3, 3]]

def raw7516step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

def raw7517 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-3, 2, -2, 3], ![4, -2, 0, -2]]

def raw7517step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![2, -2, 0], ![-1, 3, -2]]

def raw7517step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, -2, 2], ![-2, 2, 0], ![1, -3, 2]]

def raw7517step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -4, 3], ![1, 2, -3]]

def raw7518 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-3, 2, -1, 2], ![4, -2, -1, -1]]

def raw7518step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![2, -1, -1], ![-1, 2, -1]]

def raw7518step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, -2, 2], ![-2, 1, 1], ![1, -2, 1]]

def raw7518step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -2, 1], ![1, 3, -4]]

def raw7519 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-3, 2, 0, 1], ![4, -2, -2, 0]]

def raw7519step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![2, 0, -2], ![-1, 1, 0]]

def raw7519step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, -2, 2], ![-2, 0, 2], ![1, -1, 0]]

def raw7519step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical235
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7520 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-3, 3, -1, 1], ![4, -3, -1, 0]]

def raw7520step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 3, -3], ![2, -1, -1], ![-1, 1, 0]]

def raw7520step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, -3, 3], ![-2, 1, 1], ![1, -1, 0]]

def raw7520step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, -1, 0], ![1, 3, -4]]

def raw7521 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-3, 3, 0, 0], ![4, -3, -2, 1]]

def raw7521step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 3, -3], ![2, 0, -2], ![-1, 0, 1]]

def raw7521step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, -3, 3], ![-2, 0, 2], ![1, 0, -1]]

def raw7521step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 0, -1], ![1, 3, -4]]

def raw7522 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-2, 2, -2, 2], ![3, -2, 0, -1]]

def raw7522step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![2, -2, 0], ![-1, 2, -1]]

def raw7522step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, -2, 2], ![-2, 2, 0], ![1, -2, 1]]

def raw7522step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

def raw7523 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-2, 2, -1, 1], ![3, -2, -1, 0]]

def raw7523step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![2, -1, -1], ![-1, 1, 0]]

def raw7523step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, -2, 2], ![-2, 1, 1], ![1, -1, 0]]

def raw7523step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

def raw7524 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-2, 2, 0, 0], ![3, -2, -2, 1]]

def raw7524step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![2, 0, -2], ![-1, 0, 1]]

def raw7524step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

def raw7525 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-2, 3, -1, 0], ![3, -3, -1, 1]]

def raw7525step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 3, -3], ![2, -1, -1], ![-1, 0, 1]]

def raw7525step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, -3, 3], ![-2, 1, 1], ![1, 0, -1]]

def raw7525step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 0, -1], ![1, 2, -3]]

def raw7526 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-2, 4, -2, 0], ![3, -4, 0, 1]]

def raw7526step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 4, -4], ![2, -2, 0], ![-1, 0, 1]]

def raw7526step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, -4, 4], ![-2, 2, 0], ![1, 0, -1]]

def raw7526step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![1, -3, 2], ![1, -1, 0]]

def raw7527 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, -3, 0, 4], ![2, 3, -2, -3]]

def raw7527step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -3, 3], ![2, 0, -2], ![-1, 4, -3]]

def raw7527step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 3, -3], ![-2, 0, 2], ![1, -4, 3]]

def raw7527step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -4, 3], ![1, 1, -2]]

def raw7528 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, -3, 2, 2], ![2, 3, -4, -1]]

def raw7528step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -3, 3], ![2, 2, -4], ![-1, 2, -1]]

def raw7528step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 3, -3], ![-2, -2, 4], ![1, -2, 1]]

def raw7528step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, -2, 1], ![1, 1, -2]]

def raw7529 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, -2, -2, 5], ![2, 2, 0, -4]]

def raw7529step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![2, -2, 0], ![-1, 5, -4]]

def raw7529step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-2, 2, 0], ![1, -5, 4]]

def raw7529step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -2, 1], ![1, 4, -5]]

def raw7530 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, -2, -1, 4], ![2, 2, -1, -3]]

def raw7530step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![2, -1, -1], ![-1, 4, -3]]

def raw7530step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-2, 1, 1], ![1, -4, 3]]

def raw7530step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -2, 1], ![1, 3, -4]]

def raw7531 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, -2, 0, 3], ![2, 2, -2, -2]]

def raw7531step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![2, 0, -2], ![-1, 3, -2]]

def raw7531step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-2, 0, 2], ![1, -3, 2]]

def raw7531step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

def raw7532 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, -2, 1, 2], ![2, 2, -3, -1]]

def raw7532step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![2, 1, -3], ![-1, 2, -1]]

def raw7532step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-2, -1, 3], ![1, -2, 1]]

def raw7532step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def raw7533 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, -2, 2, 1], ![2, 2, -4, 0]]

def raw7533step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![2, 2, -4], ![-1, 1, 0]]

def raw7533step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-2, -2, 4], ![1, -1, 0]]

def raw7533step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def raw7534 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, -2, 3, 0], ![2, 2, -5, 1]]

def raw7534step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![2, 3, -5], ![-1, 0, 1]]

def raw7534step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-2, -3, 5], ![1, 0, -1]]

def raw7534step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def raw7535 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, 2, -4, 3], ![2, -2, 2, -2]]

def raw7535step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![2, -4, 2], ![-1, 3, -2]]

def raw7535step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, -2, 2], ![-2, 4, -2], ![1, -3, 2]]

def raw7535step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -2, 1], ![1, 2, -3]]

def raw7536 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, 2, -3, 2], ![2, -2, 1, -1]]

def raw7536step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![2, -3, 1], ![-1, 2, -1]]

def raw7536step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, -2, 2], ![-2, 3, -1], ![1, -2, 1]]

def raw7536step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def raw7537 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, 2, -2, 1], ![2, -2, 0, 0]]

def raw7537step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![2, -2, 0], ![-1, 1, 0]]

def raw7537step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

def raw7538 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, 2, -1, 0], ![2, -2, -1, 1]]

def raw7538step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![2, -1, -1], ![-1, 0, 1]]

def raw7538step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, -2, 2], ![-2, 1, 1], ![1, 0, -1]]

def raw7538step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw7539 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, 2, 0, -1], ![2, -2, -2, 2]]

def raw7539step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![2, 0, -2], ![-1, -1, 2]]

def raw7539step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, -2, 2], ![-2, 0, 2], ![1, 1, -2]]

def raw7539step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]

def raw7540 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, 2, 1, -2], ![2, -2, -3, 3]]

def raw7540step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![2, 1, -3], ![-1, -2, 3]]

def raw7540step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, -2, 2], ![-2, -1, 3], ![1, 2, -3]]

def raw7540step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 1, -2], ![1, 2, -3]]

def raw7541 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, 3, -4, 2], ![2, -3, 2, -1]]

def raw7541step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![2, -4, 2], ![-1, 2, -1]]

def raw7541step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, -3, 3], ![-2, 4, -2], ![1, -2, 1]]

def raw7541step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, -2, 1], ![1, 1, -2]]

def raw7542 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, 3, -2, 0], ![2, -3, 0, 1]]

def raw7542step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![2, -2, 0], ![-1, 0, 1]]

def raw7542step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, -3, 3], ![-2, 2, 0], ![1, 0, -1]]

def raw7542step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

def raw7543 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, 3, -1, -1], ![2, -3, -1, 2]]

def raw7543step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![2, -1, -1], ![-1, -1, 2]]

def raw7543step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, -3, 3], ![-2, 1, 1], ![1, 1, -2]]

def raw7543step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]

def raw7544 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, 3, 0, -2], ![2, -3, -2, 3]]

def raw7544step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![2, 0, -2], ![-1, -2, 3]]

def raw7544step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, -3, 3], ![-2, 0, 2], ![1, 2, -3]]

def raw7544step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 1, -2], ![1, 2, -3]]

def raw7545 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, 4, -3, 0], ![2, -4, 1, 1]]

def raw7545step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 4, -4], ![2, -3, 1], ![-1, 0, 1]]

def raw7545step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, -4, 4], ![-2, 3, -1], ![1, 0, -1]]

def raw7545step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 4, -4], ![1, -2, 1], ![1, -1, 0]]

def raw7546 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -3, 0, 3], ![1, 3, -2, -2]]

def raw7546step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![2, 0, -2], ![-1, 3, -2]]

def raw7546step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 3, -3], ![-2, 0, 2], ![1, -3, 2]]

def raw7546step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

def raw7547 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -3, 1, 2], ![1, 3, -3, -1]]

def raw7547step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![2, 1, -3], ![-1, 2, -1]]

def raw7547step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 3, -3], ![-2, -1, 3], ![1, -2, 1]]

def raw7547step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw7548 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -3, 2, 1], ![1, 3, -4, 0]]

def raw7548step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![2, 2, -4], ![-1, 1, 0]]

def raw7548step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 3, -3], ![-2, -2, 4], ![1, -1, 0]]

def raw7548step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw7549 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, -2, 4], ![1, 2, 0, -3]]

def raw7549step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![2, -2, 0], ![-1, 4, -3]]

def raw7549step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 2, -2], ![-2, 2, 0], ![1, -4, 3]]

def raw7549step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

def raw7550 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, -1, 3], ![1, 2, -1, -2]]

def raw7550step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![-1, 3, -2]]

def raw7550step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 2, -2], ![-2, 1, 1], ![1, -3, 2]]

def raw7550step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

def raw7551 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def raw7551step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, -2, 0], ![1, 0, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical236
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7552 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw7553 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 2, 1, -3], ![1, 0, -3, 2]]

def raw7554 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![1, 2, -2, -1]]

def raw7554step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![2, 0, -2], ![-1, 2, -1]]

def raw7554step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

def raw7555 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 1, 1], ![1, 2, -3, 0]]

def raw7555step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![2, 1, -3], ![-1, 1, 0]]

def raw7555step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 2, -2], ![-2, -1, 3], ![1, -1, 0]]

def raw7555step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw7556 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 2, 0], ![1, 2, -4, 1]]

def raw7556step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![2, 2, -4], ![-1, 0, 1]]

def raw7556step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 2, -2], ![-2, -2, 4], ![1, 0, -1]]

def raw7556step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw7557 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 3, -1], ![1, 2, -5, 2]]

def raw7557step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![2, 3, -5], ![-1, -1, 2]]

def raw7557step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 2, -2], ![-2, -3, 5], ![1, 1, -2]]

def raw7557step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def raw7558 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -3, 4], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw7558step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw7559 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw7560 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -3, 4], ![0, 2, 1, -3], ![1, -1, 0, 0]]

def raw7561 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -3, 4], ![1, 1, 1, -3]]

def raw7561step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![2, -3, 1], ![-1, 4, -3]]

def raw7561step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 1, -1], ![-2, 3, -1], ![1, -4, 3]]

def raw7561step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def raw7562 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -2, 3], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw7562step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![2, -2, 0, 0], ![-1, 3, -1, -1]]

def raw7562step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw7563 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -2, 3], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw7563step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -2, 1], ![0, 1, 2, -3], ![0, -2, 0, 2], ![-1, 1, 0, 0]]

def raw7563step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -2, 0, 1]]

def raw7564 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw7565 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 1, 0, -1], ![1, 0, -2, 1]]

def raw7565step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw7566 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, 0, -3, 2]]

def raw7566step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -2, 1], ![0, 1, 0, -1], ![0, -1, -1, 2], ![-1, 0, 3, -2]]

def raw7566step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw7567 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 2, 1, -3], ![1, -1, -3, 3]]

def raw7568 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 1, 0], ![0, 2, 0, -2], ![1, -1, -3, 3]]

def raw7568step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![2, 1, 0, -3], ![-1, 0, -2, 3]]

def raw7568step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, -2, 1], ![-2, -1, 0, 3], ![1, 0, 2, -3]]

def raw7568step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, -2, 1]]

def raw7569 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -3, 3], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw7569step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -1, 0, 0]]

def raw7570 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -3, 3], ![0, 2, 1, -3], ![1, -2, 0, 1]]

def raw7571 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, -1, 1]]

def raw7571step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 1, -1]]

def raw7572 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -2, -1, 2]]

def raw7573 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

def raw7573step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-1, 0, 0, 0, 1], ![0, 0, 1, 1, -2], ![2, 0, 0, 0, -2], ![-1, 0, -1, -1, 3]]

def raw7573step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![2, 0, 0, -2], ![-1, -1, -1, 3]]

def raw7573step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def raw7574 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw7574step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![2, 0, 0, -2], ![-1, 0, -1, 2]]

def raw7574step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![-1, -1, 2]]

def raw7574step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

def raw7575 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, -2, 3]]

def raw7575step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 3, -2]]

def raw7576 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -2, -2, 3]]

def raw7576step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 3, -2]]

def raw7577 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -3, 4]]

def raw7578 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -3, 3]]

def raw7578step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![2, 1, 0, -3], ![-1, -1, -1, 3]]

def raw7578step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def raw7579 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -2, -3, 4]]

def raw7579step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![2, 1, 0, -3], ![-1, -1, -2, 4]]

def raw7579step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, 2, -3]]

def raw7580 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, -1, 2]]

def raw7580step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![2, -1, 0, -1], ![-1, 0, -1, 2]]

def raw7580step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, -1, -1, 2], ![-2, 1, 0, 1], ![1, 0, 1, -2]]

def raw7580step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 1, -2]]

def raw7581 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 1, 0, -1], ![0, 0, 0, 0], ![1, -1, -2, 2]]

def raw7581step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 0, -1], ![2, 0, 0, -2], ![-1, -1, 0, 2]]

def raw7581step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![-1, -1, 2]]

def raw7581step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

def raw7582 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -2, -1, 2]]

def raw7582step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![2, 0, -1, -1], ![-1, -1, 0, 2]]

def raw7582step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, -1, -1, 2], ![-2, 0, 1, 1], ![1, 1, 0, -2]]

def raw7582step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 1, -2]]

def raw7583 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

def raw7583step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![2, 0, 0, -2], ![-1, -1, -1, 3]]

def raw7583step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, 0, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical237
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7584 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -2, -3, 4]]

def raw7584step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![2, 0, 1, -3], ![-1, -1, -2, 4]]

def raw7584step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 1, 0, -2]]

def raw7585 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw7585step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![-1, -1, 2]]

def raw7585step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

def raw7586 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 1, 1, -2], ![0, 1, 0, -1], ![1, -2, -3, 4]]

def raw7586step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![2, 1, 0, -3], ![-1, -2, -1, 4]]

def raw7586step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 1, 0, -2]]

def raw7587 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 1, 1, -2], ![1, -1, -3, 3]]

def raw7587step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![2, 1, -3], ![-1, -2, 3]]

def raw7587step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]

def raw7588 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 2, -4, 2], ![1, -2, 2, -1]]

def raw7588step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![2, -4, 2], ![-1, 2, -1]]

def raw7588step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -2, 2], ![-2, 4, -2], ![1, -2, 1]]

def raw7588step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def raw7589 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 2, -3, 1], ![1, -2, 1, 0]]

def raw7589step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![2, -3, 1], ![-1, 1, 0]]

def raw7589step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -2, 2], ![-2, 3, -1], ![1, -1, 0]]

def raw7589step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw7590 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 2, -1, -1], ![1, -2, -1, 2]]

def raw7590step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![-1, -1, 2]]

def raw7590step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -2, 2], ![-2, 1, 1], ![1, 1, -2]]

def raw7590step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw7591 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 2, 0, -2], ![1, -2, -2, 3]]

def raw7591step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![2, 0, -2], ![-1, -2, 3]]

def raw7591step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

def raw7592 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 2, 1, -3], ![1, -2, -3, 4]]

def raw7592step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![2, 1, -3], ![-1, -3, 4]]

def raw7592step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -2, 2], ![-2, -1, 3], ![1, 3, -4]]

def raw7592step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 3, -4]]

def raw7593 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 3, -4, 1], ![1, -3, 2, 0]]

def raw7593step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 3, -3], ![2, -4, 2], ![-1, 1, 0]]

def raw7593step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -3, 3], ![-2, 4, -2], ![1, -1, 0]]

def raw7593step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw7594 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 3, -2, -1], ![1, -3, 0, 2]]

def raw7594step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 3, -3], ![2, -2, 0], ![-1, -1, 2]]

def raw7594step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -3, 3], ![-2, 2, 0], ![1, 1, -2]]

def raw7594step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

def raw7595 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 3, -1, -2], ![1, -3, -1, 3]]

def raw7595step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 3, -3], ![2, -1, -1], ![-1, -2, 3]]

def raw7595step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -3, 3], ![-2, 1, 1], ![1, 2, -3]]

def raw7595step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 0, -1], ![1, 2, -3]]

def raw7596 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 3, 0, -3], ![1, -3, -2, 4]]

def raw7596step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 3, -3], ![2, 0, -2], ![-1, -3, 4]]

def raw7596step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -3, 3], ![-2, 0, 2], ![1, 3, -4]]

def raw7596step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 0, -1], ![1, 3, -4]]

def raw7597 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 4, -3, -1], ![1, -4, 1, 2]]

def raw7597step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 4, -4], ![2, -3, 1], ![-1, -1, 2]]

def raw7597step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -4, 4], ![-2, 3, -1], ![1, 1, -2]]

def raw7597step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 4, -4], ![1, -2, 1], ![1, -1, 0]]

def raw7598 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![1, -3, 1, 1], ![0, 3, -3, 0]]

def raw7598step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -3, 3], ![2, 1, -3], ![-1, 1, 0]]

def raw7598step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, 3, -3], ![-2, -1, 3], ![1, -1, 0]]

def raw7598step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw7599 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![1, -2, -3, 4], ![0, 2, 1, -3]]

def raw7599step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -2, 2], ![2, -3, 1], ![-1, 4, -3]]

def raw7599step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, 2, -2], ![-2, 3, -1], ![1, -4, 3]]

def raw7599step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 3, -4]]

def raw7600 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![1, -2, -1, 2], ![0, 2, -1, -1]]

def raw7600step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![-1, 2, -1]]

def raw7600step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, 2, -2], ![-2, 1, 1], ![1, -2, 1]]

def raw7600step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw7601 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![1, -2, 0, 1], ![0, 2, -2, 0]]

def raw7601step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![-1, 1, 0]]

def raw7601step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

def raw7602 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![1, -2, 2, -1], ![0, 2, -4, 2]]

def raw7602step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -2, 2], ![2, 2, -4], ![-1, -1, 2]]

def raw7602step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, 2, -2], ![-2, -2, 4], ![1, 1, -2]]

def raw7602step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def raw7603 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![1, 2, 0, -3], ![0, -2, -2, 4]]

def raw7603step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 2, -2], ![2, 0, -2], ![-1, -3, 4]]

def raw7603step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, -2, 2], ![-2, 0, 2], ![1, 3, -4]]

def raw7603step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

def raw7604 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![2, -3, 1, 0], ![-1, 3, -3, 1]]

def raw7604step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![0, -3, 3], ![2, 1, -3], ![-1, 0, 1]]

def raw7604step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![0, 3, -3], ![-2, -1, 3], ![1, 0, -1]]

def raw7604step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw7605 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![2, -2, 0, 0], ![-1, 2, -2, 1]]

def raw7605step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![0, -2, 2], ![2, 0, -2], ![-1, 0, 1]]

def raw7605step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

def raw7606 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![2, -2, 1, -1], ![-1, 2, -3, 2]]

def raw7606step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![0, -2, 2], ![2, 1, -3], ![-1, -1, 2]]

def raw7606step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![0, 2, -2], ![-2, -1, 3], ![1, 1, -2]]

def raw7606step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def raw7607 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![3, -3, 0, 0], ![-2, 3, -2, 1]]

def raw7607step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![0, -3, 3], ![2, 0, -2], ![-1, 0, 1]]

def raw7607step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![0, 3, -3], ![-2, 0, 2], ![1, 0, -1]]

def raw7607step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

def raw7608 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![3, -2, 0, -1], ![-2, 2, -2, 2]]

def raw7608step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![0, -2, 2], ![2, 0, -2], ![-1, -1, 2]]

def raw7608step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![0, 2, -2], ![-2, 0, 2], ![1, 1, -2]]

def raw7608step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

def raw7609 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![-1, 0, -3, 4], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw7609step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -3, 2], ![1, 0, 3, -4], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw7609step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 1, -3, 2], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw7610 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![-1, 0, -2, 3], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw7610step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -3, 2], ![1, 0, 2, -3], ![0, -1, 0, 1], ![-1, 1, 1, -1], ![-1, 0, 0, 1]]

def raw7610step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 1, -3, 2], ![0, 1, 2, -3], ![1, -1, 1, -1]]

def raw7611 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![0, -3, 1, 2], ![1, 3, -4, 0]]

def raw7611step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![3, 1, -4], ![-2, 2, 0]]

def raw7611step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 3, -3], ![-3, -1, 4], ![2, -2, 0]]

def raw7611step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]

def raw7612 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![0, -1, -3, 4], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw7612step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![3, -3, 0, 0], ![-2, 4, -1, -1]]

def raw7612step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw7613 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw7613step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![3, -3, 0, 0], ![-2, 4, -2, 0]]

def raw7613step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, -2, 1], ![-3, 3, 0, 0], ![2, -4, 2, 0]]

def raw7613step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -3, 3], ![0, 2, 2, -4], ![1, -2, 0, 1]]

def raw7614 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![0, -1, -1, 2], ![0, 0, -2, 2], ![1, 1, 0, -2]]

def raw7614step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -3, 2], ![0, 1, 1, -2], ![0, 0, 2, -2], ![-1, -1, 0, 2]]

def raw7614step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -3, 2], ![1, 0, 1, -2]]

def raw7615 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -3, 4]]

def raw7615step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![3, 0, 0, -3], ![-2, -1, -1, 4]]

def raw7615step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, -1, 1], ![0, 0, 3, -3], ![1, 1, 0, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical238
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7616 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![0, 1, 0, -1], ![1, -1, -3, 3]]

def raw7616step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![3, 0, -3], ![-2, -1, 3]]

def raw7616step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1]]

def raw7617 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![0, 2, 0, -2], ![1, -2, -3, 4]]

def raw7617step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![3, 0, -3], ![-2, -2, 4]]

def raw7617step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 3, -3], ![2, 0, -2]]

def raw7618 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![1, -3, 1, 1], ![0, 3, -4, 1]]

def raw7618step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -3, 3], ![3, 1, -4], ![-2, 1, 1]]

def raw7618step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, 3, -3], ![-3, -1, 4], ![2, -1, -1]]

def raw7618step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]

def raw7619 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![1, -2, 1, 0], ![0, 2, -4, 2]]

def raw7619step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -2, 2], ![3, 1, -4], ![-2, 0, 2]]

def raw7619step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

def raw7620 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![2, -3, 1, 0], ![-1, 3, -4, 2]]

def raw7620step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![0, -3, 3], ![3, 1, -4], ![-2, 0, 2]]

def raw7620step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![0, 3, -3], ![-3, -1, 4], ![2, 0, -2]]

def raw7620step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]

def raw7621 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![2, -2, 1, -1], ![-1, 2, -4, 3]]

def raw7621step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![0, -2, 2], ![3, 1, -4], ![-2, -1, 3]]

def raw7621step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![0, 2, -2], ![-3, -1, 4], ![2, 1, -3]]

def raw7621step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]

def raw7622 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![4, -4]]

def raw7622step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]

def raw7623 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![-1, 1], ![-1, 1], ![2, -2], ![3, -3]]

def raw7623step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]

def raw7624 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]

def raw7624step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]

def raw7625 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![0, 0], ![1, -1], ![1, -1], ![1, -1]]

def raw7625step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]

def raw7625step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7626 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![0, 0], ![2, -2], ![1, -1]]

def raw7626step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]

def raw7626step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw7627 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![0, 0], ![3, -3]]

def raw7627step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![3, -3]]

def raw7627step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw7628 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![0, 0], ![3, -3], ![0, 0]]

def raw7628step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![0, 0], ![3, -3]]

def raw7628step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![3, -3]]

def raw7628step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw7629 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![0, 0], ![0, 0], ![2, -2]]

def raw7629step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![0, 0], ![2, -2]]

def raw7629step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]

def raw7629step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw7630 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![0, 0], ![1, -1], ![1, -1]]

def raw7630step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]

def raw7630step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7631 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![0, 0], ![2, -2]]

def raw7631step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]

def raw7631step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw7632 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![0, 0], ![2, -2], ![0, 0]]

def raw7632step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![0, 0], ![2, -2]]

def raw7632step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]

def raw7632step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw7633 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![0, 0], ![1, -1]]

def raw7633step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]

def raw7633step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7634 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]

def raw7634step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7635 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![0, 0]]

def raw7635step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]

def raw7635step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7636 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]

def raw7636step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw7637 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2], ![0, 0]]

def raw7637step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]

def raw7637step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw7638 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![0, 0], ![1, -1]]

def raw7638step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]

def raw7638step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw7639 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]

def raw7639step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw7640 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1], ![0, 0]]

def raw7640step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]

def raw7640step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw7641 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1], ![0, 0], ![0, 0]]

def raw7641step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1], ![0, 0]]

def raw7641step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]

def raw7641step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw7642 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![3, -3]]

def raw7642step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw7643 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![3, -3], ![0, 0]]

def raw7643step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![3, -3]]

def raw7643step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw7644 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-2, 2], ![-1, 1], ![1, -1], ![4, -4]]

def raw7644step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]

def raw7645 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-2, 2], ![-1, 1], ![2, -2], ![3, -3]]

def raw7645step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]

def raw7646 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]

def raw7646step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]

def raw7647 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-2, 2], ![2, -2], ![2, -2]]

def raw7647step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical239
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7648 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![-2, 2], ![1, -1], ![4, -4]]

def raw7648step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]

def raw7649 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![-2, 2], ![2, -2], ![3, -3]]

def raw7649step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]

def raw7650 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![-1, 1], ![0, 0], ![4, -4]]

def raw7650step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![-1, 1], ![4, -4]]

def raw7650step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]

def raw7651 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![3, -3]]

def raw7651step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]

def raw7652 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![2, -2]]

def raw7652step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]

def raw7653 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![0, 0], ![0, 0], ![3, -3]]

def raw7653step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![0, 0], ![3, -3]]

def raw7653step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]

def raw7653step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

def raw7654 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![0, 0], ![1, -1], ![2, -2]]

def raw7654step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]

def raw7654step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7655 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![0, 0], ![2, -2], ![1, -1]]

def raw7655step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1]]

def raw7655step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7656 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![0, 0], ![3, -3]]

def raw7656step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]

def raw7656step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

def raw7657 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![0, 0], ![2, -2]]

def raw7657step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]

def raw7657step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7658 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7659 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]

def raw7659step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7660 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2], ![0, 0]]

def raw7660step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]

def raw7660step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7661 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1]]

def raw7661step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7662 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1], ![0, 0]]

def raw7662step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1]]

def raw7662step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7663 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]

def raw7663step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

def raw7664 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3], ![0, 0]]

def raw7664step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]

def raw7664step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

def raw7665 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3], ![0, 0], ![0, 0]]

def raw7665step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3], ![0, 0]]

def raw7665step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]

def raw7665step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

def raw7666 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![-1, 1], ![3, -3]]

def raw7666step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]

def raw7666step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

def raw7667 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![0, 0], ![0, 0], ![2, -2]]

def raw7667step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![0, 0], ![2, -2]]

def raw7667step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![2, -2]]

def raw7667step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw7667step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw7668 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![0, 0], ![1, -1], ![1, -1]]

def raw7668step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![1, -1], ![1, -1]]

def raw7668step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw7669 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![0, 0], ![2, -2]]

def raw7669step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![2, -2]]

def raw7669step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw7669step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw7670 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![1, -1], ![1, -1]]

def raw7670step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw7671 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![2, -2]]

def raw7671step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw7671step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw7672 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![2, -2], ![0, 0]]

def raw7672step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![2, -2]]

def raw7672step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw7672step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw7673 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![-1, 1], ![0, 0], ![2, -2]]

def raw7673step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![-1, 1], ![2, -2]]

def raw7673step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7674 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![-1, 1], ![2, -2]]

def raw7674step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7675 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![0, 0], ![-1, 1], ![2, -2]]

def raw7675step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![-1, 1], ![2, -2]]

def raw7675step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7676 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![0, 0], ![0, 0], ![1, -1]]

def raw7676step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![0, 0], ![1, -1]]

def raw7676step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw7677 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![0, 0], ![1, -1]]

def raw7677step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw7678 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw7679 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![0, 0]]

def raw7679step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

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

def raw769 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]

def raw769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]

def raw769step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

def raw770 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]

def raw770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

def raw771 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]

def raw771step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 3, 0]]

def raw771step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw772 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]

def raw772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]

def raw773 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]

def raw774 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1]]

def raw774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]

def raw775 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]

def raw776 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]

def raw777 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]

def raw777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]

def raw778 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]

def raw778step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

def raw779 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]

def raw779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]

def raw780 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]

def raw780step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw781 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

def raw781step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]

def raw781step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw782 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]

def raw782step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]

def raw782step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw783 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

def raw784 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical240
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7680 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![0, 0], ![0, 0]]

def raw7680step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![0, 0]]

def raw7680step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw7682 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![2, -2], ![-1, 1]]

def raw7682step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7683 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw7683step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw7684 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2], ![-1, 1], ![1, -1]]

def raw7684step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7685 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2], ![0, 0]]

def raw7685step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw7685step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw7686 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2], ![0, 0], ![0, 0]]

def raw7686step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2], ![0, 0]]

def raw7686step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw7686step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw7687 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2], ![0, 0], ![0, 0], ![0, 0]]

def raw7687step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2], ![0, 0], ![0, 0]]

def raw7687step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2], ![0, 0]]

def raw7687step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw7687step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw7688 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2], ![1, -1], ![-1, 1]]

def raw7688step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7689 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2], ![1, -1], ![0, 0], ![-1, 1]]

def raw7689step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2], ![1, -1], ![-1, 1]]

def raw7689step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7690 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![3, -3], ![-1, 1]]

def raw7690step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

def raw7691 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![3, -3], ![0, 0], ![-1, 1]]

def raw7691step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![3, -3], ![-1, 1]]

def raw7691step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

def raw7692 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-2, 2], ![0, 0], ![2, -2], ![1, -1]]

def raw7692step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-2, 2], ![2, -2], ![1, -1]]

def raw7692step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]

def raw7692step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw7693 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-2, 2], ![1, -1], ![2, -2]]

def raw7693step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]

def raw7693step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw7694 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-2, 2], ![1, -1], ![2, -2], ![0, 0]]

def raw7694step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-2, 2], ![1, -1], ![2, -2]]

def raw7694step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]

def raw7694step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw7695 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-2, 2], ![2, -2], ![1, -1]]

def raw7695step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]

def raw7695step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw7696 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]

def raw7696step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]

def raw7696step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7697 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1]]

def raw7697step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1]]

def raw7697step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7698 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![0, 0], ![0, 0], ![2, -2]]

def raw7698step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![0, 0], ![2, -2]]

def raw7698step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![2, -2]]

def raw7698step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw7698step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw7699 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![0, 0], ![2, -2]]

def raw7699step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![2, -2]]

def raw7699step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw7699step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw7700 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![0, 0], ![2, -2], ![0, 0]]

def raw7700step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![0, 0], ![2, -2]]

def raw7700step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![2, -2]]

def raw7700step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw7700step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw7701 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![1, -1], ![-1, 1], ![2, -2]]

def raw7701step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![-1, 1], ![2, -2]]

def raw7701step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7702 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![1, -1], ![0, 0], ![1, -1]]

def raw7702step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![1, -1], ![1, -1]]

def raw7702step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw7703 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![1, -1], ![1, -1]]

def raw7703step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw7704 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![1, -1], ![1, -1], ![0, 0]]

def raw7704step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![1, -1], ![1, -1]]

def raw7704step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw7705 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![2, -2]]

def raw7705step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw7705step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw7706 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![2, -2], ![0, 0]]

def raw7706step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![2, -2]]

def raw7706step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw7706step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw7707 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![0, 0], ![-1, 1], ![2, -2]]

def raw7707step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![2, -2]]

def raw7707step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw7707step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw7709 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![1, -1]]

def raw7709step0 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

def raw7710 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![1, -1], ![-2, 2], ![2, -2]]

def raw7710step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-2, 2], ![2, -2]]

def raw7710step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical241
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7712 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![1, -1], ![-1, 1], ![1, -1]]

def raw7712step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![1, -1]]

def raw7712step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw7714 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![1, -1], ![1, -1], ![-1, 1]]

def raw7714step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![1, -1], ![-1, 1]]

def raw7714step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw7715 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![1, -1], ![1, -1], ![0, 0], ![-1, 1]]

def raw7715step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![1, -1], ![1, -1], ![-1, 1]]

def raw7715step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![1, -1], ![-1, 1]]

def raw7715step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw7716 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![2, -2], ![-1, 1]]

def raw7716step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1]]

def raw7716step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw7717 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![2, -2], ![0, 0], ![-1, 1]]

def raw7717step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![2, -2], ![-1, 1]]

def raw7717step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1]]

def raw7717step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw7718 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

def raw7719 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-2, 2], ![0, 0], ![2, -2]]

def raw7719step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-2, 2], ![2, -2]]

def raw7719step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw7720 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-2, 2], ![1, -1], ![1, -1]]

def raw7720step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7721 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-2, 2], ![1, -1], ![1, -1], ![0, 0]]

def raw7721step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-2, 2], ![1, -1], ![1, -1]]

def raw7721step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7722 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-2, 2], ![2, -2]]

def raw7722step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw7723 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-2, 2], ![2, -2], ![0, 0]]

def raw7723step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-2, 2], ![2, -2]]

def raw7723step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw7724 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-2, 2], ![2, -2], ![0, 0], ![0, 0]]

def raw7724step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-2, 2], ![2, -2], ![0, 0]]

def raw7724step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-2, 2], ![2, -2]]

def raw7724step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw7726 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![-1, 1], ![0, 0], ![2, -2]]

def raw7726step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![-1, 1], ![2, -2]]

def raw7726step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7728 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![-1, 1], ![2, -2]]

def raw7728step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7729 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![0, 0], ![0, 0], ![1, -1]]

def raw7729step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![0, 0], ![1, -1]]

def raw7729step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![1, -1]]

def raw7729step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw7730 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![0, 0], ![1, -1]]

def raw7730step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![1, -1]]

def raw7730step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw7731 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![1, -1]]

def raw7731step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw7732 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![1, -1], ![0, 0]]

def raw7732step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![1, -1]]

def raw7732step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw7733 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![1, -1], ![0, 0], ![0, 0]]

def raw7733step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![1, -1], ![0, 0]]

def raw7733step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![1, -1]]

def raw7733step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw7735 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![0, 0]]

def raw7735step0 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

def raw7738 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![1, -1], ![-1, 1]]

def raw7738step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw7740 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![1, -1], ![-1, 1], ![0, 0]]

def raw7740step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![1, -1], ![-1, 1]]

def raw7740step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw7741 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![1, -1], ![-1, 1], ![0, 0], ![0, 0]]

def raw7741step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![1, -1], ![-1, 1], ![0, 0]]

def raw7741step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![1, -1], ![-1, 1]]

def raw7741step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw7742 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![1, -1], ![0, 0], ![-1, 1]]

def raw7742step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![1, -1], ![-1, 1]]

def raw7742step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw7743 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![1, -1], ![0, 0], ![0, 0], ![-1, 1]]

def raw7743step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![1, -1], ![0, 0], ![-1, 1]]

def raw7743step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![1, -1], ![-1, 1]]

def raw7743step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical242
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7744 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![-2, 2]]

def raw7744step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7745 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-2, 2], ![0, 0], ![1, -1]]

def raw7745step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-2, 2], ![1, -1]]

def raw7745step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw7746 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-2, 2], ![1, -1]]

def raw7746step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw7747 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-2, 2], ![1, -1], ![0, 0]]

def raw7747step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-2, 2], ![1, -1]]

def raw7747step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw7748 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-2, 2], ![1, -1], ![0, 0], ![0, 0]]

def raw7748step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-2, 2], ![1, -1], ![0, 0]]

def raw7748step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-2, 2], ![1, -1]]

def raw7748step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw7749 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1]]

def raw7749step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw7750 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1], ![-1, 1], ![0, 0], ![1, -1]]

def raw7750step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1], ![-1, 1], ![1, -1]]

def raw7750step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7751 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1], ![-1, 1], ![1, -1]]

def raw7751step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7752 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1], ![-1, 1], ![1, -1], ![0, 0]]

def raw7752step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1], ![-1, 1], ![1, -1]]

def raw7752step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7753 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1], ![0, 0]]

def raw7753step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1]]

def raw7753step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw7754 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1], ![0, 0], ![0, 0]]

def raw7754step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1], ![0, 0]]

def raw7754step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1]]

def raw7754step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw7755 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1], ![0, 0], ![0, 0], ![0, 0]]

def raw7755step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1], ![0, 0], ![0, 0]]

def raw7755step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1], ![0, 0]]

def raw7755step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1]]

def raw7755step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw7756 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1], ![1, -1], ![0, 0], ![-1, 1]]

def raw7756step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1], ![1, -1], ![-1, 1]]

def raw7756step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7757 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![0, 0], ![-1, 1]]

def raw7757step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1]]

def raw7757step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw7758 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![0, 0], ![0, 0], ![-1, 1]]

def raw7758step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![0, 0], ![-1, 1]]

def raw7758step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1]]

def raw7758step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw7759 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![1, -1], ![-2, 2], ![0, 0], ![0, 0]]

def raw7759step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![1, -1], ![-2, 2], ![0, 0]]

def raw7759step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![1, -1], ![-2, 2]]

def raw7759step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw7760 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![1, -1], ![-1, 1], ![-1, 1]]

def raw7760step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7761 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![3, -3], ![-1, 1], ![-1, 1]]

def raw7761step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

def raw7762 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -4, 4], ![0, 0, 2, -2], ![1, -1, 2, -2]]

def raw7762step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![-4, 2, 2], ![4, -2, -2]]

def raw7762step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![2, 2, -4]]

def raw7763 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![-1, 1, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw7764 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![-1, 1, 1, -1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, -1, 0, 0]]

def raw7764step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![-1, 1, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw7765 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![-1, 1, 1, -1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw7766 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![-1, 1, 1, -1], ![0, 0, 2, -2], ![2, -2, 0, 0]]

def raw7766step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![1, 1, 0, -2], ![-3, 1, 2, 0], ![3, -1, -2, 0]]

def raw7766step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -2, 1], ![2, 1, 0, -3]]

def raw7767 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![-1, 1, 1, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw7767step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, 1, -1, -1], ![-3, 1, 0, 2], ![3, -1, 0, -2]]

def raw7767step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, -2, 3], ![0, 1, 2, -3], ![1, -1, 1, -1]]

def raw7768 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![-1, 1, 1, -1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def raw7768step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, 1, -1, -1], ![-3, 1, 1, 1], ![3, -1, -1, -1]]

def raw7768step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, -1, 1, 1], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def raw7769 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![-1, 1, 1, -1], ![1, -1, 2, -2], ![1, -1, 0, 0]]

def raw7769step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, 1, -1, -1], ![-3, 1, 2, 0], ![3, -1, -2, 0]]

def raw7769step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, -2, 3], ![0, 1, 2, -3], ![1, -1, 1, -1]]

def raw7770 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![-1, 1, 2, -2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw7771 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![-1, 1, 2, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw7771step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, 1, -1, -1], ![-3, 2, 0, 1], ![3, -2, 0, -1]]

def raw7771step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 1, 2, -3], ![1, 1, -1, -1]]

def raw7772 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![-1, 1, 2, -2], ![1, -1, 1, -1], ![1, -1, 0, 0]]

def raw7772step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, 1, -1, -1], ![-3, 2, 1, 0], ![3, -2, -1, 0]]

def raw7772step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 1, 2, -3], ![1, 1, -1, -1]]

def raw7773 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![-1, 1, 3, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw7773step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, 1, -1, -1], ![-3, 3, 0, 0], ![3, -3, 0, 0]]

def raw7773step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -3, 3], ![0, 0, 3, -3], ![1, 1, -1, -1]]

def raw7774 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, -2, 3, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw7774step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, -2, 1, 0], ![-3, 3, 0, 0], ![3, -1, -1, -1]]

def raw7774step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw7775 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, -1, 2, -1], ![1, 0, 1, -2]]

def raw7775step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, -1, 0], ![-3, 2, 1], ![3, -1, -2]]

def raw7775step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical243
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7776 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, -1, 3, -2], ![1, 0, 0, -1]]

def raw7776step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, -1, 0], ![-3, 3, 0], ![3, -2, -1]]

def raw7776step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1]]

def raw7777 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw7778 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, 0, 0]]

def raw7778step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 0, -1], ![-3, 1, 2, 0], ![3, -1, -2, 0]]

def raw7778step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 0, 1], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def raw7779 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 2, -1]]

def raw7779step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-3, 1, 0, 2], ![3, -1, -1, -1]]

def raw7779step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 2, -3]]

def raw7780 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -2, 1, 0]]

def raw7780step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-3, 1, 1, 1], ![3, -1, -2, 0]]

def raw7780step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 1, 1, -3]]

def raw7781 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 0, 1, -1], ![1, -1, 2, -2]]

def raw7781step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![-3, 1, 2], ![3, -1, -2]]

def raw7781step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3]]

def raw7782 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw7782step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-3, 2, 0, 1], ![3, -2, -1, 0]]

def raw7782step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw7783 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 0, 2, -2], ![1, -1, 1, -1]]

def raw7783step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![-3, 2, 1], ![3, -2, -1]]

def raw7783step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![2, 1, -3]]

def raw7784 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 0, 3, -3], ![1, -1, 0, 0]]

def raw7784step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![-3, 3, 0], ![3, -3, 0]]

def raw7784step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 3, -3], ![1, 0, -1]]

def raw7785 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 0, 4, -4], ![1, -1, -1, 1]]

def raw7785step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![-3, 4, -1], ![3, -4, 1]]

def raw7785step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 3, -4]]

def raw7786 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 1, 1, -2], ![1, -2, 2, -1]]

def raw7786step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 1, -2], ![-3, 1, 2], ![3, -2, -1]]

def raw7786step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

def raw7787 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw7787step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 1, -2], ![-3, 2, 1], ![3, -3, 0]]

def raw7787step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 0, -1], ![1, 2, -3]]

def raw7788 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw7788step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 1, -2], ![-3, 3, 0], ![3, -4, 1]]

def raw7788step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, -1, 0], ![1, 3, -4]]

def raw7789 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw7790 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def raw7791 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw7792 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 2, -2], ![1, -1, 1, -1], ![1, -1, 0, 0]]

def raw7792step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw7793 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 2, -2], ![2, -2, 1, -1]]

def raw7793step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![1, 1, 0, -2], ![-2, -1, 2, 1], ![2, 1, -2, -1]]

def raw7793step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![2, -1, 1, -2]]

def raw7794 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 3, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw7795 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 3, -3], ![2, -2, 0, 0]]

def raw7795step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![1, 1, 0, -2], ![-2, -1, 3, 0], ![2, 1, -3, 0]]

def raw7795step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, -3, 2], ![2, -1, 0, -1]]

def raw7796 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw7796step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, 1, -1, -1], ![-2, -1, 0, 3], ![2, 1, 0, -3]]

def raw7796step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, -2, 3], ![0, 1, 2, -3], ![1, -1, -1, 1]]

def raw7797 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def raw7798 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![1, -1, 2, -2], ![1, -1, 1, -1]]

def raw7798step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def raw7799 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![1, -1, 3, -3], ![1, -1, 0, 0]]

def raw7799step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, 1, -1, -1], ![-2, -1, 3, 0], ![2, 1, -3, 0]]

def raw7799step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, -2, 3], ![0, 1, 2, -3], ![1, -1, -1, 1]]

def raw7800 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, 0, 0], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw7800step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw7801 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, 0, 0], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw7801step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw7802 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, 0, 0], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw7802step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, 1, -1, -1], ![-2, 0, 0, 2], ![2, 0, 0, -2]]

def raw7802step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, -1, 1, -1]]

def raw7803 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, 0, 0], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def raw7803step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, 1, -1, -1], ![-2, 0, 1, 1], ![2, 0, -1, -1]]

def raw7803step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, -1, -1, 1]]

def raw7804 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw7804step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw7805 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw7805step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, 1, -1, -1], ![-2, 1, 0, 1], ![2, -1, 0, -1]]

def raw7805step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw7806 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, 2, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw7806step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, 1, -1, -1], ![-2, 2, 0, 0], ![2, -2, 0, 0]]

def raw7806step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 1, -1, -1]]

def raw7807 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, 3, -3], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw7807step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, 1, -1, -1], ![-2, 3, -1, 0], ![2, -3, 1, 0]]

def raw7807step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 1, 2, -3], ![1, 1, -1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical244
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7808 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, -2, 0, 2], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def raw7808step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, -2, 1, 0], ![-2, 0, 3, -1], ![2, 2, -4, 0]]

def raw7808step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw7809 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, -2, 1, 1], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw7809step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 2, -2], ![0, 2, -1, -1], ![0, -1, -2, 3], ![-1, 0, 1, 0]]

def raw7809step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, -2, 2]]

def raw7810 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, -2, 3, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw7810step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, -2, 1, 0], ![-2, 3, 0, -1], ![2, -1, -1, 0]]

def raw7810step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw7811 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, -1, -1, 2], ![0, 0, 2, -2], ![1, 0, 1, -2]]

def raw7811step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 2, -2], ![0, 1, 1, -2], ![0, 0, -2, 2], ![-1, 0, -1, 2]]

def raw7811step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, -1, 2, -2]]

def raw7812 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw7812step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, -1, 1, -1], ![-2, -1, 3, 0], ![2, 2, -4, 0]]

def raw7812step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw7813 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, -1, -1, 1]]

def raw7814 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, -1, 2, -1], ![1, 0, 0, -1]]

def raw7814step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, -1, 0], ![-2, 2, 0], ![2, -1, -1]]

def raw7814step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

def raw7815 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, -1, 3, -2], ![1, 0, -1, 0]]

def raw7815step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, -1, 0], ![-2, 3, -1], ![2, -2, 0]]

def raw7815step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def raw7816 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -1, 1, -1]]

def raw7817 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 0, -1, 1], ![0, 0, 3, -3], ![1, -1, 0, 0]]

def raw7817step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 0, -1], ![-2, -1, 3, 0], ![2, 1, -3, 0]]

def raw7817step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def raw7818 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -2, 3, -2]]

def raw7818step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-2, -1, 0, 3], ![2, 1, -1, -2]]

def raw7818step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -1, 2, -2]]

def raw7819 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw7819step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-2, -1, 2, 1], ![2, 1, -3, 0]]

def raw7819step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, 0, -1, 2], ![2, 1, -2, -1], ![-2, -1, 3, 0]]

def raw7819step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, -1, 2, -2]]

def raw7820 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw7820step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-2, -1, 3, 0], ![2, 1, -4, 1]]

def raw7820step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, 0, -1, 2], ![2, 1, -3, 0], ![-2, -1, 4, -1]]

def raw7820step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, 2, -3]]

def raw7821 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0]]

def raw7821step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 0, -1], ![-2, 1, 1, 0], ![2, -1, -1, 0]]

def raw7821step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 1, 0, -2]]

def raw7822 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw7822step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-2, 1, 0, 1], ![2, -1, -1, 0]]

def raw7822step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 1, -2]]

def raw7823 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 0, 1, -1], ![1, -1, 1, -1]]

def raw7823step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![-2, 1, 1], ![2, -1, -1]]

def raw7823step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

def raw7824 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 0, 2, -2], ![1, -1, 0, 0]]

def raw7824step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![-2, 2, 0], ![2, -2, 0]]

def raw7824step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

def raw7825 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -2, 0, 1]]

def raw7825step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-2, 3, -1, 0], ![2, -3, 0, 1]]

def raw7825step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw7826 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -2, -1, 2]]

def raw7827 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 0, 3, -3], ![1, -1, -1, 1]]

def raw7827step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![-2, 3, -1], ![2, -3, 1]]

def raw7827step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3]]

def raw7828 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 1, 0, -1], ![1, -2, 2, -1]]

def raw7828step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 1, -2], ![-2, 0, 2], ![2, -1, -1]]

def raw7828step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1]]

def raw7829 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 1, 1, -2], ![1, -2, 1, 0]]

def raw7829step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 1, -2], ![-2, 1, 1], ![2, -2, 0]]

def raw7829step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw7830 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 1, 3, -4], ![1, -2, -1, 2]]

def raw7830step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 1, -2], ![-2, 3, -1], ![2, -4, 2]]

def raw7830step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, -1, 2], ![2, -3, 1], ![-2, 4, -2]]

def raw7830step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]

def raw7831 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![-1, 1, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw7831step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, -1, 1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw7832 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![-1, 1, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw7832step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def raw7833 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![-1, 1, -1, 1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw7833step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, 1, -1, -1], ![-1, -1, 0, 2], ![1, 1, 0, -2]]

def raw7833step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, -1, -1, 1]]

def raw7834 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![-1, 1, -1, 1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def raw7834step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, -1, 1, 1], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def raw7835 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -2, 3, -1], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw7835step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 1, -1], ![0, 2, -3, 1], ![0, -1, 2, -1], ![-1, 0, 0, 1]]

def raw7835step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -1, 2], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw7836 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, -2, 3], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw7837 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, -2, 3], ![1, 0, 3, -4]]

def raw7837step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, -1, 0], ![-1, -2, 3], ![1, 3, -4]]

def raw7837step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, 1, 0], ![1, 2, -3], ![-1, -3, 4]]

def raw7837step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3]]

def raw7838 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw7839 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw7839step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, 1, -3], ![1, 0, -1, 0]]

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

def raw7840 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def raw7841 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, 2, -1], ![1, 0, -1, 0]]

def raw7841step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0]]

def raw7841step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw7842 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, -1, 1, -1]]

def raw7843 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, -1, 0, 0]]

def raw7844 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -2, 3, -2]]

def raw7844step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-1, -2, 0, 3], ![1, 2, -1, -2]]

def raw7844step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, 0, -1, 2], ![1, 2, 0, -3], ![-1, -2, 1, 2]]

def raw7848 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![1, -1, 3, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end


