-- Prove2me | Definitions.Def_OAIQ106E143
-- name    : OAIQ106E143
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T18:30:23.02154+00:00
-- url     : https://prove2.me/theorems/b5f2a5cd-67f9-44a8-9b39-e3bafcb44150
-- title:
--   Definitions bundle OAIQ106E143 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 5533 declarations of OpenAI's Lean: 5533 definitions. The definitions and types are `OAI.MUB6.Certificate.PairSemantics.raw12step1`, `OAI.MUB6.Certificate.PairSemantics.raw13`, `OAI.MUB6.Certificate.PairSemantics.raw130`, `OAI.MUB6.Certificate.PairSemantics.raw1300`, `OAI.MUB6.Certificate.PairSemantics.raw1300step0`, `OAI.MUB6.Certificate.PairSemantics.raw1301`, `OAI.MUB6.Certificate.PairSemantics.raw1301step0`, `OAI.MUB6.Certificate.PairSemantics.raw1302`, `OAI.MUB6.Certificate.PairSemantics.raw1302step0`, `OAI.MUB6.Certificate.PairSemantics.raw1303`, `OAI.MUB6.Certificate.PairSemantics.raw1304`, `OAI.MUB6.Certificate.PairSemantics.raw1304step0`, `OAI.MUB6.Certificate.PairSemantics.raw1304step1`, `OAI.MUB6.Certificate.PairSemantics.raw1305`, `OAI.MUB6.Certificate.PairSemantics.raw1305step0`, `OAI.MUB6.Certificate.PairSemantics.raw1305step1`, `OAI.MUB6.Certificate.PairSemantics.raw1306`, `OAI.MUB6.Certificate.PairSemantics.raw1306step0`, `OAI.MUB6.Certificate.PairSemantics.raw1306step1`, `OAI.MUB6.Certificate.PairSemantics.raw1307`, `OAI.MUB6.Certificate.PairSemantics.raw1307step0`, `OAI.MUB6.Certificate.PairSemantics.raw1307step1`, `OAI.MUB6.Certificate.PairSemantics.raw1308`, `OAI.MUB6.Certificate.PairSemantics.raw1309`, `OAI.MUB6.Certificate.PairSemantics.raw1309step0`, `OAI.MUB6.Certificate.PairSemantics.raw1309step1`, `OAI.MUB6.Certificate.PairSemantics.raw130step0`, `OAI.MUB6.Certificate.PairSemantics.raw131`, `OAI.MUB6.Certificate.PairSemantics.raw1310`, `OAI.MUB6.Certificate.PairSemantics.raw1311`, `OAI.MUB6.Certificate.PairSemantics.raw1311step0`, `OAI.MUB6.Certificate.PairSemantics.raw1312`, `OAI.MUB6.Certificate.PairSemantics.raw1312step0`, `OAI.MUB6.Certificate.PairSemantics.raw1312step1`, `OAI.MUB6.Certificate.PairSemantics.raw1312step2`, `OAI.MUB6.Certificate.PairSemantics.raw1313`, `OAI.MUB6.Certificate.PairSemantics.raw1313step0`, `OAI.MUB6.Certificate.PairSemantics.raw1313step1`, `OAI.MUB6.Certificate.PairSemantics.raw1314`, `OAI.MUB6.Certificate.PairSemantics.raw1314step0` and 5493 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_PairSemantics_Canonical0`, `MutuallyUnbiased_PairSemantics_Canonical1`, `MutuallyUnbiased_PairSemantics_Canonical10`, `MutuallyUnbiased_PairSemantics_Canonical100`, `MutuallyUnbiased_PairSemantics_Canonical101`, `MutuallyUnbiased_PairSemantics_Canonical102`, `MutuallyUnbiased_PairSemantics_Canonical103`, `MutuallyUnbiased_PairSemantics_Canonical104`, `MutuallyUnbiased_PairSemantics_Canonical105`, `MutuallyUnbiased_PairSemantics_Canonical106`, `MutuallyUnbiased_PairSemantics_Canonical107`, `MutuallyUnbiased_PairSemantics_Canonical108`, `MutuallyUnbiased_PairSemantics_Canonical109`, `MutuallyUnbiased_PairSemantics_Canonical11`, `MutuallyUnbiased_PairSemantics_Canonical110`, `MutuallyUnbiased_PairSemantics_Canonical4`, `MutuallyUnbiased_PairSemantics_Canonical40`, `MutuallyUnbiased_PairSemantics_Canonical41`, `MutuallyUnbiased_PairSemantics_Canonical42`, `MutuallyUnbiased_PairSemantics_Canonical43`, `MutuallyUnbiased_PairSemantics_Canonical44`, `MutuallyUnbiased_PairSemantics_Canonical45`, `MutuallyUnbiased_PairSemantics_Canonical46`, `MutuallyUnbiased_PairSemantics_Canonical47`, `MutuallyUnbiased_PairSemantics_Canonical48`, `MutuallyUnbiased_PairSemantics_Canonical49`, `MutuallyUnbiased_PairSemantics_Canonical5`, `MutuallyUnbiased_PairSemantics_Canonical50`, `MutuallyUnbiased_PairSemantics_Canonical51`, `MutuallyUnbiased_PairSemantics_Canonical52`, `MutuallyUnbiased_PairSemantics_Canonical53`, `MutuallyUnbiased_PairSemantics_Canonical54`, `MutuallyUnbiased_PairSemantics_Canonical55`, `MutuallyUnbiased_PairSemantics_Canonical56`, `MutuallyUnbiased_PairSemantics_Canonical57`, `MutuallyUnbiased_PairSemantics_Canonical58`, `MutuallyUnbiased_PairSemantics_Canonical59`, `MutuallyUnbiased_PairSemantics_Canonical6`, `MutuallyUnbiased_PairSemantics_Canonical60`, `MutuallyUnbiased_PairSemantics_Canonical61`, `MutuallyUnbiased_PairSemantics_Canonical62`, `MutuallyUnbiased_PairSemantics_Canonical63`, `MutuallyUnbiased_PairSemantics_Canonical64`, `MutuallyUnbiased_PairSemantics_Canonical65`, `MutuallyUnbiased_PairSemantics_Canonical66`, `MutuallyUnbiased_PairSemantics_Canonical67`, `MutuallyUnbiased_PairSemantics_Canonical68`, `MutuallyUnbiased_PairSemantics_Canonical69`, `MutuallyUnbiased_PairSemantics_Canonical7`, `MutuallyUnbiased_PairSemantics_Canonical70`, `MutuallyUnbiased_PairSemantics_Canonical71`, `MutuallyUnbiased_PairSemantics_Canonical72`, `MutuallyUnbiased_PairSemantics_Canonical73`, `MutuallyUnbiased_PairSemantics_Canonical74`, `MutuallyUnbiased_PairSemantics_Canonical75`, `MutuallyUnbiased_PairSemantics_Canonical76`, `MutuallyUnbiased_PairSemantics_Canonical77`, `MutuallyUnbiased_PairSemantics_Canonical78`, `MutuallyUnbiased_PairSemantics_Canonical79`, `MutuallyUnbiased_PairSemantics_Canonical8`, `MutuallyUnbiased_PairSemantics_Canonical80`, `MutuallyUnbiased_PairSemantics_Canonical81`, `MutuallyUnbiased_PairSemantics_Canonical82`, `MutuallyUnbiased_PairSemantics_Canonical83`, `MutuallyUnbiased_PairSemantics_Canonical84`, `MutuallyUnbiased_PairSemantics_Canonical85`, `MutuallyUnbiased_PairSemantics_Canonical86`, `MutuallyUnbiased_PairSemantics_Canonical87`, `MutuallyUnbiased_PairSemantics_Canonical88`, `MutuallyUnbiased_PairSemantics_Canonical89`, `MutuallyUnbiased_PairSemantics_Canonical9`, `MutuallyUnbiased_PairSemantics_Canonical90`, `MutuallyUnbiased_PairSemantics_Canonical91`, `MutuallyUnbiased_PairSemantics_Canonical92`, `MutuallyUnbiased_PairSemantics_Canonical93`, `MutuallyUnbiased_PairSemantics_Canonical94`, `MutuallyUnbiased_PairSemantics_Canonical95`, `MutuallyUnbiased_PairSemantics_Canonical96`, `MutuallyUnbiased_PairSemantics_Canonical97`, `MutuallyUnbiased_PairSemantics_Canonical98`, `MutuallyUnbiased_PairSemantics_Canonical99`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1162_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1163_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1164_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1165_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1170_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1172_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1265_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1266_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1267_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1298_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1299_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1339_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1340_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1341_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1342_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1343_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1395_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1396_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1397_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1399_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1409_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1410_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1411_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1412_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1414_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1441_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1475_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1477_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1478_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2357_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2358_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2526_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2527_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2528_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2530_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2531_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2570_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2572_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2574_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2576_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2593_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2594_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2595_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2599_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2636_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2766_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2828_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2901_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2903_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2904_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2936_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2937_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2939_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2941_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2943_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2957_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2958_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2959_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2960_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2961_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2963_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2986_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2987_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2988_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2990_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2996_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2998_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3003_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3081_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3082_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3087_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3088_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3089_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3094_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3100_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3106_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3109_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3139_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3140_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3184_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3185_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3190_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3191_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3203_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3204_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3205_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3206_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3209_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3210_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3211_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3223_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3226_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3227_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3711_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3727_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3735_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3737_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3739_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3818_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3821_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3823_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3829_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3830_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3847_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3851_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3852_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3853_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3882_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3925_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3936_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3937_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3938_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3965_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3966_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3967_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3969_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3970_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3977_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3980_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3981_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3982_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3992_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4003_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4023_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4026_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4031_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4032_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4033_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5174_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5387_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5415_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5418_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5439_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5450_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5464_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5465_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound0_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound111_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound12_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound135_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound136_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound137_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound138_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound139_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound140_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound141_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound142_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound143_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound144_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound145_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound146_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound147_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound148_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound149_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound150_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound151_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound16_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound19_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound20_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound23_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound28_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound2_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound30_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound35_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound37_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound3_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound41_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound49_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound78_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound7_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1472_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero15_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1674_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1785_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1909_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero488_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero621_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero794_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero818_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound0_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1007_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1008_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound100_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1010_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1013_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1020_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1021_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1033_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1093_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1094_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1095_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1096_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1097_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1098_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound10_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1103_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1108_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound110_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1110_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1111_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1115_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1120_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1121_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1124_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1130_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1131_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound113_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound114_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1159_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound115_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1165_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1166_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1167_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound116_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1170_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1177_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1178_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1179_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1261_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1262_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1264_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1266_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1267_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1268_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1269_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound126_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1272_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1278_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1279_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound127_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1294_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1300_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1301_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1303_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1309_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound130_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1310_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1311_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1312_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1318_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1324_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound137_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound138_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound13_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1409_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound140_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1410_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1411_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1412_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1413_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1414_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1418_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1419_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound141_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1420_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1421_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1423_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1429_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1433_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1434_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1435_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1437_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound143_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1441_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1442_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1469_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1470_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1477_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1478_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1479_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1480_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1484_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1492_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1493_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1507_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1510_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1511_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1517_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1521_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound153_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1559_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1560_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1562_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1567_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1568_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1572_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound163_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1648_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1649_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1650_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1651_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1652_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1653_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1654_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1655_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1656_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1662_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1669_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1672_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1686_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound16_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1703_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1708_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1709_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1715_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1717_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1780_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1781_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1782_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1783_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1784_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1786_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1787_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1788_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1789_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1796_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound17_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1816_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1840_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1844_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1845_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1846_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1847_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1849_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1855_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1856_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1859_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1866_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1872_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1874_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound188_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1904_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1905_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1907_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1911_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1914_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1915_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1916_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1917_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1925_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1944_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1963_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1964_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1969_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1972_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1977_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1985_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound199_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2033_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2034_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2036_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2037_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2040_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2046_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2048_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2049_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2059_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2062_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2075_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2077_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound207_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound213_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound214_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2166_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2168_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2169_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2170_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2171_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2172_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2173_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2175_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2176_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2180_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2181_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2182_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2183_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2184_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2185_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2187_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2188_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2189_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2191_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2192_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2193_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2195_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2196_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2197_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2198_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2199_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2200_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2201_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2202_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2203_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2204_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2205_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2206_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2207_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2208_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2211_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2212_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2214_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2215_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2216_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2217_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2218_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2219_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2220_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2223_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2224_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2225_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2226_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2227_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2228_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2229_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2230_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2231_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2232_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2233_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2235_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2236_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2238_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2240_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2241_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2242_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2244_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2245_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2246_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2247_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2248_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2249_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2250_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2251_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2252_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2253_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2254_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2255_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2256_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2257_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2258_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2259_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2260_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2261_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2262_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2263_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2264_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2265_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2266_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2267_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2268_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound226_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2270_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2271_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2272_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2273_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2274_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2275_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2276_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2278_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2279_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2281_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2282_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2283_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2284_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2285_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2286_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2287_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2288_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2290_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2291_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2292_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2294_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2295_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2296_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2297_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2298_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2299_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound22_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2300_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2301_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2302_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2304_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2305_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2306_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2307_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2308_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2309_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2310_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2311_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2312_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2313_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2314_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2315_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2316_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2317_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2318_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2321_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2322_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2323_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2324_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2325_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2326_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2327_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2328_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2329_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2330_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2331_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2332_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2333_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2334_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2335_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2336_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2337_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2338_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2340_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2341_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2342_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2344_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2345_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2346_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2347_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2348_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2350_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2352_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2353_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2354_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2355_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2356_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2357_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2358_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2361_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2362_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2363_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2364_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2365_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2366_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2367_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2368_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2369_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound236_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2373_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2374_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2375_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2376_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2378_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2379_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2380_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2381_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2382_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2383_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2386_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2387_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2388_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2390_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2391_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2392_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2393_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2394_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2395_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2396_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2397_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2398_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2399_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2400_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2401_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2402_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2404_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2405_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2406_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2407_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2408_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2409_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2410_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2411_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2412_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2413_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2414_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2415_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2416_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2418_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2419_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2421_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2422_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2423_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2424_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound244_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound245_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound24_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound255_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound267_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound269_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound281_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound282_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound286_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound287_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound296_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound301_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound310_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound311_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound319_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound327_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound335_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound339_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound340_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound341_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound342_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound343_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound344_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound345_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound353_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound354_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound355_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound356_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound357_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound358_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound359_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound365_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound366_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound367_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound368_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound369_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound370_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound380_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound388_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound391_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound392_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound395_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound3_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound404_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound411_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound412_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound413_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound418_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound419_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound427_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound428_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound438_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound444_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound445_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound447_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound448_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound452_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound453_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound454_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound456_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound462_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound463_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound470_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound474_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound481_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound482_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound483_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound484_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound485_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound497_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound498_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound499_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound4_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound500_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound501_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound504_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound514_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound515_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound516_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound518_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound519_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound521_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound524_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound525_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound526_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound531_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound532_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound533_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound534_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound537_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound538_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound539_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound540_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound541_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound542_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound543_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound545_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound546_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound547_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound548_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound551_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound553_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound554_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound555_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound558_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound566_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound567_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound568_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound570_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound571_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound580_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound581_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound582_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound584_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound585_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound587_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound588_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound58_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound599_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound5_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound600_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound613_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound614_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound628_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound629_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound630_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound631_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound633_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound636_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound643_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound644_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound649_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound656_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound657_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound658_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound659_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound663_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound664_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound667_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound668_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound675_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound683_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound688_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound694_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound6_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound700_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound711_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound712_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound717_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound718_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound719_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound720_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound722_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound730_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound731_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound732_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound733_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound734_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound735_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound736_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound737_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound740_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound741_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound742_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound743_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound751_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound758_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound759_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound769_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound76_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound779_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound780_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound786_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound787_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound788_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound789_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound790_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound792_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound793_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound796_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound798_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound799_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound7_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound800_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound801_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound802_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound804_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound805_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound813_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound815_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound817_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound822_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound823_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound841_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound842_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound844_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound847_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound852_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound853_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound858_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound859_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound863_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound864_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound865_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound866_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound867_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound868_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound872_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound873_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound877_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound881_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound883_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound884_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound885_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound887_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound888_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound891_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound894_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound897_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound898_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound899_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound902_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound906_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound909_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound911_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound917_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound91_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound922_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound923_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound925_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound929_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound92_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound932_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound933_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound940_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound947_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound94_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound950_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound959_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound962_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound964_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound966_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound973_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound975_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound981_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound983_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound987_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound9_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval100_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval105_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1075_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval108_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval111_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval113_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval117_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval118_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1194_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval122_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval126_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval12_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1315_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval131_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval136_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval137_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval141_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval143_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1465_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval151_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1523_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval152_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1554_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1555_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval155_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval164_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval165_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval169_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval174_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval175_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval181_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval185_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval18_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval190_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval201_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval202_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval211_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval212_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval217_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval21_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval220_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval224_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval226_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval229_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval232_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval234_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval235_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval242_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval246_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval250_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval256_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval260_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval264_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval266_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval268_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval269_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval275_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval280_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval285_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval286_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval287_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval289_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval296_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval301_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval308_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval310_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval316_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval325_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval332_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval335_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval338_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval339_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval341_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval343_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval351_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval352_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval356_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval357_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval358_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval359_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval366_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval369_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval372_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval378_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval37_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval382_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval383_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval385_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval390_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval398_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval39_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval405_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval408_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval413_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval46_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval476_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval53_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval55_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval56_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval63_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval69_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval73_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval74_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval79_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval84_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval86_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval8_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval92_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval957_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval145_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval147_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval150_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval215_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval216_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval219_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval21_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval220_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval223_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval238_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval373_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval375_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval44_e`, `OAI.MUB6.Certificate.PairSemantics.boundarySound26_e`, `OAI.MUB6.Certificate.PairSemantics.boundarySound49_e`, `OAI.MUB6.Certificate.PairSemantics.boundarySound58_e`, `OAI.MUB6.Certificate.PairSemantics.boundarySound73_e`, `OAI.MUB6.Certificate.PairSemantics.sound1379_e`, `OAI.MUB6.Certificate.PairSemantics.sound1381_e`, `OAI.MUB6.Certificate.PairSemantics.sound1383_e`, `OAI.MUB6.Certificate.PairSemantics.sound1384_e`, `OAI.MUB6.Certificate.PairSemantics.sound1387_e`, `OAI.MUB6.Certificate.PairSemantics.sound1390_e`, `OAI.MUB6.Certificate.PairSemantics.sound1391_e`, `OAI.MUB6.Certificate.PairSemantics.sound1395_e`, `OAI.MUB6.Certificate.PairSemantics.sound1399_e`, `OAI.MUB6.Certificate.PairSemantics.sound1414_e`, `OAI.MUB6.Certificate.PairSemantics.sound1419_e`, `OAI.MUB6.Certificate.PairSemantics.sound1423_e`, `OAI.MUB6.Certificate.PairSemantics.sound1424_e`, `OAI.MUB6.Certificate.PairSemantics.sound1425_e`, `OAI.MUB6.Certificate.PairSemantics.sound1434_e`, `OAI.MUB6.Certificate.PairSemantics.sound1437_e`, `OAI.MUB6.Certificate.PairSemantics.sound1443_e`, `OAI.MUB6.Certificate.PairSemantics.sound1458_e`, `OAI.MUB6.Certificate.PairSemantics.sound1486_e`, `OAI.MUB6.Certificate.PairSemantics.sound1504_e`, `OAI.MUB6.Certificate.PairSemantics.sound1506_e`, `OAI.MUB6.Certificate.PairSemantics.sound1512_e`, `OAI.MUB6.Certificate.PairSemantics.sound1518_e`, `OAI.MUB6.Certificate.PairSemantics.sound1529_e`, `OAI.MUB6.Certificate.PairSemantics.sound1530_e`, `OAI.MUB6.Certificate.PairSemantics.sound1531_e`, `OAI.MUB6.Certificate.PairSemantics.sound1535_e`, `OAI.MUB6.Certificate.PairSemantics.sound1540_e`, `OAI.MUB6.Certificate.PairSemantics.sound1548_e`, `OAI.MUB6.Certificate.PairSemantics.sound1605_e`, `OAI.MUB6.Certificate.PairSemantics.sound1614_e`, `OAI.MUB6.Certificate.PairSemantics.sound1617_e`, `OAI.MUB6.Certificate.PairSemantics.sound1624_e`, `OAI.MUB6.Certificate.PairSemantics.sound1627_e`, `OAI.MUB6.Certificate.PairSemantics.sound1628_e`, `OAI.MUB6.Certificate.PairSemantics.sound1631_e`, `OAI.MUB6.Certificate.PairSemantics.sound1634_e`, `OAI.MUB6.Certificate.PairSemantics.sound1635_e`, `OAI.MUB6.Certificate.PairSemantics.sound1637_e`, `OAI.MUB6.Certificate.PairSemantics.sound1644_e`, `OAI.MUB6.Certificate.PairSemantics.sound1646_e`, `OAI.MUB6.Certificate.PairSemantics.sound1648_e`, `OAI.MUB6.Certificate.PairSemantics.sound1685_e`, `OAI.MUB6.Certificate.PairSemantics.sound1716_e`, `OAI.MUB6.Certificate.PairSemantics.sound1736_e`, `OAI.MUB6.Certificate.PairSemantics.sound1739_e`, `OAI.MUB6.Certificate.PairSemantics.sound1768_e`, `OAI.MUB6.Certificate.PairSemantics.sound1770_e`, `OAI.MUB6.Certificate.PairSemantics.sound1793_e`, `OAI.MUB6.Certificate.PairSemantics.sound1800_e`, `OAI.MUB6.Certificate.PairSemantics.sound1828_e`, `OAI.MUB6.Certificate.PairSemantics.sound1849_e`, `OAI.MUB6.Certificate.PairSemantics.sound1858_e`, `OAI.MUB6.Certificate.PairSemantics.sound1860_e`, `OAI.MUB6.Certificate.PairSemantics.sound1865_e`, `OAI.MUB6.Certificate.PairSemantics.sound1866_e`, `OAI.MUB6.Certificate.PairSemantics.sound1867_e`, `OAI.MUB6.Certificate.PairSemantics.sound1869_e`, `OAI.MUB6.Certificate.PairSemantics.sound1870_e`, `OAI.MUB6.Certificate.PairSemantics.sound1872_e`, `OAI.MUB6.Certificate.PairSemantics.sound1875_e`, `OAI.MUB6.Certificate.PairSemantics.sound1876_e`, `OAI.MUB6.Certificate.PairSemantics.sound1879_e`, `OAI.MUB6.Certificate.PairSemantics.sound1885_e`, `OAI.MUB6.Certificate.PairSemantics.sound1978_e`, `OAI.MUB6.Certificate.PairSemantics.sound1980_e`, `OAI.MUB6.Certificate.PairSemantics.sound1986_e`, `OAI.MUB6.Certificate.PairSemantics.sound1987_e`, `OAI.MUB6.Certificate.PairSemantics.sound2041_e`, `OAI.MUB6.Certificate.PairSemantics.sound2058_e`, `OAI.MUB6.Certificate.PairSemantics.sound2071_e`, `OAI.MUB6.Certificate.PairSemantics.sound2097_e`, `OAI.MUB6.Certificate.PairSemantics.sound2106_e`, `OAI.MUB6.Certificate.PairSemantics.sound2107_e`, `OAI.MUB6.Certificate.PairSemantics.sound2108_e`, `OAI.MUB6.Certificate.PairSemantics.sound2117_e`, `OAI.MUB6.Certificate.PairSemantics.sound2122_e`, `OAI.MUB6.Certificate.PairSemantics.sound2123_e`, `OAI.MUB6.Certificate.PairSemantics.sound2128_e`, `OAI.MUB6.Certificate.PairSemantics.sound2132_e`, `OAI.MUB6.Certificate.PairSemantics.sound2152_e`, `OAI.MUB6.Certificate.PairSemantics.sound2168_e`, `OAI.MUB6.Certificate.PairSemantics.sound2175_e`, `OAI.MUB6.Certificate.PairSemantics.sound2177_e`, `OAI.MUB6.Certificate.PairSemantics.sound2189_e`, `OAI.MUB6.Certificate.PairSemantics.sound2190_e`, `OAI.MUB6.Certificate.PairSemantics.sound2197_e`, `OAI.MUB6.Certificate.PairSemantics.sound2201_e`, `OAI.MUB6.Certificate.PairSemantics.sound2202_e`, `OAI.MUB6.Certificate.PairSemantics.sound2213_e`, `OAI.MUB6.Certificate.PairSemantics.sound2228_e`, `OAI.MUB6.Certificate.PairSemantics.sound2244_e`, `OAI.MUB6.Certificate.PairSemantics.sound2262_e`, `OAI.MUB6.Certificate.PairSemantics.sound2284_e`, `OAI.MUB6.Certificate.PairSemantics.sound2286_e`, `OAI.MUB6.Certificate.PairSemantics.sound2293_e`, `OAI.MUB6.Certificate.PairSemantics.sound2294_e`, `OAI.MUB6.Certificate.PairSemantics.sound2295_e`, `OAI.MUB6.Certificate.PairSemantics.sound2296_e`, `OAI.MUB6.Certificate.PairSemantics.sound2312_e`, `OAI.MUB6.Certificate.PairSemantics.sound2324_e`, `OAI.MUB6.Certificate.PairSemantics.sound2327_e`, `OAI.MUB6.Certificate.PairSemantics.sound2338_e`, `OAI.MUB6.Certificate.PairSemantics.sound2375_e`, `OAI.MUB6.Certificate.PairSemantics.sound2382_e`, `OAI.MUB6.Certificate.PairSemantics.sound2390_e`, `OAI.MUB6.Certificate.PairSemantics.sound2391_e`, `OAI.MUB6.Certificate.PairSemantics.sound2394_e`, `OAI.MUB6.Certificate.PairSemantics.sound2399_e`, `OAI.MUB6.Certificate.PairSemantics.sound2400_e`, `OAI.MUB6.Certificate.PairSemantics.sound2401_e`, `OAI.MUB6.Certificate.PairSemantics.sound2403_e`, `OAI.MUB6.Certificate.PairSemantics.sound2415_e`, `OAI.MUB6.Certificate.PairSemantics.sound2416_e`, `OAI.MUB6.Certificate.PairSemantics.sound2420_e`, `OAI.MUB6.Certificate.PairSemantics.sound2433_e`, `OAI.MUB6.Certificate.PairSemantics.sound2434_e`, `OAI.MUB6.Certificate.PairSemantics.sound2435_e`, `OAI.MUB6.Certificate.PairSemantics.sound2436_e`, `OAI.MUB6.Certificate.PairSemantics.sound2442_e`, `OAI.MUB6.Certificate.PairSemantics.sound2444_e`, `OAI.MUB6.Certificate.PairSemantics.sound2445_e`, `OAI.MUB6.Certificate.PairSemantics.sound2454_e`, `OAI.MUB6.Certificate.PairSemantics.sound2456_e`, `OAI.MUB6.Certificate.PairSemantics.sound2457_e`, `OAI.MUB6.Certificate.PairSemantics.sound2463_e`, `OAI.MUB6.Certificate.PairSemantics.sound2464_e`, `OAI.MUB6.Certificate.PairSemantics.sound2465_e`, `OAI.MUB6.Certificate.PairSemantics.sound2472_e`, `OAI.MUB6.Certificate.PairSemantics.sound2473_e`, `OAI.MUB6.Certificate.PairSemantics.sound2477_e`, `OAI.MUB6.Certificate.PairSemantics.sound2479_e`, `OAI.MUB6.Certificate.PairSemantics.sound2489_e`, `OAI.MUB6.Certificate.PairSemantics.sound2490_e`, `OAI.MUB6.Certificate.PairSemantics.sound2491_e`, `OAI.MUB6.Certificate.PairSemantics.sound2492_e`, `OAI.MUB6.Certificate.PairSemantics.sound2507_e`, `OAI.MUB6.Certificate.PairSemantics.sound2520_e`, `OAI.MUB6.Certificate.PairSemantics.sound2521_e`, `OAI.MUB6.Certificate.PairSemantics.sound2522_e`, `OAI.MUB6.Certificate.PairSemantics.sound2524_e`, `OAI.MUB6.Certificate.PairSemantics.sound2525_e`, `OAI.MUB6.Certificate.PairSemantics.sound2527_e`, `OAI.MUB6.Certificate.PairSemantics.sound2533_e`, `OAI.MUB6.Certificate.PairSemantics.sound2540_e`, `OAI.MUB6.Certificate.PairSemantics.sound2546_e`, `OAI.MUB6.Certificate.PairSemantics.sound2547_e`, `OAI.MUB6.Certificate.PairSemantics.sound2548_e`, `OAI.MUB6.Certificate.PairSemantics.sound2557_e`, `OAI.MUB6.Certificate.PairSemantics.sound2558_e`, `OAI.MUB6.Certificate.PairSemantics.sound2559_e`, `OAI.MUB6.Certificate.PairSemantics.sound2564_e`, `OAI.MUB6.Certificate.PairSemantics.sound2565_e`, `OAI.MUB6.Certificate.PairSemantics.sound2566_e`, `OAI.MUB6.Certificate.PairSemantics.sound2573_e`, `OAI.MUB6.Certificate.PairSemantics.sound2578_e`, `OAI.MUB6.Certificate.PairSemantics.sound2580_e`, `OAI.MUB6.Certificate.PairSemantics.sound2593_e`, `OAI.MUB6.Certificate.PairSemantics.sound2602_e`, `OAI.MUB6.Certificate.PairSemantics.sound2604_e`, `OAI.MUB6.Certificate.PairSemantics.sound2606_e`, `OAI.MUB6.Certificate.PairSemantics.sound2619_e`, `OAI.MUB6.Certificate.PairSemantics.sound2620_e`, `OAI.MUB6.Certificate.PairSemantics.sound2623_e`, `OAI.MUB6.Certificate.PairSemantics.sound2627_e`, `OAI.MUB6.Certificate.PairSemantics.sound2641_e`, `OAI.MUB6.Certificate.PairSemantics.sound2657_e`, `OAI.MUB6.Certificate.PairSemantics.sound2658_e`, `OAI.MUB6.Certificate.PairSemantics.sound2661_e`, `OAI.MUB6.Certificate.PairSemantics.sound2666_e`, `OAI.MUB6.Certificate.PairSemantics.sound2669_e`, `OAI.MUB6.Certificate.PairSemantics.sound2670_e`, `OAI.MUB6.Certificate.PairSemantics.sound2671_e`, `OAI.MUB6.Certificate.PairSemantics.sound2686_e`, `OAI.MUB6.Certificate.PairSemantics.sound2690_e`, `OAI.MUB6.Certificate.PairSemantics.sound2693_e`, `OAI.MUB6.Certificate.PairSemantics.sound2698_e`, `OAI.MUB6.Certificate.PairSemantics.sound2710_e`, `OAI.MUB6.Certificate.PairSemantics.sound2714_e`, `OAI.MUB6.Certificate.PairSemantics.sound2729_e`, `OAI.MUB6.Certificate.PairSemantics.sound2732_e`, `OAI.MUB6.Certificate.PairSemantics.sound2733_e`, `OAI.MUB6.Certificate.PairSemantics.sound2735_e`, `OAI.MUB6.Certificate.PairSemantics.sound2754_e`, `OAI.MUB6.Certificate.PairSemantics.sound2757_e`, `OAI.MUB6.Certificate.PairSemantics.sound2788_e`, `OAI.MUB6.Certificate.PairSemantics.sound2790_e`, `OAI.MUB6.Certificate.PairSemantics.sound2793_e`, `OAI.MUB6.Certificate.PairSemantics.sound2807_e`, `OAI.MUB6.Certificate.PairSemantics.sound2817_e`, `OAI.MUB6.Certificate.PairSemantics.sound2829_e`, `OAI.MUB6.Certificate.PairSemantics.sound2836_e`, `OAI.MUB6.Certificate.PairSemantics.sound2845_e`, `OAI.MUB6.Certificate.PairSemantics.sound2853_e`, `OAI.MUB6.Certificate.PairSemantics.sound2854_e`, `OAI.MUB6.Certificate.PairSemantics.sound2858_e`, `OAI.MUB6.Certificate.PairSemantics.sound2863_e`, `OAI.MUB6.Certificate.PairSemantics.sound2864_e`, `OAI.MUB6.Certificate.PairSemantics.sound2865_e`, `OAI.MUB6.Certificate.PairSemantics.sound2866_e`, `OAI.MUB6.Certificate.PairSemantics.sound2867_e`, `OAI.MUB6.Certificate.PairSemantics.sound2868_e`, `OAI.MUB6.Certificate.PairSemantics.sound2872_e`, `OAI.MUB6.Certificate.PairSemantics.sound2873_e`, `OAI.MUB6.Certificate.PairSemantics.sound2874_e`, `OAI.MUB6.Certificate.PairSemantics.sound2875_e`, `OAI.MUB6.Certificate.PairSemantics.sound2878_e`, `OAI.MUB6.Certificate.PairSemantics.sound2879_e`, `OAI.MUB6.Certificate.PairSemantics.sound2880_e`, `OAI.MUB6.Certificate.PairSemantics.sound2882_e`, `OAI.MUB6.Certificate.PairSemantics.sound2883_e`, `OAI.MUB6.Certificate.PairSemantics.sound2884_e`, `OAI.MUB6.Certificate.PairSemantics.sound2887_e`, `OAI.MUB6.Certificate.PairSemantics.sound2888_e`, `OAI.MUB6.Certificate.PairSemantics.sound2889_e`, `OAI.MUB6.Certificate.PairSemantics.sound2890_e`, `OAI.MUB6.Certificate.PairSemantics.sound2891_e`, `OAI.MUB6.Certificate.PairSemantics.sound2892_e`, `OAI.MUB6.Certificate.PairSemantics.sound2894_e`, `OAI.MUB6.Certificate.PairSemantics.sound2895_e`, `OAI.MUB6.Certificate.PairSemantics.sound2896_e`, `OAI.MUB6.Certificate.PairSemantics.sound2897_e`, `OAI.MUB6.Certificate.PairSemantics.sound2898_e`, `OAI.MUB6.Certificate.PairSemantics.sound2899_e`, `OAI.MUB6.Certificate.PairSemantics.sound2900_e`, `OAI.MUB6.Certificate.PairSemantics.sound2901_e`, `OAI.MUB6.Certificate.PairSemantics.sound2902_e`, `OAI.MUB6.Certificate.PairSemantics.sound2904_e`, `OAI.MUB6.Certificate.PairSemantics.sound2905_e`, `OAI.MUB6.Certificate.PairSemantics.sound2906_e`, `OAI.MUB6.Certificate.PairSemantics.sound2908_e`, `OAI.MUB6.Certificate.PairSemantics.sound2909_e`, `OAI.MUB6.Certificate.PairSemantics.sound2910_e`, `OAI.MUB6.Certificate.PairSemantics.sound2912_e`, `OAI.MUB6.Certificate.PairSemantics.sound2913_e`, `OAI.MUB6.Certificate.PairSemantics.sound2914_e`, `OAI.MUB6.Certificate.PairSemantics.sound2915_e`, `OAI.MUB6.Certificate.PairSemantics.sound2916_e`, `OAI.MUB6.Certificate.PairSemantics.sound2917_e`, `OAI.MUB6.Certificate.PairSemantics.sound2919_e`, `OAI.MUB6.Certificate.PairSemantics.sound2920_e`, `OAI.MUB6.Certificate.PairSemantics.sound2922_e`, `OAI.MUB6.Certificate.PairSemantics.sound2924_e`, `OAI.MUB6.Certificate.PairSemantics.sound2925_e`, `OAI.MUB6.Certificate.PairSemantics.sound2926_e`, `OAI.MUB6.Certificate.PairSemantics.sound2927_e`, `OAI.MUB6.Certificate.PairSemantics.sound2928_e`, `OAI.MUB6.Certificate.PairSemantics.sound2929_e`, `OAI.MUB6.Certificate.PairSemantics.sound2931_e`, `OAI.MUB6.Certificate.PairSemantics.sound2933_e`, `OAI.MUB6.Certificate.PairSemantics.sound2935_e`, `OAI.MUB6.Certificate.PairSemantics.sound2936_e`, `OAI.MUB6.Certificate.PairSemantics.sound2939_e`, `OAI.MUB6.Certificate.PairSemantics.sound2940_e`, `OAI.MUB6.Certificate.PairSemantics.sound2941_e`, `OAI.MUB6.Certificate.PairSemantics.sound2942_e`, `OAI.MUB6.Certificate.PairSemantics.sound2943_e`, `OAI.MUB6.Certificate.PairSemantics.sound2944_e`, `OAI.MUB6.Certificate.PairSemantics.sound2946_e`, `OAI.MUB6.Certificate.PairSemantics.sound2949_e`, `OAI.MUB6.Certificate.PairSemantics.sound2950_e`, `OAI.MUB6.Certificate.PairSemantics.sound2951_e`, `OAI.MUB6.Certificate.PairSemantics.sound2952_e`, `OAI.MUB6.Certificate.PairSemantics.sound2953_e`, `OAI.MUB6.Certificate.PairSemantics.sound2954_e`, `OAI.MUB6.Certificate.PairSemantics.sound2956_e`, `OAI.MUB6.Certificate.PairSemantics.sound2957_e`, `OAI.MUB6.Certificate.PairSemantics.sound2959_e`, `OAI.MUB6.Certificate.PairSemantics.sound2960_e`, `OAI.MUB6.Certificate.PairSemantics.sound2961_e`, `OAI.MUB6.Certificate.PairSemantics.sound2962_e`, `OAI.MUB6.Certificate.PairSemantics.sound2963_e`, `OAI.MUB6.Certificate.PairSemantics.sound2964_e`, `OAI.MUB6.Certificate.PairSemantics.sound2965_e`, `OAI.MUB6.Certificate.PairSemantics.sound2966_e`, `OAI.MUB6.Certificate.PairSemantics.sound2967_e`, `OAI.MUB6.Certificate.PairSemantics.sound2968_e`, `OAI.MUB6.Certificate.PairSemantics.sound2969_e`, `OAI.MUB6.Certificate.PairSemantics.sound2970_e`, `OAI.MUB6.Certificate.PairSemantics.sound2972_e`, `OAI.MUB6.Certificate.PairSemantics.sound2973_e`, `OAI.MUB6.Certificate.PairSemantics.sound2974_e`, `OAI.MUB6.Certificate.PairSemantics.sound2975_e`, `OAI.MUB6.Certificate.PairSemantics.sound2976_e`, `OAI.MUB6.Certificate.PairSemantics.sound2977_e`, `OAI.MUB6.Certificate.PairSemantics.sound2979_e`, `OAI.MUB6.Certificate.PairSemantics.sound2980_e`, `OAI.MUB6.Certificate.PairSemantics.sound2984_e`, `OAI.MUB6.Certificate.PairSemantics.sound2985_e`, `OAI.MUB6.Certificate.PairSemantics.sound2986_e`, `OAI.MUB6.Certificate.PairSemantics.sound2987_e`, `OAI.MUB6.Certificate.PairSemantics.sound2989_e`, `OAI.MUB6.Certificate.PairSemantics.sound2990_e`, `OAI.MUB6.Certificate.PairSemantics.sound2991_e`, `OAI.MUB6.Certificate.PairSemantics.sound2992_e`, `OAI.MUB6.Certificate.PairSemantics.sound2994_e`, `OAI.MUB6.Certificate.PairSemantics.sound2996_e`, `OAI.MUB6.Certificate.PairSemantics.sound2997_e`, `OAI.MUB6.Certificate.PairSemantics.sound2998_e`, `OAI.MUB6.Certificate.PairSemantics.sound2999_e`, `OAI.MUB6.Certificate.PairSemantics.sound3000_e`, `OAI.MUB6.Certificate.PairSemantics.sound3001_e`, `OAI.MUB6.Certificate.PairSemantics.sound3002_e`, `OAI.MUB6.Certificate.PairSemantics.sound3004_e`, `OAI.MUB6.Certificate.PairSemantics.sound3006_e`, `OAI.MUB6.Certificate.PairSemantics.sound3007_e`, `OAI.MUB6.Certificate.PairSemantics.sound3009_e`, `OAI.MUB6.Certificate.PairSemantics.sound3011_e`, `OAI.MUB6.Certificate.PairSemantics.sound3012_e`, `OAI.MUB6.Certificate.PairSemantics.sound3013_e`, `OAI.MUB6.Certificate.PairSemantics.sound3014_e`, `OAI.MUB6.Certificate.PairSemantics.sound3015_e`, `OAI.MUB6.Certificate.PairSemantics.sound3016_e`, `OAI.MUB6.Certificate.PairSemantics.sound3017_e`, `OAI.MUB6.Certificate.PairSemantics.sound3018_e`, `OAI.MUB6.Certificate.PairSemantics.sound3019_e`, `OAI.MUB6.Certificate.PairSemantics.sound3020_e`, `OAI.MUB6.Certificate.PairSemantics.sound3021_e`, `OAI.MUB6.Certificate.PairSemantics.sound3022_e`, `OAI.MUB6.Certificate.PairSemantics.sound3023_e`, `OAI.MUB6.Certificate.PairSemantics.sound3024_e`, `OAI.MUB6.Certificate.PairSemantics.sound3025_e`, `OAI.MUB6.Certificate.PairSemantics.sound3026_e`, `OAI.MUB6.Certificate.PairSemantics.sound3027_e`, `OAI.MUB6.Certificate.PairSemantics.sound3028_e`, `OAI.MUB6.Certificate.PairSemantics.sound3029_e`, `OAI.MUB6.Certificate.PairSemantics.sound3030_e`, `OAI.MUB6.Certificate.PairSemantics.sound3032_e`, `OAI.MUB6.Certificate.PairSemantics.sound3034_e`, `OAI.MUB6.Certificate.PairSemantics.sound3035_e`, `OAI.MUB6.Certificate.PairSemantics.sound3036_e`, `OAI.MUB6.Certificate.PairSemantics.sound3037_e`, `OAI.MUB6.Certificate.PairSemantics.sound3038_e`, `OAI.MUB6.Certificate.PairSemantics.sound3039_e`, `OAI.MUB6.Certificate.PairSemantics.sound3040_e`, `OAI.MUB6.Certificate.PairSemantics.sound3041_e`, `OAI.MUB6.Certificate.PairSemantics.sound3042_e`, `OAI.MUB6.Certificate.PairSemantics.sound3045_e`, `OAI.MUB6.Certificate.PairSemantics.sound3049_e`, `OAI.MUB6.Certificate.PairSemantics.sound3050_e`, `OAI.MUB6.Certificate.PairSemantics.sound3051_e`, `OAI.MUB6.Certificate.PairSemantics.sound3052_e`, `OAI.MUB6.Certificate.PairSemantics.sound3053_e`, `OAI.MUB6.Certificate.PairSemantics.sound3054_e`, `OAI.MUB6.Certificate.PairSemantics.sound3055_e`, `OAI.MUB6.Certificate.PairSemantics.sound3057_e`, `OAI.MUB6.Certificate.PairSemantics.sound3059_e`, `OAI.MUB6.Certificate.PairSemantics.sound3060_e`, `OAI.MUB6.Certificate.PairSemantics.sound3061_e`, `OAI.MUB6.Certificate.PairSemantics.sound3062_e`, `OAI.MUB6.Certificate.PairSemantics.sound3063_e`, `OAI.MUB6.Certificate.PairSemantics.sound3065_e`, `OAI.MUB6.Certificate.PairSemantics.sound3066_e`, `OAI.MUB6.Certificate.PairSemantics.sound3067_e`, `OAI.MUB6.Certificate.PairSemantics.sound3068_e`, `OAI.MUB6.Certificate.PairSemantics.sound3069_e`, `OAI.MUB6.Certificate.PairSemantics.sound3071_e`, `OAI.MUB6.Certificate.PairSemantics.sound3072_e`, `OAI.MUB6.Certificate.PairSemantics.sound3073_e`, `OAI.MUB6.Certificate.PairSemantics.sound3074_e`, `OAI.MUB6.Certificate.PairSemantics.sound3075_e`, `OAI.MUB6.Certificate.PairSemantics.sound3076_e`, `OAI.MUB6.Certificate.PairSemantics.sound3077_e`, `OAI.MUB6.Certificate.PairSemantics.sound3078_e`, `OAI.MUB6.Certificate.PairSemantics.sound3079_e`, `OAI.MUB6.Certificate.PairSemantics.sound3081_e`, `OAI.MUB6.Certificate.PairSemantics.sound3082_e`, `OAI.MUB6.Certificate.PairSemantics.sound3084_e`, `OAI.MUB6.Certificate.PairSemantics.sound3085_e`, `OAI.MUB6.Certificate.PairSemantics.sound3086_e`, `OAI.MUB6.Certificate.PairSemantics.sound3087_e`, `OAI.MUB6.Certificate.PairSemantics.sound3088_e`, `OAI.MUB6.Certificate.PairSemantics.sound3090_e`, `OAI.MUB6.Certificate.PairSemantics.sound3091_e`, `OAI.MUB6.Certificate.PairSemantics.sound3092_e`, `OAI.MUB6.Certificate.PairSemantics.sound3093_e`, `OAI.MUB6.Certificate.PairSemantics.sound3094_e`, `OAI.MUB6.Certificate.PairSemantics.sound3095_e`, `OAI.MUB6.Certificate.PairSemantics.sound3096_e`, `OAI.MUB6.Certificate.PairSemantics.sound3098_e`, `OAI.MUB6.Certificate.PairSemantics.sound3099_e`, `OAI.MUB6.Certificate.PairSemantics.sound3100_e`, `OAI.MUB6.Certificate.PairSemantics.sound3101_e`, `OAI.MUB6.Certificate.PairSemantics.sound3105_e`, `OAI.MUB6.Certificate.PairSemantics.sound3106_e`, `OAI.MUB6.Certificate.PairSemantics.sound3107_e`, `OAI.MUB6.Certificate.PairSemantics.sound3108_e`, `OAI.MUB6.Certificate.PairSemantics.sound3110_e`, `OAI.MUB6.Certificate.PairSemantics.sound3111_e`, `OAI.MUB6.Certificate.PairSemantics.sound3112_e`, `OAI.MUB6.Certificate.PairSemantics.sound3113_e`, `OAI.MUB6.Certificate.PairSemantics.sound3114_e`, `OAI.MUB6.Certificate.PairSemantics.sound3115_e`, `OAI.MUB6.Certificate.PairSemantics.sound3118_e`, `OAI.MUB6.Certificate.PairSemantics.sound3119_e`, `OAI.MUB6.Certificate.PairSemantics.sound3120_e`, `OAI.MUB6.Certificate.PairSemantics.sound3122_e`, `OAI.MUB6.Certificate.PairSemantics.sound3123_e`, `OAI.MUB6.Certificate.PairSemantics.sound3124_e`, `OAI.MUB6.Certificate.PairSemantics.sound3125_e`, `OAI.MUB6.Certificate.PairSemantics.sound3127_e`, `OAI.MUB6.Certificate.PairSemantics.sound3128_e`, `OAI.MUB6.Certificate.PairSemantics.sound3129_e`, `OAI.MUB6.Certificate.PairSemantics.sound3130_e`, `OAI.MUB6.Certificate.PairSemantics.sound3131_e`, `OAI.MUB6.Certificate.PairSemantics.sound3132_e`, `OAI.MUB6.Certificate.PairSemantics.sound3133_e`, `OAI.MUB6.Certificate.PairSemantics.sound3135_e`, `OAI.MUB6.Certificate.PairSemantics.sound3136_e`, `OAI.MUB6.Certificate.PairSemantics.sound3137_e`, `OAI.MUB6.Certificate.PairSemantics.sound3138_e`, `OAI.MUB6.Certificate.PairSemantics.sound3139_e`, `OAI.MUB6.Certificate.PairSemantics.sound3140_e`, `OAI.MUB6.Certificate.PairSemantics.sound3141_e`, `OAI.MUB6.Certificate.PairSemantics.sound3142_e`, `OAI.MUB6.Certificate.PairSemantics.sound3144_e`, `OAI.MUB6.Certificate.PairSemantics.sound3145_e`, `OAI.MUB6.Certificate.PairSemantics.sound3146_e`, `OAI.MUB6.Certificate.PairSemantics.sound3149_e`, `OAI.MUB6.Certificate.PairSemantics.sound3150_e`, `OAI.MUB6.Certificate.PairSemantics.sound3151_e`, `OAI.MUB6.Certificate.PairSemantics.sound3152_e`, `OAI.MUB6.Certificate.PairSemantics.sound3153_e`, `OAI.MUB6.Certificate.PairSemantics.sound3154_e`, `OAI.MUB6.Certificate.PairSemantics.sound3158_e`, `OAI.MUB6.Certificate.PairSemantics.sound3159_e`, `OAI.MUB6.Certificate.PairSemantics.sound3160_e`, `OAI.MUB6.Certificate.PairSemantics.sound3161_e`, `OAI.MUB6.Certificate.PairSemantics.sound3163_e`, `OAI.MUB6.Certificate.PairSemantics.sound3164_e`, `OAI.MUB6.Certificate.PairSemantics.sound3166_e`, `OAI.MUB6.Certificate.PairSemantics.sound3167_e`, `OAI.MUB6.Certificate.PairSemantics.sound3169_e`, `OAI.MUB6.Certificate.PairSemantics.sound3170_e`, `OAI.MUB6.Certificate.PairSemantics.sound3171_e`, `OAI.MUB6.Certificate.PairSemantics.sound3172_e`, `OAI.MUB6.Certificate.PairSemantics.sound3173_e`, `OAI.MUB6.Certificate.PairSemantics.sound3174_e`, `OAI.MUB6.Certificate.PairSemantics.sound3176_e`, `OAI.MUB6.Certificate.PairSemantics.sound3178_e`, `OAI.MUB6.Certificate.PairSemantics.sound3179_e`, `OAI.MUB6.Certificate.PairSemantics.sound3180_e`, `OAI.MUB6.Certificate.PairSemantics.sound3181_e`, `OAI.MUB6.Certificate.PairSemantics.sound3183_e`, `OAI.MUB6.Certificate.PairSemantics.sound3184_e`, `OAI.MUB6.Certificate.PairSemantics.sound3185_e`, `OAI.MUB6.Certificate.PairSemantics.sound3187_e`, `OAI.MUB6.Certificate.PairSemantics.sound3188_e`, `OAI.MUB6.Certificate.PairSemantics.sound3189_e`, `OAI.MUB6.Certificate.PairSemantics.sound3191_e`, `OAI.MUB6.Certificate.PairSemantics.sound3192_e`, `OAI.MUB6.Certificate.PairSemantics.sound3193_e`, `OAI.MUB6.Certificate.PairSemantics.sound3194_e`, `OAI.MUB6.Certificate.PairSemantics.sound3195_e`, `OAI.MUB6.Certificate.PairSemantics.sound3196_e`, `OAI.MUB6.Certificate.PairSemantics.sound3197_e`, `OAI.MUB6.Certificate.PairSemantics.sound3198_e`, `OAI.MUB6.Certificate.PairSemantics.sound3199_e`, `OAI.MUB6.Certificate.PairSemantics.sound3200_e`, `OAI.MUB6.Certificate.PairSemantics.sound3201_e`, `OAI.MUB6.Certificate.PairSemantics.sound3202_e`, `OAI.MUB6.Certificate.PairSemantics.sound3203_e`, `OAI.MUB6.Certificate.PairSemantics.sound3204_e`, `OAI.MUB6.Certificate.PairSemantics.sound3205_e`, `OAI.MUB6.Certificate.PairSemantics.sound3206_e`, `OAI.MUB6.Certificate.PairSemantics.sound3208_e`, `OAI.MUB6.Certificate.PairSemantics.sound3209_e`, `OAI.MUB6.Certificate.PairSemantics.sound3211_e`, `OAI.MUB6.Certificate.PairSemantics.sound3212_e`, `OAI.MUB6.Certificate.PairSemantics.sound3213_e`, `OAI.MUB6.Certificate.PairSemantics.sound3215_e`, `OAI.MUB6.Certificate.PairSemantics.sound3216_e`, `OAI.MUB6.Certificate.PairSemantics.sound3218_e`, `OAI.MUB6.Certificate.PairSemantics.sound3220_e`, `OAI.MUB6.Certificate.PairSemantics.sound3221_e`, `OAI.MUB6.Certificate.PairSemantics.sound3222_e`, `OAI.MUB6.Certificate.PairSemantics.sound3223_e`, `OAI.MUB6.Certificate.PairSemantics.sound3224_e`, `OAI.MUB6.Certificate.PairSemantics.sound3225_e`, `OAI.MUB6.Certificate.PairSemantics.sound3226_e`, `OAI.MUB6.Certificate.PairSemantics.sound3227_e`, `OAI.MUB6.Certificate.PairSemantics.sound3228_e`, `OAI.MUB6.Certificate.PairSemantics.sound3229_e`, `OAI.MUB6.Certificate.PairSemantics.sound3230_e`, `OAI.MUB6.Certificate.PairSemantics.sound3233_e`, `OAI.MUB6.Certificate.PairSemantics.sound3234_e`, `OAI.MUB6.Certificate.PairSemantics.sound3235_e`, `OAI.MUB6.Certificate.PairSemantics.sound3237_e`, `OAI.MUB6.Certificate.PairSemantics.sound3238_e`, `OAI.MUB6.Certificate.PairSemantics.sound3240_e`, `OAI.MUB6.Certificate.PairSemantics.sound3242_e`, `OAI.MUB6.Certificate.PairSemantics.sound3243_e`, `OAI.MUB6.Certificate.PairSemantics.sound3244_e`, `OAI.MUB6.Certificate.PairSemantics.sound3246_e`, `OAI.MUB6.Certificate.PairSemantics.sound3247_e`, `OAI.MUB6.Certificate.PairSemantics.sound3248_e`, `OAI.MUB6.Certificate.PairSemantics.sound3249_e`, `OAI.MUB6.Certificate.PairSemantics.sound3253_e`, `OAI.MUB6.Certificate.PairSemantics.sound3254_e`, `OAI.MUB6.Certificate.PairSemantics.sound3255_e`, `OAI.MUB6.Certificate.PairSemantics.sound3256_e`, `OAI.MUB6.Certificate.PairSemantics.sound3258_e`, `OAI.MUB6.Certificate.PairSemantics.sound3260_e`, `OAI.MUB6.Certificate.PairSemantics.sound3262_e`, `OAI.MUB6.Certificate.PairSemantics.sound3263_e`, `OAI.MUB6.Certificate.PairSemantics.sound3264_e`, `OAI.MUB6.Certificate.PairSemantics.sound3266_e`, `OAI.MUB6.Certificate.PairSemantics.sound3267_e`, `OAI.MUB6.Certificate.PairSemantics.sound3268_e`, `OAI.MUB6.Certificate.PairSemantics.sound3269_e`, `OAI.MUB6.Certificate.PairSemantics.sound3271_e`, `OAI.MUB6.Certificate.PairSemantics.sound3272_e`, `OAI.MUB6.Certificate.PairSemantics.sound3273_e`, `OAI.MUB6.Certificate.PairSemantics.sound3274_e`, `OAI.MUB6.Certificate.PairSemantics.sound3275_e`, `OAI.MUB6.Certificate.PairSemantics.sound3276_e`, `OAI.MUB6.Certificate.PairSemantics.sound3277_e`, `OAI.MUB6.Certificate.PairSemantics.sound3278_e`, `OAI.MUB6.Certificate.PairSemantics.sound3279_e`, `OAI.MUB6.Certificate.PairSemantics.sound3280_e`, `OAI.MUB6.Certificate.PairSemantics.sound3281_e`, `OAI.MUB6.Certificate.PairSemantics.sound3282_e`, `OAI.MUB6.Certificate.PairSemantics.sound3283_e`, `OAI.MUB6.Certificate.PairSemantics.sound3284_e`, `OAI.MUB6.Certificate.PairSemantics.sound3288_e`, `OAI.MUB6.Certificate.PairSemantics.sound3289_e`, `OAI.MUB6.Certificate.PairSemantics.sound3290_e`, `OAI.MUB6.Certificate.PairSemantics.sound3291_e`, `OAI.MUB6.Certificate.PairSemantics.sound3292_e`, `OAI.MUB6.Certificate.PairSemantics.sound3293_e`, `OAI.MUB6.Certificate.PairSemantics.sound3294_e`, `OAI.MUB6.Certificate.PairSemantics.sound3295_e`, `OAI.MUB6.Certificate.PairSemantics.sound3296_e`, `OAI.MUB6.Certificate.PairSemantics.sound3297_e`, `OAI.MUB6.Certificate.PairSemantics.sound3298_e`, `OAI.MUB6.Certificate.PairSemantics.sound3299_e`, `OAI.MUB6.Certificate.PairSemantics.sound3300_e`, `OAI.MUB6.Certificate.PairSemantics.sound3301_e`, `OAI.MUB6.Certificate.PairSemantics.sound3302_e`, `OAI.MUB6.Certificate.PairSemantics.sound3303_e`, `OAI.MUB6.Certificate.PairSemantics.sound3304_e`, `OAI.MUB6.Certificate.PairSemantics.sound3305_e`, `OAI.MUB6.Certificate.PairSemantics.sound3307_e`, `OAI.MUB6.Certificate.PairSemantics.sound3308_e`, `OAI.MUB6.Certificate.PairSemantics.sound3309_e`, `OAI.MUB6.Certificate.PairSemantics.sound3310_e`, `OAI.MUB6.Certificate.PairSemantics.sound3311_e`, `OAI.MUB6.Certificate.PairSemantics.sound3313_e`, `OAI.MUB6.Certificate.PairSemantics.sound3314_e`, `OAI.MUB6.Certificate.PairSemantics.sound3315_e`, `OAI.MUB6.Certificate.PairSemantics.sound3316_e`, `OAI.MUB6.Certificate.PairSemantics.sound3317_e`, `OAI.MUB6.Certificate.PairSemantics.sound3319_e`, `OAI.MUB6.Certificate.PairSemantics.sound3322_e`, `OAI.MUB6.Certificate.PairSemantics.sound3324_e`, `OAI.MUB6.Certificate.PairSemantics.sound3325_e`, `OAI.MUB6.Certificate.PairSemantics.sound3326_e`, `OAI.MUB6.Certificate.PairSemantics.sound3327_e`, `OAI.MUB6.Certificate.PairSemantics.sound3328_e`, `OAI.MUB6.Certificate.PairSemantics.sound3331_e`, `OAI.MUB6.Certificate.PairSemantics.sound3333_e`, `OAI.MUB6.Certificate.PairSemantics.sound3334_e`, `OAI.MUB6.Certificate.PairSemantics.sound3335_e`, `OAI.MUB6.Certificate.PairSemantics.sound3336_e`, `OAI.MUB6.Certificate.PairSemantics.sound3338_e`, `OAI.MUB6.Certificate.PairSemantics.sound3339_e`, `OAI.MUB6.Certificate.PairSemantics.sound3341_e`, `OAI.MUB6.Certificate.PairSemantics.sound3343_e`, `OAI.MUB6.Certificate.PairSemantics.sound3345_e`, `OAI.MUB6.Certificate.PairSemantics.sound3346_e`, `OAI.MUB6.Certificate.PairSemantics.sound3347_e`, `OAI.MUB6.Certificate.PairSemantics.sound3348_e`, `OAI.MUB6.Certificate.PairSemantics.sound3349_e`, `OAI.MUB6.Certificate.PairSemantics.sound3350_e`, `OAI.MUB6.Certificate.PairSemantics.sound3351_e`, `OAI.MUB6.Certificate.PairSemantics.sound3352_e`, `OAI.MUB6.Certificate.PairSemantics.sound3353_e`, `OAI.MUB6.Certificate.PairSemantics.sound3354_e`, `OAI.MUB6.Certificate.PairSemantics.sound3355_e`, `OAI.MUB6.Certificate.PairSemantics.sound3356_e`, `OAI.MUB6.Certificate.PairSemantics.sound3357_e`, `OAI.MUB6.Certificate.PairSemantics.sound3358_e`, `OAI.MUB6.Certificate.PairSemantics.sound3359_e`, `OAI.MUB6.Certificate.PairSemantics.sound3360_e`, `OAI.MUB6.Certificate.PairSemantics.sound3361_e`, `OAI.MUB6.Certificate.PairSemantics.sound3362_e`, `OAI.MUB6.Certificate.PairSemantics.sound3363_e`, `OAI.MUB6.Certificate.PairSemantics.sound3364_e`, `OAI.MUB6.Certificate.PairSemantics.sound3366_e`, `OAI.MUB6.Certificate.PairSemantics.sound3367_e`, `OAI.MUB6.Certificate.PairSemantics.sound3368_e`, `OAI.MUB6.Certificate.PairSemantics.sound3369_e`, `OAI.MUB6.Certificate.PairSemantics.sound3370_e`, `OAI.MUB6.Certificate.PairSemantics.sound3371_e`, `OAI.MUB6.Certificate.PairSemantics.sound3372_e`, `OAI.MUB6.Certificate.PairSemantics.sound3375_e`, `OAI.MUB6.Certificate.PairSemantics.sound3376_e`, `OAI.MUB6.Certificate.PairSemantics.sound3377_e`, `OAI.MUB6.Certificate.PairSemantics.sound3378_e`, `OAI.MUB6.Certificate.PairSemantics.sound3380_e`, `OAI.MUB6.Certificate.PairSemantics.sound3382_e`, `OAI.MUB6.Certificate.PairSemantics.sound3383_e`, `OAI.MUB6.Certificate.PairSemantics.sound3384_e`, `OAI.MUB6.Certificate.PairSemantics.sound3385_e`, `OAI.MUB6.Certificate.PairSemantics.sound3387_e`, `OAI.MUB6.Certificate.PairSemantics.sound3388_e`, `OAI.MUB6.Certificate.PairSemantics.sound3389_e`, `OAI.MUB6.Certificate.PairSemantics.sound3390_e`, `OAI.MUB6.Certificate.PairSemantics.sound3391_e`, `OAI.MUB6.Certificate.PairSemantics.sound3392_e`, `OAI.MUB6.Certificate.PairSemantics.sound3393_e`, `OAI.MUB6.Certificate.PairSemantics.sound3394_e`, `OAI.MUB6.Certificate.PairSemantics.sound3395_e`, `OAI.MUB6.Certificate.PairSemantics.sound3396_e`, `OAI.MUB6.Certificate.PairSemantics.sound3397_e`, `OAI.MUB6.Certificate.PairSemantics.sound3399_e`, `OAI.MUB6.Certificate.PairSemantics.sound3400_e`, `OAI.MUB6.Certificate.PairSemantics.sound3401_e`, `OAI.MUB6.Certificate.PairSemantics.sound3402_e`, `OAI.MUB6.Certificate.PairSemantics.sound3405_e`, `OAI.MUB6.Certificate.PairSemantics.sound3407_e`, `OAI.MUB6.Certificate.PairSemantics.sound3408_e`, `OAI.MUB6.Certificate.PairSemantics.sound3411_e`, `OAI.MUB6.Certificate.PairSemantics.sound3412_e`, `OAI.MUB6.Certificate.PairSemantics.sound3413_e`, `OAI.MUB6.Certificate.PairSemantics.sound3414_e`, `OAI.MUB6.Certificate.PairSemantics.sound3415_e`, `OAI.MUB6.Certificate.PairSemantics.sound3416_e`, `OAI.MUB6.Certificate.PairSemantics.sound3417_e`, `OAI.MUB6.Certificate.PairSemantics.sound3418_e`, `OAI.MUB6.Certificate.PairSemantics.sound3419_e`, `OAI.MUB6.Certificate.PairSemantics.sound3420_e`, `OAI.MUB6.Certificate.PairSemantics.sound3421_e`, `OAI.MUB6.Certificate.PairSemantics.sound3422_e`, `OAI.MUB6.Certificate.PairSemantics.sound3423_e`, `OAI.MUB6.Certificate.PairSemantics.sound3424_e`, `OAI.MUB6.Certificate.PairSemantics.sound3425_e`, `OAI.MUB6.Certificate.PairSemantics.sound3428_e`, `OAI.MUB6.Certificate.PairSemantics.sound3431_e`, `OAI.MUB6.Certificate.PairSemantics.sound3433_e`, `OAI.MUB6.Certificate.PairSemantics.sound3434_e`, `OAI.MUB6.Certificate.PairSemantics.sound3435_e`, `OAI.MUB6.Certificate.PairSemantics.sound3436_e`, `OAI.MUB6.Certificate.PairSemantics.sound3437_e`, `OAI.MUB6.Certificate.PairSemantics.sound3439_e`, `OAI.MUB6.Certificate.PairSemantics.sound3440_e`, `OAI.MUB6.Certificate.PairSemantics.sound3441_e`, `OAI.MUB6.Certificate.PairSemantics.sound3442_e`, `OAI.MUB6.Certificate.PairSemantics.sound3443_e`, `OAI.MUB6.Certificate.PairSemantics.sound3444_e`, `OAI.MUB6.Certificate.PairSemantics.sound3447_e`, `OAI.MUB6.Certificate.PairSemantics.sound3449_e`, `OAI.MUB6.Certificate.PairSemantics.sound3451_e`, `OAI.MUB6.Certificate.PairSemantics.sound3454_e`, `OAI.MUB6.Certificate.PairSemantics.sound3455_e`, `OAI.MUB6.Certificate.PairSemantics.sound3456_e`, `OAI.MUB6.Certificate.PairSemantics.sound3457_e`, `OAI.MUB6.Certificate.PairSemantics.sound3458_e`, `OAI.MUB6.Certificate.PairSemantics.sound3459_e`, `OAI.MUB6.Certificate.PairSemantics.sound3460_e`, `OAI.MUB6.Certificate.PairSemantics.sound3461_e`, `OAI.MUB6.Certificate.PairSemantics.sound3462_e`, `OAI.MUB6.Certificate.PairSemantics.sound3463_e`, `OAI.MUB6.Certificate.PairSemantics.sound3467_e`, `OAI.MUB6.Certificate.PairSemantics.sound3468_e`, `OAI.MUB6.Certificate.PairSourceBridge.allRowsSound_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound0_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound100_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound101_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound102_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound103_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound104_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound105_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound106_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound107_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound108_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound10_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound110_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound111_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound112_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound113_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound114_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound115_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound116_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound117_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound118_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound119_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound120_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound121_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound123_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound124_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound125_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound127_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound128_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound129_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound130_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound131_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound132_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound133_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound134_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound135_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound136_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound137_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound138_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound139_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound140_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound141_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound142_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound143_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound144_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound145_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound146_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound147_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound148_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound149_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound14_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound150_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound151_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound152_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound153_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound154_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound155_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound156_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound157_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound158_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound159_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound15_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound160_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound161_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound162_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound163_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound164_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound165_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound166_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound167_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound168_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound16_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound170_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound171_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound172_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound174_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound175_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound176_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound177_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound178_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound179_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound17_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound180_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound181_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound182_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound183_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound184_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound185_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound186_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound187_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound188_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound189_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound18_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound191_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound192_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound193_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound194_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound195_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound196_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound197_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound198_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound199_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound19_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound1_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound200_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound203_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound204_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound205_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound206_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound208_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound209_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound20_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound210_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound211_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound212_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound213_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound216_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound217_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound218_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound219_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound21_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound220_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound221_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound222_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound223_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound224_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound225_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound226_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound227_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound228_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound229_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound22_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound230_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound231_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound232_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound233_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound234_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound235_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound236_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound237_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound238_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound239_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound23_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound240_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound241_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound242_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound243_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound244_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound245_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound246_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound247_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound248_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound249_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound24_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound250_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound251_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound252_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound253_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound254_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound26_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound27_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound28_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound29_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound2_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound30_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound31_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound32_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound34_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound35_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound36_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound37_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound38_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound39_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound3_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound40_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound41_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound42_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound43_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound44_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound45_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound46_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound47_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound49_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound4_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound50_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound51_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound52_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound53_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound54_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound55_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound56_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound58_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound59_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound5_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound60_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound61_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound62_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound63_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound64_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound65_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound66_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound67_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound69_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound6_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound70_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound72_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound73_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound74_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound75_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound76_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound77_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound78_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound79_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound7_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound80_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound81_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound82_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound83_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound84_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound85_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound86_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound87_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound88_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound89_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound90_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound91_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound92_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound93_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound94_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound95_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound96_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound97_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound98_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound99_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound9_e`, `OAI.MUB6.Certificate.PairTargetSemantics.expandedIdentity1_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm11_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm12_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm13_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm14_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm16_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm17_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm18_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm19_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm21_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm22_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm23_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm24_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm25_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm26_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm6_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm7_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm8_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm9_e` and `OAI.MUB6.pair_cross_certificate_e`.
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

def raw1step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]

def raw1step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

def raw2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]

def raw2step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]

def raw2step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def raw3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]

def raw12step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 5, -5], ![1, -3, 2]]

def raw13 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw13step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]

def raw13step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def raw14 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]

def raw14step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]

def raw14step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw15 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]

def raw15step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]

def raw15step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw16 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]

def raw16step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]

def raw16step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]

def raw17 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]

def raw17step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]

def raw17step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def raw18 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]

def raw18step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]

def raw18step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw19 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]

def raw19step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]

def raw19step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

def raw20 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]

def raw20step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]

def raw20step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

def raw21 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]

def raw21step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 1, 0], ![-2, 2, 0], ![-2, -1, 3]]

def raw21step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]

def raw22 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]

def raw22step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]

def raw22step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def raw23 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]

def raw23step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]

def raw23step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]

def raw24 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]

def raw24step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]

def raw24step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]

def raw25 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]

def raw25step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]

def raw25step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

def raw26 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]

def raw26step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]

def raw26step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

def raw27 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]

def raw27step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![2, 0, -2], ![3, -1, -2]]

def raw27step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -1, -4], ![-2, 0, 2], ![-3, 1, 2]]

def raw27step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 2, -2], ![1, 2, -3]]

def raw28 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]

def raw28step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![-1, -1, 2], ![-2, 2, 0], ![-2, 1, 1]]

def raw28step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

def raw29 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![4, -3, -1]]

def raw29step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![2, 1, -3], ![3, -2, -1]]

def raw29step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -3, 2], ![1, 4, -5]]

def raw30 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]

def raw30step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![-2, 2, 0], ![-3, 0, 3]]

def raw30step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 3, -3], ![2, 0, -2]]

def raw31 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -1, -1], ![3, -1, -2]]

def raw31step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![-2, 1, 1], ![-3, 1, 2]]

def raw31step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![1, 1, -2], ![1, 2, -3]]

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

def raw32 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 0, -2], ![3, -2, -1]]

def raw32step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![-2, 0, 2], ![-3, 2, 1]]

def raw32step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![2, 1, -3]]

def raw33 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 1, -3], ![3, -3, 0]]

def raw33step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![-2, -1, 3], ![-3, 3, 0]]

def raw33step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![3, -1, -2]]

def raw34 : Matrix (Fin 2) (Fin 3) ℤ := ![![-5, 2, 3], ![5, -2, -3]]

def raw34step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![2, -2], ![3, -3]]

def raw35 : Matrix (Fin 2) (Fin 3) ℤ := ![![-5, 3, 2], ![5, -3, -2]]

def raw53 : Matrix (Fin 2) (Fin 2) ℤ := ![![-5, 5], ![5, -5]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw320 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![3, -2, -1]]

def raw321 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 0, -1], ![1, 3, -4]]

def raw321step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 2, -1], ![-1, 0, 1], ![-1, -3, 4]]

def raw321step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]

def raw322 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]

def raw323 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 2, -3], ![1, 1, -2]]

def raw323step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]

def raw324 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![2, 3, -5]]

def raw324step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -2, 3], ![4, 1, -5]]

def raw324step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -3, 2], ![1, 4, -5]]

def raw325 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]

def raw326 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

def raw326step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]

def raw326step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def raw327 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]

def raw327step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2]]

def raw328 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![2, 2, -4]]

def raw328step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![4, 0, -4]]

def raw328step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-4, 0, 4]]

def raw328step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 4, -4], ![1, -2, 1]]

def raw329 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 0, -1], ![1, -1, 0], ![1, 2, -3]]

def raw329step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-1, 1, 0], ![-1, -2, 3]]

def raw329step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def raw330 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 1, -2], ![1, -1, 0], ![1, 1, -2]]

def raw330step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2]]

def raw331 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 2, -3], ![1, -2, 1], ![1, 1, -2]]

def raw331step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]

def raw332 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 2, -3], ![1, -1, 0], ![1, 0, -1]]

def raw332step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, -2, 3], ![-1, 1, 0], ![-1, 0, 1]]

def raw332step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def raw333 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 2, -3], ![2, -1, -1]]

def raw333step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, -2, 3], ![-2, 1, 1]]

def raw333step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -2, 1], ![1, 3, -4]]

def raw334 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 3, -4], ![1, -2, 1], ![1, 0, -1]]

def raw334step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, -3, 4], ![-1, 2, -1], ![-1, 0, 1]]

def raw334step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]

def raw335 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 3, -4], ![2, -2, 0]]

def raw335step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![4, -4, 0]]

def raw335step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 4, -4], ![2, -3, 1]]

def raw336 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![2, -2, 0], ![1, 3, -4]]

def raw336step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![4, 0, -4]]

def raw336step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 4, -4], ![2, -3, 1]]

def raw337 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 0, 3], ![0, -2, 2, 0], ![3, 2, -2, -3]]

def raw337step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![3, 0, -3]]

def raw337step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 3, -3], ![2, 0, -2]]

def raw338 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 0, 3], ![1, -2, 2, -1], ![2, 2, -2, -2]]

def raw338step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]

def raw339 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 1, 2], ![-2, 2, 1, -1], ![5, -2, -2, -1]]

def raw339step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

def raw340 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 1, 2], ![-1, 2, -2, 1], ![4, -2, 1, -3]]

def raw340step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]

def raw341 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 1, 2], ![-1, 2, 1, -2], ![4, -2, -2, 0]]

def raw341step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

def raw342 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 1, 2], ![-1, 3, -2, 0], ![4, -3, 1, -2]]

def raw342step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]

def raw343 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 1, 2], ![0, -2, 1, 1], ![3, 2, -2, -3]]

def raw343step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 1, -2], ![2, 1, -3]]

def raw343step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 1, -2], ![1, 2, -3]]

def raw344 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 1, 2], ![0, -2, 2, 0], ![3, 2, -3, -2]]

def raw344step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]

def raw344step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, -2, 3], ![-2, 0, 2]]

def raw344step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![2, 0, -2]]

def raw345 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 1, 2], ![0, -2, 3, -1], ![3, 2, -4, -1]]

def raw345step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 3, -4], ![2, -1, -1]]

def raw345step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, -3, 4], ![-2, 1, 1]]

def raw345step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]

def raw346 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 1, 2], ![0, 2, -2, 0], ![3, -2, 1, -2]]

def raw346step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]

def raw346step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]

def raw346step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

def raw347 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 1, 2], ![0, 3, -2, -1], ![3, -3, 1, -1]]

def raw347step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]

def raw348 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 1, 2], ![0, 4, -2, -2], ![3, -4, 1, 0]]

def raw348step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 4, -4], ![1, -2, 1], ![2, -2, 0]]

def raw349 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 1, 2], ![1, -2, 1, 0], ![2, 2, -2, -2]]

def raw349step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]

def raw349step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

def raw350 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 1, 2], ![1, -2, 2, -1], ![2, 2, -3, -1]]

def raw350step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]

def raw351 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 1, 2], ![1, -2, 3, -2], ![2, 2, -4, 0]]

def raw351step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 3, -4], ![2, -2, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical100
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3200 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw3200step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![-1, -1, 0, 2], ![3, 0, -1, -2]]

def raw3200step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![1, 1, 0, -2], ![-3, 0, 1, 2]]

def raw3200step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -3, 2], ![1, 0, 1, -2]]

def raw3201 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 0, 0, -1]]

def raw3201step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw3202 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def raw3203 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, -1, 2, -2]]

def raw3204 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -2, 1, -1]]

def raw3204step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![-1, -1, 1, 1], ![3, 0, -2, -1]]

def raw3204step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![1, 1, -1, -1], ![-3, 0, 2, 1]]

def raw3204step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -3, 1], ![1, -1, 1, -1]]

def raw3205 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def raw3206 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, -1, 1, -1]]

def raw3207 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw3207step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw3208 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, -2, 0, 0]]

def raw3208step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![-1, -1, 2, 0], ![3, 0, -3, 0]]

def raw3208step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -2, 0, 1]]

def raw3209 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def raw3210 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw3211 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, -1, 1]]

def raw3211step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw3212 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![2, -2, -1, 1]]

def raw3212step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![-1, -1, 3, -1], ![3, 0, -4, 1]]

def raw3212step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -2, 2, 0], ![0, 3, 1, -4], ![1, 0, -2, 1]]

def raw3213 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 1, 2, -4]]

def raw3213step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![-1, -1, 0, 2], ![3, 0, 1, -4]]

def raw3213step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw3214 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 1, 1, -3]]

def raw3214step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![-1, -1, 1, 1], ![3, 0, 0, -3]]

def raw3214step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -2, 0, 1]]

def raw3215 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 1, 0, -2]]

def raw3215step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![-1, -1, 2, 0], ![3, 0, -1, -2]]

def raw3215step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 2, -1], ![1, 1, -2, 0], ![-3, 0, 1, 2]]

def raw3215step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -3, 1], ![1, 0, 1, -2]]

def raw3216 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![1, -2, 3, -2], ![1, 1, -1, -1]]

def raw3216step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![-1, -1, 3, -1], ![3, 0, -2, -1]]

def raw3216step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def raw3217 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 3, -4]]

def raw3217step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![-1, -1, -1, 3], ![3, 0, 1, -4]]

def raw3217step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw3218 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw3218step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![-1, -1, 0, 2], ![3, 0, 0, -3]]

def raw3218step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -1, 0, 0]]

def raw3219 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw3219step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, -1, 1, 0], ![-1, 1, -1, 1], ![-1, 0, -1, 2]]

def raw3219step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -1, 2], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw3220 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def raw3220step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![-1, -1, 2, 0], ![3, 0, -2, -1]]

def raw3220step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw3221 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw3221step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![-1, -1, 3, -1], ![3, 0, -3, 0]]

def raw3221step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw3222 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, -1, 3, -3]]

def raw3222step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 0, -1], ![-1, -1, -1, 3], ![3, 0, 0, -3]]

def raw3222step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw3223 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, -1, 2, -2]]

def raw3223step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 0, -1], ![-1, -1, 0, 2], ![3, 0, -1, -2]]

def raw3223step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw3224 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 0, 1, -2]]

def raw3224step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def raw3225 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw3225step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -2, -1]]

def raw3226 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw3226step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, -1, -2]]

def raw3227 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 0, -1], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def raw3227step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![-1, 0, -1, 2], ![3, -1, 0, -2]]

def raw3227step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![1, 0, 1, -2], ![-3, 1, 0, 2]]

def raw3227step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -3, 2], ![1, 0, 1, -2]]

def raw3228 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def raw3228step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 2, -2, -1]]

def raw3229 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 2, -2]]

def raw3229step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 2, -1, -2]]

def raw3230 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def raw3230step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw3231 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw3231step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, -1, 0, 1], ![0, -1, -2, 3], ![-1, 1, 1, -1], ![-1, 1, 0, 0]]

def raw3231step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, 2, -3], ![1, 1, -1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical101
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3232 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 1, -1, -1]]

def raw3232step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![-1, 0, 2, -1], ![3, -1, -1, -1]]

def raw3232step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw3233 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 1, -2, 0]]

def raw3233step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![-1, 0, 3, -2], ![3, -1, -2, 0]]

def raw3233step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 2, -1], ![1, 0, -3, 2], ![-3, 1, 2, 0]]

def raw3233step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, 0, -3, 2]]

def raw3234 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 2, -3]]

def raw3234step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw3235 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw3235step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![-1, 0, 2, -1], ![3, -1, -2, 0]]

def raw3235step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw3236 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 0, -1], ![1, -1, 3, -3], ![1, 0, -2, 1]]

def raw3236step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, -1, 0, 1], ![-1, 1, -3, 3], ![-1, 0, 2, -1]]

def raw3236step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, -1, -3, 3]]

def raw3237 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, -1, 3, -3]]

def raw3237step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, -1, 0, 1], ![-1, 0, 2, -1], ![-1, 1, -3, 3]]

def raw3237step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, -1, -3, 3]]

def raw3238 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 1, -2], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 0, 0, -1]]

def raw3238step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw3239 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 1, -2], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def raw3239step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![-1, 1, -1, 1], ![3, -2, 0, -1]]

def raw3239step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![1, -1, 1, -1], ![-3, 2, 0, 1]]

def raw3239step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -3, 1], ![1, -1, 1, -1]]

def raw3240 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 1, -2], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def raw3240step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw3241 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 1, -1, -1]]

def raw3241step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw3242 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 1, -2, 0]]

def raw3243 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def raw3243step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, -1, -1, 2], ![-1, 1, 1, -1], ![-1, 0, -1, 2]]

def raw3243step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, 1, -1, -1]]

def raw3244 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw3244step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, -1, -1, 2], ![-1, 1, -1, 1], ![-1, 0, 1, 0]]

def raw3244step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1]]

def raw3245 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 1, -2], ![1, 0, -2, 1], ![1, -1, 2, -2]]

def raw3245step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, -1, -1, 2], ![-1, 0, 2, -1], ![-1, 1, -2, 2]]

def raw3245step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, -1, -2, 2]]

def raw3246 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 2, -3], ![0, 1, -2, 1], ![2, -2, 1, -1]]

def raw3246step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![2, -2, 1, -1]]

def raw3247 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 2, -3], ![0, 1, -1, 0], ![2, -2, 0, 0]]

def raw3247step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![-1, 2, -1, 0], ![3, -3, 0, 0]]

def raw3247step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -2, 0, 1]]

def raw3248 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 2, -3], ![1, -2, 1, 0], ![1, 1, -2, 0]]

def raw3249 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw3249step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, -1, -2, 3], ![-1, 1, 1, -1], ![-1, 0, 0, 1]]

def raw3249step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 1, -1, -1]]

def raw3250 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw3250step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![-1, 2, 0, -1], ![3, -3, 0, 0]]

def raw3250step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 1, 0], ![1, -2, 0, 1], ![-3, 3, 0, 0]]

def raw3250step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, -1, 0]]

def raw3251 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 0, -2, 1]]

def raw3251step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, -1, -2, 3], ![-1, 1, -1, 1], ![-1, 0, 2, -1]]

def raw3251step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw3252 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 2, -3], ![1, 0, -2, 1], ![1, -1, 1, -1]]

def raw3252step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, -1, -2, 3], ![-1, 0, 2, -1], ![-1, 1, -1, 1]]

def raw3252step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw3253 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 3, -4], ![1, -2, 0, 1], ![1, 1, -2, 0]]

def raw3254 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw3254step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![-1, 3, -1, -1], ![3, -4, 1, 0]]

def raw3254step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 0, 1], ![0, 1, 3, -4], ![1, 1, -2, 0]]

def raw3255 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw3255step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![-1, 3, 0, -2], ![3, -4, 0, 1]]

def raw3255step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 1, 0], ![1, -3, 0, 2], ![-3, 4, 0, -1]]

def raw3255step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -3, 4], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw3256 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 3, -4], ![1, 0, -2, 1], ![1, -1, 0, 0]]

def raw3256step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 0, -1], ![-1, 3, -2, 0], ![3, -4, 1, 0]]

def raw3256step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 0, 1], ![1, -3, 2, 0], ![-3, 4, -1, 0]]

def raw3256step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -3, 4], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw3257 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def raw3257step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![-1, -2, 0, 3], ![3, 0, 1, -4]]

def raw3257step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 3, -4], ![2, -2, 0, 0]]

def raw3258 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -2, 1, 0], ![1, 0, 2, -3]]

def raw3259 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -2, 2, -1], ![1, 0, 1, -2]]

def raw3260 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw3260step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![-1, -2, 3, 0], ![3, 0, -2, -1]]

def raw3260step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -2, 2, 0], ![1, 2, -3, 0], ![-3, 0, 2, 1]]

def raw3260step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 2, 1, -3], ![1, 0, -3, 2]]

def raw3261 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw3261step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![-1, -2, 0, 3], ![3, 0, 0, -3]]

def raw3261step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -2, 1, 1], ![1, 2, 0, -3], ![-3, 0, 0, 3]]

def raw3261step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -3, 3], ![0, 2, 1, -3], ![1, -2, 0, 1]]

def raw3262 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def raw3263 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -1, 2, -2], ![1, -1, 1, -1]]

def raw3263step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, -1, 2, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical102
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3264 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -1, -1], ![1, -2, 1, 0], ![1, 0, 1, -2]]

def raw3264step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def raw3265 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -1, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw3265step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![-1, -1, 2, 0], ![3, -1, -1, -1]]

def raw3265step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def raw3266 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -1, -1], ![1, -2, 3, -2], ![1, 0, -1, 0]]

def raw3266step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![-1, -1, 3, -1], ![3, -1, -2, 0]]

def raw3266step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw3267 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, -1, 3, -3]]

def raw3268 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw3268step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![-1, -1, 0, 2], ![3, -1, 0, -2]]

def raw3268step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -2, 1, 1], ![1, 1, 0, -2], ![-3, 1, 0, 2]]

def raw3268step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw3269 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def raw3269step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def raw3270 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, 0, -2], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def raw3270step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![-1, 0, 2, -1], ![3, -2, -1, 0]]

def raw3270step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -2, 2, 0], ![1, 0, -2, 1], ![-3, 2, 1, 0]]

def raw3270step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 2, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw3271 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, -1, 2, -2]]

def raw3271step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 2, -1, -2]]

def raw3272 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, 1, -3], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def raw3272step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![-1, 1, 1, -1], ![3, -3, 0, 0]]

def raw3272step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -2, 2, 0], ![1, -1, -1, 1], ![-3, 3, 0, 0]]

def raw3272step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, -1, 1]]

def raw3273 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, 1, -3], ![1, -1, -1, 1], ![1, -1, 1, -1]]

def raw3273step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def raw3274 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, 2, -4], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def raw3274step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![-1, 2, 0, -1], ![3, -4, 1, 0]]

def raw3274step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -2, 2, 0], ![1, -2, 0, 1], ![-3, 4, -1, 0]]

def raw3274step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw3275 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, 2, -4], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw3275step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![-1, 2, -1, 0], ![3, -4, 1, 0]]

def raw3275step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, 1, -2, 0]]

def raw3276 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![1, -2, 2, -1], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def raw3276step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -2, 2, -1], ![1, 0, 1, -2]]

def raw3277 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![1, -2, 3, -2], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def raw3277step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![1, -2, 3, -2], ![1, 1, 0, -2]]

def raw3278 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![1, -2, 3, -2], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw3278step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 2, 0], ![-1, 3, -2, 0], ![3, -2, 0, -1]]

def raw3278step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 2, -2, 0], ![1, -3, 2, 0], ![-3, 2, 0, 1]]

def raw3278step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 2, 1, -3], ![1, 0, -3, 2]]

def raw3279 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![1, -2, 3, -2], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw3279step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 2, 0], ![-1, 3, -1, -1], ![3, -2, -1, 0]]

def raw3279step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw3280 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![1, -1, 2, -2], ![0, 2, -2, 0], ![1, -1, 1, -1]]

def raw3280step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def raw3281 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![1, -1, 3, -3], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw3281step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 2, -1], ![-1, 3, -2, 0], ![3, -3, 0, 0]]

def raw3281step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 1, -2, 1], ![1, -3, 2, 0], ![-3, 3, 0, 0]]

def raw3281step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -3, 3], ![0, 2, 1, -3], ![1, -2, 0, 1]]

def raw3282 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![1, -1, 3, -3], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw3282step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, -1, 3, -3]]

def raw3283 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![1, 0, -2, 1], ![0, 1, 1, -2], ![1, -1, 2, -2]]

def raw3283step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![-1, 0, 2, -1], ![0, -1, -1, 2], ![-1, 1, -2, 2]]

def raw3283step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, -1, -2, 2]]

def raw3284 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![1, 0, -2, 1], ![0, 1, 2, -3], ![1, -1, 1, -1]]

def raw3284step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![-1, 0, 2, -1], ![0, -1, -2, 3], ![-1, 1, -1, 1]]

def raw3284step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw3285 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![1, 0, -2, 1], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw3285step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![-1, -2, 3, 0], ![3, 1, -4, 0]]

def raw3285step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, -1, 1], ![1, 2, -3, 0], ![-3, -1, 4, 0]]

def raw3285step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -3, 4], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw3286 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![1, 0, 1, -2], ![0, 2, -1, -1], ![1, -2, 1, 0]]

def raw3286step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def raw3287 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![1, 0, 2, -3], ![0, 2, -2, 0], ![1, -2, 1, 0]]

def raw3287step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -2, 1, 0], ![1, 0, 2, -3]]

def raw3288 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 2, 2, -2], ![4, -2, -2, 0]]

def raw3288step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 2, -2], ![2, -2, 0]]

def raw3289 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, -2, 2, 1], ![3, 2, -2, -3]]

def raw3289step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![2, 1, -3]]

def raw3290 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, -2, 3, 0], ![3, 2, -3, -2]]

def raw3290step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![2, 0, -2]]

def raw3291 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, -2, 4, -1], ![3, 2, -4, -1]]

def raw3291step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 4, -4], ![2, -1, -1]]

def raw3292 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -3, 3, 0], ![2, 3, -3, -2]]

def raw3292step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 3, -3], ![2, 0, -2]]

def raw3293 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -3, 4, -1], ![2, 3, -4, -1]]

def raw3293step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 4, -4], ![2, -1, -1]]

def raw3294 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 0, 2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw3294step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, 0, -2], ![0, -1, 1, 0], ![-1, 0, 1, 0], ![-1, -1, -2, 4]]

def raw3294step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw3295 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 0, 2], ![0, 1, -1, 0], ![1, 1, -2, 0], ![1, 0, 3, -4]]

def raw3295step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 0, 2], ![0, 1, -1, 0], ![1, 0, 3, -4], ![1, 1, -2, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical103
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3296 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 0, 2], ![0, 1, 3, -4], ![2, 1, -3, 0]]

def raw3296step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 0, 3, -3], ![2, 2, -4, 0]]

def raw3296step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, -1, -1], ![0, 0, -3, 3], ![-2, -2, 4, 0]]

def raw3296step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 3, -3], ![0, 2, -2, 0], ![2, 0, -1, -1]]

def raw3297 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 0, 2], ![0, 2, -2, 0], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def raw3297step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![2, 0, -2, 0]]

def raw3298 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 0, 2], ![0, 2, 2, -4], ![2, 0, -2, 0]]

def raw3298step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, 0, -2], ![0, -2, -2, 4], ![-2, 0, 2, 0]]

def raw3298step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![2, 0, 0, -2]]

def raw3299 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 0, 2], ![1, 0, 3, -4], ![1, 2, -3, 0]]

def raw3299step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 0, 2], ![0, 0, 3, -3], ![2, 2, -4, 0]]

def raw3299step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 2, 0, -2], ![0, 0, -3, 3], ![-2, -2, 4, 0]]

def raw3299step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 3, -3], ![0, 2, -2, 0], ![2, 0, -1, -1]]

def raw3300 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 0, 2], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def raw3300step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, 0, -2], ![-1, -1, 1, 1], ![-1, -1, -1, 3]]

def raw3300step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw3301 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 0, 2], ![1, 1, 2, -4], ![1, 1, -2, 0]]

def raw3301step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 0, 2, -2], ![2, 2, -4, 0]]

def raw3301step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 2, -1, -1], ![0, 0, -2, 2], ![-2, -2, 4, 0]]

def raw3301step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw3302 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, -2, 1], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw3303 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, -2, 1], ![2, 1, 1, -4]]

def raw3303step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, -1, -1], ![0, -1, 2, -1], ![-2, -1, -1, 4]]

def raw3303step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def raw3304 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 0, -2, 1], ![1, 1, 2, -4]]

def raw3305 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw3306 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw3306step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, 0, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -2, 1]]

def raw3307 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw3308 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw3308step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, -1, -1], ![0, -1, 0, 1], ![-1, 0, 0, 1], ![-1, -1, 1, 1]]

def raw3308step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw3309 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -2, 0]]

def raw3310 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw3311 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, 1, -2], ![2, 1, -2, -1]]

def raw3311step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, -1, -1], ![0, -1, -1, 2], ![-2, -1, 2, 1]]

def raw3311step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def raw3312 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw3313 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 2, -2, 0], ![1, 0, 1, -2], ![1, 0, 0, -1]]

def raw3313step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw3314 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 2, -2, 0], ![2, 0, 1, -3]]

def raw3314step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, -1, -1], ![0, -2, 2, 0], ![-2, 0, -1, 3]]

def raw3314step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![2, 0, 0, -2]]

def raw3315 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw3315step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1]]

def raw3316 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![1, 0, -2, 1], ![1, 2, 1, -4]]

def raw3316step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, -1, -1], ![-1, 0, 2, -1], ![-1, -2, -1, 4]]

def raw3316step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw3317 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![1, 0, -1, 0], ![1, 2, 0, -3]]

def raw3317step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -2, 0, 1]]

def raw3318 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![1, 0, 1, -2], ![1, 2, -2, -1]]

def raw3318step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, -1, -1], ![-1, 0, -1, 2], ![-1, -2, 2, 1]]

def raw3318step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw3319 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![1, 1, -3, 1], ![1, 1, 2, -4]]

def raw3319step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 1, -3, 2], ![2, 1, 1, -4]]

def raw3319step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 2, -1, -1], ![0, -1, 3, -2], ![-2, -1, -1, 4]]

def raw3319step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 3, -2], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw3320 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![1, 1, -2, 0], ![1, 1, 1, -3]]

def raw3320step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 1, -2, 1], ![2, 1, 0, -3]]

def raw3320step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 2, -1, -1], ![0, -1, 2, -1], ![-2, -1, 0, 3]]

def raw3320step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw3321 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def raw3321step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, -1, -1], ![-1, -1, 1, 1], ![-1, -1, 0, 2]]

def raw3321step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw3322 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![1, 1, 0, -2], ![1, 1, -1, -1]]

def raw3322step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, -1, -1], ![-1, -1, 0, 2], ![-1, -1, 1, 1]]

def raw3322step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw3323 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![1, 1, 1, -3], ![1, 1, -2, 0]]

def raw3323step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 1, 1, -2], ![2, 1, -3, 0]]

def raw3323step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 2, -1, -1], ![0, -1, -1, 2], ![-2, -1, 3, 0]]

def raw3323step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw3324 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![1, 2, -2, -1], ![1, 0, 1, -2]]

def raw3324step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, -1, -1], ![-1, -2, 2, 1], ![-1, 0, -1, 2]]

def raw3324step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw3325 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw3326 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw3327 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical104
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3328 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, -1, 0], ![1, 1, -1, -1], ![1, 0, 0, -1]]

def raw3328step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw3329 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, -1, 0], ![2, 1, -1, -2]]

def raw3329step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def raw3329step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw3330 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw3331 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 1, 0, -2]]

def raw3332 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw3333 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw3333step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, -2, 0], ![0, -1, 0, 1], ![-1, 0, 0, 1], ![-1, -1, 2, 0]]

def raw3333step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw3334 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![1, 1, -2, 0], ![1, 0, 0, -1]]

def raw3334step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, -2, 0], ![0, -1, 0, 1], ![-1, -1, 2, 0], ![-1, 0, 0, 1]]

def raw3334step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw3335 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![1, 1, -1, -1], ![1, 0, -1, 0]]

def raw3335step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw3336 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def raw3336step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw3336step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -2, 0, 1]]

def raw3337 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw3337step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw3338 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 2, -2, 0], ![2, 0, 0, -2]]

def raw3339 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw3340 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 2, 0, -2], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def raw3341 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw3341step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw3342 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 2, 0, -2], ![2, 0, -2, 0]]

def raw3343 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![1, 0, -2, 1], ![1, 2, 0, -3]]

def raw3343step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, -2, 0], ![-1, 0, 2, -1], ![-1, -2, 0, 3]]

def raw3343step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -2, 0]]

def raw3344 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![1, 0, -1, 0], ![1, 2, -1, -2]]

def raw3344step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 0, 2], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def raw3344step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -2, 0, 1]]

def raw3345 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![1, 0, 0, -1], ![1, 2, -2, -1]]

def raw3345step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 0, 2], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw3345step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw3346 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def raw3346step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, -2, 0], ![-1, -1, 2, 0], ![-1, -1, 0, 2]]

def raw3346step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw3347 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def raw3348 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![1, 2, 0, -3], ![1, 0, -2, 1]]

def raw3348step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, -2, 0], ![-1, -2, 0, 3], ![-1, 0, 2, -1]]

def raw3348step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -2, 0]]

def raw3349 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![2, 2, -2, -2]]

def raw3349step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![2, 0, -2]]

def raw3350 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 3, -1], ![2, 2, -3, -1]]

def raw3350step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

def raw3351 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 4, -2], ![2, 2, -4, 0]]

def raw3351step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 4, -4], ![2, -2, 0]]

def raw3352 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 0, 0, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw3352step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 1, -2], ![0, 0, 0, 0], ![-1, 0, 1, 0], ![-1, -1, -2, 4]]

def raw3352step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 1, -2], ![-1, 0, 1, 0], ![-1, -1, -2, 4]]

def raw3352step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

def raw3353 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw3353step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 1, -2], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, -1, -2, 4]]

def raw3353step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw3354 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def raw3354step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def raw3355 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![2, 0, 2, -4]]

def raw3355step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -1, 0, 0]]

def raw3356 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def raw3356step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def raw3357 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw3358 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw3358step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 1, -2], ![0, -1, -3, 4], ![-1, 0, 1, 0], ![-1, 0, 1, 0]]

def raw3358step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw3359 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![2, 0, -2, 0]]

def raw3359step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 1, -2], ![0, -1, -3, 4], ![-2, 0, 2, 0]]

def raw3359step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -2, 2, 0], ![0, 2, 0, -2], ![1, 0, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical105
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3360 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw3361 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 2, -2, 0], ![2, -1, 3, -4]]

def raw3361step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, -1, -2, 3], ![2, 2, 0, -4]]

def raw3361step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![-2, -2, 0, 4]]

def raw3361step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![0, 1, 2, -3], ![2, 0, 0, -2]]

def raw3362 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw3362step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 1, -2], ![0, -2, -2, 4], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw3362step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw3363 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw3363step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 1, -2], ![-1, 0, 1, 0], ![-1, -1, -2, 4]]

def raw3363step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

def raw3364 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![1, 0, 0, -1], ![1, 1, 1, -3]]

def raw3364step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 1, -2], ![-1, 0, 0, 1], ![-1, -1, -1, 3]]

def raw3364step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def raw3365 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![1, 0, 3, -4], ![1, 1, -2, 0]]

def raw3365step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 1, -2], ![-1, 0, -3, 4], ![-1, -1, 2, 0]]

def raw3365step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw3366 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![1, 1, -2, 0], ![1, 0, 3, -4]]

def raw3366step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 1, -2], ![-1, -1, 2, 0], ![-1, 0, -3, 4]]

def raw3366step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw3367 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw3367step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![0, -1, 1, 0], ![-1, 0, 1, 0], ![-1, -1, -2, 4]]

def raw3367step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw3368 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![2, 1, 1, -4]]

def raw3368step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 0, -1], ![0, 1, -1, 0], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-2, -1, -1, 4]]

def raw3368step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw3369 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 1, -3]]

def raw3369step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 0, -1], ![0, 1, -1, 0], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-2, 0, -1, 3]]

def raw3369step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw3370 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw3371 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 2, 2, -5]]

def raw3371step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, -2, -2, 5]]

def raw3371step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw3372 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw3372step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 0, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, -1, -2, 4]]

def raw3372step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw3373 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, 2, -4]]

def raw3373step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 0, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![0, -2, -2, 4]]

def raw3373step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw3374 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw3374step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 0, -1], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, -2, 3]]

def raw3374step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw3375 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 2, -3]]

def raw3375step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 0, -1], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-2, 1, -2, 3]]

def raw3375step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw3376 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def raw3376step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 0, -1], ![0, -1, 1, 0], ![-1, 1, 1, -1], ![-1, -1, -2, 4]]

def raw3376step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw3377 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 1, 2, -3]]

def raw3377step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 0, -1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![0, -1, -2, 3]]

def raw3377step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw3378 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![1, 0, -2, 1], ![1, 1, 2, -4]]

def raw3378step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 0, -1], ![-1, 0, 2, -1], ![-1, -1, -2, 4]]

def raw3378step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw3379 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw3379step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 0, -1], ![-1, 0, 1, 0], ![-1, -1, -1, 3]]

def raw3379step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw3380 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw3380step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 0, -1], ![-1, 0, -1, 2], ![-1, -1, 1, 1]]

def raw3380step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1]]

def raw3381 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw3381step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, -1, 0], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![-1, -1, -1, 3]]

def raw3381step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw3382 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, 0, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw3382step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw3382step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, -1, 0, 0]]

def raw3383 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, 0, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw3383step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw3383step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw3384 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, 0, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw3384step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![0, -1, 0, 0, 1], ![0, 1, 0, 0, -1], ![2, 0, 0, -1, -1]]

def raw3384step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw3384step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw3385 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw3385step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw3386 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw3386step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, -1, 0], ![0, 0, -1, 1], ![-1, 0, 1, 0], ![-1, -1, 1, 1]]

def raw3386step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw3387 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw3387step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, -1, 0], ![0, 0, -1, 1], ![-1, 0, 0, 1], ![-1, -1, 2, 0]]

def raw3387step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw3388 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 0, 0, 0], ![2, 0, 0, -2]]

def raw3388step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw3388step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, -1, 0, 0]]

def raw3389 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 0, 1, -1], ![2, 0, -1, -1]]

def raw3389step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, -1, 0], ![0, -1, 1, 0], ![0, 0, -1, 1], ![-2, 0, 1, 1]]

def raw3389step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw3390 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def raw3390step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw3391 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def raw3391step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, -1, 0], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-2, 1, 0, 1]]

def raw3391step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical106
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3392 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def raw3393 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw3394 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw3394step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw3395 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw3395step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0]]

def raw3396 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw3396step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, -1, 0, 0]]

def raw3397 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 0, 1, -1], ![2, 0, -2, 0]]

def raw3397step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw3398 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw3398step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw3399 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw3399step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw3400 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw3401 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw3401step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw3402 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, -1, 0]]

def raw3402step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw3403 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw3403step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw3404 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 2, -1, -1], ![2, -1, 0, -1]]

def raw3404step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw3405 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![1, 0, -2, 1], ![1, 1, 1, -3]]

def raw3405step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, -1, 0], ![-1, 0, 2, -1], ![-1, -1, -1, 3]]

def raw3405step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw3406 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw3406step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw3406step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw3407 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![1, 0, 1, -2], ![1, 1, -2, 0]]

def raw3407step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, -1, 0], ![-1, 0, -1, 2], ![-1, -1, 2, 0]]

def raw3407step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw3408 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![1, 1, -2, 0], ![1, 0, 1, -2]]

def raw3408step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, -1, 0], ![-1, -1, 2, 0], ![-1, 0, -1, 2]]

def raw3408step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw3409 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![1, 1, -1, -1], ![1, 0, 0, -1]]

def raw3409step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![2, 0, -1, -1]]

def raw3409step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw3410 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw3410step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1]]

def raw3411 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw3411step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -1, -1, 0]]

def raw3412 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw3413 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def raw3413step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, -2, 1], ![0, -1, 0, 1], ![-1, 0, 2, -1], ![-1, 0, 0, 1]]

def raw3413step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw3414 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw3414step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw3415 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw3415step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw3416 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 1, 1, -2], ![2, 0, -3, 1]]

def raw3416step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 2, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw3417 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 2, -3, 1], ![2, -1, 1, -2]]

def raw3417step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, -2, 1], ![0, -2, 3, -1], ![-2, 1, -1, 2]]

def raw3417step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -2, 2, -1], ![1, 0, 1, -2]]

def raw3418 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, -1, -1, 0]]

def raw3419 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![1, -1, 0, 0], ![1, 2, -2, -1]]

def raw3419step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![2, -1, 0, -1]]

def raw3419step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw3420 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![1, 0, -2, 1], ![1, 1, 0, -2]]

def raw3420step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, -2, 1], ![-1, 0, 2, -1], ![-1, -1, 0, 2]]

def raw3420step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw3421 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw3421step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 2, -1, -1], ![2, -1, 0, -1]]

def raw3421step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 0, -1], ![0, -2, 1, 1], ![-2, 1, 0, 1]]

def raw3421step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw3422 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw3422step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def raw3423 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![1, 0, 1, -2], ![1, 1, -3, 1]]

def raw3423step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, -2, 1], ![-1, 0, -1, 2], ![-1, -1, 3, -1]]

def raw3423step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical107
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3424 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 0, -1, 0]]

def raw3424step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 1, 0], ![0, 2, -1, -1], ![2, -1, -1, 0]]

def raw3424step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, -1, 0], ![0, -2, 1, 1], ![-2, 1, 1, 0]]

def raw3424step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw3425 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 3, -3]]

def raw3426 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -2, 2, -2]]

def raw3427 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![2, -2, 0, 0]]

def raw3428 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def raw3429 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw3429step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 2, -2], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, -3, 4]]

def raw3429step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -3, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw3430 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def raw3430step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 2, -2], ![0, -1, 1, 0], ![-1, 1, -3, 3], ![-1, 0, 0, 1]]

def raw3430step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -3, 3]]

def raw3431 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw3431step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 2, -2], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-2, 2, -2, 2]]

def raw3431step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, 0, -2]]

def raw3432 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 1, -1, -1]]

def raw3433 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def raw3433step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 2, -2], ![0, -1, 0, 1], ![-1, 1, -2, 2], ![-1, 0, 0, 1]]

def raw3433step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw3434 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw3434step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 2, -2], ![0, -1, 0, 1], ![-1, 1, -3, 3], ![-1, 0, 1, 0]]

def raw3434step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -3, 3]]

def raw3435 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![2, -1, 2, -3]]

def raw3435step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 2, -2], ![0, -1, 0, 1], ![-2, 1, -2, 3]]

def raw3435step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -2, -2, 3]]

def raw3436 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, -1, 1, -2]]

def raw3436step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 2, -2], ![0, -1, -1, 2], ![-2, 1, -1, 2]]

def raw3436step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw3437 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw3437step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 2, -2], ![0, -1, -3, 4], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw3437step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw3438 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, 0, -1, 0], ![1, -1, 0, 0]]

def raw3438step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 2, -2], ![0, -1, -3, 4], ![-1, 0, 1, 0], ![-1, 1, 0, 0]]

def raw3438step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw3439 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, 3, -4], ![2, -1, -1, 0]]

def raw3439step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 2, -2], ![0, -1, -3, 4], ![-2, 1, 1, 0]]

def raw3439step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -2, 1, 0]]

def raw3440 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 2, -1, -1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw3441 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 2, -1, -1], ![2, -2, 3, -3]]

def raw3441step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, -2, -1, 3], ![2, 2, -1, -3]]

def raw3441step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![-2, -2, 1, 3]]

def raw3441step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, 0, 1, -3]]

def raw3442 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, -2, 2, -2]]

def raw3442step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 2, -2], ![0, -2, 0, 2], ![-2, 2, -2, 2]]

def raw3442step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, 0, 0, -2]]

def raw3443 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw3443step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 2, -2], ![0, -2, -2, 4], ![-1, 1, 0, 0], ![-1, 1, 0, 0]]

def raw3443step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw3444 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![2, -2, 0, 0]]

def raw3444step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 2, -2], ![0, -2, -2, 4], ![-2, 2, 0, 0]]

def raw3444step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![2, 0, 0, -2]]

def raw3445 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![1, -2, 1, 0], ![1, 2, 1, -4]]

def raw3445step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, -2, 1, 1], ![2, 2, 0, -4]]

def raw3445step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 2, -2], ![0, 2, -1, -1], ![-2, -2, 0, 4]]

def raw3445step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw3446 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![1, -2, 3, -2], ![1, 2, -1, -2]]

def raw3446step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, -2, 3, -1], ![2, 2, -2, -2]]

def raw3446step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 2, -2], ![0, 2, -3, 1], ![-2, -2, 2, 2]]

def raw3446step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 2, -1, -1], ![2, 0, 1, -3]]

def raw3447 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw3447step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 2, -2], ![-1, 1, 0, 0], ![-1, -1, -2, 4]]

def raw3447step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw3448 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![1, -1, 1, -1], ![1, 1, 1, -3]]

def raw3448step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 2, -2], ![-1, 1, -1, 1], ![-1, -1, -1, 3]]

def raw3448step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw3449 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![1, -1, 2, -2], ![1, 1, 0, -2]]

def raw3449step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 2, -2], ![-1, 1, -2, 2], ![-1, -1, 0, 2]]

def raw3449step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw3450 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![1, -1, 3, -3], ![1, 1, -1, -1]]

def raw3450step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 2, -2], ![-1, 1, -3, 3], ![-1, -1, 1, 1]]

def raw3450step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -3, 3]]

def raw3451 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![1, 2, -1, -2], ![1, -2, 3, -2]]

def raw3451step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 2, -2], ![0, -2, -1, 3], ![2, 2, -2, -2]]

def raw3451step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, -2, 2], ![0, 2, 1, -3], ![-2, -2, 2, 2]]

def raw3451step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 2, -1, -1], ![2, 0, 1, -3]]

def raw3452 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![0, 2, 2, -4]]

def raw3452step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![0, -2, -2, 4]]

def raw3452step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw3453 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw3453step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, -1, -2, 4]]

def raw3453step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw3454 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 1, -1], ![1, 1, 1, -3]]

def raw3454step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, -1, 1], ![-1, -1, -1, 3]]

def raw3454step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw3455 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![2, -1, 2, -3]]

def raw3455step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![0, 0, 0, 1, -1], ![0, -1, 0, -1, 2], ![2, 1, 0, 0, -3]]

def raw3455step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, -1, -1, 2], ![2, 1, 0, -3]]

def raw3455step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical108
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3456 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 0, 0, 0], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def raw3456step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![0, 0, 0, -1, 1], ![0, -1, 0, -1, 2], ![2, 1, 0, 1, -4]]

def raw3456step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, -1, -1], ![0, 0, 0, 1, -1], ![0, 1, 0, 1, -2], ![-2, -1, 0, -1, 4]]

def raw3456step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![-2, -1, -1, 4]]

def raw3456step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw3457 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw3457step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, -1, 1], ![-1, -1, 1, 1]]

def raw3457step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw3458 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw3458step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 1, -1], ![0, 0, -2, 2], ![-1, 1, 0, 0], ![-1, -1, 1, 1]]

def raw3458step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw3459 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![0, 1, 3, -4], ![2, -2, 0, 0]]

def raw3460 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def raw3461 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def raw3461step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 1, -1], ![0, -1, 2, -1], ![-1, 1, -3, 3], ![-1, 0, 0, 1]]

def raw3461step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -3, 3]]

def raw3462 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 0, 0, 0], ![2, -1, 2, -3]]

def raw3462step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![0, 0, 1, 0, -1], ![0, -1, -1, 0, 2], ![2, 1, 0, 0, -3]]

def raw3462step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, -1, -1, 2], ![2, 1, 0, -3]]

def raw3462step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def raw3463 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 3, -3]]

def raw3464 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw3464step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 1, -1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-2, 2, -2, 2]]

def raw3464step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw3465 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, -2, 0, 0]]

def raw3465step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 1, -1], ![0, -1, 1, 0], ![0, -1, -2, 3], ![-2, 2, 0, 0]]

def raw3465step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw3466 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![2, -2, -1, 1]]

def raw3467 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 1, 2, -4]]

def raw3467step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-1, 2, 0, -1], ![-1, -1, -2, 4]]

def raw3467step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw3468 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 1, 1, -3]]

def raw3468step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, -1, 1, 0], ![1, 1, -2, 0], ![1, 1, 1, -3]]

def raw3469 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 3, -4]]

def raw3469step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-1, 1, 1, -1], ![-1, 0, -3, 4]]

def raw3469step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw3470 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![0, 1, 2, -3]]

def raw3470step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![0, -1, -2, 3]]

def raw3470step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw3471 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw3471step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-1, 1, -3, 3], ![-1, 0, 1, 0]]

def raw3471step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, -2, 0], ![1, -1, 3, -3]]

def raw3472 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 3, -3], ![1, 0, -2, 1]]

def raw3472step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 1, -3, 3], ![-1, 0, 2, -1]]

def raw3472step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -3, 3]]

def raw3473 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw3473step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 1, -1], ![0, -1, -3, 4], ![-1, 1, 1, -1], ![-1, 0, 1, 0]]

def raw3473step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw3474 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![1, -1, 3, -3], ![1, 1, -2, 0]]

def raw3474step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, -1, 3, -2], ![2, 1, -3, 0]]

def raw3474step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 1, -1], ![0, 1, -3, 2], ![-2, -1, 3, 0]]

def raw3474step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 2, -3]]

def raw3475 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 0, 0], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw3475step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![0, 0, 1, 1, -2], ![0, 0, -2, 0, 2], ![2, 0, 1, -1, -2]]

def raw3475step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, 0, -2], ![0, 0, -1, -1, 2], ![0, 0, 2, 0, -2], ![-2, 0, -1, 1, 2]]

def raw3475step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![0, 2, 0, -2], ![-2, -1, 1, 2]]

def raw3475step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw3476 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 0, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def raw3476step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![0, 0, 1, 1, -2], ![0, 0, -1, -1, 2], ![2, 0, 0, 0, -2]]

def raw3476step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![0, -1, -1, 2], ![2, 0, 0, -2]]

def raw3476step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def raw3477 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 0, 0], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def raw3477step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![2, 0, 1, -3]]

def raw3477step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-2, 0, -1, 3]]

def raw3477step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, -1, 3]]

def raw3477step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw3478 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 0, 0], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw3478step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![2, 0, -1, -1]]

def raw3478step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]

def raw3479 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw3479step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw3479step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def raw3480 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw3480step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, -1, 2, 0]]

def raw3480step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw3481 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 1, -3, 2], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw3482 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def raw3483 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def raw3483step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, -1, 1], ![0, -1, 2, -1], ![0, -1, 0, 1], ![-2, 2, -1, 1]]

def raw3483step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def raw3484 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 0, 1, -1], ![2, -1, -1, 0]]

def raw3484step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw3485 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -2, 1], ![2, -2, 2, -2]]

def raw3485step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def raw3486 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw3486step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw3487 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def raw3487step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, -1, 1], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-2, 2, -1, 1]]

def raw3487step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical109
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3488 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 0, 0]]

def raw3488step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw3489 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 1, -2, 0]]

def raw3489step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, -1, 1], ![0, -1, 0, 1], ![-1, 2, -1, 0], ![-1, -1, 2, 0]]

def raw3489step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw3490 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw3490step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def raw3491 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw3491step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def raw3492 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw3492step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw3493 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -2, 0, 0]]

def raw3493step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw3494 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw3494step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, 1, -2], ![2, -1, -1, 0]]

def raw3494step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw3495 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![1, -1, 2, -2], ![1, 1, -3, 1]]

def raw3495step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, -1, 1], ![-1, 1, -2, 2], ![-1, -1, 3, -1]]

def raw3495step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 2, -2]]

def raw3496 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, 1, -3, 2], ![2, -1, 1, -2]]

def raw3496step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, -2, 2], ![0, -1, 3, -2], ![-2, 1, -1, 2]]

def raw3496step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -2, -1, 2]]

def raw3497 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def raw3498 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, -1, 0, -1]]

def raw3498step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -2, 0, 1]]

def raw3499 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -2, 1], ![2, -2, 1, -1]]

def raw3499step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def raw3500 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 0, 0]]

def raw3500step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw3501 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw3501step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw3502 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw3502step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 1, 0], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw3503 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -1, -2, 1]]

def raw3503step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw3504 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, 2, -3, 1], ![2, -2, 1, -1]]

def raw3504step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, -2, 2], ![0, -2, 3, -1], ![-2, 2, -1, 1]]

def raw3504step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![2, -2, 1, -1]]

def raw3505 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw3505step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw3506 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def raw3506step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw3507 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw3507step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, -2, 2], ![-1, 1, 0, 0], ![-1, -1, 2, 0]]

def raw3507step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw3508 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![1, -1, 1, -1], ![1, 1, -3, 1]]

def raw3508step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, -2, 2], ![-1, 1, -1, 1], ![-1, -1, 3, -1]]

def raw3508step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 1, -1]]

def raw3509 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 3, -3], ![1, -1, 0, 0], ![1, 1, -3, 1]]

def raw3509step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, -3, 3], ![-1, 1, 0, 0], ![-1, -1, 3, -1]]

def raw3509step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw3510 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -3, 2], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw3511 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -3, 2], ![0, 1, 0, -1], ![2, -2, 3, -3]]

def raw3511step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![0, -3, 0, 3], ![2, 2, -1, -3]]

def raw3511step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![0, 3, 0, -3], ![-2, -2, 1, 3]]

def raw3511step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 2, 0, -2], ![1, -2, -2, 3]]

def raw3512 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -3, 2], ![0, 1, 1, -2], ![2, -2, 2, -2]]

def raw3513 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -3, 2], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw3514 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -3, 2], ![0, 1, 3, -4], ![2, -2, 0, 0]]

def raw3514step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![0, -3, 3, 0], ![2, 2, -4, 0]]

def raw3514step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![0, 3, -3, 0], ![-2, -2, 4, 0]]

def raw3514step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 3, -3], ![0, 2, -1, -1], ![2, -2, 0, 0]]

def raw3515 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -3, 2], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def raw3515step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, -3, 1, 2], ![2, 2, 0, -4]]

def raw3515step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 2, -1], ![0, 3, -1, -2], ![-2, -2, 0, 4]]

def raw3515step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 3, -2], ![0, 2, -1, -1], ![2, -1, 0, -1]]

def raw3516 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -3, 2], ![1, -2, 3, -2], ![1, 1, 0, -2]]

def raw3517 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -3, 2], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw3517step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, -3, 0, 3], ![2, 2, 0, -4]]

def raw3517step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -3, 3], ![0, 2, 2, -4], ![1, -2, 0, 1]]

def raw3518 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -3, 2], ![1, -1, 1, -1], ![1, 0, 2, -3]]

def raw3518step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 3, -2], ![-1, 1, -1, 1], ![-1, 0, -2, 3]]

def raw3518step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![0, -1, -2, 3], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw3519 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -3, 2], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def raw3519step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 3, -2], ![-1, 1, -3, 3], ![-1, 0, 0, 1]]

def raw3519step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![0, -1, 0, 1], ![0, 2, 0, -2], ![1, -1, -3, 3]]

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

def raw352 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 1, 2], ![1, 2, -3, 0], ![2, -2, 2, -2]]

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

def raw3520 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -3, 2], ![1, 0, 3, -4], ![1, -1, 0, 0]]

def raw3520step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 0, -1], ![0, -3, 3, 0], ![2, 2, -4, 0]]

def raw3520step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -3, 3], ![0, 2, 2, -4], ![1, -2, 0, 1]]

def raw3521 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def raw3522 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw130 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]

def raw130step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -2, 1], ![1, 3, -4]]

def raw131 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]

def raw131step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]

def raw131step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 2, -1], ![-3, 0, 3]]

def raw131step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, -1, -1]]

def raw132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]

def raw132step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]

def raw132step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

def raw133 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]

def raw133step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]

def raw134 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]

def raw134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]

def raw134step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]

def raw135 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]

def raw135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]

def raw136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]

def raw136step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]

def raw136step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw137 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]

def raw137step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]

def raw137step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def raw138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]

def raw138step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]

def raw138step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw139 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]

def raw139step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]

def raw139step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

def raw140 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]

def raw140step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]

def raw140step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]

def raw141 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]

def raw141step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]

def raw142 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]

def raw142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]

def raw142step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def raw143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]

def raw143step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]

def raw143step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw144 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]

def raw144step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]

def raw144step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]

def raw145 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]

def raw145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]

def raw145step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

def raw146 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]

def raw146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]

def raw146step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

def raw147 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]

def raw147step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![2, 2, -4]]

def raw148 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]

def raw148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, -1, 2], ![-2, 2, 0], ![-2, 1, 1]]

def raw148step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

def raw149 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]

def raw149step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-2, 2, 0], ![-3, 0, 3]]

def raw149step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 3, -3], ![2, 0, -2]]

def raw150 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]

def raw150step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-2, 1, 1], ![-3, 1, 2]]

def raw150step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![1, 1, -2], ![1, 2, -3]]

def raw151 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]

def raw151step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-2, 0, 2], ![-3, 2, 1]]

def raw151step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 2, -2], ![2, 1, -3]]

def raw152 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]

def raw152step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]

def raw157 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]

def raw157step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]

def raw157step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

def raw158 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]

def raw158step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![2, 2, -4]]

def raw159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]

def raw159step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]

def raw159step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1300 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -2, 1], ![2, 0, 0, -2]]

def raw1300step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

def raw1301 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, -1, -1]]

def raw1301step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw1302 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw1302step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw1303 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw1304 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw1304step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![2, -2, 0, 0], ![2, 1, -1, -2]]

def raw1304step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw1305 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw1305step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![2, -2, 1, -1], ![2, 1, -2, -1]]

def raw1305step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, 0, -2], ![1, -1, -2, 2], ![1, 0, 1, -2]]

def raw1306 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw1306step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![2, -2, 0, 0], ![2, 1, -1, -2]]

def raw1306step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 1, 0, -2]]

def raw1307 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -2, 1], ![1, 1, 0, -2], ![1, 0, 0, -1]]

def raw1307step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 1, 0], ![2, -2, 0, 0], ![2, 1, -2, -1]]

def raw1307step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 1, 0, -2]]

def raw1308 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw1309 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw1309step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![2, -1, -1, 0], ![2, 0, 0, -2]]

def raw1309step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def raw1310 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw1311 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, -1, 0]]

def raw1311step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1312 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw1312step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![2, -1, 0, -1], ![2, 0, -1, -1]]

def raw1312step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![2, -1, -1, 0], ![-2, 1, 0, 1], ![-2, 0, 1, 1]]

def raw1312step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw1313 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, -2, 0]]

def raw1313step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![2, -1, 1, -2], ![2, 0, -2, 0]]

def raw1313step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw1314 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw1314step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![2, -1, -1, 0], ![2, 0, 0, -2]]

def raw1314step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw1315 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw1315step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![2, -1, 0, -1], ![2, 0, -1, -1]]

def raw1315step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw1316 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -1, 0], ![1, 1, -1, -1], ![1, 0, 0, -1]]

def raw1316step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 1, 0], ![2, -1, -1, 0], ![2, 0, -1, -1]]

def raw1316step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw1317 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, 0, -1], ![0, 1, -1, 0], ![2, 0, -1, -1]]

def raw1317step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![2, 0, -1, -1], ![2, -1, 0, -1]]

def raw1317step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![2, -1, -1, 0], ![-2, 0, 1, 1], ![-2, 1, 0, 1]]

def raw1317step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw1318 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def raw1318step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw1319 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw1319step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw1320 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw1320step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![2, 0, 0, -2], ![2, -1, -1, 0]]

def raw1320step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def raw1321 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -3, 1]]

def raw1321step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![2, 0, 1, -3], ![2, -1, -2, 1]]

def raw1321step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 2, -2], ![0, 1, -3, 2], ![1, 1, 0, -2]]

def raw1322 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw1322step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![2, 0, -1, -1], ![2, -1, 0, -1]]

def raw1322step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw1323 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw1323step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![2, 0, 0, -2], ![2, -1, -1, 0]]

def raw1323step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw1324 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, 0, -1], ![1, 1, -2, 0], ![1, 0, 0, -1]]

def raw1324step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 1, 0], ![2, 0, -2, 0], ![2, -1, 0, -1]]

def raw1324step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw1325 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, 2, -3], ![2, 1, -4, 1]]

def raw1325step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, 2, -4], ![2, -3, 1]]

def raw1325step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -4, 2]]

def raw1326 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw1326step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 2, 0, 0], ![2, -2, 0, 0], ![2, 0, -1, -1]]

def raw1326step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def raw1327 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw1327step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 2, 0, 0], ![2, -1, -1, 0], ![2, -1, 0, -1]]

def raw1327step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![2, -2, 0, 0], ![-2, 1, 1, 0], ![-2, 1, 0, 1]]

def raw1327step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw1328 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 2, 0, -2], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def raw1328step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 2, 0, 0], ![2, 0, -2, 0], ![2, -2, 1, -1]]

def raw1328step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw1329 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 3, -3, 0], ![2, -1, 1, -2]]

def raw1329step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![2, -3, 1], ![2, 0, -2]]

def raw1329step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]

def raw1330 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![1, -1, 2, -2], ![1, 3, -4, 0]]

def raw1330step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, -1, 3], ![2, 2, -4], ![2, -2, 0]]

def raw1330step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![2, 1, -3], ![-2, -2, 4], ![-2, 2, 0]]

def raw1330step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 2, -3], ![2, -2, 0]]

def raw1331 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![1, 0, 2, -3], ![1, 2, -4, 1]]

def raw1331step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![2, 2, -4], ![2, -3, 1]]

def raw1331step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -4, 2]]

def raw1332 : Matrix (Fin 2) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![2, 2, -2, -2]]

def raw1332step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![2, -2]]

def raw1333 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -2, 3, 1], ![-1, 2, 1, -2], ![3, 0, -4, 1]]

def raw1333step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![3, 1, -4], ![1, -2, 1]]

def raw1333step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-3, -1, 4], ![-1, 2, -1]]

def raw1333step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![1, -3, 2], ![2, -1, -1]]

def raw1334 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 3, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw1334step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, -1, -1]]

def raw1335 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -2, 3, 1], ![0, 3, -1, -2], ![2, -1, -2, 1]]

def raw1335step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![3, -1, -2], ![1, -2, 1]]

def raw1335step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![2, -3, 1], ![-3, 1, 2], ![-1, 2, -1]]

def raw1335step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]

def raw1336 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -2, 3, 1], ![2, -1, 1, -2], ![0, 3, -4, 1]]

def raw1336step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![3, 1, -4], ![1, -2, 1]]

def raw1336step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -2, 0], ![2, 1, -3], ![-3, -1, 4], ![-1, 2, -1]]

def raw1336step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![1, -3, 2], ![2, -1, -1]]

def raw1337 : Matrix (Fin 2) (Fin 4) ℤ := ![![-2, -2, 3, 1], ![2, 2, -3, -1]]

def raw1337step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![3, -3], ![1, -1]]

def raw1337step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]

def raw1338 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

def raw1339 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

def raw1340 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![2, 2, -4]]

def raw1341 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]

def raw1342 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

def raw1342step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

def raw1343 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1344 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]

def raw1345 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 2, -2], ![2, -2, 0], ![1, 0, -1]]

def raw1345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

def raw1346 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 2, -2], ![3, -2, -1]]

def raw1346step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![0, -2, 2], ![-3, 2, 1]]

def raw1346step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -4, 2]]

def raw1347 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

def raw1348 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw1348step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]

def raw1349 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, -1, 0], ![2, 1, -3]]

def raw1349step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]

def raw1350 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]

def raw1350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]

def raw1351 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![2, 0, -2]]

def raw1351step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def raw1352 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]

def raw1352step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]

def raw1353 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]

def raw1354 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 2, -3], ![2, -2, 0]]

def raw1355 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![2, -2, 0], ![1, 2, -3]]

def raw1355step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 2, -3], ![2, -2, 0]]

def raw1356 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

def raw1357 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

def raw1358 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def raw1358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -3, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]

def raw1358step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]

def raw1359 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![1, -1, 0], ![2, 0, -2]]

def raw1359step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -3, 2], ![-1, 1, 0], ![-2, 0, 2]]

def raw1359step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]

def raw1360 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]

def raw1360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -3, 2], ![-1, 0, 1], ![-1, 1, 0], ![-1, 0, 1]]

def raw1360step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]

def raw1361 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![1, 0, -1], ![2, -1, -1]]

def raw1361step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -3, 2], ![-1, 0, 1], ![-2, 1, 1]]

def raw1361step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]

def raw1362 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![2, -2, 0], ![1, 1, -2]]

def raw1362step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![1, 1, -2], ![2, -2, 0]]

def raw1363 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw1364 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 4, -3], ![1, -1, 0], ![2, -1, -1]]

def raw1365 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 4, -3], ![2, -2, 0], ![1, 0, -1]]

def raw1365step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 4, -3], ![1, 0, -1], ![2, -2, 0]]

def raw1366 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 4, -3], ![3, -2, -1]]

def raw1366step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![1, -4, 3], ![-3, 2, 1]]

def raw1366step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 3, -4], ![2, -4, 2]]

def raw1367 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]

def raw1368 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

def raw1369 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 3, -4]]

def raw1370 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

def raw1371 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

def raw1372 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def raw1373 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def raw1374 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 3, -3], ![2, 0, -2]]

def raw1375 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0], ![1, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1376 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![1, -1, 0], ![1, 4, -5]]

def raw1377 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![1, 0, -1], ![1, 3, -4]]

def raw1378 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![1, 1, -2], ![1, 2, -3]]

def raw1379 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw1379step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw1380 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw1380step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw1381 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw1381step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw1382 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, 1, -1], ![2, 1, -3]]

def raw1382step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![4, 0, -1, -3]]

def raw1382step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![4, -1, -3]]

def raw1382step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![1, 1, -2]]

def raw1383 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw1383step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw1383step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw1384 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, 2, -2], ![2, 0, -2]]

def raw1384step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![2, 0, -2]]

def raw1385 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw1385step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw1386 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![1, -1, 0], ![1, 3, -4]]

def raw1386step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 0, -1, 3], ![4, 0, 0, -4]]

def raw1386step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, -1, 3], ![4, 0, -4]]

def raw1386step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 4, -4], ![1, -2, 1]]

def raw1387 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![1, 0, -1], ![1, 2, -3]]

def raw1387step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 0, 0, 2], ![4, 0, -1, -3]]

def raw1387step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![4, -1, -3]]

def raw1387step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![1, 1, -2]]

def raw1388 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2]]

def raw1388step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![1, 1, -2], ![1, 1, -2]]

def raw1389 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![2, 2, -4]]

def raw1389step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![4, 0, -4]]

def raw1389step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![4, -4]]

def raw1389step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![2, -2]]

def raw1390 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]

def raw1390step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

def raw1391 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]

def raw1391step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def raw1392 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, -1, 1], ![2, 2, -4]]

def raw1392step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![2, 2, -4]]

def raw1393 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2]]

def raw1393step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw1394 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3]]

def raw1394step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw1395 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2]]

def raw1395step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw1396 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 0, 0], ![2, 1, -3]]

def raw1396step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 0, 1], ![4, -1, 0, -3]]

def raw1396step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![4, -1, -3]]

def raw1396step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![1, 1, -2]]

def raw1397 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2]]

def raw1397step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw1398 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw1399 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def raw1400 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

def raw1401 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw1402 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw1403 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw1404 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![0, -1, 1], ![2, 0, -2]]

def raw1404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

def raw1405 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1]]

def raw1405step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def raw1406 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def raw1407 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1408 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]

def raw1408step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw1409 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def raw1410 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw1411 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw1412 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 3, -3], ![2, -2, 0]]

def raw1413 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, -2, 1], ![1, 3, -4]]

def raw1414 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2]]

def raw1414step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw1415 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![0, 2, -2]]

def raw1415step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw1416 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw1417 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw1418 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1]]

def raw1418step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw1419 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, 2, -3], ![1, -1, 0]]

def raw1419step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw1420 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![2, 1, -3]]

def raw1420step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![4, -1, -3]]

def raw1420step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![1, 1, -2]]

def raw1421 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]

def raw1421step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def raw1422 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, -1, 1], ![2, 1, -3]]

def raw1422step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 2, -2], ![2, 1, -3]]

def raw1423 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 0, 0], ![2, 0, -2]]

def raw1423step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![2, 0, -2]]

def raw1424 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw1424step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def raw1425 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw1425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw1426 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 1, -1], ![2, -1, -1]]

def raw1426step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def raw1427 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

def raw1428 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 2, -2], ![2, -2, 0]]

def raw1429 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -2, 1], ![1, 2, -3]]

def raw1430 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]

def raw1430step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def raw1431 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]

def raw1431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw1432 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def raw1433 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw1433step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw1434 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0]]

def raw1434step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def raw1435 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![2, 0, -2]]

def raw1436 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, -2, 1], ![1, 1, -2]]

def raw1437 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw1438 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0]]

def raw1438step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw1439 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, -1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1440 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 4, -4], ![1, -2, 1], ![1, 0, -1]]

def raw1441 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

def raw1442 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 4, -4], ![2, -2, 0]]

def raw1443 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![1, -2, 1], ![1, 4, -5]]

def raw1444 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![1, -1, 0], ![0, 1, -1], ![1, 2, -3]]

def raw1444step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw1445 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![1, -1, 0], ![1, 1, -2], ![0, 2, -2]]

def raw1445step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def raw1446 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![1, -1, 0], ![1, 3, -4]]

def raw1446step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, -1, 3], ![4, 0, -4]]

def raw1446step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 4, -4], ![1, -2, 1]]

def raw1447 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![1, 0, -1], ![1, 2, -3]]

def raw1447step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![4, -1, -3]]

def raw1447step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![1, 1, -2]]

def raw1448 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![1, 1, -2], ![0, 2, -2], ![1, -1, 0]]

def raw1448step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def raw1449 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![1, 1, -2], ![1, 1, -2]]

def raw1450 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![1, 2, -3], ![1, 0, -1]]

def raw1450step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![4, -3, -1]]

def raw1450step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![1, 1, -2]]

def raw1451 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![1, 3, -4], ![1, -1, 0]]

def raw1451step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![4, -4, 0]]

def raw1451step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 4, -4], ![1, -2, 1]]

def raw1452 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![1, 4, -5], ![1, -2, 1]]

def raw1452step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![1, -2, 1], ![1, 4, -5]]

def raw1453 : Matrix (Fin 2) (Fin 4) ℤ := ![![-2, -2, 5, -1], ![2, 2, -5, 1]]

def raw1453step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![5, -5], ![-1, 1]]

def raw1453step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![2, -2], ![2, -2]]

def raw1454 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -2, 5], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw1454step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw1455 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -2, 5], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw1455step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw1456 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -2, 5], ![0, 0, 2, -2], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw1456step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw1457 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -2, 5], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 2, -3]]

def raw1457step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![-2, 0, 0, 2], ![5, -1, -1, -3]]

def raw1457step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -3, 5], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw1458 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -2, 5], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 0, 1, -2]]

def raw1458step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw1459 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -2, 5], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw1459step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, 0, -2]]

def raw1460 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -2, 5], ![0, 1, 2, -3], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw1460step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![-2, 2, 0, 0], ![5, -3, -1, -1]]

def raw1460step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -3, 5], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def raw1461 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -1, -2]]

def raw1462 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def raw1463 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw1464 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, 0, -3]]

def raw1465 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -1, -2]]

def raw1466 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def raw1467 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def raw1468 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw1469 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2], ![1, 1, 0, -2]]

def raw1470 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw1471 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1472 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw1473 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw1474 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw1475 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, -1, -2]]

def raw1476 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def raw1477 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, 0, 0, -2]]

def raw1478 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw1479 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, 0, -2, 0]]

def raw1480 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, -1, -2]]

def raw1481 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -2, -1]]

def raw1482 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def raw1483 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw1483step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def raw1484 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw1485 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw1485step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw1486 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, -1, 0], ![2, 1, 0, -3]]

def raw1486step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, -1, 1, 1], ![-1, 2, -1, 0], ![4, -1, 0, -3]]

def raw1486step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![1, 1, -1, -1], ![1, -2, 1, 0], ![-4, 1, 0, 3]]

def raw1486step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw1487 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw1488 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

def raw1489 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw1490 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw1491 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -2, 0]]

def raw1492 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 1, -1, -1], ![1, 0, 0, -1]]

def raw1492step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw1493 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![2, 1, -1, -2]]

def raw1493step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, -1, 1, 1], ![-1, 2, 0, -1], ![4, -1, -1, -2]]

def raw1493step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def raw1494 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![2, 1, -2, -1]]

def raw1495 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw1496 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, -2, 0], ![2, 0, 1, -3]]

def raw1497 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw1498 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw1499 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def raw1500 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw1501 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw1502 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, 1, -3], ![2, 0, -2, 0]]

def raw1503 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 0, -1, 0], ![1, 2, 0, -3]]

def raw1503step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, -1, 0, 2], ![-1, 2, -1, 0], ![4, -1, 0, -3]]

def raw1503step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, 1, 0, -2], ![1, -2, 1, 0], ![-4, 1, 0, 3]]

def raw1503step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -2, 0, 1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1504 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 0, 0, -1], ![1, 2, -1, -2]]

def raw1504step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, -1, 0, 2], ![-1, 2, 0, -1], ![4, -1, -1, -2]]

def raw1504step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw1505 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 0, 1, -2], ![1, 2, -2, -1]]

def raw1506 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 1, -2, 0], ![1, 1, 1, -3]]

def raw1507 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def raw1508 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 1, 0, -2], ![1, 1, -1, -1]]

def raw1508step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def raw1509 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 1, 1, -3], ![1, 1, -2, 0]]

def raw1509step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 1, -2, 0], ![1, 1, 1, -3]]

def raw1510 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 2, -2, -1], ![1, 0, 1, -2]]

def raw1510step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 0, 1, -2], ![1, 2, -2, -1]]

def raw1511 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 2, -1, -2], ![1, 0, 0, -1]]

def raw1511step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, -1, 2, 0], ![-1, 2, -1, 0], ![4, -1, -2, -1]]

def raw1511step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw1512 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 3, -2], ![0, 1, -1, 0], ![2, 1, -1, -2]]

def raw1512step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, -1, 1, 1], ![-1, 3, -1, -1], ![4, -2, 0, -2]]

def raw1512step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![1, 1, -1, -1], ![1, -3, 1, 1], ![-4, 2, 0, 2]]

def raw1512step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -2, 0, 2], ![0, 2, 2, -4], ![1, 1, -3, 1]]

def raw1513 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 3, -2], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def raw1513step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, -1, 1, 1], ![-1, 3, 0, -2], ![4, -2, -1, -1]]

def raw1513step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 3, -2, -1], ![1, -1, 1, -1]]

def raw1514 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 3, -2], ![0, 2, -2, 0], ![2, 0, 0, -2]]

def raw1515 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 3, -2], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw1516 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 3, -2], ![0, 2, 0, -2], ![2, 0, -2, 0]]

def raw1517 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 3, -2], ![1, 0, -1, 0], ![1, 2, -1, -2]]

def raw1517step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, -1, 0, 2], ![-1, 3, -1, -1], ![4, -2, 0, -2]]

def raw1517step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, 1, 0, -2], ![1, -3, 1, 1], ![-4, 2, 0, 2]]

def raw1517step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -2, 1, 1], ![0, 2, 2, -4], ![1, 1, -3, 1]]

def raw1518 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 3, -2], ![1, 0, 0, -1], ![1, 2, -2, -1]]

def raw1518step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, -1, 0, 2], ![-1, 3, 0, -2], ![4, -2, -1, -1]]

def raw1518step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, -1, 2, -1], ![0, 3, -2, -1], ![1, 0, 1, -2]]

def raw1519 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 3, -2], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def raw1520 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 2, 0, -3]]

def raw1520step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 0, 1], ![0, 1, 0, -1], ![1, 0, 2, -3], ![1, 1, -1, -1]]

def raw1521 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, -1, 1], ![0, 1, 1, -2], ![2, 0, 1, -3]]

def raw1521step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, 1, -2]]

def raw1522 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw1522step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 0, 1], ![0, 1, 2, -3], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw1523 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, -1, 1], ![0, 2, 1, -3], ![2, -1, 1, -2]]

def raw1523step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 2, -1], ![-1, -1, 1, 1], ![4, 1, -3, -2]]

def raw1523step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -2, -3, 4]]

def raw1524 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 2, -3]]

def raw1524step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 1, 0, 0], ![-1, 0, 0, -1, 2], ![4, 0, -1, 0, -3]]

def raw1524step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![-1, 0, -1, 2], ![4, -1, 0, -3]]

def raw1524step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw1525 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 0, 0], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def raw1525step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 1, 0], ![-1, 0, 1, 0], ![4, 0, -2, -2]]

def raw1525step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![4, -2, -2]]

def raw1525step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw1526 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 0, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw1526step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, 0, 1], ![-1, 0, -1, 2], ![4, 0, 0, -4]]

def raw1526step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, -1, 2], ![4, 0, -4]]

def raw1526step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 4, -4], ![1, -2, 1]]

def raw1527 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 0, 0], ![1, 0, 1, -2], ![1, 1, 0, -2]]

def raw1527step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, 0, 1], ![-1, 0, 1, 0], ![4, 0, -2, -2]]

def raw1527step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![4, -2, -2]]

def raw1527step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw1528 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 0, 0], ![1, 0, 2, -3], ![1, 1, -1, -1]]

def raw1528step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, 0, 1], ![-1, 0, 2, -1], ![4, 0, -3, -1]]

def raw1528step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![4, -3, -1]]

def raw1528step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2]]

def raw1529 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, -1, 1, 0], ![0, 1, 0, -1], ![2, 1, -1, -2]]

def raw1529step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -1, -2]]

def raw1530 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, -1, 1, 0], ![1, 0, -1, 0], ![1, 2, 0, -3]]

def raw1530step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, 0, -3]]

def raw1531 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, -1, 1, 0], ![1, 0, 0, -1], ![1, 2, -1, -2]]

def raw1531step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -1, -2]]

def raw1532 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, -1, 2, -1], ![0, 1, -1, 0], ![2, 1, -1, -2]]

def raw1532step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, -1, -2]]

def raw1533 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, -1, 2, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def raw1533step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def raw1534 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, -1, 2, -1], ![0, 2, -2, 0], ![2, 0, 0, -2]]

def raw1534step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, 0, 0, -2]]

def raw1535 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw1535step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1536 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -2, 0]]

def raw1536step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, 0, -2, 0]]

def raw1537 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, -1, 2, -1], ![1, 0, -1, 0], ![1, 2, -1, -2]]

def raw1537step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, -1, -2]]

def raw1538 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, -1, 2, -1], ![1, 0, 0, -1], ![1, 2, -2, -1]]

def raw1538step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -2, -1]]

def raw1539 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, -1, 2, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def raw1539step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def raw1540 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw1540step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw1540step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw1541 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw1541step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw1541step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw1542 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 0, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw1542step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw1542step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw1543 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![2, 1, -1, -2]]

def raw1543step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![-1, 0, 0, 0, 1], ![-1, 1, 1, 0, -1], ![4, -1, -1, 0, -2]]

def raw1543step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 0, 1], ![-1, 1, 1, -1], ![4, -1, -1, -2]]

def raw1543step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, 1, -1, -1]]

def raw1544 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, 1, -2, -1]]

def raw1544step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 2, -2, -1]]

def raw1545 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw1545step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw1546 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw1546step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw1547 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

def raw1547step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def raw1548 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, -1, 1, -2]]

def raw1549 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -1, 0, -1]]

def raw1549step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw1550 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, -1, -1, 0]]

def raw1551 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 2, 0, -3]]

def raw1552 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 2, -1, -2]]

def raw1553 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 2, -2, -1]]

def raw1554 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw1554step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 1, 0, -2]]

def raw1555 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw1555step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def raw1556 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, 1, -2], ![1, 1, -2, 0]]

def raw1556step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw1557 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 1, -2, 0], ![1, 0, 1, -2]]

def raw1557step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw1558 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, 1, -1, -2]]

def raw1558step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 0, 1], ![-1, 1, 1, -1], ![4, -1, -1, -2]]

def raw1558step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, 1, -1, -1]]

def raw1559 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 2, -2, 0], ![2, -1, 0, -1]]

def raw1560 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 2, -2, -1]]

def raw1561 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 0, 1, -1], ![2, 0, 0, -2]]

def raw1561step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw1562 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 0, 2, -2], ![2, 0, -1, -1]]

def raw1562step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw1563 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 2, -3]]

def raw1564 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 1, -2]]

def raw1564step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -1, -2]]

def raw1565 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def raw1565step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw1566 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw1566step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw1567 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def raw1567step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1568 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw1568step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw1569 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 0, 1, -1], ![2, 0, -1, -1]]

def raw1569step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw1570 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 0, 2, -2], ![2, 0, -2, 0]]

def raw1570step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw1571 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def raw1571step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -1, -2]]

def raw1572 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def raw1572step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw1573 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, -1, -1, 0]]

def raw1574 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def raw1575 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw1575step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw1576 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw1577 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 1, -2, 0]]

def raw1578 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw1578step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw1579 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw1579step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw1580 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 0, -1, 0]]

def raw1580step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw1581 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw1581step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw1582 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw1582step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, -1, -1, 0]]

def raw1583 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def raw1584 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw1585 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw1586 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw1586step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw1587 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw1587step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw1588 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw1589 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw1590 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw1591 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def raw1592 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, -1, 2, -2]]

def raw1592step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def raw1593 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, -1, 2, -3]]

def raw1593step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 2, -1], ![-1, 1, -2, 2], ![4, -1, 0, -3]]

def raw1593step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -2, 2, -1]]

def raw1594 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw1594step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw1595 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw1595step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw1596 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw1597 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, -1, 2, -2]]

def raw1597step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw1598 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, -1, 1, -1]]

def raw1598step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw1599 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -1, 1, -2]]

def raw1599step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 2, -1], ![-1, 1, -1, 1], ![4, -1, -1, -2]]

def raw1599step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw160 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]

def raw160step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]

def raw160step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw161 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]

def raw161step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, 1, 0], ![-3, 0, 3]]

def raw161step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw162 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]

def raw162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]

def raw162step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw163 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]

def raw163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]

def raw163step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

def raw164 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]

def raw164step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, 0, 1], ![-3, 1, 2]]

def raw164step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw165 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]

def raw165step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]

def raw165step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]

def raw166 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]

def raw166step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]

def raw167 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]

def raw167step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]

def raw167step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def raw168 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]

def raw168step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def raw169 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]

def raw169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]

def raw169step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw170 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]

def raw170step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]

def raw170step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def raw171 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]

def raw171step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]

def raw171step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]

def raw172 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]

def raw172step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 2, -1], ![-3, 0, 3]]

def raw172step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, -1, -1]]

def raw173 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def raw173step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]

def raw173step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw174 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]

def raw174step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]

def raw174step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw175 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]

def raw175step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]

def raw175step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw176 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]

def raw176step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![2, 0, -2]]

def raw176step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![-2, 1, 1], ![-2, 0, 2]]

def raw176step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![1, 1, -2]]

def raw177 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -3, 1], ![2, 1, -3]]

def raw177step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![2, 2, -4]]

def raw178 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]

def raw178step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -2, -2], ![-2, 2, 0], ![-2, 0, 2]]

def raw178step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![2, 0, -2]]

def raw179 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![2, -1, -1]]

def raw179step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -2, -2], ![-2, 1, 1], ![-2, 1, 1]]

def raw179step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![1, 1, -2], ![1, 1, -2]]

def raw180 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 2, 2], ![4, -2, -2]]

def raw180step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![2, -2]]

def raw181 : Matrix (Fin 2) (Fin 4) ℤ := ![![-4, 2, 3, -1], ![4, -2, -3, 1]]

def raw181step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![3, -3], ![-1, 1]]

def raw181step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![2, -2], ![3, -3]]

def raw182 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 3, 1], ![4, -3, -1]]

def raw182step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![3, -3], ![1, -1]]

def raw182step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]

def raw183 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![0, 0], ![1, -1], ![1, -1], ![3, -3]]

def raw183step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![3, -3]]

def raw184 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![0, 0], ![1, -1], ![2, -2], ![2, -2]]

def raw184step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]

def raw185 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![0, 0], ![1, -1], ![4, -4]]

def raw185step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![4, -4]]

def raw186 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![0, 0], ![2, -2], ![3, -3]]

def raw186step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![2, -2], ![3, -3]]

def raw187 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]

def raw188 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![3, -3]]

def raw189 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]

def raw190 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![4, -4]]

def raw191 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![2, -2], ![3, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1600 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def raw1601 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw1601step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw1602 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw1603 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, -1, 1, -1]]

def raw1603step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw1604 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, -1, 0, -1]]

def raw1604step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw1605 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw1606 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw1607 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, -1, 0, 0]]

def raw1607step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw1608 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, 1, -3], ![2, -1, -1, 0]]

def raw1608step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 2, -1], ![-1, 1, 1, -1], ![4, -1, -3, 0]]

def raw1608step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw1609 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 2, 1, -4]]

def raw1609step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, -1, 2], ![-1, 1, -1, 1], ![4, -1, 1, -4]]

def raw1609step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -4, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw1610 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 2, 0, -3]]

def raw1610step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, -1, 2], ![-1, 1, 0, 0], ![4, -1, 0, -3]]

def raw1610step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw1611 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 2, -1, -2]]

def raw1611step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, -1, 2], ![-1, 1, 1, -1], ![4, -1, -1, -2]]

def raw1611step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw1612 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![1, -1, 2, -2], ![1, 2, -2, -1]]

def raw1612step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, -1, 2], ![-1, 1, 2, -2], ![4, -1, -2, -1]]

def raw1612step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 2, -2, -1]]

def raw1613 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw1613step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, 0, 1], ![-1, 1, -1, 1], ![4, -1, 0, -3]]

def raw1613step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw1614 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw1614step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw1615 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw1615step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw1616 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![1, 1, -1, -1], ![1, 0, 1, -2]]

def raw1616step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw1617 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, -1, 0, -1]]

def raw1617step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 2, -2, 0], ![2, -1, 0, -1]]

def raw1618 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 2, -2, -1]]

def raw1618step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 2, -2, -1]]

def raw1619 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def raw1620 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw1620step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw1621 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw1621step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw1622 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw1622step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, -1, -1, 0]]

def raw1623 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def raw1623step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def raw1624 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw1624step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw1625 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw1626 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw1626step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw1627 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw1627step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw1628 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw1629 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![2, 0, -2, 0]]

def raw1629step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def raw1630 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw1631 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1632 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![2, -1, 1, -2]]

def raw1633 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw1634 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, -1, 0, -1]]

def raw1634step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw1635 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw1636 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw1637 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![2, -1, -1, 0]]

def raw1637step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 2, -1], ![-1, 2, 0, -1], ![4, -2, -2, 0]]

def raw1637step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw1638 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 2, 0, -3]]

def raw1639 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 2, -1, -2]]

def raw1639step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, -1, 2], ![-1, 2, 0, -1], ![4, -2, 0, -2]]

def raw1639step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, 0, 1, -2], ![1, -2, 0, 1], ![-4, 2, 0, 2]]

def raw1639step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw1640 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![1, -1, 1, -1], ![1, 2, -2, -1]]

def raw1640step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, -1, 2], ![-1, 2, 1, -2], ![4, -2, -1, -1]]

def raw1640step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![2, 1, -2, -1]]

def raw1641 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw1641step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

def raw1642 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw1642step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, 0, 1], ![-1, 2, 0, -1], ![4, -2, -1, -1]]

def raw1642step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw1643 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![1, 0, 1, -2], ![1, 1, -2, 0]]

def raw1643step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw1644 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![1, 1, -2, 0], ![1, 0, 1, -2]]

def raw1644step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw1645 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![1, 1, 0, -2], ![1, 0, -1, 0]]

def raw1645step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

def raw1646 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![1, 2, -2, -1], ![1, -1, 1, -1]]

def raw1646step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, 2, -1], ![-1, 2, -2, 1], ![4, -2, -1, -1]]

def raw1646step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![2, 1, -2, -1]]

def raw1647 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![1, 2, 0, -3], ![1, -1, -1, 1]]

def raw1647step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 2, 0, -3]]

def raw1648 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 3, -3], ![0, 2, -2, 0], ![2, -1, 0, -1]]

def raw1649 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 3, -3], ![1, -1, 0, 0], ![1, 2, -2, -1]]

def raw1649step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, -1, 2], ![-1, 3, 0, -2], ![4, -3, 0, -1]]

def raw1649step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, 0, 1, -2], ![1, -3, 0, 2], ![-4, 3, 0, 1]]

def raw1649step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 3, -4], ![0, 2, -3, 1], ![1, -2, 0, 1]]

def raw1650 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, -1, 0], ![0, 0, 1, -1], ![2, 0, 1, -3]]

def raw1650step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 0, 0], ![-1, -1, 1, 1], ![4, 0, -1, -3]]

def raw1650step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 1, -1]]

def raw1651 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, -1, 0], ![0, 0, 2, -2], ![2, 0, 0, -2]]

def raw1651step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw1652 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw1653 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 2, -3]]

def raw1654 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 3, -4]]

def raw1654step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![-1, -1, -1, 3], ![4, 0, 0, -4]]

def raw1654step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -2, 2], ![0, 0, 4, -4], ![1, 1, -1, -1]]

def raw1655 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw1655step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, 0, -3]]

def raw1656 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw1656step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def raw1657 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def raw1657step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -1, -2]]

def raw1658 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 2, -3]]

def raw1658step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![-1, -1, 0, 2], ![4, 0, -1, -3]]

def raw1658step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![1, -1, -1, 1], ![1, 1, 0, -2], ![-4, 0, 1, 3]]

def raw1658step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, -2, 1], ![1, 0, 3, -4]]

def raw1659 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -1, 1, -2]]

def raw1659step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![-1, -1, 1, 1], ![4, 0, -2, -2]]

def raw1659step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![1, -1, -1, 1], ![1, 1, -1, -1], ![-4, 0, 2, 2]]

def raw1659step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -1, -1, 1]]

def raw1660 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw1660step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw1661 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw1662 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, -1, 0, -1]]

def raw1662step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![-1, -1, 2, 0], ![4, 0, -3, -1]]

def raw1662step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw1663 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1664 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw1664step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![-1, -1, 0, 2], ![4, 0, 0, -4]]

def raw1664step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 4, -4], ![0, 1, -2, 1], ![1, -1, -1, 1]]

def raw1665 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 1, 1, -3]]

def raw1665step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![-1, -1, 1, 1], ![4, 0, -1, -3]]

def raw1665step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 1, -1], ![1, 1, -1, -1], ![-4, 0, 1, 3]]

def raw1665step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def raw1666 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, -1, 0], ![1, -1, 2, -2], ![1, 1, 0, -2]]

def raw1666step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![-1, -1, 2, 0], ![4, 0, -2, -2]]

def raw1666step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 1, -1], ![1, 1, -2, 0], ![-4, 0, 2, 2]]

def raw1666step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw1667 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def raw1667step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![-1, -1, -1, 3], ![4, 0, 0, -4]]

def raw1667step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 4, -4], ![0, 1, -2, 1], ![1, 0, -1, 0]]

def raw1668 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 2, -3]]

def raw1668step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![-1, -1, 0, 2], ![4, 0, -1, -3]]

def raw1668step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw1669 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, -1, 0], ![1, 0, 1, -2], ![1, 0, 1, -2]]

def raw1669step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw1670 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 0, -1], ![0, 0, 0, 0], ![1, 0, -1, 0], ![1, 0, 2, -3]]

def raw1670step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 1, 0, 0, 0], ![-1, 0, 0, -1, 2], ![4, -1, 0, 0, -3]]

def raw1670step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![-1, 0, -1, 2], ![4, -1, 0, -3]]

def raw1670step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw1671 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 0, -1], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw1671step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw1672 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 0, -1], ![0, 0, 2, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw1672step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw1673 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 0, -1], ![0, 0, 2, -2], ![2, 0, -1, -1]]

def raw1673step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw1674 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw1674step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, 0, -3]]

def raw1675 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 0, -1], ![0, 1, -1, 0], ![2, -1, 2, -3]]

def raw1675step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![-1, 0, -1, 2], ![4, -1, 0, -3]]

def raw1675step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![1, -1, -1, 1], ![1, 0, 1, -2], ![-4, 1, 0, 3]]

def raw1675step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, -2, 1], ![1, 0, 3, -4]]

def raw1676 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 2, -3]]

def raw1676step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 2, 0, -3]]

def raw1677 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw1677step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 1, 0, -2]]

def raw1678 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw1678step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 2, -1, -2]]

def raw1679 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, -1, 2, -2]]

def raw1679step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 2, -1, -2]]

def raw1680 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw1680step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw1681 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw1681step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw1682 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, -1, 1, -1]]

def raw1682step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw1683 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def raw1683step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw1684 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw1684step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw1685 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 0, -1], ![0, 1, 2, -3], ![2, -1, -1, 0]]

def raw1685step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![-1, 0, 2, -1], ![4, -1, -3, 0]]

def raw1685step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw1686 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def raw1686step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![-1, 0, -1, 2], ![4, -1, 1, -4]]

def raw1686step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -4, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw1687 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw1687step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![-1, 0, 0, 1], ![4, -1, 0, -3]]

def raw1687step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw1688 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def raw1688step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw1689 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 1, -1, -1]]

def raw1689step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![-1, 0, 2, -1], ![4, -1, -2, -1]]

def raw1689step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw1690 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 0, -1], ![1, -1, 3, -3], ![1, 1, -2, 0]]

def raw1690step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![-1, 0, 3, -2], ![4, -1, -3, 0]]

def raw1690step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 1, -1], ![1, 0, -3, 2], ![-4, 1, 3, 0]]

def raw1690step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, -3, 1], ![1, 0, 3, -4]]

def raw1691 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 2, -3]]

def raw1691step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![-1, 0, -1, 2], ![4, -1, 0, -3]]

def raw1691step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw1692 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw1692step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw1693 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 0, 0, -1]]

def raw1693step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw1694 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 0, -1], ![1, 0, 2, -3], ![1, 0, -1, 0]]

def raw1694step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![-1, 0, 2, -1], ![4, -1, -3, 0]]

def raw1694step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw1695 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 1, -2], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def raw1695step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![-1, 1, -1, 1], ![4, -2, 0, -2]]

def raw1695step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![1, -1, -1, 1], ![1, -1, 1, -1], ![-4, 2, 0, 2]]

def raw1695step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -1, -1, 1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1696 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw1697 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![2, -1, -1, 0]]

def raw1697step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![-1, 1, 1, -1], ![4, -2, -2, 0]]

def raw1697step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def raw1698 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def raw1699 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw1699step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw1700 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw1701 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 1, -2], ![1, -1, 2, -2], ![1, 1, -2, 0]]

def raw1702 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw1702step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw1703 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 1, -2], ![1, 0, 1, -2], ![1, 0, -1, 0]]

def raw1703step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw1704 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def raw1705 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw1705step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![-1, 2, 0, -1], ![4, -3, 0, -1]]

def raw1705step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 1, -1], ![1, -2, 0, 1], ![-4, 3, 0, 1]]

def raw1705step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def raw1706 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw1707 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 2, -3], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw1707step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![-1, 2, -1, 0], ![4, -3, 0, -1]]

def raw1707step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 0, 0], ![1, -2, 1, 0], ![-4, 3, 0, 1]]

def raw1707step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, 0, 3, -4]]

def raw1708 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 2, -3], ![1, 0, 0, -1], ![1, 0, -1, 0]]

def raw1708step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![-1, 2, 0, -1], ![4, -3, -1, 0]]

def raw1708step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 0, 0], ![1, -2, 0, 1], ![-4, 3, 1, 0]]

def raw1708step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, 0, 3, -4]]

def raw1709 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw1709step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![-1, 3, 0, -2], ![4, -4, 0, 0]]

def raw1709step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 1, -1], ![1, -3, 0, 2], ![-4, 4, 0, 0]]

def raw1709step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 4, -4], ![0, 2, -3, 1], ![1, -1, -1, 1]]

def raw1710 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 3, -4], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw1710step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![-1, 3, -1, -1], ![4, -4, 0, 0]]

def raw1710step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 4, -4], ![1, 1, -2, 0]]

def raw1711 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw1711step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![-1, -2, 0, 3], ![4, 0, 0, -4]]

def raw1711step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![1, 2, 0, -3], ![-4, 0, 0, 4]]

def raw1711step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 4, -4], ![0, 2, -3, 1], ![1, -2, 0, 1]]

def raw1712 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 2, -3]]

def raw1713 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, -2, 0], ![1, -1, 2, -2], ![1, 0, 1, -2]]

def raw1714 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, -2, 0], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def raw1714step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![-1, -2, 3, 0], ![4, 0, -3, -1]]

def raw1714step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -2, 3, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw1715 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw1715step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![-1, -1, 0, 2], ![4, -1, 0, -3]]

def raw1715step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![1, 1, 0, -2], ![-4, 1, 0, 3]]

def raw1715step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw1716 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw1716step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def raw1717 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, -1, -1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def raw1717step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![-1, -1, 2, 0], ![4, -1, -2, -1]]

def raw1717step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw1718 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, -1, -1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw1718step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![-1, -1, 3, -1], ![4, -1, -3, 0]]

def raw1718step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 4, -3], ![0, 2, -1, -1], ![1, 0, -2, 1]]

def raw1719 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, -1, 2, -2]]

def raw1719step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, 0, -1], ![-1, -1, 0, 2], ![4, -1, -1, -2]]

def raw1719step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw1720 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 2, -3]]

def raw1720step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 2, 0, -3]]

def raw1721 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw1721step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

def raw1722 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw1722step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![-1, 0, 1, 0], ![4, -2, -1, -1]]

def raw1722step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw1723 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, 0, -2], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw1723step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![-1, 0, 2, -1], ![4, -2, -2, 0]]

def raw1723step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![1, 0, -2, 1], ![-4, 2, 2, 0]]

def raw1723step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw1724 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, -1, 2, -2]]

def raw1724step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, 0, -1], ![-1, 0, -1, 2], ![4, -2, 0, -2]]

def raw1724step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 0, 1], ![1, 0, 1, -2], ![-4, 2, 0, 2]]

def raw1724step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw1725 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, 1, -3], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def raw1725step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def raw1726 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, 1, -3], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw1726step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![-1, 1, 0, 0], ![4, -3, 0, -1]]

def raw1726step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![1, -1, 0, 0], ![-4, 3, 0, 1]]

def raw1726step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, 0, 3, -4]]

def raw1727 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, 1, -3], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw1727step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![-1, 1, 1, -1], ![4, -3, -1, 0]]

def raw1727step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![1, -1, -1, 1], ![-4, 3, 1, 0]]

def raw1727step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, -1, 1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1728 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, -1, 1, -1]]

def raw1728step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, 0, -1], ![-1, 1, -1, 1], ![4, -3, 0, -1]]

def raw1728step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 0, 1], ![1, -1, 1, -1], ![-4, 3, 0, 1]]

def raw1728step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def raw1729 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, 2, -4], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw1729step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![-1, 2, -1, 0], ![4, -4, 1, -1]]

def raw1729step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![1, -2, 1, 0], ![-4, 4, -1, 1]]

def raw1729step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, -2, 1], ![1, -1, 4, -4]]

def raw1730 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, 2, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw1730step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![-1, 2, 0, -1], ![4, -4, 0, 0]]

def raw1730step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![1, -2, 0, 1], ![-4, 4, 0, 0]]

def raw1730step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 4, -4], ![0, 1, -2, 1], ![1, 0, -2, 1]]

def raw1731 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![1, -1, 1, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw1731step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def raw1732 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![1, -1, 1, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw1732step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![-1, -1, 2, 0], ![-1, 1, 0, 0], ![4, -1, -2, -1]]

def raw1732step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw1733 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![1, -1, 2, -2], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw1733step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 1, -2], ![1, -1, 2, -2], ![1, 1, -2, 0]]

def raw1734 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![1, -1, 2, -2], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def raw1734step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, -2, 0], ![1, -1, 2, -2], ![1, 0, 1, -2]]

def raw1735 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![1, -1, 2, -2], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw1735step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![-1, -1, 2, 0], ![-1, 2, -1, 0], ![4, -2, -1, -1]]

def raw1735step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw1736 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![1, -1, 2, -2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw1736step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![-1, -1, 2, 0], ![-1, 2, 0, -1], ![4, -2, -2, 0]]

def raw1736step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![1, 1, -2, 0], ![1, -2, 0, 1], ![-4, 2, 2, 0]]

def raw1736step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw1737 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![1, 0, 1, -2], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw1737step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw1738 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![1, 0, 1, -2], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def raw1738step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def raw1739 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![1, 0, 2, -3], ![0, 2, -2, 0], ![1, -1, 1, -1]]

def raw1739step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 2, -3]]

def raw1740 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![1, 0, 2, -3], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw1740step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 2, 0, -3]]

def raw1741 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, -1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, 1, -4]]

def raw1741step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 1, 1, -2], ![0, 0, -1, 1], ![0, -1, 1, 0], ![-2, -1, -1, 4]]

def raw1741step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, 1, -3]]

def raw1742 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, -1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, 0, -3]]

def raw1742step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -2, 3], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def raw1743 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, -1, 2], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, 1, -1, -2]]

def raw1744 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, -1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, 1, 0, -3]]

def raw1745 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, -1, 2], ![0, 0, 2, -2], ![2, 2, -1, -3]]

def raw1745step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 1, 1, -2], ![0, 0, -2, 2], ![-2, -2, 1, 3]]

def raw1745step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, 1, 0, -3]]

def raw1746 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, 0, 0, -2]]

def raw1747 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, -1, 2], ![0, 1, 1, -2], ![2, 1, 0, -3]]

def raw1747step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -2, 3], ![0, 1, 2, -3], ![1, 1, 0, -2]]

def raw1748 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw1749 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, -1, 2], ![0, 1, 2, -3], ![2, 1, -1, -2]]

def raw1750 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, -1, 2], ![0, 2, 1, -3], ![2, 0, 0, -2]]

def raw1750step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 1, 1, -2], ![0, -2, -1, 3], ![-2, 0, 0, 2]]

def raw1750step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, 1, 0, -2]]

def raw1751 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, -1, 2], ![1, 1, 2, -4], ![1, 1, -1, -1]]

def raw1751step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 1, 1, -2], ![-1, -1, -2, 4], ![-1, -1, 1, 1]]

def raw1751step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def raw1752 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![2, 0, 0, -2]]

def raw1752step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 1, 0, -1], ![0, 0, 1, -1], ![0, -2, -1, 3], ![-2, 0, 0, 2]]

def raw1752step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def raw1753 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, 0, -3]]

def raw1753step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 1, 0, -1], ![0, 0, -1, 1], ![0, -1, 1, 0], ![-2, -1, 0, 3]]

def raw1753step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, -1, 3], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw1754 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 2, -4]]

def raw1754step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 1, 0, -1], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-2, 0, -2, 4]]

def raw1754step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 1, -3]]

def raw1755 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw1755step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 1, 0, -1], ![0, -1, 1, 0], ![-1, 0, 1, 0], ![-1, -1, -2, 4]]

def raw1755step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw1756 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 1, 1, -2], ![2, 1, -1, -2]]

def raw1756step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 1, 0, -1], ![0, -1, -1, 2], ![-2, -1, 1, 2]]

def raw1756step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, -1, -2, 2]]

def raw1757 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw1757step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 1, 0, -1], ![0, -2, -1, 3], ![-1, 0, 1, 0], ![-1, 0, 0, 1]]

def raw1757step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw1758 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 2, 1, -3], ![2, 0, -1, -1]]

def raw1758step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 1, 0, -1], ![0, -2, -1, 3], ![-2, 0, 1, 1]]

def raw1758step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, -2, 1]]

def raw1759 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 2, 2, -4], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw1759step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 1, 0, -1], ![0, -2, -2, 4], ![-1, 0, 1, 0], ![-1, 0, 1, 0]]

def raw1759step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1760 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, -1, -2]]

def raw1761 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def raw1762 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, -1, -2]]

def raw1763 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw1764 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw1764step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, -1, 3], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw1765 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw1765step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 1, -1, 0], ![0, -1, 0, 1], ![-1, 0, 0, 1], ![-1, -1, 1, 1]]

def raw1765step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw1766 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw1767 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![1, 1, -2, 0], ![1, 1, 1, -3]]

def raw1767step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, -1, 1, 1], ![0, 1, -2, 1], ![3, 0, 0, -3]]

def raw1767step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -2, 0, 1]]

def raw1768 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def raw1768step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 1, -1, 0], ![-1, -1, 1, 1], ![-1, -1, 0, 2]]

def raw1768step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -1, 2], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw1769 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw1770 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 1, 0, -2], ![1, 0, 0, -1]]

def raw1770step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw1771 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -2, 1], ![2, 1, 0, -3]]

def raw1772 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw1773 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw1774 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw1775 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw1776 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 1, -1, -1], ![1, 0, 0, -1]]

def raw1776step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw1777 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![2, 1, -1, -2]]

def raw1777step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, -1, 1, 1], ![0, 2, -1, -1], ![3, -1, 0, -2]]

def raw1777step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![1, 1, -1, -1], ![0, -2, 1, 1], ![-3, 1, 0, 2]]

def raw1777step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw1778 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw1779 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 1, 0, -2]]

def raw1780 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw1781 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw1782 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 1, -2, 0], ![1, 0, 0, -1]]

def raw1782step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw1783 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 1, -1, -1], ![1, 0, -1, 0]]

def raw1783step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw1784 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def raw1784step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, -1, 1, 1], ![0, 2, 0, -2], ![3, -1, -1, -1]]

def raw1784step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 1, -1]]

def raw1785 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw1786 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![2, 0, 0, -2]]

def raw1787 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw1788 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw1789 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def raw1790 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw1791 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -2, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1792 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 0, -2, 1], ![1, 2, 0, -3]]

def raw1793 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 0, -1, 0], ![1, 2, -1, -2]]

def raw1793step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, -1, 0, 2], ![0, 2, -1, -1], ![3, -1, 0, -2]]

def raw1793step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, 1, 0, -2], ![0, -2, 1, 1], ![-3, 1, 0, 2]]

def raw1793step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw1794 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 0, 0, -1], ![1, 2, -2, -1]]

def raw1794step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, -1, 0, 2], ![0, 2, 0, -2], ![3, -1, -1, -1]]

def raw1794step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def raw1795 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def raw1796 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def raw1797 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 1, 0, -2], ![1, 1, -2, 0]]

def raw1797step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def raw1798 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 2, -2, -1], ![1, 0, 0, -1]]

def raw1798step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, -1, 2, 0], ![0, 2, -2, 0], ![3, -1, -1, -1]]

def raw1798step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def raw1799 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 2, -1, -2], ![1, 0, -1, 0]]

def raw1799step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, -1, 2, 0], ![0, 2, -1, -1], ![3, -1, -2, 0]]

def raw1799step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, 1, -2, 0], ![0, -2, 1, 1], ![-3, 1, 2, 0]]

def raw1799step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw1800 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 2, 0, -3], ![1, 0, -2, 1]]

def raw1800step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 0, -2, 1], ![1, 2, 0, -3]]

def raw1801 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 2, 1, -4]]

def raw1801step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, 2, -2], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, -2, -1, 4]]

def raw1801step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 0, 1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 2, -3]]

def raw1802 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 2, 0, -3]]

def raw1803 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 2, 0, -3]]

def raw1804 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 0, 2, -2], ![2, 1, 0, -3]]

def raw1804step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 2, 0, -3]]

def raw1805 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, 2, -3]]

def raw1805step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, 2, -2], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-2, 1, -2, 3]]

def raw1805step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, 1, -3]]

def raw1806 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, -1, 1, -2]]

def raw1807 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 1, 0, -2]]

def raw1808 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 2, -3], ![1, 0, 0, -1]]

def raw1808step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def raw1809 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 1, 1, -2], ![0, 1, 0, -1], ![2, -1, 1, -2]]

def raw1809step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, -1, 1, -2]]

def raw1810 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, 0, 1, -3]]

def raw1810step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, 0, 1, -2]]

def raw1811 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 1, 2, -3], ![2, 0, 0, -2]]

def raw1811step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 2, -3]]

def raw1812 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def raw1813 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, -1, 2, -3]]

def raw1813step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, 2, -2], ![0, -2, 0, 2], ![-2, 1, -2, 3]]

def raw1813step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, 0, 1, -3]]

def raw1814 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw1815 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 2, 1, -3], ![2, -1, 1, -2]]

def raw1816 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![1, -1, 1, -1], ![1, 2, 1, -4]]

def raw1816step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, 2, -2], ![-1, 1, -1, 1], ![-1, -2, -1, 4]]

def raw1816step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 2, 0, -3]]

def raw1817 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![1, -1, 2, -2], ![1, 2, 0, -3]]

def raw1818 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![1, 0, 2, -3], ![1, 1, 0, -2]]

def raw1818step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, 1, 0, -2]]

def raw1819 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![1, 2, 0, -3], ![1, -1, 2, -2]]

def raw1819step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![1, -1, 2, -2], ![1, 2, 0, -3]]

def raw1820 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![1, 2, 1, -4], ![1, -1, 1, -1]]

def raw1820step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, 2, -2], ![-1, -2, -1, 4], ![-1, 1, -1, 1]]

def raw1820step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 2, 0, -3]]

def raw1821 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, -1, 0, 1], ![0, 2, 1, -3], ![2, 0, 0, -2]]

def raw1821step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, -2, -1, 3], ![-2, 0, 0, 2]]

def raw1821step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def raw1822 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, -1, 1, 0], ![0, 1, 1, -2], ![2, 1, -1, -2]]

def raw1822step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, 1, -2], ![2, 1, -1, -2]]

def raw1823 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, -1, 2, -1], ![0, 1, -1, 0], ![2, 1, 0, -3]]

def raw1823step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, -1, 1, 0], ![-2, -1, 0, 3]]

def raw1823step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -2, 1], ![2, 1, 0, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1824 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![2, 0, 0, -2]]

def raw1824step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, -2, 3], ![-2, 0, 0, 2]]

def raw1824step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def raw1825 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![2, -1, 1, -2]]

def raw1826 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![2, 0, 2, -4]]

def raw1826step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![-1, 0, 0, 1, 0], ![0, -1, 0, -1, 2], ![3, 1, 0, 0, -4]]

def raw1826step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 1, 0], ![0, -1, -1, 2], ![3, 1, 0, -4]]

def raw1826step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, 0, 3, -4]]

def raw1827 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, 0, 0], ![1, -1, 1, -1], ![1, 2, 0, -3]]

def raw1827step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, 1, -1], ![0, 0, 0, 0], ![-1, 1, -1, 1], ![-1, -2, 0, 3]]

def raw1827step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, 1, -1], ![-1, 1, -1, 1], ![-1, -2, 0, 3]]

def raw1827step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw1828 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, 0, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw1828step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 0, 0, 1], ![0, -1, 0, -1, 2], ![3, 1, 0, 0, -4]]

def raw1828step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, 0, 1], ![0, -1, -1, 2], ![3, 1, 0, -4]]

def raw1828step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, 0, 3, -4]]

def raw1829 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![2, 1, 0, -3]]

def raw1829step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![2, 1, 0, -3]]

def raw1829step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 0, 1], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def raw1830 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, 1, -1, -2]]

def raw1830step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 2, -1, -2]]

def raw1831 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 0, 1, -3]]

def raw1831step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw1832 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw1832step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw1833 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 2, 0, -3]]

def raw1833step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, -1, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def raw1834 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 2, -1, -2]]

def raw1835 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw1835step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def raw1836 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![2, 1, -1, -2]]

def raw1836step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 2, -1, -2]]

def raw1837 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 0, 0, 0], ![2, 0, 2, -4]]

def raw1837step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![-1, 0, 1, 0, 0], ![0, -1, -1, 0, 2], ![3, 1, 0, 0, -4]]

def raw1837step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 1, 0], ![0, -1, -1, 2], ![3, 1, 0, -4]]

def raw1837step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, 0, 3, -4]]

def raw1838 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 0, 2, -2], ![2, 0, 0, -2]]

def raw1838step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw1839 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 3, -4]]

def raw1840 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, -1, 0, -1]]

def raw1841 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw1841step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, -1, -2, 4]]

def raw1841step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw1842 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def raw1842step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def raw1843 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, 1, -2]]

def raw1843step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, 1, -1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-2, 1, -1, 2]]

def raw1843step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw1844 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 2, -3]]

def raw1844step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def raw1845 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def raw1845step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, 1, -1], ![0, -1, -1, 2], ![-2, 0, 0, 2]]

def raw1845step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def raw1846 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw1847 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw1847step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def raw1848 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 0, 0, -1], ![1, 0, -1, 0]]

def raw1848step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def raw1849 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, 2, -3], ![2, 0, -1, -1]]

def raw1849step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 2, -3]]

def raw1850 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw1850step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 3, -4]]

def raw1851 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw1851step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, 1, -1], ![0, -2, 0, 2], ![-1, 1, -1, 1], ![-1, 0, 0, 1]]

def raw1851step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw1852 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, -1, 1, -2]]

def raw1852step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, 1, -1], ![0, -2, 0, 2], ![-2, 1, -1, 2]]

def raw1852step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw1853 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw1853step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, 1, -1], ![0, -2, -1, 3], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw1853step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def raw1854 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw1855 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, -1, 1, -1]]

def raw1855step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, 1, -1], ![1, 0, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1856 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 2, 1, -3], ![2, -1, 0, -1]]

def raw1856step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, 1, -1], ![0, -2, -1, 3], ![-2, 1, 0, 1]]

def raw1856step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def raw1857 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw1857step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, 1, -1], ![0, -2, -2, 4], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw1857step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 2, -3]]

def raw1858 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0], ![1, -1, 0, 0]]

def raw1858step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, 1, -1], ![0, -2, -2, 4], ![-1, 0, 1, 0], ![-1, 1, 0, 0]]

def raw1858step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 2, -3]]

def raw1859 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![1, -1, 1, -1], ![1, 2, 0, -3]]

def raw1859step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, 1, -1], ![-1, 1, -1, 1], ![-1, -2, 0, 3]]

def raw1859step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw1860 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![1, 0, 2, -3], ![1, 1, -1, -1]]

def raw1860step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 1, -1, -1]]

def raw1861 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 0, 0], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 2, -1, -2]]

def raw1861step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 0, -1, 2], ![0, 0, 1, 0, -1], ![3, 0, -1, 0, -2]]

def raw1861step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, -1, 2], ![0, 1, 0, -1], ![3, -1, 0, -2]]

def raw1861step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw1862 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 0, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 1, -2]]

def raw1862step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![-1, 0, 1, 1, -1], ![0, 0, -1, 0, 1], ![3, 0, 0, -1, -2]]

def raw1862step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, 0, -2], ![1, 0, -1, -1, 1], ![0, 0, 1, 0, -1], ![-3, 0, 0, 1, 2]]

def raw1862step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![1, -1, -1, 1], ![0, 1, 0, -1], ![-3, 0, 1, 2]]

def raw1862step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def raw1863 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 0, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw1863step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 1, -1, 1], ![0, 0, -1, 0, 1], ![3, 0, 0, 0, -3]]

def raw1863step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, -1, -1], ![1, 0, -1, 1, -1], ![0, 0, 1, 0, -1], ![-3, 0, 0, 0, 3]]

def raw1863step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 1, -1], ![0, 1, 0, -1], ![-3, 0, 0, 3]]

def raw1863step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, -1, 1]]

def raw1864 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 0, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw1864step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 1, 0, 0], ![0, 0, -1, 0, 1], ![3, 0, 0, -1, -2]]

def raw1864step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![0, -1, 0, 1], ![3, 0, -1, -2]]

def raw1864step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw1865 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw1865step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw1865step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw1866 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 0, 0], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw1866step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, 0, 0], ![0, -1, -1, 2], ![-1, 0, 1, 0], ![-1, 0, 0, 1]]

def raw1866step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, -1, 2], ![-1, 0, 1, 0], ![-1, 0, 0, 1]]

def raw1866step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def raw1867 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 0, 0], ![0, 1, 2, -3], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw1867step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 1, 0, 0], ![0, 0, 2, -1, -1], ![3, 0, -3, 0, 0]]

def raw1867step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![0, 2, -1, -1], ![3, -3, 0, 0]]

def raw1867step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 3, -3], ![1, 1, -2, 0]]

def raw1868 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 0, 0], ![1, -1, 1, -1], ![1, 2, -1, -2]]

def raw1868step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, -1, 2], ![0, 0, 1, -1], ![3, 0, -1, -2]]

def raw1868step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![3, -1, -2]]

def raw1868step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

def raw1869 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 0, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw1869step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, 0, 1], ![0, 0, -1, 1], ![3, 0, 0, -3]]

def raw1869step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, 0, 0, -1], ![0, 0, 1, -1], ![-3, 0, 0, 3]]

def raw1869step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![-3, 0, 3]]

def raw1869step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

def raw1870 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![2, 1, -1, -2]]

def raw1870step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, -1, -2]]

def raw1871 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, -1, 1, 0], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def raw1871step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def raw1872 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, -1, 1, 0], ![1, 0, -1, 0], ![1, 2, -1, -2]]

def raw1872step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, -1, -2]]

def raw1873 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, -1, 1], ![2, 1, 0, -3]]

def raw1873step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 0, 1], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def raw1874 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw1874step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw1874step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 0, 0]]

def raw1875 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, 2, -1, -2]]

def raw1875step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 0, -1, 2], ![0, 1, 0, 0, -1], ![3, -1, 0, 0, -2]]

def raw1875step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, -1, 2], ![0, 1, 0, -1], ![3, -1, 0, -2]]

def raw1875step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw1876 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 0, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw1876step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 0, 0, 1], ![0, 1, 0, 0, -1], ![3, -1, 0, -1, -1]]

def raw1876step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, 0, 1], ![0, 1, 0, -1], ![3, -1, -1, -1]]

def raw1876step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw1877 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 0, 0], ![2, 1, -1, -2]]

def raw1877step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 0, 1], ![0, 1, 0, -1], ![3, -1, 0, -2]]

def raw1877step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![3, -1, -2]]

def raw1877step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def raw1878 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, -1, 1], ![2, 1, -1, -2]]

def raw1878step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 2, -1, -2]]

def raw1879 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![2, 1, -2, -1]]

def raw1879step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![-1, 0, 0, 0, 1], ![0, 1, 1, 0, -2], ![3, -1, -1, 0, -1]]

def raw1879step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 0, 1], ![0, 1, 1, -2], ![3, -1, -1, -1]]

def raw1879step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, 1, -2, 0]]

def raw1880 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 0, -1, -1]]

def raw1880step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw1881 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw1881step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw1882 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, -1, 0, -1]]

def raw1883 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 2, -1, -2]]

def raw1884 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 2, -2, -1]]

def raw1885 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw1885step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 1, -1, -1]]

def raw1886 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw1886step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def raw1887 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, 1, -2, -1]]

def raw1887step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 0, 1], ![0, 1, 1, -2], ![3, -1, -1, -1]]

def raw1887step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, 1, -2, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1888 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -1, 2, -3]]

def raw1889 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -1, 1, -2]]

def raw1890 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def raw1891 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw1892 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def raw1893 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![2, 0, 1, -3]]

def raw1893step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw1894 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 0, 0, 0], ![2, 0, 0, -2]]

def raw1894step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw1894step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 0, 0]]

def raw1895 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def raw1896 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def raw1896step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, -1, 1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-2, 1, 0, 1]]

def raw1896step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw1897 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -1, -1, 0]]

def raw1898 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def raw1899 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw1899step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, -1, 1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, -1, 0, 2]]

def raw1899step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, -1, 2], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw1900 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw1901 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw1901step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0]]

def raw1902 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw1902step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 0, 0]]

def raw1903 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 0, 1, -1], ![2, 0, -2, 0]]

def raw1903step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw1904 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def raw1904step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, -1, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![-2, 1, 0, 1]]

def raw1904step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw1905 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw1905step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -2, 3], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw1906 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, -1, -2, 1]]

def raw1907 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def raw1907step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw1908 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw1908step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, -1, 1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, -1, 1, 1]]

def raw1908step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1]]

def raw1909 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw1910 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw1910step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw1911 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, -1, 0]]

def raw1911step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw1912 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw1912step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 1, 0], ![0, 1, 0, -1], ![3, -1, -1, -1]]

def raw1912step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw1913 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![0, 1, 0, -1], ![2, -1, -2, 1]]

def raw1913step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, -1, -2, 1]]

def raw1914 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw1915 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw1915step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw1916 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

def raw1916step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def raw1917 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw1918 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw1919 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, -1, 1, -2]]

def raw1919step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 2, -1], ![0, 1, -2, 1], ![3, -1, 0, -2]]

def raw1919step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -2, 1, 0]]

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

def raw192 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![0, 0], ![0, 0], ![1, -1], ![1, -1], ![2, -2]]

def raw192step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![0, 0], ![1, -1], ![1, -1], ![2, -2]]

def raw192step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]

def raw193 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![0, 0], ![0, 0], ![1, -1], ![3, -3]]

def raw193step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![0, 0], ![1, -1], ![3, -3]]

def raw193step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]

def raw194 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![0, 0], ![0, 0], ![2, -2], ![2, -2]]

def raw194step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![0, 0], ![2, -2], ![2, -2]]

def raw194step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![2, -2]]

def raw195 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![0, 0], ![0, 0], ![4, -4]]

def raw195step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![0, 0], ![4, -4]]

def raw195step1 : Matrix (Fin 2) (Fin 2) ℤ := ![![-4, 4], ![4, -4]]

def raw196 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![0, 0], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]

def raw196step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]

def raw197 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![0, 0], ![1, -1], ![1, -1], ![2, -2]]

def raw197step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]

def raw198 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![0, 0], ![1, -1], ![3, -3]]

def raw198step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]

def raw199 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![0, 0], ![2, -2], ![2, -2]]

def raw199step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![2, -2]]

def raw200 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![0, 0], ![4, -4]]

def raw200step0 : Matrix (Fin 2) (Fin 2) ℤ := ![![-4, 4], ![4, -4]]

def raw201 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![0, 0], ![1, -1], ![2, -2]]

def raw201step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]

def raw202 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![0, 0], ![2, -2], ![1, -1]]

def raw202step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![2, -2], ![1, -1]]

def raw202step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]

def raw203 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![0, 0], ![3, -3]]

def raw203step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]

def raw204 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![0, 0], ![0, 0], ![2, -2]]

def raw204step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![0, 0], ![2, -2]]

def raw204step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]

def raw205 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![0, 0], ![1, -1], ![1, -1]]

def raw205step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]

def raw206 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![0, 0], ![2, -2]]

def raw206step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]

def raw207 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]

def raw208 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]

def raw209 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2], ![0, 0]]

def raw209step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]

def raw210 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![2, -2], ![1, -1]]

def raw210step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]

def raw211 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]

def raw213 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![1, -1], ![1, -1]]

def raw213step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]

def raw214 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![2, -2]]

def raw215 : Matrix (Fin 2) (Fin 2) ℤ := ![![-4, 4], ![4, -4]]

def raw216 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 5, -1], ![4, -5, 1]]

def raw216step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![5, -5], ![-1, 1]]

def raw216step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![4, -4]]

def raw217 : Matrix (Fin 2) (Fin 4) ℤ := ![![-3, -2, 2, 3], ![3, 2, -2, -3]]

def raw217step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![2, -2], ![3, -3]]

def raw218 : Matrix (Fin 2) (Fin 4) ℤ := ![![-3, -2, 3, 2], ![3, 2, -3, -2]]

def raw218step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![3, -3], ![2, -2]]

def raw218step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![2, -2], ![3, -3]]

def raw219 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

def raw220 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]

def raw220step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw221 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]

def raw222 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

def raw223 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1920 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def raw1921 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw1921step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, -1, 1], ![0, -2, 1, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw1921step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw1922 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw1923 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, -1, 1, -1]]

def raw1923step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw1924 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -1, 0, -1]]

def raw1924step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 2, -1], ![0, 1, -1, 0], ![3, -1, -1, -1]]

def raw1924step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw1925 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw1925step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw1926 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw1926step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, -1, 1], ![0, -2, 0, 2], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw1926step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw1927 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, -2, 1]]

def raw1928 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, -1, 0, 0]]

def raw1928step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, -1, 1], ![0, -2, 0, 2], ![-1, 0, 1, 0], ![-1, 1, 0, 0]]

def raw1928step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw1929 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, -1, -1, 0]]

def raw1929step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 2, -1], ![0, 1, 0, -1], ![3, -1, -2, 0]]

def raw1929step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw1930 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw1930step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, -1, 1], ![0, -2, -1, 3], ![-1, 1, 1, -1], ![-1, 0, 1, 0]]

def raw1930step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, 2, -3], ![1, 1, -1, -1]]

def raw1931 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw1931step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, -1, 1], ![0, -2, -1, 3], ![-1, 1, 0, 0], ![-1, 0, 2, -1]]

def raw1931step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 2, -3]]

def raw1932 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, -1, -1, 1]]

def raw1932step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, -1, 1], ![0, -2, -1, 3], ![-1, 0, 1, 0], ![-1, 1, 1, -1]]

def raw1932step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, 2, -3], ![1, 1, -1, -1]]

def raw1933 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 2, 0, -3]]

def raw1933step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw1934 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 2, -1, -2]]

def raw1934step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, -1, 2], ![0, 1, 0, -1], ![3, -1, 0, -2]]

def raw1934step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw1935 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 2, -2, -1]]

def raw1935step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, -1, 2], ![0, 1, 1, -2], ![3, -1, -1, -1]]

def raw1935step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw1936 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw1936step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw1937 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw1937step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, 0, 1], ![0, 1, 0, -1], ![3, -1, -1, -1]]

def raw1937step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw1938 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![1, 0, 1, -2], ![1, 1, -2, 0]]

def raw1938step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw1939 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![1, 1, -2, 0], ![1, 0, 1, -2]]

def raw1939step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw1940 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw1940step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw1941 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw1941step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw1942 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw1942step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

def raw1943 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 0, -1, 1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw1943step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def raw1944 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 0, 0, 0], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw1944step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw1944step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, -1, -1]]

def raw1945 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def raw1946 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def raw1947 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw1948 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw1948step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1]]

def raw1949 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, 0, 0, -2]]

def raw1949step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw1950 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 0, -1, 1], ![2, 0, 0, -2]]

def raw1950step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw1951 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 0, 0, 0], ![2, 0, -1, -1]]

def raw1951step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, 0, -1, -1]]

def raw1951step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1952 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def raw1953 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw1954 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def raw1955 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw1956 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw1956step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw1957 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, -1, 0]]

def raw1957step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw1958 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, 0, -1, -1]]

def raw1958step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw1959 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -2, 1]]

def raw1960 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def raw1961 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw1962 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def raw1962step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw1963 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw1963step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw1964 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw1964step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw1965 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, -3, 1], ![2, -1, 1, -2]]

def raw1966 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw1967 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![2, -1, 0, -1]]

def raw1967step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 2, -1], ![0, 2, -2, 0], ![3, -2, 0, -1]]

def raw1967step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -2, 0]]

def raw1968 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw1969 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw1970 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, -1, -1, 0]]

def raw1971 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw1972 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw1973 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, -1, -1, 1]]

def raw1973step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw1974 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![2, -1, -2, 1]]

def raw1975 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 2, -1, -2]]

def raw1976 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 2, -2, -1]]

def raw1976step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, -1, 2], ![0, 2, 0, -2], ![3, -2, 0, -1]]

def raw1976step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, 0, 1, -2], ![0, -2, 0, 2], ![-3, 2, 0, 1]]

def raw1976step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 2, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw1977 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![1, 0, -2, 1], ![1, 1, 0, -2]]

def raw1977step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def raw1978 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw1978step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, -1, -1]]

def raw1979 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw1979step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, 0, 1], ![0, 2, 0, -2], ![3, -2, -1, 0]]

def raw1979step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def raw1980 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![1, 1, -2, 0], ![1, 0, 0, -1]]

def raw1980step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, 1, 0], ![0, 2, -2, 0], ![3, -2, 0, -1]]

def raw1980step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def raw1981 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![1, 1, -1, -1], ![1, 0, -1, 0]]

def raw1981step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, -1, -1]]

def raw1982 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![1, 1, 0, -2], ![1, 0, -2, 1]]

def raw1982step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def raw1983 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![1, 2, -1, -2], ![1, -1, -1, 1]]

def raw1983step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 2, -1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1984 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw1985 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 2, -3]]

def raw1986 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -1, 3, -4]]

def raw1986step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![0, -2, -1, 3], ![3, 1, 0, -4]]

def raw1986step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, 1, -1, -1]]

def raw1987 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw1987step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, 2, -1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, -2, 3]]

def raw1987step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 1, -3], ![2, 0, -1, -1]]

def raw1988 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw1989 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def raw1990 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -1, 2, -3]]

def raw1990step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![0, -2, 0, 2], ![3, 1, -1, -3]]

def raw1990step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![1, -1, -1, 1], ![0, 2, 0, -2], ![-3, -1, 1, 3]]

def raw1990step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -3, 3]]

def raw1991 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw1992 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, 1, -2]]

def raw1993 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw1993step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, 2, -1], ![0, -1, -2, 3], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw1993step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, -1, 0, -1]]

def raw1994 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw1995 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![2, -1, 0, -1]]

def raw1996 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw1997 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 3, -4], ![2, -1, -1, 0]]

def raw1998 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw1998step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![0, -2, 0, 2], ![3, 1, 0, -4]]

def raw1998step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 1, -1], ![0, 2, 0, -2], ![-3, -1, 0, 4]]

def raw1998step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw1999 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 1, 1, -3]]

def raw2000 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 2, -2], ![1, 1, 0, -2]]

def raw2001 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def raw2001step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -2, 1]]

def raw2002 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 0, 2, -3]]

def raw2002step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, -2, 1]]

def raw2003 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, 0, 1, -2], ![1, 0, 1, -2]]

def raw2003step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, 0, -2, 1]]

def raw2004 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, 0, 2, -3], ![1, 0, 0, -1]]

def raw2004step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, -2, 1]]

def raw2005 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, 0, 3, -4], ![1, 0, -1, 0]]

def raw2005step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -2, 1]]

def raw2006 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, 1, 1, -3], ![1, -1, 1, -1]]

def raw2006step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 1, 1, -3]]

def raw2007 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def raw2007step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def raw2008 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 0, 0, 0], ![1, 0, -1, 0], ![1, 0, 2, -3]]

def raw2008step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 1, 0, 0, 0], ![0, -1, 0, -1, 2], ![3, 0, 0, 0, -3]]

def raw2008step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![0, -1, -1, 2], ![3, 0, 0, -3]]

def raw2008step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, -1, 0]]

def raw2009 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 0, 0, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw2009step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 1, 0, 0, 0], ![0, -1, 0, 0, 1], ![3, 0, 0, -1, -2]]

def raw2009step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![0, -1, 0, 1], ![3, 0, -1, -2]]

def raw2009step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw2010 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw2010step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw2011 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 0, 2, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw2011step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw2012 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 0, 2, -2], ![2, 0, -1, -1]]

def raw2012step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw2013 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 0, 3, -3], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw2013step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 3, -3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def raw2014 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw2014step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw2015 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, -2, 1], ![2, -1, 3, -4]]

def raw2015step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![0, -1, -2, 3], ![3, 0, 1, -4]]

def raw2015step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, 1, -1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2016 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 3, -4]]

def raw2017 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw2017step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, -2, 3]]

def raw2017step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw2018 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw2019 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def raw2020 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw2021 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, -1, 3, -3]]

def raw2021step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw2022 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, -1, 2, -2]]

def raw2022step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def raw2023 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 2, -3]]

def raw2023step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![0, -1, -1, 2], ![3, 0, 0, -3]]

def raw2023step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, 1, -1, -1]]

def raw2024 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 2, -3]]

def raw2024step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 1, 1, -1], ![-1, 0, -2, 3]]

def raw2024step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw2025 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw2025step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, -1, 2]]

def raw2025step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw2026 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw2026step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 1, -1, 1], ![-1, 0, 0, 1]]

def raw2026step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw2027 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw2028 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, -1, 2, -2]]

def raw2028step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw2029 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 1, -2]]

def raw2029step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![0, -1, 0, 1], ![3, 0, -1, -2]]

def raw2029step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![1, -1, -1, 1], ![0, 1, 0, -1], ![-3, 0, 1, 2]]

def raw2029step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def raw2030 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw2030step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, 1, 0], ![0, -1, -1, 2], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw2030step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw2031 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw2032 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, -1, 1, -1]]

def raw2032step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw2033 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def raw2033step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, 1, 0], ![0, -1, -1, 2], ![-2, 1, 0, 1]]

def raw2033step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw2034 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw2034step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, 1, 0], ![0, -1, -2, 3], ![-1, 1, 1, -1], ![-1, 0, 0, 1]]

def raw2034step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw2035 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw2036 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 0, -2, 1]]

def raw2037 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0], ![1, -1, 0, 0]]

def raw2037step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw2038 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, -1, -1, 0]]

def raw2038step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![0, -1, 2, -1], ![3, 0, -3, 0]]

def raw2038step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, -1, 1]]

def raw2039 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw2040 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw2041 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -1, 0], ![1, -1, -1, 1]]

def raw2041step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw2042 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def raw2042step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![0, -1, -1, 2], ![3, 0, 1, -4]]

def raw2042step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def raw2043 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw2043step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![0, -1, 0, 1], ![3, 0, 0, -3]]

def raw2043step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 1, -1], ![0, 1, 0, -1], ![-3, 0, 0, 3]]

def raw2043step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, -1, 1]]

def raw2044 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def raw2044step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, 1, 0], ![-1, 1, -1, 1], ![-1, -1, 0, 2]]

def raw2044step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw2045 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![1, -1, 2, -2], ![1, 1, -1, -1]]

def raw2045step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![0, -1, 2, -1], ![3, 0, -2, -1]]

def raw2045step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, 1, -1, -1]]

def raw2046 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 1, -2, 0]]

def raw2046step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![0, -1, 3, -2], ![3, 0, -3, 0]]

def raw2046step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 1, -1, -1]]

def raw2047 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![1, 0, -2, 1], ![1, 0, 3, -4]]

def raw2047step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, 0, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2048 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 2, -3]]

def raw2048step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![0, -1, -1, 2], ![3, 0, 0, -3]]

def raw2048step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, -1, 0]]

def raw2049 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw2049step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![0, -1, 0, 1], ![3, 0, -1, -2]]

def raw2049step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw2050 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![1, 0, 1, -2], ![1, 0, 0, -1]]

def raw2050step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![0, -1, 1, 0], ![3, 0, -2, -1]]

def raw2050step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw2051 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![1, 0, 2, -3], ![1, 0, -1, 0]]

def raw2051step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![0, -1, 2, -1], ![3, 0, -3, 0]]

def raw2051step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, -1, 0]]

def raw2052 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 0, -1], ![0, 0, 2, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw2052step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw2053 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 0, -1], ![0, 0, 2, -2], ![2, 0, -2, 0]]

def raw2053step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw2054 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 2, -3]]

def raw2054step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, 0, 1], ![0, -1, 1, 0], ![-1, 1, 1, -1], ![-1, 0, -2, 3]]

def raw2054step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw2055 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw2055step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, 0, 1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, -1, 2]]

def raw2055step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw2056 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw2056step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, 0, 1], ![0, -1, 1, 0], ![-1, 1, -1, 1], ![-1, 0, 0, 1]]

def raw2056step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw2057 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw2057step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw2058 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 0, -1], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def raw2058step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![0, 0, -1, 1], ![3, -1, 0, -2]]

def raw2058step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![1, -1, -1, 1], ![0, 0, 1, -1], ![-3, 1, 0, 2]]

def raw2058step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def raw2059 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw2059step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 1, -1, 1], ![-1, 0, 1, 0]]

def raw2059step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, 0, 0]]

def raw2060 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -2, 1]]

def raw2061 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw2061step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, 0, 1], ![0, -1, -1, 2], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw2061step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw2062 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, -1, 0, 0]]

def raw2062step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, 0, 1], ![0, -1, -1, 2], ![-1, 0, 1, 0], ![-1, 1, 0, 0]]

def raw2062step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw2063 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, -1, -1, 0]]

def raw2063step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![0, 0, 1, -1], ![3, -1, -2, 0]]

def raw2063step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, -1, -1]]

def raw2064 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw2064step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, 0, 1], ![0, -1, -2, 3], ![-1, 1, 1, -1], ![-1, 0, 1, 0]]

def raw2064step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 1, 2, -3], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw2065 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw2065step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, 0, 1], ![0, -1, -2, 3], ![-1, 1, 0, 0], ![-1, 0, 2, -1]]

def raw2065step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, 0, -1, -1]]

def raw2066 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, -1, 0], ![1, -1, -1, 1]]

def raw2066step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, 0, 1], ![0, -1, -2, 3], ![-1, 0, 1, 0], ![-1, 1, 1, -1]]

def raw2066step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 1, 2, -3], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw2067 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 0, -1], ![0, 1, 2, -3], ![2, -1, -2, 1]]

def raw2067step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![0, 0, 2, -2], ![3, -1, -3, 1]]

def raw2067step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -3, 1, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, 1, -1, -1]]

def raw2068 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def raw2068step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, 0, 1], ![-1, 1, 1, -1], ![-1, -1, -1, 3]]

def raw2068step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 0, 1], ![0, 1, 2, -3], ![1, 1, -1, -1]]

def raw2069 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw2069step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![0, 0, 1, -1], ![3, -1, -1, -1]]

def raw2069step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw2070 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 1, -2, 0]]

def raw2070step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![0, 0, 2, -2], ![3, -1, -2, 0]]

def raw2070step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 1, -1], ![0, 0, -2, 2], ![-3, 1, 2, 0]]

def raw2070step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, -2, 0], ![1, 0, 2, -3]]

def raw2071 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw2071step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw2072 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 0, -1, 0]]

def raw2072step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw2073 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 0, -1], ![1, 0, 2, -3], ![1, 0, -2, 1]]

def raw2073step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def raw2074 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 1, -2], ![0, 1, -2, 1], ![2, -1, 1, -2]]

def raw2074step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, 1, -2]]

def raw2075 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 1, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw2075step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, -1, 2], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw2075step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw2076 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 1, -2], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def raw2076step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, -1, 2], ![0, -1, 1, 0], ![-2, 1, 0, 1]]

def raw2076step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw2077 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 1, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw2077step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, -1, 2], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw2077step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw2078 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 1, -2], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw2078step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![0, 1, 0, -1], ![3, -2, -1, 0]]

def raw2078step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, -1, -1]]

def raw2079 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 1, -2], ![0, 1, 1, -2], ![2, -1, -2, 1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2080 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def raw2080step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, -1, 2], ![-1, 1, 1, -1], ![-1, -1, 0, 2]]

def raw2080step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, 1, -1, -1]]

def raw2081 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw2081step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, -1, 2], ![-1, 1, 0, 0], ![-1, -1, 1, 1]]

def raw2081step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1]]

def raw2082 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw2083 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw2083step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, -1, 2], ![-1, 0, 1, 0], ![-1, 0, 0, 1]]

def raw2083step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def raw2084 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 0, -1, 0]]

def raw2084step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, -1, 2], ![-1, 0, 0, 1], ![-1, 0, 1, 0]]

def raw2084step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def raw2085 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 2, -3], ![0, 1, -2, 1], ![2, -1, 0, -1]]

def raw2085step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![2, -1, 0, -1]]

def raw2086 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 2, -3], ![0, 1, 0, -1], ![2, -1, -2, 1]]

def raw2086step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![0, 2, 0, -2], ![3, -3, -1, 1]]

def raw2086step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -3, 1, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, 1, -1, -1]]

def raw2087 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def raw2088 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw2088step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![0, 2, 0, -2], ![3, -3, 0, 0]]

def raw2088step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 1, -1], ![0, -2, 0, 2], ![-3, 3, 0, 0]]

def raw2088step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, -1, 1]]

def raw2089 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 1, -3, 1]]

def raw2090 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 2, -3], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw2090step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![0, 2, -1, -1], ![3, -3, 0, 0]]

def raw2090step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 3, -3], ![1, 1, -2, 0]]

def raw2091 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 2, -3], ![1, 0, 0, -1], ![1, 0, -2, 1]]

def raw2091step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, -2, 3], ![-1, 0, 0, 1], ![-1, 0, 2, -1]]

def raw2091step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 2, -3]]

def raw2092 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, 1, -2, 0]]

def raw2093 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 1, -3, 1]]

def raw2093step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![0, 3, 0, -3], ![3, -4, 0, 1]]

def raw2093step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -3, 3], ![0, 3, 1, -4], ![1, -2, 1, 0]]

def raw2094 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 3, -4], ![1, 0, -2, 1], ![1, 0, -1, 0]]

def raw2094step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![0, 3, -2, -1], ![3, -4, 1, 0]]

def raw2094step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, 1, -2, 0]]

def raw2095 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 3, -4], ![1, 0, -1, 0], ![1, 0, -2, 1]]

def raw2095step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![0, 3, -1, -2], ![3, -4, 0, 1]]

def raw2095step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, 1, -2, 0]]

def raw2096 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, -3, 1], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw2096step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![0, -3, 0, 3], ![3, 1, 0, -4]]

def raw2096step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 0, -3, 3], ![0, 3, 1, -4], ![1, -2, 0, 1]]

def raw2097 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, -3, 1], ![1, -1, 1, -1], ![1, 0, 2, -3]]

def raw2098 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, -2, 0], ![1, -1, -1, 1], ![1, 0, 3, -4]]

def raw2098step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![0, -2, -1, 3], ![3, 0, 1, -4]]

def raw2098step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 3, -4], ![2, -1, -1, 0]]

def raw2099 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw2099step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![0, -2, 0, 2], ![3, 0, 0, -3]]

def raw2099step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![0, 2, 0, -2], ![-3, 0, 0, 3]]

def raw2099step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -2, 0, 1]]

def raw2100 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw2100step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![0, -2, 1, 1], ![3, 0, -1, -2]]

def raw2100step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def raw2101 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, -2, 0], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def raw2101step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![0, -2, 2, 0], ![3, 0, -2, -1]]

def raw2101step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 2, 0], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw2102 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, -2, 0], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw2102step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![0, -2, 3, -1], ![3, 0, -3, 0]]

def raw2102step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 3, -3], ![0, 2, -1, -1], ![1, 0, -2, 1]]

def raw2103 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, -1, 2, -2]]

def raw2103step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, 0, -1], ![0, -2, 0, 2], ![3, 0, -1, -2]]

def raw2103step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 2, 0], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw2104 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 2, -3]]

def raw2105 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw2105step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -2, 1, 1], ![-1, 1, 0, 0], ![-1, 0, -1, 2]]

def raw2105step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw2106 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw2106step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![0, -1, 1, 0], ![3, -1, -1, -1]]

def raw2106step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw2107 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, -1, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw2107step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![0, -1, 2, -1], ![3, -1, -2, 0]]

def raw2107step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, 0, -2, 1]]

def raw2108 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, -1, 2, -2]]

def raw2108step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, 0, -1], ![0, -1, -1, 2], ![3, -1, 0, -2]]

def raw2108step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, 0, -2, 1]]

def raw2109 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def raw2109step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -2, 0, 2], ![-1, 1, 1, -1], ![-1, 0, -1, 2]]

def raw2109step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -1, 1, -1]]

def raw2110 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw2110step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![0, 0, 1, -1], ![3, -2, -1, 0]]

def raw2110step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![0, 0, -1, 1], ![-3, 2, 1, 0]]

def raw2110step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw2111 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, 0, -2], ![1, -1, 2, -2], ![1, 0, -2, 1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2112 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, 1, -3], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw2112step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -2, -1, 3], ![-1, 1, 1, -1], ![-1, 0, 0, 1]]

def raw2112step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 1, -1, -1]]

def raw2113 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, 1, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw2113step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![0, 1, 0, -1], ![3, -3, 0, 0]]

def raw2113step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![0, -1, 0, 1], ![-3, 3, 0, 0]]

def raw2113step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, -1, 0]]

def raw2114 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, 1, -3], ![1, -1, 1, -1], ![1, 0, -2, 1]]

def raw2114step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -2, -1, 3], ![-1, 1, -1, 1], ![-1, 0, 2, -1]]

def raw2114step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 2, -3]]

def raw2115 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, -1, 0, 0]]

def raw2115step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, 0, -1], ![0, 1, -1, 0], ![3, -3, 0, 0]]

def raw2115step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 0, 1], ![0, -1, 1, 0], ![-3, 3, 0, 0]]

def raw2115step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, -1, 0]]

def raw2116 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, 2, -4], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw2116step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![0, 2, -1, -1], ![3, -4, 1, 0]]

def raw2116step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, 1, -2, 0]]

def raw2117 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, 2, -4], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw2117step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![0, 2, 0, -2], ![3, -4, 0, 1]]

def raw2117step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![0, -2, 0, 2], ![-3, 4, 0, -1]]

def raw2117step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw2118 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![1, -1, -2, 2], ![0, 0, 2, -2], ![1, 2, 0, -3]]

def raw2118step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![-1, 1, 2, -2], ![0, 0, -2, 2], ![-1, -2, 0, 3]]

def raw2118step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![1, -1, 2, -2], ![1, 2, 0, -3]]

def raw2119 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![1, -1, -1, 1], ![0, 1, 2, -3], ![1, 1, -1, -1]]

def raw2119step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def raw2120 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![1, -1, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw2120step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![-1, -1, 2, 0], ![0, 1, -1, 0], ![3, -1, -1, -1]]

def raw2120step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw2121 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![1, -1, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw2121step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![-1, -1, 2, 0], ![0, 1, 0, -1], ![3, -1, -2, 0]]

def raw2121step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![1, 1, -2, 0], ![0, -1, 0, 1], ![-3, 1, 2, 0]]

def raw2121step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw2122 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![1, -1, 2, -2], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def raw2122step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 2, -2], ![1, 1, 0, -2]]

def raw2123 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![1, -1, 2, -2], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw2123step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![-1, -1, 2, 0], ![0, 2, -2, 0], ![3, -2, 0, -1]]

def raw2123step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 2, 0], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw2124 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![1, -1, 2, -2], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw2124step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![-1, -1, 2, 0], ![0, 2, -1, -1], ![3, -2, -1, 0]]

def raw2124step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, 0, -2, 1]]

def raw2125 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![1, -1, 2, -2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw2125step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, 0, -2], ![1, -1, 2, -2], ![1, 0, -2, 1]]

def raw2126 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![1, 0, -2, 1], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def raw2126step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![-1, 0, 1, 0], ![0, -2, 3, -1], ![3, 1, -4, 0]]

def raw2126step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, 1, -2, 0]]

def raw2127 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![1, 0, -2, 1], ![0, 2, 0, -2], ![1, -1, 2, -2]]

def raw2127step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, 0, -2], ![1, -1, 2, -2], ![1, 0, -2, 1]]

def raw2128 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![1, 0, -2, 1], ![0, 2, 1, -3], ![1, -1, 1, -1]]

def raw2128step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![-1, 0, 2, -1], ![0, -2, -1, 3], ![-1, 1, -1, 1]]

def raw2128step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 2, -3]]

def raw2129 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![1, 0, 1, -2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw2129step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![-1, 0, -1, 2], ![0, -2, 0, 2], ![-1, 1, 1, -1]]

def raw2129step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -1, 1, -1]]

def raw2130 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![1, 0, 2, -3], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw2130step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 2, -3]]

def raw2131 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![1, 1, -3, 1], ![0, 1, 2, -3], ![1, -1, 1, -1]]

def raw2131step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 1, -3, 1]]

def raw2132 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![1, 1, -2, 0], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw2132step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw2133 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![-3, 2, 1, 0], ![5, -1, -2, -2]]

def raw2133step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![-1, 2, -1], ![1, 1, -2], ![2, 0, -2]]

def raw2133step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

def raw2134 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![-2, 2, 1, -1], ![4, -1, -2, -1]]

def raw2134step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]

def raw2135 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![-2, 3, 1, -2], ![4, -2, -2, 0]]

def raw2135step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![1, 1, -2], ![2, -2, 0]]

def raw2141 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![-1, -1, 1, 1], ![3, 2, -2, -3]]

def raw2141step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 1, -2], ![2, 1, -3]]

def raw2141step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![1, 1, -2], ![1, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical67
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2144 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![-1, -1, 2, 0], ![3, 2, -3, -2]]

def raw2144step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 2, -3], ![2, 0, -2]]

def raw2144step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![-1, -2, 3], ![-2, 0, 2]]

def raw2144step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 1, -2], ![1, 2, -3]]

def raw2145 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![-1, 2, -2, 1], ![3, -1, 1, -3]]

def raw2145step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![2, 1, -3]]

def raw2146 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![-1, 2, 1, -2], ![3, -1, -2, 0]]

def raw2146step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]

def raw2146step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, -1, 2], ![-2, 2, 0]]

def raw2146step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

def raw2147 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![-1, 3, -2, 0], ![3, -2, 1, -2]]

def raw2147step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![1, -2, 1], ![2, 0, -2]]

def raw2147step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -3, 2], ![-1, 2, -1], ![-2, 0, 2]]

def raw2147step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]

def raw2151 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -2, 2, 0], ![2, 3, -3, -2]]

def raw2151step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![1, 2, -3], ![2, 0, -2]]

def raw2151step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![2, 1, -3]]

def raw2152 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -2, 3, -1], ![2, 3, -4, -1]]

def raw2152step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![1, 3, -4], ![2, -1, -1]]

def raw2152step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 2, -3], ![-1, -3, 4], ![-2, 1, 1]]

def raw2152step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]

def raw2153 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, 0, -3]]

def raw2153step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, -1, -2], ![0, 1, 1, -2], ![0, 0, -1, 1], ![0, -1, 1, 0], ![-2, -1, 0, 3]]

def raw2153step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, 1, -2], ![2, 1, -1, -2]]

def raw2154 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 2, -4]]

def raw2155 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def raw2156 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw2157 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 1, -3]]

def raw2158 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![2, 1, 1, -4]]

def raw2158step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, -1, 1, 1], ![1, -1, -1, 1], ![2, 2, 0, -4]]

def raw2158step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -1, -1, 1]]

def raw2159 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw2160 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw2161 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw2162 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw2163 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 1, 1, -2], ![2, 1, -1, -2]]

def raw2164 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 2, -2, 0], ![2, 0, 2, -4]]

def raw2165 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw2166 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 2, -1, -1], ![2, 0, 1, -3]]

def raw2166step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, -1, -2], ![0, 1, 1, -2], ![0, -2, 1, 1], ![-2, 0, -1, 3]]

def raw2166step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, 1, -2]]

def raw2167 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw2168 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 2, 0, -2], ![2, 0, 0, -2]]

def raw2168step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw2169 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 2, 1, -3], ![2, 0, -1, -1]]

def raw2169step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, -1, -2], ![0, 1, 1, -2], ![0, -2, -1, 3], ![-2, 0, 1, 1]]

def raw2169step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 2, -2], ![1, 1, 0, -2]]

def raw2170 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw2171 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 2, 2, -4], ![2, 0, -2, 0]]

def raw2172 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 0, -1, 0], ![1, 2, 1, -4]]

def raw2172step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, -1, 0, 2], ![1, -1, -1, 1], ![2, 2, 0, -4]]

def raw2172step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw2173 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 0, 0, -1], ![1, 2, 0, -3]]

def raw2173step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -2, 2]]

def raw2174 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 0, 1, -2], ![1, 2, -1, -2]]

def raw2175 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 1, -2, 0], ![1, 1, 2, -4]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2176 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def raw2177 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 1, 1, -3], ![1, 1, -1, -1]]

def raw2177step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def raw2178 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 2, -1, -2], ![1, 0, 1, -2]]

def raw2178step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 0, 1, -2], ![1, 2, -1, -2]]

def raw2179 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 2, 1, -4], ![1, 0, -1, 0]]

def raw2179step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, -1, 2, 0], ![1, -1, 1, -1], ![2, 2, -4, 0]]

def raw2179step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw2180 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, 0, -2]]

def raw2180step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw2181 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def raw2182 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw2183 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw2183step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw2184 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw2184step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -1, 2]]

def raw2185 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def raw2185step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -2, -1, 2]]

def raw2186 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw2186step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw2187 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw2187step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw2188 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![1, 1, -2, 0], ![1, 1, 1, -3]]

def raw2188step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, -1, 1, 1], ![1, 0, -2, 1], ![2, 1, 0, -3]]

def raw2188step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, 1, -1, -1], ![-1, 0, 2, -1], ![-2, -1, 0, 3]]

def raw2188step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def raw2191 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw2192 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw2193 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw2193step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, -1, -2], ![0, 1, -1, 0], ![0, -1, 1, 0], ![-1, 0, 1, 0], ![-1, -1, 0, 2]]

def raw2193step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw2194 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw2195 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw2196 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw2197 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw2198 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def raw2198step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, -1, 1, 1], ![1, 1, 0, -2], ![2, 0, -1, -1]]

def raw2198step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, 1, -1]]

def raw2199 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw2200 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw2200step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, -1, -2], ![0, 1, -1, 0], ![0, -2, 1, 1], ![-1, 0, 1, 0], ![-1, 0, 0, 1]]

def raw2200step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw2201 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw2201step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, -1, 2, 0], ![1, 1, -1, -1], ![2, 0, -1, -1]]

def raw2201step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw2202 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw2202step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, -1, -2], ![0, 1, -1, 0], ![0, -2, 0, 2], ![-1, 0, 1, 0], ![-1, 0, 1, 0]]

def raw2202step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw2203 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![1, 0, 0, -1], ![1, 2, -2, -1]]

def raw2203step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, -1, 0, 2], ![1, 1, 0, -2], ![2, 0, -1, -1]]

def raw2203step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 0, 1, -2]]

def raw2204 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def raw2204step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, -1, 1, 1], ![1, 1, -1, -1], ![2, 0, -1, -1]]

def raw2204step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, -1, -1, 1]]

def raw2205 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 2, -1], ![2, 2, -3, -1]]

def raw2205step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 2, -3], ![2, -1, -1]]

def raw2205step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-1, -2, 3], ![-2, 1, 1]]

def raw2205step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def raw2206 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 3, -2], ![2, 2, -4, 0]]

def raw2206step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 3, -4], ![2, -2, 0]]

def raw2206step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-1, -3, 4], ![-2, 2, 0]]

def raw2206step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

def raw2207 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 2, 0, -3]]

def raw2207step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, -1, -2], ![0, 0, 2, -2], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, -2, 0, 3]]

def raw2207step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 2, -1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2208 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw2209 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 1, 1, -3]]

def raw2210 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![2, 0, 2, -4]]

def raw2210step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw2211 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, 1, -2]]

def raw2212 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def raw2213 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw2214 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def raw2215 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 0, 0, -1]]

def raw2215step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw2216 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![2, 0, 1, -3]]

def raw2216step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw2217 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def raw2217step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def raw2218 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def raw2218step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw2219 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw2220 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw2221 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, -1, 1, -2]]

def raw2222 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw2222step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, -1, -2], ![0, 0, 2, -2], ![0, -2, -1, 3], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw2222step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw2223 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw2224 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![2, -1, 0, -1]]

def raw2224step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, -1, -2], ![0, 0, 2, -2], ![0, -2, -1, 3], ![-2, 1, 0, 1]]

def raw2224step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, 0, -2], ![1, -1, 2, -2], ![1, 0, -2, 1]]

def raw2225 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw2226 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![2, -1, -1, 0]]

def raw2226step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 2, -1], ![1, -2, 2, -1], ![2, 2, -4, 0]]

def raw2226step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 2, -2, 0], ![2, 0, 2, -4]]

def raw2227 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 2, 1, -4]]

def raw2227step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, -1, 2], ![1, -2, 0, 1], ![2, 2, 0, -4]]

def raw2227step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw2228 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![1, -1, 1, -1], ![1, 2, 0, -3]]

def raw2228step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, -1, -2], ![0, 0, 2, -2], ![-1, 1, -1, 1], ![-1, -2, 0, 3]]

def raw2228step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 2, -1, -2]]

def raw2229 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw2229step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, 1, 2, -4]]

def raw2230 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![1, 0, 0, -1], ![1, 1, 1, -3]]

def raw2230step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 1, 1, -3]]

def raw2231 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![1, 0, 1, -2], ![1, 1, 0, -2]]

def raw2231step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 1, 0, -2]]

def raw2232 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![1, 1, 0, -2], ![1, 0, 1, -2]]

def raw2232step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 1, 0, -2]]

def raw2233 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![1, 1, 2, -4], ![1, 0, -1, 0]]

def raw2233step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, 1, 2, -4]]

def raw2234 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![1, 2, 0, -3], ![1, -1, 1, -1]]

def raw2234step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, -1, -2], ![0, 0, 2, -2], ![-1, -2, 0, 3], ![-1, 1, -1, 1]]

def raw2234step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 2, -1, -2]]

def raw2235 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, -1, 0, 1], ![0, 2, 0, -2], ![2, 0, 0, -2]]

def raw2235step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw2236 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![2, 0, 2, -4]]

def raw2236step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw2237 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def raw2237step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw2238 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, -1, 1, -2]]

def raw2238step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, -1, -2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -2, 0, 2], ![-2, 1, -1, 2]]

def raw2238step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, 1, -2]]

def raw2239 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw2239step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 1, 2, -4]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw224 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]

def raw225 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

def raw226 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]

def raw227 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]

def raw228 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]

def raw228step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw229 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]

def raw229step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

def raw230 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]

def raw230step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def raw231 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]

def raw232 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

def raw232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

def raw233 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def raw233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

def raw234 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw235 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1]]

def raw235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw236 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]

def raw237 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]

def raw237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw238 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]

def raw238step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

def raw239 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

def raw240 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![2, -1, -1], ![1, 1, -2]]

def raw240step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

def raw241 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![3, 0, -3]]

def raw241step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 3, -3], ![2, 0, -2]]

def raw242 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def raw243 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]

def raw244 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]

def raw245 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![2, -1, -1], ![1, 0, -1]]

def raw245step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]

def raw246 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![3, -1, -2]]

def raw247 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]

def raw248 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]

def raw249 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 2, -3], ![1, 1, -2]]

def raw249step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]

def raw250 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![2, 3, -5]]

def raw250step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, -1, 3], ![5, 0, -5]]

def raw250step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 5, -5], ![1, -3, 2]]

def raw251 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]

def raw251step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]

def raw252 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]

def raw252step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

def raw253 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![2, 2, -4]]

def raw253step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![5, -1, -4]]

def raw253step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 2, -2], ![1, 2, -3]]

def raw254 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 1, -2], ![1, 0, -1], ![1, 1, -2]]

def raw254step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

def raw255 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 1, -2], ![2, 1, -3]]

def raw255step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![1, 1, -2], ![1, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2240 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, 0, -1], ![1, 1, 1, -3]]

def raw2240step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 1, 1, -3]]

def raw2241 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw2241step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw2241step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw2242 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 0, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw2242step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 0, 0, 1], ![1, -1, 0, -1, 1], ![2, 1, 0, 0, -3]]

def raw2242step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, 0, 1], ![1, -1, -1, 1], ![2, 1, 0, -3]]

def raw2242step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, 0, 2, -3]]

def raw2243 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 0, 0], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw2243step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw2243step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw2244 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw2244step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw2245 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw2245step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def raw2246 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw2247 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 0, -1, 1], ![2, 0, 2, -4]]

def raw2247step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw2248 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 0, 1, -1], ![2, 0, 0, -2]]

def raw2248step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw2249 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 2, -3]]

def raw2250 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def raw2251 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def raw2252 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw2253 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 2, -3]]

def raw2253step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw2254 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw2254step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw2255 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 0, 1, -1], ![2, 0, -1, -1]]

def raw2255step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw2256 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def raw2256step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw2257 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, -1, -1, 0]]

def raw2258 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def raw2259 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw2260 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw2260step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw2261 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw2261step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, -1, -2], ![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 0, 0, 1], ![-1, 0, 0, 1]]

def raw2261step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 2, -2]]

def raw2262 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 0, -1, 0]]

def raw2262step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw2263 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw2263step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, -1, -2], ![0, 0, 1, -1], ![0, -1, 0, 1], ![-2, 0, 0, 2]]

def raw2263step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 2, -2]]

def raw2264 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw2265 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw2265step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw2266 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 0, -1, 0]]

def raw2266step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw2267 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw2267step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw2268 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw2268step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def raw2269 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw2270 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw2271 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, -1, 1, -1]]

def raw2271step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2272 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![2, -1, 1, -2]]

def raw2272step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 2, -1], ![1, -1, -1, 1], ![2, 1, -1, -2]]

def raw2272step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, -1, -1], ![1, -1, 2, -2]]

def raw2273 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def raw2274 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw2274step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw2275 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw2276 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, -1, 1, -1]]

def raw2276step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw2277 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, -1, 0, -1]]

def raw2277step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw2278 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw2278step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, -1, -2], ![0, 0, 1, -1], ![0, -2, -1, 3], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw2278step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw2279 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw2280 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw2281 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0], ![1, -1, -1, 1]]

def raw2281step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw2282 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw2282step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, 0, 1], ![1, -1, -1, 1], ![2, 1, 0, -3]]

def raw2282step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, 0, 2, -3]]

def raw2283 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw2283step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, -1, -2], ![0, 0, 1, -1], ![-1, 0, 0, 1], ![-1, -1, 0, 2]]

def raw2283step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 2, -2]]

def raw2284 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw2284step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw2285 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![1, 1, -1, -1], ![1, 0, 1, -2]]

def raw2285step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw2286 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 0, 0], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw2286step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 1, -1, 1], ![1, 0, -2, 0, 1], ![2, 0, 1, 0, -3]]

def raw2286step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, -1, -1], ![1, 0, -1, 1, -1], ![-1, 0, 2, 0, -1], ![-2, 0, -1, 0, 3]]

def raw2286step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 1, -1], ![-1, 2, 0, -1], ![-2, -1, 0, 3]]

def raw2286step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw2287 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 0, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def raw2287step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![-1, 0, 1, 1, -1], ![1, 0, -1, -1, 1], ![2, 0, 0, 0, -2]]

def raw2287step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![1, -1, -1, 1], ![2, 0, 0, -2]]

def raw2287step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 1, -1, -1]]

def raw2288 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 0, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def raw2288step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![-1, 0, 1, 1, -1], ![1, 0, -1, 0, 0], ![2, 0, 0, -1, -1]]

def raw2288step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, 0, -2], ![1, 0, -1, -1, 1], ![-1, 0, 1, 0, 0], ![-2, 0, 0, 1, 1]]

def raw2288step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![1, -1, -1, 1], ![-1, 1, 0, 0], ![-2, 0, 1, 1]]

def raw2288step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw2289 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 0, 0], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -1, -1, 0]]

def raw2289step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![-1, 0, 1, 1, -1], ![1, 0, -1, 1, -1], ![2, 0, 0, -2, 0]]

def raw2289step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![1, -1, 1, -1], ![2, 0, -2, 0]]

def raw2289step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw2290 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 0, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def raw2290step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 1, -1, 1], ![1, 0, -1, -1, 1], ![2, 0, 0, 1, -3]]

def raw2290step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![1, -1, -1, 1], ![2, 0, 1, -3]]

def raw2290step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -3, 2], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw2291 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 0, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw2291step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 1, -1, 1], ![1, 0, -1, 0, 0], ![2, 0, 0, 0, -2]]

def raw2291step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, -1, -1], ![1, 0, -1, 1, -1], ![-1, 0, 1, 0, 0], ![-2, 0, 0, 0, 2]]

def raw2291step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 1, -1], ![-1, 1, 0, 0], ![-2, 0, 0, 2]]

def raw2291step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1]]

def raw2292 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 0, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw2292step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 1, 0, 0], ![1, 0, -1, 0, 0], ![2, 0, 0, -1, -1]]

def raw2292step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![1, -1, 0, 0], ![2, 0, -1, -1]]

def raw2292step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 1, 0, -2]]

def raw2293 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 0, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw2293step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 1, 0], ![1, 0, -1, 0], ![2, 0, 0, -2]]

def raw2293step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]

def raw2293step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

def raw2294 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 0, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw2294step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![-1, 0, 1, 1, -1], ![1, 0, 0, 0, -1], ![2, 0, -1, -1, 0]]

def raw2294step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![1, 0, 0, -1], ![2, -1, -1, 0]]

def raw2294step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, -1, -1]]

def raw2295 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw2295step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 1, -1, 1], ![1, 0, 0, 0, -1], ![2, 0, -1, 0, -1]]

def raw2295step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![1, 0, 0, -1], ![2, -1, 0, -1]]

def raw2295step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw2296 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw2296step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 1, -1, 1], ![1, 0, 0, 1, -2], ![2, 0, -1, -1, 0]]

def raw2296step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![1, 0, 1, -2], ![2, -1, -1, 0]]

def raw2296step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw2297 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw2297step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 1, 0, 0], ![1, 0, 0, -1, 0], ![2, 0, -1, 0, -1]]

def raw2297step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![1, 0, -1, 0], ![2, -1, 0, -1]]

def raw2297step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw2298 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 0, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw2298step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 1, 0], ![1, 0, 0, -1], ![2, 0, -1, -1]]

def raw2298step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]

def raw2298step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

def raw2299 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 0, 0], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw2299step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 1, -1, 1], ![1, 0, 1, 0, -2], ![2, 0, -2, 0, 0]]

def raw2299step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, -1, -1], ![1, 0, -1, 1, -1], ![-1, 0, -1, 0, 2], ![-2, 0, 2, 0, 0]]

def raw2299step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 1, -1], ![-1, -1, 0, 2], ![-2, 2, 0, 0]]

def raw2299step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw2300 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 0, 0], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw2300step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 1, 0, 0], ![1, 0, 1, -1, -1], ![2, 0, -2, 0, 0]]

def raw2300step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, -1, -1], ![1, 0, -1, 0, 0], ![-1, 0, -1, 1, 1], ![-2, 0, 2, 0, 0]]

def raw2300step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 0, 0], ![-1, -1, 1, 1], ![-2, 2, 0, 0]]

def raw2300step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, -1, -1]]

def raw2301 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 0, 0], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw2301step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 2, -1, 0], ![1, 0, -2, 0, 1], ![2, 0, 0, 0, -2]]

def raw2301step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, -1, -1], ![1, 0, -2, 1, 0], ![-1, 0, 2, 0, -1], ![-2, 0, 0, 0, 2]]

def raw2301step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![-1, 2, 0, -1], ![-2, 0, 0, 2]]

def raw2301step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw2302 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 0, 0], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw2302step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 2, -1, 0], ![1, 0, -2, 1, 0], ![2, 0, 0, -1, -1]]

def raw2302step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![1, -2, 1, 0], ![2, 0, -1, -1]]

def raw2302step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def raw2303 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 0, 0], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw2303step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 2, -1, 0], ![1, 0, -1, 0, 0], ![2, 0, -1, 0, -1]]

def raw2303step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, -1, -1], ![1, 0, -2, 1, 0], ![-1, 0, 1, 0, 0], ![-2, 0, 1, 0, 1]]

def raw2303step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![-1, 1, 0, 0], ![-2, 1, 0, 1]]

def raw2303step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2304 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 0, 0], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw2304step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 2, -1, 0], ![1, 0, 0, -1, 0], ![2, 0, -2, 1, -1]]

def raw2304step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![1, 0, -1, 0], ![2, -2, 1, -1]]

def raw2304step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw2305 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 0, 0], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw2305step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 2, -1, 0], ![1, 0, 0, 0, -1], ![2, 0, -2, 0, 0]]

def raw2305step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, -1, -1], ![1, 0, -2, 1, 0], ![-1, 0, 0, 0, 1], ![-2, 0, 2, 0, 0]]

def raw2305step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![-1, 0, 0, 1], ![-2, 2, 0, 0]]

def raw2305step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw2306 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 0, 0], ![0, 2, 1, -3], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw2306step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 2, -1, 0], ![1, 0, 1, -1, -1], ![2, 0, -3, 1, 0]]

def raw2306step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, -1, -1], ![1, 0, -2, 1, 0], ![-1, 0, -1, 1, 1], ![-2, 0, 3, -1, 0]]

def raw2306step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![-1, -1, 1, 1], ![-2, 3, -1, 0]]

def raw2306step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, 1, -1, -1]]

def raw2307 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 0, 0], ![0, 2, 1, -3], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw2307step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 2, -1, 0], ![1, 0, 1, 0, -2], ![2, 0, -3, 0, 1]]

def raw2307step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, -1, -1], ![1, 0, -2, 1, 0], ![-1, 0, -1, 0, 2], ![-2, 0, 3, 0, -1]]

def raw2307step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![-1, -1, 0, 2], ![-2, 3, 0, -1]]

def raw2307step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, 0, -2, 1]]

def raw2308 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 0, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw2308step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, 0, 1], ![1, 0, 0, -1], ![2, 0, -1, -1]]

def raw2308step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]

def raw2308step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

def raw2309 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw2309step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![-1, 0, 0, 1, 0], ![1, 1, 0, 0, -2], ![2, -1, 0, -1, 0]]

def raw2309step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 1, 0], ![1, 1, 0, -2], ![2, -1, -1, 0]]

def raw2309step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw2310 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 0, 0, 0], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw2310step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 0, 0, 1], ![1, 1, 0, -1, -1], ![2, -1, 0, 0, -1]]

def raw2310step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, -1, -1], ![1, 0, 0, 0, -1], ![-1, -1, 0, 1, 1], ![-2, 1, 0, 0, 1]]

def raw2310step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, 0, 0, -1], ![-1, -1, 1, 1], ![-2, 1, 0, 1]]

def raw2310step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw2311 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 0, 0, 0], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw2311step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 0, 0, 1], ![1, 1, 0, 0, -2], ![2, -1, 0, -1, 0]]

def raw2311step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, 0, 1], ![1, 1, 0, -2], ![2, -1, -1, 0]]

def raw2311step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 1, -2]]

def raw2312 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 0, 0, 0], ![2, 1, -2, -1]]

def raw2312step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 0, 1], ![1, 1, 0, -2], ![2, -1, 0, -1]]

def raw2312step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]

def raw2312step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1]]

def raw2313 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -3, 2], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw2314 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def raw2315 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def raw2316 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, -1, 0]]

def raw2317 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def raw2318 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw2319 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw2319step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1]]

def raw2320 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -2, 1], ![2, -1, 1, -2]]

def raw2320step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def raw2321 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def raw2322 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw2323 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -1, -2, 1]]

def raw2324 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -2, 2], ![1, 1, 1, -3]]

def raw2325 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def raw2326 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw2327 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw2327step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def raw2328 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 0, 0, 0], ![2, 0, -2, 0]]

def raw2328step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![-1, 0, 1, 0, 0], ![1, 1, 0, 0, -2], ![2, -1, -1, 0, 0]]

def raw2328step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 1, 0], ![1, 1, 0, -2], ![2, -1, -1, 0]]

def raw2328step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw2329 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![2, -1, -1, 0]]

def raw2329step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw2330 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -2, 1]]

def raw2331 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def raw2332 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw2333 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -3, 1]]

def raw2334 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def raw2334step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw2335 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw2335step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2336 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, -2, 1]]

def raw2336step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw2337 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw2337step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 1, 0], ![1, 1, 0, -2], ![2, -1, -1, 0]]

def raw2337step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw2338 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 1, -2, 0]]

def raw2339 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -3, 1]]

def raw2340 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw2341 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw2342 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def raw2343 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw2344 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw2344step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw2345 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, -1, 0, 0]]

def raw2345step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw2346 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, -1, 0, -1]]

def raw2346step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 2, -1], ![1, 1, -2, 0], ![2, -1, 0, -1]]

def raw2346step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw2347 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw2348 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw2348step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, -1, -2], ![0, 0, -1, 1], ![0, -2, 1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw2348step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw2349 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -1, -1, 0]]

def raw2349step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 2, -1], ![1, 1, -1, -1], ![2, -1, -1, 0]]

def raw2349step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw2350 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -2, 2], ![1, 0, 0, -1]]

def raw2351 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw2352 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw2353 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, -1, -1, 1]]

def raw2353step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw2354 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -2, 2], ![1, 0, -1, 0]]

def raw2355 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -1, 1], ![1, 0, -2, 1]]

def raw2356 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, 0, 0], ![1, 0, -3, 2]]

def raw2357 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 2, -1, -2]]

def raw2357step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, -1, 2], ![1, 1, -1, -1], ![2, -1, 1, -2]]

def raw2357step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, -1, -1, 1]]

def raw2358 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 2, -2, -1]]

def raw2358step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, -1, 2], ![1, 1, 0, -2], ![2, -1, 0, -1]]

def raw2358step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, -2, 1]]

def raw2359 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw2359step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, 0, 1], ![1, 1, -1, -1], ![2, -1, 0, -1]]

def raw2359step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, 0, 0, -1], ![-1, -1, 1, 1], ![-2, 1, 0, 1]]

def raw2359step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw2360 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw2360step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, 0, 1], ![1, 1, 0, -2], ![2, -1, -1, 0]]

def raw2360step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 1, -2]]

def raw2361 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def raw2362 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw2363 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, 0, -1, -1]]

def raw2363step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, -2, 1]]

def raw2364 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -2, 1], ![2, -1, 0, -1]]

def raw2364step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def raw2365 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, -1, 0]]

def raw2365step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def raw2366 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -2, 1]]

def raw2367 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, -1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical74
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2368 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw2368step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw2369 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def raw2369step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw2370 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, -2, 0]]

def raw2371 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -3, 1]]

def raw2372 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, -1, 0]]

def raw2372step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw2373 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, 0, -3, 1]]

def raw2373step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 2, -2], ![0, 2, -3, 1], ![1, 0, 0, -1]]

def raw2374 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 2, -3, 1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw2375 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 2, -3, 1], ![2, -1, 0, -1]]

def raw2375step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 2, -1], ![1, 2, -3, 0], ![2, -2, 1, -1]]

def raw2375step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -3, 1]]

def raw2376 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw2377 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw2377step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw2378 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![2, -1, -1, 0]]

def raw2378step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, -1, 0, -1]]

def raw2379 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw2380 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, -1, -2, 1]]

def raw2381 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 2, -2, -1]]

def raw2382 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 2, -3, 0]]

def raw2382step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, -1, 2], ![1, 2, 0, -3], ![2, -2, 0, 0]]

def raw2382step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 2, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw2383 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![1, 0, -2, 1], ![1, 1, -1, -1]]

def raw2383step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 1, -1, -1]]

def raw2384 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![1, 0, -1, 0], ![1, 1, -2, 0]]

def raw2384step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 1, 0, -2]]

def raw2385 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![1, 0, 0, -1], ![1, 1, -3, 1]]

def raw2385step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, 0, 1], ![1, 2, 0, -3], ![2, -2, -1, 1]]

def raw2385step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, 0, 1, -2]]

def raw2386 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![1, 1, -3, 1], ![1, 0, 0, -1]]

def raw2386step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, 1, 0], ![1, 2, -3, 0], ![2, -2, 1, -1]]

def raw2386step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, 0, 1, -2]]

def raw2387 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![1, 2, -2, -1], ![1, -1, -1, 1]]

def raw2387step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 2, -2, -1]]

def raw2388 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -3, 2], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw2388step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![1, -3, 0, 2], ![2, 2, 0, -4]]

def raw2388step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -3, 2], ![0, 2, 2, -4], ![1, -2, 0, 1]]

def raw2389 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -3, 2], ![1, -1, 1, -1], ![1, 1, 1, -3]]

def raw2390 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw2390step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1]]

def raw2391 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 0, 1, -1], ![2, 0, 0, -2]]

def raw2391step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw2392 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw2393 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -1, 2, -3]]

def raw2393step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![1, -2, -1, 2], ![2, 1, 0, -3]]

def raw2393step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, 1, -1, -1]]

def raw2394 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw2395 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw2396 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, -1, 1, -1]]

def raw2396step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw2397 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -1, 1, -2]]

def raw2397step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![1, -2, 0, 1], ![2, 1, -1, -2]]

def raw2397step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![1, -1, -1, 1], ![-1, 2, 0, -1], ![-2, -1, 1, 2]]

def raw2397step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, -1, -1], ![1, -1, 2, -2]]

def raw2398 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw2399 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2400 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw2401 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![2, -1, -1, 0]]

def raw2402 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def raw2403 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw2403step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![1, -2, 0, 1], ![2, 1, 0, -3]]

def raw2403step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 1, -1], ![-1, 2, 0, -1], ![-2, -1, 0, 3]]

def raw2403step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw2404 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def raw2405 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![1, 0, -1, 0], ![1, 0, 2, -3]]

def raw2405step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -2, 1]]

def raw2406 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw2406step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![1, -2, 0, 1], ![2, 1, -1, -2]]

def raw2406step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def raw2407 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![1, 0, 1, -2], ![1, 0, 0, -1]]

def raw2407step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![1, -2, 1, 0], ![2, 1, -2, -1]]

def raw2407step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def raw2408 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![1, 0, 2, -3], ![1, 0, -1, 0]]

def raw2408step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -2, 1]]

def raw2409 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 0, 0, 0], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw2409step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 1, 0, 0, 0], ![1, -1, 0, -1, 1], ![2, 0, 0, 0, -2]]

def raw2409step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![1, -1, -1, 1], ![2, 0, 0, -2]]

def raw2409step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw2410 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 0, 0, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw2410step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 1, 0, 0, 0], ![1, -1, 0, 0, 0], ![2, 0, 0, -1, -1]]

def raw2410step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![1, -1, 0, 0], ![2, 0, -1, -1]]

def raw2410step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 1, 0, -2]]

def raw2411 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 0, 0, 0], ![2, 0, 0, -2]]

def raw2411step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 0, 0], ![1, -1, 0, 0], ![2, 0, 0, -2]]

def raw2411step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]

def raw2411step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

def raw2412 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw2412step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw2413 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 0, 1, -1], ![2, 0, -1, -1]]

def raw2413step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 0, 0], ![1, -1, 1, -1], ![2, 0, -1, -1]]

def raw2413step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1]]

def raw2414 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, -2, 1], ![2, -1, 2, -3]]

def raw2414step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![1, -1, -2, 2], ![2, 0, 1, -3]]

def raw2414step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, 1, -1, -1]]

def raw2415 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 2, -3]]

def raw2416 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw2416step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, -1, -2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, -1, 2]]

def raw2416step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def raw2417 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw2418 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, -1, 1, -1]]

def raw2418step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw2419 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def raw2419step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![1, -1, -1, 1], ![2, 0, 0, -2]]

def raw2419step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 1, -1, -1]]

def raw2420 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def raw2421 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw2421step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, -1, -2], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw2421step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw2422 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw2423 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, -1, 1, -1]]

def raw2423step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw2424 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def raw2424step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![1, -1, 0, 0], ![2, 0, -1, -1]]

def raw2424step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![1, -1, -1, 1], ![-1, 1, 0, 0], ![-2, 0, 1, 1]]

def raw2424step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw2425 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw2426 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw2426step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, -1, -2], ![0, -1, 1, 0], ![0, -1, -1, 2], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw2426step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw2427 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, -1, 0, 0]]

def raw2427step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, -1, -2], ![0, -1, 1, 0], ![0, -1, -1, 2], ![-1, 0, 1, 0], ![-1, 1, 0, 0]]

def raw2427step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw2428 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -1, -1, 0]]

def raw2428step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![1, -1, 1, -1], ![2, 0, -2, 0]]

def raw2428step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw2429 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw2430 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw2431 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, -1, -2, 1]]

def raw2431step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![1, -1, 2, -2], ![2, 0, -3, 1]]

def raw2431step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, 2, -3], ![0, 2, -2, 0], ![1, -1, -1, 1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2432 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![1, -1, -2, 2], ![1, 1, 2, -4]]

def raw2432step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![1, -1, -2, 2], ![2, 0, 2, -4]]

def raw2432step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -2, 1], ![0, 2, 2, -4], ![1, -1, -1, 1]]

def raw2433 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def raw2433step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![1, -1, -1, 1], ![2, 0, 1, -3]]

def raw2433step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -3, 2], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw2434 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw2434step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![1, -1, 0, 0], ![2, 0, 0, -2]]

def raw2434step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 1, -1], ![-1, 1, 0, 0], ![-2, 0, 0, 2]]

def raw2434step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1]]

def raw2435 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw2435step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![1, -1, 1, -1], ![2, 0, -1, -1]]

def raw2435step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw2436 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![1, 0, -2, 1], ![1, 0, 2, -3]]

def raw2436step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw2437 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw2437step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![1, -1, -1, 1], ![2, 0, 0, -2]]

def raw2437step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw2438 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw2438step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![1, -1, 0, 0], ![2, 0, -1, -1]]

def raw2438step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 1, 0, -2]]

def raw2439 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 0, 1, -1], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def raw2439step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw2440 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw2440step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw2441 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 0, 1, -1], ![2, 0, -2, 0]]

def raw2441step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 0, 0], ![1, 0, 1, -2], ![2, -1, -1, 0]]

def raw2441step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw2442 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def raw2442step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def raw2443 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw2443step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, -1, -2], ![0, -1, 0, 1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw2443step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw2444 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw2444step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw2445 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def raw2445step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![1, 0, -1, 0], ![2, -1, 0, -1]]

def raw2445step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![1, -1, -1, 1], ![-1, 0, 1, 0], ![-2, 1, 0, 1]]

def raw2445step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw2446 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw2446step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw2447 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw2447step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, -1, -2], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw2447step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw2448 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -2, 1]]

def raw2449 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, -1, 1, -1]]

def raw2449step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -2, 1]]

def raw2450 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, -1, 0, 0]]

def raw2450step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, -1, -2], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 0, 1, 0], ![-1, 1, 0, 0]]

def raw2450step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw2451 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw2451step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![1, 0, 0, -1], ![2, -1, -1, 0]]

def raw2451step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, -1, -1]]

def raw2452 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw2453 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw2454 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, -1, -1, 1]]

def raw2454step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw2455 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, -1, -2, 1]]

def raw2455step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![1, 0, 1, -2], ![2, -1, -2, 1]]

def raw2455step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 1, -1, -1]]

def raw2456 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![1, -1, -2, 2], ![1, 1, 1, -3]]

def raw2456step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![1, 0, -2, 1], ![2, -1, 2, -3]]

def raw2456step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -3, 2, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw2457 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def raw2457step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![1, 0, -1, 0], ![2, -1, 1, -2]]

def raw2457step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw2458 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw2458step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![1, 0, 0, -1], ![2, -1, 0, -1]]

def raw2458step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw2459 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw2459step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![1, 0, 1, -2], ![2, -1, -1, 0]]

def raw2459step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw2460 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 1, -3, 1]]

def raw2460step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![1, 0, 2, -3], ![2, -1, -2, 1]]

def raw2460step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, 1, -2], ![0, 2, -3, 1], ![1, -1, 1, -1]]

def raw2461 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 1, -2]]

def raw2461step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw2462 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw2462step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![1, 0, -1, 0], ![2, -1, 0, -1]]

def raw2462step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw2463 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, -1, 0]]

def raw2463step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![1, 0, 0, -1], ![2, -1, -1, 0]]

def raw2463step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2464 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 0, -2, 1]]

def raw2464step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw2465 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 1, -2], ![0, 1, -2, 1], ![2, -1, 0, -1]]

def raw2465step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def raw2466 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 1, -2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw2466step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw2467 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 1, -2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw2467step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw2468 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 1, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw2468step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw2469 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 1, -2], ![0, 1, 0, -1], ![2, -1, -2, 1]]

def raw2469step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![1, 1, 0, -2], ![2, -2, -1, 1]]

def raw2469step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 1, -1, -1]]

def raw2470 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def raw2471 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw2471step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![1, 1, 0, -2], ![2, -2, 0, 0]]

def raw2471step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 1, -1], ![-1, -1, 0, 2], ![-2, 2, 0, 0]]

def raw2471step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw2472 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -3, 1]]

def raw2473 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 1, -2], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def raw2473step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw2474 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw2474step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![1, 1, -1, -1], ![2, -2, 0, 0]]

def raw2474step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 0, 0], ![-1, -1, 1, 1], ![-2, 2, 0, 0]]

def raw2474step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, -1, -1]]

def raw2475 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 0, -2, 1]]

def raw2475step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw2476 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 2, -3], ![0, 1, -2, 1], ![2, -1, -1, 0]]

def raw2476step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![2, -1, -1, 0]]

def raw2477 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, 1, -2, 0]]

def raw2478 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 1, -3, 1]]

def raw2478step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![1, 2, 0, -3], ![2, -3, 0, 1]]

def raw2478step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 1, -1], ![-1, -2, 0, 3], ![-2, 3, 0, -1]]

def raw2478step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 3, -2, -1], ![1, -1, -1, 1]]

def raw2479 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 2, -3], ![1, 0, -2, 1], ![1, 0, -1, 0]]

def raw2479step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![1, 2, -2, -1], ![2, -3, 1, 0]]

def raw2479step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 1, -2, 0]]

def raw2480 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 2, -3], ![1, 0, -1, 0], ![1, 0, -2, 1]]

def raw2480step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![1, 2, -1, -2], ![2, -3, 0, 1]]

def raw2480step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 1, -2, 0]]

def raw2481 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, -3, 1], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw2481step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![1, -3, 0, 2], ![2, 1, 0, -3]]

def raw2481step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![-1, 3, 0, -2], ![-2, -1, 0, 3]]

def raw2481step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -2, 3, -1], ![0, 3, -1, -2], ![1, 0, -2, 1]]

def raw2482 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, -3, 1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw2482step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![1, -3, 1, 1], ![2, 1, -1, -2]]

def raw2482step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 2, -1], ![1, 1, -3, 1], ![1, 1, 0, -2]]

def raw2483 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, -3, 1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def raw2483step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![1, -3, 2, 0], ![2, 1, -2, -1]]

def raw2483step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, -1, 2, -1], ![0, 2, -3, 1], ![1, 1, 0, -2]]

def raw2484 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, -2, 0], ![1, -1, -1, 1], ![1, 0, 2, -3]]

def raw2484step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![1, -2, -1, 2], ![2, 0, 1, -3]]

def raw2484step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![2, -1, -1, 0]]

def raw2485 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw2485step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![1, -2, 0, 1], ![2, 0, 0, -2]]

def raw2485step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![-1, 2, 0, -1], ![-2, 0, 0, 2]]

def raw2485step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw2486 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw2486step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![1, -2, 1, 0], ![2, 0, -1, -1]]

def raw2486step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def raw2487 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, -1, 1, -1]]

def raw2487step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, 0, -1], ![1, -2, 0, 1], ![2, 0, -1, -1]]

def raw2487step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def raw2488 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, -2, 0], ![2, -1, 1, -2]]

def raw2488step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]

def raw2488step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]

def raw2489 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def raw2490 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw2490step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![1, -1, 0, 0], ![2, -1, 0, -1]]

def raw2490step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![-1, 1, 0, 0], ![-2, 1, 0, 1]]

def raw2490step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 1, -2]]

def raw2491 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw2491step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![1, -1, 1, -1], ![2, -1, -1, 0]]

def raw2491step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![-1, 1, -1, 1], ![-2, 1, 1, 0]]

def raw2491step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw2492 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, -1, 1, -1]]

def raw2492step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, 0, -1], ![1, -1, -1, 1], ![2, -1, 0, -1]]

def raw2492step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 0, 1], ![-1, 1, 1, -1], ![-2, 1, 0, 1]]

def raw2492step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw2493 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, 0, -2], ![1, -1, -2, 2], ![1, 0, 1, -2]]

def raw2494 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw2494step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![1, 0, -1, 0], ![2, -2, 1, -1]]

def raw2494step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw2495 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw2495step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![1, 0, 0, -1], ![2, -2, 0, 0]]

def raw2495step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![-1, 0, 0, 1], ![-2, 2, 0, 0]]

def raw2495step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2496 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, -2, 1]]

def raw2496step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![1, 0, 1, -2], ![2, -2, -1, 1]]

def raw2496step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def raw2497 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, 0, -2], ![1, 0, -2, 1], ![1, -1, 1, -1]]

def raw2497step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, 0, -1], ![1, 0, -2, 1], ![2, -2, 1, -1]]

def raw2497step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def raw2498 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, 1, -3], ![1, -1, -2, 2], ![1, 0, 0, -1]]

def raw2498step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![1, 1, -2, 0], ![2, -3, 2, -1]]

def raw2498step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -3, 2, 2], ![0, 1, -2, 1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw2499 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, 1, -3], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw2499step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![1, 1, -1, -1], ![2, -3, 1, 0]]

def raw2499step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![-1, -1, 1, 1], ![-2, 3, -1, 0]]

def raw2499step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, 1, -1, -1]]

def raw2500 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, 1, -3], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw2500step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![1, 1, 0, -2], ![2, -3, 0, 1]]

def raw2500step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![-1, -1, 0, 2], ![-2, 3, 0, -1]]

def raw2500step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, 0, -2, 1]]

def raw2501 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, 1, -3], ![1, -1, 1, -1], ![1, 0, -3, 2]]

def raw2502 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, 2, -4], ![1, -1, -2, 2], ![1, 0, -1, 0]]

def raw2502step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![1, 2, -2, -1], ![2, -4, 2, 0]]

def raw2502step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 1, -2, 0]]

def raw2503 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, 2, -4], ![1, -1, -1, 1], ![1, 0, -2, 1]]

def raw2503step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![1, 2, -1, -2], ![2, -4, 1, 1]]

def raw2503step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 1, -2, 0], ![1, 1, 2, -4]]

def raw2504 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, 2, -4], ![1, -1, 0, 0], ![1, 0, -3, 2]]

def raw2504step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![1, 2, 0, -3], ![2, -4, 0, 2]]

def raw2504step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -3, 2], ![0, 2, 2, -4], ![1, -2, 1, 0]]

def raw2505 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 3, -3, 0], ![2, -2, 2, -2]]

def raw2505step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -3, 2], ![2, 0, -2]]

def raw2505step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]

def raw2506 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 3, -2, -1], ![2, -2, 1, -1]]

def raw2506step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]

def raw2506step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -3, 2], ![-1, 2, -1], ![-2, 1, 1]]

def raw2506step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

def raw2507 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 4, -3, -1], ![2, -3, 2, -1]]

def raw2507step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![1, -3, 2], ![2, -1, -1]]

def raw2508 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![1, -2, 2, -1], ![1, 3, -3, -1]]

def raw2508step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![1, 2, -3], ![2, -1, -1]]

def raw2508step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![2, 1, -3]]

def raw2509 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![1, -1, -2, 2], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw2509step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, 0, -2], ![1, -1, -2, 2], ![1, 0, 1, -2]]

def raw2510 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![1, -1, -2, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw2510step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![-1, -1, 2, 0], ![1, -2, 2, -1], ![2, 2, -4, 0]]

def raw2510step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 1, -2, 0]]

def raw2511 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![1, -1, -1, 1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw2511step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def raw2512 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![1, -1, -1, 1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw2512step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def raw2513 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![1, -1, 1, -1], ![1, 2, -2, -1]]

def raw2513step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]

def raw2513step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2]]

def raw2514 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![1, -1, 2, -2], ![0, 2, -3, 1], ![1, 0, 0, -1]]

def raw2514step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![-1, -1, 2, 0], ![1, 2, -3, 0], ![2, -2, 1, -1]]

def raw2514step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, -1, 2, -1], ![0, 2, -3, 1], ![1, 1, 0, -2]]

def raw2515 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![1, 0, -3, 2], ![0, 2, 1, -3], ![1, -1, 1, -1]]

def raw2515step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, 1, -3], ![1, -1, 1, -1], ![1, 0, -3, 2]]

def raw2516 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![1, 0, -2, 1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw2516step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw2517 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![1, 0, -2, 1], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw2517step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![-1, 0, 1, 0], ![1, -2, 2, -1], ![2, 1, -3, 0]]

def raw2517step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 1, -2, 0]]

def raw2518 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![1, 0, -2, 1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw2518step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![-1, 0, 2, -1], ![1, -2, 0, 1], ![2, 1, -2, -1]]

def raw2518step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def raw2519 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![1, 0, 1, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw2519step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def raw2520 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![1, 0, 2, -3], ![0, 2, -2, 0], ![1, -1, -1, 1]]

def raw2520step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![-1, 0, 2, -1], ![1, 2, -2, -1], ![2, -3, 0, 1]]

def raw2520step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![2, -1, -1, 0]]

def raw2521 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![1, 2, -2, -1], ![1, -1, 1, -1]]

def raw2521step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]

def raw2521step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2]]

def raw2522 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![-3, 2, 0, 1], ![5, -1, -2, -2]]

def raw2522step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![-1, 2, -1], ![2, 0, -2], ![1, 1, -2]]

def raw2522step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

def raw2523 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![-2, 2, -2, 2], ![4, -1, 0, -3]]

def raw2523step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![2, -2, 0], ![1, 2, -3]]

def raw2523step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 2, -3], ![2, -2, 0]]

def raw2524 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![-2, 2, -1, 1], ![4, -1, -1, -2]]

def raw2524step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![2, -1, -1], ![1, 1, -2]]

def raw2524step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]

def raw2525 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![-2, 2, 1, -1], ![4, -1, -3, 0]]

def raw2525step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![2, 1, -3], ![1, -1, 0]]

def raw2525step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]

def raw2526 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![-2, 3, -2, 1], ![4, -2, 0, -2]]

def raw2526step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![2, -2, 0], ![1, 1, -2]]

def raw2526step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![1, 1, -2], ![2, -2, 0]]

def raw2527 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![-1, -1, -1, 3], ![3, 2, -1, -4]]

def raw2527step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![2, -1, -1], ![1, 3, -4]]

def raw2527step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![-2, 1, 1], ![-1, -3, 4]]

def raw2527step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2528 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![-1, 2, -2, 1], ![3, -1, 0, -2]]

def raw2528step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![2, -2, 0], ![1, 1, -2]]

def raw2528step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-2, 2, 0], ![-1, -1, 2]]

def raw2528step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

def raw2529 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![-1, 2, 1, -2], ![3, -1, -3, 1]]

def raw2529step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![2, 1, -3], ![1, -2, 1]]

def raw2529step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![2, 1, -3]]

def raw2530 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![-1, 3, 0, -2], ![3, -2, -2, 1]]

def raw2530step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![2, 0, -2], ![1, -2, 1]]

def raw2530step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -3, 2], ![-2, 0, 2], ![-1, 2, -1]]

def raw2530step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]

def raw2531 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![-1, 4, -1, -2], ![3, -3, -1, 1]]

def raw2531step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 4, -3], ![2, -1, -1], ![1, -2, 1]]

def raw2531step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 4, -3], ![1, -2, 1], ![2, -1, -1]]

def raw2532 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -2, 1, 1], ![2, 3, -3, -2]]

def raw2532step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![2, 1, -3], ![1, 1, -2]]

def raw2532step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 1, -2], ![1, 2, -3]]

def raw2533 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -2, 3], ![0, 2, 0, -2], ![2, 0, 0, -2]]

def raw2533step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![2, -1, -2, 1]]

def raw2534 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -2, 3], ![2, 2, 0, -4]]

def raw2534step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![2, -2, 0], ![1, 3, -4]]

def raw2534step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-2, 2, 0], ![-1, -3, 4]]

def raw2534step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

def raw2535 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, 0, -2]]

def raw2536 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw2537 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw2538 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw2539 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw2540 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 1, 0, -1], ![2, 1, -1, -2]]

def raw2540step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, -1, 1, 1], ![2, -1, 0, -1], ![1, 2, -1, -2]]

def raw2540step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![1, 1, -1, -1], ![-2, 1, 0, 1], ![-1, -2, 1, 2]]

def raw2540step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, -2, 2, -1]]

def raw2541 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw2542 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def raw2543 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw2544 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw2545 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![1, 0, -1, 0], ![1, 2, 0, -3]]

def raw2545step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, -1, 0, 2], ![2, -1, -1, 0], ![1, 2, 0, -3]]

def raw2545step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -3, 1], ![1, 0, 1, -2]]

def raw2546 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![1, 0, 0, -1], ![1, 2, -1, -2]]

def raw2546step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, -1, 0, 2], ![2, -1, 0, -1], ![1, 2, -1, -2]]

def raw2546step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, 1, 0, -2], ![-2, 1, 0, 1], ![-1, -2, 1, 2]]

def raw2546step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -2, 2, -1]]

def raw2547 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def raw2548 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![1, 2, -1, -2], ![1, 0, 0, -1]]

def raw2548step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, -1, 2, 0], ![2, -1, -1, 0], ![1, 2, -2, -1]]

def raw2548step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, 1, -2, 0], ![-2, 1, 1, 0], ![-1, -2, 2, 1]]

def raw2548step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -2, 2, -1]]

def raw2549 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 2, -1], ![2, 2, -4, 0]]

def raw2549step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![2, 2, -4], ![1, -1, 0]]

def raw2549step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-2, -2, 4], ![-1, 1, 0]]

def raw2549step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def raw2550 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 3, -2], ![2, 2, -5, 1]]

def raw2550step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![2, 3, -5], ![1, -2, 1]]

def raw2550step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-2, -3, 5], ![-1, 2, -1]]

def raw2550step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

def raw2551 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw2551step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -3, 1]]

def raw2552 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def raw2553 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw2554 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw2554step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw2555 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw2555step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw2556 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw2556step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, -2, 1]]

def raw2557 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw2558 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, -1, 0, -1]]

def raw2559 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw2559step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 2, -3, 1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw256 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 2, -3], ![1, 0, -1], ![1, 0, -1]]

def raw256step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]

def raw257 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 2, -3], ![2, 0, -2]]

def raw257step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![2, 1, -3]]

def raw258 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 3, -4], ![2, -1, -1]]

def raw258step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![5, -4, -1]]

def raw258step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![2, -3, 1], ![-5, 4, 1]]

def raw258step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -3, 2], ![1, 4, -5]]

def raw259 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![2, -1, -1], ![1, 3, -4]]

def raw259step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, -1, 3], ![5, -1, -4]]

def raw259step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -2, -1], ![2, 1, -3], ![-5, 1, 4]]

def raw259step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -3, 2], ![1, 4, -5]]

def raw260 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![2, 0, -2], ![1, 2, -3]]

def raw260step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![2, 1, -3]]

def raw261 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, -1, 1, 3], ![-1, 2, 1, -2], ![4, -1, -2, -1]]

def raw261step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 1, -2], ![3, -2, -1]]

def raw261step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 4, -3], ![1, -2, 1], ![2, -1, -1]]

def raw262 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, -1, 1, 3], ![1, 2, -2, -1], ![2, -1, 1, -2]]

def raw262step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![3, -1, -2]]

def raw262step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![2, 1, -3]]

def raw263 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, -1, 2, 2], ![-1, 2, -2, 1], ![4, -1, 0, -3]]

def raw263step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![2, -2, 0], ![2, 1, -3]]

def raw263step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![1, -3, 2], ![2, -1, -1]]

def raw264 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, -1, 2, 2], ![-1, 2, 1, -2], ![4, -1, -3, 0]]

def raw264step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![2, 1, -3], ![2, -2, 0]]

def raw264step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![1, -3, 2], ![2, -1, -1]]

def raw265 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, -1, 2, 2], ![1, -1, 2, -2], ![2, 2, -4, 0]]

def raw265step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, 2, -4], ![2, -2, 0]]

def raw265step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-2, -2, 4], ![-2, 2, 0]]

def raw265step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![1, 1, -2], ![2, -2, 0]]

def raw266 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, -1, 2, 2], ![1, 2, -3, 0], ![2, -1, 1, -2]]

def raw266step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]

def raw266step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]

def raw267 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, -1, 3, 1], ![-1, 2, -2, 1], ![4, -1, -1, -2]]

def raw267step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![3, -2, -1], ![1, 1, -2]]

def raw267step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 4, -3], ![1, -2, 1], ![2, -1, -1]]

def raw268 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, -1, 3, 1], ![1, 2, -1, -2], ![2, -1, -2, 1]]

def raw268step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![3, -1, -2], ![1, -2, 1]]

def raw268step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![2, 1, -3]]

def raw269 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]

def raw270 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]

def raw271 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]

def raw272 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

def raw273 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]

def raw274 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]

def raw275 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

def raw275step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

def raw275step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3]]

def raw276 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 2, -2], ![3, -1, -2]]

def raw276step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 0, 3], ![-1, 0, 2, -1], ![4, 0, -2, -2]]

def raw276step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![4, -2, -2]]

def raw276step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, -1, -1]]

def raw277 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

def raw277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]

def raw277step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]

def raw277step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def raw278 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]

def raw278step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 1, 2], ![-1, 0, -1, 2], ![4, 0, 0, -4]]

def raw278step1 : Matrix (Fin 3) (Fin 4) ℤ := ![![3, 0, -1, -2], ![1, 0, 1, -2], ![-4, 0, 0, 4]]

def raw278step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-4, 0, 4]]

def raw278step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 4, -4], ![1, -2, 1]]

def raw279 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![1, 2, -3], ![2, -1, -1]]

def raw279step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, -2, 3], ![-2, 1, 1]]

def raw279step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, -2, 3], ![-2, 1, 1]]

def raw279step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -2, 1], ![1, 3, -4]]

def raw280 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]

def raw280step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

def raw280step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3]]

def raw281 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]

def raw282 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

def raw282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw283 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def raw283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw284 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]

def raw285 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]

def raw285step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1]]

def raw286 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]

def raw287 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2560 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 2, 0, -3]]

def raw2560step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, -1, 2], ![2, -2, 0, 0], ![1, 2, 0, -3]]

def raw2560step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 2, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw2561 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw2561step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 1, 0, -2]]

def raw2562 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![1, 1, 0, -2], ![1, 0, 0, -1]]

def raw2562step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 1, 0, -2]]

def raw2563 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![2, 0, 0, -2]]

def raw2563step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, 0, -2]]

def raw2564 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw2564step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw2565 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, -1, 0, -1]]

def raw2566 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw2566step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 1, 0, -2]]

def raw2567 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw2567step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![-1, 0, 0, 1, 0], ![2, -1, 0, 0, -1], ![1, 1, 0, -1, -1]]

def raw2567step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 1, 0], ![2, -1, 0, -1], ![1, 1, -1, -1]]

def raw2567step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1]]

def raw2568 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 0, 0, 0], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw2568step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 0, 0, 1], ![2, -1, 0, -1, 0], ![1, 1, 0, 0, -2]]

def raw2568step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, 0, 1], ![2, -1, -1, 0], ![1, 1, 0, -2]]

def raw2568step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 1, -2]]

def raw2569 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 0, 0, 0], ![2, 0, 0, -2]]

def raw2569step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![-1, 0, 1, 0, 0], ![2, -1, -1, 0, 0], ![1, 1, 0, 0, -2]]

def raw2569step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 1, 0], ![2, -1, -1, 0], ![1, 1, 0, -2]]

def raw2569step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw2570 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def raw2570step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw2571 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw2571step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw2572 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw2572step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw2573 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw2573step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 1, 0], ![2, -1, -1, 0], ![1, 1, 0, -2]]

def raw2573step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw2574 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 0, 0, 0], ![2, 0, -1, -1]]

def raw2574step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![-1, 0, 1, 0, 0], ![2, -1, 0, 0, -1], ![1, 1, -1, 0, -1]]

def raw2574step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 1, 0], ![2, -1, 0, -1], ![1, 1, -1, -1]]

def raw2574step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1]]

def raw2575 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw2575step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def raw2576 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def raw2577 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw2577step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw2578 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw2578step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 1, 0], ![2, -1, 0, -1], ![1, 1, -1, -1]]

def raw2578step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1]]

def raw2579 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw2579step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, -2, -1], ![0, 0, 1, -1], ![0, -2, 1, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw2579step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw2580 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, -1, 0, 0]]

def raw2580step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, -2, -1], ![0, 0, 1, -1], ![0, -2, 1, 1], ![-1, 0, 0, 1], ![-1, 1, 0, 0]]

def raw2580step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw2581 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![2, -1, 0, -1]]

def raw2581step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 2, -1], ![2, -1, -1, 0], ![1, 1, -1, -1]]

def raw2581step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw2582 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw2583 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw2583step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw2584 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, -1, 0, 0]]

def raw2584step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw2585 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, -1, -1, 0]]

def raw2585step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 2, -1], ![2, -1, 0, -1], ![1, 1, -2, 0]]

def raw2585step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw2586 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw2586step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, 0, 1], ![2, -1, -1, 0], ![1, 1, 0, -2]]

def raw2586step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 1, -2]]

def raw2587 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![1, 1, -1, -1], ![1, 0, 0, -1]]

def raw2587step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, 1, 0], ![2, -1, -1, 0], ![1, 1, -1, -1]]

def raw2587step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, 0, -1, 0], ![-2, 1, 1, 0], ![-1, -1, 1, 1]]

def raw2587step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw2588 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def raw2588step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 1, 0, 0], ![2, 0, 0, -2, 0], ![1, 0, -1, 1, -1]]

def raw2588step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![2, 0, -2, 0], ![1, -1, 1, -1]]

def raw2588step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw2589 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, -3, 2], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw2589step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![2, -3, 0, 1], ![1, 2, 0, -3]]

def raw2589step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 1, -1], ![-2, 3, 0, -1], ![-1, -2, 0, 3]]

def raw2589step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 3, -2, -1], ![1, -1, -1, 1]]

def raw2590 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, -2, 1], ![0, 0, 0, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw2590step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 1, 0, 0, 0], ![2, -2, 0, 0, 0], ![1, 1, 0, -1, -1]]

def raw2590step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, -1, -1], ![1, -1, 0, 0, 0], ![-2, 2, 0, 0, 0], ![-1, -1, 0, 1, 1]]

def raw2590step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 0, 0], ![-2, 2, 0, 0], ![-1, -1, 1, 1]]

def raw2590step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, -1, -1]]

def raw2591 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def raw2591step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![2, -2, -1, 1], ![1, 1, 0, -2]]

def raw2591step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 1, -1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2592 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw2592step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, -2, -1], ![0, -1, 2, -1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw2592step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw2593 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, -1, 0, 0]]

def raw2593step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, -2, -1], ![0, -1, 2, -1], ![0, -1, 0, 1], ![-1, 0, 0, 1], ![-1, 1, 0, 0]]

def raw2593step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw2594 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def raw2594step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![2, -2, 0, 0], ![1, 1, -1, -1]]

def raw2594step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw2595 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, -1, 0]]

def raw2595step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def raw2596 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, -2, 1], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def raw2596step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -3, 1]]

def raw2597 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw2597step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![2, -2, 0, 0], ![1, 1, 0, -2]]

def raw2597step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 1, -1], ![-2, 2, 0, 0], ![-1, -1, 0, 2]]

def raw2597step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw2598 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw2598step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![2, -2, 0, 0], ![1, 1, -1, -1]]

def raw2598step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 0, 0], ![-2, 2, 0, 0], ![-1, -1, 1, 1]]

def raw2598step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, -1, -1]]

def raw2599 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def raw2599step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -2, 1]]

def raw2600 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw2600step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, -2, -1], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw2600step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw2601 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def raw2601step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![2, -1, -1, 0], ![1, 0, 0, -1]]

def raw2601step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, -1, -1]]

def raw2602 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw2602step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw2603 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw2603step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, -2, -1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw2603step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw2604 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw2604step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![2, -1, 0, -1], ![1, 0, -1, 0]]

def raw2604step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![1, -1, -1, 1], ![-2, 1, 0, 1], ![-1, 0, 1, 0]]

def raw2604step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw2605 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw2605step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw2606 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -1, -2, 1]]

def raw2606step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![2, -1, 1, -2], ![1, 0, -2, 1]]

def raw2606step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![1, -1, -1, 1], ![-2, 1, -1, 2], ![-1, 0, 2, -1]]

def raw2606step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, -1, -1], ![1, -1, 2, -2]]

def raw2607 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, -1, 0], ![1, -1, -2, 2], ![1, 1, 1, -3]]

def raw2607step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![2, -1, -2, 1], ![1, 0, 2, -3]]

def raw2607step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, 1, -2], ![0, 2, -3, 1], ![1, -1, 1, -1]]

def raw2608 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def raw2608step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![2, -1, -1, 0], ![1, 0, 1, -2]]

def raw2608step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw2609 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw2609step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![2, -1, 0, -1], ![1, 0, 0, -1]]

def raw2609step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw2610 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, 0, -1], ![0, 0, 0, 0], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def raw2610step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 1, 0, 0, 0], ![2, 0, 0, -2, 0], ![1, -1, 0, 1, -1]]

def raw2610step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![2, 0, -2, 0], ![1, -1, 1, -1]]

def raw2610step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw2611 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw2611step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw2612 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2], ![1, 0, 0, -1]]

def raw2612step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -2, 1]]

def raw2613 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw2613step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw2614 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw2614step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, -2, -1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 2, -1]]

def raw2614step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def raw2615 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, -1, 0, 0]]

def raw2615step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, -2, -1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 0, 2, -1], ![-1, 1, 0, 0]]

def raw2615step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def raw2616 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -2, 1]]

def raw2616step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![2, 0, 0, -2], ![1, -1, -1, 1]]

def raw2616step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 1, -1, -1]]

def raw2617 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, 0, -1], ![1, -1, -2, 2], ![1, 1, 0, -2]]

def raw2617step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![2, 0, -2, 0], ![1, -1, 2, -2]]

def raw2617step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 1, -1, -1]]

def raw2618 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def raw2618step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![2, 0, -1, -1], ![1, -1, 1, -1]]

def raw2618step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw2619 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw2619step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![2, 0, 0, -2], ![1, -1, 0, 0]]

def raw2619step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 1, -1], ![-2, 0, 0, 2], ![-1, 1, 0, 0]]

def raw2619step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1]]

def raw2620 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -3, 1]]

def raw2620step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![2, 0, 1, -3], ![1, -1, -1, 1]]

def raw2620step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -3, 2], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw2621 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 1, -2, 0]]

def raw2621step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def raw2622 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -3, 1]]

def raw2622step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![2, 1, 0, -3], ![1, -2, 0, 1]]

def raw2622step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 1, -1], ![-2, -1, 0, 3], ![-1, 2, 0, -1]]

def raw2622step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw2623 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 2, -3, 1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw2623step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![2, -3, 0, 1], ![1, 1, 0, -2]]

def raw2623step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![-2, 3, 0, -1], ![-1, -1, 0, 2]]

def raw2623step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, 0, -2, 1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2624 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 2, -3, 1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw2624step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![2, -3, 1, 0], ![1, 1, -1, -1]]

def raw2624step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![-2, 3, -1, 0], ![-1, -1, 1, 1]]

def raw2624step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, 1, -1, -1]]

def raw2625 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 2, -3, 1], ![2, -1, 1, -2]]

def raw2625step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![2, -3, 1], ![1, 1, -2]]

def raw2625step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

def raw2626 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 2, -2, 0], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def raw2626step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![2, -2, -1, 1], ![1, 0, 1, -2]]

def raw2626step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def raw2627 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw2627step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![2, -2, 0, 0], ![1, 0, 0, -1]]

def raw2627step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![-2, 2, 0, 0], ![-1, 0, 0, 1]]

def raw2627step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw2628 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw2628step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![2, -1, -1, 0], ![1, -1, 1, -1]]

def raw2628step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![-2, 1, 1, 0], ![-1, 1, -1, 1]]

def raw2628step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw2629 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 2, 0, -2], ![1, -1, -2, 2], ![1, 0, 0, -1]]

def raw2629step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![2, 0, -2, 0], ![1, -2, 2, -1]]

def raw2629step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, -2, 1]]

def raw2630 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw2630step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![2, 0, -1, -1], ![1, -2, 1, 0]]

def raw2630step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def raw2631 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw2631step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![2, 0, 0, -2], ![1, -2, 0, 1]]

def raw2631step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![-2, 0, 0, 2], ![-1, 2, 0, -1]]

def raw2631step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw2632 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 2, 0, -2], ![2, -1, -2, 1]]

def raw2632step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![2, 0, -2], ![1, -2, 1]]

def raw2632step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]

def raw2633 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 2, 1, -3], ![1, -1, -2, 2], ![1, 0, -1, 0]]

def raw2633step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![2, 1, -2, -1], ![1, -3, 2, 0]]

def raw2633step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, -1, 2, -1], ![0, 2, -3, 1], ![1, 1, 0, -2]]

def raw2634 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 2, 1, -3], ![1, -1, -1, 1], ![1, 0, -2, 1]]

def raw2634step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![2, 1, -1, -2], ![1, -3, 1, 1]]

def raw2634step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 2, -1], ![1, 1, -3, 1], ![1, 1, 0, -2]]

def raw2635 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 2, 1, -3], ![1, -1, 0, 0], ![1, 0, -3, 2]]

def raw2635step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![2, 1, 0, -3], ![1, -3, 0, 2]]

def raw2635step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![-2, -1, 0, 3], ![-1, 3, 0, -2]]

def raw2635step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -2, 3, -1], ![0, 3, -1, -2], ![1, 0, -2, 1]]

def raw2636 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 2, 1, -3], ![2, -1, -3, 2]]

def raw2636step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![2, 1, -3], ![1, -3, 2]]

def raw2636step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]

def raw2637 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 3, -4, 1], ![2, -2, 2, -2]]

def raw2637step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![2, -4, 2], ![1, 1, -2]]

def raw2637step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -3, 2], ![-2, 4, -2], ![-1, -1, 2]]

def raw2637step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 2, -3], ![2, -2, 0]]

def raw2638 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 3, -1, -2], ![2, -2, -1, 1]]

def raw2638step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![2, -1, -1], ![1, -2, 1]]

def raw2638step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -3, 2], ![-2, 1, 1], ![-1, 2, -1]]

def raw2638step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

def raw2639 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 3, 0, -3], ![2, -2, -2, 2]]

def raw2639step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![2, 0, -2], ![1, -3, 2]]

def raw2639step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]

def raw2640 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 4, -1, -3], ![2, -3, -1, 2]]

def raw2640step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![2, -1, -1], ![1, -3, 2]]

def raw2640step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![1, -3, 2], ![2, -1, -1]]

def raw2641 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![1, -3, 1, 1], ![1, 4, -3, -2]]

def raw2641step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -3, 4], ![2, 1, -3], ![1, 1, -2]]

def raw2641step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]

def raw2642 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![1, -2, -1, 2], ![1, 3, -1, -3]]

def raw2642step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![2, -1, -1], ![1, 2, -3]]

def raw2642step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![2, 1, -3]]

def raw2643 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![1, -1, -3, 3], ![1, 2, 1, -4]]

def raw2643step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![2, -3, 1], ![1, 3, -4]]

def raw2643step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-2, 3, -1], ![-1, -3, 4]]

def raw2643step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 4, -3], ![1, -2, 1], ![2, -1, -1]]

def raw2644 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![1, -1, -2, 2], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw2644step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![-1, -1, 2, 0], ![2, -2, 0, 0], ![1, 2, -2, -1]]

def raw2644step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, -2, 1]]

def raw2645 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![1, -1, -2, 2], ![1, 2, 0, -3]]

def raw2645step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![2, -2, 0], ![1, 2, -3]]

def raw2645step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

def raw2646 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![1, -1, -1, 1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw2646step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![-1, -1, 2, 0], ![2, -1, -1, 0], ![1, 1, -1, -1]]

def raw2646step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![1, 1, -2, 0], ![-2, 1, 1, 0], ![-1, -1, 1, 1]]

def raw2646step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw2647 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![1, -1, 2, -2], ![1, 2, -4, 1]]

def raw2647step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![2, 2, -4], ![1, -2, 1]]

def raw2647step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-2, -2, 4], ![-1, 2, -1]]

def raw2647step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]

def raw2648 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![1, 2, -3, 0], ![1, -1, 1, -1]]

def raw2648step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![2, -3, 1], ![1, 0, -1]]

def raw2648step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![1, -2, 1], ![-2, 3, -1], ![-1, 0, 1]]

def raw2648step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

def raw2649 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![2, -3, 0, 1], ![0, 4, -2, -2]]

def raw2649step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -3, 4], ![2, 0, -2], ![1, 1, -2]]

def raw2649step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

def raw2650 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]

def raw2650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, -2, 4]]

def raw2650step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]

def raw2651 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]

def raw2651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

def raw2653 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]

def raw2654 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]

def raw2655 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]

def raw2655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]

def raw2655step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![1, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2656 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

def raw2657 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![3, 0, -3]]

def raw2657step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-3, 0, 3]]

def raw2657step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 1, -2], ![1, 2, -3]]

def raw2659 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 1, -2], ![2, 1, -3]]

def raw2659step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![1, 1, -2], ![1, 2, -3]]

def raw2660 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 2, -3], ![2, 0, -2]]

def raw2660step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![-1, -2, 3], ![-2, 0, 2]]

def raw2660step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 1, -2], ![1, 2, -3]]

def raw2661 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 3, -4], ![2, -1, -1]]

def raw2661step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![-1, -3, 4], ![-2, 1, 1]]

def raw2661step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]

def raw2662 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

def raw2662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]

def raw2662step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw2663 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

def raw2663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]

def raw2663step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw2664 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

def raw2664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]

def raw2664step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

def raw2665 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

def raw2665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]

def raw2665step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw2666 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 2, -3], ![2, -1, -1]]

def raw2666step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, -2, 3], ![-2, 1, 1]]

def raw2666step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

def raw2667 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

def raw2667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw2668 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def raw2668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw2669 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]

def raw2670 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

def raw2670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]

def raw2670step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

def raw2671 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

def raw2671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]

def raw2672 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]

def raw2672step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

def raw2673 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]

def raw2673step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]

def raw2674 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]

def raw2674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![-1, 0, 1], ![-2, -1, 3]]

def raw2674step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]

def raw2675 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]

def raw2676 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]

def raw2676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]

def raw2676step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]

def raw2677 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]

def raw2678 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]

def raw2678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2]]

def raw2678step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-2, 0, 2]]

def raw2678step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

def raw2679 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]

def raw2679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1]]

def raw2679step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]

def raw2679step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

def raw2680 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]

def raw2681 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

def raw2681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]

def raw2681step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]

def raw2682 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]

def raw2682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]

def raw2682step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

def raw2683 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

def raw2684 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]

def raw2685 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

def raw2686 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]

def raw2686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

def raw2687 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![2, 1, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2688 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![1, 2, -3]]

def raw2688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]

def raw2689 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

def raw2689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]

def raw2689step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]

def raw2690 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def raw2690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]

def raw2690step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]

def raw2691 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]

def raw2691step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-2, 0, 2]]

def raw2691step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

def raw2692 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]

def raw2692step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]

def raw2692step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

def raw2693 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]

def raw2693step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, -1, 2], ![-2, 2, 0]]

def raw2693step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

def raw2694 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 2, -3], ![2, -3, 1]]

def raw2695 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![2, -3, 1], ![1, 2, -3]]

def raw2695step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 2, -3], ![2, -3, 1]]

def raw2696 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![2, -2, 0], ![1, 1, -2]]

def raw2696step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-2, 2, 0], ![-1, -1, 2]]

def raw2696step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

def raw2697 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]

def raw2697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -3, 2], ![0, 2, -2], ![-1, 0, 1], ![-2, 0, 2]]

def raw2697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]

def raw2698 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]

def raw2698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -3, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]

def raw2698step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]

def raw2699 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![1, -2, 1], ![2, 0, -2]]

def raw2699step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -3, 2], ![-1, 2, -1], ![-2, 0, 2]]

def raw2699step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]

def raw2700 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw2700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]

def raw2700step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

def raw2701 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]

def raw2701step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -3, 2], ![-1, 1, 0], ![-2, 1, 1]]

def raw2701step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

def raw2702 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![1, 1, -2], ![2, -3, 1]]

def raw2702step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -3, 2], ![-1, -1, 2], ![-2, 3, -1]]

def raw2702step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 2, -3], ![2, -3, 1]]

def raw2703 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 4, -3], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

def raw2704 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 4, -3], ![1, -2, 1], ![2, -1, -1]]

def raw2705 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 4, -3], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1]]

def raw2705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 4, -3], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

def raw2706 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]

def raw2706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]

def raw2707 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 4, -3], ![2, -3, 1], ![1, 0, -1]]

def raw2707step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -4, 3], ![-2, 3, -1], ![-1, 0, 1]]

def raw2707step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 3, -4], ![2, -3, 1]]

def raw2708 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![-1, 3, -2], ![1, 0, -1], ![2, 0, -2]]

def raw2708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![1, -3, 2], ![-1, 0, 1], ![-2, 0, 2]]

def raw2708step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]

def raw2709 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]

def raw2710 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

def raw2711 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 3, -4]]

def raw2712 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

def raw2713 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

def raw2714 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![2, 2, -4]]

def raw2714step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -1, 1], ![-2, -2, 4]]

def raw2714step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 2, -2], ![2, 1, -3]]

def raw2715 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![0, 1, -1], ![2, 0, -2]]

def raw2715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

def raw2716 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 2, -3]]

def raw2717 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def raw2718 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![2, 1, -3]]

def raw2719 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2720 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def raw2721 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![2, 0, -2]]

def raw2722 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 4, -4], ![1, -1, 0], ![1, 0, -1]]

def raw2723 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 4, -4], ![2, -1, -1]]

def raw2724 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, -1, 0], ![1, 4, -5]]

def raw2725 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 3, -4]]

def raw2726 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 1, -2], ![1, 2, -3]]

def raw2727 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 2, -3], ![1, 1, -2]]

def raw2727step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 1, -2], ![1, 2, -3]]

def raw2728 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 3, -4], ![1, 0, -1]]

def raw2728step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 3, -4]]

def raw2729 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![2, 3, -5]]

def raw2729step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![-2, -3, 5]]

def raw2729step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![2, 1, -3]]

def raw2730 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]

def raw2730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]

def raw2731 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, 1, -3]]

def raw2731step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -2, 1], ![-1, 1, 0], ![-2, -1, 3]]

def raw2731step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]

def raw2732 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]

def raw2732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]

def raw2733 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0], ![2, 0, -2]]

def raw2733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -3, 2], ![-1, 1, 0], ![-2, 0, 2]]

def raw2733step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

def raw2734 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![-1, 3, -2], ![1, 0, -1], ![2, -1, -1]]

def raw2734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -3, 2], ![-1, 0, 1], ![-2, 1, 1]]

def raw2734step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]

def raw2736 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 4, -5]]

def raw2737 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 3, -4]]

def raw2738 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, 1, -3]]

def raw2738step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![2, 1, -3]]

def raw2739 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, 0, -2]]

def raw2739step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

def raw2740 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 3, -4]]

def raw2740step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def raw2741 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 2, -3]]

def raw2741step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]

def raw2742 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, 1, -3]]

def raw2742step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![2, 1, -3]]

def raw2744 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw2745 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def raw2746 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 3, -4]]

def raw2747 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw2748 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw2749 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![1, -1, 0]]

def raw2749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw2750 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![2, 1, -3]]

def raw2751 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![0, 0, 0], ![2, 0, -2]]

def raw2751step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical86
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2752 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![0, 1, -1], ![2, -1, -1]]

def raw2752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def raw2753 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def raw2754 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw2755 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0]]

def raw2755step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def raw2756 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

def raw2757 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw2758 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0]]

def raw2758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw2759 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![2, -1, -1]]

def raw2760 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 4, -4], ![1, -2, 1], ![1, 0, -1]]

def raw2761 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

def raw2762 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, -2, 1], ![1, 4, -5]]

def raw2763 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 2, -3]]

def raw2763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw2764 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![0, 3, -3]]

def raw2764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw2765 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def raw2766 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]

def raw2767 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]

def raw2768 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1]]

def raw2768step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]

def raw2769 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw2769step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw2770 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def raw2770step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def raw2771 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

def raw2771step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

def raw2772 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw2772step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw2773 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw2773step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw2773step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw2774 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2]]

def raw2774step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![2, 0, -2]]

def raw2774step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![1, 0, -1]]

def raw2775 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw2775step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw2776 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]

def raw2776step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]

def raw2777 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw2777step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw2778 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw2778step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw2780 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![1, -2, 1], ![1, 3, -4]]

def raw2780step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -2, 1], ![1, 3, -4]]

def raw2781 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3]]

def raw2781step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, -1, 2], ![3, 0, 0, -3]]

def raw2781step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![3, 0, -3]]

def raw2781step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -2, 1]]

def raw2782 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2]]

def raw2782step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, 0, -1], ![1, 1, -2]]

def raw2782step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![1, 1, -2]]

def raw2783 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![2, 1, -3]]

def raw2783step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![3, 0, -3]]

def raw2783step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]

def raw2783step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical87
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2784 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]

def raw2784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]

def raw2785 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]

def raw2785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0]]

def raw2785step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

def raw2786 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]

def raw2786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

def raw2787 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]

def raw2787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw2788 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, -1, 1], ![2, 1, -3]]

def raw2788step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![2, 1, -3]]

def raw2789 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]

def raw2789step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw2790 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]

def raw2790step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def raw2791 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, 2, -3]]

def raw2791step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

def raw2792 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]

def raw2792step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw2793 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]

def raw2793step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw2793step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw2794 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2]]

def raw2794step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![2, 0, -2]]

def raw2794step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![1, 0, -1]]

def raw2795 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]

def raw2795step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw2796 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

def raw2797 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]

def raw2798 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 2, -3]]

def raw2799 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw2800 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw2801 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]

def raw2801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw2802 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]

def raw2802step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw2803 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw2804 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![0, -2, 2], ![2, 0, -2]]

def raw2804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

def raw2805 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0]]

def raw2805step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def raw2806 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![0, 1, -1], ![2, -3, 1]]

def raw2806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]

def raw2807 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

def raw2808 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

def raw2809 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

def raw2810 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]

def raw2810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

def raw2811 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def raw2812 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

def raw2813 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

def raw2814 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![1, -2, 1]]

def raw2814step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

def raw2815 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 3, -3], ![2, -3, 1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical88
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2816 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -3, 2], ![1, 3, -4]]

def raw2817 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

def raw2818 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, 2, -3]]

def raw2818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw2819 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]

def raw2819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

def raw2820 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw2821 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw2821step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw2822 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, 2, -3], ![1, -2, 1]]

def raw2822step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

def raw2823 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![2, 0, -2]]

def raw2823step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![1, 0, -1]]

def raw2824 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]

def raw2824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def raw2825 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, -2, 2], ![2, 1, -3]]

def raw2825step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![2, 1, -3]]

def raw2826 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]

def raw2826step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def raw2827 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

def raw2827step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw2828 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, -1, 1], ![2, 0, -2]]

def raw2828step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

def raw2829 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]

def raw2829step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]

def raw2830 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2]]

def raw2830step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

def raw2831 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

def raw2831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

def raw2832 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]

def raw2832step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

def raw2833 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]

def raw2833step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def raw2834 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 2, -2], ![2, -3, 1]]

def raw2835 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -3, 2], ![1, 2, -3]]

def raw2836 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]

def raw2836step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def raw2837 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1]]

def raw2837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

def raw2838 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1]]

def raw2838step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

def raw2839 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def raw2840 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2]]

def raw2840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def raw2841 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]

def raw2841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

def raw2842 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw2843 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]

def raw2843step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw2844 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, 1, -2], ![1, -2, 1]]

def raw2844step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def raw2845 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]

def raw2846 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -3, 2], ![1, 1, -2]]

def raw2847 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical89
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2848 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw2849 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![2, -2, 0]]

def raw2850 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 4, -4], ![1, -3, 2], ![1, 0, -1]]

def raw2851 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 4, -4], ![1, -2, 1], ![1, -1, 0]]

def raw2852 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 4, -4], ![1, -1, 0], ![1, -2, 1]]

def raw2852step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 4, -4], ![1, -2, 1], ![1, -1, 0]]

def raw2853 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 4, -4], ![2, -3, 1]]

def raw2854 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -3, 2], ![0, 2, -2], ![1, 2, -3]]

def raw2854step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -3, 2], ![1, 2, -3]]

def raw2855 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -3, 2], ![0, 3, -3], ![1, 1, -2]]

def raw2855step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -3, 2], ![1, 1, -2]]

def raw2856 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -3, 2], ![0, 4, -4], ![1, 0, -1]]

def raw2856step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 4, -4], ![1, -3, 2], ![1, 0, -1]]

def raw2857 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -3, 2], ![1, 4, -5]]

def raw2858 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -2, 1], ![0, 2, -2], ![1, 1, -2]]

def raw2858step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def raw2859 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -2, 1], ![0, 3, -3], ![1, 0, -1]]

def raw2859step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw2860 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -2, 1], ![1, 3, -4]]

def raw2861 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -1, 0], ![1, 2, -3]]

def raw2861step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![3, 0, -3]]

def raw2861step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -2, 1]]

def raw2862 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, 0, -1], ![1, 1, -2]]

def raw2862step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![1, 1, -2]]

def raw2863 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, 1, -2], ![1, 0, -1]]

def raw2863step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![1, 1, -2]]

def raw2864 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, 2, -3], ![1, -1, 0]]

def raw2864step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![3, -3, 0]]

def raw2864step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -2, 1]]

def raw2865 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, 3, -4], ![1, -2, 1]]

def raw2865step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -2, 1], ![1, 3, -4]]

def raw2866 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, 4, -5], ![1, -3, 2]]

def raw2866step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -3, 2], ![1, 4, -5]]

def raw2867 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 3, 0], ![-2, 2, -2, 2], ![4, -1, -1, -2]]

def raw2867step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![3, -2, -1], ![0, 2, -2]]

def raw2867step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-3, 2, 1], ![0, -2, 2]]

def raw2867step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -4, 2]]

def raw2868 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 3, 0], ![-1, 2, -2, 1], ![3, -1, -1, -1]]

def raw2868step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![3, -2, -1], ![0, 1, -1]]

def raw2868step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-3, 2, 1], ![0, -1, 1]]

def raw2868step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

def raw2869 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 3, 0], ![0, 2, -1, -1], ![2, -1, -2, 1]]

def raw2869step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![3, -1, -2], ![0, -1, 1]]

def raw2869step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-3, 1, 2], ![0, 1, -1]]

def raw2869step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

def raw2870 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 3, 0], ![0, 3, -2, -1], ![2, -2, -1, 1]]

def raw2870step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![3, -2, -1], ![0, -1, 1]]

def raw2870step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -3, 2], ![-3, 2, 1], ![0, 1, -1]]

def raw2870step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]

def raw2871 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 3, 0], ![1, 2, -1, -2], ![1, -1, -2, 2]]

def raw2871step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![3, -1, -2], ![0, -2, 2]]

def raw2871step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![1, -2, 1], ![-3, 1, 2], ![0, 2, -2]]

def raw2871step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

def raw2872 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 3, 0], ![2, -2, 1, -1], ![0, 3, -4, 1]]

def raw2872step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![3, 1, -4], ![0, -1, 1]]

def raw2872step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -2, 0], ![1, 2, -3], ![-3, -1, 4], ![0, 1, -1]]

def raw2872step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]

def raw2873 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def raw2874 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw2875 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 0, 1, -1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def raw2876 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def raw2877 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw2878 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw2879 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 1, 1, -2], ![2, 1, -1, -2]]

def raw2879step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 2, -2, 0], ![0, -1, -1, 2], ![-2, -1, 1, 2]]

def raw2879step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 2, -2, 0], ![2, 0, 2, -4]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw288 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

def raw289 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]

def raw290 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]

def raw291 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]

def raw292 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]

def raw293 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

def raw294 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw295 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

def raw295step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3]]

def raw296 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]

def raw296step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw297 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]

def raw297step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2]]

def raw298 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]

def raw299 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]

def raw299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]

def raw300 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

def raw300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]

def raw301 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]

def raw301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

def raw302 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![3, -2, -1]]

def raw302step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]

def raw303 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

def raw304 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]

def raw305 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

def raw306 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def raw306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]

def raw306step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def raw307 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

def raw307step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]

def raw307step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

def raw308 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]

def raw308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 0, 1], ![-1, 1, 0], ![-1, 0, 1]]

def raw308step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def raw309 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

def raw309step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]

def raw309step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -2, 1], ![1, 3, -4]]

def raw310 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

def raw311 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![2, -2, 0], ![1, 1, -2]]

def raw311step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

def raw312 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![3, -1, -2]]

def raw312step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![4, -2, -2]]

def raw312step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, -1, -1]]

def raw313 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]

def raw314 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]

def raw315 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw316 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]

def raw316step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw317 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]

def raw318 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]

def raw319 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![2, -2, 0], ![1, 0, -1]]

def raw319step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical90
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2880 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw2881 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 2, -1, -1], ![2, 0, 1, -3]]

def raw2882 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw2883 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 2, 0, -2], ![2, 0, 0, -2]]

def raw2883step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![2, 0, 0, -2]]

def raw2884 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 2, 1, -3], ![2, 0, -1, -1]]

def raw2885 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![1, 0, 1, -2], ![1, 2, -1, -2]]

def raw2885step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 2, -2, 0], ![-1, 0, -1, 2], ![-1, -2, 1, 2]]

def raw2885step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 2, 2, -4], ![2, 0, -2, 0]]

def raw2886 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def raw2887 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![1, 1, 0, -2], ![1, 1, 0, -2]]

def raw2887step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![-2, 2, 0, 0], ![4, 0, -2, -2]]

def raw2887step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def raw2888 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![1, 1, 1, -3], ![1, 1, -1, -1]]

def raw2888step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def raw2889 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![1, 2, -1, -2], ![1, 0, 1, -2]]

def raw2889step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 2, -2, 0], ![-1, -2, 1, 2], ![-1, 0, -1, 2]]

def raw2889step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 2, 2, -4], ![2, 0, -2, 0]]

def raw2890 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 3, -1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def raw2890step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![-2, 3, -1, 0], ![4, -1, -1, -2]]

def raw2890step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 3, -2], ![0, 2, -2, 0], ![2, 0, 0, -2]]

def raw2891 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 3, -1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw2891step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![-2, 3, 0, -1], ![4, -1, -2, -1]]

def raw2891step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 3, -2], ![0, 2, 0, -2], ![2, 0, -2, 0]]

def raw2892 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 3, -1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def raw2892step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![-2, 3, -1, 0], ![4, -1, -1, -2]]

def raw2892step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 3, -2], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def raw2893 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def raw2894 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw2895 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def raw2896 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 0, 0], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def raw2896step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 1, -1, 0], ![0, 0, 0, 0], ![0, -1, -1, 2], ![-2, 0, 0, 2]]

def raw2896step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 1, -1, 0], ![0, -1, -1, 2], ![-2, 0, 0, 2]]

def raw2896step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -1, 0, 0]]

def raw2897 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw2897step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 1, -1, 0], ![0, 0, -1, 1], ![0, -1, 0, 1], ![-2, 0, 0, 2]]

def raw2897step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw2898 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw2898step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 1, -1, 0], ![0, 0, -1, 1], ![0, -1, -1, 2], ![-2, 0, 1, 1]]

def raw2898step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw2899 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -1, 1, -2]]

def raw2900 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, -1, 0, -1]]

def raw2900step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw2901 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw2901step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 1, -1, 0], ![0, 0, -1, 1], ![-1, 0, 0, 1], ![-1, -1, 0, 2]]

def raw2901step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw2902 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw2902step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 1, -1, 0], ![0, 0, -1, 1], ![-1, 0, -1, 2], ![-1, -1, 1, 1]]

def raw2902step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw2903 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 1, -1, -1], ![1, 0, 1, -2]]

def raw2903step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 1, -1, 0], ![0, 0, -1, 1], ![-1, -1, 1, 1], ![-1, 0, -1, 2]]

def raw2903step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw2904 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 0, 2, -2], ![2, 0, 0, -2]]

def raw2904step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, -2, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw2905 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -1, 1, -2]]

def raw2906 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 0, 2, -2], ![2, 0, -1, -1]]

def raw2906step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 1, -1, 0], ![0, -1, 0, 1], ![0, 0, -2, 2], ![-2, 0, 1, 1]]

def raw2906step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw2907 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def raw2907step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw2908 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 1, -1, -1]]

def raw2909 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw2909step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 1, -1, 0], ![0, -1, 0, 1], ![-1, 0, 0, 1], ![-1, 0, -1, 2]]

def raw2909step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, -1, 2], ![0, -1, 0, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw2910 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 0, 0, -1]]

def raw2910step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 1, -1, 0], ![0, -1, 0, 1], ![-1, 0, -1, 2], ![-1, 0, 0, 1]]

def raw2910step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, -1, 2], ![0, -1, 0, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw2911 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw2911step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 1, -1, 0], ![0, -1, -1, 2], ![-1, 0, 1, 0], ![-1, 0, -1, 2]]

def raw2911step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, -1, 1, 0], ![0, 2, 2, -4], ![1, 0, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical91
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2912 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def raw2912step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 1, -1, 0], ![0, -1, -1, 2], ![-2, 0, 0, 2]]

def raw2912step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -1, 0, 0]]

def raw2913 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw2914 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, -1, 2, -2]]

def raw2914step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def raw2915 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw2915step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw2916 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, -1, 2, -2]]

def raw2916step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 2, 0, -2], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw2917 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -1, 0, -1]]

def raw2918 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def raw2919 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw2920 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw2920step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![-2, 2, 0, 0], ![4, -1, -1, -2]]

def raw2920step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw2921 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw2922 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw2922step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 1, -2, 1], ![0, -1, -1, 2], ![-2, 0, 1, 1]]

def raw2922step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw2923 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw2924 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw2925 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, -1, 1, -2]]

def raw2926 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw2927 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, -1, 0, -1]]

def raw2927step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw2928 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![1, -1, 1, -1], ![1, 2, -1, -2]]

def raw2928step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![-2, 2, 1, -1], ![4, -1, -1, -2]]

def raw2928step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 1, -2], ![2, -2, -1, 1], ![-4, 1, 1, 2]]

def raw2928step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 1, -2, 0], ![1, 1, 2, -4]]

def raw2929 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw2929step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![-2, 2, 0, 0], ![4, -1, -1, -2]]

def raw2929step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

def raw2930 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw2930step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 1, -2, 1], ![-1, 0, -1, 2], ![-1, -1, 1, 1]]

def raw2930step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw2931 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 0, 1, -2]]

def raw2931step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 1, -2, 1], ![-1, -1, 1, 1], ![-1, 0, -1, 2]]

def raw2931step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw2932 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![1, 2, -1, -2], ![1, -1, 1, -1]]

def raw2932step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 2, -1], ![-2, 2, -1, 1], ![4, -1, -2, -1]]

def raw2932step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, -2, 1], ![2, -2, 1, -1], ![-4, 1, 2, 1]]

def raw2932step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 1, -2, 0], ![1, 1, 2, -4]]

def raw2933 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw2934 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw2934step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 1, -3, 2], ![0, -1, 0, 1], ![-1, 0, 1, 0], ![-1, 0, 0, 1]]

def raw2934step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 2, 2, -4], ![1, 0, -3, 2]]

def raw2935 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw2936 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 3, -2], ![0, 2, -1, -1], ![2, -1, 0, -1]]

def raw2937 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 3, -2], ![1, -1, 0, 0], ![1, 2, -1, -2]]

def raw2937step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![-2, 3, 0, -1], ![4, -2, 0, -2]]

def raw2937step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 1, -2], ![2, -3, 0, 1], ![-4, 2, 0, 2]]

def raw2937step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -3, 2], ![0, 2, 2, -4], ![1, -2, 1, 0]]

def raw2938 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 3, -2], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw2938step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![-2, 3, 0, -1], ![4, -2, -1, -1]]

def raw2938step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

def raw2939 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 3, -2], ![1, 1, -1, -1], ![1, 0, 0, -1]]

def raw2939step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 1, 0], ![-2, 3, -1, 0], ![4, -2, -1, -1]]

def raw2939step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

def raw2940 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 0, 0], ![0, 1, 1, -2], ![2, -1, 1, -2]]

def raw2940step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![-2, 0, 1, 1], ![4, 0, -2, -2]]

def raw2940step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-2, 1, 1], ![4, -2, -2]]

def raw2940step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def raw2941 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, -1, 0, -1]]

def raw2941step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -1, 0, -1]]

def raw2942 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def raw2942step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![0, 0, 0, 1, -1], ![-2, 1, 0, 1, 0], ![4, -1, 0, -2, -1]]

def raw2942step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![-2, 1, 1, 0], ![4, -1, -2, -1]]

def raw2942step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

def raw2943 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def raw2943step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -1, 0, 1], ![-2, 1, 0, 1]]

def raw2943step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical92
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2944 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -2, 1, -1]]

def raw2945 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, -2, 0, 0]]

def raw2945step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw2946 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw2946step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 1, -1, 1], ![-1, -1, 1, 1]]

def raw2946step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, -1, 1]]

def raw2947 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, -2, 0, 0]]

def raw2948 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw2948step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 0, -1, 1], ![0, 0, -2, 2], ![-1, 1, 0, 0], ![-1, -1, 1, 1]]

def raw2948step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, 0, 0]]

def raw2949 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 0, 2, -2], ![2, -1, 0, -1]]

def raw2949step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 0, -1, 1], ![0, -1, 1, 0], ![0, 0, -2, 2], ![-2, 1, 0, 1]]

def raw2949step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -2, 0, 1]]

def raw2950 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw2951 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -2, 1, -1]]

def raw2952 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, -2, 0, 0]]

def raw2953 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def raw2953step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def raw2954 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, -2, 0, 0]]

def raw2954step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

def raw2955 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 1, -1, -1]]

def raw2956 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw2956step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 0, -1, 1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, -1, 2]]

def raw2956step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, -1, 2], ![0, -1, 0, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw2957 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw2957step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 0, -1, 1], ![0, -1, 0, 1], ![-1, 1, -1, 1], ![-1, 0, 0, 1]]

def raw2957step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, -1, 1]]

def raw2958 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw2958step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 0, -1, 1], ![0, -1, 0, 1], ![-1, 1, -2, 2], ![-1, 0, 1, 0]]

def raw2958step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, -2, 2]]

def raw2959 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -1, 1, -2]]

def raw2959step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![-2, 1, 0, 1], ![4, -1, -1, -2]]

def raw2959step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw2960 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 1, -1, -1]]

def raw2961 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw2961step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 0, -1, 1], ![0, -1, -1, 2], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw2961step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw2962 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw2962step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 0, -1, 1], ![0, -1, -1, 2], ![-1, 1, -1, 1], ![-1, 0, 1, 0]]

def raw2962step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, -1, 1]]

def raw2963 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def raw2963step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![-2, 1, 1, 0], ![4, -1, -2, -1]]

def raw2963step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

def raw2964 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -2, 1, 0], ![1, 0, 1, -2]]

def raw2965 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw2966 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw2967 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def raw2968 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -2, 2, -2]]

def raw2968step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![-2, 1, -1, 2], ![4, -1, -1, -2]]

def raw2968step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 2, -2]]

def raw2969 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def raw2970 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw2970step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw2971 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, -1, 0, 0]]

def raw2971step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw2972 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, -2, 1, -1]]

def raw2972step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![-2, 1, 0, 1], ![4, -1, -2, -1]]

def raw2972step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def raw2973 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![1, -1, 2, -2], ![1, 1, -1, -1]]

def raw2973step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![-2, 1, 2, -1], ![4, -1, -2, -1]]

def raw2973step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 2, -2]]

def raw2974 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 2, -2], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -2, 0, 0]]

def raw2974step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, -2, 0, 0]]

def raw2975 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical93
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2976 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -2, 0, 0]]

def raw2977 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def raw2977step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 0, -2, 2], ![0, -1, 1, 0], ![-2, 1, -1, 2]]

def raw2977step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -2, -1, 2]]

def raw2978 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw2978step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 0, -2, 2], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw2978step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw2979 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def raw2979step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![-2, 2, 0, 0], ![4, -2, -1, -1]]

def raw2979step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw2980 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![2, -1, -1, 0]]

def raw2980step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 0, -2, 2], ![0, -1, -1, 2], ![-2, 1, 1, 0]]

def raw2980step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -2, 1, 0]]

def raw2981 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw2982 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, -1, 0, 0]]

def raw2982step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw2983 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, -2, 1, -1]]

def raw2983step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![-2, 2, -1, 1], ![4, -2, -1, -1]]

def raw2983step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![2, -1, 1, -2]]

def raw2984 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw2984step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw2985 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![2, -2, 0, 0]]

def raw2985step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![2, 0, 0, -2]]

def raw2986 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 2, -2], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw2986step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 0, -2, 2], ![-1, 1, -1, 1], ![-1, -1, 1, 1]]

def raw2986step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -1, -1, 1]]

def raw2987 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 2, -2], ![1, 1, -1, -1], ![1, -1, 1, -1]]

def raw2987step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 0, -2, 2], ![-1, -1, 1, 1], ![-1, 1, -1, 1]]

def raw2987step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -1, -1, 1]]

def raw2988 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 3, -3], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw2989 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 3, -3], ![0, 2, -1, -1], ![2, -2, 0, 0]]

def raw2990 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 3, -3], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw2990step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![-2, 3, 0, -1], ![4, -3, 0, -1]]

def raw2990step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 1, -1], ![2, -3, 0, 1], ![-4, 3, 0, 1]]

def raw2990step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -3, 2], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw2991 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 3, -3], ![1, 1, -1, -1], ![1, -1, 0, 0]]

def raw2991step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 1, -1], ![-2, 3, -1, 0], ![4, -3, -1, 0]]

def raw2991step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, -1, 1], ![2, -3, 1, 0], ![-4, 3, 1, 0]]

def raw2991step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -3, 2], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw2992 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, -1, 0], ![0, 0, 2, -2], ![2, -1, 1, -2]]

def raw2992step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, -1, 1, 0], ![0, 0, -2, 2], ![-2, 1, -1, 2]]

def raw2992step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -2, -1, 2]]

def raw2993 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw2994 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw2995 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def raw2996 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 3, -3]]

def raw2996step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![-2, -1, 0, 3], ![4, 0, -1, -3]]

def raw2996step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![2, 1, 0, -3], ![-4, 0, 1, 3]]

def raw2996step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -4, 3], ![1, 0, 2, -3]]

def raw2997 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw2998 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -2, 2, -2]]

def raw2998step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![-2, -1, 1, 2], ![4, 0, -2, -2]]

def raw2998step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![2, 1, -1, -2], ![-4, 0, 2, 2]]

def raw2998step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -4, 2], ![1, -1, 2, -2]]

def raw2999 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw3000 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, -1, 0, 0]]

def raw3000step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw3001 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, -2, 1, -1]]

def raw3001step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![-2, -1, 2, 1], ![4, 0, -3, -1]]

def raw3001step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![2, 1, -2, -1], ![-4, 0, 3, 1]]

def raw3001step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 0, -2, 2], ![0, 3, 1, -4], ![1, -2, -1, 2]]

def raw3002 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw3003 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, -1, 0], ![0, 1, 3, -4], ![2, -2, 0, 0]]

def raw3003step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![-2, -1, 3, 0], ![4, 0, -4, 0]]

def raw3003step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 4, -4], ![0, 2, -2, 0], ![1, -2, 0, 1]]

def raw3004 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def raw3004step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![-2, -1, 1, 2], ![4, 0, 0, -4]]

def raw3004step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 0, 4, -4], ![0, 1, -2, 1], ![1, -2, 0, 1]]

def raw3005 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw3005step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![-2, -1, 0, 3], ![4, 0, 0, -4]]

def raw3005step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 4, -4], ![0, 1, -2, 1], ![1, -1, 0, 0]]

def raw3006 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 2, -3]]

def raw3006step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, -1, 1, 0], ![-1, 1, -1, 1], ![-1, 0, -2, 3]]

def raw3006step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -2, 3], ![0, 2, 2, -4], ![1, -1, -1, 1]]

def raw3007 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw3007step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, -1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical94
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3008 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw3008step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![-2, 0, 0, 2], ![4, -1, -1, -2]]

def raw3008step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 0, 2, -2], ![1, 1, -2, 0]]

def raw3009 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, -2, 1, -1]]

def raw3009step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![-2, 0, 1, 1], ![4, -1, -2, -1]]

def raw3009step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw3010 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw3010step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 1, -3]]

def raw3011 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 0, -1], ![0, 1, 2, -3], ![2, -2, 0, 0]]

def raw3011step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![-2, 0, 2, 0], ![4, -1, -3, 0]]

def raw3011step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -2, 1, 0]]

def raw3012 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 1, 0, -2]]

def raw3012step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![-2, 0, 2, 0], ![4, -1, -1, -2]]

def raw3012step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw3013 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 1, -1, -1]]

def raw3013step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![-2, 0, 3, -1], ![4, -1, -2, -1]]

def raw3013step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 3, -2], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw3014 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw3014step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![-2, 0, 0, 2], ![4, -1, 0, -3]]

def raw3014step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw3015 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw3015step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![-2, 0, 1, 1], ![4, -1, -1, -2]]

def raw3015step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw3016 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def raw3016step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![-2, 0, 2, 0], ![4, -1, -2, -1]]

def raw3016step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw3017 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, -1, 3, -3]]

def raw3017step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 0, -1], ![-2, 0, -1, 3], ![4, -1, 0, -3]]

def raw3017step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 3, -2], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw3018 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, -1, 2, -2]]

def raw3018step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 0, -1], ![-2, 0, 0, 2], ![4, -1, -1, -2]]

def raw3018step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw3019 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 1, -2], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def raw3019step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![-2, 1, 0, 1], ![4, -2, -1, -1]]

def raw3019step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw3020 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw3020step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2], ![1, 0, 1, -2]]

def raw3021 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![2, -2, 0, 0]]

def raw3021step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![-2, 1, 1, 0], ![4, -2, -2, 0]]

def raw3021step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def raw3022 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 1, 0, -2]]

def raw3022step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 1, -2], ![1, 0, 1, -2], ![1, 1, -2, 0]]

def raw3023 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 1, -1, -1]]

def raw3023step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![-2, 1, 2, -1], ![4, -2, -1, -1]]

def raw3023step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 1, -2], ![1, -1, 2, -2], ![1, 1, -2, 0]]

def raw3024 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw3024step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, -1, -1, 2], ![-1, 1, 0, 0], ![-1, 0, -1, 2]]

def raw3024step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw3025 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 1, -2], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw3025step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, -1, -1, 2], ![-1, 1, -2, 2], ![-1, 0, 1, 0]]

def raw3025step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 2, 2, -4], ![1, -1, -2, 2]]

def raw3026 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, -1, 2, -2]]

def raw3026step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, -1, -1, 2], ![-1, 0, 1, 0], ![-1, 1, -2, 2]]

def raw3026step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 2, 2, -4], ![1, -1, -2, 2]]

def raw3027 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 2, -3], ![1, -2, 1, 0], ![1, 1, -1, -1]]

def raw3028 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw3028step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![-2, 2, 0, 0], ![4, -3, 0, -1]]

def raw3028step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 1, 0], ![2, -2, 0, 0], ![-4, 3, 0, 1]]

def raw3028step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, 0, 3, -4]]

def raw3029 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw3029step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![-2, 2, 1, -1], ![4, -3, -1, 0]]

def raw3029step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 1, 0], ![2, -2, -1, 1], ![-4, 3, 1, 0]]

def raw3029step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -2, 2]]

def raw3030 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 2, -3], ![1, 0, -1, 0], ![1, -1, 1, -1]]

def raw3030step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 0, -1], ![-2, 2, -1, 1], ![4, -3, 0, -1]]

def raw3030step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 0, 1], ![2, -2, 1, -1], ![-4, 3, 0, 1]]

def raw3030step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -2, 2]]

def raw3031 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw3031step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![-2, 3, 0, -1], ![4, -4, 0, 0]]

def raw3031step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 1, 0], ![2, -3, 0, 1], ![-4, 4, 0, 0]]

def raw3031step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 4, -4], ![0, 1, -3, 2], ![1, 0, -1, 0]]

def raw3032 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 3, -4], ![1, 0, -1, 0], ![1, -1, 0, 0]]

def raw3032step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 0, -1], ![-2, 3, -1, 0], ![4, -4, 0, 0]]

def raw3032step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 0, 1], ![2, -3, 1, 0], ![-4, 4, 0, 0]]

def raw3032step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 4, -4], ![0, 1, -3, 2], ![1, 0, -1, 0]]

def raw3033 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -2, 1, 0], ![1, 0, 2, -3]]

def raw3034 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -2, 2, -1], ![1, 0, 1, -2]]

def raw3034step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![-2, -1, 2, 1], ![4, -1, -1, -2]]

def raw3034step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, -2, 0], ![1, -1, 2, -2], ![1, 0, 1, -2]]

def raw3035 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw3035step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![-2, -1, 3, 0], ![4, -1, -2, -1]]

def raw3035step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 3, -2], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def raw3036 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw3036step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![-2, -1, 0, 3], ![4, -1, 0, -3]]

def raw3036step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -2, 1, 1], ![2, 1, 0, -3], ![-4, 1, 0, 3]]

def raw3036step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -3, 2], ![0, 1, 3, -4], ![1, -2, 1, 0]]

def raw3037 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def raw3038 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -1, 2, -2], ![1, -1, 1, -1]]

def raw3038step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def raw3039 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, 0, -2], ![1, -2, 1, 0], ![1, 0, 1, -2]]

def raw3039step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 1, -2, 0], ![1, 1, 0, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical95
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3040 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, 0, -2], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw3040step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![-2, 0, 2, 0], ![4, -2, -1, -1]]

def raw3040step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def raw3041 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, 0, -2], ![1, -2, 3, -2], ![1, 0, -1, 0]]

def raw3041step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![-2, 0, 3, -1], ![4, -2, -2, 0]]

def raw3041step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 4, -2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw3042 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw3042step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![-2, 0, 0, 2], ![4, -2, 0, -2]]

def raw3042step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -2, 1, 1], ![2, 0, 0, -2], ![-4, 2, 0, 2]]

def raw3042step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -2, 1, 0]]

def raw3043 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def raw3043step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def raw3044 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, 0, -2], ![1, -1, 2, -2], ![1, -1, 0, 0]]

def raw3044step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![-2, 0, 2, 0], ![4, -2, -2, 0]]

def raw3044step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -2, 1, 1], ![2, 0, -2, 0], ![-4, 2, 2, 0]]

def raw3044step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -2, 1, 0]]

def raw3045 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, 1, -3], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def raw3045step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![-2, 1, 2, -1], ![4, -3, -1, 0]]

def raw3045step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -2, 2, 0], ![2, -1, -2, 1], ![-4, 3, 1, 0]]

def raw3045step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 3, -4], ![0, 2, -2, 0], ![1, -2, -1, 2]]

def raw3046 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, 1, -3], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw3046step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![-2, 1, 0, 1], ![4, -3, 0, -1]]

def raw3046step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -2, 1, 1], ![2, -1, 0, -1], ![-4, 3, 0, 1]]

def raw3046step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, 1, -2, 0]]

def raw3047 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, 2, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw3047step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![-2, 2, 0, 0], ![4, -4, 0, 0]]

def raw3047step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 4, -4], ![1, 1, -2, 0]]

def raw3048 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![1, -2, 1, 0], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw3048step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def raw3049 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![1, -2, 2, -1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw3049step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 1, 1], ![-2, 2, 1, -1], ![4, -1, -2, -1]]

def raw3049step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 1, -2], ![1, -1, 2, -2], ![1, 1, -2, 0]]

def raw3050 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![1, -2, 2, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw3050step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 2, 0], ![-2, 2, -1, 1], ![4, -1, -1, -2]]

def raw3050step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, -2, 0], ![1, -1, 2, -2], ![1, 0, 1, -2]]

def raw3051 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![1, -2, 3, -2], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw3051step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 2, 0], ![-2, 3, -1, 0], ![4, -2, -1, -1]]

def raw3051step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 3, -2], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def raw3052 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![1, -1, 1, -1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw3052step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def raw3053 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![1, -1, 2, -2], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def raw3053step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def raw3054 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![1, -1, 3, -3], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def raw3054step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 2, -1], ![-2, 3, -1, 0], ![4, -3, -1, 0]]

def raw3054step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 1, -2, 1], ![2, -3, 1, 0], ![-4, 3, 1, 0]]

def raw3054step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -3, 2], ![0, 1, 3, -4], ![1, -2, 1, 0]]

def raw3055 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw3056 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -2, 1, 1], ![1, 0, -1, 0], ![1, 2, 1, -4]]

def raw3056step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 0, 2], ![-1, 1, -1, 1], ![3, 1, 0, -4]]

def raw3056step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 2, 0, -2], ![1, -1, 1, -1], ![-3, -1, 0, 4]]

def raw3056step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw3057 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -2, 1, 1], ![1, 1, -2, 0], ![1, 1, 2, -4]]

def raw3058 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -2, 1, 1], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def raw3058step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 1, 1, -3]]

def raw3059 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -2, 2, 0], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def raw3059step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![2, 0, 0, -2]]

def raw3060 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -2, 2, 0], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw3060step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![-1, 2, 0, -1], ![3, 0, -2, -1]]

def raw3060step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -2, 0]]

def raw3061 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -2, 2, 0], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def raw3061step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![-1, 2, -1, 0], ![3, 0, -1, -2]]

def raw3061step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def raw3062 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, -1, 2], ![0, 0, 2, -2], ![2, 1, 0, -3]]

def raw3062step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, 1, -2], ![0, 0, -2, 2], ![-2, -1, 0, 3]]

def raw3062step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, 0, 1, -2]]

def raw3063 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, -1, 2], ![0, 1, 2, -3], ![2, 0, 0, -2]]

def raw3063step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, 1, -2], ![0, -1, -2, 3], ![-2, 0, 0, 2]]

def raw3063step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, 1, 0, -2]]

def raw3064 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 0, 1], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw3064step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![-1, 0, -1, 2], ![3, 1, 0, -4]]

def raw3064step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![-3, -1, 0, 4]]

def raw3064step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw3065 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 1, 0], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw3065step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, -1, 0], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![-1, -1, -2, 4]]

def raw3065step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw3066 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def raw3067 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 2, -3]]

def raw3067step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 3, -1], ![0, 1, -3, 2], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw3068 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw3068step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw3069 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw3070 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw3070step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 3, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw3071 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw3071step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, -2, 1], ![0, -1, 1, 0], ![-1, 0, 0, 1], ![-1, 0, 0, 1]]

def raw3071step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 2, 1, -3], ![1, 0, -2, 1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical96
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3072 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw3072step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, -2, 1], ![0, -1, 1, 0], ![-2, 0, 0, 2]]

def raw3072step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, 0, 2], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw3073 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw3073step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, -2, 1], ![0, -1, 0, 1], ![-1, 0, 1, 0], ![-1, 0, 0, 1]]

def raw3073step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw3074 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw3074step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![-1, 2, 0, -1], ![3, -1, -1, -1]]

def raw3074step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw3075 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

def raw3075step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, -2, 1], ![0, -1, -1, 2], ![-2, 0, 2, 0]]

def raw3075step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 2, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw3076 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw3077 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw3078 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![2, -1, 1, -2]]

def raw3079 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, -1, 0, -1]]

def raw3079step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw3080 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![1, -1, 1, -1], ![1, 2, -2, -1]]

def raw3080step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![-1, 2, 1, -2], ![3, -1, -1, -1]]

def raw3080step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 1, -2], ![1, -2, -1, 2], ![-3, 1, 1, 1]]

def raw3080step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 2, -1], ![1, 1, -3, 1], ![1, 1, 0, -2]]

def raw3081 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw3081step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, -2, 1], ![-1, 0, 1, 0], ![-1, -1, 0, 2]]

def raw3081step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw3082 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw3082step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![-1, 2, 0, -1], ![3, -1, -1, -1]]

def raw3082step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw3083 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![1, 0, 1, -2], ![1, 1, -2, 0]]

def raw3083step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, -2, 1], ![-1, 0, -1, 2], ![-1, -1, 2, 0]]

def raw3083step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -3, 1], ![1, 0, 1, -2]]

def raw3084 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![1, 1, -2, 0], ![1, 0, 1, -2]]

def raw3084step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, -2, 1], ![-1, -1, 2, 0], ![-1, 0, -1, 2]]

def raw3084step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -3, 1], ![1, 0, 1, -2]]

def raw3085 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![1, 2, -2, -1], ![1, -1, 1, -1]]

def raw3085step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 2, -1], ![-1, 2, -2, 1], ![3, -1, -1, -1]]

def raw3085step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, -2, 1], ![1, -2, 2, -1], ![-3, 1, 1, 1]]

def raw3085step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 2, -1], ![1, 1, -3, 1], ![1, 1, 0, -2]]

def raw3086 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw3087 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw3087step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, -3, 2], ![0, -1, 2, -1], ![-1, 0, 0, 1], ![-1, 0, 0, 1]]

def raw3087step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 2, 1, -3], ![1, 0, -3, 2]]

def raw3088 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, -2, 1], ![2, 0, 0, -2]]

def raw3088step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, -3, 2], ![0, -1, 2, -1], ![-2, 0, 0, 2]]

def raw3088step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 2, 1, -3], ![1, 0, -3, 2]]

def raw3089 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw3090 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw3090step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 3, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw3091 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def raw3092 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw3093 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def raw3093step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, -3, 2], ![0, -1, 0, 1], ![-1, 0, 2, -1], ![-1, 0, 0, 1]]

def raw3093step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, 0, -3, 2]]

def raw3094 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw3094step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 3, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw3095 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw3096 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 2, -2, 0], ![2, -1, 0, -1]]

def raw3097 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw3098 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw3099 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 2, -1, -1], ![2, -1, -1, 0]]

def raw3100 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![1, -1, -1, 1], ![1, 2, -1, -2]]

def raw3100step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, -3, 2], ![-1, 1, 1, -1], ![-1, -2, 1, 2]]

def raw3100step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, 1, -3], ![1, -1, 1, -1], ![1, 0, -3, 2]]

def raw3101 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![1, -1, 0, 0], ![1, 2, -2, -1]]

def raw3101step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![-1, 3, 0, -2], ![3, -2, 0, -1]]

def raw3101step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -2, 3, -1], ![0, 3, -1, -2], ![1, 0, -2, 1]]

def raw3102 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![1, 0, -2, 1], ![1, 1, 0, -2]]

def raw3102step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, -3, 2], ![-1, 0, 2, -1], ![-1, -1, 0, 2]]

def raw3102step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, 0, -3, 2]]

def raw3103 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw3103step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![-1, 3, -1, -1], ![3, -2, 0, -1]]

def raw3103step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, 1, -2, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical97
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3104 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw3104step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, -3, 2], ![-1, 0, 0, 1], ![-1, -1, 2, 0]]

def raw3104step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, -3, 1], ![1, 0, 2, -3]]

def raw3105 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![1, 1, -2, 0], ![1, 0, 0, -1]]

def raw3105step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, -3, 2], ![-1, -1, 2, 0], ![-1, 0, 0, 1]]

def raw3105step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, -3, 1], ![1, 0, 2, -3]]

def raw3106 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![1, 1, -1, -1], ![1, 0, -1, 0]]

def raw3106step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 1, 0], ![-1, 3, -1, -1], ![3, -2, -1, 0]]

def raw3106step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def raw3107 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![1, 2, -1, -2], ![1, -1, -1, 1]]

def raw3107step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, -3, 2], ![-1, -2, 1, 2], ![-1, 1, 1, -1]]

def raw3107step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, 1, -3], ![1, -1, 1, -1], ![1, 0, -3, 2]]

def raw3108 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw3108step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, -1, -1, 3]]

def raw3108step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 0, 1], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw3109 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def raw3109step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, -1, 1], ![-1, -1, 0, 2]]

def raw3109step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw3110 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw3110step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, 1, -1], ![0, 0, -2, 2], ![-1, 1, 0, 0], ![-1, -1, 0, 2]]

def raw3110step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, 0, 0]]

def raw3111 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![2, -2, 0, 0]]

def raw3112 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def raw3113 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def raw3113step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-1, 1, -3, 3], ![-1, 0, 0, 1]]

def raw3113step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -3, 3]]

def raw3114 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw3114step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 1, -3, 3], ![-1, 0, 1, 0]]

def raw3114step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -3, 3]]

def raw3115 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 0, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw3115step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![0, 0, 1, 1, -2], ![-1, 0, -1, 0, 2], ![3, 0, 0, -1, -2]]

def raw3115step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, 0, -2], ![0, 0, -1, -1, 2], ![1, 0, 1, 0, -2], ![-3, 0, 0, 1, 2]]

def raw3115step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![1, 1, 0, -2], ![-3, 0, 1, 2]]

def raw3115step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -3, 2], ![1, 0, 1, -2]]

def raw3116 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 0, 0], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def raw3116step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![-1, 0, -1, 2], ![3, 0, 1, -4]]

def raw3116step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 1, -1], ![1, 0, 1, -2], ![-3, 0, -1, 4]]

def raw3116step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![1, 1, -2], ![-3, -1, 4]]

def raw3116step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2]]

def raw3117 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def raw3117step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -1, 1, 0], ![-2, 1, 0, 1]]

def raw3117step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -2, 0, 1]]

def raw3118 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -2, 0, 0]]

def raw3118step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw3119 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw3119step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, -1, 1, 1]]

def raw3119step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, 0, 0]]

def raw3120 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw3121 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -2, 1, -1]]

def raw3122 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def raw3123 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def raw3123step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def raw3124 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -2, 0, 0]]

def raw3124step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

def raw3125 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw3125step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -2, 3], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw3126 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw3126step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, -1, 1], ![0, -1, 1, 0], ![-1, 1, -1, 1], ![-1, 0, 0, 1]]

def raw3126step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw3127 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw3127step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, -1, 1], ![0, -1, 1, 0], ![-1, 1, -2, 2], ![-1, 0, 1, 0]]

def raw3127step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, -1, 2, -2]]

def raw3128 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def raw3128step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def raw3129 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -2, 1]]

def raw3129step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, -1, 1], ![0, -1, 0, 1], ![-1, 1, -2, 2], ![-1, 0, 2, -1]]

def raw3129step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, -2, 2]]

def raw3130 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw3131 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def raw3132 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw3132step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw3133 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -2, 1, -1]]

def raw3133step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![-1, 1, -1, 1], ![3, -1, -1, -1]]

def raw3133step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 1, -1]]

def raw3134 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw3134step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![-1, 1, 1, -1], ![3, -1, -1, -1]]

def raw3134step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw3135 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -2, 1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical98
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3136 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, -1, 1, -2]]

def raw3136step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, -2, 2], ![0, -1, 2, -1], ![-2, 1, -1, 2]]

def raw3136step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -2, -1, 2]]

def raw3137 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def raw3138 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 0, 0]]

def raw3138step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, 0, -2, 0]]

def raw3139 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 1, -1, -1]]

def raw3140 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw3140step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -2, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw3141 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def raw3141step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, -2, 2], ![0, -1, 1, 0], ![-2, 1, 0, 1]]

def raw3141step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -2, 0, 1]]

def raw3142 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![0, 1, -1, 0], ![2, -2, 0, 0]]

def raw3142step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, 0, -2, 0]]

def raw3143 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 1, -2, 0]]

def raw3144 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw3144step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw3145 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw3145step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, -2, 2], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw3145step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw3146 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw3146step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![-1, 2, 0, -1], ![3, -2, -1, 0]]

def raw3146step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw3147 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -2, 1, 0], ![1, 0, 0, -1]]

def raw3148 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw3149 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, -1, 0, 0]]

def raw3149step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw3150 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![2, -2, 1, -1]]

def raw3151 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def raw3152 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw3152step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw3153 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, -2, 0, 0]]

def raw3153step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -2, 0]]

def raw3154 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![1, -2, 1, 0], ![1, 2, -2, -1]]

def raw3154step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![-1, 2, 1, -2], ![3, -2, 0, -1]]

def raw3154step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 2, -2], ![1, -2, -1, 2], ![-3, 2, 0, 1]]

def raw3154step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -3, 1]]

def raw3155 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def raw3155step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, -2, 2], ![-1, 1, 1, -1], ![-1, -1, 0, 2]]

def raw3155step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -1, 1, -1]]

def raw3156 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw3156step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![-1, 2, 0, -1], ![3, -2, 0, -1]]

def raw3156step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 1, -1], ![1, -2, 0, 1], ![-3, 2, 0, 1]]

def raw3156step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw3157 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw3157step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, -2, 2], ![-1, 1, -1, 1], ![-1, -1, 2, 0]]

def raw3157step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -3, 1], ![1, -1, 1, -1]]

def raw3158 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![1, 1, -2, 0], ![1, -1, 1, -1]]

def raw3158step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, -2, 2], ![-1, -1, 2, 0], ![-1, 1, -1, 1]]

def raw3158step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -3, 1], ![1, -1, 1, -1]]

def raw3159 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![1, 2, -2, -1], ![1, -2, 1, 0]]

def raw3159step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 2, -2], ![-1, 2, -2, 1], ![3, -2, -1, 0]]

def raw3159step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, -2, 2], ![1, -2, 2, -1], ![-3, 2, 1, 0]]

def raw3159step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -3, 1]]

def raw3160 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw3160step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, -3, 3], ![0, -1, 2, -1], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw3160step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 0, -3, 3], ![0, 2, 1, -3], ![1, -1, 0, 0]]

def raw3161 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 3, -3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 0, 0]]

def raw3162 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 3, -3], ![0, 1, -1, 0], ![2, -1, -1, 0]]

def raw3162step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![-1, 3, -1, -1], ![3, -3, 0, 0]]

def raw3162step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw3163 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw3164 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 3, -3], ![0, 2, -2, 0], ![2, -2, 0, 0]]

def raw3165 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 3, -3], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def raw3165step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, -3, 3], ![-1, 1, 1, -1], ![-1, -1, 1, 1]]

def raw3165step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -3, 3], ![0, 2, 1, -3], ![1, -1, 1, -1]]

def raw3166 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 3, -3], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw3166step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, -3, 3], ![-1, 1, 0, 0], ![-1, -1, 2, 0]]

def raw3166step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 2, -3, 1], ![1, -1, 0, 0]]

def raw3167 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 3, -3], ![1, 1, -2, 0], ![1, -1, 0, 0]]

def raw3167step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, -3, 3], ![-1, -1, 2, 0], ![-1, 1, 0, 0]]

def raw3167step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 2, -3, 1], ![1, -1, 0, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical99
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3168 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw3169 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw3170 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def raw3171 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -2, 3, -3]]

def raw3171step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![-1, -2, 0, 3], ![3, 1, -1, -3]]

def raw3171step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![1, 2, 0, -3], ![-3, -1, 1, 3]]

def raw3171step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, 1, -3], ![1, -1, -3, 3]]

def raw3172 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw3173 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -2, 2, -2]]

def raw3174 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw3175 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, -1, 0, 0]]

def raw3175step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw3176 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![2, -2, 1, -1]]

def raw3177 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw3178 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 3, -4], ![2, -2, 0, 0]]

def raw3179 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def raw3180 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![1, -2, 3, -2], ![1, 1, 0, -2]]

def raw3181 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw3181step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, -1, 2, -1], ![-1, 1, 0, 0], ![-1, 0, -3, 4]]

def raw3181step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -3, 4], ![0, 2, 1, -3], ![1, -1, 0, 0]]

def raw3182 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 0, 2, -3]]

def raw3182step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, -1, 2, -1], ![-1, 1, -1, 1], ![-1, 0, -2, 3]]

def raw3182step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -2, 3], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw3183 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def raw3183step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, -1, 2, -1], ![-1, 1, -3, 3], ![-1, 0, 0, 1]]

def raw3183step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 2, 1, -3], ![1, -1, -3, 3]]

def raw3184 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, -1, 3, -3]]

def raw3184step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, -1, 2, -1], ![-1, 0, 0, 1], ![-1, 1, -3, 3]]

def raw3184step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 2, 1, -3], ![1, -1, -3, 3]]

def raw3185 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![1, 0, 1, -2], ![1, -1, 2, -2]]

def raw3185step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, -1, 2, -1], ![-1, 0, -1, 2], ![-1, 1, -2, 2]]

def raw3185step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 1, -3], ![1, -1, -2, 2]]

def raw3186 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![1, 0, 2, -3], ![1, -1, 1, -1]]

def raw3186step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, -1, 2, -1], ![-1, 0, -2, 3], ![-1, 1, -1, 1]]

def raw3186step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -2, 3], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw3187 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![1, 0, 3, -4], ![1, -1, 0, 0]]

def raw3187step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, -1, 2, -1], ![-1, 0, -3, 4], ![-1, 1, 0, 0]]

def raw3187step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -3, 4], ![0, 2, 1, -3], ![1, -1, 0, 0]]

def raw3188 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def raw3189 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 0, 2, -3]]

def raw3190 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 1, -2]]

def raw3191 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw3192 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw3193 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def raw3194 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 3, -3]]

def raw3194step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![-1, -1, -1, 3], ![3, 0, 0, -3]]

def raw3194step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, 1, 0, -2]]

def raw3195 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 0, 1, -2]]

def raw3195step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def raw3196 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw3196step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -2, -1]]

def raw3197 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, -1, 0]]

def raw3198 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 3, -3]]

def raw3199 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw3199step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, -1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end


