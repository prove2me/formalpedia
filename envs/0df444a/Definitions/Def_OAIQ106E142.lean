-- Prove2me | Definitions.Def_OAIQ106E142
-- name    : OAIQ106E142
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T18:28:08.138196+00:00
-- url     : https://prove2.me/theorems/95b8ccbb-c3da-4bbc-9092-c24ddb4e3ac7
-- title:
--   Definitions bundle OAIQ106E142 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 4124 declarations of OpenAI's Lean: 4124 definitions. The definitions and types are `OAI.MUB6.Certificate.PairSemantics.pivotPermutation1325`, `OAI.MUB6.Certificate.PairSemantics.pivotPermutation1326`, `OAI.MUB6.Certificate.PairSemantics.pivotPermutation1327`, `OAI.MUB6.Certificate.PairSemantics.pivotPermutation1328`, `OAI.MUB6.Certificate.PairSemantics.pivotPermutation1329`, `OAI.MUB6.Certificate.PairSemantics.pivotPermutation133`, `OAI.MUB6.Certificate.PairSemantics.pivotPermutation1331`, `OAI.MUB6.Certificate.PairSemantics.pivotPermutation1332`, `OAI.MUB6.Certificate.PairSemantics.pivotPermutation1333`, `OAI.MUB6.Certificate.PairSemantics.pivotPermutation1334`, `OAI.MUB6.Certificate.PairSemantics.pivotPermutation1335`, `OAI.MUB6.Certificate.PairSemantics.pivotPermutation1336`, `OAI.MUB6.Certificate.PairSemantics.pivotPermutation1337`, `OAI.MUB6.Certificate.PairSemantics.pivotPermutation1338`, `OAI.MUB6.Certificate.PairSemantics.pivotPermutation1339`, `OAI.MUB6.Certificate.PairSemantics.pivotPermutation1340`, `OAI.MUB6.Certificate.PairSemantics.pivotPermutation1341`, `OAI.MUB6.Certificate.PairSemantics.pivotPermutation1342`, `OAI.MUB6.Certificate.PairSemantics.pivotPermutation1343`, `OAI.MUB6.Certificate.PairSemantics.pivotPermutation1344`, `OAI.MUB6.Certificate.PairSemantics.pivotPermutation1345`, `OAI.MUB6.Certificate.PairSemantics.pivotPermutation1346`, `OAI.MUB6.Certificate.PairSemantics.pivotPermutation1347`, `OAI.MUB6.Certificate.PairSemantics.pivotPermutation1348`, `OAI.MUB6.Certificate.PairSemantics.pivotPermutation1349`, `OAI.MUB6.Certificate.PairSemantics.pivotPermutation1350`, `OAI.MUB6.Certificate.PairSemantics.pivotPermutation1351`, `OAI.MUB6.Certificate.PairSemantics.pivotPermutation1352`, `OAI.MUB6.Certificate.PairSemantics.pivotPermutation1353`, `OAI.MUB6.Certificate.PairSemantics.pivotPermutation1354`, `OAI.MUB6.Certificate.PairSemantics.pivotPermutation1355`, `OAI.MUB6.Certificate.PairSemantics.pivotPermutation1356`, `OAI.MUB6.Certificate.PairSemantics.pivotPermutation1357`, `OAI.MUB6.Certificate.PairSemantics.pivotPermutation1358`, `OAI.MUB6.Certificate.PairSemantics.pivotPermutation1359`, `OAI.MUB6.Certificate.PairSemantics.pivotPermutation1360`, `OAI.MUB6.Certificate.PairSemantics.pivotPermutation1361`, `OAI.MUB6.Certificate.PairSemantics.pivotPermutation1362`, `OAI.MUB6.Certificate.PairSemantics.pivotPermutation1363`, `OAI.MUB6.Certificate.PairSemantics.pivotPermutation1364` and 4084 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_Moments_SmallPartitions`, `MutuallyUnbiased_PairSemantics_Canonical0`, `MutuallyUnbiased_PairSemantics_Canonical3`, `MutuallyUnbiased_PairSemantics_Canonical31`, `MutuallyUnbiased_PairSemantics_Canonical312`, `MutuallyUnbiased_PairSemantics_Canonical313`, `MutuallyUnbiased_PairSemantics_Canonical314`, `MutuallyUnbiased_PairSemantics_Canonical315`, `MutuallyUnbiased_PairSemantics_Canonical316`, `MutuallyUnbiased_PairSemantics_Canonical317`, `MutuallyUnbiased_PairSemantics_Canonical318`, `MutuallyUnbiased_PairSemantics_Canonical32`, `MutuallyUnbiased_PairSemantics_Canonical33`, `MutuallyUnbiased_PairSemantics_Canonical34`, `MutuallyUnbiased_PairSemantics_Canonical35`, `MutuallyUnbiased_PairSemantics_Canonical36`, `MutuallyUnbiased_PairSemantics_Canonical37`, `MutuallyUnbiased_PairSemantics_Canonical38`, `MutuallyUnbiased_PairSemantics_Canonical39`, `MutuallyUnbiased_PairSemantics_Canonical4`, `MutuallyUnbiased_PairSemantics_Canonical40`, `MutuallyUnbiased_PairSemantics_Sound0`, `MutuallyUnbiased_PairSemantics_Sound1`, `MutuallyUnbiased_PairSemantics_Sound10`, `MutuallyUnbiased_PairSemantics_Sound11`, `MutuallyUnbiased_PairSemantics_Sound12`, `MutuallyUnbiased_PairSemantics_Sound13`, `MutuallyUnbiased_PairSemantics_Sound14`, `MutuallyUnbiased_PairSemantics_Sound15`, `MutuallyUnbiased_PairSemantics_Sound2`, `MutuallyUnbiased_PairSemantics_Sound20`, `MutuallyUnbiased_PairSemantics_Sound21`, `MutuallyUnbiased_PairSemantics_Sound22`, `MutuallyUnbiased_PairSemantics_Sound23`, `MutuallyUnbiased_PairSemantics_Sound24`, `MutuallyUnbiased_PairSemantics_Sound25`, `MutuallyUnbiased_PairSemantics_Sound26`, `MutuallyUnbiased_PairSemantics_Sound27`, `MutuallyUnbiased_PairSemantics_Sound28`, `MutuallyUnbiased_PairSemantics_Sound29`, `MutuallyUnbiased_PairSemantics_Sound3`, `MutuallyUnbiased_PairSemantics_Sound30`, `MutuallyUnbiased_PairSemantics_Sound31`, `MutuallyUnbiased_PairSemantics_Sound32`, `MutuallyUnbiased_PairSemantics_Sound33`, `MutuallyUnbiased_PairSemantics_Sound34`, `MutuallyUnbiased_PairSemantics_Sound35`, `MutuallyUnbiased_PairSemantics_Sound36`, `MutuallyUnbiased_PairSemantics_Sound37`, `MutuallyUnbiased_PairSemantics_Sound38`, `MutuallyUnbiased_PairSemantics_Sound39`, `MutuallyUnbiased_PairSemantics_Sound4`, `MutuallyUnbiased_PairSemantics_Sound40`, `MutuallyUnbiased_PairSemantics_Sound41`, `MutuallyUnbiased_PairSemantics_Sound42`, `MutuallyUnbiased_PairSemantics_Sound43`, `MutuallyUnbiased_PairSemantics_Sound44`, `MutuallyUnbiased_PairSemantics_Sound45`, `MutuallyUnbiased_PairSemantics_Sound46`, `MutuallyUnbiased_PairSemantics_Sound47`, `MutuallyUnbiased_PairSemantics_Sound48`, `MutuallyUnbiased_PairSemantics_Sound49`, `MutuallyUnbiased_PairSemantics_Sound5`, `MutuallyUnbiased_PairSemantics_Sound50`, `MutuallyUnbiased_PairSemantics_Sound51`, `MutuallyUnbiased_PairSemantics_Sound52`, `MutuallyUnbiased_PairSemantics_Sound53`, `MutuallyUnbiased_PairSemantics_Sound54`, `MutuallyUnbiased_PairSemantics_Sound6`, `MutuallyUnbiased_PairSemantics_Sound8`, `MutuallyUnbiased_PairSemantics_Sound9`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ106E150`; the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1162_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1163_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1164_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1165_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1170_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1172_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1265_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1266_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1267_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1298_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1299_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1339_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1340_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1341_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1342_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1343_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1395_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1396_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1397_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1399_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1409_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1410_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1411_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1412_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1414_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1441_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1475_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1477_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1478_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2357_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2358_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2526_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2527_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2528_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2530_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2531_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2570_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2572_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2574_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2576_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2593_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2594_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2595_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2599_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2636_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2766_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2828_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2901_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2903_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2904_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2936_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2937_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2939_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2941_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2943_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2957_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2958_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2959_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2960_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2961_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2963_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2986_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2987_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2988_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2990_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2996_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2998_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3003_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3081_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3082_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3087_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3088_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3089_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3094_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3100_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3106_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3109_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3139_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3140_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3184_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3185_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3190_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3191_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3203_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3204_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3205_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3206_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3209_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3210_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3211_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3223_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3226_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3227_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3711_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3727_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3735_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3737_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3739_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3818_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3821_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3823_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3829_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3830_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3847_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3851_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3852_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3853_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3882_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3925_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3936_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3937_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3938_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3965_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3966_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3967_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3969_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3970_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3977_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3980_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3981_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3982_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3984_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3990_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3992_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3994_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3995_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3998_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4003_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4023_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4026_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4031_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4032_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4033_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4053_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5174_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5387_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5415_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5418_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5439_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5450_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5452_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5464_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5465_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5490_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5492_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound111_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound12_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound135_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound136_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound137_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound138_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound139_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound140_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound141_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound142_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound143_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound144_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound145_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound146_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound147_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound148_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound149_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound150_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound151_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound16_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound19_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound20_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound21_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound23_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound28_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound29_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound2_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound30_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound32_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound35_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound37_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound3_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound41_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound49_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound5_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound6_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound78_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound7_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1472_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero14_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero15_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1674_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1785_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero18_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1909_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero488_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero621_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero794_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero818_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound0_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1007_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1008_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound100_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1010_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1013_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1020_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1021_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1093_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1094_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1095_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1096_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1097_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1098_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1103_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1108_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound110_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1110_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1111_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1115_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound111_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1120_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1121_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1124_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1130_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1131_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound113_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound114_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1159_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound115_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1165_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1166_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1167_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound116_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1170_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1177_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1178_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1179_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1194_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound125_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1261_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1262_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1264_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1266_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1267_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1269_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound126_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1272_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1278_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1279_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound127_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1294_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound12_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1300_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1301_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1303_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1309_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound130_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1310_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1311_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1312_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1318_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1324_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound137_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound138_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound139_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound13_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1409_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound140_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1410_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1411_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1412_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1413_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1414_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1418_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1419_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound141_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1420_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1421_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1423_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1429_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1433_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1434_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1435_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1437_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1441_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1442_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound144_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1469_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1470_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1477_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1478_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1479_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1480_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1484_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1492_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1493_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1507_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1510_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1511_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1517_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound151_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1521_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound153_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1559_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1560_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1562_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1567_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1568_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1572_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound163_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1648_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1649_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1650_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1651_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1652_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1653_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1654_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1655_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1656_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1662_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1669_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1672_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1686_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound16_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1703_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1708_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1709_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1715_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1717_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1780_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1781_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1782_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1783_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1784_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1786_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1787_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1788_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1789_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1796_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound17_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1816_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1840_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1844_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1845_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1846_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1847_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1849_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1853_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1854_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1855_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1856_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1859_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1866_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1872_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1874_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound188_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1904_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1905_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1907_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1911_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1914_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1915_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1916_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1917_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1925_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1944_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1963_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1964_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1968_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1969_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1972_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1977_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1985_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound199_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound19_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2033_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2034_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2035_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2036_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2037_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2038_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2040_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2046_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2048_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2049_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2050_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2059_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2062_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2075_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2077_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound207_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound213_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound214_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2166_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2168_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2169_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2170_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2171_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2172_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2173_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2174_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2175_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2176_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2178_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2180_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2181_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2182_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2183_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2184_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2185_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2187_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2188_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2189_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2191_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2192_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2193_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2195_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2196_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2197_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2199_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound21_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2200_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2201_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2202_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2203_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2204_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2205_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2206_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2207_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2208_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2211_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2212_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2214_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2215_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2216_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2217_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2218_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2219_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2220_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2223_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2224_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2225_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2226_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2227_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2228_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2229_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2230_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2231_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2232_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2233_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2235_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2236_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2238_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2240_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2241_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2242_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2244_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2245_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2246_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2247_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2248_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2249_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2250_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2251_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2252_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2253_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2254_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2255_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2256_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2257_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2258_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2259_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2260_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2261_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2262_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2263_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2264_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2265_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2266_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2267_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2268_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound226_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2270_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2271_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2272_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2273_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2274_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2275_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2276_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2278_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2279_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2281_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2282_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2283_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2284_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2285_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2286_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2287_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2288_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2290_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2291_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2292_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2294_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2295_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2296_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2297_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2298_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2299_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2300_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2301_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2302_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2304_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2305_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2306_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2307_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2308_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2309_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2310_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2311_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2312_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2313_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2314_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2315_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2316_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2317_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2318_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2321_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2322_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2323_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2324_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2325_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2326_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2327_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2328_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2329_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2330_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2331_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2332_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2333_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2334_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2335_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2336_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2337_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2338_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2340_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2341_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2342_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2344_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2345_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2346_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2347_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2348_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2350_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2352_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2353_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2354_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2355_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2356_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2357_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2358_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2361_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2362_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2363_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2364_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2365_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2366_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2367_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2368_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2369_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound236_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2373_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2374_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2375_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2376_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2378_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2379_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2380_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2381_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2382_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2383_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2386_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2387_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2388_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2390_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2391_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2392_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2393_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2394_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2395_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2396_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2397_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2398_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2399_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2400_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2401_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2402_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2404_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2405_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2406_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2407_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2408_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2409_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2410_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2411_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2412_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2413_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2414_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2415_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2416_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2418_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2419_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2421_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2422_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2423_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2424_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound244_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound245_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound255_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound267_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound269_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound281_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound282_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound286_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound287_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound296_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound301_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound310_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound311_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound319_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound327_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound335_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound339_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound340_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound341_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound342_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound343_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound344_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound345_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound353_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound354_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound355_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound356_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound357_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound358_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound359_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound365_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound366_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound367_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound368_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound369_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound370_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound371_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound380_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound388_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound391_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound392_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound395_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound396_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound3_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound404_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound411_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound412_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound413_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound418_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound419_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound427_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound428_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound438_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound444_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound445_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound447_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound448_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound452_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound453_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound454_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound456_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound462_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound463_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound470_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound473_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound474_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound481_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound482_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound483_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound484_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound485_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound497_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound498_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound499_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound4_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound500_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound501_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound504_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound513_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound514_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound515_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound516_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound521_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound523_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound524_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound525_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound526_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound531_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound532_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound533_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound534_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound537_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound538_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound539_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound540_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound541_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound542_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound543_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound545_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound546_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound547_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound548_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound551_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound552_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound553_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound554_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound555_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound558_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound564_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound565_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound566_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound567_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound568_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound570_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound571_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound579_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound580_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound581_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound582_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound584_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound585_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound587_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound588_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound589_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound58_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound599_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound5_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound600_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound613_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound614_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound628_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound629_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound630_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound631_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound633_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound635_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound636_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound643_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound644_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound649_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound656_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound657_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound658_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound659_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound663_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound664_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound666_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound667_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound668_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound675_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound683_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound688_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound694_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound700_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound707_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound711_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound712_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound717_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound718_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound719_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound720_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound722_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound727_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound730_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound731_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound732_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound733_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound734_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound735_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound736_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound740_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound741_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound742_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound743_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound751_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound758_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound759_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound769_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound76_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound779_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound780_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound786_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound787_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound788_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound789_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound790_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound792_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound793_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound796_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound797_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound798_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound799_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound7_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound800_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound801_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound802_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound804_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound805_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound813_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound815_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound817_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound822_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound823_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound834_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound841_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound842_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound844_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound847_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound852_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound853_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound857_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound858_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound859_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound863_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound864_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound865_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound866_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound867_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound868_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound872_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound873_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound877_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound878_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound881_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound883_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound884_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound885_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound887_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound888_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound891_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound894_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound897_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound898_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound899_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound902_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound906_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound909_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound911_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound912_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound913_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound917_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound919_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound91_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound925_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound926_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound927_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound928_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound929_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound92_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound932_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound933_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound935_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound936_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound937_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound938_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound939_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound940_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound941_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound942_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound94_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound950_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound954_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound956_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound959_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound962_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound963_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound964_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound966_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound967_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound968_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound971_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound973_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound975_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound976_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound97_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound981_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound983_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound987_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound992_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound99_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval100_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval105_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1075_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval108_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval111_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval113_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval117_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval118_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1194_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1225_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval122_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval126_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1315_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval131_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval136_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval137_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval141_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval143_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1465_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval151_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1523_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval152_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1554_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1555_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval155_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval164_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval165_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval169_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval174_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval175_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval181_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval185_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval18_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval190_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval201_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval202_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval211_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval212_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval217_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval21_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval220_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval224_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval226_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval229_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval232_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval234_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval235_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval242_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval246_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval250_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval256_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval260_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval264_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval266_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval268_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval269_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval275_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval280_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval285_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval286_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval287_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval289_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval296_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval301_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval308_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval310_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval316_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval325_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval332_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval335_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval338_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval339_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval341_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval343_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval351_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval352_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval356_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval357_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval358_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval359_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval366_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval369_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval372_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval378_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval37_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval382_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval383_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval385_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval390_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval398_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval39_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval405_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval408_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval413_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval46_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval474_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval476_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval53_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval55_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval56_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval63_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval69_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval73_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval74_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval79_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval84_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval86_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval8_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval92_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval957_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval145_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval147_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval150_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval215_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval216_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval219_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval21_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval220_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval223_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval238_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval373_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval375_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval44_e`, `OAI.MUB6.Certificate.PairSemantics.boundarySound26_e`, `OAI.MUB6.Certificate.PairSemantics.boundarySound49_e`, `OAI.MUB6.Certificate.PairSemantics.boundarySound58_e`, `OAI.MUB6.Certificate.PairSemantics.boundarySound73_e`, `OAI.MUB6.Certificate.PairSemantics.sound1379_e`, `OAI.MUB6.Certificate.PairSemantics.sound1381_e`, `OAI.MUB6.Certificate.PairSemantics.sound1383_e`, `OAI.MUB6.Certificate.PairSemantics.sound1384_e`, `OAI.MUB6.Certificate.PairSemantics.sound1387_e`, `OAI.MUB6.Certificate.PairSemantics.sound1390_e`, `OAI.MUB6.Certificate.PairSemantics.sound1391_e`, `OAI.MUB6.Certificate.PairSemantics.sound1395_e`, `OAI.MUB6.Certificate.PairSemantics.sound1399_e`, `OAI.MUB6.Certificate.PairSemantics.sound1414_e`, `OAI.MUB6.Certificate.PairSemantics.sound1419_e`, `OAI.MUB6.Certificate.PairSemantics.sound1423_e`, `OAI.MUB6.Certificate.PairSemantics.sound1424_e`, `OAI.MUB6.Certificate.PairSemantics.sound1425_e`, `OAI.MUB6.Certificate.PairSemantics.sound1434_e`, `OAI.MUB6.Certificate.PairSemantics.sound1437_e`, `OAI.MUB6.Certificate.PairSemantics.sound1443_e`, `OAI.MUB6.Certificate.PairSemantics.sound1458_e`, `OAI.MUB6.Certificate.PairSemantics.sound1486_e`, `OAI.MUB6.Certificate.PairSemantics.sound1504_e`, `OAI.MUB6.Certificate.PairSemantics.sound1506_e`, `OAI.MUB6.Certificate.PairSemantics.sound1512_e`, `OAI.MUB6.Certificate.PairSemantics.sound1518_e`, `OAI.MUB6.Certificate.PairSemantics.sound1529_e`, `OAI.MUB6.Certificate.PairSemantics.sound1530_e`, `OAI.MUB6.Certificate.PairSemantics.sound1531_e`, `OAI.MUB6.Certificate.PairSemantics.sound1535_e`, `OAI.MUB6.Certificate.PairSemantics.sound1540_e`, `OAI.MUB6.Certificate.PairSemantics.sound1548_e`, `OAI.MUB6.Certificate.PairSemantics.sound1605_e`, `OAI.MUB6.Certificate.PairSemantics.sound1614_e`, `OAI.MUB6.Certificate.PairSemantics.sound1617_e`, `OAI.MUB6.Certificate.PairSemantics.sound1624_e`, `OAI.MUB6.Certificate.PairSemantics.sound1627_e`, `OAI.MUB6.Certificate.PairSemantics.sound1628_e`, `OAI.MUB6.Certificate.PairSemantics.sound1631_e`, `OAI.MUB6.Certificate.PairSemantics.sound1634_e`, `OAI.MUB6.Certificate.PairSemantics.sound1635_e`, `OAI.MUB6.Certificate.PairSemantics.sound1637_e`, `OAI.MUB6.Certificate.PairSemantics.sound1644_e`, `OAI.MUB6.Certificate.PairSemantics.sound1646_e`, `OAI.MUB6.Certificate.PairSemantics.sound1648_e`, `OAI.MUB6.Certificate.PairSemantics.sound1685_e`, `OAI.MUB6.Certificate.PairSemantics.sound1716_e`, `OAI.MUB6.Certificate.PairSemantics.sound1736_e`, `OAI.MUB6.Certificate.PairSemantics.sound1739_e`, `OAI.MUB6.Certificate.PairSemantics.sound1768_e`, `OAI.MUB6.Certificate.PairSemantics.sound1770_e`, `OAI.MUB6.Certificate.PairSemantics.sound1793_e`, `OAI.MUB6.Certificate.PairSemantics.sound1800_e`, `OAI.MUB6.Certificate.PairSemantics.sound1828_e`, `OAI.MUB6.Certificate.PairSemantics.sound1849_e`, `OAI.MUB6.Certificate.PairSemantics.sound1858_e`, `OAI.MUB6.Certificate.PairSemantics.sound1860_e`, `OAI.MUB6.Certificate.PairSemantics.sound1865_e`, `OAI.MUB6.Certificate.PairSemantics.sound1866_e`, `OAI.MUB6.Certificate.PairSemantics.sound1867_e`, `OAI.MUB6.Certificate.PairSemantics.sound1869_e`, `OAI.MUB6.Certificate.PairSemantics.sound1870_e`, `OAI.MUB6.Certificate.PairSemantics.sound1872_e`, `OAI.MUB6.Certificate.PairSemantics.sound1875_e`, `OAI.MUB6.Certificate.PairSemantics.sound1876_e`, `OAI.MUB6.Certificate.PairSemantics.sound1879_e`, `OAI.MUB6.Certificate.PairSemantics.sound1885_e`, `OAI.MUB6.Certificate.PairSemantics.sound1978_e`, `OAI.MUB6.Certificate.PairSemantics.sound1980_e`, `OAI.MUB6.Certificate.PairSemantics.sound1986_e`, `OAI.MUB6.Certificate.PairSemantics.sound1987_e`, `OAI.MUB6.Certificate.PairSemantics.sound2041_e`, `OAI.MUB6.Certificate.PairSemantics.sound2058_e`, `OAI.MUB6.Certificate.PairSemantics.sound2071_e`, `OAI.MUB6.Certificate.PairSemantics.sound2097_e`, `OAI.MUB6.Certificate.PairSemantics.sound2106_e`, `OAI.MUB6.Certificate.PairSemantics.sound2107_e`, `OAI.MUB6.Certificate.PairSemantics.sound2108_e`, `OAI.MUB6.Certificate.PairSemantics.sound2117_e`, `OAI.MUB6.Certificate.PairSemantics.sound2122_e`, `OAI.MUB6.Certificate.PairSemantics.sound2123_e`, `OAI.MUB6.Certificate.PairSemantics.sound2128_e`, `OAI.MUB6.Certificate.PairSemantics.sound2132_e`, `OAI.MUB6.Certificate.PairSemantics.sound2152_e`, `OAI.MUB6.Certificate.PairSemantics.sound2168_e`, `OAI.MUB6.Certificate.PairSemantics.sound2175_e`, `OAI.MUB6.Certificate.PairSemantics.sound2177_e`, `OAI.MUB6.Certificate.PairSemantics.sound2189_e`, `OAI.MUB6.Certificate.PairSemantics.sound2190_e`, `OAI.MUB6.Certificate.PairSemantics.sound2197_e`, `OAI.MUB6.Certificate.PairSemantics.sound2201_e`, `OAI.MUB6.Certificate.PairSemantics.sound2202_e`, `OAI.MUB6.Certificate.PairSemantics.sound2213_e`, `OAI.MUB6.Certificate.PairSemantics.sound2228_e`, `OAI.MUB6.Certificate.PairSemantics.sound2244_e`, `OAI.MUB6.Certificate.PairSemantics.sound2262_e`, `OAI.MUB6.Certificate.PairSemantics.sound2284_e`, `OAI.MUB6.Certificate.PairSemantics.sound2286_e`, `OAI.MUB6.Certificate.PairSemantics.sound2293_e`, `OAI.MUB6.Certificate.PairSemantics.sound2294_e`, `OAI.MUB6.Certificate.PairSemantics.sound2295_e`, `OAI.MUB6.Certificate.PairSemantics.sound2296_e`, `OAI.MUB6.Certificate.PairSemantics.sound2312_e`, `OAI.MUB6.Certificate.PairSemantics.sound2324_e`, `OAI.MUB6.Certificate.PairSemantics.sound2327_e`, `OAI.MUB6.Certificate.PairSemantics.sound2338_e`, `OAI.MUB6.Certificate.PairSemantics.sound2375_e`, `OAI.MUB6.Certificate.PairSemantics.sound2382_e`, `OAI.MUB6.Certificate.PairSemantics.sound2390_e`, `OAI.MUB6.Certificate.PairSemantics.sound2391_e`, `OAI.MUB6.Certificate.PairSemantics.sound2394_e`, `OAI.MUB6.Certificate.PairSemantics.sound2399_e`, `OAI.MUB6.Certificate.PairSemantics.sound2400_e`, `OAI.MUB6.Certificate.PairSemantics.sound2401_e`, `OAI.MUB6.Certificate.PairSemantics.sound2403_e`, `OAI.MUB6.Certificate.PairSemantics.sound2415_e`, `OAI.MUB6.Certificate.PairSemantics.sound2416_e`, `OAI.MUB6.Certificate.PairSemantics.sound2420_e`, `OAI.MUB6.Certificate.PairSemantics.sound2433_e`, `OAI.MUB6.Certificate.PairSemantics.sound2434_e`, `OAI.MUB6.Certificate.PairSemantics.sound2435_e`, `OAI.MUB6.Certificate.PairSemantics.sound2436_e`, `OAI.MUB6.Certificate.PairSemantics.sound2442_e`, `OAI.MUB6.Certificate.PairSemantics.sound2444_e`, `OAI.MUB6.Certificate.PairSemantics.sound2445_e`, `OAI.MUB6.Certificate.PairSemantics.sound2454_e`, `OAI.MUB6.Certificate.PairSemantics.sound2456_e`, `OAI.MUB6.Certificate.PairSemantics.sound2457_e`, `OAI.MUB6.Certificate.PairSemantics.sound2463_e`, `OAI.MUB6.Certificate.PairSemantics.sound2464_e`, `OAI.MUB6.Certificate.PairSemantics.sound2465_e`, `OAI.MUB6.Certificate.PairSemantics.sound2472_e`, `OAI.MUB6.Certificate.PairSemantics.sound2473_e`, `OAI.MUB6.Certificate.PairSemantics.sound2477_e`, `OAI.MUB6.Certificate.PairSemantics.sound2479_e`, `OAI.MUB6.Certificate.PairSemantics.sound2489_e`, `OAI.MUB6.Certificate.PairSemantics.sound2490_e`, `OAI.MUB6.Certificate.PairSemantics.sound2491_e`, `OAI.MUB6.Certificate.PairSemantics.sound2492_e`, `OAI.MUB6.Certificate.PairSemantics.sound2507_e`, `OAI.MUB6.Certificate.PairSemantics.sound2520_e`, `OAI.MUB6.Certificate.PairSemantics.sound2521_e`, `OAI.MUB6.Certificate.PairSemantics.sound2522_e`, `OAI.MUB6.Certificate.PairSemantics.sound2524_e`, `OAI.MUB6.Certificate.PairSemantics.sound2525_e`, `OAI.MUB6.Certificate.PairSemantics.sound2527_e`, `OAI.MUB6.Certificate.PairSemantics.sound2533_e`, `OAI.MUB6.Certificate.PairSemantics.sound2540_e`, `OAI.MUB6.Certificate.PairSemantics.sound2546_e`, `OAI.MUB6.Certificate.PairSemantics.sound2547_e`, `OAI.MUB6.Certificate.PairSemantics.sound2548_e`, `OAI.MUB6.Certificate.PairSemantics.sound2557_e`, `OAI.MUB6.Certificate.PairSemantics.sound2558_e`, `OAI.MUB6.Certificate.PairSemantics.sound2559_e`, `OAI.MUB6.Certificate.PairSemantics.sound2564_e`, `OAI.MUB6.Certificate.PairSemantics.sound2565_e`, `OAI.MUB6.Certificate.PairSemantics.sound2566_e`, `OAI.MUB6.Certificate.PairSemantics.sound2573_e`, `OAI.MUB6.Certificate.PairSemantics.sound2578_e`, `OAI.MUB6.Certificate.PairSemantics.sound2580_e`, `OAI.MUB6.Certificate.PairSemantics.sound2593_e`, `OAI.MUB6.Certificate.PairSemantics.sound2602_e`, `OAI.MUB6.Certificate.PairSemantics.sound2604_e`, `OAI.MUB6.Certificate.PairSemantics.sound2606_e`, `OAI.MUB6.Certificate.PairSemantics.sound2619_e`, `OAI.MUB6.Certificate.PairSemantics.sound2620_e`, `OAI.MUB6.Certificate.PairSemantics.sound2623_e`, `OAI.MUB6.Certificate.PairSemantics.sound2627_e`, `OAI.MUB6.Certificate.PairSemantics.sound2641_e`, `OAI.MUB6.Certificate.PairSemantics.sound2657_e`, `OAI.MUB6.Certificate.PairSemantics.sound2658_e`, `OAI.MUB6.Certificate.PairSemantics.sound2661_e`, `OAI.MUB6.Certificate.PairSemantics.sound2666_e`, `OAI.MUB6.Certificate.PairSemantics.sound2669_e`, `OAI.MUB6.Certificate.PairSemantics.sound2670_e`, `OAI.MUB6.Certificate.PairSemantics.sound2671_e`, `OAI.MUB6.Certificate.PairSemantics.sound2686_e`, `OAI.MUB6.Certificate.PairSemantics.sound2690_e`, `OAI.MUB6.Certificate.PairSemantics.sound2693_e`, `OAI.MUB6.Certificate.PairSemantics.sound2698_e`, `OAI.MUB6.Certificate.PairSemantics.sound2708_e`, `OAI.MUB6.Certificate.PairSemantics.sound2710_e`, `OAI.MUB6.Certificate.PairSemantics.sound2714_e`, `OAI.MUB6.Certificate.PairSemantics.sound2729_e`, `OAI.MUB6.Certificate.PairSemantics.sound2732_e`, `OAI.MUB6.Certificate.PairSemantics.sound2733_e`, `OAI.MUB6.Certificate.PairSemantics.sound2735_e`, `OAI.MUB6.Certificate.PairSemantics.sound2754_e`, `OAI.MUB6.Certificate.PairSemantics.sound2757_e`, `OAI.MUB6.Certificate.PairSemantics.sound2788_e`, `OAI.MUB6.Certificate.PairSemantics.sound2790_e`, `OAI.MUB6.Certificate.PairSemantics.sound2793_e`, `OAI.MUB6.Certificate.PairSemantics.sound2807_e`, `OAI.MUB6.Certificate.PairSemantics.sound2817_e`, `OAI.MUB6.Certificate.PairSemantics.sound2829_e`, `OAI.MUB6.Certificate.PairSemantics.sound2836_e`, `OAI.MUB6.Certificate.PairSemantics.sound2845_e`, `OAI.MUB6.Certificate.PairSemantics.sound2853_e`, `OAI.MUB6.Certificate.PairSemantics.sound2854_e`, `OAI.MUB6.Certificate.PairSemantics.sound2858_e`, `OAI.MUB6.Certificate.PairSemantics.sound2863_e`, `OAI.MUB6.Certificate.PairSemantics.sound2864_e`, `OAI.MUB6.Certificate.PairSemantics.sound2865_e`, `OAI.MUB6.Certificate.PairSemantics.sound2866_e`, `OAI.MUB6.Certificate.PairSemantics.sound2867_e`, `OAI.MUB6.Certificate.PairSemantics.sound2868_e`, `OAI.MUB6.Certificate.PairSemantics.sound2872_e`, `OAI.MUB6.Certificate.PairSemantics.sound2873_e`, `OAI.MUB6.Certificate.PairSemantics.sound2874_e`, `OAI.MUB6.Certificate.PairSemantics.sound2875_e`, `OAI.MUB6.Certificate.PairSemantics.sound2878_e`, `OAI.MUB6.Certificate.PairSemantics.sound2879_e`, `OAI.MUB6.Certificate.PairSemantics.sound2880_e`, `OAI.MUB6.Certificate.PairSemantics.sound2882_e`, `OAI.MUB6.Certificate.PairSemantics.sound2883_e`, `OAI.MUB6.Certificate.PairSemantics.sound2884_e`, `OAI.MUB6.Certificate.PairSemantics.sound2887_e`, `OAI.MUB6.Certificate.PairSemantics.sound2888_e`, `OAI.MUB6.Certificate.PairSemantics.sound2889_e`, `OAI.MUB6.Certificate.PairSemantics.sound2890_e`, `OAI.MUB6.Certificate.PairSemantics.sound2891_e`, `OAI.MUB6.Certificate.PairSemantics.sound2892_e`, `OAI.MUB6.Certificate.PairSemantics.sound2894_e`, `OAI.MUB6.Certificate.PairSemantics.sound2895_e`, `OAI.MUB6.Certificate.PairSemantics.sound2896_e`, `OAI.MUB6.Certificate.PairSemantics.sound2897_e`, `OAI.MUB6.Certificate.PairSemantics.sound2898_e`, `OAI.MUB6.Certificate.PairSemantics.sound2899_e`, `OAI.MUB6.Certificate.PairSemantics.sound2900_e`, `OAI.MUB6.Certificate.PairSemantics.sound2901_e`, `OAI.MUB6.Certificate.PairSemantics.sound2902_e`, `OAI.MUB6.Certificate.PairSemantics.sound2904_e`, `OAI.MUB6.Certificate.PairSemantics.sound2905_e`, `OAI.MUB6.Certificate.PairSemantics.sound2906_e`, `OAI.MUB6.Certificate.PairSemantics.sound2908_e`, `OAI.MUB6.Certificate.PairSemantics.sound2909_e`, `OAI.MUB6.Certificate.PairSemantics.sound2910_e`, `OAI.MUB6.Certificate.PairSemantics.sound2912_e`, `OAI.MUB6.Certificate.PairSemantics.sound2913_e`, `OAI.MUB6.Certificate.PairSemantics.sound2914_e`, `OAI.MUB6.Certificate.PairSemantics.sound2915_e`, `OAI.MUB6.Certificate.PairSemantics.sound2916_e`, `OAI.MUB6.Certificate.PairSemantics.sound2917_e`, `OAI.MUB6.Certificate.PairSemantics.sound2919_e`, `OAI.MUB6.Certificate.PairSemantics.sound2920_e`, `OAI.MUB6.Certificate.PairSemantics.sound2922_e`, `OAI.MUB6.Certificate.PairSemantics.sound2924_e`, `OAI.MUB6.Certificate.PairSemantics.sound2925_e`, `OAI.MUB6.Certificate.PairSemantics.sound2926_e`, `OAI.MUB6.Certificate.PairSemantics.sound2927_e`, `OAI.MUB6.Certificate.PairSemantics.sound2928_e`, `OAI.MUB6.Certificate.PairSemantics.sound2929_e`, `OAI.MUB6.Certificate.PairSemantics.sound2931_e`, `OAI.MUB6.Certificate.PairSemantics.sound2933_e`, `OAI.MUB6.Certificate.PairSemantics.sound2935_e`, `OAI.MUB6.Certificate.PairSemantics.sound2936_e`, `OAI.MUB6.Certificate.PairSemantics.sound2939_e`, `OAI.MUB6.Certificate.PairSemantics.sound2940_e`, `OAI.MUB6.Certificate.PairSemantics.sound2941_e`, `OAI.MUB6.Certificate.PairSemantics.sound2942_e`, `OAI.MUB6.Certificate.PairSemantics.sound2943_e`, `OAI.MUB6.Certificate.PairSemantics.sound2944_e`, `OAI.MUB6.Certificate.PairSemantics.sound2946_e`, `OAI.MUB6.Certificate.PairSemantics.sound2949_e`, `OAI.MUB6.Certificate.PairSemantics.sound2950_e`, `OAI.MUB6.Certificate.PairSemantics.sound2951_e`, `OAI.MUB6.Certificate.PairSemantics.sound2952_e`, `OAI.MUB6.Certificate.PairSemantics.sound2953_e`, `OAI.MUB6.Certificate.PairSemantics.sound2954_e`, `OAI.MUB6.Certificate.PairSemantics.sound2956_e`, `OAI.MUB6.Certificate.PairSemantics.sound2957_e`, `OAI.MUB6.Certificate.PairSemantics.sound2959_e`, `OAI.MUB6.Certificate.PairSemantics.sound2960_e`, `OAI.MUB6.Certificate.PairSemantics.sound2961_e`, `OAI.MUB6.Certificate.PairSemantics.sound2962_e`, `OAI.MUB6.Certificate.PairSemantics.sound2963_e`, `OAI.MUB6.Certificate.PairSemantics.sound2964_e`, `OAI.MUB6.Certificate.PairSemantics.sound2965_e`, `OAI.MUB6.Certificate.PairSemantics.sound2966_e`, `OAI.MUB6.Certificate.PairSemantics.sound2967_e`, `OAI.MUB6.Certificate.PairSemantics.sound2968_e`, `OAI.MUB6.Certificate.PairSemantics.sound2969_e`, `OAI.MUB6.Certificate.PairSemantics.sound2970_e`, `OAI.MUB6.Certificate.PairSemantics.sound2972_e`, `OAI.MUB6.Certificate.PairSemantics.sound2973_e`, `OAI.MUB6.Certificate.PairSemantics.sound2974_e`, `OAI.MUB6.Certificate.PairSemantics.sound2975_e`, `OAI.MUB6.Certificate.PairSemantics.sound2976_e`, `OAI.MUB6.Certificate.PairSemantics.sound2977_e`, `OAI.MUB6.Certificate.PairSemantics.sound2979_e`, `OAI.MUB6.Certificate.PairSemantics.sound2980_e`, `OAI.MUB6.Certificate.PairSemantics.sound2984_e`, `OAI.MUB6.Certificate.PairSemantics.sound2985_e`, `OAI.MUB6.Certificate.PairSemantics.sound2986_e`, `OAI.MUB6.Certificate.PairSemantics.sound2987_e`, `OAI.MUB6.Certificate.PairSemantics.sound2989_e`, `OAI.MUB6.Certificate.PairSemantics.sound2990_e`, `OAI.MUB6.Certificate.PairSemantics.sound2991_e`, `OAI.MUB6.Certificate.PairSemantics.sound2992_e`, `OAI.MUB6.Certificate.PairSemantics.sound2994_e`, `OAI.MUB6.Certificate.PairSemantics.sound2996_e`, `OAI.MUB6.Certificate.PairSemantics.sound2997_e`, `OAI.MUB6.Certificate.PairSemantics.sound2998_e`, `OAI.MUB6.Certificate.PairSemantics.sound2999_e`, `OAI.MUB6.Certificate.PairSemantics.sound3000_e`, `OAI.MUB6.Certificate.PairSemantics.sound3001_e`, `OAI.MUB6.Certificate.PairSemantics.sound3002_e`, `OAI.MUB6.Certificate.PairSemantics.sound3004_e`, `OAI.MUB6.Certificate.PairSemantics.sound3006_e`, `OAI.MUB6.Certificate.PairSemantics.sound3007_e`, `OAI.MUB6.Certificate.PairSemantics.sound3009_e`, `OAI.MUB6.Certificate.PairSemantics.sound3011_e`, `OAI.MUB6.Certificate.PairSemantics.sound3012_e`, `OAI.MUB6.Certificate.PairSemantics.sound3013_e`, `OAI.MUB6.Certificate.PairSemantics.sound3014_e`, `OAI.MUB6.Certificate.PairSemantics.sound3015_e`, `OAI.MUB6.Certificate.PairSemantics.sound3016_e`, `OAI.MUB6.Certificate.PairSemantics.sound3017_e`, `OAI.MUB6.Certificate.PairSemantics.sound3018_e`, `OAI.MUB6.Certificate.PairSemantics.sound3019_e`, `OAI.MUB6.Certificate.PairSemantics.sound3020_e`, `OAI.MUB6.Certificate.PairSemantics.sound3021_e`, `OAI.MUB6.Certificate.PairSemantics.sound3022_e`, `OAI.MUB6.Certificate.PairSemantics.sound3023_e`, `OAI.MUB6.Certificate.PairSemantics.sound3024_e`, `OAI.MUB6.Certificate.PairSemantics.sound3025_e`, `OAI.MUB6.Certificate.PairSemantics.sound3026_e`, `OAI.MUB6.Certificate.PairSemantics.sound3027_e`, `OAI.MUB6.Certificate.PairSemantics.sound3028_e`, `OAI.MUB6.Certificate.PairSemantics.sound3029_e`, `OAI.MUB6.Certificate.PairSemantics.sound3030_e`, `OAI.MUB6.Certificate.PairSemantics.sound3032_e`, `OAI.MUB6.Certificate.PairSemantics.sound3034_e`, `OAI.MUB6.Certificate.PairSemantics.sound3035_e`, `OAI.MUB6.Certificate.PairSemantics.sound3036_e`, `OAI.MUB6.Certificate.PairSemantics.sound3037_e`, `OAI.MUB6.Certificate.PairSemantics.sound3038_e`, `OAI.MUB6.Certificate.PairSemantics.sound3039_e`, `OAI.MUB6.Certificate.PairSemantics.sound3040_e`, `OAI.MUB6.Certificate.PairSemantics.sound3041_e`, `OAI.MUB6.Certificate.PairSemantics.sound3042_e`, `OAI.MUB6.Certificate.PairSemantics.sound3045_e`, `OAI.MUB6.Certificate.PairSemantics.sound3049_e`, `OAI.MUB6.Certificate.PairSemantics.sound3050_e`, `OAI.MUB6.Certificate.PairSemantics.sound3051_e`, `OAI.MUB6.Certificate.PairSemantics.sound3052_e`, `OAI.MUB6.Certificate.PairSemantics.sound3053_e`, `OAI.MUB6.Certificate.PairSemantics.sound3054_e`, `OAI.MUB6.Certificate.PairSemantics.sound3055_e`, `OAI.MUB6.Certificate.PairSemantics.sound3057_e`, `OAI.MUB6.Certificate.PairSemantics.sound3059_e`, `OAI.MUB6.Certificate.PairSemantics.sound3060_e`, `OAI.MUB6.Certificate.PairSemantics.sound3061_e`, `OAI.MUB6.Certificate.PairSemantics.sound3062_e`, `OAI.MUB6.Certificate.PairSemantics.sound3063_e`, `OAI.MUB6.Certificate.PairSemantics.sound3065_e`, `OAI.MUB6.Certificate.PairSemantics.sound3066_e`, `OAI.MUB6.Certificate.PairSemantics.sound3067_e`, `OAI.MUB6.Certificate.PairSemantics.sound3068_e`, `OAI.MUB6.Certificate.PairSemantics.sound3069_e`, `OAI.MUB6.Certificate.PairSemantics.sound3071_e`, `OAI.MUB6.Certificate.PairSemantics.sound3072_e`, `OAI.MUB6.Certificate.PairSemantics.sound3073_e`, `OAI.MUB6.Certificate.PairSemantics.sound3074_e`, `OAI.MUB6.Certificate.PairSemantics.sound3075_e`, `OAI.MUB6.Certificate.PairSemantics.sound3076_e`, `OAI.MUB6.Certificate.PairSemantics.sound3077_e`, `OAI.MUB6.Certificate.PairSemantics.sound3078_e`, `OAI.MUB6.Certificate.PairSemantics.sound3079_e`, `OAI.MUB6.Certificate.PairSemantics.sound3081_e`, `OAI.MUB6.Certificate.PairSemantics.sound3082_e`, `OAI.MUB6.Certificate.PairSemantics.sound3084_e`, `OAI.MUB6.Certificate.PairSemantics.sound3085_e`, `OAI.MUB6.Certificate.PairSemantics.sound3086_e`, `OAI.MUB6.Certificate.PairSemantics.sound3087_e`, `OAI.MUB6.Certificate.PairSemantics.sound3088_e`, `OAI.MUB6.Certificate.PairSemantics.sound3090_e`, `OAI.MUB6.Certificate.PairSemantics.sound3091_e`, `OAI.MUB6.Certificate.PairSemantics.sound3092_e`, `OAI.MUB6.Certificate.PairSemantics.sound3093_e`, `OAI.MUB6.Certificate.PairSemantics.sound3094_e`, `OAI.MUB6.Certificate.PairSemantics.sound3095_e`, `OAI.MUB6.Certificate.PairSemantics.sound3096_e`, `OAI.MUB6.Certificate.PairSemantics.sound3098_e`, `OAI.MUB6.Certificate.PairSemantics.sound3099_e`, `OAI.MUB6.Certificate.PairSemantics.sound3100_e`, `OAI.MUB6.Certificate.PairSemantics.sound3101_e`, `OAI.MUB6.Certificate.PairSemantics.sound3105_e`, `OAI.MUB6.Certificate.PairSemantics.sound3106_e`, `OAI.MUB6.Certificate.PairSemantics.sound3107_e`, `OAI.MUB6.Certificate.PairSemantics.sound3108_e`, `OAI.MUB6.Certificate.PairSemantics.sound3110_e`, `OAI.MUB6.Certificate.PairSemantics.sound3111_e`, `OAI.MUB6.Certificate.PairSemantics.sound3112_e`, `OAI.MUB6.Certificate.PairSemantics.sound3113_e`, `OAI.MUB6.Certificate.PairSemantics.sound3114_e`, `OAI.MUB6.Certificate.PairSemantics.sound3115_e`, `OAI.MUB6.Certificate.PairSemantics.sound3118_e`, `OAI.MUB6.Certificate.PairSemantics.sound3119_e`, `OAI.MUB6.Certificate.PairSemantics.sound3120_e`, `OAI.MUB6.Certificate.PairSemantics.sound3122_e`, `OAI.MUB6.Certificate.PairSemantics.sound3123_e`, `OAI.MUB6.Certificate.PairSemantics.sound3124_e`, `OAI.MUB6.Certificate.PairSemantics.sound3125_e`, `OAI.MUB6.Certificate.PairSemantics.sound3127_e`, `OAI.MUB6.Certificate.PairSemantics.sound3128_e`, `OAI.MUB6.Certificate.PairSemantics.sound3129_e`, `OAI.MUB6.Certificate.PairSemantics.sound3130_e`, `OAI.MUB6.Certificate.PairSemantics.sound3131_e`, `OAI.MUB6.Certificate.PairSemantics.sound3132_e`, `OAI.MUB6.Certificate.PairSemantics.sound3133_e`, `OAI.MUB6.Certificate.PairSemantics.sound3135_e`, `OAI.MUB6.Certificate.PairSemantics.sound3136_e`, `OAI.MUB6.Certificate.PairSemantics.sound3137_e`, `OAI.MUB6.Certificate.PairSemantics.sound3138_e`, `OAI.MUB6.Certificate.PairSemantics.sound3139_e`, `OAI.MUB6.Certificate.PairSemantics.sound3140_e`, `OAI.MUB6.Certificate.PairSemantics.sound3141_e`, `OAI.MUB6.Certificate.PairSemantics.sound3142_e`, `OAI.MUB6.Certificate.PairSemantics.sound3144_e`, `OAI.MUB6.Certificate.PairSemantics.sound3145_e`, `OAI.MUB6.Certificate.PairSemantics.sound3146_e`, `OAI.MUB6.Certificate.PairSemantics.sound3149_e`, `OAI.MUB6.Certificate.PairSemantics.sound3150_e`, `OAI.MUB6.Certificate.PairSemantics.sound3151_e`, `OAI.MUB6.Certificate.PairSemantics.sound3152_e`, `OAI.MUB6.Certificate.PairSemantics.sound3153_e`, `OAI.MUB6.Certificate.PairSemantics.sound3154_e`, `OAI.MUB6.Certificate.PairSemantics.sound3158_e`, `OAI.MUB6.Certificate.PairSemantics.sound3159_e`, `OAI.MUB6.Certificate.PairSemantics.sound3160_e`, `OAI.MUB6.Certificate.PairSemantics.sound3161_e`, `OAI.MUB6.Certificate.PairSemantics.sound3163_e`, `OAI.MUB6.Certificate.PairSemantics.sound3164_e`, `OAI.MUB6.Certificate.PairSemantics.sound3166_e`, `OAI.MUB6.Certificate.PairSemantics.sound3167_e`, `OAI.MUB6.Certificate.PairSemantics.sound3169_e`, `OAI.MUB6.Certificate.PairSemantics.sound3170_e`, `OAI.MUB6.Certificate.PairSemantics.sound3171_e`, `OAI.MUB6.Certificate.PairSemantics.sound3172_e`, `OAI.MUB6.Certificate.PairSemantics.sound3173_e`, `OAI.MUB6.Certificate.PairSemantics.sound3174_e`, `OAI.MUB6.Certificate.PairSemantics.sound3176_e`, `OAI.MUB6.Certificate.PairSemantics.sound3178_e`, `OAI.MUB6.Certificate.PairSemantics.sound3179_e`, `OAI.MUB6.Certificate.PairSemantics.sound3180_e`, `OAI.MUB6.Certificate.PairSemantics.sound3181_e`, `OAI.MUB6.Certificate.PairSemantics.sound3183_e`, `OAI.MUB6.Certificate.PairSemantics.sound3184_e`, `OAI.MUB6.Certificate.PairSemantics.sound3185_e`, `OAI.MUB6.Certificate.PairSemantics.sound3187_e`, `OAI.MUB6.Certificate.PairSemantics.sound3188_e`, `OAI.MUB6.Certificate.PairSemantics.sound3189_e`, `OAI.MUB6.Certificate.PairSemantics.sound3191_e`, `OAI.MUB6.Certificate.PairSemantics.sound3192_e`, `OAI.MUB6.Certificate.PairSemantics.sound3193_e`, `OAI.MUB6.Certificate.PairSemantics.sound3194_e`, `OAI.MUB6.Certificate.PairSemantics.sound3195_e`, `OAI.MUB6.Certificate.PairSemantics.sound3196_e`, `OAI.MUB6.Certificate.PairSemantics.sound3197_e`, `OAI.MUB6.Certificate.PairSemantics.sound3198_e`, `OAI.MUB6.Certificate.PairSemantics.sound3199_e`, `OAI.MUB6.Certificate.PairSemantics.sound3200_e`, `OAI.MUB6.Certificate.PairSemantics.sound3201_e`, `OAI.MUB6.Certificate.PairSemantics.sound3202_e`, `OAI.MUB6.Certificate.PairSemantics.sound3203_e`, `OAI.MUB6.Certificate.PairSemantics.sound3204_e`, `OAI.MUB6.Certificate.PairSemantics.sound3205_e`, `OAI.MUB6.Certificate.PairSemantics.sound3206_e`, `OAI.MUB6.Certificate.PairSemantics.sound3208_e`, `OAI.MUB6.Certificate.PairSemantics.sound3209_e`, `OAI.MUB6.Certificate.PairSemantics.sound3211_e`, `OAI.MUB6.Certificate.PairSemantics.sound3212_e`, `OAI.MUB6.Certificate.PairSemantics.sound3213_e`, `OAI.MUB6.Certificate.PairSemantics.sound3215_e`, `OAI.MUB6.Certificate.PairSemantics.sound3216_e`, `OAI.MUB6.Certificate.PairSemantics.sound3218_e`, `OAI.MUB6.Certificate.PairSemantics.sound3220_e`, `OAI.MUB6.Certificate.PairSemantics.sound3221_e`, `OAI.MUB6.Certificate.PairSemantics.sound3222_e`, `OAI.MUB6.Certificate.PairSemantics.sound3223_e`, `OAI.MUB6.Certificate.PairSemantics.sound3224_e`, `OAI.MUB6.Certificate.PairSemantics.sound3225_e`, `OAI.MUB6.Certificate.PairSemantics.sound3226_e`, `OAI.MUB6.Certificate.PairSemantics.sound3227_e`, `OAI.MUB6.Certificate.PairSemantics.sound3228_e`, `OAI.MUB6.Certificate.PairSemantics.sound3229_e`, `OAI.MUB6.Certificate.PairSemantics.sound3230_e`, `OAI.MUB6.Certificate.PairSemantics.sound3233_e`, `OAI.MUB6.Certificate.PairSemantics.sound3234_e`, `OAI.MUB6.Certificate.PairSemantics.sound3235_e`, `OAI.MUB6.Certificate.PairSemantics.sound3237_e`, `OAI.MUB6.Certificate.PairSemantics.sound3238_e`, `OAI.MUB6.Certificate.PairSemantics.sound3240_e`, `OAI.MUB6.Certificate.PairSemantics.sound3242_e`, `OAI.MUB6.Certificate.PairSemantics.sound3243_e`, `OAI.MUB6.Certificate.PairSemantics.sound3244_e`, `OAI.MUB6.Certificate.PairSemantics.sound3246_e`, `OAI.MUB6.Certificate.PairSemantics.sound3247_e`, `OAI.MUB6.Certificate.PairSemantics.sound3248_e`, `OAI.MUB6.Certificate.PairSemantics.sound3249_e`, `OAI.MUB6.Certificate.PairSemantics.sound3253_e`, `OAI.MUB6.Certificate.PairSemantics.sound3254_e`, `OAI.MUB6.Certificate.PairSemantics.sound3255_e`, `OAI.MUB6.Certificate.PairSemantics.sound3256_e`, `OAI.MUB6.Certificate.PairSemantics.sound3258_e`, `OAI.MUB6.Certificate.PairSemantics.sound3260_e`, `OAI.MUB6.Certificate.PairSemantics.sound3262_e`, `OAI.MUB6.Certificate.PairSemantics.sound3263_e`, `OAI.MUB6.Certificate.PairSemantics.sound3264_e`, `OAI.MUB6.Certificate.PairSemantics.sound3266_e`, `OAI.MUB6.Certificate.PairSemantics.sound3267_e`, `OAI.MUB6.Certificate.PairSemantics.sound3268_e`, `OAI.MUB6.Certificate.PairSemantics.sound3269_e`, `OAI.MUB6.Certificate.PairSemantics.sound3271_e`, `OAI.MUB6.Certificate.PairSemantics.sound3272_e`, `OAI.MUB6.Certificate.PairSemantics.sound3273_e`, `OAI.MUB6.Certificate.PairSemantics.sound3274_e`, `OAI.MUB6.Certificate.PairSemantics.sound3275_e`, `OAI.MUB6.Certificate.PairSemantics.sound3276_e`, `OAI.MUB6.Certificate.PairSemantics.sound3277_e`, `OAI.MUB6.Certificate.PairSemantics.sound3278_e`, `OAI.MUB6.Certificate.PairSemantics.sound3279_e`, `OAI.MUB6.Certificate.PairSemantics.sound3280_e`, `OAI.MUB6.Certificate.PairSemantics.sound3281_e`, `OAI.MUB6.Certificate.PairSemantics.sound3282_e`, `OAI.MUB6.Certificate.PairSemantics.sound3283_e`, `OAI.MUB6.Certificate.PairSemantics.sound3284_e`, `OAI.MUB6.Certificate.PairSemantics.sound3288_e`, `OAI.MUB6.Certificate.PairSemantics.sound3289_e`, `OAI.MUB6.Certificate.PairSemantics.sound3290_e`, `OAI.MUB6.Certificate.PairSemantics.sound3291_e`, `OAI.MUB6.Certificate.PairSemantics.sound3292_e`, `OAI.MUB6.Certificate.PairSemantics.sound3293_e`, `OAI.MUB6.Certificate.PairSemantics.sound3294_e`, `OAI.MUB6.Certificate.PairSemantics.sound3295_e`, `OAI.MUB6.Certificate.PairSemantics.sound3296_e`, `OAI.MUB6.Certificate.PairSemantics.sound3297_e`, `OAI.MUB6.Certificate.PairSemantics.sound3298_e`, `OAI.MUB6.Certificate.PairSemantics.sound3299_e`, `OAI.MUB6.Certificate.PairSemantics.sound3300_e`, `OAI.MUB6.Certificate.PairSemantics.sound3301_e`, `OAI.MUB6.Certificate.PairSemantics.sound3302_e`, `OAI.MUB6.Certificate.PairSemantics.sound3303_e`, `OAI.MUB6.Certificate.PairSemantics.sound3304_e`, `OAI.MUB6.Certificate.PairSemantics.sound3305_e`, `OAI.MUB6.Certificate.PairSemantics.sound3307_e`, `OAI.MUB6.Certificate.PairSemantics.sound3308_e`, `OAI.MUB6.Certificate.PairSemantics.sound3309_e`, `OAI.MUB6.Certificate.PairSemantics.sound3310_e`, `OAI.MUB6.Certificate.PairSemantics.sound3311_e`, `OAI.MUB6.Certificate.PairSemantics.sound3313_e`, `OAI.MUB6.Certificate.PairSemantics.sound3314_e`, `OAI.MUB6.Certificate.PairSemantics.sound3315_e`, `OAI.MUB6.Certificate.PairSemantics.sound3316_e`, `OAI.MUB6.Certificate.PairSemantics.sound3317_e`, `OAI.MUB6.Certificate.PairSemantics.sound3319_e`, `OAI.MUB6.Certificate.PairSemantics.sound3322_e`, `OAI.MUB6.Certificate.PairSemantics.sound3324_e`, `OAI.MUB6.Certificate.PairSemantics.sound3325_e`, `OAI.MUB6.Certificate.PairSemantics.sound3326_e`, `OAI.MUB6.Certificate.PairSemantics.sound3327_e`, `OAI.MUB6.Certificate.PairSemantics.sound3328_e`, `OAI.MUB6.Certificate.PairSemantics.sound3331_e`, `OAI.MUB6.Certificate.PairSemantics.sound3333_e`, `OAI.MUB6.Certificate.PairSemantics.sound3334_e`, `OAI.MUB6.Certificate.PairSemantics.sound3335_e`, `OAI.MUB6.Certificate.PairSemantics.sound3336_e`, `OAI.MUB6.Certificate.PairSemantics.sound3338_e`, `OAI.MUB6.Certificate.PairSemantics.sound3339_e`, `OAI.MUB6.Certificate.PairSemantics.sound3341_e`, `OAI.MUB6.Certificate.PairSemantics.sound3343_e`, `OAI.MUB6.Certificate.PairSemantics.sound3345_e`, `OAI.MUB6.Certificate.PairSemantics.sound3346_e`, `OAI.MUB6.Certificate.PairSemantics.sound3347_e`, `OAI.MUB6.Certificate.PairSemantics.sound3348_e`, `OAI.MUB6.Certificate.PairSemantics.sound3349_e`, `OAI.MUB6.Certificate.PairSemantics.sound3350_e`, `OAI.MUB6.Certificate.PairSemantics.sound3351_e`, `OAI.MUB6.Certificate.PairSemantics.sound3352_e`, `OAI.MUB6.Certificate.PairSemantics.sound3353_e`, `OAI.MUB6.Certificate.PairSemantics.sound3354_e`, `OAI.MUB6.Certificate.PairSemantics.sound3355_e`, `OAI.MUB6.Certificate.PairSemantics.sound3356_e`, `OAI.MUB6.Certificate.PairSemantics.sound3357_e`, `OAI.MUB6.Certificate.PairSemantics.sound3358_e`, `OAI.MUB6.Certificate.PairSemantics.sound3359_e`, `OAI.MUB6.Certificate.PairSemantics.sound3360_e`, `OAI.MUB6.Certificate.PairSemantics.sound3361_e`, `OAI.MUB6.Certificate.PairSemantics.sound3362_e`, `OAI.MUB6.Certificate.PairSemantics.sound3363_e`, `OAI.MUB6.Certificate.PairSemantics.sound3364_e`, `OAI.MUB6.Certificate.PairSemantics.sound3366_e`, `OAI.MUB6.Certificate.PairSemantics.sound3367_e`, `OAI.MUB6.Certificate.PairSemantics.sound3368_e`, `OAI.MUB6.Certificate.PairSemantics.sound3369_e`, `OAI.MUB6.Certificate.PairSemantics.sound3370_e`, `OAI.MUB6.Certificate.PairSemantics.sound3371_e`, `OAI.MUB6.Certificate.PairSemantics.sound3372_e`, `OAI.MUB6.Certificate.PairSemantics.sound3375_e`, `OAI.MUB6.Certificate.PairSemantics.sound3376_e`, `OAI.MUB6.Certificate.PairSemantics.sound3377_e`, `OAI.MUB6.Certificate.PairSemantics.sound3378_e`, `OAI.MUB6.Certificate.PairSemantics.sound3380_e`, `OAI.MUB6.Certificate.PairSemantics.sound3382_e`, `OAI.MUB6.Certificate.PairSemantics.sound3383_e`, `OAI.MUB6.Certificate.PairSemantics.sound3384_e`, `OAI.MUB6.Certificate.PairSemantics.sound3385_e`, `OAI.MUB6.Certificate.PairSemantics.sound3387_e`, `OAI.MUB6.Certificate.PairSemantics.sound3388_e`, `OAI.MUB6.Certificate.PairSemantics.sound3389_e`, `OAI.MUB6.Certificate.PairSemantics.sound3390_e`, `OAI.MUB6.Certificate.PairSemantics.sound3391_e`, `OAI.MUB6.Certificate.PairSemantics.sound3392_e`, `OAI.MUB6.Certificate.PairSemantics.sound3393_e`, `OAI.MUB6.Certificate.PairSemantics.sound3394_e`, `OAI.MUB6.Certificate.PairSemantics.sound3395_e`, `OAI.MUB6.Certificate.PairSemantics.sound3396_e`, `OAI.MUB6.Certificate.PairSemantics.sound3397_e`, `OAI.MUB6.Certificate.PairSemantics.sound3399_e`, `OAI.MUB6.Certificate.PairSemantics.sound3400_e`, `OAI.MUB6.Certificate.PairSemantics.sound3401_e`, `OAI.MUB6.Certificate.PairSemantics.sound3402_e`, `OAI.MUB6.Certificate.PairSemantics.sound3405_e`, `OAI.MUB6.Certificate.PairSemantics.sound3407_e`, `OAI.MUB6.Certificate.PairSemantics.sound3408_e`, `OAI.MUB6.Certificate.PairSemantics.sound3411_e`, `OAI.MUB6.Certificate.PairSemantics.sound3412_e`, `OAI.MUB6.Certificate.PairSemantics.sound3413_e`, `OAI.MUB6.Certificate.PairSemantics.sound3414_e`, `OAI.MUB6.Certificate.PairSemantics.sound3415_e`, `OAI.MUB6.Certificate.PairSemantics.sound3416_e`, `OAI.MUB6.Certificate.PairSemantics.sound3417_e`, `OAI.MUB6.Certificate.PairSemantics.sound3418_e`, `OAI.MUB6.Certificate.PairSemantics.sound3419_e`, `OAI.MUB6.Certificate.PairSemantics.sound3420_e`, `OAI.MUB6.Certificate.PairSemantics.sound3421_e`, `OAI.MUB6.Certificate.PairSemantics.sound3422_e`, `OAI.MUB6.Certificate.PairSemantics.sound3423_e`, `OAI.MUB6.Certificate.PairSemantics.sound3424_e`, `OAI.MUB6.Certificate.PairSemantics.sound3425_e`, `OAI.MUB6.Certificate.PairSemantics.sound3428_e`, `OAI.MUB6.Certificate.PairSemantics.sound3431_e`, `OAI.MUB6.Certificate.PairSemantics.sound3433_e`, `OAI.MUB6.Certificate.PairSemantics.sound3434_e`, `OAI.MUB6.Certificate.PairSemantics.sound3435_e`, `OAI.MUB6.Certificate.PairSemantics.sound3436_e`, `OAI.MUB6.Certificate.PairSemantics.sound3437_e`, `OAI.MUB6.Certificate.PairSemantics.sound3439_e`, `OAI.MUB6.Certificate.PairSemantics.sound3440_e`, `OAI.MUB6.Certificate.PairSemantics.sound3441_e`, `OAI.MUB6.Certificate.PairSemantics.sound3442_e`, `OAI.MUB6.Certificate.PairSemantics.sound3443_e`, `OAI.MUB6.Certificate.PairSemantics.sound3444_e`, `OAI.MUB6.Certificate.PairSemantics.sound3447_e`, `OAI.MUB6.Certificate.PairSemantics.sound3449_e`, `OAI.MUB6.Certificate.PairSemantics.sound3451_e`, `OAI.MUB6.Certificate.PairSemantics.sound3454_e`, `OAI.MUB6.Certificate.PairSemantics.sound3455_e`, `OAI.MUB6.Certificate.PairSemantics.sound3456_e`, `OAI.MUB6.Certificate.PairSemantics.sound3457_e`, `OAI.MUB6.Certificate.PairSemantics.sound3458_e`, `OAI.MUB6.Certificate.PairSemantics.sound3459_e`, `OAI.MUB6.Certificate.PairSemantics.sound3460_e`, `OAI.MUB6.Certificate.PairSemantics.sound3461_e`, `OAI.MUB6.Certificate.PairSemantics.sound3462_e`, `OAI.MUB6.Certificate.PairSemantics.sound3463_e`, `OAI.MUB6.Certificate.PairSemantics.sound3467_e`, `OAI.MUB6.Certificate.PairSemantics.sound3468_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound0_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound100_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound101_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound102_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound103_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound104_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound105_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound106_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound107_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound108_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound10_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound110_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound111_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound112_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound113_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound114_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound115_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound116_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound117_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound118_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound119_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound120_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound121_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound123_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound124_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound125_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound127_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound128_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound129_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound12_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound130_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound131_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound132_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound133_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound134_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound135_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound136_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound137_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound138_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound139_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound140_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound141_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound142_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound143_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound144_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound145_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound146_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound147_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound148_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound149_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound14_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound150_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound151_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound152_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound153_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound154_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound155_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound156_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound157_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound158_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound159_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound15_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound160_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound161_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound162_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound163_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound164_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound165_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound166_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound167_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound168_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound16_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound170_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound171_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound172_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound174_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound175_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound176_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound177_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound178_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound179_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound17_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound180_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound181_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound182_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound183_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound184_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound185_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound186_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound187_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound188_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound189_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound18_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound191_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound192_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound193_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound194_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound195_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound196_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound197_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound198_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound199_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound19_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound1_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound200_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound203_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound204_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound205_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound206_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound208_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound209_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound20_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound210_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound211_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound212_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound213_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound216_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound217_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound218_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound219_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound21_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound220_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound221_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound222_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound223_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound224_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound225_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound226_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound227_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound228_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound229_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound22_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound230_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound231_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound232_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound233_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound234_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound235_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound236_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound237_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound238_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound239_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound23_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound240_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound241_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound242_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound243_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound244_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound245_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound246_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound247_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound248_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound249_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound24_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound250_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound251_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound252_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound253_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound254_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound26_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound27_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound28_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound29_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound2_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound30_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound31_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound32_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound34_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound35_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound36_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound37_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound38_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound39_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound3_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound40_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound41_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound42_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound43_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound44_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound45_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound46_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound47_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound49_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound4_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound50_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound51_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound52_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound53_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound54_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound55_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound56_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound58_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound59_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound5_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound60_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound61_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound62_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound63_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound64_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound65_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound66_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound67_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound69_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound6_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound70_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound72_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound73_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound74_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound75_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound76_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound77_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound78_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound79_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound7_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound80_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound81_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound82_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound83_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound84_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound85_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound86_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound87_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound88_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound89_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound8_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound90_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound91_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound92_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound93_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound94_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound95_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound96_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound97_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound98_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound99_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound9_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm11_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm12_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm13_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm14_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm16_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm17_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm18_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm19_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm21_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm22_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm23_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm24_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm25_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm26_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm6_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm7_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm8_e` and `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm9_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_SmallPartitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.EqualityPatterns

def blocks2 : Fin 2 → ℕ := ![1, 2]

end MUB6.EqualityPatterns

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]

def raw0step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]

def raw0step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

def raw1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]

def raw10 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]

def raw10step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-2, 1, 1], ![-3, 2, 1]]

def raw10step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]

def raw11 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]

def raw11step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-2, 0, 2], ![-3, 3, 0]]

def raw11step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]

def raw12 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![5, -3, -2]]

def raw12step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 0, 5], ![2, 1, -3], ![3, -1, -2]]

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

def raw101 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]

def raw101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]

def raw101step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw105 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]

def raw105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]

def raw105step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw106 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]

def raw106step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]

def raw107 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]

def raw107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def raw108 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]

def raw108step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, -1, 0], ![1, 3, -4]]

def raw109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def raw109step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]

def raw109step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw110 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]

def raw110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]

def raw110step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw111 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]

def raw111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]

def raw111step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw112 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]

def raw112step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]

def raw112step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3]]

def raw113 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]

def raw113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def raw114 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]

def raw114step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def raw115 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]

def raw115step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]

def raw115step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]

def raw116 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]

def raw116step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

def raw117 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]

def raw117step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]

def raw117step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2]]

def raw118 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]

def raw118step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![3, -1, -2]]

def raw118step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 4, -4], ![1, -2, 1]]

def raw119 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]

def raw119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]

def raw119step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

def raw120 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]

def raw120step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 0, 1], ![-3, 3, 0]]

def raw120step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]

def raw121 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]

def raw121step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]

def raw121step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

def raw122 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![4, -3, -1]]

def raw122step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 2, -3], ![3, -2, -1]]

def raw122step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 4, -4], ![2, -3, 1]]

def raw123 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]

def raw123step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -3, 2], ![1, 3, -4]]

def raw124 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]

def raw124step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -2, 1], ![1, 3, -4]]

def raw125 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![3, 1, -4]]

def raw125step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -4, 3], ![1, 3, -4]]

def raw126 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]

def raw126step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw127 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]

def raw127step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]

def raw127step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1000 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, 1, -3]]

def raw1000step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![-1, -1, 1, 1], ![5, 0, -2, -3]]

def raw1000step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![2, -1, -1, 0], ![1, 1, -1, -1], ![-5, 0, 2, 3]]

def raw1000step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 3, -5], ![1, -1, -1, 1]]

def raw1001 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw1002 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, 0, 0, -2]]

def raw1002step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![-1, -1, 2, 0], ![5, 0, -3, -2]]

def raw1002step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![2, -1, -1, 0], ![1, 1, -2, 0], ![-5, 0, 3, 2]]

def raw1002step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 0, 2], ![0, 2, 3, -5], ![1, 0, -2, 1]]

def raw1003 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 2, -4]]

def raw1003step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![-1, -1, 0, 2], ![5, 0, -1, -4]]

def raw1003step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -4, 5], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw1004 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, -1, 0], ![1, 0, 1, -2], ![1, 1, 1, -3]]

def raw1004step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![-1, -1, 1, 1], ![5, 0, -2, -3]]

def raw1004step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![2, -1, 0, -1], ![1, 1, -1, -1], ![-5, 0, 2, 3]]

def raw1004step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 2, 3, -5], ![1, -1, -1, 1]]

def raw1005 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, -1, 0], ![1, 0, 2, -3], ![1, 1, 0, -2]]

def raw1005step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![-1, -1, 2, 0], ![5, 0, -3, -2]]

def raw1005step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![2, -1, 0, -1], ![1, 1, -2, 0], ![-5, 0, 3, 2]]

def raw1005step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 2, 3, -5], ![1, 0, -2, 1]]

def raw1006 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 2, -3]]

def raw1006step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw1007 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw1007step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, 0, -2]]

def raw1008 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, 1, -3]]

def raw1008step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![-1, 0, 0, 1], ![5, -1, -1, -3]]

def raw1008step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -3, 5], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def raw1009 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw1009step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, 0, -2]]

def raw1010 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def raw1010step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw1011 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, 0, -1], ![0, 1, 2, -3], ![2, 0, -1, -1]]

def raw1011step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![-1, 0, 2, -1], ![5, -1, -3, -1]]

def raw1011step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -3, 5], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw1012 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, 1, -3]]

def raw1012step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![-1, 0, 0, 1], ![5, -1, -1, -3]]

def raw1012step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -3, 5], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw1013 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, 0, -2]]

def raw1013step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, 0, -2]]

def raw1014 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, 0, -1], ![1, 0, 2, -3], ![1, 1, -1, -1]]

def raw1014step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![-1, 0, 2, -1], ![5, -1, -3, -1]]

def raw1014step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -3, 5], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 1, 0, -2]]

def raw1015 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, 0, -1], ![1, 1, -1, -1], ![1, 0, 2, -3]]

def raw1015step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 1, 0], ![-1, 0, -1, 2], ![5, -1, -1, -3]]

def raw1015step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -3, 5], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 1, 0, -2]]

def raw1016 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, 0, -1], ![1, 1, 0, -2], ![1, 0, 1, -2]]

def raw1016step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, 0, -2]]

def raw1017 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, 1, -2], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw1017step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, 0, -2]]

def raw1018 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, 1, -2], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw1018step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw1019 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, 1, -2], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw1019step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![-1, 1, 1, -1], ![5, -2, -2, -1]]

def raw1019step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def raw1020 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw1020step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, 0, -2]]

def raw1021 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, 1, -2], ![1, 1, -1, -1], ![1, 0, 1, -2]]

def raw1021step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, 1, -2], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw1022 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, 2, -3], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw1022step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![-1, 2, 0, -1], ![5, -3, -1, -1]]

def raw1022step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -3, 5], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw1023 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, 2, -3], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw1023step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![-1, 2, 0, -1], ![5, -3, -1, -1]]

def raw1023step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -3, 5], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 1, 0, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical312
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw10000 : Matrix (Fin 2) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1]]

def raw10000step0 : Matrix (Fin 2) (Fin 2) ℤ := ![![1, -1], ![-1, 1]]

def raw10000step1 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

def raw10001 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, -1, 3]]

def raw10001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, -1, 3]]

def raw10001step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw10002 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![-2, -2, 4]]

def raw10002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![-2, -2, 4]]

def raw10002step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw10003 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![-3, 0, 3]]

def raw10003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![-3, 0, 3]]

def raw10003step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw10004 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![-3, -1, 4]]

def raw10004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![-3, -1, 4]]

def raw10004step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw10005 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, -2, 4]]

def raw10005step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, -2, 4]]

def raw10005step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw10006 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![-3, 0, 3]]

def raw10006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![-3, 0, 3]]

def raw10006step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw10007 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![-3, -1, 4]]

def raw10007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![-3, -1, 4]]

def raw10007step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw10008 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![-1, -2, 3]]

def raw10008step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw10009 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![-2, -1, 3]]

def raw10009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, -1, 3]]

def raw10009step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw10010 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![-2, -2, 4]]

def raw10010step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![-2, -2, 4]]

def raw10010step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw10011 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![-3, 0, 3]]

def raw10011step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![-3, 0, 3]]

def raw10011step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw10012 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![-3, -1, 4]]

def raw10012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![-3, -1, 4]]

def raw10012step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw10013 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![-2, -2, 4]]

def raw10013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, -2, 4]]

def raw10013step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw10014 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![-3, 0, 3]]

def raw10014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![-3, 0, 3]]

def raw10014step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw10015 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![-1, -2, 3]]

def raw10015step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical313
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw10016 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![-2, -1, 3]]

def raw10016step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

def raw10017 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![-2, -2, 4]]

def raw10017step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw10018 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1], ![-3, 0, 3]]

def raw10018step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]

def raw10019 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2], ![-3, -1, 4]]

def raw10019step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]

def raw10020 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, -2, 3]]

def raw10020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-1, -2, 3]]

def raw10020step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw10021 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]

def raw10021step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]

def raw10022 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, -2, 4]]

def raw10022step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw10023 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![-2, -3, 5]]

def raw10023step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw10024 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]

def raw10024step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]

def raw10025 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![-3, -1, 4]]

def raw10025step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

def raw10026 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![-3, -2, 5]]

def raw10026step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

def raw10027 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![-2, -2, 4]]

def raw10027step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw10028 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, -3, 5]]

def raw10028step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw10029 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1], ![-3, 0, 3]]

def raw10029step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]

def raw10030 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![-3, -1, 4]]

def raw10030step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]

def raw10031 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2], ![-3, -1, 4]]

def raw10031step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

def raw10032 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![-3, -1, 4]]

def raw10032step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

def raw10033 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-3, -1, 4]]

def raw10033step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw10034 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![-3, -2, 5]]

def raw10034step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw10035 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![-1, 2, -1], ![-2, -1, 3]]

def raw10035step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]

def raw10036 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![-1, 2, -1], ![-2, -1, 3]]

def raw10036step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]

def raw10036step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

def raw10037 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![-1, 2, -1], ![-2, -1, 3]]

def raw10037step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]

def raw10037step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

def raw10038 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-2, -1, 3]]

def raw10038step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw10039 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-1, 2, -1], ![-2, -2, 4]]

def raw10039step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def raw10040 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 0, -1, 3], ![0, -1, 3, -2]]

def raw10040step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw10041 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, -1, 3], ![-1, 0, 3, -2]]

def raw10041step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw10042 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 0, -1, 2], ![-1, -1, 3, -1]]

def raw10042step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![1, 0, 1, -2], ![1, 1, -3, 1]]

def raw10042step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw10043 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1], ![-2, 0, -1, 3], ![0, -1, 3, -2]]

def raw10043step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw10044 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1], ![-1, -1, -1, 3], ![-1, 0, 3, -2]]

def raw10044step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw10045 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1], ![-1, 0, -1, 2], ![-1, -1, 3, -1]]

def raw10045step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw10046 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 0, -1, 3], ![0, -1, 3, -2]]

def raw10046step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw10047 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, -1, 3], ![-1, 0, 3, -2]]

def raw10047step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical314
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw10048 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, 0, -1, 2], ![-1, -1, 3, -1]]

def raw10048step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, 0, 1, -2], ![1, 1, -3, 1]]

def raw10048step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw10049 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, -1, -1, 2], ![-2, 0, 3, -1]]

def raw10049step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw10050 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 0, -2, 4], ![0, -1, 3, -2]]

def raw10050step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 3, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw10051 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 0, -1, 3], ![0, -1, 2, -1]]

def raw10051step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw10052 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 0, 3, -1], ![0, -1, -2, 3]]

def raw10052step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw10053 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, -2, 4], ![-1, 0, 3, -2]]

def raw10053step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 0, 3, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw10054 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, -1, 3], ![-1, 0, 2, -1]]

def raw10054step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![1, 1, 1, -3], ![1, 0, -2, 1]]

def raw10054step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw10055 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, 3, -1], ![-1, 0, -2, 3]]

def raw10055step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw10056 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 0, -2, 3], ![-1, -1, 3, -1]]

def raw10056step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw10057 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 0, -1, 2], ![-1, -1, 2, 0]]

def raw10057step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![1, 0, 1, -2], ![1, 1, -2, 0]]

def raw10057step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw10058 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-1, 0, 2, -1], ![-1, -2, 0, 3]]

def raw10058step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw10059 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -1, 2, -1], ![-2, -1, 0, 3]]

def raw10059step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw10060 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, 0, -1, 2], ![-1, -1, 3, -1]]

def raw10060step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, 0, 1, -2], ![1, 1, -3, 1]]

def raw10060step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw10061 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, -1, -1, 2], ![-2, 0, 3, -1]]

def raw10061step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw10062 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 0, 3, -1], ![0, -1, -2, 3]]

def raw10062step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw10063 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, 3, -1], ![-1, 0, -2, 3]]

def raw10063step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw10064 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-1, 0, 2, -1], ![-1, -2, 0, 3]]

def raw10064step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw10065 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -1, 2, -1], ![-2, -1, 0, 3]]

def raw10065step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw10066 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0], ![-1, 0, -1, 2], ![-1, -1, 3, -1]]

def raw10066step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw10067 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0], ![0, -1, -1, 2], ![-2, 0, 3, -1]]

def raw10067step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw10068 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1], ![-2, 0, 3, -1], ![0, -1, -2, 3]]

def raw10068step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, -1, -2, 3], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw10069 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1], ![-1, -1, 3, -1], ![-1, 0, -2, 3]]

def raw10069step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![-1, 0, -2, 3], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw10070 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -2, 1], ![-1, 0, -1, 2], ![-1, -1, 3, -1]]

def raw10070step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw10071 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -2, 1], ![0, -1, -1, 2], ![-2, 0, 3, -1]]

def raw10071step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw10072 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 0, 3, -1], ![0, -1, -2, 3]]

def raw10072step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw10073 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 3, -1], ![-1, 0, -2, 3]]

def raw10073step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw10074 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, 0, -2, 3], ![-1, -1, 3, -1]]

def raw10074step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw10075 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, 0, -1, 2], ![-1, -1, 2, 0]]

def raw10075step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, 0, 1, -2], ![1, 1, -2, 0]]

def raw10075step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw10076 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, -1, -2, 3], ![-2, 0, 3, -1]]

def raw10076step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw10077 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, -1, -1, 2], ![-2, 0, 2, 0]]

def raw10077step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![0, 1, 1, -2], ![2, 0, -2, 0]]

def raw10077step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw10078 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 0, 2, 0], ![0, -1, -2, 3]]

def raw10078step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw10079 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 0, 3, -1], ![0, -1, -3, 4]]

def raw10079step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, -1, -3, 4], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical315
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw10080 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, 2, 0], ![-1, 0, -2, 3]]

def raw10080step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw10081 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, 3, -1], ![-1, 0, -3, 4]]

def raw10081step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![-1, 0, -3, 4], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw10082 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1], ![-1, 0, 2, -1], ![-1, -2, 0, 3]]

def raw10082step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw10083 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1], ![0, -1, 2, -1], ![-2, -1, 0, 3]]

def raw10083step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def raw10084 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-1, 0, 2, -1], ![-1, -2, 0, 3]]

def raw10084step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw10085 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![0, -1, 2, -1], ![-2, -1, 0, 3]]

def raw10085step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw10086 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-1, 0, 1, 0], ![-1, -2, 0, 3]]

def raw10086step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, -1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw10087 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-1, 0, 2, -1], ![-1, -2, -1, 4]]

def raw10087step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw10088 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -1, 1, 0], ![-2, -1, 0, 3]]

def raw10088step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -2, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0]]

def raw10089 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -1, 2, -1], ![-2, -1, -1, 4]]

def raw10089step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw10090 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 1, -2], ![-4, 1, 1, 2], ![4, -2, -2, 0]]

def raw10090step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![1, 1, -2], ![1, 1, -2], ![-2, 2, 0]]

def raw10090step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![1, -2, 1], ![1, -2, 1]]

def raw10091 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 1, -2], ![-4, 1, 2, 1], ![4, -2, -3, 1]]

def raw10091step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![1, 1, -2], ![1, 2, -3], ![-2, 1, 1]]

def raw10091step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -4, 4], ![1, 1, -2], ![1, 2, -3]]

def raw10092 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 1, -2], ![-3, -2, 3, 2], ![3, 1, -4, 0]]

def raw10092step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 3, -4], ![-2, 2, 0]]

def raw10092step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -4, 3], ![1, 1, -2]]

def raw10093 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 1, -2], ![-3, 1, 1, 1], ![3, -2, -2, 1]]

def raw10093step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![1, 1, -2], ![1, 1, -2], ![-2, 1, 1]]

def raw10093step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]

def raw10094 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 1, -2], ![-3, 1, 2, 0], ![3, -2, -3, 2]]

def raw10094step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![1, 1, -2], ![1, 2, -3], ![-2, 0, 2]]

def raw10094step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 1, -2], ![1, 2, -3]]

def raw10095 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 1, -2], ![-2, -3, 1, 4], ![2, 2, -2, -2]]

def raw10095step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![1, -3, 2], ![1, 1, -2], ![-2, 4, -2]]

def raw10095step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -2, 1], ![1, 2, -3]]

def raw10096 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 1, -2], ![-2, -3, 3, 2], ![2, 2, -4, 0]]

def raw10096step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![1, -3, 2], ![1, 3, -4], ![-2, 2, 0]]

def raw10096step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -4, 3], ![1, 2, -3]]

def raw10097 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 1, -2], ![-2, -2, 1, 3], ![2, 1, -2, -1]]

def raw10097step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 1, -2], ![-2, 3, -1]]

def raw10097step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def raw10098 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 1, -2], ![-2, -2, 2, 2], ![2, 1, -3, 0]]

def raw10098step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 2, -3], ![-2, 2, 0]]

def raw10098step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

def raw10099 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 1, -2], ![-2, -2, 3, 1], ![2, 1, -4, 1]]

def raw10099step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 3, -4], ![-2, 1, 1]]

def raw10099step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -2, 1], ![1, 3, -4]]

def raw10100 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 1, -2], ![-2, 1, 2, -1], ![2, -2, -3, 3]]

def raw10100step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![1, 1, -2], ![1, 2, -3], ![-2, -1, 3]]

def raw10100step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 1, -2], ![1, 2, -3]]

def raw10101 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 1, -2], ![-1, -3, 1, 3], ![1, 2, -2, -1]]

def raw10101step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![1, -3, 2], ![1, 1, -2], ![-2, 3, -1]]

def raw10101step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

def raw10102 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 1, -2], ![-1, -3, 3, 1], ![1, 2, -4, 1]]

def raw10102step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![1, -3, 2], ![1, 3, -4], ![-2, 1, 1]]

def raw10102step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -3, 2], ![1, 3, -4]]

def raw10103 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 1, -2], ![-1, -2, 1, 2], ![1, 1, -2, 0]]

def raw10103step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![-2, 2, 0]]

def raw10103step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw10104 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 1, -2], ![-1, -2, 2, 1], ![1, 1, -3, 1]]

def raw10104step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![1, -2, 1], ![1, 2, -3], ![-2, 1, 1]]

def raw10104step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

def raw10105 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 1, -2], ![-1, -2, 3, 0], ![1, 1, -4, 2]]

def raw10105step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![1, -2, 1], ![1, 3, -4], ![-2, 0, 2]]

def raw10105step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -2, 1], ![1, 3, -4]]

def raw10106 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 1, -2], ![-1, 1, 2, -2], ![1, -2, -3, 4]]

def raw10106step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![1, 1, -2], ![1, 2, -3], ![-2, -2, 4]]

def raw10106step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![1, 1, -2], ![1, 2, -3]]

def raw10107 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 1, -2], ![2, -2, 1, -1], ![-2, 1, -2, 3]]

def raw10107step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, -2, 1], ![1, 1, -2], ![-2, -1, 3]]

def raw10107step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def raw10108 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, -2, 2, -1], ![0, 1, 1, -2], ![-1, 1, -3, 3]]

def raw10108step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-2, 1, 1], ![2, 1, -3], ![-1, -2, 3]]

def raw10108step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

def raw10109 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, -2, 2, -1], ![1, 1, 1, -3], ![-2, 1, -3, 4]]

def raw10109step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 1, 1], ![2, 1, -3], ![-1, -3, 4]]

def raw10109step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical316
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw10113 : Matrix (Fin 6) (Fin 2) ℤ := ![![1, -1], ![1, -1], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]

def raw10113step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw10115 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, -1, 1, -1], ![-5, 2, 1, 2], ![4, -1, -2, -1]]

def raw10115step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![-1, 2, -1], ![1, 1, -2], ![-1, 2, -1]]

def raw10115step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -2, 1], ![-1, -1, 2], ![1, -2, 1]]

def raw10115step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -4, 5], ![-1, 2, -1], ![1, 1, -2], ![1, 1, -2]]

def raw10116 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, -1, 1, -1], ![-4, 2, 1, 1], ![3, -1, -2, 0]]

def raw10116step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 2, -1], ![1, 1, -2], ![-1, 1, 0]]

def raw10116step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -2, 1], ![-1, -1, 2], ![1, -1, 0]]

def raw10116step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2]]

def raw10117 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, -1, 1, -1], ![-4, 3, 1, 0], ![3, -2, -2, 1]]

def raw10117step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 3, -2], ![1, 1, -2], ![-1, 0, 1]]

def raw10117step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -3, 2], ![-1, -1, 2], ![1, 0, -1]]

def raw10117step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 2, -3]]

def raw10118 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, -1, 1, -1], ![-3, -1, 1, 3], ![2, 2, -2, -2]]

def raw10118step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![1, 1, -2], ![-1, 3, -2]]

def raw10118step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 2, -3]]

def raw10119 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, -1, 1, -1], ![-3, -1, 2, 2], ![2, 2, -3, -1]]

def raw10119step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![1, 2, -3], ![-1, 2, -1]]

def raw10119step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 1, -2], ![-1, -2, 3], ![1, -2, 1]]

def raw10119step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![1, -2, 1], ![1, 1, -2]]

def raw10120 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, -1, 1, -1], ![-3, 2, 1, 0], ![2, -1, -2, 1]]

def raw10120step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 2, -1], ![1, 1, -2], ![-1, 0, 1]]

def raw10120step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![1, -2, 1], ![-1, -1, 2], ![1, 0, -1]]

def raw10120step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

def raw10121 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, -1, 1, -1], ![-3, 3, 1, -1], ![2, -2, -2, 2]]

def raw10121step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 3, -2], ![1, 1, -2], ![-1, -1, 2]]

def raw10121step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 2, -3]]

def raw10122 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, -1, 1, -1], ![-2, -2, 2, 2], ![1, 3, -3, -1]]

def raw10122step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -2, 3], ![1, 2, -3], ![-1, 2, -1]]

def raw10122step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 2, -3]]

def raw10123 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, -1, 1, -1], ![-2, -1, 1, 2], ![1, 2, -2, -1]]

def raw10123step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, 1, -2], ![-1, 2, -1]]

def raw10123step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2]]

def raw10124 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, -1, 1, -1], ![-2, -1, 2, 1], ![1, 2, -3, 0]]

def raw10124step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, 2, -3], ![-1, 1, 0]]

def raw10124step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![1, 1, -2], ![-1, -2, 3], ![1, -1, 0]]

def raw10124step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

def raw10125 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, -1, 1, -1], ![-2, -1, 3, 0], ![1, 2, -4, 1]]

def raw10125step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, 3, -4], ![-1, 0, 1]]

def raw10125step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![1, 1, -2], ![-1, -3, 4], ![1, 0, -1]]

def raw10125step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2]]

def raw10126 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, -1, 1, -1], ![-2, 2, 1, -1], ![1, -1, -2, 2]]

def raw10126step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![-1, 2, -1], ![1, 1, -2], ![-1, -1, 2]]

def raw10126step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2]]

def raw10127 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, -1, 1, -1], ![-1, -2, 2, 1], ![0, 3, -3, 0]]

def raw10127step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-1, -2, 3], ![1, 2, -3], ![-1, 1, 0]]

def raw10127step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3]]

def raw10128 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, -1, 1, -1], ![-1, -1, 3, -1], ![0, 2, -4, 2]]

def raw10128step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-1, -1, 2], ![1, 3, -4], ![-1, -1, 2]]

def raw10128step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![1, 1, -2], ![-1, -3, 4], ![1, 1, -2]]

def raw10128step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2]]

def raw10129 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, -1, 1, -1], ![0, -2, 2, 0], ![-1, 3, -3, 1]]

def raw10129step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, -2, 3], ![1, 2, -3], ![-1, 0, 1]]

def raw10129step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![2, 1, -3]]

def raw10130 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, -1, 1, -1], ![0, -1, 1, 0], ![-1, 2, -2, 1]]

def raw10130step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, -1, 2], ![1, 1, -2], ![-1, 0, 1]]

def raw10130step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

def raw10131 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, -1, 1, -1], ![0, -1, 2, -1], ![-1, 2, -3, 2]]

def raw10131step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, -1, 2], ![1, 2, -3], ![-1, -1, 2]]

def raw10131step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 1, -2], ![-1, -2, 3], ![1, 1, -2]]

def raw10131step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]

def raw10132 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, -1, 1, -1], ![1, -2, 2, -1], ![-2, 3, -3, 2]]

def raw10132step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, -2, 3], ![1, 2, -3], ![-1, -1, 2]]

def raw10132step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![1, 1, -2], ![1, 2, -3]]

def raw10133 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, -1, 1, -1], ![1, -1, 1, -1], ![-2, 2, -2, 2]]

def raw10133step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, -1, 2], ![1, 1, -2], ![-1, -1, 2]]

def raw10133step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![1, 1, -2], ![1, 1, -2]]

def raw10134 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, -1, 1, -1], ![1, -1, 2, -2], ![-2, 2, -3, 3]]

def raw10134step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, -1, 2], ![1, 2, -3], ![-1, -2, 3]]

def raw10134step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![1, 1, -2], ![1, 2, -3]]

def raw10135 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, -1, 1, -1], ![2, -1, 1, -2], ![-3, 2, -2, 3]]

def raw10135step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, -1, 2], ![1, 1, -2], ![-1, -2, 3]]

def raw10135step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![1, 1, -2], ![1, 2, -3]]

def raw10136 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, -1, 2, -2], ![0, 2, 0, -2], ![-1, -1, -2, 4]]

def raw10136step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, 2, -1], ![2, 0, -2], ![-2, -2, 4]]

def raw10136step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def raw10137 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, -1, 2, -2], ![1, 2, 0, -3], ![-2, -1, -2, 5]]

def raw10137step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, 0, -2], ![-2, -3, 5]]

def raw10137step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

def raw10138 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -2, 2, 2], ![1, 2, -2, -1]]

def raw10138step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![0, -2, 2], ![0, 2, -2], ![-1, 2, -1]]

def raw10138step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

def raw10139 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, -3, 4, 0], ![0, 3, -4, 1]]

def raw10139step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, -3, 3], ![0, 4, -4], ![-1, 0, 1]]

def raw10139step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 4, -4], ![1, -1, 0]]

def raw10140 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, -2, 2, 1], ![0, 2, -2, 0]]

def raw10140step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, -2, 2], ![0, 2, -2], ![-1, 1, 0]]

def raw10140step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

def raw10141 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, -2, 3, 0], ![0, 2, -3, 1]]

def raw10141step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, -2, 2], ![0, 3, -3], ![-1, 0, 1]]

def raw10141step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0]]

def raw10142 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, -3, 3, 0], ![-1, 3, -3, 1]]

def raw10142step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -3, 3], ![0, 3, -3], ![-1, 0, 1]]

def raw10142step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 3, -3], ![1, 0, -1]]

def raw10143 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, -2, 3, -1], ![-1, 2, -3, 2]]

def raw10143step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -2, 2], ![0, 3, -3], ![-1, -1, 2]]

def raw10143step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical317
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw10144 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, -2, 2, -1], ![-2, 2, -2, 2]]

def raw10144step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, -2, 2], ![0, 2, -2], ![-1, -1, 2]]

def raw10144step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

def raw10145 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![-5, 2, 1, 2], ![4, -2, -2, 0]]

def raw10145step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![0, 2, -2], ![1, 1, -2], ![-2, 2, 0]]

def raw10145step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -2, 1], ![1, 4, -5]]

def raw10146 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![-4, 2, 1, 1], ![3, -2, -2, 1]]

def raw10146step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![0, 2, -2], ![1, 1, -2], ![-2, 1, 1]]

def raw10146step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -2, 1], ![1, 3, -4]]

def raw10147 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![-3, 2, 1, 0], ![2, -2, -2, 2]]

def raw10147step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![0, 2, -2], ![1, 1, -2], ![-2, 0, 2]]

def raw10147step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

def raw10148 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![-3, 4, -2, 1], ![2, -4, 1, 1]]

def raw10148step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![0, 4, -4], ![1, -2, 1], ![-2, 1, 1]]

def raw10148step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -4, 4], ![1, 1, -2], ![1, 2, -3]]

def raw10149 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![-2, -3, 1, 4], ![1, 3, -2, -2]]

def raw10149step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![0, -3, 3], ![1, 1, -2], ![-2, 4, -2]]

def raw10149step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, -2, 1], ![1, 1, -2]]

def raw10150 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![-2, -3, 3, 2], ![1, 3, -4, 0]]

def raw10150step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![0, -3, 3], ![1, 3, -4], ![-2, 2, 0]]

def raw10150step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -4, 3], ![1, 1, -2]]

def raw10151 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![-2, -2, 1, 3], ![1, 2, -2, -1]]

def raw10151step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![0, -2, 2], ![1, 1, -2], ![-2, 3, -1]]

def raw10151step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def raw10152 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![-2, -2, 2, 2], ![1, 2, -3, 0]]

def raw10152step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![0, -2, 2], ![1, 2, -3], ![-2, 2, 0]]

def raw10152step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

def raw10153 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![-2, -2, 3, 1], ![1, 2, -4, 1]]

def raw10153step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![0, -2, 2], ![1, 3, -4], ![-2, 1, 1]]

def raw10153step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -2, 1], ![1, 3, -4]]

def raw10154 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![-2, 2, 1, -1], ![1, -2, -2, 3]]

def raw10154step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![0, 2, -2], ![1, 1, -2], ![-2, -1, 3]]

def raw10154step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def raw10155 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![-2, 3, -2, 1], ![1, -3, 1, 1]]

def raw10155step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![0, 3, -3], ![1, -2, 1], ![-2, 1, 1]]

def raw10155step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]

def raw10156 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![-2, 4, -3, 1], ![1, -4, 2, 1]]

def raw10156step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![0, 4, -4], ![1, -3, 2], ![-2, 1, 1]]

def raw10156step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -4, 4], ![1, 1, -2], ![1, 2, -3]]

def raw10157 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![-2, 4, -2, 0], ![1, -4, 1, 2]]

def raw10157step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![0, 4, -4], ![1, -2, 1], ![-2, 0, 2]]

def raw10157step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![1, -2, 1], ![1, -2, 1]]

def raw10158 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![-1, -3, 1, 3], ![0, 3, -2, -1]]

def raw10158step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, -3, 3], ![1, 1, -2], ![-2, 3, -1]]

def raw10158step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw10159 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![-1, -3, 3, 1], ![0, 3, -4, 1]]

def raw10159step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, -3, 3], ![1, 3, -4], ![-2, 1, 1]]

def raw10159step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, -1, 0], ![1, 3, -4]]

def raw10160 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![-1, -2, 1, 2], ![0, 2, -2, 0]]

def raw10160step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![-2, 2, 0]]

def raw10160step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 2, -2], ![-1, -1, 2], ![2, -2, 0]]

def raw10160step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

def raw10161 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![-1, -2, 2, 1], ![0, 2, -3, 1]]

def raw10161step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, -2, 2], ![1, 2, -3], ![-2, 1, 1]]

def raw10161step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

def raw10162 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![-1, -2, 3, 0], ![0, 2, -4, 2]]

def raw10162step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, -2, 2], ![1, 3, -4], ![-2, 0, 2]]

def raw10162step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

def raw10163 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![-1, 2, 1, -2], ![0, -2, -2, 4]]

def raw10163step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, 2, -2], ![1, 1, -2], ![-2, -2, 4]]

def raw10163step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def raw10164 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![-1, 3, -2, 0], ![0, -3, 1, 2]]

def raw10164step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, 3, -3], ![1, -2, 1], ![-2, 0, 2]]

def raw10164step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

def raw10165 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![-1, 4, -3, 0], ![0, -4, 2, 2]]

def raw10165step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, 4, -4], ![1, -3, 2], ![-2, 0, 2]]

def raw10165step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![1, -3, 2], ![1, -1, 0]]

def raw10166 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, -3, 2, 1], ![-1, 3, -3, 1]]

def raw10166step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -3, 3], ![1, 2, -3], ![-2, 1, 1]]

def raw10166step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 0, -1], ![1, 2, -3]]

def raw10167 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, -2, 2, 0], ![-1, 2, -3, 2]]

def raw10167step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -2, 2], ![1, 2, -3], ![-2, 0, 2]]

def raw10167step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![-1, -2, 3], ![2, 0, -2]]

def raw10167step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

def raw10168 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![1, -3, 1, 1], ![-2, 3, -2, 1]]

def raw10168step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, -3, 3], ![1, 1, -2], ![-2, 1, 1]]

def raw10168step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]

def raw10169 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![1, -3, 2, 0], ![-2, 3, -3, 2]]

def raw10169step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, -3, 3], ![1, 2, -3], ![-2, 0, 2]]

def raw10169step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 1, -2], ![1, 2, -3]]

def raw10170 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![1, -2, 1, 0], ![-2, 2, -2, 2]]

def raw10170step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, -2, 2], ![1, 1, -2], ![-2, 0, 2]]

def raw10170step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]

def raw10171 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![1, -2, 2, -1], ![-2, 2, -3, 3]]

def raw10171step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, -2, 2], ![1, 2, -3], ![-2, -1, 3]]

def raw10171step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 1, -2], ![1, 2, -3]]

def raw10172 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![2, -3, 1, 0], ![-3, 3, -2, 2]]

def raw10172step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, -3, 3], ![1, 1, -2], ![-2, 0, 2]]

def raw10172step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 1, -2], ![1, 2, -3]]

def raw10173 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![2, -2, 1, -1], ![-3, 2, -2, 3]]

def raw10173step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, -2, 2], ![1, 1, -2], ![-2, -1, 3]]

def raw10173step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 1, -2], ![1, 2, -3]]

def raw10174 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 1, 1, -3], ![1, -2, 1, 0], ![-2, 1, -2, 3]]

def raw10174step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -2, 1], ![1, 1, -2], ![-3, 0, 3]]

def raw10174step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]

def raw10175 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 1, 1, -3], ![2, -2, 1, -1], ![-3, 1, -2, 4]]

def raw10175step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -2, 1], ![1, 1, -2], ![-3, -1, 4]]

def raw10175step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical318
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw10176 : Matrix (Fin 3) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-2, -3, 4, 1], ![0, 3, -4, 1]]

def raw10176step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -2, 0], ![0, -3, 3], ![0, 4, -4], ![-2, 1, 1]]

def raw10176step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 3, -3], ![0, -4, 4], ![2, -1, -1]]

def raw10176step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 4, -4], ![2, -1, -1]]

def raw10177 : Matrix (Fin 3) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-2, -2, 3, 1], ![0, 2, -3, 1]]

def raw10177step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![0, 3, -3], ![-2, 1, 1]]

def raw10177step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 2, -2], ![0, -3, 3], ![2, -1, -1]]

def raw10177step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

def raw10178 : Matrix (Fin 3) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, -3, 3, 1], ![-1, 3, -3, 1]]

def raw10178step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, -3, 3], ![0, 3, -3], ![-2, 1, 1]]

def raw10178step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 3, -3], ![2, -1, -1]]

def raw10179 : Matrix (Fin 3) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, -3, 4, 0], ![-1, 3, -4, 2]]

def raw10179step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, -3, 3], ![0, 4, -4], ![-2, 0, 2]]

def raw10179step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 4, -4], ![2, -1, -1]]

def raw10180 : Matrix (Fin 3) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, -2, 3, 0], ![-1, 2, -3, 2]]

def raw10180step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, -2, 2], ![0, 3, -3], ![-2, 0, 2]]

def raw10180step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

def raw10181 : Matrix (Fin 3) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -3, 3, 0], ![-2, 3, -3, 2]]

def raw10181step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -3, 3], ![0, 3, -3], ![-2, 0, 2]]

def raw10181step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 3, -3], ![2, 0, -2]]

def raw10182 : Matrix (Fin 3) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -2, 2, 0], ![-2, 2, -2, 2]]

def raw10182step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -2, 2], ![0, 2, -2], ![-2, 0, 2]]

def raw10182step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![2, 0, -2]]

def raw10183 : Matrix (Fin 3) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -2, 3, -1], ![-2, 2, -3, 3]]

def raw10183step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -2, 2], ![0, 3, -3], ![-2, -1, 3]]

def raw10183step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![2, 0, -2]]

def raw10184 : Matrix (Fin 3) (Fin 4) ℤ := ![![2, 0, 0, -2], ![1, -2, 2, -1], ![-3, 2, -2, 3]]

def raw10184step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![0, 2, -2], ![-2, -1, 3]]

def raw10184step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![2, 1, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1024 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, 2, -3], ![1, 1, -1, -1], ![1, 0, 0, -1]]

def raw1024step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 1, 0], ![-1, 2, -1, 0], ![5, -3, -1, -1]]

def raw1024step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -3, 5], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 1, 0, -2]]

def raw1025 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 2, -3]]

def raw1025step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 2, 0, 0], ![-1, -1, 0, 2], ![5, -1, -1, -3]]

def raw1025step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -3, 5], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw1026 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 2, -1, -1], ![1, 0, 1, -2], ![1, 0, 1, -2]]

def raw1026step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 2, 0, 0], ![-1, -1, 1, 1], ![5, -1, -2, -2]]

def raw1026step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def raw1027 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 2, -3]]

def raw1027step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 2, 0, 0], ![-1, 0, -1, 2], ![5, -2, 0, -3]]

def raw1027step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![2, -2, 0, 0], ![1, 0, 1, -2], ![-5, 2, 0, 3]]

def raw1027step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 0, 2], ![0, 2, 3, -5], ![1, 0, -2, 1]]

def raw1028 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 2, 0, -2], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw1028step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw1029 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 2, 1, -3], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw1029step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 2, 0, 0], ![-1, 1, 0, 0], ![5, -3, -1, -1]]

def raw1029step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -3, 5], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def raw1030 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, 0, -3]]

def raw1030step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, -2, 4], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw1031 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, 1, -1, -2]]

def raw1032 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, 0, 0, -2]]

def raw1033 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw1033step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 2, -3], ![1, 1, -1, -1]]

def raw1034 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, 1, -3]]

def raw1034step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 2, 0, -4], ![0, 0, 1, -1], ![0, -2, 0, 2], ![-2, 0, -1, 3]]

def raw1034step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, 0, 0, -1]]

def raw1035 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, 0, -3]]

def raw1035step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![-2, 0, 0, 1, 1], ![0, 0, 1, -1, 0], ![4, 0, -1, 0, -3]]

def raw1035step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![0, 1, -1, 0], ![4, -1, 0, -3]]

def raw1035step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw1036 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 0, 0], ![0, 1, 1, -2], ![2, 1, -1, -2]]

def raw1036step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![0, 0, 1, -1], ![4, 0, -2, -2]]

def raw1036step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![4, -2, -2]]

def raw1036step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def raw1037 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![2, 1, 0, -3]]

def raw1037step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![-2, 0, 0, 1, 1], ![0, 1, 0, -1, 0], ![4, -1, 0, 0, -3]]

def raw1037step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![0, 1, -1, 0], ![4, -1, 0, -3]]

def raw1037step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw1038 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![2, 1, 0, -3]]

def raw1039 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, -1, -2]]

def raw1040 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def raw1041 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, 0, 0, -2]]

def raw1042 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw1043 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, 0, -2, 0]]

def raw1043step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, 0, 0, -2]]

def raw1044 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, -1, -2]]

def raw1044step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, -1, -2]]

def raw1045 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -2, -1]]

def raw1045step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def raw1046 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def raw1047 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, 0, 1, -3]]

def raw1048 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def raw1049 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 1, 1, -3]]

def raw1050 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 1, -2], ![1, 1, 0, -2]]

def raw1051 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -2, 1], ![2, 1, 1, -4]]

def raw1051step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![0, 1, -2, 1], ![4, -1, 1, -4]]

def raw1051step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -4, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -2, 1, 0]]

def raw1052 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 1, -3]]

def raw1053 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw1053step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 2, 0, -4], ![0, 0, -1, 1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-2, 0, 0, 2]]

def raw1053step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw1054 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw1055 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1056 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw1056step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 2, 0, -4], ![0, 0, -1, 1], ![0, -1, 1, 0], ![-1, 0, 0, 1], ![-1, -1, 0, 2]]

def raw1056step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, -1, 2], ![0, -1, 0, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw1057 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw1058 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, 0, -3]]

def raw1058step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![0, 1, -1, 0], ![4, -1, 0, -3]]

def raw1058step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw1059 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw1059step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 2, 0, -4], ![0, 0, -1, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![-2, 0, 0, 2]]

def raw1059step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw1060 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw1060step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 2, 0, -4], ![0, 0, -1, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-2, 0, 1, 1]]

def raw1060step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw1061 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

def raw1062 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw1062step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 2, 0, -4], ![0, 0, -1, 1], ![0, -1, 0, 1], ![-1, 0, 1, 0], ![-1, -1, 0, 2]]

def raw1062step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, -1, 2], ![0, -1, 0, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw1063 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw1063step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 2, 0, -4], ![0, 0, -1, 1], ![0, -1, 0, 1], ![-1, 0, 0, 1], ![-1, -1, 1, 1]]

def raw1063step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, -1, 1]]

def raw1064 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -2, 0]]

def raw1065 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -1, -2]]

def raw1065step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![0, 1, 0, -1], ![4, -1, -1, -2]]

def raw1065step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw1066 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw1066step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

def raw1067 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, 1, -2, -1]]

def raw1067step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![0, 1, 1, -2], ![4, -1, -2, -1]]

def raw1067step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw1068 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw1068step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

def raw1069 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, 0, 1, -3]]

def raw1069step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 2, 0], ![0, 1, -2, 1], ![4, -1, 0, -3]]

def raw1069step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -2, 1, 0]]

def raw1070 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw1070step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw1071 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw1071step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 2, 0, -4], ![0, 0, -1, 1], ![0, -2, 1, 1], ![-1, 0, 0, 1], ![-1, 0, 0, 1]]

def raw1071step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw1072 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def raw1072step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 2, 0], ![0, 1, -1, 0], ![4, -1, -1, -2]]

def raw1072step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw1073 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw1073step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 2, 0, -4], ![0, 0, -1, 1], ![0, -2, 0, 2], ![-1, 0, 1, 0], ![-1, 0, 0, 1]]

def raw1073step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw1074 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw1074step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 2, 0], ![0, 1, 0, -1], ![4, -1, -2, -1]]

def raw1074step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw1075 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw1075step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 1, -3]]

def raw1076 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, 0, -3]]

def raw1076step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 0, 0, 2], ![0, 1, -1, 0], ![4, -1, 0, -3]]

def raw1076step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw1077 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -1, -2]]

def raw1077step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 0, 0, 2], ![0, 1, 0, -1], ![4, -1, -1, -2]]

def raw1077step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw1078 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![1, 1, -2, 0], ![1, 1, 1, -3]]

def raw1078step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 0, 1, 1], ![0, 1, -2, 1], ![4, -1, 0, -3]]

def raw1078step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -2, 1, 0]]

def raw1079 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def raw1079step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 0, 1, 1], ![0, 1, -1, 0], ![4, -1, -1, -2]]

def raw1079step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw1080 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw1081 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw1082 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, 1, 0, -3]]

def raw1083 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw1084 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw1085 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw1086 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw1087 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, -1, -1], ![1, 0, 0, -1]]

def raw1087step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1088 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, 1, -1, -2]]

def raw1088step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![0, 2, -1, -1], ![4, -2, 0, -2]]

def raw1088step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![2, 0, -1, -1], ![0, -2, 1, 1], ![-4, 2, 0, 2]]

def raw1088step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -2, 1, 0]]

def raw1089 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw1090 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw1090step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw1091 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 1, -2, 0], ![1, 0, 0, -1]]

def raw1091step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw1092 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def raw1092step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![0, 2, 0, -2], ![4, -2, -1, -1]]

def raw1092step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def raw1093 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw1093step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw1094 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![2, 0, 0, -2]]

def raw1095 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw1095step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw1096 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw1097 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw1097step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw1098 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![2, 0, -2, 0]]

def raw1098step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![2, 0, 0, -2]]

def raw1099 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 0, -1, 0], ![1, 2, -1, -2]]

def raw1099step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 0, 0, 2], ![0, 2, -1, -1], ![4, -2, 0, -2]]

def raw1099step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![2, 0, 0, -2], ![0, -2, 1, 1], ![-4, 2, 0, 2]]

def raw1099step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -2, 1, 0]]

def raw1100 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 0, 0, -1], ![1, 2, -2, -1]]

def raw1100step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 0, 0, 2], ![0, 2, 0, -2], ![4, -2, -1, -1]]

def raw1100step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def raw1101 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def raw1102 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def raw1103 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 1, 0, -2], ![1, 1, -2, 0]]

def raw1103step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def raw1104 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, 0, 2, -4]]

def raw1104step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![0, -2, 0, 2], ![4, 1, -1, -4]]

def raw1104step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![2, -1, -1, 0], ![0, 2, 0, -2], ![-4, -1, 1, 4]]

def raw1104step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, -2, 0], ![1, -1, 4, -4]]

def raw1105 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw1106 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 1, -2], ![1, 0, 0, -1]]

def raw1106step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw1107 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, 0, 1, -3]]

def raw1108 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw1109 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![0, 1, 2, -3], ![2, 0, 0, -2]]

def raw1110 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 1, 2, -4]]

def raw1110step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![0, -2, 0, 2], ![4, 1, -1, -4]]

def raw1110step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![2, -1, 0, -1], ![0, 2, 0, -2], ![-4, -1, 1, 4]]

def raw1110step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 2, -2, 0], ![1, -1, 4, -4]]

def raw1111 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![1, 0, 1, -2], ![1, 1, 1, -3]]

def raw1112 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![1, 0, 2, -3], ![1, 1, 0, -2]]

def raw1113 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![1, 1, 1, -3], ![1, 0, 1, -2]]

def raw1113step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![1, 0, 1, -2], ![1, 1, 1, -3]]

def raw1114 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![1, 1, 2, -4], ![1, 0, 0, -1]]

def raw1114step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 1, 0], ![0, -2, 2, 0], ![4, 1, -4, -1]]

def raw1114step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![2, -1, -1, 0], ![0, 2, -2, 0], ![-4, -1, 4, 1]]

def raw1114step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 2, -2, 0], ![1, -1, 4, -4]]

def raw1115 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def raw1116 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 2, -3]]

def raw1117 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2], ![1, 0, 1, -2]]

def raw1118 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 2, -4]]

def raw1118step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![0, -1, -1, 2], ![4, 0, 0, -4]]

def raw1118step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 4, -4], ![1, 1, -2, 0]]

def raw1119 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1120 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw1120step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 2, 0, -4], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 0, 0, 1], ![-1, 0, -1, 2]]

def raw1120step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw1121 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 1, -3]]

def raw1121step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![0, -1, 0, 1], ![4, 0, -1, -3]]

def raw1121step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![2, -1, -1, 0], ![0, 1, 0, -1], ![-4, 0, 1, 3]]

def raw1121step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, 0, 3, -4]]

def raw1122 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw1123 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw1123step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 2, 0, -4], ![0, -1, 1, 0], ![0, -1, -1, 2], ![-1, 0, 0, 1], ![-1, 0, 0, 1]]

def raw1123step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, 0, 0]]

def raw1124 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def raw1124step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 2, 0, -4], ![0, -1, 1, 0], ![0, -1, -1, 2], ![-2, 0, 0, 2]]

def raw1124step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -1, 0, 0]]

def raw1125 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw1125step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 2, -3]]

def raw1126 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, 0, -1, -1]]

def raw1126step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![0, -1, 2, -1], ![4, 0, -3, -1]]

def raw1126step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw1127 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw1127step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def raw1128 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw1128step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![0, -1, -1, 2], ![4, 0, 0, -4]]

def raw1128step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 4, -4], ![0, 1, -2, 1], ![1, 0, -2, 1]]

def raw1129 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 1, -3]]

def raw1129step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![0, -1, 0, 1], ![4, 0, -1, -3]]

def raw1129step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw1130 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![1, 0, 1, -2], ![1, 1, 0, -2]]

def raw1130step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 2, 0, -4], ![0, -1, 1, 0], ![-1, 0, -1, 2], ![-1, -1, 0, 2]]

def raw1130step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw1131 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![1, 0, 2, -3], ![1, 1, -1, -1]]

def raw1131step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![0, -1, 2, -1], ![4, 0, -3, -1]]

def raw1131step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![2, -1, 0, -1], ![0, 1, -2, 1], ![-4, 0, 3, 1]]

def raw1131step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, 1, -2, 0]]

def raw1132 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![1, 1, -2, 0], ![1, 0, 3, -4]]

def raw1132step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 1, 0], ![0, -1, -2, 3], ![4, 0, 0, -4]]

def raw1132step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 4, -4], ![0, 1, -2, 1], ![1, 1, -2, 0]]

def raw1133 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![1, 1, -1, -1], ![1, 0, 2, -3]]

def raw1133step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 1, 0], ![0, -1, -1, 2], ![4, 0, -1, -3]]

def raw1133step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![2, -1, -1, 0], ![0, 1, 1, -2], ![-4, 0, 1, 3]]

def raw1133step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, 1, -2, 0]]

def raw1134 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![1, 1, 0, -2], ![1, 0, 1, -2]]

def raw1134step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 2, 0, -4], ![0, -1, 1, 0], ![-1, -1, 0, 2], ![-1, 0, -1, 2]]

def raw1134step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw1135 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw1135step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 2, 0, -4], ![0, -1, 0, 1], ![0, -1, 1, 0], ![-1, 0, 0, 1], ![-1, 0, -1, 2]]

def raw1135step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw1136 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 0, -1], ![0, 1, -1, 0], ![2, 0, 1, -3]]

def raw1136step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![0, 0, -1, 1], ![4, -1, 0, -3]]

def raw1136step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![2, -1, -1, 0], ![0, 0, 1, -1], ![-4, 1, 0, 3]]

def raw1136step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, 0, 3, -4]]

def raw1137 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw1137step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 2, 0, -4], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 0, 1, 0], ![-1, 0, -1, 2]]

def raw1137step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, 0, 0]]

def raw1138 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw1138step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 2, 0, -4], ![0, -1, 0, 1], ![0, -1, -1, 2], ![-1, 0, 1, 0], ![-1, 0, 0, 1]]

def raw1138step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw1139 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw1139step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![0, 0, 1, -1], ![4, -1, -2, -1]]

def raw1139step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

def raw1140 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw1140step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 2, -3]]

def raw1141 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 0, -1], ![0, 1, 2, -3], ![2, 0, -2, 0]]

def raw1141step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![0, 0, 2, -2], ![4, -1, -3, 0]]

def raw1141step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -2, 2, 0], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw1142 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw1142step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![0, 0, -1, 1], ![4, -1, 0, -3]]

def raw1142step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw1143 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw1143step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![0, 0, 1, -1], ![4, -1, -2, -1]]

def raw1143step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw1144 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 0, -1], ![1, 0, 2, -3], ![1, 1, -2, 0]]

def raw1144step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![0, 0, 2, -2], ![4, -1, -3, 0]]

def raw1144step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![2, -1, 0, -1], ![0, 0, -2, 2], ![-4, 1, 3, 0]]

def raw1144step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 2, -2, 0], ![1, 0, 3, -4]]

def raw1145 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 0, -1], ![1, 1, -2, 0], ![1, 0, 2, -3]]

def raw1145step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 1, 0], ![0, 0, -2, 2], ![4, -1, 0, -3]]

def raw1145step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![2, -1, -1, 0], ![0, 0, 2, -2], ![-4, 1, 0, 3]]

def raw1145step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 2, -2, 0], ![1, 0, 3, -4]]

def raw1146 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 1, -2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw1146step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 2, 0, -4], ![0, -1, -1, 2], ![0, -1, 1, 0], ![-1, 0, 0, 1], ![-1, 0, 0, 1]]

def raw1146step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, 0, 0]]

def raw1147 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 1, -2], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw1147step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 2, 0, -4], ![0, -1, -1, 2], ![0, -1, 1, 0], ![-2, 0, 0, 2]]

def raw1147step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -1, 0, 0]]

def raw1148 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 1, -2], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw1148step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 2, 0, -4], ![0, -1, -1, 2], ![0, -1, 0, 1], ![-1, 0, 1, 0], ![-1, 0, 0, 1]]

def raw1148step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw1149 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 1, -2], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw1149step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![0, 1, 0, -1], ![4, -2, -1, -1]]

def raw1149step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

def raw1150 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![2, 0, -2, 0]]

def raw1150step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![0, 1, 1, -2], ![4, -2, -2, 0]]

def raw1150step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def raw1151 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw1151step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 2, 0, -4], ![0, -1, -1, 2], ![-1, 0, 1, 0], ![-1, -1, 0, 2]]

def raw1151step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1152 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw1152step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![0, 1, 0, -1], ![4, -2, -1, -1]]

def raw1152step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw1153 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 1, -2], ![1, 0, 1, -2], ![1, 1, -2, 0]]

def raw1154 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 1, -2], ![1, 1, -2, 0], ![1, 0, 1, -2]]

def raw1154step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 1, -2], ![1, 0, 1, -2], ![1, 1, -2, 0]]

def raw1155 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 2, -3], ![0, 1, -2, 1], ![2, 0, 0, -2]]

def raw1155step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![0, 1, 2, -3], ![2, 0, 0, -2]]

def raw1156 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 2, -3], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw1156step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![0, 2, 0, -2], ![4, -3, -1, 0]]

def raw1156step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -2, 2, 0], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw1157 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 2, -3], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw1157step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![0, 2, -1, -1], ![4, -3, 0, -1]]

def raw1157step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![2, -1, 0, -1], ![0, -2, 1, 1], ![-4, 3, 0, 1]]

def raw1157step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, 1, -2, 0]]

def raw1158 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 2, -3], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw1158step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![0, 2, 0, -2], ![4, -3, -1, 0]]

def raw1158step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![2, -1, 0, -1], ![0, -2, 0, 2], ![-4, 3, 1, 0]]

def raw1158step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 2, -2, 0], ![1, 0, 3, -4]]

def raw1159 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 2, -2, 0], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def raw1159step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 2, 0, 0], ![0, -2, -1, 3], ![4, 0, 0, -4]]

def raw1159step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 4, -4], ![0, 2, -2, 0], ![1, 0, -2, 1]]

def raw1160 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 2, -3]]

def raw1160step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 2, 0, 0], ![0, -2, 0, 2], ![4, 0, -1, -3]]

def raw1160step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -2, 2, 0], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw1161 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 2, -2, 0], ![1, 0, 1, -2], ![1, 0, 1, -2]]

def raw1161step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 2, 0, 0], ![0, -2, 1, 1], ![4, 0, -2, -2]]

def raw1161step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def raw1162 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 2, -3]]

def raw1162step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 2, 0, 0], ![0, -1, -1, 2], ![4, -1, 0, -3]]

def raw1162step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw1163 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw1163step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 2, 0, 0], ![0, -1, 0, 1], ![4, -1, -1, -2]]

def raw1163step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

def raw1164 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw1164step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 2, 0, -4], ![0, -2, 0, 2], ![-1, 0, 1, 0], ![-1, 0, -1, 2]]

def raw1164step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -1, 0, 0]]

def raw1165 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw1165step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 2, 0, 0], ![0, 1, -1, 0], ![4, -3, 0, -1]]

def raw1165step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![2, -2, 0, 0], ![0, -1, 1, 0], ![-4, 3, 0, 1]]

def raw1165step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, 0, 3, -4]]

def raw1166 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![1, 0, 2, -3], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def raw1166step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![1, 0, 2, -3], ![1, 1, 0, -2]]

def raw1167 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![1, 1, -2, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw1167step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 1, -2], ![1, 0, 1, -2], ![1, 1, -2, 0]]

def raw1168 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![1, 1, -2, 0], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def raw1168step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![-2, 1, 1, 0], ![0, -2, 2, 0], ![4, 0, -3, -1]]

def raw1168step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![2, -1, -1, 0], ![0, 2, -2, 0], ![-4, 0, 3, 1]]

def raw1168step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 2, -2, 0], ![1, 0, 3, -4]]

def raw1169 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, 0, -3]]

def raw1170 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, 1, -3]]

def raw1171 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def raw1172 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -2, 2], ![0, 1, 0, -1], ![2, 1, 1, -4]]

def raw1172step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![1, -2, 0, 1], ![3, 2, -1, -4]]

def raw1172step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![2, 0, -1, -1], ![-1, 2, 0, -1], ![-3, -2, 1, 4]]

def raw1172step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 2, -1, -1], ![1, -2, 4, -3]]

def raw1173 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -2, 2], ![0, 1, 1, -2], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw1173step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def raw1174 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, 1, 0, -3]]

def raw1175 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, 0, 1, -3]]

def raw1176 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -2, 2], ![0, 2, 1, -3], ![2, 0, 0, -2]]

def raw1176step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, 0, 1, -3]]

def raw1177 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![2, 0, 0, -2]]

def raw1177step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, 1, -3]]

def raw1178 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![2, 1, 0, -3]]

def raw1178step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![-2, 0, 0, 1, 1], ![1, -1, 0, 0, 0], ![3, 1, 0, -1, -3]]

def raw1178step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, 0, -2], ![2, 0, 0, -1, -1], ![-1, 1, 0, 0, 0], ![-3, -1, 0, 1, 3]]

def raw1178step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![2, 0, -1, -1], ![-1, 1, 0, 0], ![-3, -1, 1, 3]]

def raw1178step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 3, -3]]

def raw1179 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, 0, -3]]

def raw1180 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -1, -2]]

def raw1181 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 2, -4]]

def raw1182 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def raw1183 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1184 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 1, -3]]

def raw1185 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw1185step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -2, -2, 3]]

def raw1186 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw1187 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw1187step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 1, -3]]

def raw1188 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw1189 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 1, 0, -1], ![2, 1, 0, -3]]

def raw1189step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![1, -1, 0, 0], ![3, 1, -1, -3]]

def raw1189step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![2, 0, -1, -1], ![-1, 1, 0, 0], ![-3, -1, 1, 3]]

def raw1189step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 3, -3]]

def raw1190 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw1190step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw1191 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 1, 1, -2], ![2, 1, -1, -2]]

def raw1191step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![1, -1, 1, -1], ![3, 1, -2, -2]]

def raw1191step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -2, -2, 3]]

def raw1192 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw1192step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw1193 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 2, -1, -1], ![2, 0, 1, -3]]

def raw1193step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 2, 0], ![1, -1, -1, 1], ![3, 1, -1, -3]]

def raw1193step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -3, 3]]

def raw1194 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw1194step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def raw1195 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, 0, -2]]

def raw1195step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -2, -2, 3]]

def raw1196 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw1196step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 1, -3]]

def raw1197 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 2, 1, -3], ![2, 0, -1, -1]]

def raw1197step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 2, 0], ![1, -1, 1, -1], ![3, 1, -3, -1]]

def raw1197step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -3, 3]]

def raw1198 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw1198step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 2, -4]]

def raw1199 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def raw1199step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 0, 1, 1], ![1, -1, -1, 1], ![3, 1, -1, -3]]

def raw1199step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -1, -3, 3]]

def raw1200 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 0, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw1200step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![-2, 0, 1, 1, 0], ![1, 0, -1, 0, 0], ![3, 0, 0, -1, -2]]

def raw1200step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, 0, -2], ![2, 0, -1, -1, 0], ![-1, 0, 1, 0, 0], ![-3, 0, 0, 1, 2]]

def raw1200step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![2, -1, -1, 0], ![-1, 1, 0, 0], ![-3, 0, 1, 2]]

def raw1200step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def raw1201 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 0, 0], ![0, 1, -1, 0], ![2, 1, 0, -3]]

def raw1201step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![1, 0, -1, 0], ![3, 0, 0, -3]]

def raw1201step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![2, 0, -1, -1], ![-1, 0, 1, 0], ![-3, 0, 0, 3]]

def raw1201step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-3, 0, 3]]

def raw1201step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

def raw1202 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 0, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw1202step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![-2, 0, 1, 1, 0], ![1, 0, 0, 0, -1], ![3, 0, -1, -1, -1]]

def raw1202step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![1, 0, 0, -1], ![3, -1, -1, -1]]

def raw1202step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def raw1203 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 0, 0], ![0, 1, 0, -1], ![2, 1, -1, -2]]

def raw1203step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![1, 0, 0, -1], ![3, 0, -1, -2]]

def raw1203step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![3, -1, -2]]

def raw1203step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2]]

def raw1204 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw1205 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw1206 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![2, 1, 0, -3]]

def raw1206step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![1, 1, -2, 0], ![3, -1, 1, -3]]

def raw1206step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -2, 0, 1]]

def raw1207 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw1208 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw1209 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw1210 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw1211 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, -1, -2]]

def raw1211step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![1, 1, -1, -1], ![3, -1, 0, -2]]

def raw1211step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, -1, 1]]

def raw1212 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![2, 0, -1, -1]]

def raw1212step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw1213 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw1214 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw1214step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw1215 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1216 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def raw1216step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![1, 1, 0, -2], ![3, -1, -1, -1]]

def raw1216step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 1, -2]]

def raw1217 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw1217step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw1218 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, 0, 0, -2]]

def raw1218step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 2, 0], ![1, 1, -2, 0], ![3, -1, 0, -2]]

def raw1218step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw1219 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw1219step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw1220 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw1220step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 2, 0], ![1, 1, -1, -1], ![3, -1, -1, -1]]

def raw1220step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw1221 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw1221step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw1222 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, 0, -2, 0]]

def raw1222step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 2, 0], ![1, 1, 0, -2], ![3, -1, -2, 0]]

def raw1222step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw1223 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, -1, -2]]

def raw1223step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 0, 0, 2], ![1, 1, -1, -1], ![3, -1, 0, -2]]

def raw1223step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, -1, 1]]

def raw1224 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -2, -1]]

def raw1224step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 0, 0, 2], ![1, 1, 0, -2], ![3, -1, -1, -1]]

def raw1224step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 1, -2]]

def raw1225 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def raw1225step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 0, 1, 1], ![1, 1, -2, 0], ![3, -1, 0, -2]]

def raw1225step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, 0, -2, 1]]

def raw1226 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, 1, -2, -1]]

def raw1226step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![1, 2, -1, -2], ![3, -2, 0, -1]]

def raw1226step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![2, 0, -1, -1], ![-1, -2, 1, 2], ![-3, 2, 0, 1]]

def raw1226step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -2, 2, -1]]

def raw1227 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![2, 0, -1, -1]]

def raw1227step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 2, 0], ![1, 2, -2, -1], ![3, -2, 0, -1]]

def raw1227step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![2, -1, -2, 1]]

def raw1228 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, 0, 2, -4]]

def raw1228step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![1, -2, -1, 2], ![3, 1, 0, -4]]

def raw1228step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, 1, -2, 0]]

def raw1229 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw1230 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 0, 0, -1]]

def raw1230step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw1231 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, 0, 1, -3]]

def raw1231step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![1, -2, 0, 1], ![3, 1, -1, -3]]

def raw1231step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![2, -1, -1, 0], ![-1, 2, 0, -1], ![-3, -1, 1, 3]]

def raw1231step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, -1, -1], ![1, -1, 3, -3]]

def raw1232 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw1233 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def raw1234 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -2, 1], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw1234step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![1, -2, -1, 2], ![3, 1, 0, -4]]

def raw1234step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, 0, -2, 1]]

def raw1235 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 1, 1, -3]]

def raw1235step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![1, -2, 0, 1], ![3, 1, -1, -3]]

def raw1235step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![2, -1, 0, -1], ![-1, 2, 0, -1], ![-3, -1, 1, 3]]

def raw1235step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 2, -1, -1], ![1, -1, 3, -3]]

def raw1236 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -2, 1], ![1, 0, 1, -2], ![1, 1, 0, -2]]

def raw1237 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -2, 1], ![1, 1, 0, -2], ![1, 0, 1, -2]]

def raw1237step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -2, 1], ![1, 0, 1, -2], ![1, 1, 0, -2]]

def raw1238 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -2, 1], ![1, 1, 1, -3], ![1, 0, 0, -1]]

def raw1238step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 1, 0], ![1, -2, 1, 0], ![3, 1, -3, -1]]

def raw1238step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![2, -1, -1, 0], ![-1, 2, -1, 0], ![-3, -1, 3, 1]]

def raw1238step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 2, -1, -1], ![1, -1, 3, -3]]

def raw1239 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, -2, 1], ![2, 0, 2, -4]]

def raw1239step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![1, -1, -2, 2], ![3, 0, 1, -4]]

def raw1239step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, 1, -2, 0]]

def raw1240 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw1241 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2], ![1, 0, 0, -1]]

def raw1241step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw1242 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 1, -3]]

def raw1242step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![1, -1, -1, 1], ![3, 0, 0, -3]]

def raw1242step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![2, -1, -1, 0], ![-1, 1, 1, -1], ![-3, 0, 0, 3]]

def raw1242step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, 1, -1, -1]]

def raw1243 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw1244 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw1244step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

def raw1245 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw1245step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![1, -1, 0, 0], ![3, 0, -1, -2]]

def raw1245step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![2, -1, -1, 0], ![-1, 1, 0, 0], ![-3, 0, 1, 2]]

def raw1245step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def raw1246 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw1246step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw1247 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 0, -1, 0]]

def raw1247step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1248 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw1248step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![1, -1, 1, -1], ![3, 0, -2, -1]]

def raw1248step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![2, -1, -1, 0], ![-1, 1, -1, 1], ![-3, 0, 2, 1]]

def raw1248step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -1, 1, -1]]

def raw1249 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -1, 0], ![1, 0, -2, 1], ![1, 1, 2, -4]]

def raw1249step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![1, -1, -2, 2], ![3, 0, 1, -4]]

def raw1249step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, 0, -2, 1]]

def raw1250 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw1250step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![1, -1, -1, 1], ![3, 0, 0, -3]]

def raw1250step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -3, 3], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw1251 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw1251step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![1, -1, 0, 0], ![3, 0, -1, -2]]

def raw1251step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw1252 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -1, 0], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw1252step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![1, -1, 1, -1], ![3, 0, -2, -1]]

def raw1252step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![2, -1, 0, -1], ![-1, 1, -1, 1], ![-3, 0, 2, 1]]

def raw1252step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, 1, -1, -1]]

def raw1253 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -1, 0], ![1, 1, -1, -1], ![1, 0, 1, -2]]

def raw1253step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 1, 0], ![1, -1, -1, 1], ![3, 0, -1, -2]]

def raw1253step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![2, -1, -1, 0], ![-1, 1, 1, -1], ![-3, 0, 1, 2]]

def raw1253step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, 1, -1, -1]]

def raw1254 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw1254step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

def raw1255 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, 0, -1], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw1255step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![1, 0, -1, 0], ![3, -1, 0, -2]]

def raw1255step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![2, -1, -1, 0], ![-1, 0, 1, 0], ![-3, 1, 0, 2]]

def raw1255step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def raw1256 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw1256step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

def raw1257 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw1257step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![1, 0, 0, -1], ![3, -1, -1, -1]]

def raw1257step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def raw1258 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw1258step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw1259 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

def raw1259step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![1, 0, 1, -2], ![3, -1, -2, 0]]

def raw1259step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def raw1260 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw1260step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![1, 0, -1, 0], ![3, -1, 0, -2]]

def raw1260step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw1261 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw1261step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![1, 0, 0, -1], ![3, -1, -1, -1]]

def raw1261step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw1262 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -2, 0]]

def raw1262step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![1, 0, 1, -2], ![3, -1, -2, 0]]

def raw1262step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw1263 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, 0, -1], ![1, 1, -2, 0], ![1, 0, 1, -2]]

def raw1263step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 1, 0], ![1, 0, -2, 1], ![3, -1, 0, -2]]

def raw1263step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw1264 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, 1, -2], ![0, 1, -1, 0], ![2, 0, -1, -1]]

def raw1264step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![1, 1, -1, -1], ![3, -2, 0, -1]]

def raw1264step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![2, -1, -1, 0], ![-1, -1, 1, 1], ![-3, 2, 0, 1]]

def raw1264step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -1, 1, -1]]

def raw1265 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, 1, -2], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw1265step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![1, 1, 0, -2], ![3, -2, -1, 0]]

def raw1265step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def raw1266 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw1266step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![1, 1, -1, -1], ![3, -2, 0, -1]]

def raw1266step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![2, -1, 0, -1], ![-1, -1, 1, 1], ![-3, 2, 0, 1]]

def raw1266step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, 1, -1, -1]]

def raw1267 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw1267step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![1, 1, 0, -2], ![3, -2, -1, 0]]

def raw1267step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw1268 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw1268step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 2, 0, 0], ![1, -2, 0, 1], ![3, 0, -1, -2]]

def raw1268step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def raw1269 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw1269step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 2, 0, 0], ![1, -1, -1, 1], ![3, -1, 0, -2]]

def raw1269step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![2, -2, 0, 0], ![-1, 1, 1, -1], ![-3, 1, 0, 2]]

def raw1269step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -1, 1, -1]]

def raw1270 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw1270step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 2, 0, 0], ![1, 1, -1, -1], ![3, -3, 0, 0]]

def raw1270step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![2, -2, 0, 0], ![-1, -1, 1, 1], ![-3, 3, 0, 0]]

def raw1270step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, 1, -1, -1]]

def raw1271 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![1, 1, -2, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw1271step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![-2, 1, 1, 0], ![1, -2, 1, 0], ![3, 0, -2, -1]]

def raw1271step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw1272 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![-1, 1, 2, -2], ![3, 1, -4, 0]]

def raw1272step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![2, 2, -4], ![2, -2, 0]]

def raw1272step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-2, -2, 4], ![-2, 2, 0]]

def raw1272step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 2, -3], ![2, -2, 0]]

def raw1273 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![-1, 2, 1, -2], ![3, 0, -3, 0]]

def raw1273step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, 1, -3], ![2, -2, 0]]

def raw1273step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]

def raw1274 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw1275 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw1276 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw1277 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 1, 0, -2], ![1, 0, 0, -1]]

def raw1277step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw1278 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![2, 1, 0, -3]]

def raw1278step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![2, -2, 0, 0], ![2, 2, -1, -3]]

def raw1278step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![2, 0, -1, -1], ![-2, 2, 0, 0], ![-2, -2, 1, 3]]

def raw1278step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -2, 3, -2]]

def raw1279 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw1279step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

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

def raw128 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]

def raw128step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]

def raw128step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2]]

def raw129 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]

def raw129step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -2, 1], ![1, 3, -4]]

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

def raw1280 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, 1, -1, -2]]

def raw1281 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw1281step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw1282 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, 0, 0, -2]]

def raw1283 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![2, 0, -1, -1]]

def raw1283step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 2, -1, -1], ![2, 0, 1, -3]]

def raw1284 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![1, 0, 0, -1], ![1, 2, 0, -3]]

def raw1284step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 0, 0, 2], ![2, -2, 0, 0], ![2, 2, -1, -3]]

def raw1284step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![2, 0, 0, -2], ![-2, 2, 0, 0], ![-2, -2, 1, 3]]

def raw1284step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -2, 3, -2]]

def raw1285 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![1, 1, 0, -2], ![1, 1, 0, -2]]

def raw1286 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, 0, -2]]

def raw1287 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw1288 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw1289 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw1290 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw1290step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw1291 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw1291step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw1292 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def raw1292step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 2, 0], ![2, -1, -1, 0], ![2, 1, -1, -2]]

def raw1292step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw1293 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw1293step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw1294 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw1294step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 2, 0], ![2, -1, 0, -1], ![2, 1, -2, -1]]

def raw1294step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw1295 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def raw1295step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 0, 1, 1], ![2, -1, -1, 0], ![2, 1, -1, -2]]

def raw1295step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -1, -2, 2]]

def raw1296 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, 0, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw1296step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![-2, 0, 1, 1, 0], ![2, 0, -1, -1, 0], ![2, 0, 0, 0, -2]]

def raw1296step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![2, -1, -1, 0], ![2, 0, 0, -2]]

def raw1296step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def raw1297 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, 0, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw1297step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![-2, 0, 1, 1, 0], ![2, 0, -1, 0, -1], ![2, 0, 0, -1, -1]]

def raw1297step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, 0, -2], ![2, 0, -1, -1, 0], ![-2, 0, 1, 0, 1], ![-2, 0, 0, 1, 1]]

def raw1297step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![2, -1, -1, 0], ![-2, 1, 0, 1], ![-2, 0, 1, 1]]

def raw1297step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw1298 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw1298step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

def raw1299 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw1299step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, -1, -1]]

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

def pivotPermutation5 : Equiv.Perm (Fin 2) where
  toFun := ![0, 1]
  invFun := ![0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation6 : Equiv.Perm (Fin 3) where
  toFun := ![1, 0, 2]
  invFun := ![1, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation8 : Equiv.Perm (Fin 3) where
  toFun := ![1, 0, 2]
  invFun := ![1, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation14 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation15 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation16 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation24 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation25 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation26 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation46 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation47 : Equiv.Perm (Fin 3) where
  toFun := ![1, 0, 2]
  invFun := ![1, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation48 : Equiv.Perm (Fin 3) where
  toFun := ![0, 1, 2]
  invFun := ![0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation49 : Equiv.Perm (Fin 3) where
  toFun := ![0, 1, 2]
  invFun := ![0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation50 : Equiv.Perm (Fin 3) where
  toFun := ![2, 0, 1]
  invFun := ![1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation51 : Equiv.Perm (Fin 3) where
  toFun := ![1, 0, 2]
  invFun := ![1, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation52 : Equiv.Perm (Fin 3) where
  toFun := ![0, 1, 2]
  invFun := ![0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation53 : Equiv.Perm (Fin 3) where
  toFun := ![2, 0, 1]
  invFun := ![1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation54 : Equiv.Perm (Fin 3) where
  toFun := ![2, 0, 1]
  invFun := ![1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation55 : Equiv.Perm (Fin 3) where
  toFun := ![0, 1, 2]
  invFun := ![0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation56 : Equiv.Perm (Fin 3) where
  toFun := ![1, 0, 2]
  invFun := ![1, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation57 : Equiv.Perm (Fin 3) where
  toFun := ![2, 0, 1]
  invFun := ![1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation58 : Equiv.Perm (Fin 3) where
  toFun := ![2, 0, 1]
  invFun := ![1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation59 : Equiv.Perm (Fin 3) where
  toFun := ![0, 1, 2]
  invFun := ![0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation60 : Equiv.Perm (Fin 3) where
  toFun := ![0, 1, 2]
  invFun := ![0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation61 : Equiv.Perm (Fin 3) where
  toFun := ![1, 0, 2]
  invFun := ![1, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation62 : Equiv.Perm (Fin 3) where
  toFun := ![2, 0, 1]
  invFun := ![1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation63 : Equiv.Perm (Fin 3) where
  toFun := ![0, 1, 2]
  invFun := ![0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

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

def pivotPermutation64 : Equiv.Perm (Fin 3) where
  toFun := ![0, 1, 2]
  invFun := ![0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation65 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation66 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation67 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation68 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation69 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation70 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation71 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation72 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation73 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation75 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation76 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation77 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation78 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation79 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation80 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation81 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation82 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation83 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation87 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation88 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation90 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation92 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation93 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation94 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation95 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

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

def pivotPermutation133 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation137 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation138 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation139 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation140 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation141 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation142 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation143 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation144 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation145 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation146 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation147 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation148 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation149 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation150 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation153 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation155 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation156 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation157 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation158 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation165 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation166 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation168 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation169 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation170 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation171 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation172 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation173 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation174 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation175 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation176 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation177 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation178 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation179 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation180 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation181 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation185 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation187 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation188 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation189 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation190 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

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

def pivotPermutation194 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation195 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation201 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation203 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation204 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation205 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation206 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation207 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation208 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation209 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation210 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation214 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation215 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation216 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation217 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation221 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation222 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation226 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation227 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation228 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation229 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation230 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation231 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation232 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation233 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation235 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation236 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation237 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation238 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation239 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation240 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation241 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation242 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation243 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation244 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation245 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation246 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation247 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation248 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation249 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation250 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation251 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation252 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation253 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation254 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation255 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

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

def pivotPermutation256 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation257 : Equiv.Perm (Fin 3) where
  toFun := ![0, 1, 2]
  invFun := ![0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation259 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation261 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation263 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation264 : Equiv.Perm (Fin 3) where
  toFun := ![0, 1, 2]
  invFun := ![0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation265 : Equiv.Perm (Fin 3) where
  toFun := ![0, 1, 2]
  invFun := ![0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation266 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation267 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation268 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation269 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation270 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation271 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation272 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation273 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation274 : Equiv.Perm (Fin 3) where
  toFun := ![0, 1, 2]
  invFun := ![0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation277 : Equiv.Perm (Fin 3) where
  toFun := ![0, 1, 2]
  invFun := ![0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation278 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation279 : Equiv.Perm (Fin 3) where
  toFun := ![0, 1, 2]
  invFun := ![0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation280 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation281 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation282 : Equiv.Perm (Fin 3) where
  toFun := ![0, 1, 2]
  invFun := ![0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation283 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation284 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation285 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation286 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation287 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation288 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation289 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation290 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation291 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation292 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation293 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation294 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation295 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation296 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation297 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation298 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation299 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation300 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation301 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation302 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation303 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation304 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation305 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation306 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation307 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation308 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation309 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation310 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation311 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation312 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation313 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation314 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation315 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation316 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation317 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation318 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation319 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
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

def pivotPermutation640 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation641 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation642 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation644 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation645 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation646 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation647 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation648 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation649 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation650 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation651 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation652 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation653 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation654 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation655 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation656 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation657 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation658 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation659 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation660 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation661 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation662 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation663 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation664 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation665 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation666 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation667 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation668 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation669 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation670 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation671 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation672 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation694 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation695 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation696 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation697 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation698 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation699 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation700 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation701 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation702 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

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

def pivotPermutation704 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation705 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation706 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation707 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation708 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation709 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation710 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation711 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation715 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation716 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation717 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation721 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation722 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation723 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation724 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation725 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation726 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation727 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation728 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation729 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation730 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation731 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation732 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation733 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation734 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation735 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation736 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation737 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation738 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation739 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation740 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation741 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation742 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation743 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation744 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation745 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation746 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation747 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation748 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation749 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation750 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation751 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation752 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation753 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation754 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation755 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation756 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation757 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation758 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation759 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation760 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation761 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation762 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation763 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation764 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation765 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation766 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation767 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

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

def pivotPermutation768 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation769 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation770 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation771 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation772 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation773 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation774 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation775 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation776 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation777 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation778 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation779 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation780 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation781 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation782 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation783 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation784 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation785 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation786 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation787 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation788 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation789 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation790 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation791 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation792 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation793 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation794 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation795 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation796 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation797 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation798 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation799 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation800 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation801 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation802 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation803 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation804 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation805 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation806 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation807 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation808 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation809 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation810 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation811 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation812 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation813 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation814 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation815 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation816 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation817 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation818 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation819 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation820 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation821 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation822 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation823 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation824 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation825 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation826 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation827 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation828 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation829 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation830 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation831 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

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

def pivotPermutation832 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation833 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation834 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation835 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation836 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation837 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation838 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation839 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation840 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation841 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation842 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation843 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation844 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation845 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation846 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation847 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation848 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation849 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation850 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation851 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation852 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation853 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation854 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation855 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation856 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation857 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation858 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation859 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation860 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation861 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation862 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation863 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation864 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation865 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation866 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation867 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation868 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation869 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation870 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation871 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation872 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation873 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation874 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation875 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation876 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation877 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation878 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation879 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation880 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation881 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation882 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation883 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation884 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation885 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation886 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation887 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation888 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation889 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation890 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation892 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation893 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation894 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation895 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

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

def pivotPermutation896 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation897 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation898 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation899 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation900 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation901 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation902 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation903 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation904 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation905 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation906 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation907 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation908 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation909 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation910 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation911 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation912 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation913 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation914 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation915 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation916 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation917 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation918 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation919 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation920 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation921 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation922 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation923 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation927 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation928 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation929 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation930 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation931 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation932 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation933 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation934 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation935 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation936 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation937 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation938 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation939 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation940 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation941 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation942 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation943 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation944 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation945 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation946 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation947 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation948 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation949 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation950 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation951 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation952 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation953 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation954 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation955 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation956 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation957 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation958 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation959 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

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

def pivotPermutation960 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation961 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation962 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation963 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation964 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation965 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation966 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation967 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation968 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation969 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation970 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation971 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation972 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation973 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation974 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation975 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation976 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation977 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation978 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation979 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation980 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation981 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation982 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation983 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation984 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation985 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation986 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation987 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation988 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation989 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation990 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation991 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation992 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation993 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation994 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation995 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation996 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation997 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation998 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation999 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

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

def pivotPermutation1325 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1326 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1327 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1328 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1329 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1331 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1332 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1333 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1334 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1335 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1336 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1337 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1338 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1339 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1340 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1341 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1342 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1343 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
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

def pivotPermutation320 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation321 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation322 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation323 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation324 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation325 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation326 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation327 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation328 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation330 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation331 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation332 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation333 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation334 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation335 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation336 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation337 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation338 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation339 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation340 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation341 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation342 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation343 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation344 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation345 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation346 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation347 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation348 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation349 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation350 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation351 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation352 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation353 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation354 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation355 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation356 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation357 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation358 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation359 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation360 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation361 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation362 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation363 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation364 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation365 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation366 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation367 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation368 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation369 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation370 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation371 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation372 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation373 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation374 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation375 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation376 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation377 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation378 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation379 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation380 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation381 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation382 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation383 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

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

def pivotPermutation384 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation385 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation386 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation387 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation388 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation389 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation390 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation414 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation415 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation416 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation417 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation418 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation419 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation420 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation421 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation422 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation423 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation424 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation425 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation426 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation427 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation428 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation429 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation430 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation431 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation432 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation433 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation434 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation435 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation436 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation437 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation438 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation439 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation440 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation441 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation442 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation443 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation444 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation445 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation446 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

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

def pivotPermutation524 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation525 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation527 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation528 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation529 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation530 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation531 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation532 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation533 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation535 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation536 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation537 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation538 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation539 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation540 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation541 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation542 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation543 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation544 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation545 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation546 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation547 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation548 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation549 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation550 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation551 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation552 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation553 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation554 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation555 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation556 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation558 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation559 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation560 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation561 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation562 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation563 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation564 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation565 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation566 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation567 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation568 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation569 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation570 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation571 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation572 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation573 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation574 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation575 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

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

def pivotPermutation623 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation624 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation626 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation627 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation628 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation629 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation630 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation631 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation632 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation633 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation634 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation635 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation636 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation637 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation638 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation639 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

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

def pivotPermutation1344 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1345 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1346 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1347 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1348 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1349 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1350 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1351 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1352 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1353 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1354 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1355 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1356 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1357 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1358 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1359 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1360 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1361 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1362 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1363 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1364 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1365 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1366 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1367 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1368 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1369 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1370 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1371 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1372 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1373 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1374 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1375 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1376 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1377 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1378 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1379 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1380 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1381 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1382 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1383 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1384 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1385 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1386 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1387 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1388 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1389 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1390 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1391 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1392 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1393 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1394 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1395 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1396 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1397 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1398 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1399 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1400 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1401 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1402 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1403 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1404 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1405 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1406 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1407 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

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

def pivotPermutation1408 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1409 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1410 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1411 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1412 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1413 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1414 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1415 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1416 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1417 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1418 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1419 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1420 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1421 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1422 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1423 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1424 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1425 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1426 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1427 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1428 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1429 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1430 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1431 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1432 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1433 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1434 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1435 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1436 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1437 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1438 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1439 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1440 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1441 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1442 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1443 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1444 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1445 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1446 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1447 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1448 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1449 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1450 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1451 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1452 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1453 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1454 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1455 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1456 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1457 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1458 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1459 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1460 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1461 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1462 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1463 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1464 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1465 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1466 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1467 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1468 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1469 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1470 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1471 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

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

def pivotPermutation1472 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1473 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1474 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1475 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1476 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1477 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1478 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1479 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1480 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1481 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1482 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1483 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1484 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1485 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1486 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1487 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1488 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1489 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1490 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1491 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1492 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1493 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1494 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1495 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1496 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1497 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1498 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1499 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1500 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1501 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1502 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1503 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1504 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1505 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1506 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1507 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1508 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1509 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1510 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1511 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1512 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1513 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1514 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1515 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1516 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1517 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1518 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1519 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1520 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1521 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1522 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1523 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1524 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1525 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1526 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1527 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1528 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1529 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1530 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1531 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1532 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1533 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1534 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1535 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

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

def pivotPermutation1536 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1537 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1538 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1539 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1540 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1541 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1542 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1543 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1544 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1545 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1546 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1547 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1548 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1549 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1550 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1551 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1552 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1553 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1554 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1555 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1556 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1557 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1558 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1559 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1560 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1561 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1562 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1563 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1564 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1565 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1566 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1567 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1568 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1569 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1570 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1571 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1572 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1573 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1574 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1575 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1576 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1577 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1578 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1579 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1580 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1581 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1582 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1583 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1584 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1585 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1586 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1587 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1588 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1589 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1590 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1591 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1592 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1593 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1594 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1595 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1596 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1597 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1598 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1599 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

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

def pivotPermutation1600 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1601 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1602 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1603 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1604 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1605 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1606 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1607 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1608 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1609 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1610 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1611 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1612 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1613 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1614 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1615 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1616 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1617 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1618 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1619 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1620 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1621 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1622 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1623 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1624 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1625 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1626 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1627 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1628 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1629 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1630 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1631 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1632 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1633 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1634 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1635 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1636 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1637 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1638 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1639 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1640 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1641 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1642 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1643 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1644 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1645 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1646 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1647 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1648 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1649 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1650 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1651 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1652 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1653 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1654 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1655 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1656 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1657 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1658 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1659 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1660 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1661 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1662 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1663 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

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

def pivotPermutation1664 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1665 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1666 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1667 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1668 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1669 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1670 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1671 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1672 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1673 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1674 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1675 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1676 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1677 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1678 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1679 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1680 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1681 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1682 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1683 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1684 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1685 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1686 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1687 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1688 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1689 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1690 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1691 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1692 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1693 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1694 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1695 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1696 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1697 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1698 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1699 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1700 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1701 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1702 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1703 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1704 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1705 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1706 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1707 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1708 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1709 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1710 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1711 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1712 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1713 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1714 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1715 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1716 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1717 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1718 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1719 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1720 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1721 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1722 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1723 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1724 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1725 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1726 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1727 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

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

def pivotPermutation1728 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1729 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1730 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1731 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1732 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1733 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1734 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1735 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1736 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1737 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1738 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1739 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1740 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1741 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1742 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1743 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1744 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1745 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1746 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1747 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1748 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1749 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1750 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1751 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1752 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1753 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1754 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1755 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1756 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1757 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1758 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1759 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1760 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1761 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1762 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1763 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1764 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1765 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1766 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1767 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1768 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1769 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1770 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1771 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1772 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1773 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1774 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1775 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1776 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1777 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1778 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1779 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1780 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1781 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1782 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1783 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1784 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1785 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1786 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1787 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1788 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1789 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1790 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1791 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

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

def pivotPermutation1792 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1793 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1794 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1795 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1796 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1797 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1798 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1799 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1800 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1801 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1802 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1803 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1804 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1805 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1806 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1807 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1808 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1809 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1810 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1811 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1812 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1813 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1814 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1815 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1816 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1817 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1818 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1819 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1820 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1821 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1822 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1823 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1824 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1825 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1826 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1827 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1828 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1829 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1830 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1831 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1832 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1833 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1834 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1835 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1836 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1837 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1838 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1839 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1840 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1841 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1842 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1843 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1844 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1845 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1846 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1847 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1848 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1849 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1850 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1851 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1852 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1853 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1854 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1855 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

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

def pivotPermutation1856 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1857 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1858 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1859 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1860 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1861 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1862 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1863 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1864 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1865 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1866 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1867 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1868 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1869 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1870 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1871 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1872 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1873 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1874 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1875 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1876 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1877 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1878 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1879 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1880 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1881 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1882 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1883 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1884 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1885 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1886 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1887 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1888 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1889 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1890 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1891 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1892 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1893 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1894 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1895 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1896 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1897 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1898 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1899 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1900 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1901 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1902 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1903 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1904 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1905 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1906 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1907 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1908 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1909 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1910 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1911 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1912 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1913 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1914 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1915 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1916 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1917 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1918 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1919 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

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

def pivotPermutation1920 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1921 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1922 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1923 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1924 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1925 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1926 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1927 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1928 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1929 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1930 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1931 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1932 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1933 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1934 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1935 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1936 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1937 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1938 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1939 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1940 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1941 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1942 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1943 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1944 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1945 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1946 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1947 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1948 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1949 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1950 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1951 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1952 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1953 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1954 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1955 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1956 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1957 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1958 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1959 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1960 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1961 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1962 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1963 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1964 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1965 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1966 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1967 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1968 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1969 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1970 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1971 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1972 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1973 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1974 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1975 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1976 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1977 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1978 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1979 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1980 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1981 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1982 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1983 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

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

def pivotPermutation1984 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1985 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1986 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1987 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1988 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1989 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1990 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1991 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1992 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1993 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1994 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1995 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1996 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1997 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1998 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation1999 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2000 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2001 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2002 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2003 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2004 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2005 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2006 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2007 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2008 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2009 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2010 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2011 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2012 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2013 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2014 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2015 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2016 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2017 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2018 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2019 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2020 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2021 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2022 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2023 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2024 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2025 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2026 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2027 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2028 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2029 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2030 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2031 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2032 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2033 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2034 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2035 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2036 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2037 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2038 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2039 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2040 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2041 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2042 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2043 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2044 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2045 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2046 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2047 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

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

def pivotPermutation2048 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2049 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2050 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2051 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2052 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2053 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2054 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2055 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2056 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2057 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2058 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2059 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2060 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2061 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2062 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2063 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2064 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2065 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2066 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2067 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2068 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2069 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2070 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2071 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2072 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2073 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2074 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2075 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2076 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2077 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2078 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2079 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2080 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2081 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2082 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2083 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2084 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2085 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2086 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2087 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2088 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2089 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2090 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2091 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2092 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2093 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2094 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2095 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2096 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2097 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2098 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2099 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2100 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2101 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2102 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2103 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2104 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2105 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2106 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2107 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2108 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2109 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2110 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2111 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

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

def pivotPermutation2112 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2113 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2114 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2115 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2116 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2117 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2118 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2119 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2120 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2121 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2122 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2123 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2124 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2125 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2126 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2127 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2128 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2129 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2130 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2131 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2132 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2133 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2134 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2135 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2136 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2137 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2138 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2139 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2140 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2141 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2142 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2143 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2144 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2145 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2146 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2147 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2148 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2149 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2150 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2151 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2152 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2153 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2154 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2155 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2156 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2157 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2158 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2159 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2160 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2161 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2162 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2163 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2164 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2165 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2166 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2167 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2168 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2169 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2170 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2171 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2172 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2173 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2174 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2175 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

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

def pivotPermutation2176 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2177 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2178 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2179 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2180 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2181 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2182 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2183 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2184 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2185 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2186 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2187 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2188 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2189 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2190 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2191 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2192 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2193 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2194 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2195 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2196 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2197 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2198 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2199 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2200 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2201 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2202 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2203 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2204 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2205 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2206 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2207 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2208 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2209 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2210 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2211 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2212 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2213 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2214 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2215 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2216 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2217 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2218 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2219 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2220 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2221 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2222 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2223 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2224 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2225 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2226 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2227 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2228 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2229 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2230 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2231 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2232 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2233 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2234 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2235 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2236 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2237 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2238 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2239 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

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

def pivotPermutation2240 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2241 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2242 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2243 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2244 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2245 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2246 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2247 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2248 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2249 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2250 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2251 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2252 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2253 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2254 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2255 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2256 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2257 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2258 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2259 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2260 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2261 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2262 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2263 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2264 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2265 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2266 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2267 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2268 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2269 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2270 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2271 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2272 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2273 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2274 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2275 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2276 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2277 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2278 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2279 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2280 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2281 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2282 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2283 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2284 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2285 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2286 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2287 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2288 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2289 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2290 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2291 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2292 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2293 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2294 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2295 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2296 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2297 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2298 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2299 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2300 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2301 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2302 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2303 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

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

def pivotPermutation2304 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2305 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2306 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2307 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2308 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2309 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2310 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2311 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2312 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2313 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2314 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2315 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2316 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2317 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2318 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2319 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2320 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2321 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2322 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2323 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2324 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2325 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2326 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2327 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2328 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2329 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2330 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2331 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2332 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2333 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2334 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2335 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2336 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2337 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2338 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2339 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2340 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2341 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2342 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2343 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2344 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2345 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2346 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2347 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2348 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2349 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2350 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2351 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2352 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2353 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2354 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2355 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2356 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2357 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2358 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2359 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2360 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2361 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2362 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2363 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2364 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2365 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2366 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2367 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

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

def pivotPermutation2368 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2369 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2370 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2371 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2372 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2373 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2374 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2375 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2376 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2377 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2378 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2379 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2380 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2381 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2382 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2383 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2384 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2385 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2386 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2387 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2388 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2389 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2390 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2391 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2392 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2393 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2394 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2395 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2396 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2397 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2398 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2399 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2400 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2401 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2402 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2403 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2404 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2405 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2406 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2407 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2408 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2409 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2410 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2411 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2412 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2413 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2414 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2415 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2416 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2417 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2418 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2419 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2420 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2421 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2422 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2423 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2424 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2425 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2426 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2427 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2428 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2429 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2430 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2431 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

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

def pivotPermutation2432 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2433 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2434 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2435 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2436 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2437 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2438 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2439 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2440 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2441 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2442 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2443 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2444 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2445 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2446 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2447 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2448 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2449 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2450 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2451 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2452 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2453 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2454 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2455 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2456 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2457 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2458 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2459 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2460 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2461 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2462 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2463 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2464 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2465 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2466 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2467 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2468 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2469 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2470 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2471 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2472 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2473 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2474 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2475 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2476 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2477 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2478 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2479 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2480 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2481 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2482 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2483 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2484 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2485 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2486 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2487 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2488 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2489 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2490 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2491 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2492 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2493 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2494 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2495 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

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

def pivotPermutation2496 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2497 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2498 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2499 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2500 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2501 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2502 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2503 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2504 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2505 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2506 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2507 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2508 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2509 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2510 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2511 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2512 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2513 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2514 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2515 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2516 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2517 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2518 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2519 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2520 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2521 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2522 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2523 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2524 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2525 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2526 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2527 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2528 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2529 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2530 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2531 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2532 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2533 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2534 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2535 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2536 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2537 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2538 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2539 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2540 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2541 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2542 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2543 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2544 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2545 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2546 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2547 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2548 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2549 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2550 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2551 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2552 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2553 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2554 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2555 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2556 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2557 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2558 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2559 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

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

def pivotPermutation2560 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2561 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2562 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2563 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2564 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2565 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2566 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2567 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2568 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2569 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2570 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2571 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2572 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2573 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2574 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2575 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2576 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2577 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2578 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2579 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2580 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2581 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2582 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2583 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2584 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2585 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2586 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2587 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2588 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2589 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2590 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2591 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2592 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2593 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2594 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2595 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2596 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2597 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2598 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2599 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2600 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2601 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2602 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2603 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2604 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2605 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2606 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2607 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2608 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2609 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2610 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2611 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2612 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2613 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2614 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2615 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2616 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2617 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2618 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2619 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2620 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2621 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2622 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2623 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

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

def pivotPermutation2624 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2625 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2626 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2627 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2628 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2629 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2630 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2631 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2632 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2633 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2634 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2635 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2636 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2637 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2638 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2639 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2640 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2641 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2642 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2643 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2644 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2645 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2646 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2647 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2649 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2650 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2651 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2652 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2653 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2654 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2655 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2656 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2657 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2658 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2659 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2660 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2661 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2662 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2663 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2666 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2667 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2668 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2669 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2670 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2671 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2672 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2673 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2674 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2675 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2676 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2677 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2678 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2679 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2680 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2681 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2682 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2683 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2684 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2685 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2686 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2687 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

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

def pivotPermutation2688 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2689 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2690 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2691 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2692 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2693 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2694 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2695 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2696 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2697 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2698 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2699 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2700 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2701 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2702 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2703 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2704 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2705 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2706 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2707 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2708 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2709 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2710 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2711 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2712 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2713 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2714 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2715 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2716 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2717 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2718 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2719 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2720 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2721 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2722 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2723 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2724 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2725 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2726 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2727 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2728 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2729 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2730 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2731 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2732 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2733 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2734 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2735 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2736 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2737 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2738 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2739 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2740 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2741 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2742 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2743 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2744 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2745 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2746 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2747 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2748 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2749 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2750 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2751 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

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

def pivotPermutation2752 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2753 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2754 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2755 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2756 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2757 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2758 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2759 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2760 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2761 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2762 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2763 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2764 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2765 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2766 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2767 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2768 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2769 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2770 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2771 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2772 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2773 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2774 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2775 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2776 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2777 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2778 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2779 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2780 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2781 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2782 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2783 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2784 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2785 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2786 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2787 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2788 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2789 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2790 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2791 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2792 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2793 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2795 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2796 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2797 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2799 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2800 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2801 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2802 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2803 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2804 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2805 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2806 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2807 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2808 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2809 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2810 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2811 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2812 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2813 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2814 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2815 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

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

def pivotPermutation2816 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2817 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2818 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2819 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2820 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2821 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2822 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2823 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2824 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2825 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2826 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2827 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2828 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2829 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2830 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2831 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2832 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2833 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2834 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2835 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2836 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2837 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2838 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2839 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2840 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2841 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2842 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2843 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2844 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2845 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2846 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2847 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2848 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2849 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2850 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2851 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2852 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2853 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2854 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2855 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2856 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2857 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2858 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2859 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2860 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2861 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2862 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2863 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2864 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2865 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2866 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2867 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2868 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2869 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2870 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2871 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2872 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2873 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2874 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2875 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2876 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2877 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2878 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2879 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

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

def pivotPermutation2880 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2881 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2882 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2883 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2884 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2885 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2886 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2887 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2888 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2889 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2890 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2891 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2892 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2893 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2894 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2895 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2896 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2897 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2898 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2899 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2900 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2901 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2902 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2903 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2904 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2905 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2906 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2907 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2908 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2909 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2910 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2911 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2912 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2913 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2914 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2915 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2916 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2917 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2918 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2919 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2920 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2921 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2922 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2923 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2924 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2925 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2926 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2927 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2928 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2929 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2930 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2931 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2932 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2933 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2934 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2935 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2936 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2937 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2938 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2939 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2940 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2941 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2942 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2943 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

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

def pivotPermutation2944 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2945 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2946 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2947 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2948 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2949 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2950 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2951 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2952 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2953 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2954 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2955 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2956 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2957 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2958 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2959 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2960 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2961 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2962 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2963 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2964 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2965 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2966 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2967 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2968 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2969 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2970 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2971 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2972 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2973 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2974 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2975 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2976 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2977 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2978 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2979 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2980 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2981 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2982 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2983 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2984 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2985 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2986 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2987 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2988 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2989 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2990 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2991 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2992 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2993 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2994 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2995 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2996 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2997 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2998 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation2999 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3000 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3001 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3002 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3003 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3004 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3005 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3006 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3007 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

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

def pivotPermutation3008 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3009 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3010 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3011 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3012 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3013 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3014 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3015 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3016 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3017 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3018 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3019 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3020 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3021 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3022 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3023 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3024 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3025 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3026 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3027 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3028 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3029 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3030 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3031 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3032 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3033 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3034 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3035 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3036 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3037 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3038 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3039 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3040 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3041 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3042 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3043 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3044 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3045 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3046 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3047 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3048 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3049 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3050 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3051 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3052 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3053 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3054 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3055 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3056 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3057 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3058 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3059 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3060 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3061 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3062 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3063 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3064 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3065 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3066 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3067 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3068 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3069 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3070 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3071 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

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

def pivotPermutation3072 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3073 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3074 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3075 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3076 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3077 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3078 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3079 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3080 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3081 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3082 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3083 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3084 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3085 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3086 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3087 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3088 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3089 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3090 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3091 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3092 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3093 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3094 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3095 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3096 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3097 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3098 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3099 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3100 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3101 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3102 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3103 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3104 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3105 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3106 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3107 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3108 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3109 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3110 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3111 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3112 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3113 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3114 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3115 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3116 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3117 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3118 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3119 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3120 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3121 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3122 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3123 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3124 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3125 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3126 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3127 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3128 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3129 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3130 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3131 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3132 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3133 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3134 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3135 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

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

def pivotPermutation3136 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3137 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3138 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3139 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3140 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3141 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3142 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3143 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3144 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3145 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3146 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3147 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3148 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3149 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3150 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3151 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3152 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3153 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3154 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3155 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3156 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3157 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3158 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3159 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3160 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3161 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3162 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3163 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3164 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3165 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3166 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3167 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3168 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3169 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3170 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3171 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3172 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3173 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3174 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3175 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3176 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3177 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3178 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3179 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3180 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3181 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3182 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3183 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3184 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3185 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3186 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3187 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3188 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3189 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3190 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3191 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3192 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3193 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3194 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3195 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3196 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3197 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3198 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3199 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

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

def pivotPermutation3200 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3201 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3202 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3203 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3204 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3205 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3206 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3207 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3208 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3209 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3210 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3211 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3212 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3213 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3214 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3215 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3216 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3217 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3218 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3219 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3220 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3221 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3222 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3223 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3224 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3225 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3226 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3227 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3228 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3229 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3230 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3231 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3232 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3233 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3234 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3235 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3236 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3237 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3238 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3239 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3240 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3241 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3242 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3243 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3244 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3245 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3246 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3247 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3248 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3249 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3250 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3251 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3252 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3253 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3254 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3255 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3256 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3257 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3258 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3259 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3260 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3261 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3262 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3263 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

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

def pivotPermutation3264 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3265 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3266 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3267 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3268 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3269 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3270 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3271 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3272 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3273 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3274 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3275 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3276 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3277 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3278 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3279 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3280 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3281 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3282 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3283 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3284 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3285 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3286 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3287 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3288 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3289 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3290 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3291 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3292 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3293 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3294 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3295 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3296 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3297 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3298 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3299 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3300 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3301 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3302 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3303 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3304 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3305 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3306 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3307 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3308 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3309 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3310 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3311 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3312 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3313 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3314 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3315 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3316 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3317 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3318 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3319 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3320 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3321 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3322 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3323 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3324 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3325 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3326 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3327 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

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

def pivotPermutation3328 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3329 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3330 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3331 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3332 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3333 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3334 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3335 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3336 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3337 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3338 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3339 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3340 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3341 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3342 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3343 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3344 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3345 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3346 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3347 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3348 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3349 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3350 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3351 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3352 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3353 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3354 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3355 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3356 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3357 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3358 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3359 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3360 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3361 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3362 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3363 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3364 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3365 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3366 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3367 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3368 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3369 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3370 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3371 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3372 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3373 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3374 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3375 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3376 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3377 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3378 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3379 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3380 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3381 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3382 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3383 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3384 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3385 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3386 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3387 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3388 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3389 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3390 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3391 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

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

def pivotPermutation3392 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3393 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3394 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3395 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3396 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3397 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3398 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3399 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3400 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3401 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3402 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3403 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3404 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3405 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3406 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3407 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3408 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3409 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3410 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3411 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3412 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3413 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3414 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3415 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3416 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3417 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3418 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3419 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3420 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3421 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3422 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3423 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3424 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3425 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3426 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3427 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3428 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3429 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3430 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3431 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3432 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3433 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3434 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3435 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3436 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3437 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3438 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3439 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3440 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3441 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3442 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3443 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3444 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3445 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3446 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3447 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3448 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3449 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3450 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3451 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3452 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3453 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3454 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3455 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

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

def pivotPermutation3456 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3457 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3458 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3459 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3460 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3461 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3462 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3463 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3464 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3465 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3466 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3467 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotPermutation3468 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

end MUB6.Certificate.PairSemantics

end OAI
end


