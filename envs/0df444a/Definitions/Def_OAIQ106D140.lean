-- Prove2me | Definitions.Def_OAIQ106D140
-- name    : OAIQ106D140
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T13:40:15.590878+00:00
-- url     : https://prove2.me/theorems/712019f9-c9bf-4685-9143-559f21ddc442
-- title:
--   Definitions bundle OAIQ106D140 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1353 declarations of OpenAI's Lean: 1346 definitions, 1 inductive type or structure and 6 theorems. The definitions and types are `OAI.MUB6.Certificate.PairSemantics.value3192`, `OAI.MUB6.Certificate.PairSemantics.value3193`, `OAI.MUB6.Certificate.PairSemantics.value3194`, `OAI.MUB6.Certificate.PairSemantics.value3195`, `OAI.MUB6.Certificate.PairSemantics.value3196`, `OAI.MUB6.Certificate.PairSemantics.value3197`, `OAI.MUB6.Certificate.PairSemantics.value3198`, `OAI.MUB6.Certificate.PairSemantics.value3199`, `OAI.MUB6.Certificate.PairSemantics.value320`, `OAI.MUB6.Certificate.PairSemantics.value3200`, `OAI.MUB6.Certificate.PairSemantics.value3201`, `OAI.MUB6.Certificate.PairSemantics.value3202`, `OAI.MUB6.Certificate.PairSemantics.value3203`, `OAI.MUB6.Certificate.PairSemantics.value3204`, `OAI.MUB6.Certificate.PairSemantics.value3205`, `OAI.MUB6.Certificate.PairSemantics.value3206`, `OAI.MUB6.Certificate.PairSemantics.value3207`, `OAI.MUB6.Certificate.PairSemantics.value3208`, `OAI.MUB6.Certificate.PairSemantics.value3209`, `OAI.MUB6.Certificate.PairSemantics.value321`, `OAI.MUB6.Certificate.PairSemantics.value3210`, `OAI.MUB6.Certificate.PairSemantics.value3211`, `OAI.MUB6.Certificate.PairSemantics.value3212`, `OAI.MUB6.Certificate.PairSemantics.value3213`, `OAI.MUB6.Certificate.PairSemantics.value3214`, `OAI.MUB6.Certificate.PairSemantics.value3215`, `OAI.MUB6.Certificate.PairSemantics.value3216`, `OAI.MUB6.Certificate.PairSemantics.value3217`, `OAI.MUB6.Certificate.PairSemantics.value3218`, `OAI.MUB6.Certificate.PairSemantics.value3219`, `OAI.MUB6.Certificate.PairSemantics.value322`, `OAI.MUB6.Certificate.PairSemantics.value3220`, `OAI.MUB6.Certificate.PairSemantics.value3221`, `OAI.MUB6.Certificate.PairSemantics.value3222`, `OAI.MUB6.Certificate.PairSemantics.value3223`, `OAI.MUB6.Certificate.PairSemantics.value3224`, `OAI.MUB6.Certificate.PairSemantics.value3225`, `OAI.MUB6.Certificate.PairSemantics.value3226`, `OAI.MUB6.Certificate.PairSemantics.value3227`, `OAI.MUB6.Certificate.PairSemantics.value3228` and 1307 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_Certificate_Gram`, `MutuallyUnbiased_Cubic_CubicPattern`, `MutuallyUnbiased_Fourier_Dichotomy`, `MutuallyUnbiased_Matrix_Hadamard`, `MutuallyUnbiased_Moments_GramNormalization`, `MutuallyUnbiased_Moments_Moments`, `MutuallyUnbiased_Moments_SmallPartitions`, `MutuallyUnbiased_PairMoments_PairCharges`, `MutuallyUnbiased_PairPolynomial_Grid`, `MutuallyUnbiased_PairPolynomial_Terms`, `MutuallyUnbiased_PairSemantics_Values0`, `MutuallyUnbiased_PairSemantics_Values1`, `MutuallyUnbiased_PairSemantics_Values10`, `MutuallyUnbiased_PairSemantics_Values11`, `MutuallyUnbiased_PairSemantics_Values12`, `MutuallyUnbiased_PairSemantics_Values13`, `MutuallyUnbiased_PairSemantics_Values14`, `MutuallyUnbiased_PairSemantics_Values15`, `MutuallyUnbiased_PairSemantics_Values49`, `MutuallyUnbiased_PairSemantics_Values5`, `MutuallyUnbiased_PairSemantics_Values50`, `MutuallyUnbiased_PairSemantics_Values51`, `MutuallyUnbiased_PairSemantics_Values52`, `MutuallyUnbiased_PairSemantics_Values53`, `MutuallyUnbiased_PairSemantics_Values54`, `MutuallyUnbiased_PairSemantics_Values6`, `MutuallyUnbiased_PairSemantics_Values7`, `MutuallyUnbiased_PairSemantics_Values8`, `MutuallyUnbiased_PairSemantics_Values9`, `MutuallyUnbiased_PairSources_Data`, `MutuallyUnbiased_PairTargets_Data`, `MutuallyUnbiased_PairTargets_IntegerTerms`, `MutuallyUnbiased_PairTargets_Partition0`, `MutuallyUnbiased_PairTargets_Partition1`, `MutuallyUnbiased_PairTargets_Partition10`, `MutuallyUnbiased_PairTargets_Partition11`, `MutuallyUnbiased_PairTargets_Partition12`, `MutuallyUnbiased_PairTargets_Partition13`, `MutuallyUnbiased_PairTargets_Partition14`, `MutuallyUnbiased_PairTargets_Partition15`, `MutuallyUnbiased_PairTargets_Partition16`, `MutuallyUnbiased_PairTargets_Partition17`, `MutuallyUnbiased_PairTargets_Partition18`, `MutuallyUnbiased_PairTargets_Partition19`, `MutuallyUnbiased_PairTargets_Partition2`, `MutuallyUnbiased_PairTargets_Partition20`, `MutuallyUnbiased_PairTargets_Partition21`, `MutuallyUnbiased_PairTargets_Partition22`, `MutuallyUnbiased_PairTargets_Partition23`, `MutuallyUnbiased_PairTargets_Partition24`, `MutuallyUnbiased_PairTargets_Partition25`, `MutuallyUnbiased_PairTargets_Partition26`, `MutuallyUnbiased_PairTargets_Partition3`, `MutuallyUnbiased_PairTargets_Partition4`, `MutuallyUnbiased_PairTargets_Partition5`, `MutuallyUnbiased_PairTargets_Partition6`, `MutuallyUnbiased_PairTargets_Partition7`, `MutuallyUnbiased_PairTargets_Partition8`, `MutuallyUnbiased_PairTargets_Partition9`, `MutuallyUnbiased_TaoCertificate_Merge0`, `MutuallyUnbiased_TaoCertificate_Merge1`, `MutuallyUnbiased_TaoCertificate_Merge12`, `MutuallyUnbiased_TaoCertificate_Merge13`, `MutuallyUnbiased_TaoCertificate_Merge14`, `MutuallyUnbiased_TaoCertificate_Merge15`, `MutuallyUnbiased_TaoCertificate_Merge16`, `MutuallyUnbiased_TaoCertificate_Merge17`, `MutuallyUnbiased_TaoCertificate_Merge18`, `MutuallyUnbiased_TaoCertificate_Merge19`, `MutuallyUnbiased_TaoCertificate_Merge2`, `MutuallyUnbiased_Tao_TaoArithmetic`, `MutuallyUnbiased_Tao_TaoSparse`, `MutuallyUnbiased_Tao_TaoTarget`.
--
--   **Imports.** It imports the published bundle `Def_MUBSix`; the bundles `OAIQ106D000`, `OAIQ106D001`, `OAIQ106D002`, `OAIQ106D029`, `OAIQ106D044`, `OAIQ106D059`, `OAIQ106D064`, `OAIQ106D065`, `OAIQ106D067` and `OAIQ106D068` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ106D160`, `OAIQ106D161`, `OAIQ106D163`, `OAIQ106D164`, `OAIQ106D168`, `OAIQ106D172`, `OAIQ106D176`, `OAIQ106D182`, `OAIQ106D184`, `OAIQ106D185`, `OAIQ106D186`, `OAIQ106D187`, `OAIQ106D188`, `OAIQ106D189`, `OAIQ106D190`, `OAIQ106D191`, `OAIQ106D192`, `OAIQ106D193`, `OAIQ106D194`, `OAIQ106D195`, `OAIQ106D196` and `OAIQ106D197`; the statements `OAI.MUB6.Certificate.PairTargetSemantics.certificate_zero1`, `OAI.MUB6.Certificate.PairTargetSemantics.pair_partition4` and `OAI.MUB6.fourier_vanishing_of_pair_certificates`; the proofs of `OAI.MUB6.Certificate.GramData.Block3.entry_0_12`, `OAI.MUB6.Certificate.GramData.Block3.entry_0_13`, `OAI.MUB6.Certificate.GramData.Block3.entry_0_14`, `OAI.MUB6.Certificate.GramData.Block3.entry_0_15`, `OAI.MUB6.Certificate.GramData.Block3.entry_0_16`, `OAI.MUB6.Certificate.GramData.Block3.entry_0_17`, `OAI.MUB6.Certificate.GramData.Block3.entry_0_18`, `OAI.MUB6.Certificate.GramData.Block3.entry_0_19`, `OAI.MUB6.Certificate.GramData.Block3.entry_0_20`, `OAI.MUB6.Certificate.GramData.Block3.entry_0_21`, `OAI.MUB6.Certificate.GramData.Block3.entry_0_22`, `OAI.MUB6.Certificate.GramData.Block3.entry_0_23`, `OAI.MUB6.Certificate.GramData.Block3.entry_0_24`, `OAI.MUB6.Certificate.GramData.Block3.entry_0_25`, `OAI.MUB6.Certificate.GramData.Block3.entry_0_26`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_0`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_1`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_10`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_11`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_12`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_13`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_14`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_15`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_16`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_17`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_18`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_19`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_2`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_20`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_21`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_22`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_23`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_24`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_25`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_26`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_3`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_4`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_5`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_6`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_7`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_8`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_9`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_0`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_1`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_10`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_11`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_12`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_13`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_14`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_15`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_16`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_17`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_18`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_19`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_2`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_20`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_21`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_22`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_23`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_24`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_25`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_26`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_3`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_4`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_5`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_6`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_7`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_8`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_9`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_0`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_1`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_10`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_11`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_12`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_13`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_14`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_15`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_16`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_17`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_18`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_19`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_2`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_20`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_21`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_22`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_23`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_24`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_25`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_26`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_3`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_4`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_5`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_6`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_7`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_8`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_9`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_0`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_1`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_10`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_11`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_12`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_13`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_14`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_15`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_16`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_17`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_18`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_19`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_2`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_20`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_21`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_22`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_23`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_24`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_25`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_26`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_3`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_4`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_5`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_6`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_7`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_8`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_9`, `OAI.MUB6.Certificate.GramData.Block3.entry_14_0`, `OAI.MUB6.Certificate.GramData.Block3.entry_14_1`, `OAI.MUB6.Certificate.GramData.Block3.entry_14_2`, `OAI.MUB6.Certificate.GramData.Block3.entry_14_3`, `OAI.MUB6.Certificate.GramData.Block3.entry_14_4`, `OAI.MUB6.Certificate.GramData.Block3.entry_14_5`, `OAI.MUB6.Certificate.GramData.Block3.entry_1_10`, `OAI.MUB6.Certificate.GramData.Block3.entry_1_11`, `OAI.MUB6.Certificate.GramData.Block3.entry_1_12`, `OAI.MUB6.Certificate.GramData.Block3.entry_1_13`, `OAI.MUB6.Certificate.GramData.Block3.entry_1_14`, `OAI.MUB6.Certificate.GramData.Block3.entry_1_15`, `OAI.MUB6.Certificate.GramData.Block3.entry_1_16`, `OAI.MUB6.Certificate.GramData.Block3.entry_1_17`, `OAI.MUB6.Certificate.GramData.Block3.entry_1_18`, `OAI.MUB6.Certificate.GramData.Block3.entry_1_19`, `OAI.MUB6.Certificate.GramData.Block3.entry_1_20`, `OAI.MUB6.Certificate.GramData.Block3.entry_1_21`, `OAI.MUB6.Certificate.GramData.Block3.entry_1_22`, `OAI.MUB6.Certificate.GramData.Block3.entry_1_23`, `OAI.MUB6.Certificate.GramData.Block3.entry_1_24`, `OAI.MUB6.Certificate.GramData.Block3.entry_1_25`, `OAI.MUB6.Certificate.GramData.Block3.entry_1_26`, `OAI.MUB6.Certificate.GramData.Block3.entry_20_12`, `OAI.MUB6.Certificate.GramData.Block3.entry_20_13`, `OAI.MUB6.Certificate.GramData.Block3.entry_20_14`, `OAI.MUB6.Certificate.GramData.Block3.entry_20_15`, `OAI.MUB6.Certificate.GramData.Block3.entry_20_16`, `OAI.MUB6.Certificate.GramData.Block3.entry_20_17`, `OAI.MUB6.Certificate.GramData.Block3.entry_20_18`, `OAI.MUB6.Certificate.GramData.Block3.entry_20_19`, `OAI.MUB6.Certificate.GramData.Block3.entry_20_20`, `OAI.MUB6.Certificate.GramData.Block3.entry_20_21`, `OAI.MUB6.Certificate.GramData.Block3.entry_20_22`, `OAI.MUB6.Certificate.GramData.Block3.entry_20_23`, `OAI.MUB6.Certificate.GramData.Block3.entry_20_24`, `OAI.MUB6.Certificate.GramData.Block3.entry_20_25`, `OAI.MUB6.Certificate.GramData.Block3.entry_20_26`, `OAI.MUB6.Certificate.GramData.Block3.entry_21_0`, `OAI.MUB6.Certificate.GramData.Block3.entry_21_1`, `OAI.MUB6.Certificate.GramData.Block3.entry_21_2`, `OAI.MUB6.Certificate.GramData.Block3.entry_21_3`, `OAI.MUB6.Certificate.GramData.Block3.entry_21_4`, `OAI.MUB6.Certificate.GramData.Block3.entry_21_5`, `OAI.MUB6.Certificate.GramData.Block3.entry_21_6`, `OAI.MUB6.Certificate.GramData.Block3.entry_21_7`, `OAI.MUB6.Certificate.GramData.Block3.entry_21_8`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_0`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_1`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_10`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_11`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_12`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_13`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_14`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_15`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_16`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_17`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_18`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_19`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_2`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_20`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_21`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_22`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_23`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_24`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_25`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_26`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_3`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_4`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_5`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_6`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_7`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_8`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_9`, `OAI.MUB6.Certificate.GramData.Block3.entry_3_10`, `OAI.MUB6.Certificate.GramData.Block3.entry_3_11`, `OAI.MUB6.Certificate.GramData.Block3.entry_3_12`, `OAI.MUB6.Certificate.GramData.Block3.entry_3_13`, `OAI.MUB6.Certificate.GramData.Block3.entry_3_14`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_10`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_11`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_12`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_13`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_14`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_15`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_16`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_17`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_18`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_19`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_20`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_21`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_22`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_23`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_24`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_25`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_26`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_9`, `OAI.MUB6.Certificate.GramData.Block3.entry_6_0`, `OAI.MUB6.Certificate.GramData.Block3.entry_6_1`, `OAI.MUB6.Certificate.GramData.Block3.entry_6_2`, `OAI.MUB6.Certificate.GramData.Block3.entry_6_3`, `OAI.MUB6.Certificate.GramData.Block3.entry_6_4`, `OAI.MUB6.Certificate.GramData.Block3.entry_6_5`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_0`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_1`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_10`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_11`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_12`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_13`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_14`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_15`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_16`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_17`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_18`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_19`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_2`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_20`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_21`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_22`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_23`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_3`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_4`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_5`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_6`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_7`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_8`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_9`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_21`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_22`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_23`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_24`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_25`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_26`, `OAI.MUB6.Certificate.GramData.Block3.gram`, `OAI.MUB6.Certificate.GramData.Block4.positiveDefinite`, `OAI.MUB6.Certificate.PairTargetSemantics.pair_partition4` and `OAI.MUB6.complete_family_fourier_zero`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106D000
import Definitions.Def_OAIQ106D001
import Definitions.Def_OAIQ106D002
import Definitions.Def_OAIQ106D029
import Definitions.Def_OAIQ106D044
import Definitions.Def_OAIQ106D059
import Definitions.Def_OAIQ106D064
import Definitions.Def_OAIQ106D065
import Definitions.Def_OAIQ106D067
import Definitions.Def_OAIQ106D068

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_Gram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact rational Gram witnesses

A unit lower triangular matrix and a positive rational diagonal certify a real
matrix's positive definiteness. The large numerical checks can therefore be
split into separate rational identities for individual matrix entries.
-/
namespace MUB6.Certificate

open Matrix
open scoped BigOperators

@[simp] theorem lowerUnit_diag {n : ℕ} (entries : Matrix (Fin n) (Fin n) ℚ)
    (i : Fin n) : lowerUnit entries i i = 1 := by simp [lowerUnit]

@[simp] theorem lowerUnit_above {n : ℕ} (entries : Matrix (Fin n) (Fin n) ℚ)
    {i j : Fin n} (h : i < j) : lowerUnit entries i j = 0 := by
  simp [lowerUnit, not_lt_of_ge h.le, ne_of_lt h]

end MUB6.Certificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Cubic_CubicPattern
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! From cubed row-ratio patterns to the single three-by-three exceptional block. -/

noncomputable section

namespace MUB6

@[simp] theorem mem_nonOneSupport (f : Fin 6 → ℂ) (i : Fin 6) :
    i ∈ nonOneSupport f ↔ f i ≠ 1 := by
  classical
  simp [nonOneSupport]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Matrix_Hadamard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
open Matrix

namespace MUB6

def difference (i j : Coord) : Charge := Pi.single i 1 - Pi.single j 1

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_Moments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite injective moments of Section 2 of the exact companion.
Both orientations are retained with weight 1/2, including when H = Hᵀ. -/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

/-- Equation (pair-average), with the two orientations counted separately. -/
def pairAverage (H : CMatrix) (F : CMatrix → ℝ) : ℝ :=
  average (fun π : Equiv.Perm Coord =>
    (F (fun i j => H (π i) j) + F (fun i j => H j (π i))) / 2)

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMoments_PairCharges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace MUB6

def qCross : Charge := ![2, 0, 0, -2, 0, 0]
def qSame : Charge := ![2, -2, 0, 0, 0, 0]
def pairW : Charge := ![-3, -2, 0, 1, 2, 2]
def pairA : Fin 4 → Charge :=
  ![![-1, -1, 0, 0, 1, 1], ![-2, 0, 0, 0, 1, 1],
    ![-1, -1, 0, 1, 0, 1], ![-1, -1, 0, 1, 1, 0]]

def pairL (H : CMatrix) : ℂ :=
  -g H pairW + ∑ j, pairCoefficient j * g H (pairA j) * g H (pairW - pairA j)

def PairCertificateIdentity (H : CMatrix) (q : Charge) : Prop :=
  3 * pairAverage H (fun K => Complex.normSq (pairL K)) +
    pairAverage H (fun K => Complex.normSq (g K alpha * g K q)) = 0

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Fourier_Dichotomy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

def PairProductsZero (H : CMatrix) : Prop :=
  ∀ π : Equiv.Perm Coord,
    g (fun i j => H (π i) j) alpha * g (fun i j => H (π i) j) qCross = 0 ∧
    g (fun i j => H (π i) j) alpha * g (fun i j => H (π i) j) qSame = 0

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_GramNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Row permutation and symmetry normalization of auxiliary Gram terms.
The normalizer is executable, but its interpretation theorem is an ordinary
proof valid for arbitrary complex mutually unbiased bases. -/

open scoped BigOperators

namespace MUB6.GramNormalization

def Key.leftCharge (K : Key) : Charge := fun i => (K.rows.getD i.val (0, 0)).1
def Key.rightCharge (K : Key) : Charge := fun i => (K.rows.getD i.val (0, 0)).2

end MUB6.GramNormalization

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_SmallPartitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.EqualityPatterns

def label2 (p : Fin 2) (i : Fin 2) : Fin (blocks2 p) :=
  ⟨raw2 p i, by fin_cases p <;> fin_cases i <;> decide⟩

def family2 : Family (Fin 2) (Fin 2) where
  blocks := blocks2
  label := label2
  onto := by decide +kernel
  unique := by decide +kernel

end MUB6.EqualityPatterns

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open scoped BigOperators

structure Term where
  arity : ℕ
  charges : Matrix Coord (Fin arity) ℤ
  coefficient : ℤ
  deriving Inhabited

noncomputable def weightedAverage (H : CMatrix) (t : Term) : ℝ :=
  (t.coefficient : ℝ) * pairAverage H (fun K => (∏ j, g K (fun i => t.charges i j)).re)

def term0 : Term := ⟨2, ![![-3, 3], ![-2, 2], ![0, 0], ![1, -1], ![2, -2], ![2, -2]], 3⟩

def term1 : Term := ⟨3, ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]], -6⟩

def term2 : Term := ⟨3, ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]], -3⟩

def term3 : Term := ⟨3, ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]], -3⟩

def term4 : Term := ⟨3, ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]], -3⟩

def term5 : Term := ⟨3, ![![-1, -2, 3], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]], -6⟩

def term6 : Term := ⟨4, ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, 1, -1, -1], ![1, 1, -1, -1]], 12⟩

def term7 : Term := ⟨4, ![![-1, -2, 2, 1], ![-1, -1, 0, 2], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, 1, -1, -1], ![1, 1, -1, -1]], 6⟩

def term8 : Term := ⟨4, ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![1, 1, 0, -2], ![1, 1, -1, -1]], 6⟩

def term9 : Term := ⟨4, ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![1, 1, -1, -1], ![1, 1, 0, -2]], 6⟩

def term10 : Term := ⟨3, ![![-2, -1, 3], ![0, -2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]], -3⟩

def term11 : Term := ⟨4, ![![-2, -1, 1, 2], ![0, -2, 1, 1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, 1, -1, -1], ![1, 1, -1, -1]], 6⟩

def term12 : Term := ⟨4, ![![-2, -1, 2, 1], ![0, -2, 0, 2], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, 1, -1, -1], ![1, 1, -1, -1]], 3⟩

def term13 : Term := ⟨4, ![![-2, -1, 1, 2], ![0, -2, 1, 1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![1, 1, 0, -2], ![1, 1, -1, -1]], 3⟩

def term14 : Term := ⟨4, ![![-2, -1, 1, 2], ![0, -2, 1, 1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![1, 1, -1, -1], ![1, 1, 0, -2]], 3⟩

def term15 : Term := ⟨3, ![![-1, -2, 3], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![1, 1, -2]], -3⟩

def term16 : Term := ⟨4, ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![0, 0, 0, 0], ![1, 0, 0, -1], ![0, 2, -1, -1], ![1, 1, -1, -1]], 6⟩

def term17 : Term := ⟨4, ![![-1, -2, 2, 1], ![-1, -1, 0, 2], ![0, 0, 0, 0], ![1, 0, 0, -1], ![0, 2, -1, -1], ![1, 1, -1, -1]], 3⟩

def term18 : Term := ⟨4, ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![0, 0, 0, 0], ![1, 0, -1, 0], ![0, 2, 0, -2], ![1, 1, -1, -1]], 3⟩

def term19 : Term := ⟨4, ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![0, 0, 0, 0], ![1, 0, -1, 0], ![0, 2, -1, -1], ![1, 1, 0, -2]], 3⟩

def term20 : Term := ⟨3, ![![-1, -2, 3], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![0, 2, -2]], -3⟩

def term21 : Term := ⟨4, ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![0, 0, 0, 0], ![1, 0, 0, -1], ![1, 1, -1, -1], ![0, 2, -1, -1]], 6⟩

def term22 : Term := ⟨4, ![![-1, -2, 2, 1], ![-1, -1, 0, 2], ![0, 0, 0, 0], ![1, 0, 0, -1], ![1, 1, -1, -1], ![0, 2, -1, -1]], 3⟩

def term23 : Term := ⟨4, ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![0, 0, 0, 0], ![1, 0, -1, 0], ![1, 1, 0, -2], ![0, 2, -1, -1]], 3⟩

def term24 : Term := ⟨4, ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![0, 0, 0, 0], ![1, 0, -1, 0], ![1, 1, -1, -1], ![0, 2, 0, -2]], 3⟩

def term25 : Term := ⟨4, ![![1, 2, -1, -2], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-1, -2, 1, 2], ![-1, 0, 1, 0], ![-1, 0, 1, 0]], 1⟩

def term26 : Term := ⟨4, ![![1, 2, -1, -2], ![1, -2, -1, 2], ![1, 0, -1, 0], ![-1, 0, 1, 0], ![-1, 0, 1, 0], ![-1, 0, 1, 0]], 1⟩

def terms0 (i : Fin 26) : Term :=
  (#[term0, term1, term2, term3, term4, term5, term6, term7, term8, term9, term10, term11, term12, term13, term14, term15, term16, term17, term18, term19, term20, term21, term22, term23, term24, term25])[i.val]!

noncomputable def expanded0 (H : CMatrix) : ℝ := ∑ i : Fin 26, weightedAverage H (terms0 i)

def terms1 (i : Fin 26) : Term :=
  (#[term0, term1, term2, term3, term4, term5, term6, term7, term8, term9, term10, term11, term12, term13, term14, term15, term16, term17, term18, term19, term20, term21, term22, term23, term24, term26])[i.val]!

noncomputable def expanded1 (H : CMatrix) : ℝ := ∑ i : Fin 26, weightedAverage H (terms1 i)

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairPolynomial_Terms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace MUB6.Certificate.PairTargetSemantics

def termPolynomial (H : CMatrix) (t : Term) : ℂ :=
  (t.coefficient : ℂ) * ∏ j, g H (fun i => t.charges i j)

end MUB6.Certificate.PairTargetSemantics

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairPolynomial_Grid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace MUB6.Certificate.PairTargetSemantics

def termGrid : Fin 5 → Fin 5 → Term :=
  ![![term0, term1, term2, term3, term4], ![term5, term6, term7, term8, term9], ![term10, term11, term12, term13, term14], ![term15, term16, term17, term18, term19], ![term20, term21, term22, term23, term24]]

def pairSummand (H : CMatrix) : Fin 5 → ℂ :=
  ![-g H pairW, 2 * g H (pairA 0) * g H (pairW - pairA 0),
    g H (pairA 1) * g H (pairW - pairA 1),
    g H (pairA 2) * g H (pairW - pairA 2),
    g H (pairA 3) * g H (pairW - pairA 3)]

end MUB6.Certificate.PairTargetSemantics

end

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

def value4 : Sparse (Fin 909) := [(1, (1 / 1))]

def value5 : Sparse (Fin 909) := [(0, (-1 / 5))]

def value6 : Sparse (Fin 909) := [(6, (-1 / 4)), (58, (-1 / 4))]

def value7 : Sparse (Fin 909) := [(9, (1 / 1))]

def value8 : Sparse (Fin 909) := [(2, (-1 / 4)), (6, (-1 / 4))]

def value9 : Sparse (Fin 909) := [(5, (1 / 1))]

def value33 : Sparse (Fin 909) := [(82, (1 / 1))]

def value34 : Sparse (Fin 909) := [(310, (1 / 1))]

def value35 : Sparse (Fin 909) := [(8, (1 / 1))]

def value36 : Sparse (Fin 909) := [(3, (1 / 1))]

def value37 : Sparse (Fin 909) := [(13, (1 / 1))]

def value38 : Sparse (Fin 909) := [(128, (1 / 1))]

def value39 : Sparse (Fin 909) := [(495, (1 / 1))]

def value40 : Sparse (Fin 909) := [(52, (1 / 1))]

def value41 : Sparse (Fin 909) := [(12, (1 / 1))]

def value42 : Sparse (Fin 909) := [(11, (1 / 1))]

def value43 : Sparse (Fin 909) := [(26, (1 / 1))]

def value44 : Sparse (Fin 909) := [(4, (1 / 1))]

def value45 : Sparse (Fin 909) := [(27, (1 / 1))]

def value46 : Sparse (Fin 909) := [(0, (-1 / 60)), (1, (-1 / 6)), (2, (1 / 12))]

def value47 : Sparse (Fin 909) := [(2, (1 / 16)), (6, (1 / 8)), (58, (1 / 16))]

def value48 : Sparse (Fin 909) := [(5, (-1 / 4)), (9, (-1 / 4))]

def value49 : Sparse (Fin 909) := [(2, (1 / 16)), (6, (1 / 16)), (9, (-1 / 4))]

def value50 : Sparse (Fin 909) := [(6, (-3 / 16)), (58, (1 / 16))]

def value51 : Sparse (Fin 909) := [(1, (1 / 16)), (2, (1 / 8)), (6, (1 / 16))]

def value52 : Sparse (Fin 909) := [(1, (1 / 16)), (2, (1 / 16)), (5, (-1 / 4))]

def value53 : Sparse (Fin 909) := [(2, (-3 / 16)), (6, (1 / 16))]

def value54 : Sparse (Fin 909) := [(2, (1 / 16)), (6, (-3 / 16))]

def value55 : Sparse (Fin 909) := [(6, (1 / 16)), (9, (-1 / 4)), (58, (1 / 16))]

def value56 : Sparse (Fin 909) := [(0, (-1 / 80)), (1, (1 / 8)), (2, (1 / 16))]

def value57 : Sparse (Fin 909) := [(1, (-3 / 16)), (2, (1 / 16))]

def value58 : Sparse (Fin 909) := [(1, (1 / 16)), (2, (-3 / 16))]

def value59 : Sparse (Fin 909) := [(2, (1 / 16)), (5, (-1 / 4)), (6, (1 / 16))]

def value60 : Sparse (Fin 909) := [(9, (-1 / 2))]

def value61 : Sparse (Fin 909) := [(0, (3 / 80)), (1, (1 / 16))]

def value62 : Sparse (Fin 909) := [(0, (-1 / 80)), (1, (-3 / 16))]

def value63 : Sparse (Fin 909) := [(1, (1 / 8)), (2, (1 / 8))]

end MUB6.Certificate.PairSemantics

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

def value64 : Sparse (Fin 909) := [(0, (1 / 10))]

def value65 : Sparse (Fin 909) := [(0, (7 / 60)), (1, (1 / 12))]

def value66 : Sparse (Fin 909) := [(1, (-1 / 24)), (2, (-1 / 8)), (5, (1 / 2)), (6, (-1 / 8)), (9, (5 / 6)), (58, (-1 / 24))]

def value67 : Sparse (Fin 909) := [(1, (-1 / 24)), (2, (1 / 8)), (5, (1 / 6)), (6, (1 / 8)), (9, (1 / 6)), (58, (-1 / 24))]

def value68 : Sparse (Fin 909) := [(1, (-1 / 12)), (2, (-1 / 6)), (6, (-1 / 12)), (9, (1 / 3))]

def value69 : Sparse (Fin 909) := [(0, (1 / 120)), (1, (-1 / 4)), (2, (-1 / 3)), (5, (1 / 2)), (6, (-1 / 8))]

def value70 : Sparse (Fin 909) := [(35, (-1 / 3)), (70, (-1 / 3)), (257, (-1 / 3))]

def value71 : Sparse (Fin 909) := [(2, (-1 / 48)), (5, (1 / 6)), (6, (-1 / 48)), (9, (1 / 4))]

def value72 : Sparse (Fin 909) := [(52, (-1 / 3)), (69, (-1 / 3)), (495, (-1 / 3))]

def value73 : Sparse (Fin 909) := [(69, (-1 / 3)), (70, (-1 / 3)), (71, (-1 / 3))]

def value74 : Sparse (Fin 909) := [(256, (1 / 1))]

def value75 : Sparse (Fin 909) := [(69, (-1 / 3)), (70, (-1 / 3)), (257, (-1 / 3))]

def value76 : Sparse (Fin 909) := [(35, (-1 / 3)), (257, (-1 / 3)), (495, (-1 / 3))]

def value77 : Sparse (Fin 909) := [(2, (-1 / 48)), (5, (1 / 12)), (6, (-1 / 48)), (9, (1 / 6)), (495, (-1 / 3))]

def value78 : Sparse (Fin 909) := [(69, (-1 / 3)), (71, (-2 / 3))]

def value79 : Sparse (Fin 909) := [(35, (-1 / 3)), (60, (-1 / 3)), (257, (-1 / 3))]

def value80 : Sparse (Fin 909) := [(52, (-1 / 3)), (128, (-1 / 3)), (495, (-1 / 3))]

def value81 : Sparse (Fin 909) := [(13, (-1 / 3)), (35, (-1 / 3)), (60, (-1 / 3))]

def value82 : Sparse (Fin 909) := [(2, (-1 / 48)), (5, (1 / 12)), (6, (-1 / 48)), (35, (-1 / 3)), (495, (-1 / 3))]

def value83 : Sparse (Fin 909) := [(13, (-1 / 3)), (52, (-1 / 3)), (128, (-1 / 3))]

def value84 : Sparse (Fin 909) := [(259, (1 / 1))]

def value85 : Sparse (Fin 909) := [(59, (1 / 1))]

def value86 : Sparse (Fin 909) := [(260, (1 / 1))]

def value87 : Sparse (Fin 909) := [(35, (-1 / 3)), (52, (-1 / 3)), (60, (-1 / 3))]

def value88 : Sparse (Fin 909) := [(13, (-1 / 3)), (60, (-1 / 3)), (128, (-1 / 3))]

def value89 : Sparse (Fin 909) := [(262, (1 / 1))]

def value90 : Sparse (Fin 909) := [(2, (-1 / 24)), (5, (1 / 6)), (6, (-1 / 24)), (128, (-1 / 3))]

def value91 : Sparse (Fin 909) := [(264, (1 / 1))]

def value92 : Sparse (Fin 909) := [(13, (-1 / 3)), (32, (-1 / 3)), (60, (-1 / 3))]

def value93 : Sparse (Fin 909) := [(13, (-2 / 3)), (32, (-1 / 3))]

def value94 : Sparse (Fin 909) := [(35, (-1 / 3)), (67, (-1 / 3)), (257, (-1 / 3))]

def value95 : Sparse (Fin 909) := [(13, (-1 / 3)), (34, (-1 / 3)), (60, (-1 / 3))]

def value96 : Sparse (Fin 909) := [(266, (1 / 1))]

def value97 : Sparse (Fin 909) := [(61, (1 / 1))]

def value98 : Sparse (Fin 909) := [(62, (1 / 1))]

def value99 : Sparse (Fin 909) := [(267, (1 / 1))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value640 : Sparse (Fin 909) := [(1, (-1 / 32)), (2, (1 / 96)), (3, (1 / 6)), (7, (1 / 6)), (24, (-1 / 2)), (126, (-1 / 2)), (197, (-1 / 2))]

def value641 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (1 / 24)), (2, (1 / 48)), (3, (1 / 3)), (7, (1 / 6)), (12, (1 / 6)), (23, (-1 / 2))]

def value642 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 32)), (3, (1 / 6)), (12, (1 / 6)), (23, (-1 / 2)), (25, (-1 / 2)), (54, (-1 / 2))]

def value644 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (1 / 96)), (3, (1 / 6)), (5, (-1 / 24)), (7, (1 / 6)), (35, (1 / 3)), (52, (1 / 6)), (228, (-1 / 2)), (726, (-1 / 2))]

def value645 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 16)), (2, (5 / 96)), (3, (1 / 2)), (5, (-1 / 24)), (7, (1 / 3)), (26, (1 / 6)), (35, (1 / 6))]

def value646 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-11 / 96)), (2, (1 / 48)), (3, (1 / 3)), (4, (1 / 6)), (7, (1 / 6)), (24, (-1 / 2))]

def value647 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 48)), (2, (1 / 96)), (23, (-1 / 2)), (24, (-1 / 2)), (27, (1 / 8)), (55, (-1 / 2))]

def value648 : Sparse (Fin 909) := [(1, (-1 / 32)), (2, (-1 / 32)), (3, (1 / 6)), (5, (-1 / 24)), (7, (1 / 6)), (13, (1 / 6)), (35, (1 / 6)), (54, (-1 / 2))]

def value649 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (1 / 48)), (5, (1 / 12)), (6, (1 / 96)), (199, (-1 / 2)), (201, (-1 / 2)), (726, (-1 / 2))]

def value650 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 24)), (6, (1 / 48)), (7, (1 / 6)), (35, (1 / 3)), (82, (1 / 6)), (199, (-1 / 2))]

def value651 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 32)), (3, (1 / 3)), (12, (1 / 3)), (13, (1 / 2)), (35, (1 / 6)), (54, (-1 / 2))]

def value652 : Sparse (Fin 909) := [(3, (1 / 6)), (35, (1 / 3)), (52, (1 / 3)), (278, (1 / 6)), (310, (1 / 6)), (495, (1 / 3)), (726, (-1 / 2))]

def value653 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (1 / 48)), (2, (1 / 16)), (3, (1 / 3)), (5, (-1 / 12)), (6, (1 / 96)), (7, (1 / 6)), (35, (1 / 3)), (52, (1 / 3))]

def value654 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-1 / 16)), (2, (1 / 24)), (8, (1 / 6)), (24, (-1 / 2))]

def value655 : Sparse (Fin 909) := [(0, (1 / 160)), (1, (1 / 16)), (2, (1 / 96)), (3, (1 / 6)), (12, (1 / 6))]

def value656 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-1 / 16)), (3, (1 / 3)), (13, (1 / 3))]

def value657 : Sparse (Fin 909) := [(3, (1 / 6)), (11, (1 / 6)), (26, (1 / 6)), (52, (1 / 6)), (278, (1 / 6)), (495, (1 / 6))]

def value658 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 96)), (2, (1 / 48)), (4, (1 / 6)), (26, (1 / 6)), (35, (1 / 6)), (52, (1 / 6))]

def value659 : Sparse (Fin 909) := [(0, (1 / 80)), (1, (1 / 96)), (2, (1 / 32)), (3, (1 / 6)), (4, (1 / 6))]

def value660 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-1 / 16)), (3, (1 / 3)), (4, (1 / 6)), (12, (1 / 6)), (51, (-1 / 2)), (55, (-1 / 2))]

def value661 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-1 / 6)), (2, (1 / 48)), (3, (1 / 3)), (12, (1 / 3))]

def value662 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (1 / 48)), (2, (1 / 96)), (3, (1 / 3)), (12, (1 / 6)), (13, (1 / 2)), (35, (1 / 6)), (52, (1 / 6))]

def value663 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (1 / 96)), (2, (1 / 32)), (3, (1 / 3)), (12, (1 / 6)), (13, (1 / 2))]

def value664 : Sparse (Fin 909) := [(1, (1 / 96)), (5, (-1 / 12)), (6, (-1 / 96)), (13, (1 / 6)), (35, (1 / 3)), (82, (1 / 3)), (128, (1 / 6)), (278, (1 / 6)), (495, (1 / 6))]

def value665 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 24)), (3, (1 / 6)), (5, (-1 / 12)), (6, (1 / 48)), (13, (1 / 6)), (35, (1 / 6)), (52, (1 / 6)), (82, (1 / 6)), (128, (1 / 6)), (201, (-1 / 2))]

def value666 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 32)), (3, (1 / 2)), (4, (1 / 3)), (26, (1 / 3)), (35, (1 / 6)), (55, (-1 / 2))]

def value667 : Sparse (Fin 909) := [(0, (1 / 80)), (1, (-7 / 48)), (3, (1 / 3)), (4, (1 / 3)), (12, (1 / 6))]

def value668 : Sparse (Fin 909) := [(0, (1 / 24)), (1, (-5 / 24)), (12, (1 / 6))]

def value669 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-5 / 96)), (2, (-1 / 48)), (3, (1 / 3)), (12, (1 / 6)), (13, (1 / 6)), (26, (1 / 6)), (35, (1 / 6)), (55, (-1 / 2))]

def value670 : Sparse (Fin 909) := [(0, (-1 / 120)), (1, (-5 / 48)), (2, (1 / 48)), (3, (1 / 2)), (4, (1 / 6)), (12, (1 / 3)), (13, (1 / 6))]

def value671 : Sparse (Fin 909) := [(1, (1 / 24)), (2, (-1 / 32)), (3, (1 / 6)), (5, (-1 / 24)), (6, (1 / 96)), (13, (1 / 3)), (26, (1 / 6)), (35, (1 / 2)), (82, (1 / 6))]

def value672 : Sparse (Fin 909) := [(1, (1 / 24)), (2, (1 / 24)), (3, (1 / 3)), (13, (1 / 3)), (56, (-1 / 2)), (201, (-1 / 2))]

def value673 : Sparse (Fin 909) := [(735, (1 / 1))]

def value674 : Sparse (Fin 909) := [(736, (1 / 1))]

def value675 : Sparse (Fin 909) := [(737, (1 / 1))]

def value676 : Sparse (Fin 909) := [(738, (1 / 1))]

def value677 : Sparse (Fin 909) := [(739, (1 / 1))]

def value678 : Sparse (Fin 909) := [(203, (1 / 1))]

def value679 : Sparse (Fin 909) := [(745, (1 / 1))]

def value680 : Sparse (Fin 909) := [(204, (1 / 1))]

def value681 : Sparse (Fin 909) := [(751, (1 / 1))]

def value682 : Sparse (Fin 909) := [(753, (1 / 1))]

def value683 : Sparse (Fin 909) := [(205, (1 / 1))]

def value684 : Sparse (Fin 909) := [(207, (1 / 1))]

def value685 : Sparse (Fin 909) := [(208, (1 / 1))]

def value686 : Sparse (Fin 909) := [(209, (1 / 1))]

def value687 : Sparse (Fin 909) := [(760, (1 / 1))]

def value688 : Sparse (Fin 909) := [(764, (1 / 1))]

def value689 : Sparse (Fin 909) := [(216, (1 / 1))]

def value690 : Sparse (Fin 909) := [(217, (1 / 1))]

def value691 : Sparse (Fin 909) := [(783, (1 / 1))]

def value692 : Sparse (Fin 909) := [(784, (1 / 1))]

def value693 : Sparse (Fin 909) := [(794, (1 / 1))]

def value694 : Sparse (Fin 909) := [(1, (1 / 32)), (2, (-1 / 48)), (5, (-1 / 12)), (6, (1 / 32)), (11, (1 / 6)), (35, (1 / 3)), (52, (1 / 6)), (721, (-1 / 2))]

def value695 : Sparse (Fin 909) := [(1, (1 / 32)), (2, (1 / 32)), (5, (-1 / 24)), (52, (1 / 6)), (81, (-1 / 2)), (228, (-1 / 2)), (490, (-1 / 2))]

def value696 : Sparse (Fin 909) := [(1, (-1 / 96)), (2, (-1 / 12)), (3, (1 / 6)), (6, (1 / 96)), (11, (1 / 6)), (13, (1 / 6)), (26, (1 / 3)), (35, (1 / 2))]

def value697 : Sparse (Fin 909) := [(0, (-1 / 480)), (2, (-1 / 96)), (3, (1 / 3)), (4, (1 / 6)), (13, (1 / 6)), (26, (1 / 6)), (35, (1 / 6)), (56, (-1 / 2))]

def value698 : Sparse (Fin 909) := [(1, (-1 / 96)), (2, (-1 / 96)), (5, (-1 / 24)), (54, (-1 / 2)), (56, (-1 / 2)), (228, (-1 / 2))]

def value699 : Sparse (Fin 909) := [(1, (-1 / 12)), (2, (-1 / 12)), (3, (1 / 6)), (26, (1 / 3)), (35, (1 / 6)), (54, (-1 / 2))]

def value700 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 24)), (6, (1 / 48)), (11, (1 / 6)), (26, (1 / 6)), (35, (1 / 3)), (226, (-1 / 2))]

def value701 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (-1 / 96)), (3, (1 / 6)), (5, (-1 / 24)), (6, (1 / 96)), (7, (1 / 6)), (11, (1 / 6)), (26, (1 / 6)), (35, (1 / 3)), (228, (-1 / 2))]

def value702 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 12)), (2, (-1 / 96)), (3, (1 / 2)), (4, (1 / 6)), (7, (1 / 6)), (26, (1 / 3)), (35, (1 / 6))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value704 : Sparse (Fin 909) := [(1, (-1 / 6)), (3, (1 / 3)), (12, (1 / 3)), (25, (-1 / 2))]

def value705 : Sparse (Fin 909) := [(1, (-11 / 96)), (2, (1 / 96)), (3, (1 / 2)), (4, (1 / 3)), (12, (1 / 6)), (26, (1 / 6))]

def value706 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (1 / 24)), (2, (1 / 48)), (3, (1 / 3)), (4, (1 / 6)), (25, (-1 / 2)), (26, (1 / 6))]

def value707 : Sparse (Fin 909) := [(3, (1 / 3)), (4, (1 / 6)), (11, (1 / 6)), (26, (1 / 3)), (35, (1 / 3)), (52, (1 / 6)), (228, (-1 / 2))]

def value708 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 16)), (2, (1 / 32)), (3, (1 / 2)), (4, (1 / 3)), (26, (1 / 3))]

def value709 : Sparse (Fin 909) := [(0, (13 / 480)), (1, (-1 / 8)), (2, (1 / 96)), (3, (1 / 6)), (4, (1 / 3))]

def value710 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-5 / 96)), (3, (1 / 3)), (26, (1 / 6))]

def value711 : Sparse (Fin 909) := [(0, (3 / 160)), (1, (-13 / 96)), (4, (1 / 6))]

def value712 : Sparse (Fin 909) := [(798, (1 / 1))]

def value713 : Sparse (Fin 909) := [(810, (1 / 1))]

def value714 : Sparse (Fin 909) := [(811, (1 / 1))]

def value715 : Sparse (Fin 909) := [(0, (-1 / 30)), (2, (1 / 2)), (5, (-2 / 3)), (27, (1 / 1)), (68, (2 / 1))]

def value716 : Sparse (Fin 909) := [(0, (1 / 12)), (1, (-3 / 4)), (2, (2 / 3)), (5, (-1 / 2)), (27, (3 / 2))]

def value717 : Sparse (Fin 909) := [(0, (3 / 40)), (1, (-1 / 12)), (5, (-1 / 3)), (6, (1 / 24)), (27, (1 / 2))]

def value718 : Sparse (Fin 909) := [(812, (1 / 1))]

def value719 : Sparse (Fin 909) := [(230, (1 / 1))]

def value720 : Sparse (Fin 909) := [(231, (1 / 1))]

def value721 : Sparse (Fin 909) := [(1, (1 / 32)), (2, (1 / 16)), (5, (-1 / 6)), (6, (1 / 32)), (9, (-1 / 12)), (52, (1 / 6)), (310, (1 / 6)), (495, (1 / 6)), (818, (-1 / 2))]

def value722 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (-1 / 96)), (5, (-1 / 12)), (6, (-1 / 96)), (9, (-1 / 12)), (35, (1 / 6)), (58, (1 / 96)), (278, (1 / 6)), (495, (1 / 3))]

def value723 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (7 / 96)), (2, (11 / 96)), (5, (-1 / 4)), (6, (1 / 16)), (9, (-5 / 24)), (58, (1 / 96))]

def value724 : Sparse (Fin 909) := [(1, (-1 / 96)), (2, (-1 / 96)), (5, (-1 / 24)), (6, (1 / 96)), (9, (-5 / 24)), (58, (1 / 96))]

def value725 : Sparse (Fin 909) := [(33, (-1 / 3)), (54, (-1 / 3)), (721, (-1 / 3))]

def value726 : Sparse (Fin 909) := [(3, (1 / 9)), (12, (2 / 9)), (13, (1 / 3)), (59, (-1 / 3))]

def value727 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (-1 / 48)), (13, (1 / 9)), (35, (1 / 9)), (63, (-1 / 3)), (721, (-1 / 3))]

def value728 : Sparse (Fin 909) := [(33, (-1 / 3)), (55, (-1 / 3)), (306, (-1 / 3))]

def value729 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 72)), (13, (2 / 9)), (63, (-1 / 3)), (306, (-1 / 3))]

def value730 : Sparse (Fin 909) := [(3, (2 / 9)), (4, (2 / 9)), (26, (2 / 9)), (81, (-1 / 3))]

def value731 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 36)), (2, (1 / 48)), (3, (1 / 9)), (33, (-1 / 3)), (81, (-1 / 3))]

def value732 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (-5 / 96)), (5, (-1 / 8)), (6, (1 / 96)), (9, (-1 / 24)), (71, (1 / 6))]

def value733 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (5 / 48)), (2, (5 / 48)), (5, (-1 / 6)), (6, (1 / 48)), (8, (1 / 3)), (71, (1 / 3))]

def value734 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (5 / 48)), (6, (-1 / 32)), (9, (-1 / 24)), (35, (1 / 6)), (70, (1 / 6))]

def value735 : Sparse (Fin 909) := [(1, (1 / 16)), (2, (1 / 16)), (5, (-5 / 24)), (6, (1 / 24)), (8, (1 / 6)), (9, (-1 / 12)), (71, (1 / 3))]

def value736 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (-1 / 24)), (5, (-1 / 8)), (6, (-1 / 48)), (52, (1 / 6))]

def value737 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (1 / 12)), (2, (1 / 12)), (5, (-1 / 6)), (6, (1 / 48)), (8, (1 / 6)), (52, (1 / 6))]

def value738 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (1 / 48)), (5, (1 / 12)), (6, (1 / 96)), (7, (1 / 6)), (8, (1 / 6)), (35, (1 / 6))]

def value739 : Sparse (Fin 909) := [(1, (-5 / 96)), (2, (-1 / 16)), (5, (-1 / 8)), (6, (1 / 32)), (7, (1 / 6)), (35, (1 / 6))]

def value740 : Sparse (Fin 909) := [(1, (1 / 48)), (5, (-1 / 24)), (6, (-1 / 16)), (11, (1 / 6)), (35, (1 / 6))]

def value741 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (3 / 32)), (2, (11 / 96)), (3, (1 / 6)), (5, (-1 / 6)), (6, (1 / 32)), (35, (1 / 6)), (52, (1 / 3))]

def value742 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (1 / 96)), (2, (1 / 96)), (3, (1 / 6)), (5, (-1 / 12)), (6, (1 / 96)), (35, (1 / 6)), (52, (1 / 3))]

def value743 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 24)), (6, (1 / 48)), (52, (1 / 6)), (228, (-1 / 2))]

def value744 : Sparse (Fin 909) := [(2, (-1 / 12)), (5, (-1 / 12)), (11, (1 / 6)), (26, (1 / 6)), (35, (1 / 3))]

def value745 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (-3 / 32)), (6, (-3 / 32)), (11, (1 / 3)), (35, (1 / 6)), (58, (1 / 96)), (278, (1 / 6))]

def value746 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 96)), (2, (-5 / 96)), (5, (-1 / 12)), (6, (-1 / 48)), (9, (-1 / 24)), (58, (1 / 96))]

def value747 : Sparse (Fin 909) := [(1, (-1 / 96)), (2, (1 / 96)), (5, (-1 / 24)), (6, (-5 / 96)), (9, (-1 / 24)), (58, (1 / 96))]

def value748 : Sparse (Fin 909) := [(0, (1 / 480)), (2, (1 / 24)), (5, (-1 / 8)), (6, (1 / 32))]

def value749 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 24)), (2, (-1 / 16)), (5, (1 / 24)), (6, (-1 / 96))]

def value750 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 36)), (2, (1 / 48)), (5, (-1 / 18)), (8, (2 / 9)), (69, (1 / 9)), (71, (1 / 3))]

def value751 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (1 / 48)), (5, (-1 / 18)), (7, (2 / 9)), (69, (2 / 9)), (70, (1 / 9)), (71, (1 / 9))]

def value752 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 72)), (5, (-1 / 18)), (7, (1 / 9)), (8, (1 / 9)), (69, (1 / 9)), (71, (1 / 9)), (256, (-1 / 3))]

def value753 : Sparse (Fin 909) := [(3, (1 / 9)), (7, (1 / 9)), (35, (1 / 9)), (256, (-1 / 3)), (277, (-1 / 3))]

def value754 : Sparse (Fin 909) := [(7, (-1 / 9)), (69, (2 / 9)), (70, (2 / 9))]

def value755 : Sparse (Fin 909) := [(8, (-1 / 9)), (71, (4 / 9))]

def value756 : Sparse (Fin 909) := [(33, (-1 / 3)), (81, (-1 / 3)), (490, (-1 / 3))]

def value757 : Sparse (Fin 909) := [(33, (-1 / 3)), (306, (-1 / 3)), (721, (-1 / 3))]

def value758 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 144)), (5, (-1 / 36)), (35, (1 / 9)), (52, (1 / 9)), (123, (-1 / 3)), (721, (-1 / 3))]

def value759 : Sparse (Fin 909) := [(3, (1 / 9)), (26, (1 / 9)), (34, (1 / 9)), (273, (-1 / 3)), (490, (-1 / 3))]

def value760 : Sparse (Fin 909) := [(1, (-1 / 72)), (2, (-1 / 144)), (3, (1 / 9)), (5, (-1 / 36)), (6, (1 / 144)), (7, (2 / 9)), (35, (1 / 9)), (69, (1 / 9)), (70, (1 / 9))]

def value761 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (7 / 144)), (2, (1 / 24)), (5, (-1 / 18)), (6, (1 / 144)), (8, (2 / 9)), (71, (2 / 9))]

def value762 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (7 / 144)), (2, (1 / 24)), (5, (-1 / 12)), (8, (1 / 9)), (52, (1 / 9)), (69, (1 / 9)), (71, (1 / 9))]

def value763 : Sparse (Fin 909) := [(1, (-1 / 72)), (2, (1 / 72)), (3, (1 / 9)), (5, (-1 / 36)), (7, (2 / 9)), (35, (1 / 9)), (52, (1 / 9)), (69, (1 / 9)), (70, (1 / 9))]

def value764 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (1 / 72)), (5, (-1 / 12)), (6, (1 / 144)), (7, (1 / 9)), (69, (1 / 9)), (71, (1 / 9))]

def value765 : Sparse (Fin 909) := [(3, (2 / 9)), (7, (1 / 9)), (12, (1 / 9)), (13, (2 / 9)), (35, (2 / 9)), (60, (1 / 9))]

def value766 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (7 / 144)), (2, (1 / 18)), (5, (-1 / 18)), (8, (1 / 9)), (52, (1 / 9))]

def value767 : Sparse (Fin 909) := [(1, (5 / 144)), (2, (1 / 24)), (3, (1 / 9)), (5, (-1 / 18)), (6, (1 / 144)), (13, (1 / 9)), (52, (2 / 9)), (128, (1 / 9))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value768 : Sparse (Fin 909) := [(3, (1 / 9)), (12, (1 / 9)), (13, (1 / 3)), (35, (1 / 9)), (52, (1 / 9)), (82, (1 / 9)), (128, (1 / 9))]

def value769 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 48)), (2, (1 / 36)), (3, (2 / 9)), (5, (-1 / 36)), (7, (1 / 9)), (35, (1 / 9)), (52, (1 / 9))]

def value770 : Sparse (Fin 909) := [(51, (-1 / 3)), (259, (-1 / 3)), (308, (-1 / 3))]

def value771 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 144)), (2, (1 / 36)), (3, (1 / 9)), (5, (-1 / 18)), (7, (2 / 9)), (8, (1 / 9)), (35, (1 / 9))]

def value772 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 144)), (5, (-1 / 36)), (7, (1 / 9)), (8, (1 / 9)), (51, (-1 / 3)), (59, (-1 / 3))]

def value773 : Sparse (Fin 909) := [(3, (1 / 9)), (10, (-1 / 3)), (12, (1 / 9)), (13, (1 / 9)), (59, (-1 / 3))]

def value774 : Sparse (Fin 909) := [(3, (-1 / 9)), (7, (1 / 9)), (35, (2 / 9)), (52, (1 / 9))]

def value775 : Sparse (Fin 909) := [(1, (-1 / 72)), (2, (1 / 72)), (3, (1 / 9)), (5, (-1 / 36)), (7, (-1 / 9)), (35, (1 / 9))]

def value776 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 144)), (5, (-1 / 36)), (7, (1 / 9)), (69, (1 / 9)), (124, (-1 / 3)), (259, (-1 / 3))]

def value777 : Sparse (Fin 909) := [(3, (1 / 9)), (13, (2 / 9)), (34, (1 / 9)), (35, (1 / 9)), (60, (1 / 9)), (273, (-1 / 3))]

def value778 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 72)), (13, (1 / 9)), (52, (1 / 9)), (260, (-1 / 3)), (309, (-1 / 3))]

def value779 : Sparse (Fin 909) := [(1, (1 / 36)), (2, (-1 / 48)), (5, (-1 / 36)), (6, (1 / 144)), (13, (1 / 9)), (35, (2 / 9)), (52, (1 / 9)), (60, (1 / 9))]

def value780 : Sparse (Fin 909) := [(1, (1 / 48)), (5, (-1 / 36)), (6, (1 / 144)), (13, (2 / 9)), (35, (1 / 9)), (52, (1 / 9)), (60, (1 / 9)), (128, (1 / 9))]

def value781 : Sparse (Fin 909) := [(13, (-1 / 9)), (35, (1 / 9)), (60, (1 / 9)), (82, (1 / 9)), (128, (1 / 9))]

def value782 : Sparse (Fin 909) := [(3, (1 / 9)), (13, (1 / 9)), (35, (-1 / 9)), (52, (1 / 9)), (60, (1 / 9))]

def value783 : Sparse (Fin 909) := [(7, (1 / 9)), (35, (1 / 9)), (70, (1 / 9)), (125, (-1 / 3)), (260, (-1 / 3))]

def value784 : Sparse (Fin 909) := [(51, (-1 / 3)), (262, (-1 / 3)), (309, (-1 / 3))]

def value785 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 72)), (3, (1 / 9)), (52, (1 / 9)), (262, (-1 / 3)), (308, (-1 / 3))]

def value786 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 36)), (2, (1 / 24)), (5, (-1 / 12)), (7, (1 / 9)), (8, (2 / 9))]

def value787 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 24)), (2, (1 / 36)), (5, (-1 / 18)), (8, (-1 / 9))]

def value788 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 144)), (5, (-1 / 36)), (8, (1 / 9)), (71, (1 / 9)), (126, (-1 / 3)), (262, (-1 / 3))]

def value789 : Sparse (Fin 909) := [(23, (-1 / 3)), (124, (-1 / 3)), (196, (-1 / 3))]

def value790 : Sparse (Fin 909) := [(24, (-1 / 3)), (126, (-1 / 3)), (197, (-1 / 3))]

def value791 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (1 / 144)), (3, (1 / 9)), (7, (1 / 9)), (125, (-1 / 3)), (126, (-1 / 3))]

def value792 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 72)), (5, (-1 / 18)), (7, (1 / 9)), (35, (1 / 9)), (52, (1 / 9)), (69, (1 / 9)), (260, (-1 / 3))]

def value793 : Sparse (Fin 909) := [(23, (-1 / 3)), (125, (-2 / 3))]

def value794 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (1 / 144)), (3, (1 / 9)), (7, (1 / 9)), (124, (-1 / 3)), (197, (-1 / 3))]

def value795 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 144)), (5, (-1 / 36)), (7, (-1 / 9)), (35, (1 / 9)), (69, (1 / 9)), (70, (1 / 9))]

def value796 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-5 / 144)), (2, (-1 / 72)), (3, (2 / 9)), (7, (1 / 9)), (12, (1 / 9)), (13, (1 / 9)), (35, (1 / 9))]

def value797 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 24)), (2, (1 / 18)), (3, (1 / 9)), (5, (-1 / 36)), (13, (1 / 9)), (52, (1 / 9))]

def value798 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 48)), (3, (1 / 9)), (5, (-1 / 36)), (6, (1 / 144)), (13, (1 / 9)), (35, (1 / 9)), (52, (2 / 9)), (60, (1 / 9)), (128, (1 / 9))]

def value799 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 144)), (2, (1 / 72)), (3, (2 / 9)), (12, (1 / 9)), (13, (2 / 9)), (35, (1 / 9)), (52, (1 / 9))]

def value800 : Sparse (Fin 909) := [(0, (-1 / 720)), (2, (-1 / 144)), (3, (2 / 9)), (4, (1 / 9)), (26, (1 / 9)), (35, (1 / 9)), (52, (1 / 9))]

def value801 : Sparse (Fin 909) := [(0, (-1 / 240)), (2, (5 / 144)), (3, (2 / 9)), (4, (1 / 9)), (13, (1 / 9))]

def value802 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-1 / 36)), (2, (1 / 72)), (3, (2 / 9)), (12, (2 / 9)), (13, (2 / 9))]

def value803 : Sparse (Fin 909) := [(1, (-1 / 18)), (2, (-1 / 36)), (3, (1 / 9)), (5, (-1 / 36)), (7, (1 / 9)), (26, (1 / 9)), (35, (1 / 9))]

def value804 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 48)), (3, (1 / 9)), (12, (1 / 9)), (51, (-1 / 3)), (54, (-1 / 3))]

def value805 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-5 / 144)), (2, (1 / 36)), (3, (2 / 9)), (12, (1 / 9)), (13, (1 / 9))]

def value806 : Sparse (Fin 909) := [(3, (1 / 9)), (12, (-1 / 9)), (13, (1 / 3))]

def value807 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 144)), (2, (1 / 72)), (3, (-1 / 9)), (12, (1 / 9)), (13, (1 / 9))]

def value808 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (1 / 144)), (3, (1 / 9)), (7, (1 / 9)), (23, (-1 / 3)), (54, (-1 / 3))]

def value809 : Sparse (Fin 909) := [(1, (1 / 36)), (2, (1 / 36)), (3, (1 / 9)), (13, (2 / 9)), (52, (1 / 9)), (62, (-1 / 3))]

def value810 : Sparse (Fin 909) := [(1, (5 / 144)), (2, (1 / 144)), (3, (1 / 9)), (13, (4 / 9)), (32, (1 / 9))]

def value811 : Sparse (Fin 909) := [(12, (1 / 9)), (13, (1 / 9)), (32, (1 / 9))]

def value812 : Sparse (Fin 909) := [(3, (1 / 9)), (13, (1 / 9)), (35, (1 / 9)), (54, (-1 / 3)), (62, (-1 / 3))]

def value813 : Sparse (Fin 909) := [(2, (1 / 144)), (5, (-1 / 36)), (6, (1 / 144)), (52, (1 / 9)), (128, (1 / 9)), (201, (-1 / 3)), (267, (-1 / 3))]

def value814 : Sparse (Fin 909) := [(13, (1 / 9)), (82, (1 / 9)), (128, (1 / 9)), (199, (-1 / 3)), (267, (-1 / 3))]

def value815 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 48)), (3, (1 / 9)), (4, (1 / 9)), (51, (-1 / 3)), (56, (-1 / 3))]

def value816 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 72)), (3, (-1 / 9)), (13, (1 / 9)), (35, (1 / 9)), (52, (1 / 9))]

def value817 : Sparse (Fin 909) := [(3, (1 / 9)), (35, (2 / 9)), (52, (-1 / 9)), (60, (1 / 9))]

def value818 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 36)), (5, (-1 / 18)), (6, (1 / 144)), (7, (1 / 9)), (35, (2 / 9)), (52, (2 / 9)), (60, (1 / 9))]

def value819 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 72)), (2, (5 / 144)), (3, (2 / 9)), (5, (-1 / 36)), (7, (1 / 9)), (13, (1 / 9)), (35, (1 / 9))]

def value820 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 36)), (2, (1 / 72)), (8, (1 / 9)), (24, (-1 / 3)), (56, (-1 / 3))]

def value821 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 144)), (5, (-1 / 36)), (7, (1 / 9)), (8, (1 / 9)), (81, (-1 / 3)), (307, (-1 / 3))]

def value822 : Sparse (Fin 909) := [(25, (-1 / 3)), (31, (-1 / 3)), (123, (-1 / 3))]

def value823 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 36)), (2, (1 / 48)), (3, (1 / 9)), (33, (-1 / 3)), (64, (-1 / 3))]

def value824 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (1 / 144)), (3, (1 / 9)), (26, (1 / 9)), (33, (-1 / 3)), (123, (-1 / 3))]

def value825 : Sparse (Fin 909) := [(23, (-1 / 3)), (25, (-1 / 3)), (63, (-1 / 3))]

def value826 : Sparse (Fin 909) := [(1, (-1 / 72)), (2, (1 / 72)), (3, (1 / 9)), (5, (-1 / 36)), (7, (2 / 9)), (26, (1 / 9)), (35, (2 / 9)), (67, (1 / 9))]

def value827 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 24)), (2, (1 / 144)), (3, (1 / 3)), (4, (1 / 9)), (7, (1 / 9)), (26, (1 / 9)), (35, (1 / 9))]

def value828 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 48)), (3, (1 / 9)), (4, (1 / 9)), (24, (-1 / 3)), (55, (-1 / 3))]

def value829 : Sparse (Fin 909) := [(1, (-1 / 24)), (2, (1 / 72)), (3, (2 / 9)), (7, (1 / 9)), (26, (1 / 9)), (64, (-1 / 3))]

def value830 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 144)), (5, (-1 / 36)), (7, (1 / 9)), (35, (1 / 9)), (228, (-1 / 3)), (271, (-1 / 3))]

def value831 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 48)), (3, (1 / 9)), (12, (1 / 9)), (23, (-1 / 3)), (55, (-1 / 3))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value832 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (1 / 144)), (3, (-1 / 9)), (7, (1 / 9)), (26, (1 / 9)), (35, (1 / 9))]

def value833 : Sparse (Fin 909) := [(3, (1 / 9)), (7, (-1 / 9)), (35, (2 / 9)), (67, (1 / 9))]

def value834 : Sparse (Fin 909) := [(3, (2 / 9)), (4, (1 / 9)), (26, (2 / 9)), (35, (2 / 9)), (52, (1 / 9)), (67, (1 / 9))]

def value835 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-1 / 48)), (2, (1 / 36)), (3, (1 / 9)), (4, (1 / 9))]

def value836 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 144)), (2, (1 / 72)), (3, (1 / 3)), (4, (1 / 9)), (13, (1 / 9)), (26, (1 / 9)), (34, (1 / 9))]

def value837 : Sparse (Fin 909) := [(1, (-1 / 16)), (2, (1 / 48)), (3, (2 / 9)), (12, (1 / 9))]

def value838 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 18)), (2, (1 / 144)), (3, (2 / 9)), (4, (2 / 9)), (26, (1 / 9))]

def value839 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 24)), (2, (1 / 144)), (3, (1 / 3)), (12, (1 / 9)), (13, (1 / 9)), (26, (1 / 9)), (34, (1 / 9))]

def value840 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 36)), (2, (1 / 72)), (3, (2 / 9)), (12, (1 / 9)), (26, (1 / 9))]

def value841 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (1 / 144)), (3, (1 / 9)), (26, (1 / 9)), (55, (-1 / 3)), (65, (-1 / 3))]

def value842 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-1 / 24)), (3, (2 / 9)), (4, (1 / 9)), (12, (1 / 9)), (33, (-1 / 3))]

def value843 : Sparse (Fin 909) := [(3, (-1 / 9)), (12, (1 / 9)), (13, (2 / 9)), (34, (1 / 9))]

def value844 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 48)), (3, (1 / 9)), (12, (1 / 9)), (25, (-1 / 3)), (33, (-1 / 3))]

def value845 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-5 / 144)), (3, (2 / 9)), (4, (2 / 9)), (12, (1 / 9)), (26, (1 / 9))]

def value846 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 48)), (3, (2 / 9)), (4, (-1 / 9)), (26, (1 / 9))]

def value847 : Sparse (Fin 909) := [(3, (-1 / 9)), (4, (1 / 9)), (26, (2 / 9)), (34, (1 / 9))]

def value848 : Sparse (Fin 909) := [(3, (1 / 9)), (35, (1 / 9)), (52, (1 / 9)), (228, (-1 / 3)), (275, (-1 / 3))]

def value849 : Sparse (Fin 909) := [(3, (1 / 9)), (7, (1 / 9)), (26, (1 / 9)), (35, (2 / 9)), (67, (1 / 9)), (81, (-1 / 3))]

def value850 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 36)), (2, (1 / 48)), (3, (1 / 3)), (26, (2 / 9)), (34, (1 / 9))]

def value851 : Sparse (Fin 909) := [(3, (2 / 9)), (4, (1 / 9)), (26, (2 / 9)), (33, (-1 / 3)), (34, (1 / 9))]

def value852 : Sparse (Fin 909) := [(3, (2 / 9)), (12, (1 / 9)), (13, (2 / 9)), (33, (-1 / 3)), (34, (1 / 9))]

def value853 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-1 / 16)), (3, (2 / 9)), (4, (1 / 9)), (12, (2 / 9)), (13, (1 / 9))]

def value854 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 48)), (3, (2 / 9)), (12, (-1 / 9)), (13, (1 / 9))]

def value855 : Sparse (Fin 909) := [(0, (-1 / 240)), (2, (1 / 32)), (5, (-1 / 12)), (6, (1 / 96)), (8, (1 / 6)), (71, (1 / 6)), (236, (-1 / 2))]

def value856 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (1 / 24)), (2, (1 / 48)), (8, (1 / 6)), (30, (-1 / 2)), (236, (-1 / 1))]

def value857 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 48)), (5, (-1 / 24)), (27, (1 / 8)), (68, (1 / 4)), (126, (-1 / 2)), (236, (-1 / 2))]

def value858 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-1 / 48)), (2, (1 / 24)), (5, (-1 / 24)), (27, (1 / 8)), (126, (-1 / 2)), (236, (-1 / 2))]

def value859 : Sparse (Fin 909) := [(1, (1 / 32)), (5, (-1 / 24)), (6, (1 / 96)), (68, (1 / 4)), (197, (-1 / 2)), (236, (-1 / 2))]

def value860 : Sparse (Fin 909) := [(1, (-1 / 96)), (2, (-1 / 32)), (5, (-1 / 12)), (6, (1 / 48)), (71, (1 / 6)), (197, (-1 / 2))]

def value861 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 48)), (9, (-1 / 12)), (71, (1 / 6)), (796, (-1 / 2))]

def value862 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-1 / 24)), (2, (-1 / 24)), (5, (-1 / 12)), (6, (1 / 48))]

def value863 : Sparse (Fin 909) := [(0, (-1 / 160)), (2, (5 / 96)), (3, (1 / 6)), (5, (-1 / 12)), (7, (1 / 6)), (8, (1 / 6))]

def value864 : Sparse (Fin 909) := [(1, (-1 / 16)), (5, (-1 / 24)), (6, (1 / 48)), (26, (1 / 6)), (35, (1 / 6))]

def value865 : Sparse (Fin 909) := [(1, (1 / 32)), (2, (-1 / 16)), (5, (-1 / 8)), (6, (-5 / 96)), (35, (1 / 6)), (82, (1 / 6))]

def value866 : Sparse (Fin 909) := [(0, (-1 / 80)), (1, (1 / 12)), (2, (5 / 48)), (5, (-1 / 12)), (8, (1 / 3))]

def value867 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (1 / 24)), (2, (1 / 96)), (3, (1 / 6)), (5, (-1 / 24)), (6, (1 / 48)), (52, (1 / 6)), (237, (-1 / 2))]

def value868 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 16)), (2, (1 / 96)), (3, (1 / 6))]

def value869 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (1 / 96)), (2, (-5 / 96)), (3, (1 / 6)), (26, (1 / 6))]

def value870 : Sparse (Fin 909) := [(0, (-1 / 120)), (1, (1 / 48)), (2, (5 / 48)), (3, (1 / 3)), (5, (-1 / 24)), (52, (1 / 6))]

def value871 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (1 / 24)), (2, (1 / 32)), (3, (1 / 6)), (31, (-1 / 2)), (237, (-1 / 2)), (238, (-1 / 2))]

def value872 : Sparse (Fin 909) := [(1, (-1 / 16)), (2, (1 / 48)), (3, (1 / 3)), (4, (1 / 6)), (26, (1 / 6))]

def value873 : Sparse (Fin 909) := [(0, (-1 / 480)), (2, (1 / 32)), (5, (-1 / 24)), (27, (1 / 4)), (55, (-1 / 2)), (237, (-1 / 2))]

def value874 : Sparse (Fin 909) := [(1, (1 / 24)), (2, (1 / 24)), (5, (-1 / 12)), (27, (1 / 8)), (68, (1 / 8)), (238, (-1 / 2)), (493, (-1 / 2))]

def value875 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (1 / 32)), (2, (1 / 32)), (3, (1 / 6)), (5, (-1 / 12)), (6, (1 / 96)), (26, (1 / 6)), (35, (1 / 6)), (238, (-1 / 2))]

def value876 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-3 / 32)), (2, (-3 / 32)), (3, (1 / 6)), (6, (1 / 96)), (26, (1 / 3)), (35, (1 / 6))]

def value877 : Sparse (Fin 909) := [(1, (1 / 32)), (2, (5 / 96)), (5, (1 / 12)), (6, (1 / 48)), (9, (-1 / 24)), (35, (1 / 6)), (727, (-1 / 2))]

def value878 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (1 / 96)), (2, (5 / 96)), (5, (-1 / 8)), (6, (1 / 48)), (9, (-1 / 24)), (27, (1 / 8)), (68, (1 / 8))]

def value879 : Sparse (Fin 909) := [(1, (-1 / 96)), (2, (-1 / 32)), (6, (1 / 48)), (9, (-1 / 24)), (68, (1 / 8))]

def value880 : Sparse (Fin 909) := [(1, (-1 / 96)), (2, (-7 / 96)), (5, (1 / 24)), (6, (-5 / 96)), (9, (-1 / 24)), (58, (1 / 96))]

def value881 : Sparse (Fin 909) := [(0, (7 / 480)), (1, (-1 / 12)), (5, (-1 / 24)), (6, (1 / 96))]

def value882 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 48)), (2, (-1 / 24)), (5, (-1 / 24)), (6, (1 / 96))]

def value883 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 24)), (2, (1 / 48)), (5, (-1 / 24)), (6, (-1 / 96))]

def value884 : Sparse (Fin 909) := [(0, (1 / 48)), (1, (-1 / 8)), (2, (-1 / 48))]

def value885 : Sparse (Fin 909) := [(0, (-1 / 160)), (1, (-1 / 24)), (2, (1 / 48)), (5, (-1 / 12)), (6, (1 / 96)), (27, (1 / 8))]

def value886 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 48)), (5, (-1 / 36)), (52, (1 / 9)), (256, (-1 / 3)), (818, (-1 / 3))]

def value887 : Sparse (Fin 909) := [(3, (1 / 9)), (35, (1 / 9)), (52, (1 / 9)), (256, (-1 / 3)), (726, (-1 / 3))]

def value888 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (1 / 144)), (5, (-1 / 12)), (6, (1 / 72)), (7, (1 / 9)), (9, (-1 / 18)), (69, (1 / 9)), (70, (1 / 9))]

def value889 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (5 / 144)), (2, (1 / 24)), (5, (-1 / 12)), (6, (1 / 72)), (8, (1 / 9)), (9, (-1 / 18)), (71, (2 / 9))]

def value890 : Sparse (Fin 909) := [(1, (-1 / 144)), (6, (1 / 144)), (9, (-1 / 18)), (69, (1 / 9)), (71, (1 / 9))]

def value891 : Sparse (Fin 909) := [(855, (1 / 1))]

def value892 : Sparse (Fin 909) := [(1, (-1 / 72)), (2, (-1 / 144)), (3, (1 / 9)), (5, (-1 / 36)), (6, (1 / 144)), (11, (1 / 9)), (26, (1 / 9)), (35, (2 / 9)), (52, (1 / 9))]

def value893 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 24)), (2, (7 / 144)), (3, (1 / 9)), (5, (-1 / 18)), (6, (1 / 72)), (35, (1 / 9)), (52, (2 / 9))]

def value894 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (7 / 144)), (2, (1 / 24)), (3, (1 / 9)), (5, (-1 / 36)), (52, (1 / 9)), (81, (-1 / 3))]

def value895 : Sparse (Fin 909) := [(55, (-1 / 3)), (306, (-1 / 3)), (728, (-1 / 3))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value896 : Sparse (Fin 909) := [(3, (1 / 9)), (4, (1 / 9)), (26, (1 / 9)), (81, (-1 / 3)), (228, (-1 / 3))]

def value897 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 48)), (3, (1 / 9)), (5, (-1 / 36)), (35, (1 / 9)), (52, (-1 / 9))]

def value898 : Sparse (Fin 909) := [(1, (-1 / 144)), (5, (-1 / 18)), (6, (1 / 144)), (7, (1 / 9)), (26, (1 / 9)), (35, (2 / 9)), (67, (1 / 9))]

def value899 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (-1 / 18)), (6, (1 / 144)), (26, (2 / 9)), (35, (2 / 9)), (67, (1 / 9))]

def value900 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 72)), (5, (-1 / 18)), (6, (1 / 144)), (35, (1 / 9)), (238, (-1 / 3)), (307, (-1 / 3))]

def value901 : Sparse (Fin 909) := [(3, (1 / 9)), (26, (1 / 9)), (35, (1 / 9)), (307, (-1 / 3)), (727, (-1 / 3))]

def value902 : Sparse (Fin 909) := [(11, (1 / 9)), (26, (-1 / 9)), (35, (2 / 9)), (67, (1 / 9))]

def value903 : Sparse (Fin 909) := [(3, (1 / 9)), (7, (1 / 9)), (26, (1 / 9)), (35, (-1 / 9)), (67, (1 / 9))]

def value904 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 48)), (2, (7 / 144)), (5, (-1 / 9)), (6, (1 / 144)), (7, (1 / 9)), (9, (-1 / 36)), (69, (1 / 9))]

def value905 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (-1 / 24)), (5, (-1 / 36)), (6, (1 / 48)), (7, (1 / 9)), (9, (-1 / 36)), (35, (1 / 9)), (70, (1 / 9))]

def value906 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 72)), (2, (1 / 18)), (5, (-1 / 18)), (6, (1 / 144)), (7, (1 / 9))]

def value907 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-7 / 144)), (2, (-1 / 48)), (3, (1 / 9)), (5, (-1 / 36)), (6, (1 / 144)), (7, (1 / 9)), (35, (1 / 9))]

def value908 : Sparse (Fin 909) := [(1, (1 / 36)), (2, (-5 / 144)), (5, (-1 / 36)), (6, (-1 / 144)), (13, (1 / 9)), (35, (1 / 9)), (82, (1 / 9))]

def value909 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 144)), (2, (-1 / 48)), (5, (-1 / 18)), (6, (-1 / 144))]

def value910 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 144)), (2, (1 / 48)), (5, (-1 / 18)), (6, (1 / 144)), (8, (1 / 9))]

def value911 : Sparse (Fin 909) := [(3, (2 / 9)), (4, (1 / 9)), (7, (1 / 9)), (11, (1 / 9)), (26, (2 / 9)), (35, (2 / 9))]

def value912 : Sparse (Fin 909) := [(1, (1 / 36)), (2, (1 / 36)), (5, (1 / 36)), (10, (-1 / 3)), (27, (1 / 12))]

def value913 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 48)), (5, (-1 / 18)), (6, (1 / 144)), (9, (-1 / 36)), (27, (1 / 12)), (68, (1 / 12)), (308, (-1 / 3))]

def value914 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 72)), (2, (1 / 144)), (5, (1 / 36)), (7, (1 / 9)), (8, (1 / 9))]

def value915 : Sparse (Fin 909) := [(1, (5 / 144)), (2, (-1 / 72)), (5, (-1 / 18)), (6, (1 / 144)), (7, (1 / 9))]

def value916 : Sparse (Fin 909) := [(10, (-1 / 3)), (55, (-1 / 3)), (727, (-1 / 3))]

def value917 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (1 / 144)), (3, (2 / 9)), (7, (1 / 9)), (26, (1 / 9)), (35, (1 / 9)), (228, (-1 / 3))]

def value918 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 144)), (5, (-1 / 18)), (6, (1 / 72)), (9, (-1 / 36)), (68, (1 / 12)), (309, (-1 / 3))]

def value919 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (1 / 72)), (5, (-1 / 36)), (6, (-1 / 144)), (35, (1 / 9))]

def value920 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (-1 / 24)), (6, (1 / 144)), (11, (1 / 9)), (26, (1 / 9)), (35, (-1 / 9))]

def value921 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 24)), (2, (1 / 24)), (3, (1 / 9)), (5, (-1 / 12)), (6, (1 / 144)), (7, (1 / 9)), (8, (1 / 9)), (35, (1 / 9))]

def value922 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 72)), (5, (-1 / 12)), (6, (1 / 48)), (52, (1 / 9))]

def value923 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 36)), (5, (-1 / 18)), (6, (1 / 144)), (8, (1 / 9)), (71, (2 / 9)), (236, (-1 / 3))]

def value924 : Sparse (Fin 909) := [(239, (1 / 1))]

def value925 : Sparse (Fin 909) := [(870, (1 / 1))]

def value926 : Sparse (Fin 909) := [(57, (1 / 1))]

def value927 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 144)), (5, (-1 / 36)), (35, (1 / 9)), (52, (1 / 9)), (81, (-1 / 3)), (306, (-1 / 3))]

def value928 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 72)), (13, (2 / 9)), (33, (-1 / 3)), (63, (-1 / 3))]

def value929 : Sparse (Fin 909) := [(13, (1 / 9)), (52, (1 / 9)), (59, (-1 / 3)), (128, (1 / 9)), (721, (-1 / 3))]

def value930 : Sparse (Fin 909) := [(30, (-1 / 3)), (236, (-2 / 3))]

def value931 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 36)), (2, (1 / 72)), (8, (1 / 9)), (126, (-1 / 3)), (236, (-1 / 3))]

def value932 : Sparse (Fin 909) := [(56, (-1 / 3)), (262, (-1 / 3)), (796, (-1 / 3))]

def value933 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-1 / 48)), (2, (1 / 48)), (3, (1 / 9)), (5, (-1 / 36)), (52, (1 / 9))]

def value934 : Sparse (Fin 909) := [(1, (5 / 144)), (2, (1 / 48)), (5, (-1 / 18)), (6, (1 / 72)), (13, (1 / 9)), (52, (2 / 9)), (128, (1 / 9))]

def value935 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 48)), (3, (1 / 9)), (5, (-1 / 36)), (6, (1 / 144)), (13, (2 / 9)), (35, (1 / 9)), (52, (1 / 9)), (82, (1 / 9)), (128, (1 / 9))]

def value936 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-5 / 144)), (2, (1 / 24)), (3, (1 / 9))]

def value937 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (5 / 144)), (3, (1 / 9)), (13, (2 / 9))]

def value938 : Sparse (Fin 909) := [(0, (-1 / 720)), (2, (-1 / 144)), (3, (1 / 9)), (12, (1 / 9)), (13, (1 / 3)), (35, (1 / 9))]

def value939 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 144)), (2, (1 / 36)), (3, (2 / 9)), (4, (1 / 9)), (26, (1 / 9))]

def value940 : Sparse (Fin 909) := [(1, (5 / 144)), (2, (1 / 24)), (5, (-1 / 9)), (6, (1 / 144)), (7, (1 / 9)), (8, (1 / 9)), (35, (1 / 9)), (52, (1 / 9))]

def value941 : Sparse (Fin 909) := [(31, (-1 / 3)), (123, (-1 / 3)), (237, (-1 / 3))]

def value942 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 18)), (2, (1 / 144)), (3, (2 / 9)), (4, (2 / 9)), (26, (1 / 9))]

def value943 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 36)), (2, (1 / 48)), (3, (1 / 9)), (31, (-1 / 3)), (33, (-1 / 3))]

def value944 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 48)), (3, (1 / 9)), (4, (1 / 9)), (33, (-1 / 3)), (55, (-1 / 3))]

def value945 : Sparse (Fin 909) := [(3, (2 / 9)), (4, (-1 / 9)), (26, (2 / 9))]

def value946 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 24)), (2, (1 / 144)), (3, (-1 / 9)), (4, (1 / 9)), (26, (1 / 9))]

def value947 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 72)), (3, (1 / 9)), (51, (-1 / 3)), (52, (1 / 9)), (123, (-1 / 3))]

def value948 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 36)), (2, (1 / 48)), (3, (1 / 9)), (64, (-1 / 3)), (238, (-1 / 3))]

def value949 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 18)), (2, (-1 / 144)), (3, (2 / 9)), (26, (2 / 9)), (34, (1 / 9))]

def value950 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 72)), (2, (1 / 144)), (3, (2 / 9)), (13, (1 / 9)), (26, (1 / 9)), (34, (1 / 9))]

def value951 : Sparse (Fin 909) := [(3, (-1 / 9)), (13, (1 / 9)), (26, (1 / 9)), (34, (1 / 9)), (35, (1 / 9))]

def value952 : Sparse (Fin 909) := [(3, (2 / 9)), (4, (1 / 9)), (26, (-1 / 9)), (34, (1 / 9))]

def value953 : Sparse (Fin 909) := [(3, (1 / 9)), (26, (1 / 9)), (35, (1 / 9)), (55, (-1 / 3)), (64, (-1 / 3))]

def value954 : Sparse (Fin 909) := [(11, (1 / 9)), (26, (1 / 9)), (35, (1 / 9)), (228, (-1 / 3)), (490, (-1 / 3))]

def value955 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 72)), (2, (1 / 144)), (27, (1 / 6)), (68, (1 / 12)), (124, (-1 / 3))]

def value956 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 144)), (5, (-1 / 18)), (68, (1 / 12)), (125, (-1 / 3))]

def value957 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 48)), (5, (1 / 9)), (6, (1 / 72)), (9, (-1 / 36)), (492, (-1 / 3))]

def value958 : Sparse (Fin 909) := [(0, (-1 / 720)), (2, (1 / 48)), (5, (-1 / 36)), (27, (1 / 12)), (68, (1 / 12)), (126, (-1 / 3))]

def value959 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 18)), (2, (5 / 144)), (3, (1 / 9)), (5, (-1 / 36)), (7, (1 / 9))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value960 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 72)), (2, (-1 / 24)), (3, (1 / 9)), (6, (1 / 144)), (13, (1 / 9)), (35, (1 / 9))]

def value961 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 48)), (5, (-1 / 12)), (13, (1 / 9)), (82, (1 / 9)), (128, (1 / 9))]

def value962 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 48)), (2, (1 / 144)), (5, (-1 / 18)), (6, (-1 / 144)), (52, (1 / 9))]

def value963 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 72)), (5, (-1 / 36)), (6, (1 / 144))]

def value964 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (1 / 48)), (2, (1 / 24)), (5, (-1 / 36)), (8, (1 / 9))]

def value965 : Sparse (Fin 909) := [(3, (2 / 9)), (4, (1 / 9)), (11, (1 / 9)), (13, (1 / 9)), (26, (2 / 9)), (35, (2 / 9))]

def value966 : Sparse (Fin 909) := [(0, (11 / 720)), (1, (-1 / 18)), (2, (1 / 48)), (3, (1 / 9))]

def value967 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-1 / 16)), (3, (1 / 9)), (12, (1 / 9)), (13, (1 / 9))]

def value968 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 144)), (2, (1 / 36)), (3, (1 / 9)), (5, (-1 / 36)), (6, (1 / 144)), (52, (1 / 9))]

def value969 : Sparse (Fin 909) := [(0, (7 / 720)), (1, (-1 / 24)), (2, (1 / 144))]

def value970 : Sparse (Fin 909) := [(0, (-1 / 144)), (1, (-1 / 48)), (2, (1 / 36))]

def value971 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 48)), (3, (1 / 3)), (4, (1 / 9)), (12, (1 / 9)), (13, (1 / 9)), (26, (1 / 9)), (35, (1 / 9))]

def value972 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (1 / 48)), (2, (1 / 36)), (5, (-1 / 18)), (8, (1 / 9))]

def value973 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-1 / 72)), (2, (1 / 36)), (5, (-1 / 36)), (27, (1 / 12)), (51, (-1 / 3))]

def value974 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 48)), (3, (1 / 9))]

def value975 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 48)), (3, (2 / 9)), (12, (2 / 9)), (13, (1 / 9)), (55, (-1 / 3))]

def value976 : Sparse (Fin 909) := [(1, (-1 / 24)), (2, (1 / 72)), (3, (2 / 9)), (7, (2 / 9)), (24, (-1 / 3))]

def value977 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (-1 / 36)), (5, (-1 / 36)), (6, (1 / 144)), (13, (1 / 9)), (52, (1 / 9))]

def value978 : Sparse (Fin 909) := [(0, (-1 / 720)), (2, (7 / 144)), (13, (1 / 9))]

def value979 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (-1 / 144)), (3, (1 / 9)), (13, (-1 / 9)), (35, (1 / 9))]

def value980 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (-1 / 48)), (3, (1 / 9)), (13, (1 / 9)), (26, (1 / 9)), (35, (2 / 9)), (56, (-1 / 3))]

def value981 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 72)), (52, (1 / 9)), (128, (1 / 9))]

def value982 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (7 / 144)), (2, (7 / 144)), (3, (1 / 9)), (5, (-1 / 18)), (6, (1 / 144)), (13, (1 / 9)), (35, (1 / 9)), (52, (1 / 9))]

def value983 : Sparse (Fin 909) := [(31, (-1 / 3)), (51, (-1 / 3)), (238, (-1 / 3))]

def value984 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 24)), (2, (5 / 144)), (3, (2 / 9)), (52, (1 / 9)), (237, (-1 / 3))]

def value985 : Sparse (Fin 909) := [(1, (1 / 36)), (2, (1 / 24)), (5, (-1 / 18)), (6, (1 / 72)), (52, (-1 / 9))]

def value986 : Sparse (Fin 909) := [(1, (1 / 24)), (2, (5 / 144)), (5, (-1 / 9)), (6, (1 / 48)), (8, (1 / 9)), (52, (1 / 9))]

def value987 : Sparse (Fin 909) := [(0, (-1 / 180)), (1, (1 / 18)), (2, (1 / 36)), (8, (2 / 9)), (30, (-1 / 3))]

def value988 : Sparse (Fin 909) := [(26, (1 / 9)), (35, (1 / 9)), (67, (1 / 9)), (81, (-1 / 3)), (273, (-1 / 3))]

def value989 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (-5 / 144)), (63, (-1 / 3)), (123, (-1 / 3))]

def value990 : Sparse (Fin 909) := [(3, (2 / 9)), (13, (1 / 9)), (26, (1 / 9)), (34, (2 / 9)), (64, (-1 / 3))]

def value991 : Sparse (Fin 909) := [(1, (-1 / 24)), (2, (-1 / 72)), (5, (-1 / 36)), (124, (-1 / 3)), (236, (-1 / 3))]

def value992 : Sparse (Fin 909) := [(1, (1 / 36)), (2, (1 / 48)), (5, (-1 / 18)), (6, (1 / 48)), (71, (1 / 9)), (259, (-1 / 3))]

def value993 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (5 / 144)), (2, (1 / 36)), (5, (-1 / 36)), (126, (-2 / 3))]

def value994 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (-1 / 144)), (5, (1 / 36)), (7, (1 / 9)), (8, (1 / 9)), (69, (1 / 9)), (71, (1 / 9))]

def value995 : Sparse (Fin 909) := [(0, (-1 / 180)), (1, (5 / 144)), (2, (5 / 144)), (8, (1 / 9)), (51, (-1 / 3))]

def value996 : Sparse (Fin 909) := [(1, (5 / 144)), (2, (5 / 144)), (5, (-1 / 12)), (8, (1 / 9)), (52, (1 / 9)), (59, (-1 / 3))]

def value997 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 72)), (3, (1 / 9)), (13, (1 / 9)), (59, (-1 / 3)), (201, (-1 / 3))]

def value998 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 36)), (2, (1 / 48)), (5, (-1 / 18)), (7, (1 / 9)), (8, (-1 / 9))]

def value999 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 144)), (5, (-1 / 36)), (8, (1 / 9)), (69, (1 / 9)), (71, (1 / 3)), (256, (-1 / 3))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value3192 : Sparse (Fin 909) := [(0, (-1 / 144)), (1, (31 / 288)), (2, (17 / 96)), (3, (5 / 6)), (5, (-1 / 4)), (6, (5 / 144)), (7, (2 / 9)), (8, (1 / 9)), (10, (-1 / 6)), (12, (1 / 6)), (13, (5 / 9)), (33, (-1 / 6)), (35, (5 / 9)), (52, (2 / 3)), (59, (-1 / 6)), (75, (1 / 2)), (82, (1 / 9)), (128, (1 / 9)), (201, (-1 / 2)), (306, (-1 / 6)), (313, (1 / 2)), (721, (-1 / 6)), (760, (1 / 2))]

def value3193 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-7 / 36)), (2, (1 / 32)), (3, (5 / 9)), (4, (2 / 3)), (12, (1 / 9)), (15, (1 / 2)), (20, (1 / 1)), (24, (-1 / 2))]

def value3194 : Sparse (Fin 909) := [(0, (-1 / 360)), (2, (3 / 32)), (3, (5 / 6)), (4, (5 / 18)), (5, (-1 / 6)), (6, (1 / 96)), (7, (1 / 2)), (8, (2 / 9)), (11, (1 / 9)), (26, (4 / 9)), (33, (-1 / 6)), (35, (11 / 18)), (52, (2 / 9)), (67, (1 / 18)), (81, (-1 / 2)), (85, (1 / 1)), (228, (-5 / 6)), (428, (1 / 2)), (517, (1 / 2))]

def value3195 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-1 / 144)), (2, (31 / 288)), (3, (17 / 18)), (4, (5 / 18)), (5, (-1 / 6)), (6, (1 / 96)), (7, (4 / 9)), (8, (2 / 9)), (11, (1 / 9)), (26, (1 / 2)), (35, (1 / 2)), (52, (2 / 9)), (81, (-5 / 6)), (85, (1 / 1)), (228, (-5 / 6)), (709, (1 / 2))]

def value3196 : Sparse (Fin 909) := [(0, (7 / 720)), (1, (-23 / 144)), (2, (1 / 12)), (3, (5 / 6)), (4, (4 / 9)), (5, (-1 / 36)), (7, (1 / 9)), (8, (1 / 9)), (24, (-1 / 3)), (26, (5 / 18)), (31, (-1 / 3)), (37, (1 / 2)), (56, (-1 / 6)), (99, (1 / 1)), (107, (1 / 1))]

def value3197 : Sparse (Fin 909) := [(0, (7 / 1440)), (1, (-5 / 36)), (2, (19 / 288)), (3, (11 / 9)), (4, (4 / 9)), (5, (-1 / 72)), (7, (1 / 18)), (26, (13 / 18)), (37, (1 / 2)), (56, (-1 / 6))]

def value3198 : Sparse (Fin 909) := [(0, (31 / 1440)), (1, (-5 / 32)), (2, (5 / 144)), (3, (1 / 3)), (19, (1 / 2)), (24, (-1 / 3)), (27, (1 / 24)), (31, (-1 / 6))]

def value3199 : Sparse (Fin 909) := [(0, (3 / 160)), (1, (-37 / 144)), (2, (13 / 288)), (3, (1 / 6)), (4, (7 / 18)), (20, (1 / 2)), (24, (-1 / 6)), (27, (1 / 24)), (30, (-1 / 6)), (31, (-1 / 6))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value320 : Sparse (Fin 909) := [(1, (7 / 96)), (2, (7 / 96)), (5, (-1 / 6)), (6, (1 / 24)), (13, (1 / 6)), (52, (1 / 3)), (128, (1 / 6))]

def value321 : Sparse (Fin 909) := [(51, (-1 / 2)), (59, (-1 / 2)), (259, (-1 / 2)), (262, (-1 / 2))]

def value322 : Sparse (Fin 909) := [(1, (1 / 24)), (2, (1 / 24)), (5, (-1 / 6)), (7, (1 / 3)), (8, (1 / 3)), (35, (1 / 6)), (59, (-1 / 2))]

def value323 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 48)), (13, (1 / 3)), (52, (1 / 3)), (60, (1 / 6)), (128, (1 / 3)), (260, (-1 / 2)), (495, (1 / 6))]

def value324 : Sparse (Fin 909) := [(1, (1 / 32)), (2, (1 / 96)), (5, (-1 / 12)), (6, (1 / 48)), (13, (1 / 6)), (35, (1 / 3)), (52, (1 / 3)), (60, (1 / 3)), (128, (1 / 6))]

def value325 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (-1 / 32)), (13, (1 / 6)), (35, (1 / 6)), (63, (-1 / 2)), (196, (-1 / 2)), (264, (-1 / 2))]

def value326 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (-1 / 48)), (5, (-1 / 24)), (6, (1 / 96)), (7, (1 / 3)), (35, (1 / 2)), (67, (1 / 6)), (69, (1 / 6)), (70, (1 / 3)), (257, (1 / 6))]

def value327 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 48)), (13, (1 / 6)), (52, (1 / 6)), (64, (-1 / 2)), (125, (-1 / 2)), (260, (-1 / 2))]

def value328 : Sparse (Fin 909) := [(124, (-1 / 2)), (196, (-1 / 2)), (197, (-1 / 2)), (266, (-1 / 2))]

def value330 : Sparse (Fin 909) := [(125, (-1 / 1)), (264, (-1 / 1))]

def value331 : Sparse (Fin 909) := [(54, (-1 / 2)), (62, (-1 / 2)), (260, (-1 / 2)), (264, (-1 / 2))]

def value332 : Sparse (Fin 909) := [(125, (-1 / 2)), (126, (-1 / 2)), (197, (-1 / 2)), (268, (-1 / 2))]

def value333 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (-1 / 32)), (13, (1 / 3)), (32, (1 / 6)), (35, (1 / 3)), (60, (1 / 3)), (257, (1 / 6)), (264, (-1 / 2))]

def value334 : Sparse (Fin 909) := [(1, (1 / 32)), (2, (-1 / 96)), (13, (1 / 6)), (32, (1 / 6)), (35, (1 / 6)), (60, (1 / 6))]

def value335 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (-1 / 48)), (5, (-1 / 24)), (6, (1 / 96)), (26, (1 / 6)), (67, (1 / 6)), (257, (1 / 6)), (495, (1 / 6))]

def value336 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 48)), (3, (1 / 6)), (34, (1 / 6)), (52, (1 / 6)), (60, (1 / 6)), (128, (1 / 6))]

def value337 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (-1 / 32)), (26, (1 / 6)), (35, (1 / 6)), (54, (-1 / 2)), (259, (-1 / 2)), (266, (-1 / 2))]

def value338 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 48)), (3, (1 / 6)), (12, (1 / 6)), (13, (1 / 2)), (59, (-1 / 2)), (61, (-1 / 2))]

def value339 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 48)), (3, (1 / 6)), (13, (1 / 2)), (32, (1 / 6)), (35, (1 / 6)), (52, (1 / 6)), (60, (1 / 6)), (62, (-1 / 2))]

def value340 : Sparse (Fin 909) := [(12, (1 / 6)), (13, (1 / 1)), (32, (1 / 3)), (60, (1 / 3)), (128, (1 / 6))]

def value341 : Sparse (Fin 909) := [(1, (1 / 16)), (2, (-1 / 48)), (13, (1 / 1)), (32, (1 / 3))]

def value342 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (-1 / 32)), (26, (1 / 3)), (34, (1 / 6)), (35, (1 / 3)), (67, (1 / 3)), (257, (1 / 6)), (266, (-1 / 2))]

def value343 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 48)), (3, (1 / 3)), (13, (1 / 3)), (26, (1 / 6)), (34, (1 / 3)), (60, (1 / 6)), (61, (-1 / 2))]

def value344 : Sparse (Fin 909) := [(54, (-1 / 2)), (65, (-1 / 2)), (264, (-1 / 2)), (266, (-1 / 2))]

def value345 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 48)), (3, (1 / 6)), (13, (1 / 6)), (33, (-1 / 2)), (54, (-1 / 2)), (62, (-1 / 2))]

def value346 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 48)), (3, (1 / 3)), (12, (1 / 3)), (13, (1 / 1)), (32, (1 / 6))]

def value347 : Sparse (Fin 909) := [(3, (1 / 6)), (12, (1 / 6)), (13, (2 / 3)), (32, (1 / 6)), (34, (1 / 6)), (60, (1 / 6)), (61, (-1 / 2))]

def value348 : Sparse (Fin 909) := [(3, (1 / 6)), (13, (1 / 6)), (26, (1 / 6)), (34, (1 / 6)), (35, (1 / 3)), (60, (1 / 6)), (67, (1 / 6)), (257, (1 / 6)), (268, (-1 / 2))]

def value349 : Sparse (Fin 909) := [(1, (1 / 32)), (2, (-1 / 96)), (3, (1 / 3)), (13, (1 / 3)), (26, (1 / 6)), (34, (1 / 6)), (35, (1 / 3)), (52, (1 / 6)), (60, (1 / 6))]

def value350 : Sparse (Fin 909) := [(55, (-1 / 2)), (61, (-1 / 2)), (266, (-1 / 2)), (268, (-1 / 2))]

def value351 : Sparse (Fin 909) := [(51, (-1 / 2)), (54, (-1 / 2)), (56, (-1 / 2)), (61, (-1 / 2))]

def value352 : Sparse (Fin 909) := [(3, (1 / 6)), (7, (1 / 3)), (26, (1 / 6)), (35, (2 / 3)), (67, (1 / 3)), (70, (1 / 6)), (257, (1 / 6))]

def value353 : Sparse (Fin 909) := [(55, (-1 / 2)), (64, (-1 / 2)), (125, (-1 / 2)), (266, (-1 / 2))]

def value354 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (-1 / 16)), (13, (1 / 2)), (35, (1 / 6)), (63, (-1 / 2))]

def value355 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (-1 / 48)), (3, (1 / 3)), (7, (1 / 6)), (13, (1 / 6)), (26, (1 / 3)), (34, (1 / 6)), (35, (1 / 3)), (67, (1 / 6))]

def value356 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (1 / 24)), (2, (1 / 32)), (3, (1 / 6)), (33, (-1 / 2)), (55, (-1 / 2)), (64, (-1 / 2))]

def value357 : Sparse (Fin 909) := [(23, (-1 / 2)), (55, (-1 / 2)), (63, (-1 / 2)), (65, (-1 / 2))]

def value358 : Sparse (Fin 909) := [(25, (-1 / 2)), (33, (-1 / 2)), (63, (-1 / 2)), (64, (-1 / 2))]

def value359 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (1 / 96)), (5, (-1 / 24)), (7, (1 / 3)), (35, (1 / 2)), (67, (1 / 3)), (271, (-1 / 2)), (276, (1 / 6))]

def value360 : Sparse (Fin 909) := [(1, (-1 / 32)), (2, (1 / 96)), (3, (1 / 3)), (7, (1 / 6)), (26, (1 / 3)), (34, (1 / 6)), (35, (1 / 6)), (64, (-1 / 2)), (67, (1 / 6))]

def value361 : Sparse (Fin 909) := [(24, (-1 / 2)), (55, (-1 / 1)), (66, (-1 / 2))]

def value362 : Sparse (Fin 909) := [(1, (-1 / 96)), (2, (-1 / 24)), (5, (-1 / 24)), (6, (1 / 96)), (7, (1 / 6)), (26, (1 / 3)), (35, (1 / 2)), (67, (1 / 3))]

def value363 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (1 / 16)), (2, (5 / 96)), (3, (1 / 3)), (13, (1 / 3)), (34, (1 / 6)), (52, (1 / 6)), (64, (-1 / 2))]

def value364 : Sparse (Fin 909) := [(1, (-1 / 16)), (2, (-7 / 48)), (13, (1 / 3))]

def value365 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (-1 / 48)), (3, (1 / 6)), (34, (1 / 6)), (35, (1 / 6)), (67, (1 / 6))]

def value366 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (1 / 96)), (2, (1 / 24)), (13, (1 / 6)), (26, (1 / 6)), (34, (1 / 6))]

def value367 : Sparse (Fin 909) := [(1, (-1 / 32)), (2, (1 / 96)), (3, (1 / 6)), (26, (1 / 6)), (33, (-1 / 2)), (54, (-1 / 2)), (65, (-1 / 2))]

def value368 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (1 / 32)), (2, (5 / 96)), (3, (1 / 3)), (12, (1 / 6)), (13, (1 / 3)), (33, (-1 / 2))]

def value369 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 96)), (2, (1 / 48)), (3, (1 / 2)), (12, (1 / 3)), (13, (2 / 3)), (34, (1 / 6))]

def value370 : Sparse (Fin 909) := [(3, (1 / 6)), (26, (1 / 6)), (34, (1 / 6)), (35, (1 / 3)), (52, (1 / 6)), (60, (1 / 6)), (67, (1 / 6)), (275, (-1 / 2)), (276, (1 / 6))]

def value371 : Sparse (Fin 909) := [(3, (1 / 2)), (4, (1 / 6)), (13, (1 / 6)), (26, (1 / 2)), (34, (1 / 3)), (35, (1 / 6)), (67, (1 / 6))]

def value372 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 32)), (3, (1 / 2)), (13, (1 / 6)), (26, (1 / 3)), (34, (1 / 3))]

def value373 : Sparse (Fin 909) := [(1, (-1 / 32)), (2, (1 / 96)), (3, (1 / 3)), (13, (1 / 6)), (26, (1 / 3)), (34, (1 / 3)), (65, (-1 / 2)), (67, (1 / 6))]

def value374 : Sparse (Fin 909) := [(0, (-1 / 160)), (1, (1 / 48)), (2, (7 / 96)), (3, (1 / 3)), (26, (1 / 6)), (33, (-1 / 2))]

def value375 : Sparse (Fin 909) := [(3, (1 / 3)), (4, (1 / 6)), (26, (1 / 2)), (34, (1 / 3)), (66, (-1 / 2)), (67, (1 / 6))]

def value376 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 16)), (2, (1 / 96)), (3, (2 / 3)), (4, (1 / 3)), (26, (1 / 2)), (34, (1 / 6))]

def value377 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 32)), (3, (1 / 2)), (4, (1 / 6)), (12, (1 / 6)), (13, (1 / 6)), (26, (1 / 6)), (33, (-1 / 2)), (34, (1 / 6))]

def value378 : Sparse (Fin 909) := [(3, (1 / 2)), (12, (1 / 6)), (13, (1 / 2)), (26, (1 / 6)), (34, (1 / 3)), (35, (1 / 6)), (60, (1 / 6))]

def value379 : Sparse (Fin 909) := [(3, (1 / 6)), (12, (1 / 6)), (13, (1 / 6)), (33, (-1 / 2)), (55, (-1 / 2)), (61, (-1 / 2))]

def value380 : Sparse (Fin 909) := [(0, (-1 / 40)), (1, (1 / 8)), (2, (7 / 24)), (5, (-1 / 1)), (6, (1 / 8)), (9, (-1 / 6)), (27, (3 / 2)), (68, (5 / 2))]

def value381 : Sparse (Fin 909) := [(0, (-1 / 120)), (1, (-1 / 12)), (2, (1 / 6)), (5, (-2 / 3)), (6, (-1 / 6)), (9, (-1 / 3)), (58, (1 / 24)), (68, (1 / 2))]

def value382 : Sparse (Fin 909) := [(0, (-1 / 60)), (1, (-1 / 6)), (2, (-1 / 12)), (5, (-1 / 6)), (6, (1 / 6)), (9, (-1 / 3)), (27, (1 / 2)), (68, (1 / 1))]

def value383 : Sparse (Fin 909) := [(0, (7 / 120)), (1, (-3 / 4)), (2, (-1 / 3)), (5, (-1 / 2)), (6, (1 / 8))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value3200 : Sparse (Fin 909) := [(0, (7 / 180)), (1, (-17 / 36)), (2, (1 / 24)), (3, (4 / 9)), (4, (2 / 3)), (12, (2 / 9)), (17, (1 / 2)), (22, (1 / 2)), (24, (-1 / 3)), (27, (1 / 24)), (31, (-1 / 3))]

def value3201 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 12)), (2, (1 / 16)), (3, (5 / 6)), (4, (1 / 3)), (5, (-1 / 24)), (7, (5 / 9)), (12, (1 / 18)), (23, (-1 / 6)), (24, (-1 / 3)), (25, (-1 / 6)), (26, (7 / 18)), (27, (1 / 24)), (35, (5 / 18)), (51, (-1 / 6)), (54, (-1 / 6)), (55, (-1 / 3)), (64, (-1 / 3)), (104, (1 / 2))]

def value3202 : Sparse (Fin 909) := [(1, (-7 / 72)), (2, (1 / 12)), (3, (25 / 18)), (4, (1 / 2)), (5, (-1 / 24)), (7, (7 / 18)), (11, (1 / 9)), (26, (7 / 9)), (35, (11 / 18)), (52, (2 / 9)), (67, (1 / 18)), (81, (-1 / 2)), (85, (1 / 1)), (228, (-5 / 6)), (460, (1 / 2)), (709, (1 / 2))]

def value3203 : Sparse (Fin 909) := [(0, (1 / 80)), (1, (-23 / 144)), (2, (5 / 72)), (3, (17 / 18)), (4, (5 / 9)), (26, (7 / 9)), (53, (1 / 2))]

def value3204 : Sparse (Fin 909) := [(0, (49 / 1440)), (1, (-13 / 48)), (2, (11 / 288)), (3, (1 / 3)), (4, (5 / 9)), (25, (-1 / 6)), (26, (1 / 18)), (31, (-1 / 2)), (44, (1 / 2)), (45, (1 / 2))]

def value3205 : Sparse (Fin 909) := [(0, (7 / 720)), (1, (-13 / 72)), (2, (5 / 144)), (3, (5 / 9)), (4, (1 / 9)), (12, (1 / 9)), (21, (1 / 2)), (31, (-1 / 6))]

def value3206 : Sparse (Fin 909) := [(0, (13 / 480)), (1, (-49 / 96)), (2, (1 / 36)), (3, (7 / 9)), (4, (2 / 3)), (12, (11 / 18)), (22, (1 / 2)), (31, (-1 / 6))]

def value3207 : Sparse (Fin 909) := [(0, (17 / 720)), (1, (-25 / 144)), (2, (1 / 36)), (3, (4 / 9)), (4, (-1 / 6)), (12, (1 / 9)), (18, (1 / 2)), (25, (-1 / 6))]

def value3208 : Sparse (Fin 909) := [(0, (7 / 720)), (1, (-55 / 144)), (2, (1 / 36)), (3, (1 / 3)), (4, (2 / 3)), (12, (1 / 9)), (25, (-1 / 6)), (31, (-1 / 3))]

def value3209 : Sparse (Fin 909) := [(0, (7 / 180)), (1, (-13 / 48)), (2, (1 / 144)), (3, (2 / 9)), (4, (2 / 9)), (12, (1 / 18)), (22, (1 / 2)), (31, (-1 / 3))]

def value3210 : Sparse (Fin 909) := [(0, (1 / 48)), (1, (-95 / 288)), (2, (1 / 96)), (3, (5 / 6)), (4, (5 / 9)), (12, (7 / 18)), (21, (1 / 2))]

def value3211 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (-25 / 96)), (2, (1 / 72)), (3, (17 / 18)), (4, (1 / 2)), (7, (1 / 18)), (12, (11 / 18)), (13, (1 / 9)), (23, (-1 / 6)), (24, (-1 / 6)), (25, (-1 / 2)), (26, (1 / 18)), (33, (-1 / 6)), (35, (1 / 18)), (48, (1 / 2)), (50, (3 / 2)), (55, (-1 / 3)), (113, (1 / 2)), (177, (1 / 2))]

def value3212 : Sparse (Fin 909) := [(0, (1 / 288)), (1, (-53 / 288)), (2, (1 / 72)), (3, (13 / 18)), (4, (4 / 9)), (7, (1 / 18)), (12, (5 / 18)), (23, (-1 / 6)), (24, (-1 / 6)), (25, (-1 / 6)), (26, (5 / 18)), (35, (1 / 18)), (43, (1 / 1)), (44, (1 / 2)), (47, (1 / 2)), (55, (-1 / 3)), (113, (1 / 2)), (114, (1 / 1)), (191, (1 / 2))]

def value3213 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (-23 / 288)), (2, (1 / 36)), (3, (2 / 3)), (4, (5 / 18)), (5, (-1 / 72)), (7, (5 / 18)), (11, (1 / 18)), (26, (5 / 9)), (35, (7 / 18)), (52, (1 / 9)), (53, (1 / 1)), (81, (-1 / 3)), (83, (1 / 2)), (84, (3 / 2)), (228, (-2 / 3)), (702, (1 / 1)), (709, (1 / 1))]

def value3214 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-19 / 96)), (2, (1 / 72)), (3, (8 / 9)), (4, (1 / 3)), (7, (1 / 18)), (12, (4 / 9)), (13, (1 / 6)), (18, (1 / 2)), (23, (-1 / 6)), (24, (-1 / 3)), (26, (1 / 18)), (33, (-1 / 6)), (35, (1 / 18)), (47, (1 / 2)), (55, (-1 / 2)), (177, (1 / 2))]

def value3215 : Sparse (Fin 909) := [(0, (11 / 720)), (1, (-31 / 144)), (2, (1 / 36)), (3, (7 / 6)), (4, (2 / 3)), (7, (1 / 18)), (12, (1 / 6)), (21, (1 / 2)), (23, (-1 / 6)), (24, (-1 / 3)), (25, (-1 / 6)), (26, (4 / 9)), (35, (1 / 18)), (44, (1 / 1)), (48, (1 / 2)), (55, (-1 / 2)), (191, (1 / 2))]

def value3216 : Sparse (Fin 909) := [(0, (19 / 720)), (1, (-61 / 144)), (2, (1 / 72)), (3, (1 / 3)), (4, (4 / 9)), (12, (2 / 9)), (22, (1 / 2))]

def value3217 : Sparse (Fin 909) := [(0, (19 / 480)), (1, (-13 / 36)), (2, (1 / 288)), (3, (11 / 18)), (4, (5 / 18)), (12, (1 / 6)), (18, (1 / 2))]

def value3218 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (13 / 288)), (2, (-1 / 96)), (3, (1 / 9)), (5, (-11 / 72)), (6, (5 / 288)), (7, (1 / 18)), (9, (-1 / 72)), (13, (1 / 2)), (35, (13 / 18)), (52, (4 / 9)), (60, (7 / 18)), (68, (1 / 24)), (70, (1 / 18)), (82, (2 / 9)), (125, (-1 / 6)), (128, (5 / 18)), (260, (-1 / 3)), (309, (-1 / 3)), (323, (1 / 2)), (728, (-1 / 6))]

def value3219 : Sparse (Fin 909) := [(0, (-1 / 144)), (1, (-1 / 48)), (2, (11 / 288)), (3, (11 / 18)), (5, (-5 / 72)), (6, (1 / 96)), (7, (1 / 6)), (8, (1 / 9)), (12, (1 / 9)), (13, (7 / 18)), (26, (2 / 9)), (34, (1 / 6)), (35, (1 / 6)), (51, (-1 / 3)), (52, (1 / 9)), (71, (1 / 18)), (138, (1 / 2)), (146, (1 / 2)), (197, (-1 / 3)), (236, (-1 / 6)), (400, (1 / 1)), (810, (1 / 1))]

def value3220 : Sparse (Fin 909) := [(0, (-13 / 1440)), (1, (-1 / 144)), (2, (7 / 96)), (3, (1 / 2)), (5, (-1 / 24)), (7, (1 / 6)), (8, (1 / 9)), (12, (2 / 9)), (13, (2 / 9)), (23, (-1 / 6)), (33, (-1 / 6)), (51, (-1 / 1)), (52, (1 / 9)), (55, (-1 / 6)), (69, (1 / 18)), (124, (-1 / 6)), (125, (-1 / 6)), (126, (-1 / 6)), (140, (1 / 2)), (142, (1 / 1)), (145, (1 / 2)), (383, (1 / 1)), (538, (1 / 1))]

def value3221 : Sparse (Fin 909) := [(0, (-1 / 144)), (1, (1 / 288)), (2, (1 / 12)), (3, (5 / 9)), (5, (-11 / 72)), (6, (5 / 288)), (7, (1 / 6)), (9, (-1 / 72)), (12, (1 / 9)), (13, (2 / 9)), (23, (-1 / 6)), (26, (1 / 9)), (27, (1 / 8)), (35, (1 / 6)), (51, (-2 / 3)), (52, (2 / 9)), (54, (-1 / 3)), (55, (-1 / 3)), (64, (-1 / 1)), (68, (1 / 12)), (70, (1 / 18)), (125, (-1 / 3)), (238, (-2 / 3)), (260, (-1 / 3)), (309, (-1 / 3))]

def value3222 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (1 / 16)), (2, (37 / 288)), (3, (5 / 18)), (5, (-23 / 72)), (6, (1 / 32)), (7, (7 / 18)), (8, (5 / 18)), (9, (-1 / 36)), (24, (-1 / 6)), (27, (1 / 24)), (35, (2 / 9)), (51, (-1 / 6)), (52, (7 / 18)), (68, (1 / 24)), (69, (1 / 3)), (70, (1 / 6)), (71, (5 / 18)), (126, (-1 / 2)), (197, (-1 / 6)), (236, (-1 / 6)), (262, (-1 / 3)), (308, (-1 / 6)), (309, (-1 / 6)), (322, (1 / 2)), (327, (1 / 2))]

def value3223 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-1 / 24)), (2, (13 / 288)), (3, (1 / 3)), (5, (-7 / 72)), (6, (1 / 96)), (7, (1 / 3)), (9, (-1 / 72)), (12, (1 / 6)), (23, (-1 / 2)), (27, (1 / 8)), (35, (1 / 9)), (51, (-1 / 1)), (54, (-1 / 1)), (68, (1 / 24)), (69, (1 / 6)), (70, (1 / 9)), (124, (-1 / 2)), (196, (-1 / 3)), (259, (-1 / 1)), (282, (3 / 2)), (308, (-1 / 2)), (723, (-1 / 2))]

def value3224 : Sparse (Fin 909) := [(0, (1 / 120)), (1, (-1 / 16)), (2, (5 / 24)), (3, (4 / 9)), (4, (1 / 6)), (5, (-7 / 36)), (6, (1 / 144)), (7, (1 / 3)), (8, (4 / 9)), (31, (-2 / 3)), (35, (1 / 9)), (51, (-2 / 3)), (56, (-1 / 6)), (97, (1 / 2)), (107, (1 / 1)), (238, (-1 / 2))]

def value3225 : Sparse (Fin 909) := [(0, (-1 / 180)), (1, (-7 / 288)), (2, (5 / 72)), (3, (4 / 9)), (4, (1 / 9)), (5, (-5 / 36)), (6, (1 / 96)), (7, (1 / 3)), (8, (1 / 6)), (12, (1 / 18)), (13, (1 / 18)), (26, (2 / 9)), (31, (-1 / 6)), (35, (1 / 6)), (43, (1 / 2)), (51, (-1 / 6)), (77, (1 / 2)), (97, (1 / 1)), (107, (1 / 2)), (238, (-1 / 3)), (737, (1 / 2))]

def value3226 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (11 / 288)), (2, (29 / 288)), (3, (7 / 18)), (4, (1 / 6)), (5, (-1 / 8)), (6, (1 / 72)), (7, (1 / 18)), (8, (2 / 9)), (9, (-1 / 72)), (26, (1 / 9)), (51, (-1 / 3)), (52, (2 / 9)), (56, (-1 / 2)), (69, (1 / 18)), (71, (1 / 18)), (228, (-1 / 3)), (262, (-1 / 3)), (735, (1 / 2)), (796, (-1 / 6))]

def value3227 : Sparse (Fin 909) := [(1, (1 / 32)), (2, (19 / 144)), (3, (5 / 18)), (4, (1 / 9)), (5, (-11 / 72)), (6, (1 / 288)), (7, (1 / 6)), (8, (4 / 9)), (31, (-1 / 6)), (51, (-2 / 3)), (56, (-1 / 3)), (71, (1 / 9)), (107, (1 / 2)), (238, (-1 / 6)), (262, (-1 / 6)), (309, (-1 / 6)), (327, (1 / 2))]

def value3228 : Sparse (Fin 909) := [(0, (-1 / 160)), (2, (1 / 12)), (3, (1 / 2)), (4, (1 / 18)), (5, (-1 / 8)), (6, (1 / 288)), (7, (1 / 3)), (8, (5 / 18)), (26, (1 / 9)), (35, (1 / 6)), (51, (-5 / 6)), (56, (-1 / 6)), (69, (1 / 18)), (70, (1 / 18)), (71, (1 / 18)), (77, (1 / 1)), (97, (1 / 2)), (238, (-1 / 6)), (286, (1 / 2)), (309, (-1 / 6)), (736, (1 / 2))]

def value3229 : Sparse (Fin 909) := [(1, (-11 / 144)), (2, (11 / 144)), (3, (11 / 18)), (4, (1 / 9)), (5, (-1 / 18)), (7, (4 / 9)), (24, (-2 / 3)), (26, (1 / 9)), (27, (1 / 6)), (35, (1 / 9)), (51, (-1 / 3)), (68, (1 / 24)), (124, (-1 / 6)), (126, (-1 / 3)), (197, (-1 / 3))]

def value3230 : Sparse (Fin 909) := [(0, (13 / 1440)), (1, (-1 / 9)), (2, (25 / 288)), (3, (11 / 18)), (4, (7 / 18)), (5, (-1 / 24)), (7, (1 / 6)), (8, (1 / 9)), (26, (2 / 9)), (31, (-2 / 3)), (35, (1 / 9)), (51, (-2 / 3)), (56, (-1 / 6)), (97, (1 / 2)), (107, (1 / 1)), (238, (-1 / 2))]

def value3231 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 48)), (2, (5 / 144)), (3, (7 / 18)), (4, (1 / 6)), (5, (-1 / 18)), (6, (1 / 144)), (7, (1 / 6)), (8, (1 / 18)), (26, (1 / 9)), (31, (-1 / 6)), (35, (1 / 6)), (46, (1 / 2)), (51, (-1 / 2)), (52, (1 / 9)), (56, (-1 / 6)), (69, (1 / 18)), (70, (1 / 18)), (107, (1 / 2)), (238, (-1 / 6)), (262, (-1 / 6)), (309, (-1 / 6)), (327, (1 / 2)), (735, (1 / 2)), (736, (1 / 2))]

def value3232 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-37 / 288)), (2, (5 / 36)), (3, (13 / 18)), (4, (1 / 6)), (5, (-5 / 36)), (6, (1 / 144)), (7, (7 / 18)), (8, (2 / 9)), (24, (-1 / 3)), (26, (1 / 6)), (27, (1 / 12)), (31, (-1 / 6)), (35, (1 / 9)), (51, (-1 / 3)), (68, (1 / 24)), (107, (1 / 2)), (126, (-1 / 2)), (197, (-1 / 6)), (236, (-1 / 6)), (238, (-1 / 6))]

def value3233 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (-13 / 144)), (2, (7 / 72)), (3, (2 / 3)), (4, (1 / 6)), (5, (-7 / 72)), (6, (1 / 96)), (7, (5 / 18)), (8, (1 / 9)), (12, (1 / 18)), (13, (1 / 18)), (24, (-1 / 6)), (26, (1 / 18)), (27, (1 / 24)), (31, (-1 / 3)), (35, (1 / 9)), (46, (1 / 2)), (51, (-1 / 3)), (52, (1 / 18)), (55, (-1 / 6)), (95, (1 / 2)), (106, (1 / 2)), (237, (-1 / 6)), (735, (1 / 1)), (736, (1 / 2)), (738, (1 / 2))]

def value3234 : Sparse (Fin 909) := [(1, (-11 / 96)), (2, (37 / 288)), (3, (5 / 6)), (4, (2 / 9)), (5, (-1 / 9)), (6, (1 / 144)), (7, (1 / 3)), (8, (2 / 9)), (12, (1 / 18)), (13, (1 / 18)), (24, (-1 / 3)), (26, (1 / 6)), (27, (1 / 12)), (30, (-1 / 6)), (31, (-1 / 6)), (35, (1 / 6)), (51, (-1 / 2)), (52, (1 / 18)), (55, (-1 / 6)), (95, (1 / 2)), (107, (1 / 2)), (238, (-1 / 6))]

def value3235 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 72)), (2, (11 / 96)), (3, (2 / 9)), (4, (1 / 9)), (5, (-1 / 8)), (6, (1 / 96)), (8, (1 / 6)), (9, (-1 / 72)), (24, (-1 / 6)), (27, (1 / 6)), (31, (-1 / 3)), (51, (-1 / 1)), (52, (1 / 9)), (56, (-1 / 3)), (68, (1 / 12)), (71, (1 / 18)), (126, (-1 / 3)), (238, (-1 / 3)), (262, (-1 / 3)), (308, (-1 / 6)), (309, (-1 / 6))]

def value3236 : Sparse (Fin 909) := [(0, (1 / 480)), (2, (3 / 32)), (3, (1 / 18)), (5, (-1 / 9)), (6, (1 / 72)), (8, (1 / 3)), (12, (1 / 18)), (27, (1 / 24)), (30, (-1 / 6)), (45, (1 / 2)), (51, (-1 / 2)), (54, (-1 / 6)), (71, (1 / 9)), (259, (-1 / 6)), (308, (-1 / 6)), (325, (1 / 2)), (738, (1 / 2)), (739, (1 / 2))]

def value3237 : Sparse (Fin 909) := [(0, (-7 / 1440)), (1, (1 / 48)), (2, (13 / 288)), (3, (1 / 6)), (5, (-11 / 72)), (6, (1 / 48)), (8, (1 / 9)), (9, (-1 / 72)), (12, (1 / 18)), (33, (-1 / 3)), (51, (-1 / 3)), (52, (1 / 9)), (54, (-1 / 3)), (71, (1 / 9)), (259, (-1 / 3)), (721, (-1 / 3)), (723, (-1 / 6)), (739, (1 / 1))]

def value3238 : Sparse (Fin 909) := [(0, (-11 / 1440)), (1, (-1 / 144)), (2, (17 / 288)), (3, (1 / 6)), (5, (-5 / 36)), (6, (1 / 144)), (7, (5 / 18)), (8, (1 / 3)), (12, (1 / 18)), (23, (-1 / 6)), (27, (1 / 8)), (51, (-2 / 3)), (54, (-1 / 3)), (69, (1 / 18)), (71, (1 / 9)), (282, (1 / 2)), (293, (1 / 1)), (308, (-1 / 6)), (738, (1 / 1))]

def value3239 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (11 / 144)), (2, (1 / 16)), (3, (1 / 9)), (5, (-17 / 72)), (6, (1 / 24)), (7, (1 / 9)), (9, (-1 / 24)), (13, (1 / 3)), (23, (-1 / 6)), (27, (1 / 24)), (35, (4 / 9)), (52, (2 / 9)), (54, (-1 / 3)), (63, (-1 / 3)), (68, (1 / 12)), (70, (1 / 9)), (196, (-1 / 3)), (237, (-1 / 3)), (721, (-1 / 3)), (723, (-1 / 6))]

def value3240 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-11 / 72)), (2, (13 / 144)), (3, (5 / 6)), (5, (-1 / 18)), (7, (1 / 3)), (12, (1 / 2)), (13, (1 / 9)), (23, (-1 / 1)), (27, (1 / 4)), (35, (1 / 9)), (51, (-1 / 1)), (54, (-1 / 1)), (68, (1 / 24)), (124, (-1 / 2)), (196, (-1 / 3))]

def value3241 : Sparse (Fin 909) := [(0, (-7 / 1440)), (1, (-31 / 288)), (2, (1 / 48)), (3, (5 / 6)), (4, (1 / 6)), (5, (-1 / 72)), (7, (1 / 6)), (12, (1 / 2)), (13, (1 / 9)), (23, (-1 / 2)), (25, (-1 / 2)), (27, (1 / 24)), (33, (-1 / 1)), (35, (1 / 9)), (51, (-1 / 2)), (54, (-1 / 1)), (63, (-1 / 3)), (293, (3 / 2)), (721, (-1 / 2))]

def value3242 : Sparse (Fin 909) := [(0, (5 / 288)), (1, (-1 / 18)), (2, (55 / 288)), (3, (1 / 9)), (5, (-1 / 6)), (6, (1 / 144)), (7, (1 / 9)), (8, (5 / 9)), (27, (1 / 6)), (30, (-2 / 3)), (51, (-1 / 3)), (68, (1 / 24)), (124, (-1 / 6)), (236, (-2 / 3))]

def value3243 : Sparse (Fin 909) := [(0, (1 / 288)), (1, (-25 / 144)), (2, (1 / 12)), (3, (7 / 9)), (4, (1 / 2)), (5, (-5 / 72)), (6, (1 / 288)), (7, (1 / 9)), (8, (1 / 9)), (12, (1 / 9)), (23, (-1 / 6)), (24, (-1 / 3)), (26, (1 / 9)), (27, (1 / 8)), (31, (-1 / 3)), (35, (1 / 9)), (51, (-4 / 3)), (52, (1 / 9)), (54, (-1 / 3)), (56, (-5 / 6)), (97, (1 / 2)), (238, (-1 / 6))]

def value3244 : Sparse (Fin 909) := [(0, (-13 / 1440)), (1, (1 / 36)), (2, (3 / 32)), (3, (1 / 2)), (5, (-1 / 6)), (6, (1 / 72)), (7, (1 / 3)), (8, (2 / 9)), (12, (1 / 6)), (13, (1 / 9)), (23, (-1 / 3)), (27, (1 / 12)), (35, (1 / 9)), (51, (-1 / 3)), (54, (-1 / 3)), (68, (1 / 24)), (124, (-1 / 3)), (196, (-1 / 6)), (236, (-1 / 3))]

def value3245 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (7 / 144)), (2, (13 / 96)), (3, (13 / 18)), (4, (5 / 18)), (5, (-5 / 36)), (6, (5 / 288)), (7, (1 / 6)), (8, (2 / 9)), (9, (-1 / 72)), (26, (2 / 9)), (35, (2 / 9)), (52, (4 / 9)), (56, (-1 / 3)), (69, (1 / 18)), (81, (-5 / 6)), (228, (-2 / 3)), (501, (1 / 2)), (796, (-1 / 6))]

def value3246 : Sparse (Fin 909) := [(0, (7 / 1440)), (1, (-1 / 24)), (2, (5 / 36)), (3, (2 / 3)), (4, (7 / 18)), (5, (-5 / 36)), (6, (1 / 288)), (7, (1 / 6)), (8, (7 / 18)), (24, (-1 / 6)), (26, (1 / 6)), (31, (-1 / 6)), (51, (-1 / 3)), (56, (-2 / 3)), (71, (1 / 18)), (107, (1 / 1)), (126, (-1 / 6)), (262, (-1 / 6)), (753, (1 / 2))]

def value3247 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-55 / 288)), (2, (25 / 288)), (3, (7 / 18)), (4, (4 / 9)), (5, (-1 / 72)), (8, (1 / 18)), (12, (1 / 18)), (31, (-2 / 3)), (49, (1 / 2)), (51, (-1 / 3)), (107, (1 / 2)), (238, (-1 / 6))]

def value3248 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (-3 / 16)), (2, (1 / 16)), (3, (2 / 3)), (4, (1 / 3)), (5, (-1 / 72)), (7, (1 / 18)), (12, (1 / 3)), (13, (1 / 18)), (26, (1 / 9)), (31, (-1 / 2)), (35, (1 / 18)), (43, (1 / 1)), (47, (1 / 2)), (51, (-1 / 6)), (97, (1 / 2)), (204, (1 / 2)), (238, (-1 / 6))]

def value3249 : Sparse (Fin 909) := [(1, (-1 / 12)), (2, (7 / 96)), (3, (5 / 6)), (4, (7 / 18)), (5, (-5 / 72)), (6, (1 / 288)), (7, (1 / 6)), (26, (1 / 6)), (27, (1 / 24)), (31, (-1 / 6)), (46, (1 / 1)), (51, (-2 / 3)), (52, (1 / 9)), (56, (-1 / 3)), (69, (1 / 18)), (124, (-1 / 6)), (262, (-1 / 6)), (735, (1 / 1)), (745, (1 / 1)), (753, (1 / 2))]

def value3250 : Sparse (Fin 909) := [(0, (1 / 80)), (1, (-49 / 288)), (2, (5 / 288)), (3, (1 / 2)), (4, (7 / 18)), (7, (1 / 18)), (12, (1 / 9)), (13, (1 / 18)), (22, (1 / 2)), (26, (1 / 9)), (31, (-1 / 2)), (35, (1 / 18)), (46, (1 / 2)), (49, (1 / 2)), (51, (-1 / 3)), (107, (1 / 2)), (204, (1 / 2)), (238, (-1 / 6))]

def value3251 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (-1 / 8)), (2, (25 / 288)), (3, (17 / 18)), (4, (1 / 6)), (5, (-5 / 72)), (6, (1 / 144)), (7, (1 / 18)), (8, (1 / 18)), (12, (1 / 3)), (13, (2 / 9)), (24, (-1 / 6)), (26, (1 / 6)), (27, (1 / 12)), (31, (-1 / 6)), (35, (1 / 9)), (51, (-1 / 3)), (52, (1 / 9)), (55, (-1 / 3)), (68, (1 / 24)), (126, (-1 / 6)), (146, (1 / 2)), (197, (-1 / 6)), (204, (1 / 2)), (237, (-1 / 6)), (238, (-1 / 6))]

def value3252 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-37 / 288)), (2, (23 / 288)), (3, (1 / 1)), (4, (2 / 9)), (5, (-1 / 18)), (6, (1 / 144)), (12, (7 / 18)), (13, (5 / 9)), (26, (1 / 6)), (27, (1 / 12)), (31, (-1 / 3)), (33, (-1 / 3)), (35, (1 / 6)), (51, (-1 / 2)), (52, (1 / 9)), (55, (-1 / 3)), (204, (1 / 2)), (238, (-1 / 6))]

def value3253 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-43 / 288)), (2, (11 / 144)), (3, (1 / 2)), (4, (1 / 6)), (5, (-1 / 24)), (7, (1 / 6)), (8, (1 / 18)), (12, (1 / 6)), (23, (-1 / 6)), (24, (-1 / 3)), (27, (1 / 8)), (31, (-1 / 3)), (47, (1 / 2)), (51, (-2 / 3)), (52, (1 / 18)), (69, (1 / 18)), (124, (-1 / 6)), (126, (-1 / 3)), (205, (1 / 2)), (207, (1 / 2)), (209, (1 / 2)), (538, (1 / 2)), (751, (1 / 2)), (753, (1 / 1))]

def value3254 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 144)), (2, (-1 / 144)), (3, (2 / 9)), (5, (-1 / 18)), (6, (1 / 144)), (7, (1 / 6)), (13, (1 / 3)), (35, (2 / 9)), (52, (4 / 9)), (54, (-1 / 3)), (63, (-1 / 6)), (69, (1 / 6)), (123, (-1 / 3)), (124, (-1 / 6)), (125, (-1 / 3)), (126, (-1 / 6)), (129, (1 / 2)), (144, (1 / 2)), (306, (-1 / 6)), (498, (1 / 2))]

def value3255 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 48)), (2, (7 / 144)), (3, (1 / 9)), (5, (-5 / 72)), (6, (1 / 288)), (7, (1 / 9)), (9, (-1 / 72)), (12, (1 / 18)), (23, (-1 / 6)), (24, (-1 / 3)), (27, (1 / 12)), (51, (-1 / 3)), (68, (1 / 8)), (69, (1 / 18)), (124, (-1 / 6)), (126, (-1 / 3)), (308, (-1 / 6)), (751, (1 / 2))]

def value3256 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (1 / 24)), (2, (3 / 32)), (3, (5 / 18)), (5, (-5 / 24)), (6, (1 / 24)), (7, (1 / 18)), (9, (-1 / 72)), (12, (1 / 18)), (33, (-2 / 3)), (35, (2 / 9)), (52, (4 / 9)), (54, (-1 / 3)), (69, (1 / 18)), (306, (-1 / 2)), (498, (1 / 2)), (721, (-2 / 3)), (723, (-1 / 6)), (760, (1 / 1))]

def value3257 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (7 / 288)), (2, (11 / 288)), (3, (5 / 18)), (4, (1 / 18)), (5, (-1 / 24)), (7, (1 / 18)), (12, (1 / 6)), (23, (-1 / 6)), (24, (-1 / 3)), (27, (1 / 8)), (51, (-1 / 3)), (68, (1 / 24)), (124, (-1 / 6)), (126, (-1 / 6)), (205, (1 / 2))]

def value3258 : Sparse (Fin 909) := [(1, (-5 / 72)), (2, (1 / 36)), (3, (5 / 9)), (4, (1 / 18)), (7, (1 / 9)), (12, (7 / 18)), (13, (1 / 6)), (15, (1 / 2)), (23, (-1 / 2)), (25, (-1 / 3)), (27, (1 / 24)), (33, (-1 / 3)), (35, (1 / 18)), (51, (-1 / 6)), (54, (-1 / 3)), (63, (-1 / 6)), (124, (-1 / 6)), (144, (1 / 2)), (196, (-1 / 6)), (205, (1 / 2))]

def value3259 : Sparse (Fin 909) := [(0, (1 / 180)), (1, (-13 / 72)), (2, (1 / 9)), (3, (2 / 9)), (4, (5 / 18)), (5, (-1 / 18)), (8, (1 / 9)), (24, (-1 / 3)), (27, (1 / 6)), (31, (-1 / 2)), (51, (-2 / 3)), (68, (1 / 24)), (126, (-1 / 3)), (207, (1 / 2)), (238, (-1 / 6))]

def value3260 : Sparse (Fin 909) := [(0, (1 / 90)), (1, (-5 / 32)), (2, (7 / 72)), (3, (5 / 9)), (4, (7 / 18)), (5, (-1 / 18)), (6, (1 / 288)), (12, (1 / 9)), (27, (1 / 6)), (31, (-1 / 2)), (51, (-1 / 1)), (52, (1 / 9)), (209, (1 / 2)), (238, (-1 / 6))]

def value3261 : Sparse (Fin 909) := [(0, (13 / 1440)), (1, (-43 / 288)), (2, (1 / 48)), (3, (7 / 9)), (4, (1 / 2)), (12, (1 / 6)), (21, (1 / 2)), (26, (2 / 9)), (31, (-1 / 6)), (33, (-1 / 6)), (35, (1 / 18)), (51, (-1 / 2)), (52, (1 / 18)), (54, (-1 / 6)), (56, (-1 / 3)), (191, (1 / 2)), (209, (1 / 2))]

def value3262 : Sparse (Fin 909) := [(0, (1 / 288)), (1, (-13 / 72)), (2, (13 / 288)), (3, (17 / 18)), (4, (4 / 9)), (5, (-1 / 72)), (7, (1 / 6)), (8, (1 / 18)), (12, (1 / 3)), (23, (-1 / 3)), (24, (-1 / 3)), (25, (-1 / 6)), (26, (1 / 6)), (31, (-1 / 6)), (33, (-1 / 6)), (35, (1 / 18)), (43, (1 / 2)), (47, (1 / 1)), (48, (1 / 2)), (51, (-1 / 6)), (54, (-1 / 6)), (56, (-1 / 6)), (97, (1 / 2)), (191, (1 / 2))]

def value3263 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (7 / 288)), (2, (7 / 144)), (3, (11 / 18)), (5, (-5 / 72)), (6, (1 / 72)), (12, (1 / 6)), (13, (2 / 3)), (23, (-1 / 6)), (27, (1 / 24)), (33, (-1 / 3)), (35, (1 / 9)), (52, (2 / 9)), (54, (-1 / 6)), (63, (-1 / 3)), (68, (1 / 24)), (126, (-1 / 6)), (144, (1 / 2)), (196, (-1 / 6)), (237, (-1 / 3))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value3264 : Sparse (Fin 909) := [(0, (-7 / 1440)), (1, (1 / 24)), (2, (5 / 288)), (3, (5 / 9)), (5, (-1 / 9)), (6, (1 / 36)), (12, (1 / 9)), (13, (7 / 9)), (25, (-1 / 6)), (31, (-1 / 6)), (33, (-1 / 3)), (35, (2 / 9)), (52, (1 / 3)), (63, (-1 / 2)), (123, (-1 / 6)), (231, (1 / 2)), (237, (-1 / 3)), (306, (-1 / 6)), (721, (-1 / 6)), (760, (1 / 2))]

def value3265 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-35 / 288)), (2, (5 / 144)), (3, (5 / 6)), (4, (1 / 3)), (12, (1 / 2)), (13, (2 / 9)), (23, (-1 / 2)), (24, (-1 / 2)), (25, (-1 / 2)), (27, (1 / 24)), (33, (-1 / 1)), (55, (-1 / 1)), (63, (-1 / 3)), (299, (3 / 2)), (306, (-1 / 2))]

def value3266 : Sparse (Fin 909) := [(0, (29 / 720)), (1, (-79 / 288)), (2, (31 / 288)), (3, (5 / 18)), (4, (2 / 9)), (5, (-1 / 72)), (12, (1 / 18)), (20, (1 / 1)), (24, (-1 / 3)), (27, (1 / 8)), (30, (-1 / 3)), (51, (-1 / 6)), (52, (1 / 18)), (126, (-1 / 6)), (205, (1 / 2)), (208, (2 / 1))]

def value3267 : Sparse (Fin 909) := [(0, (1 / 288)), (1, (-1 / 9)), (2, (17 / 288)), (3, (5 / 9)), (4, (1 / 9)), (5, (-1 / 36)), (12, (1 / 3)), (13, (1 / 9)), (15, (1 / 2)), (23, (-1 / 6)), (24, (-1 / 6)), (27, (1 / 8)), (51, (-1 / 3)), (52, (1 / 9)), (126, (-1 / 6)), (144, (1 / 2)), (205, (1 / 1)), (208, (1 / 1))]

def value3268 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-19 / 96)), (2, (7 / 288)), (3, (11 / 9)), (4, (4 / 9)), (7, (1 / 18)), (12, (1 / 2)), (13, (1 / 6)), (18, (1 / 2)), (23, (-1 / 3)), (24, (-1 / 6)), (25, (-1 / 3)), (26, (5 / 18)), (33, (-1 / 3)), (35, (1 / 18)), (43, (1 / 1)), (47, (1 / 2)), (55, (-1 / 3)), (63, (-1 / 6)), (143, (1 / 2))]

def value3269 : Sparse (Fin 909) := [(0, (-7 / 1440)), (1, (11 / 288)), (2, (29 / 288)), (3, (11 / 18)), (5, (-1 / 4)), (6, (1 / 32)), (7, (1 / 3)), (8, (1 / 6)), (11, (1 / 9)), (13, (1 / 18)), (26, (1 / 6)), (35, (11 / 18)), (51, (-1 / 6)), (52, (11 / 18)), (59, (-1 / 3)), (85, (1 / 2)), (103, (1 / 2)), (123, (-1 / 6)), (128, (1 / 18)), (228, (-2 / 3)), (315, (1 / 2)), (545, (1 / 2)), (721, (-1 / 6))]

def value3270 : Sparse (Fin 909) := [(0, (-1 / 160)), (1, (23 / 288)), (2, (17 / 144)), (3, (7 / 18)), (5, (-2 / 9)), (6, (1 / 36)), (7, (1 / 6)), (8, (2 / 9)), (12, (1 / 9)), (13, (7 / 18)), (26, (1 / 9)), (35, (5 / 18)), (52, (2 / 9)), (54, (-1 / 6)), (59, (-1 / 6)), (82, (1 / 18)), (85, (1 / 1)), (199, (-1 / 6)), (228, (-1 / 3)), (329, (1 / 1)), (540, (1 / 2)), (728, (-1 / 6)), (794, (1 / 1))]

def value3271 : Sparse (Fin 909) := [(0, (-1 / 180)), (1, (1 / 48)), (2, (11 / 72)), (3, (8 / 9)), (4, (2 / 9)), (5, (-1 / 4)), (6, (1 / 48)), (7, (5 / 9)), (8, (5 / 18)), (11, (1 / 9)), (26, (7 / 18)), (35, (13 / 18)), (52, (4 / 9)), (81, (-1 / 2)), (84, (1 / 2)), (85, (1 / 1)), (228, (-5 / 6))]

def value3272 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (19 / 288)), (2, (1 / 9)), (3, (4 / 9)), (4, (1 / 18)), (5, (-19 / 72)), (6, (5 / 144)), (7, (7 / 18)), (8, (1 / 6)), (11, (1 / 9)), (26, (1 / 6)), (33, (-1 / 6)), (35, (5 / 9)), (51, (-1 / 6)), (52, (7 / 18)), (69, (1 / 18)), (70, (1 / 18)), (81, (-1 / 6)), (85, (1 / 2)), (228, (-2 / 3)), (259, (-1 / 6)), (306, (-1 / 6)), (308, (-1 / 6)), (315, (1 / 2)), (322, (1 / 2)), (517, (1 / 2)), (721, (-1 / 6))]

def value3273 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (5 / 96)), (2, (7 / 96)), (3, (5 / 18)), (4, (1 / 18)), (5, (-13 / 72)), (6, (5 / 288)), (7, (1 / 9)), (8, (1 / 6)), (11, (1 / 18)), (26, (1 / 9)), (35, (5 / 18)), (39, (1 / 2)), (52, (7 / 18)), (55, (-1 / 6)), (81, (-1 / 6)), (85, (1 / 2)), (228, (-1 / 3)), (306, (-1 / 6)), (329, (1 / 1)), (500, (1 / 2)), (541, (1 / 2)), (728, (-1 / 6)), (764, (1 / 2)), (794, (1 / 2))]

def value3274 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (5 / 288)), (2, (3 / 32)), (3, (13 / 18)), (4, (2 / 9)), (5, (-13 / 72)), (6, (1 / 36)), (7, (2 / 9)), (11, (1 / 9)), (26, (1 / 3)), (31, (-1 / 6)), (33, (-1 / 6)), (35, (11 / 18)), (52, (1 / 2)), (81, (-1 / 6)), (85, (1 / 2)), (99, (1 / 2)), (123, (-1 / 6)), (228, (-2 / 3)), (237, (-1 / 6)), (306, (-1 / 6)), (315, (1 / 2)), (517, (1 / 2)), (721, (-1 / 6))]

def value3275 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-31 / 288)), (2, (7 / 96)), (3, (17 / 18)), (4, (1 / 3)), (5, (-1 / 12)), (6, (1 / 144)), (7, (1 / 6)), (8, (1 / 18)), (12, (1 / 18)), (13, (1 / 6)), (24, (-1 / 6)), (26, (1 / 3)), (27, (1 / 24)), (31, (-1 / 6)), (35, (1 / 3)), (51, (-1 / 2)), (52, (1 / 3)), (56, (-1 / 3)), (99, (1 / 2)), (103, (1 / 2)), (123, (-1 / 3)), (237, (-1 / 6))]

def value3276 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 32)), (2, (23 / 288)), (3, (11 / 18)), (4, (1 / 9)), (5, (-5 / 36)), (6, (1 / 48)), (7, (1 / 18)), (8, (1 / 18)), (12, (1 / 9)), (13, (4 / 9)), (26, (1 / 9)), (35, (5 / 18)), (40, (1 / 2)), (52, (1 / 3)), (55, (-1 / 6)), (56, (-1 / 6)), (81, (-1 / 6)), (82, (1 / 18)), (85, (1 / 2)), (128, (1 / 18)), (201, (-1 / 6)), (228, (-1 / 6)), (306, (-1 / 6)), (329, (1 / 2)), (541, (1 / 2)), (728, (-1 / 6)), (760, (1 / 2)), (794, (3 / 2))]

def value3277 : Sparse (Fin 909) := [(1, (-5 / 72)), (2, (1 / 9)), (3, (13 / 9)), (4, (1 / 2)), (5, (-1 / 9)), (6, (1 / 72)), (7, (1 / 3)), (11, (1 / 9)), (26, (7 / 9)), (35, (5 / 9)), (52, (1 / 3)), (81, (-2 / 3)), (83, (1 / 2)), (85, (1 / 1)), (228, (-1 / 1))]

def value3278 : Sparse (Fin 909) := [(0, (-1 / 144)), (1, (-1 / 36)), (2, (-1 / 32)), (3, (13 / 18)), (4, (1 / 9)), (5, (-1 / 24)), (6, (1 / 288)), (7, (1 / 6)), (12, (1 / 18)), (13, (1 / 9)), (23, (-1 / 6)), (25, (-1 / 2)), (26, (7 / 18)), (33, (-1 / 6)), (35, (1 / 9)), (51, (-1 / 6)), (54, (-1 / 3)), (56, (-1 / 6)), (97, (1 / 2)), (123, (-1 / 6)), (124, (-1 / 6)), (137, (1 / 2)), (197, (-1 / 6)), (216, (1 / 2)), (217, (1 / 2))]

def value3279 : Sparse (Fin 909) := [(0, (-7 / 1440)), (1, (1 / 288)), (2, (-5 / 144)), (3, (2 / 3)), (4, (1 / 9)), (5, (-1 / 36)), (7, (1 / 6)), (8, (1 / 18)), (13, (1 / 6)), (23, (-1 / 6)), (24, (-1 / 6)), (25, (-1 / 2)), (26, (7 / 18)), (35, (1 / 6)), (36, (1 / 2)), (39, (1 / 2)), (54, (-1 / 1)), (56, (-1 / 6)), (97, (1 / 2)), (217, (1 / 2))]

def value3280 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (-19 / 288)), (2, (17 / 288)), (3, (1 / 2)), (4, (1 / 6)), (5, (-1 / 36)), (6, (1 / 288)), (8, (1 / 9)), (12, (1 / 9)), (13, (1 / 6)), (17, (1 / 2)), (24, (-1 / 3)), (26, (1 / 18)), (35, (1 / 18)), (39, (1 / 1)), (42, (1 / 2)), (51, (-1 / 6)), (52, (1 / 18)), (56, (-1 / 3)), (99, (1 / 2)), (126, (-1 / 6)), (146, (1 / 2)), (197, (-1 / 6)), (216, (1 / 2))]

def value3281 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-43 / 288)), (2, (1 / 16)), (3, (8 / 9)), (4, (1 / 3)), (12, (5 / 18)), (13, (1 / 6)), (22, (1 / 2)), (26, (1 / 6)), (31, (-1 / 3)), (33, (-1 / 3)), (35, (1 / 18)), (39, (1 / 2)), (42, (1 / 1)), (52, (1 / 18)), (55, (-1 / 6)), (99, (1 / 2)), (123, (-1 / 6)), (204, (1 / 2)), (217, (1 / 2)), (237, (-1 / 6))]

def value3282 : Sparse (Fin 909) := [(0, (11 / 1440)), (1, (-55 / 288)), (2, (1 / 18)), (3, (8 / 9)), (4, (1 / 3)), (12, (5 / 18)), (13, (4 / 9)), (22, (1 / 2)), (25, (-1 / 6)), (26, (1 / 9)), (31, (-1 / 3)), (33, (-1 / 3)), (35, (1 / 18)), (39, (1 / 2)), (42, (1 / 1)), (54, (-1 / 6)), (56, (-1 / 6)), (204, (1 / 2)), (217, (1 / 2))]

def value3283 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-19 / 144)), (2, (7 / 144)), (3, (7 / 6)), (4, (1 / 3)), (12, (4 / 9)), (13, (11 / 18)), (26, (1 / 9)), (33, (-1 / 3)), (35, (1 / 6)), (39, (1 / 2)), (42, (1 / 2)), (51, (-1 / 2)), (52, (1 / 9)), (54, (-1 / 3)), (56, (-1 / 2))]

def value3284 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-3 / 32)), (2, (1 / 36)), (3, (1 / 3)), (4, (1 / 18)), (5, (-1 / 36)), (6, (1 / 288)), (7, (2 / 9)), (12, (1 / 9)), (13, (1 / 18)), (23, (-1 / 2)), (24, (-1 / 2)), (25, (-1 / 6)), (27, (1 / 8)), (35, (1 / 9)), (48, (1 / 2)), (55, (-1 / 3)), (63, (-1 / 6)), (69, (1 / 18)), (70, (1 / 18)), (124, (-1 / 3)), (126, (-1 / 6)), (196, (-1 / 6)), (197, (-1 / 3)), (643, (1 / 2)), (751, (1 / 2))]

def value3285 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 48)), (2, (-5 / 144)), (3, (1 / 6)), (6, (-1 / 144)), (7, (2 / 9)), (11, (1 / 9)), (26, (1 / 9)), (35, (7 / 18)), (36, (1 / 2)), (52, (1 / 9)), (55, (-1 / 6)), (69, (1 / 18)), (70, (1 / 18)), (228, (-1 / 3)), (306, (-1 / 6)), (312, (1 / 1)), (498, (1 / 2)), (728, (-1 / 6)), (783, (1 / 2)), (794, (1 / 1))]

def value3286 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 32)), (3, (1 / 3)), (4, (1 / 6)), (12, (1 / 6)), (33, (-1 / 1)), (36, (3 / 2)), (54, (-1 / 2)), (55, (-1 / 2)), (306, (-1 / 2)), (312, (3 / 2)), (498, (3 / 2)), (721, (-1 / 2)), (723, (-1 / 6)), (728, (-1 / 6)), (783, (1 / 1))]

def value3287 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (-11 / 288)), (3, (2 / 3)), (4, (2 / 9)), (26, (1 / 2)), (37, (3 / 2)), (56, (-1 / 2)), (81, (-1 / 2)), (83, (3 / 2)), (228, (-2 / 3)), (501, (3 / 2)), (784, (1 / 1)), (796, (-1 / 6))]

def value3288 : Sparse (Fin 909) := [(1, (-1 / 36)), (2, (1 / 24)), (3, (5 / 18)), (4, (1 / 9)), (5, (-1 / 36)), (7, (1 / 9)), (12, (1 / 18)), (23, (-1 / 3)), (24, (-1 / 3)), (27, (1 / 12)), (55, (-1 / 3)), (68, (1 / 24)), (124, (-1 / 6)), (126, (-1 / 3)), (197, (-1 / 3))]

def value3289 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 36)), (2, (11 / 288)), (3, (1 / 2)), (4, (1 / 6)), (7, (1 / 18)), (12, (5 / 18)), (15, (1 / 1)), (23, (-1 / 2)), (24, (-1 / 3)), (25, (-1 / 3)), (27, (1 / 12)), (48, (1 / 2)), (51, (-1 / 6)), (124, (-1 / 6)), (137, (1 / 1)), (205, (1 / 1)), (230, (1 / 2))]

def value3290 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (-1 / 288)), (2, (5 / 144)), (3, (1 / 2)), (4, (1 / 6)), (5, (-5 / 72)), (6, (1 / 72)), (7, (1 / 18)), (11, (1 / 18)), (26, (1 / 3)), (33, (-1 / 3)), (35, (2 / 9)), (37, (1 / 1)), (52, (1 / 6)), (55, (-1 / 3)), (81, (-1 / 3)), (83, (1 / 2)), (228, (-1 / 2)), (306, (-1 / 3)), (312, (1 / 2)), (517, (1 / 1)), (541, (1 / 1)), (721, (-1 / 6)), (728, (-1 / 6)), (784, (1 / 1))]

def value3291 : Sparse (Fin 909) := [(0, (1 / 288)), (1, (-5 / 36)), (2, (5 / 288)), (3, (7 / 9)), (4, (1 / 3)), (5, (-1 / 12)), (6, (1 / 72)), (7, (1 / 9)), (24, (-1 / 3)), (26, (1 / 3)), (27, (1 / 12)), (31, (-1 / 3)), (35, (2 / 9)), (52, (2 / 9)), (68, (1 / 24)), (99, (1 / 1)), (123, (-1 / 3)), (124, (-1 / 6)), (126, (-1 / 3)), (197, (-1 / 3)), (237, (-1 / 3))]

def value3292 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 32)), (2, (5 / 144)), (3, (5 / 18)), (4, (1 / 9)), (5, (-1 / 8)), (6, (1 / 36)), (7, (1 / 18)), (11, (1 / 18)), (26, (1 / 9)), (33, (-1 / 3)), (35, (2 / 9)), (40, (1 / 1)), (52, (1 / 6)), (55, (-1 / 3)), (228, (-1 / 6)), (306, (-1 / 3)), (312, (1 / 2)), (721, (-1 / 6)), (728, (-1 / 6)), (760, (1 / 1)), (794, (2 / 1))]

def value3293 : Sparse (Fin 909) := [(0, (11 / 1440)), (1, (-5 / 36)), (2, (5 / 96)), (3, (5 / 6)), (4, (1 / 3)), (5, (-1 / 72)), (7, (1 / 6)), (12, (1 / 3)), (13, (1 / 9)), (23, (-1 / 1)), (24, (-1 / 1)), (25, (-1 / 2)), (27, (1 / 6)), (35, (1 / 9)), (55, (-1 / 1)), (63, (-1 / 3))]

def value3294 : Sparse (Fin 909) := [(1, (-35 / 288)), (2, (5 / 288)), (3, (1 / 2)), (4, (1 / 6)), (5, (-1 / 72)), (7, (1 / 6)), (12, (1 / 6)), (13, (1 / 9)), (23, (-1 / 2)), (24, (-1 / 1)), (27, (1 / 8)), (35, (1 / 9)), (55, (-1 / 1)), (68, (1 / 24)), (124, (-1 / 2)), (126, (-1 / 2)), (196, (-1 / 3)), (197, (-1 / 1)), (290, (3 / 2)), (728, (-1 / 2))]

def value3295 : Sparse (Fin 909) := [(0, (19 / 480)), (1, (-7 / 18)), (2, (1 / 32)), (3, (17 / 18)), (4, (8 / 9)), (12, (1 / 18)), (25, (-2 / 3)), (26, (4 / 9)), (31, (-5 / 6)), (35, (1 / 18)), (44, (1 / 1)), (55, (-1 / 6)), (108, (1 / 2)), (123, (-1 / 6))]

def value3296 : Sparse (Fin 909) := [(0, (1 / 180)), (1, (-7 / 72)), (2, (-1 / 72)), (3, (19 / 18)), (4, (7 / 18)), (7, (1 / 9)), (12, (5 / 18)), (13, (1 / 9)), (23, (-1 / 3)), (24, (-1 / 6)), (25, (-1 / 2)), (26, (4 / 9)), (31, (-1 / 6)), (35, (1 / 6)), (44, (1 / 2)), (55, (-1 / 2)), (63, (-1 / 6)), (108, (1 / 2)), (123, (-1 / 6))]

def value3297 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (-5 / 144)), (2, (1 / 36)), (3, (7 / 18)), (4, (1 / 18)), (5, (-5 / 72)), (6, (1 / 96)), (7, (1 / 9)), (12, (1 / 6)), (13, (7 / 18)), (35, (5 / 18)), (42, (1 / 1)), (51, (-1 / 3)), (52, (2 / 9)), (54, (-1 / 6)), (56, (-1 / 3)), (82, (1 / 9)), (128, (1 / 9)), (199, (-1 / 6)), (262, (-1 / 3)), (286, (1 / 2)), (309, (-1 / 6)), (328, (1 / 1)), (506, (1 / 1)), (796, (-1 / 6)), (798, (1 / 1))]

def value3298 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 16)), (2, (1 / 16)), (3, (1 / 6)), (4, (1 / 18)), (5, (-1 / 6)), (6, (1 / 72)), (8, (5 / 18)), (13, (1 / 9)), (24, (-1 / 6)), (26, (1 / 18)), (35, (1 / 9)), (39, (1 / 2)), (52, (2 / 9)), (56, (-1 / 3)), (71, (1 / 9)), (82, (1 / 18)), (99, (1 / 2)), (126, (-1 / 6)), (128, (1 / 18)), (197, (-1 / 6)), (201, (-1 / 6)), (262, (-1 / 6)), (288, (1 / 2)), (329, (1 / 2)), (500, (1 / 1)), (764, (1 / 2)), (796, (-1 / 6)), (798, (1 / 2))]

def value3299 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-7 / 288)), (2, (19 / 288)), (3, (13 / 18)), (4, (2 / 9)), (5, (-1 / 18)), (6, (1 / 144)), (7, (1 / 9)), (11, (1 / 18)), (12, (1 / 18)), (13, (1 / 9)), (26, (1 / 3)), (35, (5 / 18)), (40, (1 / 2)), (52, (1 / 6)), (55, (-1 / 6)), (56, (-1 / 6)), (75, (1 / 2)), (81, (-1 / 6)), (85, (1 / 2)), (201, (-1 / 6)), (228, (-1 / 3)), (508, (3 / 2)), (541, (1 / 2)), (794, (1 / 2)), (796, (-1 / 6))]

def value3300 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-11 / 288)), (2, (5 / 96)), (3, (4 / 9)), (4, (1 / 6)), (5, (-1 / 9)), (6, (1 / 288)), (7, (1 / 3)), (8, (2 / 9)), (10, (-1 / 6)), (12, (1 / 18)), (13, (1 / 9)), (26, (1 / 9)), (35, (2 / 9)), (40, (1 / 1)), (56, (-1 / 3)), (81, (-1 / 6)), (82, (1 / 18)), (85, (1 / 1)), (228, (-1 / 3)), (501, (1 / 2)), (508, (1 / 1)), (794, (1 / 1)), (796, (-1 / 6))]

def value3301 : Sparse (Fin 909) := [(0, (7 / 480)), (1, (-2 / 9)), (2, (13 / 288)), (3, (1 / 1)), (4, (2 / 3)), (12, (1 / 6)), (13, (1 / 9)), (26, (7 / 18)), (37, (1 / 2)), (40, (1 / 1)), (56, (-1 / 2))]

def value3302 : Sparse (Fin 909) := [(0, (1 / 160)), (1, (-19 / 144)), (2, (7 / 288)), (3, (17 / 18)), (4, (5 / 9)), (5, (-1 / 72)), (7, (1 / 6)), (11, (1 / 18)), (26, (5 / 9)), (35, (5 / 18)), (40, (1 / 1)), (52, (1 / 18)), (55, (-1 / 6)), (56, (-1 / 3)), (81, (-1 / 6)), (85, (1 / 1)), (228, (-1 / 2)), (501, (1 / 2)), (508, (1 / 1)), (794, (1 / 1)), (796, (-1 / 6))]

def value3303 : Sparse (Fin 909) := [(0, (-1 / 120)), (1, (-13 / 288)), (2, (-1 / 96)), (3, (11 / 18)), (5, (-7 / 36)), (6, (1 / 48)), (7, (1 / 9)), (8, (1 / 18)), (9, (-1 / 72)), (12, (1 / 6)), (13, (1 / 3)), (26, (7 / 18)), (27, (1 / 12)), (35, (5 / 9)), (51, (-1 / 6)), (55, (-1 / 3)), (68, (1 / 12)), (71, (1 / 18)), (82, (1 / 9)), (197, (-1 / 3)), (236, (-1 / 6)), (238, (-1 / 3)), (309, (-1 / 6)), (728, (-1 / 6)), (810, (1 / 2))]

def value3304 : Sparse (Fin 909) := [(0, (-17 / 1440)), (1, (-1 / 144)), (2, (13 / 144)), (3, (5 / 9)), (5, (-7 / 72)), (6, (1 / 288)), (7, (1 / 3)), (8, (5 / 18)), (10, (-1 / 3)), (12, (1 / 6)), (13, (1 / 6)), (27, (1 / 24)), (35, (1 / 18)), (51, (-1 / 3)), (52, (1 / 18)), (55, (-1 / 2)), (69, (1 / 18)), (71, (1 / 18)), (95, (1 / 2)), (124, (-1 / 6)), (126, (-1 / 3)), (236, (-1 / 6)), (290, (1 / 2)), (538, (1 / 2)), (811, (1 / 2))]

def value3305 : Sparse (Fin 909) := [(0, (1 / 288)), (1, (-7 / 288)), (2, (5 / 32)), (3, (7 / 18)), (4, (1 / 18)), (5, (-11 / 72)), (6, (1 / 96)), (7, (5 / 18)), (8, (1 / 2)), (24, (-1 / 3)), (26, (1 / 18)), (30, (-1 / 3)), (35, (1 / 18)), (49, (1 / 2)), (71, (1 / 9)), (107, (1 / 1)), (126, (-1 / 3)), (197, (-1 / 6)), (236, (-1 / 2)), (810, (1 / 2)), (811, (1 / 2))]

def value3306 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-7 / 96)), (2, (7 / 96)), (3, (7 / 18)), (4, (2 / 9)), (5, (-1 / 72)), (7, (1 / 18)), (23, (-1 / 6)), (24, (-1 / 3)), (27, (1 / 8)), (31, (-2 / 3)), (47, (1 / 2)), (51, (-1 / 2)), (52, (1 / 9)), (55, (-1 / 6)), (106, (1 / 1)), (237, (-1 / 3)), (308, (-1 / 6)), (538, (1 / 1)), (640, (1 / 2)), (812, (1 / 1))]

def value3307 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (1 / 16)), (3, (1 / 6)), (4, (1 / 18)), (5, (-1 / 9)), (6, (1 / 72)), (8, (1 / 18)), (9, (-1 / 72)), (24, (-1 / 3)), (27, (1 / 8)), (30, (-1 / 6)), (31, (-1 / 6)), (33, (-1 / 3)), (51, (-1 / 6)), (52, (1 / 18)), (55, (-1 / 2)), (68, (1 / 12)), (71, (1 / 18)), (197, (-1 / 3)), (236, (-1 / 6)), (237, (-1 / 3)), (306, (-1 / 3)), (308, (-1 / 6)), (728, (-1 / 6)), (811, (1 / 2))]

def value3308 : Sparse (Fin 909) := [(0, (17 / 1440)), (1, (-1 / 16)), (2, (1 / 12)), (3, (1 / 18)), (4, (1 / 18)), (5, (-1 / 18)), (6, (1 / 288)), (8, (2 / 9)), (24, (-1 / 2)), (27, (5 / 24)), (30, (-1 / 2)), (49, (1 / 2)), (55, (-1 / 6)), (71, (1 / 9)), (126, (-1 / 3)), (197, (-1 / 6)), (236, (-1 / 2)), (811, (1 / 2)), (812, (1 / 2))]

def value3309 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 18)), (2, (7 / 96)), (3, (1 / 6)), (4, (1 / 18)), (5, (-1 / 12)), (7, (1 / 6)), (8, (1 / 6)), (12, (1 / 18)), (23, (-1 / 3)), (24, (-1 / 2)), (27, (1 / 4)), (30, (-1 / 6)), (51, (-1 / 6)), (55, (-1 / 3)), (69, (1 / 18)), (71, (1 / 18)), (105, (1 / 2)), (106, (1 / 2)), (124, (-1 / 6)), (126, (-1 / 3)), (236, (-1 / 6)), (290, (1 / 2)), (299, (1 / 1)), (751, (1 / 2)), (812, (1 / 2))]

def value3310 : Sparse (Fin 909) := [(0, (1 / 90)), (1, (-31 / 288)), (2, (41 / 288)), (3, (2 / 9)), (4, (1 / 9)), (5, (-1 / 12)), (7, (1 / 9)), (8, (2 / 9)), (23, (-1 / 3)), (24, (-1 / 1)), (27, (5 / 12)), (30, (-2 / 3)), (55, (-1 / 3)), (68, (1 / 24)), (125, (-1 / 6)), (126, (-1 / 3)), (236, (-1 / 3))]

def value3311 : Sparse (Fin 909) := [(0, (1 / 180)), (1, (-11 / 96)), (2, (5 / 72)), (3, (1 / 6)), (4, (1 / 6)), (5, (-1 / 24)), (6, (1 / 288)), (8, (1 / 9)), (24, (-2 / 3)), (27, (5 / 24)), (30, (-1 / 3)), (31, (-1 / 6)), (55, (-1 / 3)), (68, (1 / 24)), (106, (1 / 2)), (126, (-1 / 2)), (197, (-1 / 6)), (236, (-1 / 6)), (237, (-1 / 6))]

def value3312 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (-1 / 144)), (2, (1 / 96)), (5, (-1 / 72)), (6, (1 / 288)), (23, (-1 / 6)), (27, (1 / 8)), (30, (-1 / 6)), (31, (-1 / 3)), (68, (1 / 24)), (105, (1 / 2)), (124, (-1 / 6)), (236, (-2 / 3)), (237, (-1 / 6))]

def value3313 : Sparse (Fin 909) := [(0, (1 / 144)), (1, (-1 / 24)), (2, (1 / 72)), (5, (-1 / 36)), (6, (1 / 144)), (23, (-1 / 3)), (25, (-1 / 3)), (27, (1 / 6)), (30, (-1 / 3)), (31, (-1 / 3)), (63, (-1 / 3)), (68, (1 / 24)), (105, (1 / 1)), (124, (-1 / 3)), (196, (-1 / 6)), (236, (-1 / 3)), (237, (-1 / 3))]

def value3314 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (1 / 144)), (2, (11 / 144)), (3, (1 / 6)), (4, (1 / 18)), (5, (-1 / 6)), (6, (1 / 32)), (7, (1 / 18)), (9, (-1 / 72)), (27, (1 / 12)), (31, (-1 / 3)), (33, (-2 / 3)), (35, (1 / 9)), (51, (-1 / 3)), (52, (2 / 9)), (55, (-1 / 3)), (68, (1 / 24)), (69, (1 / 18)), (123, (-1 / 3)), (124, (-1 / 6)), (237, (-1 / 3)), (259, (-1 / 3)), (306, (-2 / 3)), (308, (-1 / 3)), (312, (1 / 2)), (315, (1 / 1)), (721, (-1 / 2)), (728, (-1 / 6))]

def value3315 : Sparse (Fin 909) := [(0, (1 / 144)), (1, (5 / 96)), (2, (5 / 288)), (5, (-1 / 72)), (17, (1 / 1)), (23, (-1 / 3)), (25, (-1 / 2)), (27, (1 / 8)), (30, (-1 / 3)), (31, (-1 / 2)), (108, (1 / 2)), (123, (-1 / 6)), (124, (-1 / 6)), (203, (2 / 1)), (230, (1 / 2))]

def value3316 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (5 / 72)), (2, (1 / 144)), (5, (-1 / 36)), (14, (1 / 2)), (23, (-1 / 2)), (25, (-2 / 3)), (27, (1 / 8)), (31, (-1 / 3)), (63, (-1 / 6)), (108, (1 / 1)), (123, (-1 / 3)), (124, (-1 / 6)), (129, (1 / 2)), (203, (1 / 1)), (230, (1 / 1))]

def value3317 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-3 / 16)), (2, (1 / 96)), (23, (-2 / 3)), (25, (-1 / 3)), (27, (-1 / 6)), (68, (1 / 24)), (124, (-1 / 3)), (230, (1 / 2))]

def value3318 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (-7 / 144)), (2, (1 / 288)), (14, (1 / 2)), (23, (-1 / 3)), (25, (-1 / 6)), (27, (1 / 12)), (63, (-1 / 2)), (124, (-1 / 6)), (129, (1 / 2)), (196, (-1 / 6)), (230, (1 / 2))]

def value3319 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-7 / 288)), (5, (-1 / 72)), (6, (1 / 288)), (23, (-1 / 6)), (25, (-1 / 3)), (27, (1 / 24)), (30, (-1 / 3)), (31, (-1 / 6)), (68, (1 / 24)), (123, (-1 / 3)), (124, (-1 / 6)), (203, (1 / 2)), (236, (-1 / 6)), (237, (-1 / 3))]

def value3320 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (-2 / 9)), (2, (-1 / 72)), (23, (-1 / 1)), (27, (1 / 12)), (63, (-2 / 3))]

def value3321 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-1 / 96)), (2, (5 / 288)), (25, (-1 / 2)), (27, (1 / 12)), (30, (-1 / 6)), (31, (-1 / 2)), (105, (1 / 2)), (108, (1 / 2)), (123, (-1 / 6)), (237, (-1 / 6))]

def value3322 : Sparse (Fin 909) := [(0, (7 / 1440)), (1, (-7 / 144)), (2, (-1 / 96)), (17, (1 / 2)), (23, (-1 / 3)), (25, (-2 / 3)), (27, (1 / 24)), (31, (-2 / 3)), (63, (-1 / 3)), (105, (1 / 2)), (108, (1 / 2)), (123, (-1 / 6)), (231, (1 / 2)), (237, (-1 / 6))]

def value3323 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (1 / 32)), (2, (17 / 288)), (3, (7 / 18)), (4, (1 / 18)), (5, (-5 / 36)), (6, (5 / 288)), (7, (1 / 9)), (8, (1 / 9)), (11, (1 / 18)), (12, (1 / 9)), (13, (2 / 9)), (25, (-1 / 6)), (26, (1 / 9)), (35, (1 / 3)), (39, (1 / 2)), (51, (-1 / 6)), (52, (5 / 18)), (54, (-1 / 3)), (56, (-1 / 6)), (59, (-1 / 6)), (74, (1 / 2)), (82, (1 / 18)), (89, (1 / 2)), (123, (-1 / 6)), (128, (1 / 18)), (199, (-1 / 6)), (201, (-1 / 6)), (226, (-1 / 6)), (228, (-1 / 6)), (315, (1 / 2)), (507, (3 / 2)), (540, (1 / 2)), (721, (-1 / 6)), (723, (-1 / 6)), (764, (1 / 2))]

def value3324 : Sparse (Fin 909) := [(1, (-1 / 16)), (2, (-5 / 144)), (3, (1 / 9)), (12, (1 / 9)), (33, (-1 / 3)), (39, (1 / 1)), (51, (-1 / 3)), (54, (-2 / 3)), (259, (-1 / 3)), (282, (1 / 2)), (306, (-1 / 6)), (308, (-1 / 6)), (315, (1 / 1)), (498, (1 / 2)), (507, (1 / 1)), (721, (-1 / 3)), (723, (-1 / 3)), (764, (1 / 1))]

def value3325 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-11 / 288)), (2, (5 / 144)), (3, (5 / 18)), (4, (1 / 18)), (5, (-5 / 72)), (6, (1 / 72)), (7, (1 / 18)), (11, (1 / 18)), (12, (1 / 18)), (25, (-1 / 3)), (26, (1 / 9)), (31, (-1 / 3)), (33, (-1 / 3)), (35, (2 / 9)), (39, (1 / 1)), (52, (1 / 6)), (54, (-1 / 3)), (87, (1 / 2)), (123, (-1 / 3)), (226, (-1 / 6)), (228, (-1 / 6)), (237, (-1 / 6)), (306, (-1 / 6)), (315, (1 / 1)), (498, (1 / 2)), (507, (1 / 1)), (721, (-1 / 3)), (723, (-1 / 6)), (764, (1 / 1))]

def value3326 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (-19 / 144)), (2, (1 / 48)), (3, (7 / 9)), (4, (2 / 9)), (5, (-1 / 24)), (6, (1 / 288)), (7, (1 / 9)), (12, (2 / 9)), (23, (-1 / 6)), (25, (-2 / 3)), (26, (2 / 9)), (27, (1 / 24)), (31, (-1 / 3)), (35, (2 / 9)), (51, (-2 / 3)), (52, (2 / 9)), (54, (-2 / 3)), (87, (1 / 2)), (89, (1 / 1)), (123, (-2 / 3)), (226, (-1 / 2)), (237, (-1 / 6))]

def value3327 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 36)), (2, (1 / 36)), (5, (-1 / 72)), (6, (1 / 288)), (17, (1 / 2)), (23, (-1 / 3)), (25, (-2 / 3)), (27, (1 / 24)), (31, (-1 / 2)), (63, (-1 / 6)), (87, (1 / 2)), (108, (1 / 2)), (123, (-1 / 3)), (124, (-1 / 6)), (196, (-1 / 6)), (203, (1 / 2)), (216, (1 / 2)), (226, (-1 / 6))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value3328 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-1 / 24)), (2, (7 / 96)), (5, (-1 / 24)), (6, (1 / 96)), (23, (-1 / 2)), (25, (-1 / 1)), (27, (1 / 8)), (31, (-1 / 1)), (68, (1 / 24)), (87, (3 / 2)), (123, (-1 / 1)), (124, (-1 / 2)), (196, (-1 / 3)), (226, (-1 / 2)), (237, (-1 / 2))]

def value3329 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (7 / 288)), (2, (5 / 288)), (23, (-1 / 6)), (25, (-1 / 3)), (27, (1 / 24)), (31, (-1 / 2)), (87, (1 / 2)), (108, (1 / 2)), (123, (-1 / 2)), (226, (-1 / 6)), (237, (-1 / 6))]

def value3330 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 12)), (2, (1 / 8)), (5, (-3 / 8)), (6, (1 / 24)), (7, (5 / 18)), (8, (5 / 9)), (9, (-1 / 9)), (69, (2 / 3)), (70, (2 / 9)), (71, (4 / 3))]

def value3331 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-13 / 288)), (2, (5 / 24)), (3, (1 / 1)), (4, (1 / 6)), (5, (-2 / 9)), (6, (1 / 72)), (7, (1 / 3)), (8, (1 / 3)), (12, (1 / 3)), (13, (13 / 18)), (35, (5 / 18)), (51, (-1 / 2)), (52, (1 / 2)), (59, (-1 / 2)), (60, (1 / 9)), (128, (1 / 6))]

def value3332 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-1 / 288)), (2, (1 / 24)), (3, (5 / 6)), (5, (-1 / 18)), (6, (1 / 288)), (7, (1 / 3)), (10, (-1 / 2)), (12, (1 / 3)), (13, (17 / 18)), (35, (11 / 18)), (52, (1 / 3)), (59, (-1 / 2)), (60, (1 / 9)), (82, (1 / 6)), (128, (1 / 6))]

def value3333 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (23 / 288)), (2, (-1 / 48)), (3, (1 / 6)), (5, (-7 / 72)), (6, (1 / 72)), (7, (1 / 6)), (12, (1 / 6)), (13, (5 / 18)), (35, (4 / 9)), (52, (1 / 3)), (60, (1 / 9))]

def value3334 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (1 / 18)), (2, (7 / 48)), (3, (2 / 9)), (5, (-13 / 36)), (6, (11 / 288)), (7, (7 / 18)), (8, (4 / 9)), (35, (2 / 9)), (52, (2 / 9))]

def value3335 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 72)), (2, (-17 / 288)), (3, (1 / 3)), (5, (1 / 24)), (6, (-1 / 72)), (7, (1 / 3)), (9, (-1 / 36)), (12, (1 / 9)), (13, (1 / 9)), (23, (-1 / 6)), (35, (2 / 9)), (69, (1 / 9)), (70, (1 / 9)), (124, (-1 / 6)), (196, (-1 / 6))]

def value3336 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-11 / 144)), (2, (7 / 288)), (3, (5 / 18)), (5, (-1 / 24)), (6, (1 / 96)), (7, (1 / 9)), (12, (1 / 9)), (13, (1 / 18)), (23, (-1 / 6)), (26, (1 / 9)), (35, (1 / 9)), (54, (-1 / 6))]

def value3337 : Sparse (Fin 909) := [(0, (1 / 144)), (1, (-3 / 16)), (2, (1 / 24)), (3, (5 / 9)), (12, (1 / 6)), (13, (1 / 3))]

def value3338 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-11 / 144)), (2, (-1 / 96)), (3, (7 / 18)), (5, (-1 / 36)), (6, (1 / 288)), (7, (1 / 9)), (12, (1 / 9)), (13, (1 / 18)), (23, (-1 / 6)), (26, (1 / 9)), (35, (1 / 18)), (55, (-1 / 6))]

def value3339 : Sparse (Fin 909) := [(0, (1 / 160)), (1, (-11 / 96)), (2, (1 / 24)), (3, (4 / 9)), (4, (1 / 6)), (12, (1 / 9)), (26, (1 / 9))]

def value3340 : Sparse (Fin 909) := [(0, (-1 / 120)), (1, (5 / 48)), (2, (5 / 36)), (3, (1 / 6)), (5, (-7 / 24)), (6, (1 / 144)), (7, (2 / 3)), (8, (7 / 18)), (26, (1 / 18)), (35, (5 / 18)), (52, (1 / 18)), (59, (-1 / 6)), (67, (1 / 18)), (75, (1 / 2)), (81, (-1 / 6)), (428, (1 / 2))]

def value3341 : Sparse (Fin 909) := [(0, (-13 / 1440)), (1, (1 / 8)), (2, (17 / 96)), (3, (4 / 9)), (5, (-23 / 72)), (6, (1 / 36)), (7, (1 / 3)), (8, (7 / 18)), (26, (1 / 9)), (33, (-1 / 6)), (35, (5 / 18)), (52, (1 / 3)), (67, (1 / 18)), (81, (-1 / 2)), (86, (1 / 2)), (428, (1 / 2)), (760, (1 / 2)), (855, (1 / 2))]

def value3342 : Sparse (Fin 909) := [(0, (-7 / 720)), (1, (1 / 8)), (2, (5 / 24)), (3, (11 / 18)), (4, (1 / 9)), (5, (-11 / 36)), (6, (1 / 48)), (7, (1 / 3)), (8, (7 / 18)), (11, (1 / 18)), (26, (1 / 6)), (35, (1 / 3)), (52, (4 / 9)), (81, (-5 / 6)), (86, (1 / 2)), (228, (-1 / 6)), (855, (1 / 2))]

def value3343 : Sparse (Fin 909) := [(0, (-1 / 90)), (1, (1 / 6)), (2, (5 / 24)), (3, (5 / 18)), (4, (1 / 18)), (5, (-23 / 72)), (6, (1 / 36)), (7, (1 / 6)), (8, (1 / 3)), (26, (1 / 9)), (35, (1 / 9)), (52, (7 / 18)), (81, (-1 / 6)), (85, (3 / 2)), (86, (1 / 2)), (228, (-1 / 3))]

def value3344 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 24)), (2, (-19 / 288)), (3, (2 / 9)), (5, (-1 / 8)), (6, (1 / 96)), (7, (7 / 18)), (8, (1 / 18)), (11, (2 / 9)), (26, (1 / 2)), (35, (8 / 9)), (67, (1 / 2)), (228, (-1 / 6)), (702, (1 / 2))]

def value3345 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-5 / 48)), (2, (1 / 9)), (3, (7 / 9)), (4, (1 / 6)), (5, (-13 / 72)), (6, (1 / 72)), (7, (11 / 18)), (8, (2 / 9)), (11, (1 / 18)), (26, (2 / 9)), (35, (4 / 9)), (52, (1 / 18)), (57, (1 / 1)), (86, (1 / 1)), (228, (-1 / 6)), (855, (2 / 1))]

def value3346 : Sparse (Fin 909) := [(0, (-7 / 1440)), (1, (-1 / 72)), (2, (1 / 144)), (3, (13 / 18)), (4, (1 / 6)), (5, (-5 / 24)), (6, (5 / 288)), (7, (5 / 9)), (8, (5 / 18)), (11, (1 / 6)), (26, (7 / 18)), (35, (2 / 3)), (52, (1 / 6)), (81, (-1 / 3)), (228, (-1 / 3)), (855, (1 / 2))]

def value3347 : Sparse (Fin 909) := [(0, (1 / 160)), (1, (-3 / 32)), (2, (35 / 288)), (3, (5 / 6)), (4, (2 / 9)), (5, (-19 / 72)), (6, (1 / 32)), (7, (7 / 18)), (8, (2 / 9)), (26, (1 / 3)), (35, (1 / 2)), (52, (1 / 3)), (67, (1 / 9)), (81, (-1 / 3))]

def value3348 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-5 / 288)), (2, (1 / 18)), (3, (7 / 9)), (4, (1 / 6)), (5, (-5 / 36)), (6, (1 / 72)), (7, (1 / 2)), (8, (1 / 9)), (11, (1 / 6)), (26, (4 / 9)), (35, (5 / 6)), (52, (5 / 18)), (67, (1 / 9)), (81, (-1 / 3)), (228, (-1 / 2))]

def value3349 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 96)), (2, (7 / 288)), (3, (5 / 18)), (4, (1 / 9)), (5, (-1 / 9)), (6, (1 / 72)), (7, (5 / 18)), (8, (1 / 9)), (26, (2 / 9)), (35, (7 / 18)), (52, (1 / 9)), (67, (1 / 9))]

def value3350 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (-7 / 144)), (2, (11 / 144)), (3, (4 / 9)), (4, (1 / 9)), (5, (-13 / 72)), (6, (1 / 72)), (7, (1 / 3)), (8, (2 / 9)), (11, (1 / 18)), (26, (1 / 6)), (35, (5 / 18)), (52, (1 / 6)), (81, (-1 / 6)), (228, (-1 / 6))]

def value3351 : Sparse (Fin 909) := [(0, (13 / 1440)), (1, (-19 / 144)), (2, (7 / 144)), (3, (1 / 1)), (4, (1 / 2)), (5, (-1 / 18)), (6, (1 / 96)), (7, (1 / 6)), (11, (1 / 6)), (26, (2 / 3)), (35, (4 / 9)), (52, (1 / 6)), (228, (-1 / 2))]

def value3352 : Sparse (Fin 909) := [(0, (37 / 1440)), (1, (-11 / 48)), (2, (35 / 288)), (3, (7 / 18)), (4, (1 / 3)), (5, (-1 / 36)), (8, (2 / 9)), (26, (1 / 9)), (30, (-1 / 3)), (31, (-1 / 3)), (40, (1 / 2)), (56, (-1 / 6)), (107, (1 / 1)), (239, (1 / 1))]

def value3353 : Sparse (Fin 909) := [(0, (17 / 1440)), (1, (-5 / 36)), (2, (13 / 288)), (3, (5 / 9)), (4, (1 / 6)), (5, (-1 / 72)), (8, (1 / 18)), (12, (1 / 18)), (13, (1 / 18)), (26, (1 / 9)), (40, (1 / 2)), (56, (-1 / 6))]

def value3354 : Sparse (Fin 909) := [(0, (17 / 720)), (1, (-43 / 144)), (2, (1 / 9)), (3, (7 / 9)), (4, (5 / 9)), (5, (-1 / 72)), (8, (1 / 18)), (26, (2 / 9)), (40, (1 / 2)), (56, (-1 / 6)), (57, (1 / 2))]

def value3355 : Sparse (Fin 909) := [(0, (1 / 60)), (1, (-17 / 96)), (2, (1 / 288)), (3, (11 / 18)), (4, (2 / 9)), (26, (5 / 18))]

def value3356 : Sparse (Fin 909) := [(0, (37 / 1440)), (1, (-91 / 288)), (2, (19 / 144)), (3, (1 / 1)), (4, (4 / 9)), (26, (7 / 18)), (57, (1 / 2))]

def value3357 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-25 / 144)), (2, (13 / 96)), (3, (13 / 18)), (4, (1 / 3)), (5, (-1 / 72)), (12, (1 / 9)), (13, (1 / 9)), (26, (1 / 3)), (31, (-1 / 3)), (33, (-2 / 3)), (52, (1 / 18)), (55, (-1 / 6)), (177, (1 / 2))]

def value3358 : Sparse (Fin 909) := [(0, (1 / 72)), (1, (-41 / 288)), (2, (3 / 32)), (3, (1 / 1)), (4, (2 / 3)), (5, (-1 / 72)), (12, (1 / 6)), (13, (1 / 18)), (26, (1 / 3)), (52, (1 / 18)), (55, (-1 / 6)), (57, (1 / 1)), (119, (1 / 1)), (177, (1 / 2))]

def value3359 : Sparse (Fin 909) := [(0, (11 / 1440)), (1, (-61 / 288)), (2, (1 / 16)), (3, (1 / 1)), (4, (11 / 18)), (26, (5 / 9)), (31, (-1 / 3)), (33, (-1 / 6)), (53, (1 / 2)), (57, (1 / 2)), (119, (1 / 1)), (204, (1 / 2))]

def value3360 : Sparse (Fin 909) := [(0, (1 / 180)), (1, (-19 / 144)), (2, (13 / 144)), (3, (2 / 3)), (4, (1 / 3)), (5, (-1 / 36)), (7, (1 / 18)), (8, (1 / 18)), (26, (5 / 18)), (31, (-1 / 3)), (33, (-5 / 6)), (37, (1 / 2)), (40, (1 / 2)), (51, (-1 / 6)), (55, (-1 / 2))]

def value3361 : Sparse (Fin 909) := [(0, (-1 / 180)), (1, (1 / 288)), (2, (1 / 36)), (3, (13 / 18)), (4, (1 / 18)), (5, (-5 / 72)), (6, (1 / 96)), (12, (1 / 18)), (13, (7 / 18)), (26, (1 / 3)), (34, (2 / 9)), (35, (2 / 9)), (51, (-1 / 6)), (52, (1 / 6)), (55, (-1 / 2)), (64, (-5 / 6)), (139, (1 / 2)), (238, (-1 / 3)), (546, (1 / 2))]

def value3362 : Sparse (Fin 909) := [(0, (-7 / 1440)), (1, (-29 / 288)), (2, (5 / 288)), (3, (23 / 18)), (4, (5 / 18)), (6, (1 / 288)), (12, (1 / 18)), (13, (1 / 6)), (26, (1 / 2)), (34, (1 / 2)), (35, (1 / 9)), (139, (1 / 2))]

def value3363 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-5 / 96)), (2, (1 / 36)), (3, (13 / 18)), (4, (5 / 18)), (5, (-1 / 12)), (6, (1 / 96)), (8, (1 / 9)), (13, (1 / 6)), (26, (4 / 9)), (34, (1 / 9)), (35, (5 / 18)), (52, (1 / 18)), (56, (-1 / 2)), (64, (-1 / 6)), (107, (1 / 2)), (190, (1 / 2)), (238, (-1 / 3)), (453, (1 / 1)), (870, (1 / 2))]

def value3364 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-11 / 288)), (2, (-1 / 72)), (3, (8 / 9)), (4, (2 / 9)), (5, (-1 / 72)), (6, (1 / 144)), (13, (7 / 18)), (26, (1 / 2)), (34, (1 / 2)), (35, (2 / 9)), (52, (1 / 18)), (56, (-1 / 6)), (190, (1 / 2))]

def value3365 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-7 / 144)), (2, (31 / 288)), (3, (7 / 9)), (4, (7 / 18)), (5, (-1 / 8)), (6, (1 / 96)), (8, (2 / 9)), (12, (1 / 18)), (13, (1 / 18)), (26, (1 / 3)), (31, (-1 / 6)), (35, (1 / 9)), (45, (1 / 2)), (51, (-1 / 6)), (52, (1 / 18)), (56, (-1 / 3)), (107, (3 / 2)), (238, (-1 / 3)), (870, (1 / 2))]

def value3366 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (1 / 72)), (2, (1 / 144)), (3, (2 / 3)), (4, (1 / 6)), (5, (-13 / 72)), (6, (7 / 288)), (8, (1 / 18)), (9, (-1 / 72)), (11, (1 / 9)), (13, (1 / 2)), (26, (1 / 3)), (35, (11 / 18)), (52, (7 / 18)), (56, (-1 / 3)), (69, (1 / 18)), (71, (1 / 18)), (262, (-1 / 3)), (796, (-1 / 6)), (870, (1 / 2))]

def value3367 : Sparse (Fin 909) := [(0, (-7 / 1440)), (1, (1 / 32)), (2, (-1 / 288)), (3, (11 / 18)), (4, (1 / 6)), (5, (-1 / 6)), (6, (5 / 288)), (8, (1 / 9)), (11, (1 / 6)), (13, (4 / 9)), (26, (4 / 9)), (35, (11 / 18)), (52, (1 / 6)), (56, (-1 / 3)), (228, (-1 / 6)), (546, (1 / 2)), (870, (1 / 2))]

def value3368 : Sparse (Fin 909) := [(0, (7 / 1440)), (1, (-3 / 16)), (2, (1 / 96)), (3, (23 / 18)), (4, (5 / 9)), (5, (-1 / 36)), (6, (1 / 144)), (12, (2 / 9)), (13, (2 / 9)), (26, (5 / 9)), (35, (1 / 6)), (52, (1 / 18)), (56, (-1 / 3)), (204, (1 / 2))]

def value3369 : Sparse (Fin 909) := [(0, (-1 / 144)), (1, (-1 / 36)), (2, (7 / 72)), (3, (7 / 9)), (4, (2 / 9)), (5, (-1 / 18)), (6, (1 / 144)), (12, (1 / 6)), (13, (1 / 6)), (26, (2 / 9)), (27, (1 / 24)), (31, (-1 / 3)), (35, (1 / 18)), (43, (1 / 2)), (51, (-2 / 3)), (52, (1 / 6)), (204, (1 / 2)), (237, (-1 / 6)), (238, (-1 / 6)), (546, (1 / 2)), (745, (1 / 1))]

def value3370 : Sparse (Fin 909) := [(0, (31 / 1440)), (1, (-103 / 288)), (2, (7 / 72)), (3, (7 / 6)), (4, (4 / 9)), (12, (7 / 18)), (13, (7 / 18)), (26, (2 / 9)), (31, (-1 / 3)), (33, (-1 / 3)), (34, (1 / 9))]

def value3371 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-7 / 48)), (2, (5 / 144)), (3, (11 / 9)), (4, (1 / 3)), (12, (4 / 9)), (13, (1 / 2)), (26, (4 / 9)), (33, (-1 / 3)), (34, (1 / 9)), (35, (1 / 6)), (55, (-1 / 2))]

def value3372 : Sparse (Fin 909) := [(0, (13 / 1440)), (1, (-3 / 32)), (2, (1 / 48)), (3, (11 / 18)), (4, (2 / 9)), (12, (1 / 18)), (13, (1 / 18)), (26, (1 / 3)), (34, (1 / 9))]

def value3373 : Sparse (Fin 909) := [(0, (13 / 1440)), (1, (-47 / 288)), (2, (5 / 144)), (3, (5 / 9)), (4, (1 / 6)), (26, (2 / 9))]

def value3374 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-5 / 24)), (2, (7 / 288)), (3, (5 / 18)), (4, (2 / 9)), (26, (1 / 9))]

def value3375 : Sparse (Fin 909) := [(0, (19 / 720)), (1, (-29 / 96)), (2, (1 / 96)), (3, (1 / 1)), (4, (2 / 3)), (12, (1 / 3)), (13, (1 / 9)), (26, (1 / 3)), (35, (1 / 6)), (55, (-1 / 2))]

def value3376 : Sparse (Fin 909) := [(0, (-1 / 144)), (1, (1 / 8)), (2, (7 / 48)), (3, (1 / 6)), (5, (-5 / 18)), (6, (1 / 36)), (7, (11 / 18)), (8, (7 / 18)), (12, (1 / 18)), (13, (2 / 9)), (35, (1 / 3)), (52, (1 / 9)), (59, (-2 / 3)), (71, (1 / 6)), (82, (1 / 18)), (199, (-1 / 6)), (201, (-1 / 6)), (289, (1 / 2)), (309, (-1 / 6))]

def value3377 : Sparse (Fin 909) := [(0, (-1 / 180)), (1, (29 / 288)), (2, (1 / 8)), (3, (2 / 9)), (5, (-2 / 9)), (6, (7 / 288)), (7, (7 / 18)), (8, (4 / 9)), (13, (1 / 9)), (35, (2 / 9)), (52, (2 / 9)), (56, (-1 / 6)), (59, (-5 / 6)), (76, (1 / 2)), (201, (-1 / 2)), (506, (1 / 2))]

def value3378 : Sparse (Fin 909) := [(0, (-11 / 1440)), (1, (43 / 288)), (2, (2 / 9)), (3, (5 / 9)), (5, (-7 / 18)), (6, (1 / 24)), (7, (2 / 9)), (8, (7 / 18)), (12, (1 / 18)), (13, (2 / 9)), (35, (4 / 9)), (51, (-1 / 6)), (52, (13 / 18)), (71, (1 / 9)), (82, (1 / 18)), (86, (1 / 2)), (128, (1 / 18)), (201, (-1 / 6)), (262, (-1 / 6)), (309, (-1 / 6)), (327, (1 / 2)), (328, (1 / 2))]

def value3379 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (5 / 288)), (2, (23 / 144)), (3, (7 / 18)), (5, (-13 / 72)), (6, (1 / 72)), (7, (1 / 18)), (8, (1 / 3)), (12, (1 / 18)), (13, (2 / 9)), (35, (1 / 18)), (45, (1 / 2)), (51, (-1 / 3)), (52, (5 / 18)), (71, (1 / 9)), (102, (1 / 1)), (262, (-1 / 6)), (309, (-1 / 6)), (327, (1 / 2)), (739, (1 / 2)), (870, (1 / 2))]

def value3380 : Sparse (Fin 909) := [(0, (-1 / 160)), (1, (1 / 24)), (2, (23 / 144)), (3, (5 / 9)), (4, (1 / 9)), (5, (-2 / 9)), (6, (7 / 288)), (7, (1 / 18)), (8, (2 / 9)), (12, (1 / 18)), (13, (1 / 6)), (26, (1 / 18)), (35, (2 / 9)), (45, (1 / 2)), (51, (-1 / 3)), (52, (1 / 2)), (56, (-1 / 6)), (102, (1 / 1)), (103, (1 / 2)), (739, (1 / 2)), (870, (1 / 2))]

def value3381 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (31 / 288)), (2, (17 / 96)), (3, (7 / 18)), (5, (-23 / 72)), (6, (5 / 144)), (7, (2 / 9)), (8, (1 / 6)), (35, (7 / 18)), (42, (1 / 2)), (52, (2 / 3)), (86, (1 / 2)), (328, (1 / 1)), (506, (1 / 2)), (798, (1 / 2))]

def value3382 : Sparse (Fin 909) := [(0, (-7 / 1440)), (1, (-1 / 288)), (2, (-1 / 144)), (3, (1 / 3)), (5, (-1 / 8)), (6, (1 / 48)), (7, (5 / 18)), (8, (1 / 9)), (13, (2 / 9)), (26, (1 / 6)), (35, (1 / 3)), (52, (1 / 6)), (54, (-2 / 3)), (69, (1 / 18)), (70, (1 / 18)), (71, (1 / 18)), (103, (1 / 2)), (228, (-1 / 3)), (286, (1 / 2)), (309, (-1 / 6)), (739, (1 / 2))]

def value3383 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-1 / 48)), (2, (1 / 96)), (3, (1 / 2)), (5, (-7 / 72)), (6, (7 / 288)), (7, (2 / 9)), (8, (1 / 18)), (13, (2 / 9)), (26, (1 / 6)), (35, (1 / 6)), (51, (-1 / 6)), (52, (1 / 6)), (54, (-2 / 3)), (55, (-1 / 6)), (77, (1 / 2)), (228, (-1 / 2)), (737, (1 / 2)), (739, (1 / 2))]

def value3384 : Sparse (Fin 909) := [(0, (-13 / 1440)), (1, (13 / 288)), (2, (43 / 288)), (3, (8 / 9)), (5, (-13 / 72)), (6, (7 / 288)), (7, (1 / 6)), (8, (1 / 18)), (12, (2 / 9)), (13, (13 / 18)), (35, (7 / 18)), (51, (-1 / 3)), (52, (11 / 18)), (69, (1 / 18)), (70, (1 / 18)), (102, (1 / 2)), (262, (-1 / 6)), (309, (-1 / 6)), (327, (1 / 2))]

def value3385 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-1 / 48)), (2, (5 / 48)), (3, (5 / 6)), (4, (1 / 9)), (5, (-1 / 12)), (6, (1 / 144)), (7, (1 / 18)), (8, (1 / 18)), (12, (2 / 9)), (13, (2 / 3)), (26, (1 / 18)), (35, (5 / 18)), (51, (-1 / 3)), (52, (4 / 9)), (56, (-1 / 6)), (102, (1 / 2)), (103, (1 / 2))]

def value3386 : Sparse (Fin 909) := [(0, (-1 / 180)), (1, (7 / 288)), (2, (1 / 12)), (3, (4 / 9)), (4, (1 / 18)), (5, (-1 / 8)), (6, (5 / 288)), (12, (1 / 6)), (13, (1 / 2)), (26, (1 / 18)), (35, (2 / 9)), (43, (1 / 2)), (52, (4 / 9)), (102, (1 / 2)), (103, (1 / 1)), (546, (1 / 2)), (737, (1 / 2))]

def value3387 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 72)), (2, (5 / 48)), (3, (11 / 18)), (5, (-5 / 24)), (6, (1 / 32)), (7, (2 / 9)), (8, (1 / 6)), (12, (1 / 9)), (13, (1 / 2)), (35, (4 / 9)), (52, (5 / 9)), (59, (-1 / 6)), (60, (1 / 9)), (82, (1 / 18)), (128, (1 / 6)), (201, (-1 / 6))]

def value3388 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-7 / 144)), (2, (5 / 72)), (3, (5 / 18)), (5, (-1 / 9)), (6, (1 / 96)), (7, (1 / 9)), (8, (1 / 6)), (12, (1 / 9)), (13, (1 / 9)), (35, (1 / 18)), (51, (-1 / 6)), (52, (1 / 9))]

def value3389 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (5 / 144)), (2, (5 / 48)), (3, (4 / 9)), (5, (-19 / 72)), (6, (5 / 144)), (7, (5 / 18)), (8, (1 / 6)), (12, (1 / 18)), (13, (2 / 9)), (35, (1 / 2)), (52, (1 / 2)), (59, (-1 / 6)), (60, (1 / 9)), (128, (1 / 18))]

def value3390 : Sparse (Fin 909) := [(0, (1 / 60)), (1, (-7 / 72)), (2, (1 / 24)), (3, (2 / 3)), (4, (2 / 9)), (12, (5 / 18)), (13, (2 / 9))]

def value3391 : Sparse (Fin 909) := [(0, (13 / 1440)), (1, (-25 / 144)), (2, (11 / 288)), (3, (5 / 9)), (4, (1 / 6)), (12, (1 / 3)), (13, (1 / 6))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value3392 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (5 / 288)), (2, (-1 / 32)), (3, (1 / 3)), (4, (1 / 18)), (5, (-1 / 9)), (6, (1 / 72)), (7, (1 / 6)), (8, (1 / 9)), (26, (1 / 9)), (35, (1 / 18)), (51, (-1 / 6)), (52, (1 / 18))]

def value3393 : Sparse (Fin 909) := [(0, (41 / 1440)), (1, (-1 / 6)), (2, (1 / 32)), (3, (5 / 18)), (4, (1 / 3)), (12, (1 / 6))]

def value3394 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (1 / 16)), (2, (5 / 48)), (3, (1 / 9)), (5, (-5 / 18)), (6, (11 / 288)), (7, (1 / 18)), (8, (2 / 9)), (35, (1 / 9)), (52, (1 / 3))]

def value3395 : Sparse (Fin 909) := [(0, (1 / 180)), (1, (-17 / 144)), (2, (-5 / 288)), (3, (1 / 3)), (5, (-1 / 36)), (6, (1 / 288)), (12, (1 / 18)), (13, (5 / 18)), (35, (1 / 18)), (52, (1 / 9))]

def value3396 : Sparse (Fin 909) := [(0, (29 / 1440)), (1, (-3 / 16)), (2, (13 / 96)), (3, (2 / 3)), (4, (1 / 6)), (12, (1 / 6)), (13, (1 / 9)), (51, (-1 / 2)), (52, (1 / 6))]

def value3397 : Sparse (Fin 909) := [(0, (-53 / 720)), (1, (-13 / 72)), (2, (1 / 144)), (3, (1 / 9)), (4, (2 / 9)), (12, (1 / 18))]

def value3398 : Sparse (Fin 909) := [(0, (-1 / 40)), (1, (-7 / 72)), (2, (1 / 18)), (17, (1 / 2)), (28, (1 / 1)), (30, (-1 / 2))]

def value3399 : Sparse (Fin 909) := [(0, (-19 / 240)), (1, (-5 / 16)), (2, (1 / 12)), (27, (1 / 24)), (28, (1 / 2)), (30, (-1 / 3))]

def value3400 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-7 / 288)), (2, (17 / 288)), (3, (5 / 18)), (4, (1 / 9)), (5, (-5 / 72)), (6, (1 / 288)), (7, (1 / 18)), (8, (1 / 9)), (26, (1 / 9)), (35, (1 / 18)), (52, (1 / 9))]

def value3401 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 96)), (2, (35 / 288)), (3, (11 / 18)), (4, (1 / 9)), (5, (-2 / 9)), (6, (1 / 72)), (7, (11 / 18)), (8, (1 / 3)), (26, (2 / 9)), (35, (1 / 2)), (52, (1 / 9)), (67, (1 / 9)), (81, (-1 / 3))]

def value3402 : Sparse (Fin 909) := [(0, (19 / 1440)), (1, (-25 / 96)), (2, (1 / 24)), (3, (10 / 9)), (4, (4 / 9)), (12, (2 / 9)), (13, (5 / 18)), (26, (7 / 18)), (33, (-1 / 6)), (34, (1 / 9))]

def value3403 : Sparse (Fin 909) := [(0, (1 / 160)), (1, (-29 / 144)), (2, (5 / 96)), (3, (5 / 18)), (4, (2 / 9)), (26, (1 / 18)), (31, (-1 / 6))]

def value3404 : Sparse (Fin 909) := [(0, (-67 / 1440)), (1, (-17 / 72)), (2, (1 / 32)), (3, (1 / 18)), (4, (1 / 9)), (12, (1 / 18))]

def value3405 : Sparse (Fin 909) := [(0, (19 / 1440)), (1, (-11 / 288)), (2, (1 / 24)), (3, (7 / 18)), (4, (2 / 9)), (12, (1 / 6)), (13, (1 / 18))]

def value3406 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 18)), (2, (59 / 288)), (3, (1 / 6)), (5, (-25 / 72)), (6, (1 / 48)), (7, (1 / 2)), (8, (2 / 3)), (35, (1 / 9))]

def value3407 : Sparse (Fin 909) := [(0, (7 / 480)), (1, (-3 / 16)), (2, (7 / 288)), (3, (7 / 18)), (4, (1 / 9)), (26, (1 / 9))]

def value3408 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (1 / 24)), (2, (7 / 288)), (3, (5 / 18)), (5, (-1 / 8)), (6, (1 / 144)), (11, (1 / 18)), (13, (13 / 18)), (26, (1 / 9)), (35, (1 / 2)), (52, (1 / 2)), (56, (-1 / 6)), (60, (1 / 2)), (82, (1 / 18)), (128, (1 / 9)), (324, (1 / 2))]

def value3409 : Sparse (Fin 909) := [(0, (-1 / 180)), (1, (-19 / 288)), (2, (1 / 96)), (3, (1 / 1)), (4, (1 / 6)), (5, (-1 / 36)), (6, (1 / 144)), (12, (1 / 9)), (13, (2 / 9)), (26, (1 / 2)), (34, (1 / 6)), (35, (5 / 18)), (55, (-1 / 3)), (139, (1 / 2)), (204, (1 / 1)), (238, (-1 / 3)), (398, (1 / 1))]

def value3410 : Sparse (Fin 909) := [(0, (-1 / 180)), (1, (1 / 18)), (2, (1 / 16)), (5, (5 / 36)), (6, (5 / 144)), (7, (1 / 9)), (8, (-1 / 18)), (35, (1 / 9)), (52, (1 / 9)), (56, (-1 / 3)), (71, (1 / 9)), (74, (1 / 2)), (201, (-1 / 3)), (507, (1 / 1))]

def value3411 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (31 / 288)), (2, (1 / 8)), (3, (1 / 18)), (5, (-23 / 72)), (6, (5 / 144)), (8, (1 / 3)), (35, (1 / 18)), (39, (1 / 2)), (52, (1 / 3)), (71, (1 / 9)), (315, (1 / 1)), (507, (1 / 2)), (764, (1 / 2))]

def value3412 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (7 / 96)), (2, (35 / 288)), (3, (4 / 9)), (5, (-17 / 72)), (6, (5 / 144)), (7, (5 / 18)), (8, (1 / 9)), (12, (1 / 18)), (13, (7 / 18)), (35, (11 / 18)), (52, (5 / 9)), (59, (-1 / 6)), (60, (1 / 9)), (82, (2 / 9)), (128, (5 / 18)), (199, (-1 / 6)), (201, (-1 / 3))]

def value3413 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 96)), (2, (1 / 18)), (3, (5 / 9)), (5, (-7 / 72)), (6, (1 / 48)), (7, (1 / 18)), (12, (5 / 18)), (13, (5 / 6)), (35, (5 / 18)), (52, (2 / 9)), (54, (-1 / 6)), (82, (2 / 9)), (128, (2 / 9)), (199, (-1 / 6)), (201, (-1 / 3))]

def value3414 : Sparse (Fin 909) := [(1, (-5 / 288)), (2, (29 / 288)), (3, (5 / 6)), (4, (2 / 9)), (5, (-5 / 18)), (6, (7 / 144)), (7, (1 / 9)), (8, (1 / 9)), (12, (1 / 6)), (13, (11 / 18)), (26, (2 / 9)), (35, (1 / 2)), (52, (4 / 9)), (54, (-1 / 6)), (56, (-1 / 3)), (82, (2 / 9)), (128, (2 / 9)), (199, (-1 / 6)), (201, (-1 / 3))]

def value3415 : Sparse (Fin 909) := [(1, (-17 / 144)), (2, (1 / 48)), (3, (10 / 9)), (4, (4 / 9)), (12, (1 / 9)), (13, (1 / 3)), (26, (11 / 18)), (33, (-1 / 6)), (34, (1 / 9)), (35, (1 / 6)), (54, (-1 / 6)), (56, (-1 / 3))]

def value3416 : Sparse (Fin 909) := [(0, (11 / 1440)), (1, (-37 / 288)), (2, (1 / 144)), (3, (1 / 2)), (4, (1 / 9)), (12, (5 / 18)), (13, (5 / 18)), (26, (1 / 9)), (34, (1 / 9))]

def value3417 : Sparse (Fin 909) := [(0, (1 / 90)), (1, (-65 / 288)), (2, (-5 / 288)), (3, (5 / 6)), (4, (4 / 9)), (12, (1 / 3)), (13, (5 / 18)), (25, (-1 / 6)), (26, (2 / 9)), (35, (1 / 6)), (54, (-1 / 6)), (56, (-1 / 3))]

def value3418 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-1 / 16)), (2, (7 / 144)), (3, (1 / 2)), (4, (1 / 9)), (5, (-5 / 36)), (6, (1 / 72)), (8, (1 / 9)), (12, (1 / 18)), (25, (-1 / 6)), (26, (1 / 9)), (35, (1 / 9)), (51, (-1 / 3)), (52, (1 / 3)), (54, (-1 / 6)), (89, (1 / 2)), (123, (-1 / 3)), (226, (-1 / 6))]

def value3419 : Sparse (Fin 909) := [(0, (11 / 1440)), (1, (-41 / 288)), (2, (1 / 48)), (3, (1 / 2)), (4, (1 / 9)), (12, (1 / 18)), (13, (1 / 9)), (26, (1 / 9)), (33, (-1 / 6))]

def value3420 : Sparse (Fin 909) := [(1, (-1 / 288)), (2, (5 / 288)), (3, (1 / 6)), (5, (-11 / 72)), (6, (1 / 48)), (7, (1 / 6)), (8, (1 / 9)), (11, (1 / 18)), (26, (1 / 18)), (35, (5 / 18)), (52, (2 / 9)), (228, (-1 / 6))]

def value3421 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (5 / 288)), (2, (5 / 144)), (3, (5 / 18)), (5, (-5 / 36)), (6, (1 / 72)), (7, (1 / 3)), (8, (2 / 9)), (9, (-1 / 36)), (35, (2 / 9)), (69, (5 / 18)), (70, (1 / 6)), (71, (1 / 9))]

def value3422 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-1 / 288)), (2, (5 / 144)), (3, (1 / 3)), (4, (1 / 9)), (5, (-1 / 24)), (6, (1 / 288)), (7, (1 / 6)), (12, (1 / 6)), (13, (1 / 9)), (26, (1 / 9)), (35, (1 / 6)), (52, (1 / 9))]

def value3423 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 16)), (2, (13 / 144)), (3, (1 / 2)), (4, (1 / 9)), (5, (-1 / 12)), (6, (1 / 144)), (7, (2 / 9)), (8, (1 / 18)), (12, (1 / 9)), (13, (1 / 9)), (26, (1 / 9)), (35, (1 / 6)), (51, (-1 / 6)), (52, (1 / 6))]

def value3424 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 36)), (2, (1 / 36)), (3, (1 / 9)), (5, (-1 / 12)), (6, (1 / 144)), (7, (1 / 9)), (8, (1 / 9)), (12, (1 / 18)), (13, (2 / 9)), (35, (1 / 6)), (52, (1 / 9)), (59, (-1 / 6)), (60, (1 / 9)), (128, (1 / 18))]

def value3425 : Sparse (Fin 909) := [(0, (7 / 720)), (1, (-11 / 96)), (2, (1 / 32)), (3, (7 / 9)), (4, (1 / 9)), (12, (1 / 3)), (13, (7 / 18))]

def value3426 : Sparse (Fin 909) := [(0, (1 / 72)), (1, (-13 / 48)), (2, (7 / 144)), (3, (8 / 9)), (4, (2 / 9)), (12, (5 / 9)), (13, (1 / 3))]

def value3427 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (-5 / 288)), (2, (1 / 144)), (3, (5 / 18)), (12, (2 / 9)), (13, (11 / 18)), (32, (1 / 9))]

def value3428 : Sparse (Fin 909) := [(1, (13 / 288)), (2, (1 / 48)), (3, (1 / 9)), (4, (1 / 9)), (5, (-1 / 18)), (6, (1 / 288)), (8, (1 / 9)), (26, (2 / 9)), (35, (1 / 6)), (52, (1 / 9)), (67, (1 / 9)), (81, (-1 / 3))]

def value3429 : Sparse (Fin 909) := [(0, (37 / 1440)), (1, (-7 / 32)), (2, (5 / 144)), (3, (5 / 9)), (4, (7 / 18)), (12, (1 / 18)), (26, (1 / 6)), (31, (-1 / 6))]

def value3430 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-5 / 96)), (2, (7 / 288)), (3, (7 / 18)), (4, (1 / 9)), (12, (1 / 18)), (13, (1 / 18)), (26, (1 / 6)), (33, (-1 / 6)), (34, (1 / 9))]

def value3431 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-5 / 288)), (2, (5 / 288)), (3, (5 / 9)), (4, (2 / 9)), (5, (-1 / 72)), (7, (1 / 6)), (12, (1 / 6)), (13, (1 / 6)), (26, (1 / 3)), (34, (1 / 9)), (35, (1 / 9))]

def value3432 : Sparse (Fin 909) := [(0, (7 / 360)), (1, (-13 / 72)), (2, (1 / 36)), (3, (2 / 3)), (4, (1 / 3)), (12, (1 / 9)), (26, (2 / 9))]

def value3433 : Sparse (Fin 909) := [(0, (23 / 1440)), (1, (-19 / 72)), (2, (11 / 288)), (3, (1 / 6)), (4, (1 / 3)), (12, (1 / 18))]

def value3434 : Sparse (Fin 909) := [(0, (-7 / 480)), (1, (-5 / 144)), (2, (1 / 32)), (3, (1 / 18))]

def value3435 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (1 / 288)), (2, (1 / 32)), (3, (1 / 3)), (4, (1 / 9)), (13, (1 / 6)), (26, (1 / 9)), (33, (-1 / 3)), (34, (1 / 9))]

def value3436 : Sparse (Fin 909) := [(0, (13 / 720)), (1, (-11 / 72)), (2, (7 / 144)), (3, (1 / 3)), (4, (2 / 9)), (12, (2 / 9))]

def value3437 : Sparse (Fin 909) := [(0, (-11 / 480)), (1, (1 / 12)), (2, (7 / 288)), (3, (1 / 6)), (4, (1 / 9))]

def value3438 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (-1 / 32)), (2, (11 / 288)), (3, (4 / 9)), (4, (1 / 9)), (5, (-1 / 24)), (6, (1 / 288)), (7, (1 / 9)), (12, (1 / 9)), (13, (5 / 18)), (26, (2 / 9)), (34, (1 / 9)), (35, (1 / 9)), (52, (1 / 9))]

def value3439 : Sparse (Fin 909) := [(1, (-1 / 72)), (2, (5 / 96)), (3, (1 / 6)), (5, (-7 / 72)), (6, (1 / 96)), (7, (2 / 9)), (8, (1 / 9)), (35, (1 / 9))]

def value3440 : Sparse (Fin 909) := [(0, (1 / 120)), (1, (-5 / 48)), (2, (1 / 48)), (3, (2 / 9)), (12, (1 / 6)), (13, (1 / 9))]

def value3441 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 16)), (2, (-1 / 32)), (3, (1 / 6)), (4, (1 / 9)), (26, (1 / 9))]

def value3442 : Sparse (Fin 909) := [(0, (-1 / 120)), (1, (-5 / 144)), (2, (1 / 144)), (3, (1 / 9)), (4, (1 / 9)), (12, (1 / 18))]

def value3443 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-13 / 288)), (2, (-1 / 144)), (3, (2 / 9)), (5, (-1 / 36)), (6, (1 / 288)), (7, (1 / 18)), (12, (1 / 9)), (13, (1 / 6)), (35, (1 / 6)), (52, (1 / 9)), (54, (-1 / 6))]

def value3444 : Sparse (Fin 909) := [(0, (11 / 1440)), (1, (-5 / 48)), (2, (17 / 288)), (3, (1 / 2)), (4, (1 / 9)), (5, (-1 / 72)), (7, (1 / 9)), (8, (1 / 18)), (12, (5 / 18)), (23, (-1 / 6)), (24, (-1 / 6))]

def value3445 : Sparse (Fin 909) := [(0, (1 / 120)), (1, (-1 / 9)), (2, (1 / 36)), (3, (1 / 3)), (4, (1 / 9)), (5, (-1 / 72)), (7, (1 / 9)), (8, (1 / 18)), (12, (1 / 9)), (23, (-1 / 6)), (24, (-1 / 6))]

def value3446 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (-23 / 144)), (2, (1 / 32)), (3, (1 / 6)), (4, (2 / 9)), (12, (1 / 9))]

def value3447 : Sparse (Fin 909) := [(0, (1 / 144)), (1, (-13 / 144)), (2, (1 / 72)), (3, (1 / 3)), (4, (1 / 9)), (5, (-1 / 72)), (7, (1 / 6)), (26, (1 / 9)), (35, (1 / 9))]

def value3448 : Sparse (Fin 909) := [(0, (7 / 720)), (1, (-19 / 96)), (2, (1 / 288)), (3, (7 / 9)), (4, (1 / 3)), (12, (1 / 6)), (13, (1 / 9)), (26, (1 / 3)), (35, (1 / 6)), (55, (-1 / 2))]

def value3449 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 72)), (2, (19 / 288)), (3, (1 / 2)), (4, (1 / 6)), (5, (-5 / 24)), (6, (5 / 144)), (7, (1 / 6)), (8, (1 / 9)), (11, (1 / 6)), (26, (1 / 3)), (35, (4 / 9)), (52, (5 / 18)), (228, (-1 / 2))]

def value3450 : Sparse (Fin 909) := [(0, (11 / 360)), (1, (-1 / 36)), (2, (1 / 72))]

def value3451 : Sparse (Fin 909) := [(0, (1 / 120)), (1, (-3 / 16)), (2, (-1 / 16)), (3, (11 / 18)), (4, (2 / 9)), (12, (1 / 9)), (13, (1 / 3)), (26, (2 / 9)), (35, (1 / 6)), (54, (-1 / 6)), (56, (-1 / 3))]

def value3452 : Sparse (Fin 909) := [(0, (7 / 720)), (1, (-7 / 72)), (2, (11 / 288)), (3, (5 / 18)), (4, (1 / 9)), (5, (-1 / 24)), (6, (1 / 288)), (7, (1 / 9)), (26, (1 / 9)), (35, (1 / 9)), (52, (1 / 9))]

def value3453 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (-5 / 72)), (2, (5 / 72)), (3, (2 / 9)), (5, (-1 / 24)), (7, (1 / 18)), (8, (1 / 9))]

def value3454 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 144)), (2, (1 / 144)), (3, (7 / 18)), (5, (-7 / 72)), (6, (1 / 72)), (7, (1 / 3)), (8, (1 / 9)), (9, (-1 / 72)), (26, (1 / 9)), (35, (1 / 2)), (52, (1 / 9)), (67, (1 / 9)), (69, (1 / 6)), (70, (1 / 9))]

def value3455 : Sparse (Fin 909) := [(0, (17 / 1440)), (1, (-19 / 144)), (2, (23 / 288)), (3, (7 / 18)), (4, (1 / 9)), (5, (-1 / 24)), (7, (1 / 18)), (8, (1 / 9)), (26, (1 / 9))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value3456 : Sparse (Fin 909) := [(1, (1 / 288)), (2, (13 / 288)), (3, (1 / 9)), (5, (-1 / 9)), (6, (1 / 72)), (7, (2 / 9)), (9, (-1 / 72)), (35, (1 / 9)), (52, (1 / 9)), (69, (1 / 6)), (70, (1 / 9))]

def value3457 : Sparse (Fin 909) := [(0, (-1 / 180)), (1, (1 / 72)), (5, (-1 / 24)), (7, (1 / 18)), (8, (1 / 9))]

def value3458 : Sparse (Fin 909) := [(0, (1 / 96)), (1, (-1 / 18)), (2, (19 / 288)), (3, (5 / 18)), (4, (1 / 9)), (5, (-1 / 24)), (7, (1 / 18)), (8, (1 / 9)), (12, (1 / 9))]

def value3459 : Sparse (Fin 909) := [(1, (5 / 96)), (2, (11 / 144)), (3, (1 / 6)), (5, (-5 / 36)), (6, (1 / 96)), (7, (1 / 6)), (8, (1 / 3)), (9, (-1 / 72)), (35, (1 / 9)), (69, (1 / 6)), (70, (1 / 9))]

def value3460 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-7 / 288)), (2, (1 / 8)), (3, (4 / 9)), (4, (1 / 9)), (5, (-5 / 24)), (6, (5 / 288)), (7, (5 / 18)), (8, (1 / 3)), (9, (-1 / 72)), (26, (1 / 9)), (35, (1 / 6)), (52, (1 / 9)), (69, (1 / 9)), (70, (1 / 18)), (71, (1 / 9))]

def value3461 : Sparse (Fin 909) := [(0, (1 / 90)), (1, (-17 / 144)), (2, (-1 / 72)), (5, (-1 / 12)), (6, (1 / 48)), (25, (-1 / 3)), (31, (-2 / 3)), (87, (1 / 2)), (123, (-2 / 3)), (226, (-1 / 6)), (237, (-1 / 2)), (239, (1 / 1))]

def value3462 : Sparse (Fin 909) := [(0, (-1 / 96)), (1, (13 / 288)), (2, (1 / 96)), (5, (-1 / 36)), (6, (1 / 288)), (27, (1 / 8)), (28, (1 / 1)), (30, (-2 / 3)), (31, (-1 / 6)), (203, (1 / 2)), (236, (-1 / 6)), (253, (2 / 1))]

def value3463 : Sparse (Fin 909) := [(0, (1 / 80)), (1, (7 / 144)), (2, (1 / 48)), (5, (-1 / 18)), (6, (1 / 144)), (17, (1 / 2)), (23, (-1 / 6)), (25, (-1 / 6)), (27, (1 / 8)), (30, (-1 / 6)), (203, (1 / 1)), (216, (1 / 2)), (236, (-1 / 6)), (253, (1 / 1))]

def value3464 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (1 / 24)), (2, (1 / 12)), (3, (1 / 3)), (4, (1 / 18)), (5, (-1 / 4)), (6, (11 / 288)), (7, (1 / 18)), (8, (1 / 9)), (11, (1 / 18)), (26, (1 / 9)), (35, (1 / 3)), (52, (1 / 2)), (228, (-1 / 6))]

def value3465 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-5 / 72)), (2, (5 / 288)), (3, (17 / 18)), (4, (2 / 9)), (5, (-1 / 36)), (6, (1 / 288)), (7, (1 / 18)), (12, (1 / 3)), (13, (7 / 9)), (26, (2 / 9)), (35, (1 / 3)), (52, (1 / 9)), (54, (-1 / 3)), (56, (-1 / 3))]

def value3466 : Sparse (Fin 909) := [(0, (1 / 120)), (1, (-13 / 144)), (2, (53 / 288)), (3, (1 / 2)), (5, (-13 / 72)), (6, (1 / 96)), (7, (1 / 3)), (8, (1 / 3)), (12, (1 / 6)), (13, (1 / 9)), (35, (1 / 9))]

def value3467 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-59 / 288)), (2, (11 / 288)), (3, (4 / 3)), (4, (2 / 3)), (5, (-1 / 72)), (7, (1 / 6)), (12, (1 / 6)), (13, (1 / 9)), (26, (2 / 3)), (35, (5 / 18)), (55, (-1 / 2))]

def value3468 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 96)), (2, (7 / 72)), (3, (5 / 6)), (4, (1 / 6)), (5, (-13 / 72)), (6, (1 / 48)), (7, (1 / 2)), (9, (-1 / 72)), (11, (1 / 6)), (26, (1 / 3)), (35, (7 / 9)), (52, (1 / 2)), (69, (1 / 6)), (70, (1 / 9)), (228, (-1 / 2))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value384 : Sparse (Fin 909) := [(1, (-1 / 96)), (2, (1 / 32)), (5, (-1 / 8)), (7, (1 / 2)), (9, (-1 / 24)), (69, (1 / 2)), (70, (1 / 3))]

def value385 : Sparse (Fin 909) := [(3, (1 / 6)), (7, (1 / 3)), (35, (1 / 3)), (69, (1 / 6)), (70, (1 / 3)), (277, (-1 / 2)), (278, (1 / 6))]

def value386 : Sparse (Fin 909) := [(1, (1 / 24)), (2, (1 / 12)), (5, (-5 / 24)), (6, (5 / 96)), (9, (-1 / 6)), (58, (1 / 96)), (69, (1 / 6)), (71, (1 / 3))]

def value387 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (5 / 96)), (2, (5 / 96)), (5, (-1 / 8)), (6, (1 / 96)), (8, (1 / 3)), (9, (-1 / 24)), (69, (1 / 6)), (71, (2 / 3))]

def value388 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 32)), (5, (-1 / 8)), (6, (1 / 96)), (7, (1 / 6)), (8, (1 / 6)), (9, (-1 / 12)), (69, (1 / 3)), (70, (1 / 6)), (71, (1 / 2))]

def value389 : Sparse (Fin 909) := [(2, (1 / 48)), (5, (-1 / 8)), (6, (1 / 48)), (7, (1 / 6)), (9, (-1 / 24)), (69, (1 / 3)), (70, (1 / 6)), (71, (1 / 3))]

def value390 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (-1 / 48)), (5, (-1 / 24)), (6, (1 / 48)), (9, (-1 / 8)), (35, (1 / 6)), (58, (1 / 96)), (70, (1 / 3)), (71, (1 / 6)), (278, (1 / 6))]

def value391 : Sparse (Fin 909) := [(279, (1 / 1))]

def value392 : Sparse (Fin 909) := [(280, (1 / 1))]

def value393 : Sparse (Fin 909) := [(281, (1 / 1))]

def value394 : Sparse (Fin 909) := [(282, (1 / 1))]

def value395 : Sparse (Fin 909) := [(72, (1 / 1))]

def value396 : Sparse (Fin 909) := [(73, (1 / 1))]

def value397 : Sparse (Fin 909) := [(74, (1 / 1))]

def value398 : Sparse (Fin 909) := [(75, (1 / 1))]

def value399 : Sparse (Fin 909) := [(284, (1 / 1))]

def value400 : Sparse (Fin 909) := [(286, (1 / 1))]

def value401 : Sparse (Fin 909) := [(287, (1 / 1))]

def value402 : Sparse (Fin 909) := [(288, (1 / 1))]

def value403 : Sparse (Fin 909) := [(289, (1 / 1))]

def value404 : Sparse (Fin 909) := [(76, (1 / 1))]

def value405 : Sparse (Fin 909) := [(290, (1 / 1))]

def value406 : Sparse (Fin 909) := [(291, (1 / 1))]

def value407 : Sparse (Fin 909) := [(293, (1 / 1))]

def value408 : Sparse (Fin 909) := [(77, (1 / 1))]

def value409 : Sparse (Fin 909) := [(78, (1 / 1))]

def value410 : Sparse (Fin 909) := [(299, (1 / 1))]

def value411 : Sparse (Fin 909) := [(300, (1 / 1))]

def value412 : Sparse (Fin 909) := [(79, (1 / 1))]

def value413 : Sparse (Fin 909) := [(80, (1 / 1))]

def value414 : Sparse (Fin 909) := [(1, (1 / 24)), (2, (1 / 12)), (6, (1 / 24)), (9, (-1 / 6))]

def value415 : Sparse (Fin 909) := [(1, (1 / 24)), (2, (5 / 96)), (3, (1 / 6)), (5, (-1 / 8)), (6, (1 / 96)), (7, (1 / 6)), (35, (1 / 3)), (52, (1 / 3)), (69, (1 / 6)), (495, (1 / 6))]

def value416 : Sparse (Fin 909) := [(1, (1 / 32)), (2, (1 / 32)), (5, (-1 / 8)), (7, (1 / 3)), (8, (1 / 6)), (35, (1 / 6)), (52, (1 / 6)), (69, (1 / 3)), (70, (1 / 6)), (71, (1 / 6))]

def value417 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (1 / 96)), (3, (1 / 6)), (5, (-1 / 24)), (7, (1 / 3)), (8, (1 / 6)), (35, (1 / 6)), (81, (-1 / 2)), (256, (-1 / 2))]

def value418 : Sparse (Fin 909) := [(1, (5 / 96)), (2, (1 / 16)), (5, (-1 / 6)), (6, (1 / 96)), (7, (1 / 6)), (8, (1 / 3)), (69, (1 / 6)), (71, (1 / 2))]

def value419 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (1 / 16)), (2, (5 / 96)), (3, (1 / 6)), (5, (-1 / 12)), (7, (1 / 6)), (8, (1 / 6)), (35, (1 / 6)), (52, (1 / 6)), (81, (-1 / 2))]

def value420 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 48)), (5, (-1 / 12)), (8, (1 / 6)), (35, (1 / 3)), (67, (1 / 6))]

def value421 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (1 / 48)), (3, (1 / 3)), (5, (-1 / 24)), (7, (1 / 3)), (26, (1 / 6)), (35, (1 / 2)), (52, (1 / 6)), (67, (1 / 6))]

def value422 : Sparse (Fin 909) := [(3, (1 / 3)), (4, (1 / 6)), (7, (1 / 6)), (26, (1 / 3)), (35, (1 / 3)), (67, (1 / 6)), (81, (-1 / 2))]

def value423 : Sparse (Fin 909) := [(3, (1 / 6)), (7, (1 / 6)), (35, (1 / 6)), (81, (-1 / 2)), (228, (-1 / 2)), (273, (-1 / 2))]

def value424 : Sparse (Fin 909) := [(10, (-1 / 2)), (55, (-1 / 2)), (273, (-1 / 2)), (306, (-1 / 2))]

def value425 : Sparse (Fin 909) := [(1, (5 / 96)), (2, (1 / 12)), (5, (-1 / 6)), (6, (1 / 32)), (35, (1 / 6)), (52, (1 / 3)), (306, (-1 / 2))]

def value426 : Sparse (Fin 909) := [(3, (1 / 6)), (7, (1 / 6)), (11, (1 / 6)), (26, (1 / 3)), (34, (1 / 6)), (35, (1 / 2)), (67, (1 / 3)), (276, (1 / 6))]

def value427 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 32)), (5, (-1 / 8)), (6, (1 / 96)), (7, (1 / 3)), (8, (1 / 6)), (35, (1 / 3)), (67, (1 / 6)), (307, (-1 / 2))]

def value428 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (-1 / 24)), (5, (-1 / 24)), (6, (-1 / 96)), (11, (1 / 3)), (35, (1 / 2)), (82, (1 / 6)), (276, (1 / 3))]

def value429 : Sparse (Fin 909) := [(1, (-7 / 96)), (2, (-1 / 32)), (5, (1 / 8)), (7, (1 / 6)), (9, (-1 / 24)), (69, (1 / 6))]

def value430 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (1 / 48)), (3, (1 / 6)), (5, (-1 / 24)), (35, (1 / 6)), (69, (1 / 6)), (70, (1 / 6))]

def value431 : Sparse (Fin 909) := [(1, (1 / 32)), (2, (1 / 24)), (5, (-1 / 24)), (6, (1 / 48)), (9, (-1 / 12)), (52, (1 / 6)), (58, (1 / 96)), (310, (1 / 6))]

def value432 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (1 / 24)), (2, (5 / 96)), (5, (-1 / 24)), (6, (1 / 48)), (8, (1 / 6)), (9, (-1 / 24)), (71, (1 / 6))]

def value433 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (1 / 16)), (2, (1 / 24)), (5, (-1 / 12)), (71, (1 / 3))]

def value434 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (1 / 32)), (2, (1 / 16)), (5, (-1 / 6)), (7, (1 / 3)), (8, (1 / 3)), (69, (1 / 6)), (71, (1 / 6))]

def value435 : Sparse (Fin 909) := [(2, (-1 / 24)), (5, (-1 / 8)), (6, (1 / 24)), (7, (1 / 6)), (9, (-1 / 24)), (35, (1 / 3)), (70, (1 / 6))]

def value436 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (1 / 48)), (5, (-1 / 8)), (6, (-1 / 48)), (9, (-1 / 24)), (35, (1 / 6)), (58, (1 / 96)), (82, (1 / 3)), (278, (1 / 6)), (310, (1 / 6))]

def value437 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 12)), (2, (1 / 32)), (3, (1 / 2)), (5, (-1 / 24)), (7, (1 / 2)), (35, (1 / 3))]

def value438 : Sparse (Fin 909) := [(3, (1 / 3)), (7, (1 / 6)), (10, (-1 / 2)), (12, (1 / 6)), (13, (1 / 3)), (35, (1 / 3)), (82, (1 / 6))]

def value439 : Sparse (Fin 909) := [(1, (5 / 96)), (2, (7 / 96)), (3, (1 / 6)), (5, (-1 / 8)), (6, (1 / 48)), (52, (1 / 3)), (308, (-1 / 2)), (310, (1 / 6))]

def value440 : Sparse (Fin 909) := [(0, (-1 / 160)), (1, (1 / 12)), (2, (5 / 48)), (5, (-1 / 6)), (6, (1 / 96)), (7, (1 / 6)), (8, (1 / 3))]

def value441 : Sparse (Fin 909) := [(1, (1 / 24)), (2, (1 / 12)), (5, (-1 / 8)), (7, (1 / 6)), (8, (1 / 3))]

def value442 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (1 / 96)), (5, (-1 / 24)), (7, (1 / 6)), (8, (1 / 6)), (51, (-1 / 2)), (308, (-1 / 2)), (309, (-1 / 2))]

def value443 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 96)), (2, (1 / 32)), (3, (1 / 6)), (5, (-1 / 8)), (6, (1 / 96)), (7, (1 / 3)), (8, (1 / 6)), (35, (1 / 6))]

def value444 : Sparse (Fin 909) := [(1, (1 / 32)), (2, (1 / 96)), (5, (-1 / 12)), (6, (1 / 48)), (13, (1 / 6)), (35, (1 / 6)), (52, (1 / 6)), (82, (1 / 6)), (309, (-1 / 2)), (310, (1 / 6))]

def value445 : Sparse (Fin 909) := [(1, (5 / 96)), (2, (-1 / 32)), (5, (-1 / 8)), (13, (1 / 6)), (35, (1 / 3)), (82, (1 / 6))]

def value446 : Sparse (Fin 909) := [(1, (1 / 24)), (2, (1 / 24)), (7, (1 / 3)), (8, (1 / 3)), (10, (-1 / 2))]

def value447 : Sparse (Fin 909) := [(311, (1 / 1))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value448 : Sparse (Fin 909) := [(312, (1 / 1))]

def value449 : Sparse (Fin 909) := [(83, (1 / 1))]

def value450 : Sparse (Fin 909) := [(84, (1 / 1))]

def value451 : Sparse (Fin 909) := [(313, (1 / 1))]

def value452 : Sparse (Fin 909) := [(314, (1 / 1))]

def value453 : Sparse (Fin 909) := [(315, (1 / 1))]

def value454 : Sparse (Fin 909) := [(85, (1 / 1))]

def value455 : Sparse (Fin 909) := [(316, (1 / 1))]

def value456 : Sparse (Fin 909) := [(317, (1 / 1))]

def value457 : Sparse (Fin 909) := [(318, (1 / 1))]

def value458 : Sparse (Fin 909) := [(319, (1 / 1))]

def value459 : Sparse (Fin 909) := [(321, (1 / 1))]

def value460 : Sparse (Fin 909) := [(322, (1 / 1))]

def value461 : Sparse (Fin 909) := [(323, (1 / 1))]

def value462 : Sparse (Fin 909) := [(324, (1 / 1))]

def value463 : Sparse (Fin 909) := [(325, (1 / 1))]

def value464 : Sparse (Fin 909) := [(86, (1 / 1))]

def value465 : Sparse (Fin 909) := [(326, (1 / 1))]

def value466 : Sparse (Fin 909) := [(327, (1 / 1))]

def value467 : Sparse (Fin 909) := [(328, (1 / 1))]

def value468 : Sparse (Fin 909) := [(329, (1 / 1))]

def value469 : Sparse (Fin 909) := [(330, (1 / 1))]

def value470 : Sparse (Fin 909) := [(352, (1 / 1))]

def value471 : Sparse (Fin 909) := [(87, (1 / 1))]

def value472 : Sparse (Fin 909) := [(36, (1 / 1))]

def value473 : Sparse (Fin 909) := [(37, (1 / 1))]

def value474 : Sparse (Fin 909) := [(38, (1 / 1))]

def value475 : Sparse (Fin 909) := [(89, (1 / 1))]

def value476 : Sparse (Fin 909) := [(39, (1 / 1))]

def value477 : Sparse (Fin 909) := [(40, (1 / 1))]

def value478 : Sparse (Fin 909) := [(378, (1 / 1))]

def value479 : Sparse (Fin 909) := [(379, (1 / 1))]

def value480 : Sparse (Fin 909) := [(383, (1 / 1))]

def value481 : Sparse (Fin 909) := [(41, (1 / 1))]

def value482 : Sparse (Fin 909) := [(94, (1 / 1))]

def value483 : Sparse (Fin 909) := [(95, (1 / 1))]

def value484 : Sparse (Fin 909) := [(97, (1 / 1))]

def value485 : Sparse (Fin 909) := [(98, (1 / 1))]

def value486 : Sparse (Fin 909) := [(392, (1 / 1))]

def value487 : Sparse (Fin 909) := [(99, (1 / 1))]

def value488 : Sparse (Fin 909) := [(100, (1 / 1))]

def value489 : Sparse (Fin 909) := [(101, (1 / 1))]

def value490 : Sparse (Fin 909) := [(42, (1 / 1))]

def value491 : Sparse (Fin 909) := [(102, (1 / 1))]

def value492 : Sparse (Fin 909) := [(398, (1 / 1))]

def value493 : Sparse (Fin 909) := [(399, (1 / 1))]

def value494 : Sparse (Fin 909) := [(400, (1 / 1))]

def value495 : Sparse (Fin 909) := [(103, (1 / 1))]

def value496 : Sparse (Fin 909) := [(104, (1 / 1))]

def value497 : Sparse (Fin 909) := [(105, (1 / 1))]

def value498 : Sparse (Fin 909) := [(425, (1 / 1))]

def value499 : Sparse (Fin 909) := [(426, (1 / 1))]

def value500 : Sparse (Fin 909) := [(106, (1 / 1))]

def value501 : Sparse (Fin 909) := [(428, (1 / 1))]

def value502 : Sparse (Fin 909) := [(107, (1 / 1))]

def value503 : Sparse (Fin 909) := [(108, (1 / 1))]

def value504 : Sparse (Fin 909) := [(110, (1 / 1))]

def value505 : Sparse (Fin 909) := [(112, (1 / 1))]

def value506 : Sparse (Fin 909) := [(113, (1 / 1))]

def value507 : Sparse (Fin 909) := [(114, (1 / 1))]

def value508 : Sparse (Fin 909) := [(115, (1 / 1))]

def value509 : Sparse (Fin 909) := [(453, (1 / 1))]

def value510 : Sparse (Fin 909) := [(43, (1 / 1))]

def value511 : Sparse (Fin 909) := [(116, (1 / 1))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value512 : Sparse (Fin 909) := [(460, (1 / 1))]

def value513 : Sparse (Fin 909) := [(44, (1 / 1))]

def value514 : Sparse (Fin 909) := [(45, (1 / 1))]

def value515 : Sparse (Fin 909) := [(119, (1 / 1))]

def value516 : Sparse (Fin 909) := [(120, (1 / 1))]

def value517 : Sparse (Fin 909) := [(46, (1 / 1))]

def value518 : Sparse (Fin 909) := [(122, (1 / 1))]

def value519 : Sparse (Fin 909) := [(472, (1 / 1))]

def value520 : Sparse (Fin 909) := [(47, (1 / 1))]

def value521 : Sparse (Fin 909) := [(48, (1 / 1))]

def value522 : Sparse (Fin 909) := [(49, (1 / 1))]

def value523 : Sparse (Fin 909) := [(50, (1 / 1))]

def value524 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 48)), (3, (1 / 6)), (51, (-1 / 2)), (52, (1 / 6)), (126, (-1 / 2)), (262, (-1 / 2))]

def value525 : Sparse (Fin 909) := [(124, (-1 / 2)), (126, (-1 / 2)), (197, (-1 / 2)), (236, (-1 / 2))]

def value526 : Sparse (Fin 909) := [(486, (1 / 1))]

def value527 : Sparse (Fin 909) := [(1, (1 / 24)), (2, (1 / 24)), (3, (1 / 3)), (12, (1 / 6)), (13, (2 / 3)), (52, (1 / 3)), (128, (1 / 6))]

def value528 : Sparse (Fin 909) := [(51, (-1 / 2)), (123, (-1 / 2)), (124, (-1 / 2)), (259, (-1 / 2))]

def value529 : Sparse (Fin 909) := [(3, (1 / 6)), (12, (1 / 6)), (13, (1 / 6)), (33, (-1 / 2)), (51, (-1 / 2)), (59, (-1 / 2))]

def value530 : Sparse (Fin 909) := [(125, (-1 / 1)), (126, (-1 / 1))]

def value531 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (3 / 32)), (2, (1 / 12)), (3, (1 / 3)), (5, (-1 / 24)), (13, (1 / 3)), (35, (1 / 6)), (52, (1 / 3))]

def value532 : Sparse (Fin 909) := [(1, (-1 / 32)), (2, (-1 / 32)), (3, (1 / 6)), (5, (-1 / 24)), (26, (1 / 6)), (35, (1 / 6)), (52, (1 / 6)), (123, (-1 / 2))]

def value533 : Sparse (Fin 909) := [(1, (-1 / 32)), (2, (1 / 96)), (3, (1 / 6)), (7, (1 / 6)), (51, (-1 / 2)), (54, (-1 / 2)), (64, (-1 / 2))]

def value534 : Sparse (Fin 909) := [(487, (1 / 1))]

def value535 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (1 / 24)), (2, (1 / 32)), (3, (1 / 3)), (4, (1 / 6)), (26, (1 / 6)), (33, (-1 / 2)), (81, (-1 / 2))]

def value536 : Sparse (Fin 909) := [(1, (-1 / 32)), (2, (1 / 96)), (3, (1 / 6)), (25, (-1 / 2)), (26, (1 / 6)), (64, (-1 / 2)), (123, (-1 / 2))]

def value537 : Sparse (Fin 909) := [(33, (-1 / 1)), (489, (-1 / 1))]

def value538 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 48)), (3, (1 / 6)), (52, (1 / 6)), (123, (-1 / 2)), (237, (-1 / 2)), (489, (-1 / 2))]

def value539 : Sparse (Fin 909) := [(31, (-1 / 2)), (33, (-1 / 2)), (51, (-1 / 2)), (123, (-1 / 2))]

def value540 : Sparse (Fin 909) := [(1, (1 / 32)), (2, (1 / 24)), (5, (-1 / 12)), (6, (1 / 96)), (13, (1 / 6)), (35, (1 / 6)), (52, (1 / 3)), (60, (1 / 6)), (128, (1 / 6)), (490, (-1 / 2))]

def value541 : Sparse (Fin 909) := [(1, (-1 / 12)), (3, (1 / 6)), (5, (-1 / 12)), (7, (1 / 3)), (69, (1 / 6)), (124, (-1 / 2))]

def value542 : Sparse (Fin 909) := [(1, (-1 / 32)), (2, (1 / 96)), (3, (1 / 6)), (7, (1 / 6)), (23, (-1 / 2)), (124, (-1 / 2)), (125, (-1 / 2))]

def value543 : Sparse (Fin 909) := [(1, (1 / 24)), (2, (5 / 96)), (5, (-1 / 6)), (6, (1 / 96)), (7, (1 / 6)), (9, (-1 / 24)), (35, (1 / 6)), (52, (1 / 3)), (69, (1 / 3)), (495, (1 / 6))]

def value544 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (1 / 32)), (2, (1 / 16)), (3, (1 / 6)), (5, (-1 / 12)), (7, (1 / 6)), (52, (1 / 6)), (69, (1 / 6)), (126, (-1 / 2))]

def value545 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (1 / 24)), (2, (1 / 48)), (8, (1 / 6)), (24, (-1 / 2)), (126, (-1 / 1))]

def value546 : Sparse (Fin 909) := [(27, (1 / 8)), (68, (1 / 8)), (124, (-1 / 2)), (126, (-1 / 2)), (493, (-1 / 2))]

def value547 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 48)), (2, (1 / 96)), (27, (1 / 8)), (51, (-1 / 2)), (124, (-1 / 2)), (126, (-1 / 2))]

def value548 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 48)), (5, (-1 / 24)), (68, (1 / 8)), (125, (-1 / 2)), (126, (-1 / 2)), (494, (-1 / 2))]

def value549 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 48)), (5, (-1 / 12)), (13, (1 / 6)), (52, (1 / 3)), (69, (1 / 6)), (125, (-1 / 2))]

def value550 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (1 / 32)), (6, (1 / 48)), (9, (-1 / 24)), (52, (1 / 6)), (69, (1 / 6)), (128, (1 / 6)), (492, (-1 / 2)), (495, (1 / 6))]

def value551 : Sparse (Fin 909) := [(1, (-1 / 32)), (2, (1 / 96)), (3, (1 / 3)), (7, (1 / 3)), (13, (1 / 6)), (35, (1 / 3)), (70, (1 / 6)), (125, (-1 / 2))]

def value552 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 24)), (5, (-1 / 8)), (6, (1 / 32)), (9, (-1 / 12)), (52, (1 / 3)), (58, (1 / 96)), (69, (1 / 6)), (310, (1 / 3)), (495, (1 / 3))]

def value553 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (3 / 32)), (2, (11 / 96)), (5, (-5 / 24)), (6, (1 / 32)), (9, (-1 / 24)), (52, (1 / 3)), (69, (1 / 6))]

def value554 : Sparse (Fin 909) := [(0, (-1 / 160)), (1, (5 / 48)), (2, (7 / 96)), (5, (-1 / 12)), (8, (1 / 3)), (71, (1 / 6)), (126, (-1 / 2))]

def value555 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (5 / 48)), (2, (-1 / 32)), (3, (1 / 6)), (5, (-1 / 24)), (7, (1 / 6))]

def value556 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 16)), (2, (1 / 96)), (7, (1 / 6)), (12, (1 / 6)), (13, (1 / 6)), (35, (1 / 6))]

def value558 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 32)), (3, (1 / 6)), (5, (-1 / 24)), (6, (1 / 96)), (35, (1 / 6)), (310, (1 / 6)), (495, (1 / 6))]

def value559 : Sparse (Fin 909) := [(0, (-1 / 240)), (2, (1 / 32)), (3, (1 / 6)), (5, (-1 / 12)), (6, (1 / 96)), (52, (1 / 6))]

def value560 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-1 / 48)), (2, (1 / 24)), (5, (-1 / 24)), (8, (1 / 6))]

def value561 : Sparse (Fin 909) := [(0, (-1 / 160)), (1, (1 / 96)), (2, (1 / 16)), (3, (1 / 6)), (5, (-1 / 24)), (7, (1 / 6)), (8, (1 / 6)), (51, (-1 / 2))]

def value562 : Sparse (Fin 909) := [(1, (-1 / 24)), (2, (1 / 12)), (3, (1 / 3)), (5, (-1 / 24)), (7, (1 / 6))]

def value563 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (5 / 96)), (2, (1 / 96)), (3, (1 / 6)), (5, (-1 / 24)), (6, (1 / 96)), (13, (1 / 3)), (35, (1 / 6)), (52, (1 / 6))]

def value564 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (5 / 96)), (5, (-1 / 8)), (6, (1 / 32)), (13, (1 / 6)), (52, (1 / 3)), (82, (1 / 6)), (128, (1 / 3)), (310, (1 / 6)), (495, (1 / 6))]

def value565 : Sparse (Fin 909) := [(1, (1 / 32)), (2, (1 / 32)), (5, (-1 / 8)), (13, (1 / 6)), (52, (1 / 3)), (82, (1 / 6)), (128, (1 / 3))]

def value566 : Sparse (Fin 909) := [(0, (-1 / 160)), (1, (-1 / 8)), (2, (1 / 96)), (3, (1 / 2)), (12, (1 / 2)), (13, (1 / 3))]

def value567 : Sparse (Fin 909) := [(3, (1 / 3)), (12, (1 / 3)), (13, (2 / 3)), (127, (-1 / 2)), (128, (1 / 6))]

def value568 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 48)), (3, (1 / 3)), (26, (1 / 6)), (35, (1 / 3)), (52, (1 / 3)), (493, (-1 / 2)), (495, (1 / 6))]

def value569 : Sparse (Fin 909) := [(0, (-1 / 160)), (2, (5 / 96)), (3, (1 / 3)), (4, (1 / 6)), (51, (-1 / 2)), (52, (1 / 6))]

def value570 : Sparse (Fin 909) := [(0, (1 / 96)), (1, (-1 / 16)), (2, (7 / 96)), (3, (1 / 6))]

def value571 : Sparse (Fin 909) := [(51, (-1 / 2)), (55, (-1 / 2)), (493, (-1 / 2)), (494, (-1 / 2))]

def value572 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-1 / 48)), (2, (1 / 24)), (3, (1 / 3)), (12, (1 / 6)), (13, (1 / 6)), (51, (-1 / 2)), (52, (1 / 6))]

def value573 : Sparse (Fin 909) := [(0, (-1 / 120)), (1, (-5 / 96)), (2, (1 / 32)), (3, (1 / 3)), (12, (1 / 6)), (13, (1 / 6))]

def value574 : Sparse (Fin 909) := [(1, (1 / 32)), (5, (-1 / 24)), (6, (1 / 96)), (13, (1 / 3)), (35, (1 / 6)), (52, (1 / 6)), (128, (1 / 6)), (494, (-1 / 2)), (495, (1 / 6))]

def value575 : Sparse (Fin 909) := [(1, (7 / 96)), (2, (1 / 24)), (3, (1 / 6)), (5, (-1 / 24)), (6, (1 / 96)), (13, (1 / 2)), (52, (1 / 3)), (128, (1 / 6))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value576 : Sparse (Fin 909) := [(498, (1 / 1))]

def value577 : Sparse (Fin 909) := [(499, (1 / 1))]

def value578 : Sparse (Fin 909) := [(500, (1 / 1))]

def value579 : Sparse (Fin 909) := [(501, (1 / 1))]

def value580 : Sparse (Fin 909) := [(502, (1 / 1))]

def value581 : Sparse (Fin 909) := [(503, (1 / 1))]

def value582 : Sparse (Fin 909) := [(505, (1 / 1))]

def value583 : Sparse (Fin 909) := [(506, (1 / 1))]

def value584 : Sparse (Fin 909) := [(507, (1 / 1))]

def value585 : Sparse (Fin 909) := [(508, (1 / 1))]

def value586 : Sparse (Fin 909) := [(517, (1 / 1))]

def value587 : Sparse (Fin 909) := [(129, (1 / 1))]

def value588 : Sparse (Fin 909) := [(137, (1 / 1))]

def value589 : Sparse (Fin 909) := [(138, (1 / 1))]

def value590 : Sparse (Fin 909) := [(139, (1 / 1))]

def value591 : Sparse (Fin 909) := [(140, (1 / 1))]

def value592 : Sparse (Fin 909) := [(141, (1 / 1))]

def value593 : Sparse (Fin 909) := [(538, (1 / 1))]

def value594 : Sparse (Fin 909) := [(539, (1 / 1))]

def value595 : Sparse (Fin 909) := [(540, (1 / 1))]

def value596 : Sparse (Fin 909) := [(541, (1 / 1))]

def value597 : Sparse (Fin 909) := [(543, (1 / 1))]

def value598 : Sparse (Fin 909) := [(142, (1 / 1))]

def value599 : Sparse (Fin 909) := [(143, (1 / 1))]

def value600 : Sparse (Fin 909) := [(545, (1 / 1))]

def value601 : Sparse (Fin 909) := [(144, (1 / 1))]

def value602 : Sparse (Fin 909) := [(145, (1 / 1))]

def value603 : Sparse (Fin 909) := [(146, (1 / 1))]

def value604 : Sparse (Fin 909) := [(546, (1 / 1))]

def value605 : Sparse (Fin 909) := [(14, (1 / 1))]

def value606 : Sparse (Fin 909) := [(15, (1 / 1))]

def value607 : Sparse (Fin 909) := [(16, (1 / 1))]

def value608 : Sparse (Fin 909) := [(17, (1 / 1))]

def value609 : Sparse (Fin 909) := [(18, (1 / 1))]

def value610 : Sparse (Fin 909) := [(640, (1 / 1))]

def value611 : Sparse (Fin 909) := [(643, (1 / 1))]

def value612 : Sparse (Fin 909) := [(177, (1 / 1))]

def value613 : Sparse (Fin 909) := [(19, (1 / 1))]

def value614 : Sparse (Fin 909) := [(20, (1 / 1))]

def value615 : Sparse (Fin 909) := [(702, (1 / 1))]

def value616 : Sparse (Fin 909) := [(190, (1 / 1))]

def value617 : Sparse (Fin 909) := [(191, (1 / 1))]

def value618 : Sparse (Fin 909) := [(709, (1 / 1))]

def value619 : Sparse (Fin 909) := [(53, (1 / 1))]

def value620 : Sparse (Fin 909) := [(21, (1 / 1))]

def value621 : Sparse (Fin 909) := [(22, (1 / 1))]

def value622 : Sparse (Fin 909) := [(194, (1 / 1))]

def value623 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (1 / 96)), (5, (-1 / 24)), (7, (1 / 6)), (35, (1 / 6)), (59, (-1 / 2)), (199, (-1 / 2)), (271, (-1 / 2))]

def value624 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-1 / 16)), (3, (1 / 3)), (12, (1 / 3)), (33, (-1 / 1))]

def value625 : Sparse (Fin 909) := [(195, (1 / 1))]

def value626 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 32)), (3, (1 / 6)), (4, (1 / 6)), (25, (-1 / 2)), (31, (-1 / 2)), (33, (-1 / 2))]

def value627 : Sparse (Fin 909) := [(55, (-1 / 2)), (63, (-1 / 2)), (237, (-1 / 2)), (306, (-1 / 2))]

def value628 : Sparse (Fin 909) := [(54, (-1 / 2)), (228, (-1 / 2)), (271, (-1 / 2)), (721, (-1 / 2))]

def value629 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 96)), (5, (-1 / 12)), (6, (1 / 32)), (13, (1 / 6)), (35, (1 / 6)), (52, (1 / 6)), (82, (1 / 6)), (128, (1 / 6)), (721, (-1 / 2))]

def value630 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 48)), (5, (-1 / 12)), (8, (1 / 6)), (59, (-1 / 1)), (201, (-1 / 2))]

def value631 : Sparse (Fin 909) := [(23, (-1 / 2)), (54, (-1 / 2)), (125, (-1 / 2)), (196, (-1 / 2))]

def value632 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (-1 / 24)), (5, (-1 / 24)), (6, (1 / 32)), (7, (1 / 6)), (9, (-1 / 24)), (11, (1 / 6)), (35, (1 / 2)), (70, (1 / 3)), (278, (1 / 6))]

def value633 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (-5 / 96)), (3, (1 / 6)), (6, (1 / 96)), (7, (1 / 6)), (26, (1 / 6)), (35, (1 / 3)), (70, (1 / 6)), (197, (-1 / 2))]

def value634 : Sparse (Fin 909) := [(24, (-1 / 2)), (56, (-1 / 2)), (197, (-1 / 1))]

def value635 : Sparse (Fin 909) := [(1, (-1 / 96)), (2, (-1 / 96)), (5, (-1 / 24)), (55, (-1 / 2)), (125, (-1 / 2)), (197, (-1 / 2))]

def value636 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 24)), (6, (1 / 48)), (13, (1 / 6)), (35, (1 / 3)), (70, (1 / 6)), (196, (-1 / 2))]

def value637 : Sparse (Fin 909) := [(2, (-1 / 24)), (5, (-1 / 24)), (6, (-1 / 24)), (9, (-1 / 24)), (35, (1 / 6)), (70, (1 / 6)), (82, (1 / 6)), (278, (1 / 6)), (723, (-1 / 2))]

def value638 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (1 / 48)), (5, (-1 / 12)), (6, (1 / 96)), (7, (1 / 6)), (9, (-1 / 12)), (35, (1 / 6)), (69, (1 / 6)), (70, (1 / 6)), (278, (1 / 6)), (495, (1 / 6)), (726, (-1 / 2))]

def value639 : Sparse (Fin 909) := [(1, (-1 / 96)), (3, (1 / 6)), (5, (-1 / 12)), (6, (1 / 96)), (7, (1 / 3)), (35, (1 / 3)), (52, (1 / 6)), (69, (1 / 6)), (70, (1 / 6))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSources_Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSourceBridge

def coordinateMap (i : Fin 271) : Fin 909 :=
  ((#[coordinateChunk0, coordinateChunk1, coordinateChunk2, coordinateChunk3, coordinateChunk4])[i.val / 64]!)[i.val % 64]!

end MUB6.Certificate.PairSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_IntegerTerms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

def integerTerm0 : Integer.Sparse (Fin 909) := [(0, 23514624), (1, -9797760), (2, -9797760), (5, 19595520), (27, -58786560), (68, -117573120)]

def integerTerm1 : Integer.Sparse (Fin 909) := [(0, -9144576), (1, -16329600), (2, 3265920), (5, -6531840), (8, -26127360), (27, 19595520), (30, 78382080), (68, 39191040), (236, 156764160)]

def integerTerm2 : Integer.Sparse (Fin 909) := [(0, -3265920), (1, -1632960), (2, 1632960), (5, -3265920), (8, -13063680), (24, 39191040), (27, 9797760), (68, 19595520), (126, 78382080)]

def integerTerm3 : Integer.Sparse (Fin 909) := [(0, -5552064), (1, 4898880), (2, -3265920), (68, 19595520), (126, 39191040), (236, 39191040)]

def integerTerm4 : Integer.Sparse (Fin 909) := [(0, -5552064), (1, 4898880), (2, -3265920), (68, 19595520), (126, 39191040), (236, 39191040)]

def integerTerm5 : Integer.Sparse (Fin 909) := [(0, -9144576), (1, -16329600), (2, 3265920), (5, -6531840), (8, -26127360), (27, 19595520), (30, 78382080), (68, 39191040), (236, 156764160)]

def integerTerm6 : Integer.Sparse (Fin 909) := [(0, 13934592), (1, 21772800), (2, -4354560), (5, 2177280), (8, 17418240), (27, -6531840), (28, -78382080), (30, -26127360), (68, -13063680), (236, -104509440), (253, -156764160)]

def integerTerm7 : Integer.Sparse (Fin 909) := [(0, -2395008), (2, 1088640), (5, 1088640), (8, 8709120), (20, -39191040), (24, -13063680), (27, -3265920), (68, -6531840), (126, -26127360), (208, -78382080), (236, -26127360)]

def integerTerm8 : Integer.Sparse (Fin 909) := [(0, -3483648), (1, -544320), (2, -544320), (68, -6531840), (126, -13063680), (208, -39191040), (236, -39191040), (253, -39191040)]

def integerTerm9 : Integer.Sparse (Fin 909) := [(0, -3483648), (1, -544320), (2, -544320), (68, -6531840), (126, -13063680), (208, -39191040), (236, -39191040), (253, -39191040)]

def integerTerm10 : Integer.Sparse (Fin 909) := [(0, -3265920), (1, -1632960), (2, 1632960), (5, -3265920), (8, -13063680), (24, 39191040), (27, 9797760), (68, 19595520), (126, 78382080)]

def integerTerm11 : Integer.Sparse (Fin 909) := [(0, -2395008), (2, 1088640), (5, 1088640), (8, 8709120), (20, -39191040), (24, -13063680), (27, -3265920), (68, -6531840), (126, -26127360), (208, -78382080), (236, -26127360)]

def integerTerm12 : Integer.Sparse (Fin 909) := [(0, 3646944), (1, -3538080), (2, -1632960), (3, 8709120), (4, 8709120), (5, 544320), (8, 4354560), (12, 4354560), (17, -19595520), (24, -13063680), (27, -1632960), (30, 6531840), (68, -3265920), (126, -26127360), (203, -39191040)]

def integerTerm13 : Integer.Sparse (Fin 909) := [(0, 408240), (1, -1224720), (2, 272160), (4, 2177280), (31, -6531840), (68, -3265920), (126, -19595520), (207, -19595520), (208, -19595520), (236, -6531840)]

def integerTerm14 : Integer.Sparse (Fin 909) := [(0, 408240), (1, -1224720), (2, 272160), (4, 2177280), (31, -6531840), (68, -3265920), (126, -19595520), (207, -19595520), (208, -19595520), (236, -6531840)]

def integerTerm15 : Integer.Sparse (Fin 909) := [(0, -5552064), (1, 4898880), (2, -3265920), (68, 19595520), (126, 39191040), (236, 39191040)]

def integerTerm16 : Integer.Sparse (Fin 909) := [(0, -3483648), (1, -544320), (2, -544320), (68, -6531840), (126, -13063680), (208, -39191040), (236, -39191040), (253, -39191040)]

def integerTerm17 : Integer.Sparse (Fin 909) := [(0, 408240), (1, -1224720), (2, 272160), (4, 2177280), (31, -6531840), (68, -3265920), (126, -19595520), (207, -19595520), (208, -19595520), (236, -6531840)]

def integerTerm18 : Integer.Sparse (Fin 909) := [(0, 6069168), (1, -5579280), (2, 3538080), (3, 4354560), (4, 4354560), (68, -3265920), (126, -13063680), (203, -19595520), (236, -13063680), (253, -19595520)]

def integerTerm19 : Integer.Sparse (Fin 909) := [(0, 1088640), (1, -1632960), (2, 544320), (68, -3265920), (126, -13063680), (208, -39191040), (236, -13063680)]

def integerTerm20 : Integer.Sparse (Fin 909) := [(0, -5552064), (1, 4898880), (2, -3265920), (68, 19595520), (126, 39191040), (236, 39191040)]

def integerTerm21 : Integer.Sparse (Fin 909) := [(0, -3483648), (1, -544320), (2, -544320), (68, -6531840), (126, -13063680), (208, -39191040), (236, -39191040), (253, -39191040)]

def integerTerm22 : Integer.Sparse (Fin 909) := [(0, 408240), (1, -1224720), (2, 272160), (4, 2177280), (31, -6531840), (68, -3265920), (126, -19595520), (207, -19595520), (208, -19595520), (236, -6531840)]

def integerTerm23 : Integer.Sparse (Fin 909) := [(0, 1088640), (1, -1632960), (2, 544320), (68, -3265920), (126, -13063680), (208, -39191040), (236, -13063680)]

def integerTerm24 : Integer.Sparse (Fin 909) := [(0, 6069168), (1, -5579280), (2, 3538080), (3, 4354560), (4, 4354560), (68, -3265920), (126, -13063680), (203, -19595520), (236, -13063680), (253, -19595520)]

def integerTerm25 : Integer.Sparse (Fin 909) := [(0, -326592), (1, -6713280), (2, 1224720), (3, -8709120), (5, -2177280), (6, -181440), (7, -5806080), (12, -5806080), (23, -8709120), (27, -2177280), (58, 45360), (68, 1088640), (69, -2903040), (230, 6531840)]

def integerTerm26 : Integer.Sparse (Fin 909) := [(0, -18144), (1, -5806080), (2, 544320), (5, -362880), (6, 272160), (7, -8709120), (12, -8709120), (13, -5806080), (23, -13063680), (27, 1088640), (35, -5806080), (63, -8709120)]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue0 : Sparse (Fin 909) := [(0, (1 / 6)), (1, (-5 / 72)), (2, (-5 / 72)), (5, (5 / 36)), (27, (-5 / 12)), (68, (-5 / 6))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue1 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (25 / 432)), (2, (-5 / 432)), (5, (5 / 216)), (8, (5 / 54)), (27, (-5 / 72)), (30, (-5 / 18)), (68, (-5 / 36)), (236, (-5 / 9))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue10 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (5 / 432)), (2, (-5 / 432)), (5, (5 / 216)), (8, (5 / 54)), (24, (-5 / 18)), (27, (-5 / 72)), (68, (-5 / 36)), (126, (-5 / 9))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue11 : Sparse (Fin 909) := [(0, (-11 / 1296)), (2, (5 / 1296)), (5, (5 / 1296)), (8, (5 / 162)), (20, (-5 / 36)), (24, (-5 / 108)), (27, (-5 / 432)), (68, (-5 / 216)), (126, (-5 / 54)), (208, (-5 / 18)), (236, (-5 / 54))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue12 : Sparse (Fin 909) := [(0, (67 / 2592)), (1, (-65 / 2592)), (2, (-5 / 432)), (3, (5 / 81)), (4, (5 / 81)), (5, (5 / 1296)), (8, (5 / 162)), (12, (5 / 162)), (17, (-5 / 36)), (24, (-5 / 54)), (27, (-5 / 432)), (30, (5 / 108)), (68, (-5 / 216)), (126, (-5 / 27)), (203, (-5 / 18))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue13 : Sparse (Fin 909) := [(0, (5 / 1728)), (1, (-5 / 576)), (2, (5 / 2592)), (4, (5 / 324)), (31, (-5 / 108)), (68, (-5 / 216)), (126, (-5 / 36)), (207, (-5 / 36)), (208, (-5 / 36)), (236, (-5 / 108))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue14 : Sparse (Fin 909) := [(0, (5 / 1728)), (1, (-5 / 576)), (2, (5 / 2592)), (4, (5 / 324)), (31, (-5 / 108)), (68, (-5 / 216)), (126, (-5 / 36)), (207, (-5 / 36)), (208, (-5 / 36)), (236, (-5 / 108))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue15 : Sparse (Fin 909) := [(0, (17 / 432)), (1, (-5 / 144)), (2, (5 / 216)), (68, (-5 / 36)), (126, (-5 / 18)), (236, (-5 / 18))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue16 : Sparse (Fin 909) := [(0, (-1 / 81)), (1, (-5 / 2592)), (2, (-5 / 2592)), (68, (-5 / 216)), (126, (-5 / 108)), (208, (-5 / 36)), (236, (-5 / 36)), (253, (-5 / 36))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue17 : Sparse (Fin 909) := [(0, (5 / 1728)), (1, (-5 / 576)), (2, (5 / 2592)), (4, (5 / 324)), (31, (-5 / 108)), (68, (-5 / 216)), (126, (-5 / 36)), (207, (-5 / 36)), (208, (-5 / 36)), (236, (-5 / 108))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue18 : Sparse (Fin 909) := [(0, (223 / 5184)), (1, (-205 / 5184)), (2, (65 / 2592)), (3, (5 / 162)), (4, (5 / 162)), (68, (-5 / 216)), (126, (-5 / 54)), (203, (-5 / 36)), (236, (-5 / 54)), (253, (-5 / 36))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue19 : Sparse (Fin 909) := [(0, (5 / 648)), (1, (-5 / 432)), (2, (5 / 1296)), (68, (-5 / 216)), (126, (-5 / 54)), (208, (-5 / 18)), (236, (-5 / 54))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue2 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (5 / 432)), (2, (-5 / 432)), (5, (5 / 216)), (8, (5 / 54)), (24, (-5 / 18)), (27, (-5 / 72)), (68, (-5 / 36)), (126, (-5 / 9))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue20 : Sparse (Fin 909) := [(0, (17 / 432)), (1, (-5 / 144)), (2, (5 / 216)), (68, (-5 / 36)), (126, (-5 / 18)), (236, (-5 / 18))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue21 : Sparse (Fin 909) := [(0, (-1 / 81)), (1, (-5 / 2592)), (2, (-5 / 2592)), (68, (-5 / 216)), (126, (-5 / 108)), (208, (-5 / 36)), (236, (-5 / 36)), (253, (-5 / 36))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue22 : Sparse (Fin 909) := [(0, (5 / 1728)), (1, (-5 / 576)), (2, (5 / 2592)), (4, (5 / 324)), (31, (-5 / 108)), (68, (-5 / 216)), (126, (-5 / 36)), (207, (-5 / 36)), (208, (-5 / 36)), (236, (-5 / 108))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue23 : Sparse (Fin 909) := [(0, (5 / 648)), (1, (-5 / 432)), (2, (5 / 1296)), (68, (-5 / 216)), (126, (-5 / 54)), (208, (-5 / 18)), (236, (-5 / 54))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue24 : Sparse (Fin 909) := [(0, (223 / 5184)), (1, (-205 / 5184)), (2, (65 / 2592)), (3, (5 / 162)), (4, (5 / 162)), (68, (-5 / 216)), (126, (-5 / 54)), (203, (-5 / 36)), (236, (-5 / 54)), (253, (-5 / 36))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue25 : Sparse (Fin 909) := [(0, (-1 / 144)), (1, (-185 / 1296)), (2, (5 / 192)), (3, (-5 / 27)), (5, (-5 / 108)), (6, (-5 / 1296)), (7, (-10 / 81)), (12, (-10 / 81)), (23, (-5 / 27)), (27, (-5 / 108)), (58, (5 / 5184)), (68, (5 / 216)), (69, (-5 / 81)), (230, (5 / 36))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue26 : Sparse (Fin 909) := [(0, (-1 / 2592)), (1, (-10 / 81)), (2, (5 / 432)), (5, (-5 / 648)), (6, (5 / 864)), (7, (-5 / 27)), (12, (-5 / 27)), (13, (-10 / 81)), (23, (-5 / 18)), (27, (5 / 216)), (35, (-10 / 81)), (63, (-5 / 27))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue3 : Sparse (Fin 909) := [(0, (17 / 432)), (1, (-5 / 144)), (2, (5 / 216)), (68, (-5 / 36)), (126, (-5 / 18)), (236, (-5 / 18))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue4 : Sparse (Fin 909) := [(0, (17 / 432)), (1, (-5 / 144)), (2, (5 / 216)), (68, (-5 / 36)), (126, (-5 / 18)), (236, (-5 / 18))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue5 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (25 / 432)), (2, (-5 / 432)), (5, (5 / 216)), (8, (5 / 54)), (27, (-5 / 72)), (30, (-5 / 18)), (68, (-5 / 36)), (236, (-5 / 9))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue6 : Sparse (Fin 909) := [(0, (2 / 81)), (1, (25 / 648)), (2, (-5 / 648)), (5, (5 / 1296)), (8, (5 / 162)), (27, (-5 / 432)), (28, (-5 / 36)), (30, (-5 / 108)), (68, (-5 / 216)), (236, (-5 / 27)), (253, (-5 / 18))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue7 : Sparse (Fin 909) := [(0, (-11 / 1296)), (2, (5 / 1296)), (5, (5 / 1296)), (8, (5 / 162)), (20, (-5 / 36)), (24, (-5 / 108)), (27, (-5 / 432)), (68, (-5 / 216)), (126, (-5 / 54)), (208, (-5 / 18)), (236, (-5 / 54))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue8 : Sparse (Fin 909) := [(0, (-1 / 81)), (1, (-5 / 2592)), (2, (-5 / 2592)), (68, (-5 / 216)), (126, (-5 / 108)), (208, (-5 / 36)), (236, (-5 / 36)), (253, (-5 / 36))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue9 : Sparse (Fin 909) := [(0, (-1 / 81)), (1, (-5 / 2592)), (2, (-5 / 2592)), (68, (-5 / 216)), (126, (-5 / 108)), (208, (-5 / 36)), (236, (-5 / 36)), (253, (-5 / 36))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Tao_TaoArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact arithmetic in `ℤ[ω]`, interpreted in the same complex root as Tao's
matrix.  These definitions are for certificate checking, not assumptions. -/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6.TaoArithmetic

def value (z : Coeff) : ℂ := (z.1 : ℂ) + (z.2 : ℂ) * omega

def mul (z w : Coeff) : Coeff :=
  (z.1 * w.1 - z.2 * w.2, z.1 * w.2 + z.2 * w.1 - z.2 * w.2)

def conjugate (z : Coeff) : Coeff := (z.1 - z.2, -z.2)

def root (n : ℤ) : Coeff :=
  if n % 3 = 0 then (1, 0) else if n % 3 = 1 then (0, 1) else (-1, -1)

@[simp] theorem value_zero : value 0 = 0 := by simp [value]

@[simp] theorem value_add (z w : Coeff) : value (z + w) = value z + value w := by
  simp [value]
  ring

def counts (a : Charge) : Coeff :=
  ∑ k, root (∑ i, (taoExponent i k : ℤ) * a i)

end MUB6.TaoArithmetic

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Tao_TaoSparse
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6.TaoArithmetic

def encode (a : Charge) : List ℤ := List.ofFn a

def decode (l : List ℤ) : Charge := fun i => l[i.val]?.getD 0

@[simp] theorem decode_encode (a : Charge) : decode (encode a) = a := by
  funext i
  fin_cases i <;> simp [decode, encode]

abbrev Sparse := Certificate.Integer.Sparse (List ℤ)

def momentValues (f : Charge → ℂ) (key : List ℤ) : ℝ :=
  if key.headD 0 = 0 then (f (decode key.tail)).re
  else (omega * f (decode key.tail)).re

def monomial (a : Charge) (z : Coeff) : Sparse :=
  [(0 :: encode a, z.1), (1 :: encode a, z.2)]

def offDiagonalPairs : List (Coord × Coord) :=
  [(0,1),(0,2),(0,3),(0,4),(0,5),
   (1,0),(1,2),(1,3),(1,4),(1,5),
   (2,0),(2,1),(2,3),(2,4),(2,5),
   (3,0),(3,1),(3,2),(3,4),(3,5),
   (4,0),(4,1),(4,2),(4,3),(4,5),
   (5,0),(5,1),(5,2),(5,3),(5,4)]

def row (a c : Charge) (w : Coeff) : Sparse :=
  offDiagonalPairs.flatMap (fun p => monomial (a + difference p.1 p.2)
    (mul w (conjugate (counts (c + difference p.1 p.2)))))

end MUB6.TaoArithmetic

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined0_part0 : Sparse := [([0, -2, -1, 0, 0, 1, 2], -36), ([0, -1, -2, 0, 0, 1, 2], 27), ([0, -1, -2, 0, 0, 2, 1], -27), ([0, -1, -2, 0, 1, 1, 1], 9), ([0, -1, -2, 1, 0, 1, 1], -9), ([0, -1, -1, -1, 0, 2, 1], -9), ([0, -1, -1, 0, 0, 0, 2], -27), ([0, -1, -1, 0, 1, 0, 1], -36), ([0, -1, -1, 0, 1, 1, 0], -9), ([0, -1, -1, 1, -1, 1, 1], -27), ([0, -1, -1, 1, 0, 0, 1], 36), ([0, -1, -1, 1, 0, 1, 0], -36), ([0, -1, 0, 0, -1, 1, 1], -36), ([0, 0, -2, 0, 0, 1, 1], -36), ([0, 0, -1, -1, 0, 1, 1], -27), ([0, 0, -1, 0, -1, 1, 1], 27), ([0, 0, -1, 0, 0, 0, 1], -9), ([0, 0, -1, 0, 0, 1, 0], 9), ([1, -2, -1, 0, 0, 2, 1], -36), ([1, -2, 0, 0, 0, 1, 1], 18), ([1, -1, -2, 0, 0, 1, 2], 27), ([1, -1, -2, 1, 0, 1, 1], -9), ([1, -1, -1, -1, 0, 1, 2], -9), ([1, -1, -1, -1, 1, 1, 1], 27)]

def combined0_part1 : Sparse := [([1, -1, -1, 0, -1, 1, 2], -9), ([1, -1, -1, 0, -1, 2, 1], -9), ([1, -1, -1, 0, 0, 0, 2], -27), ([1, -1, -1, 0, 0, 2, 0], 27), ([1, -1, -1, 0, 1, 0, 1], -9), ([1, -1, -1, 0, 1, 1, 0], -36), ([1, -1, -1, 1, -1, 1, 1], -27), ([1, -1, -1, 1, 0, 0, 1], 27), ([1, -1, -1, 1, 0, 1, 0], -9), ([1, -1, 0, -1, 0, 1, 1], -36), ([1, 0, -2, 0, 0, 1, 1], -36), ([1, 0, -1, 0, -1, 1, 1], 27), ([1, 0, -1, 0, 0, 0, 1], -9)]

def combined0 : Sparse := combined0_part0 ++ combined0_part1

def combined1_part0 : Sparse := [([0, -2, -1, 0, 0, 1, 2], -27), ([0, -2, -1, 1, 0, 1, 1], 9), ([0, -1, -2, 0, 0, 1, 2], 27), ([0, -1, -2, 0, 0, 2, 1], -27), ([0, -1, -2, 0, 1, 1, 1], 9), ([0, -1, -2, 1, 0, 1, 1], -9), ([0, -1, -1, -1, 0, 1, 2], 9), ([0, -1, -1, 0, -1, 1, 2], -9), ([0, -1, -1, 0, -1, 2, 1], 9), ([0, -1, -1, 0, 0, 0, 2], -18), ([0, -1, -1, 0, 1, 0, 1], -27), ([0, -1, -1, 1, -1, 1, 1], -18), ([0, -1, -1, 1, 0, 0, 1], 27), ([0, -1, -1, 1, 0, 1, 0], -27), ([0, -1, 0, 0, -1, 1, 1], -27), ([0, -1, 0, 0, 0, 0, 1], 9), ([0, 0, -2, 0, 0, 1, 1], -18), ([0, 0, -1, -1, 0, 1, 1], -27), ([0, 0, -1, 0, -1, 1, 1], 27), ([0, 0, -1, 0, 0, 0, 1], -9), ([0, 0, -1, 0, 0, 1, 0], 9), ([1, -2, -1, 0, 0, 2, 1], -27), ([1, -2, -1, 0, 1, 1, 1], 9), ([1, -2, 0, 0, 0, 1, 1], 18)]

def combined1_part1 : Sparse := [([1, -1, -2, 0, 0, 1, 2], 27), ([1, -1, -2, 1, 0, 1, 1], -9), ([1, -1, -1, -1, 0, 2, 1], 9), ([1, -1, -1, -1, 1, 1, 1], 18), ([1, -1, -1, 0, -1, 1, 2], -9), ([1, -1, -1, 0, 0, 0, 2], -18), ([1, -1, -1, 0, 0, 2, 0], 18), ([1, -1, -1, 0, 1, 1, 0], -27), ([1, -1, -1, 1, -1, 1, 1], -18), ([1, -1, -1, 1, 0, 0, 1], 27), ([1, -1, 0, -1, 0, 1, 1], -27), ([1, -1, 0, 0, 0, 1, 0], 9), ([1, 0, -2, 0, 0, 1, 1], -18), ([1, 0, -1, 0, -1, 1, 1], 27), ([1, 0, -1, 0, 0, 0, 1], -9)]

def combined1 : Sparse := combined1_part0 ++ combined1_part1

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined10_part0 : Sparse := [([0, -2, -1, 0, 1, 1, 1], -9), ([0, -2, -1, 0, 1, 2, 0], -18), ([0, -2, -1, 0, 2, 1, 0], -27), ([0, -2, -1, 1, 1, 1, 0], -18), ([0, -1, -2, 0, 1, 1, 1], -18), ([0, -1, -2, 0, 1, 2, 0], -18), ([0, -1, -2, 0, 2, 1, 0], -27), ([0, -1, -2, 1, 1, 1, 0], -9), ([0, -1, -1, -1, 1, 2, 0], -18), ([0, -1, -1, -1, 2, 1, 0], -9), ([0, -1, -1, 0, 0, 1, 1], -18), ([0, -1, -1, 0, 1, 0, 1], -27), ([0, -1, -1, 0, 1, 2, -1], -18), ([0, -1, -1, 0, 2, 1, -1], -9), ([0, -1, -1, 1, 0, 1, 0], -18), ([0, -1, -1, 1, 1, 0, 0], -27), ([0, -1, 0, -1, 1, 1, 0], -18), ([0, -1, 0, 0, 0, 1, 0], -18), ([0, -1, 0, 0, 1, 0, 0], -9), ([0, -1, 0, 0, 1, 1, -1], -27), ([0, 0, -1, -1, 1, 1, 0], -27), ([0, 0, -1, 0, 0, 1, 0], -18), ([0, 0, -1, 0, 1, 0, 0], -9), ([0, 0, -1, 0, 1, 1, -1], -18)]

def combined10_part1 : Sparse := [([1, -2, -1, 0, 1, 1, 1], -18), ([1, -2, -1, 1, 1, 1, 0], -9), ([1, -2, 0, 0, 1, 1, 0], 9), ([1, -1, -2, 0, 1, 1, 1], -9), ([1, -1, -2, 1, 1, 1, 0], -18), ([1, -1, -1, -1, 1, 1, 1], 9), ([1, -1, -1, -1, 1, 2, 0], -18), ([1, -1, -1, -1, 2, 1, 0], -9), ([1, -1, -1, 0, 0, 2, 0], 18), ([1, -1, -1, 0, 1, 2, -1], -18), ([1, -1, -1, 0, 2, 1, -1], -9), ([1, -1, -1, 1, 1, 1, -1], 9), ([1, -1, 0, -1, 1, 1, 0], 9), ([1, -1, 0, 0, 0, 1, 0], -18), ([1, -1, 0, 0, 1, 0, 0], -9), ([1, -1, 0, 0, 1, 1, -1], -9), ([1, 0, -2, 0, 1, 1, 0], 9), ([1, 0, -1, -1, 1, 1, 0], -9), ([1, 0, -1, 0, 0, 1, 0], -18), ([1, 0, -1, 0, 1, 0, 0], -9), ([1, 0, -1, 0, 1, 1, -1], 9)]

def combined10 : Sparse := combined10_part0 ++ combined10_part1

def combined11_part0 : Sparse := [([0, -2, -1, 0, 1, 1, 1], -18), ([0, -2, -1, 0, 1, 2, 0], -18), ([0, -2, -1, 0, 2, 1, 0], -18), ([0, -2, -1, 1, 1, 1, 0], -18), ([0, -1, -2, 0, 1, 1, 1], -18), ([0, -1, -2, 0, 1, 2, 0], -18), ([0, -1, -2, 0, 2, 1, 0], -18), ([0, -1, -2, 1, 1, 1, 0], -18), ([0, -1, -1, -1, 1, 2, 0], -18), ([0, -1, -1, -1, 2, 1, 0], -18), ([0, -1, -1, 0, 0, 1, 1], -18), ([0, -1, -1, 0, 1, 0, 1], -18), ([0, -1, -1, 0, 1, 2, -1], -18), ([0, -1, -1, 0, 2, 1, -1], -18), ([0, -1, -1, 1, 0, 1, 0], -18), ([0, -1, -1, 1, 1, 0, 0], -18), ([0, -1, 0, -1, 1, 1, 0], -18), ([0, -1, 0, 0, 0, 1, 0], -18), ([0, -1, 0, 0, 1, 0, 0], -18), ([0, -1, 0, 0, 1, 1, -1], -18), ([0, 0, -1, -1, 1, 1, 0], -18), ([0, 0, -1, 0, 0, 1, 0], -18), ([0, 0, -1, 0, 1, 0, 0], -18), ([0, 0, -1, 0, 1, 1, -1], -18)]

def combined11_part1 : Sparse := [([1, -2, -1, 0, 1, 1, 1], -18), ([1, -2, -1, 1, 1, 1, 0], -18), ([1, -1, -2, 0, 1, 1, 1], -18), ([1, -1, -2, 1, 1, 1, 0], -18), ([1, -1, -1, -1, 1, 2, 0], -18), ([1, -1, -1, -1, 2, 1, 0], -18), ([1, -1, -1, 0, 1, 2, -1], -18), ([1, -1, -1, 0, 2, 1, -1], -18), ([1, -1, 0, 0, 0, 1, 0], -18), ([1, -1, 0, 0, 1, 0, 0], -18), ([1, 0, -1, 0, 0, 1, 0], -18), ([1, 0, -1, 0, 1, 0, 0], -18)]

def combined11 : Sparse := combined11_part0 ++ combined11_part1

def combined12_part0 : Sparse := [([0, -2, -1, 1, 0, 0, 2], -36), ([0, -2, -1, 2, 0, 0, 1], -36), ([0, -2, 0, 1, 0, 0, 1], -18), ([0, -1, -2, 1, 0, 0, 2], -27), ([0, -1, -2, 2, 0, 0, 1], -27), ([0, -1, -1, 0, 0, 0, 2], -27), ([0, -1, -1, 0, 0, 1, 1], -36), ([0, -1, -1, 0, 1, 0, 1], -27), ([0, -1, -1, 1, -1, 0, 2], 9), ([0, -1, -1, 1, -1, 1, 1], -27), ([0, -1, -1, 1, 0, -1, 2], -9), ([0, -1, -1, 1, 0, 1, 0], -27), ([0, -1, -1, 1, 1, -1, 1], -27), ([0, -1, -1, 1, 1, 0, 0], -36), ([0, -1, -1, 2, -1, 0, 1], -9), ([0, -1, -1, 2, 0, -1, 1], 9), ([0, -1, -1, 2, 0, 0, 0], -27), ([0, -1, 0, 1, -1, 0, 1], -36), ([0, -1, 0, 1, 0, -1, 1], -36), ([0, 0, -2, 1, 0, 0, 1], -36), ([0, 0, -1, 1, -1, 0, 1], -27), ([0, 0, -1, 1, 0, -1, 1], -27), ([1, -2, 0, 1, 0, 0, 1], -18), ([1, -1, -2, 1, 0, 1, 1], 9)]

def combined12_part1 : Sparse := [([1, -1, -2, 1, 1, 0, 1], 9), ([1, -1, -1, 0, 0, 0, 2], -27), ([1, -1, -1, 0, 0, 1, 1], -9), ([1, -1, -1, 0, 1, 0, 1], 9), ([1, -1, -1, 1, -1, 0, 2], 9), ([1, -1, -1, 1, -1, 1, 1], -27), ([1, -1, -1, 1, 0, 1, 0], 9), ([1, -1, -1, 1, 1, -1, 1], -27), ([1, -1, -1, 1, 1, 0, 0], -9), ([1, -1, -1, 2, 0, -1, 1], 9), ([1, -1, -1, 2, 0, 0, 0], -27), ([1, 0, -2, 1, 0, 0, 1], -36), ([1, 0, -1, 0, 0, 0, 1], 9), ([1, 0, -1, 1, 0, 0, 0], 9)]

def combined12 : Sparse := combined12_part0 ++ combined12_part1

def combined13_part0 : Sparse := [([0, -2, -1, 1, 0, 0, 2], -27), ([0, -2, -1, 2, 0, 0, 1], -27), ([0, -2, 0, 1, 0, 0, 1], -18), ([0, -1, -2, 1, 0, 0, 2], -27), ([0, -1, -2, 2, 0, 0, 1], -27), ([0, -1, -1, 0, 0, 0, 2], -18), ([0, -1, -1, 0, 0, 1, 1], -27), ([0, -1, -1, 0, 1, 0, 1], -27), ([0, -1, -1, 1, -1, 1, 1], -18), ([0, -1, -1, 1, 0, 1, 0], -27), ([0, -1, -1, 1, 1, -1, 1], -18), ([0, -1, -1, 1, 1, 0, 0], -27), ([0, -1, -1, 2, 0, 0, 0], -18), ([0, -1, 0, 1, -1, 0, 1], -27), ([0, -1, 0, 1, 0, -1, 1], -27), ([0, 0, -2, 1, 0, 0, 1], -18), ([0, 0, -1, 1, -1, 0, 1], -27), ([0, 0, -1, 1, 0, -1, 1], -27), ([1, -2, -1, 1, 0, 1, 1], 9), ([1, -2, -1, 1, 1, 0, 1], 9), ([1, -2, 0, 1, 0, 0, 1], -18), ([1, -1, -2, 1, 0, 1, 1], 9), ([1, -1, -2, 1, 1, 0, 1], 9), ([1, -1, -1, 0, 0, 0, 2], -18)]

def combined13_part1 : Sparse := [([1, -1, -1, 1, -1, 0, 2], 9), ([1, -1, -1, 1, -1, 1, 1], -18), ([1, -1, -1, 1, 0, -1, 2], 9), ([1, -1, -1, 1, 1, -1, 1], -18), ([1, -1, -1, 2, -1, 0, 1], 9), ([1, -1, -1, 2, 0, -1, 1], 9), ([1, -1, -1, 2, 0, 0, 0], -18), ([1, -1, 0, 0, 0, 0, 1], 9), ([1, -1, 0, 1, 0, 0, 0], 9), ([1, 0, -2, 1, 0, 0, 1], -18), ([1, 0, -1, 0, 0, 0, 1], 9), ([1, 0, -1, 1, 0, 0, 0], 9)]

def combined13 : Sparse := combined13_part0 ++ combined13_part1

def combined14_part0 : Sparse := [([0, -2, -1, 1, 0, 0, 2], -18), ([0, -2, -1, 1, 0, 1, 1], -9), ([0, -2, -1, 1, 1, 0, 1], 9), ([0, -2, -1, 2, 0, 0, 1], -27), ([0, -2, 0, 1, 0, 0, 1], -9), ([0, -1, -2, 1, 0, 0, 2], -18), ([0, -1, -2, 1, 0, 1, 1], 9), ([0, -1, -2, 1, 1, 0, 1], -9), ([0, -1, -2, 2, 0, 0, 1], -27), ([0, -1, -1, 0, 0, 0, 2], -18), ([0, -1, -1, 0, 0, 1, 1], -18), ([0, -1, -1, 0, 1, 0, 1], -18), ([0, -1, -1, 1, -1, 1, 1], -9), ([0, -1, -1, 1, 0, 1, 0], -27), ([0, -1, -1, 1, 1, -1, 1], -9), ([0, -1, -1, 1, 1, 0, 0], -27), ([0, -1, 0, 1, -1, 0, 1], -18), ([0, -1, 0, 1, 0, -1, 1], -27), ([0, 0, -2, 1, 0, 0, 1], -9), ([0, 0, -1, 1, -1, 0, 1], -27), ([0, 0, -1, 1, 0, -1, 1], -18), ([1, -2, -1, 1, 0, 1, 1], 9), ([1, -2, -1, 1, 1, 0, 1], 18), ([1, -2, 0, 1, 0, 0, 1], -9)]

def combined14_part1 : Sparse := [([1, -1, -2, 1, 0, 1, 1], 18), ([1, -1, -2, 1, 1, 0, 1], 9), ([1, -1, -1, 0, 0, 0, 2], -18), ([1, -1, -1, 1, -1, 0, 2], 18), ([1, -1, -1, 1, -1, 1, 1], -9), ([1, -1, -1, 1, 0, -1, 2], 18), ([1, -1, -1, 1, 1, -1, 1], -9), ([1, -1, -1, 2, -1, 0, 1], 9), ([1, -1, -1, 2, 0, -1, 1], 9), ([1, -1, 0, 0, 0, 0, 1], 18), ([1, -1, 0, 1, -1, 0, 1], 9), ([1, -1, 0, 1, 0, -1, 1], -9), ([1, -1, 0, 1, 0, 0, 0], 9), ([1, 0, -2, 1, 0, 0, 1], -9), ([1, 0, -1, 0, 0, 0, 1], 18), ([1, 0, -1, 1, -1, 0, 1], -9), ([1, 0, -1, 1, 0, -1, 1], 9), ([1, 0, -1, 1, 0, 0, 0], 9)]

def combined14 : Sparse := combined14_part0 ++ combined14_part1

def combined15 : Sparse := [([0, -2, -1, 1, 0, 0, 2], -18), ([0, -2, -1, 2, 0, 0, 1], -18), ([0, -1, -2, 1, 0, 0, 2], -18), ([0, -1, -2, 2, 0, 0, 1], -18), ([0, -1, -1, 0, 0, 1, 1], -18), ([0, -1, -1, 0, 1, 0, 1], -18), ([0, -1, -1, 1, 0, 1, 0], -18), ([0, -1, -1, 1, 1, 0, 0], -18), ([0, -1, 0, 1, -1, 0, 1], -18), ([0, -1, 0, 1, 0, -1, 1], -18), ([0, 0, -1, 1, -1, 0, 1], -18), ([0, 0, -1, 1, 0, -1, 1], -18), ([1, -2, -1, 1, 0, 1, 1], 18), ([1, -2, -1, 1, 1, 0, 1], 18), ([1, -1, -2, 1, 0, 1, 1], 18), ([1, -1, -2, 1, 1, 0, 1], 18), ([1, -1, -1, 1, -1, 0, 2], 18), ([1, -1, -1, 1, 0, -1, 2], 18), ([1, -1, -1, 2, -1, 0, 1], 18), ([1, -1, -1, 2, 0, -1, 1], 18), ([1, -1, 0, 0, 0, 0, 1], 18), ([1, -1, 0, 1, 0, 0, 0], 18), ([1, 0, -1, 0, 0, 0, 1], 18), ([1, 0, -1, 1, 0, 0, 0], 18)]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined16_part0 : Sparse := [([0, -2, -1, 1, 0, 2, 0], -36), ([0, -2, -1, 2, 0, 1, 0], 36), ([0, -2, 0, 1, 0, 1, 0], -18), ([0, -1, -2, 1, 0, 1, 1], 9), ([0, -1, -2, 2, 0, 1, 0], -27), ([0, -1, -1, 0, 0, 1, 1], -27), ([0, -1, -1, 0, 1, 1, 0], 9), ([0, -1, -1, 1, -1, 1, 1], -27), ([0, -1, -1, 1, -1, 2, 0], 9), ([0, -1, -1, 1, 0, 0, 1], 27), ([0, -1, -1, 1, 0, 2, -1], 9), ([0, -1, -1, 1, 1, 0, 0], -27), ([0, -1, -1, 2, -1, 1, 0], -9), ([0, -1, -1, 2, 0, 0, 0], -27), ([0, -1, -1, 2, 0, 1, -1], 9), ([0, -1, 0, 1, -1, 1, 0], 36), ([0, -1, 0, 1, 0, 1, -1], -36), ([0, 0, -1, 1, -1, 1, 0], -27), ([0, 0, -1, 1, 0, 0, 0], 9), ([1, -2, -1, 2, 0, 1, 0], 36), ([1, -2, 0, 1, 0, 1, 0], -18), ([1, -1, -2, 1, 0, 2, 0], -27), ([1, -1, -2, 1, 1, 1, 0], 9), ([1, -1, -1, 0, 0, 1, 1], 9)]

def combined16_part1 : Sparse := [([1, -1, -1, 0, 0, 2, 0], 27), ([1, -1, -1, 0, 1, 1, 0], -27), ([1, -1, -1, 1, -1, 1, 1], -27), ([1, -1, -1, 1, -1, 2, 0], 9), ([1, -1, -1, 1, 0, 0, 1], 36), ([1, -1, -1, 1, 0, 2, -1], 9), ([1, -1, -1, 1, 1, 0, 0], 9), ([1, -1, -1, 1, 1, 1, -1], 27), ([1, -1, -1, 2, 0, 0, 0], -27), ([1, -1, -1, 2, 0, 1, -1], 9), ([1, -1, 0, 1, -1, 1, 0], 36), ([1, 0, -2, 1, 0, 1, 0], 36), ([1, 0, -1, 0, 0, 1, 0], 9), ([1, 0, -1, 1, 0, 1, -1], -27)]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined100_part0 : Sparse := [([0, -2, 1, 0, 1, 0, 0], -18), ([0, -2, 1, 0, 2, -1, 0], 36), ([0, -2, 2, 0, 1, -1, 0], -36), ([0, -1, 0, 0, 1, -1, 1], 27), ([0, -1, 0, 0, 2, -1, 0], -27), ([0, -1, 0, 1, 1, -1, 0], -27), ([0, -1, 1, -1, 1, -1, 1], -27), ([0, -1, 1, -1, 1, 0, 0], 36), ([0, -1, 1, -1, 2, -1, 0], -9), ([0, -1, 1, 0, 0, -1, 1], -27), ([0, -1, 1, 0, 1, -2, 1], 9), ([0, -1, 1, 0, 1, 0, -1], -36), ([0, -1, 1, 0, 2, -2, 0], -27), ([0, -1, 1, 0, 2, -1, -1], 9), ([0, -1, 1, 1, 0, -1, 0], 9), ([0, -1, 2, -1, 1, -1, 0], 9), ([0, -1, 2, 0, 1, -1, -1], 9), ([0, 0, 0, 0, 1, -1, 0], 9), ([0, 0, 1, -1, 1, -1, 0], -27), ([1, -2, 1, 0, 1, 0, 0], -18), ([1, -2, 1, 0, 2, -1, 0], 36), ([1, -1, 0, 0, 1, -1, 1], 36), ([1, -1, 0, 0, 2, -1, 0], -27), ([1, -1, 0, 1, 1, -1, 0], 9)]

def combined100_part1 : Sparse := [([1, -1, 1, -1, 1, -1, 1], -27), ([1, -1, 1, -1, 1, 0, 0], 36), ([1, -1, 1, 0, 0, -1, 1], 9), ([1, -1, 1, 0, 2, -1, -1], 9), ([1, -1, 1, 1, 0, -1, 0], -27), ([1, -1, 1, 1, 1, -2, 0], 9), ([1, -1, 1, 1, 1, -1, -1], 27), ([1, -1, 2, -1, 1, -1, 0], 9), ([1, -1, 2, 0, 0, -1, 0], 27), ([1, -1, 2, 0, 1, -2, 0], -27), ([1, -1, 2, 0, 1, -1, -1], 9), ([1, 0, 1, 0, 0, -1, 0], 9), ([1, 0, 1, 0, 1, -2, 0], 36), ([1, 0, 1, 0, 1, -1, -1], -27)]

def combined100 : Sparse := combined100_part0 ++ combined100_part1

def combined101_part0 : Sparse := [([0, -2, 1, 0, 1, 0, 0], -9), ([0, -2, 1, 0, 2, -1, 0], 27), ([0, -2, 2, 0, 1, -1, 0], -36), ([0, -1, 0, 0, 1, -1, 1], 18), ([0, -1, 0, 0, 1, 0, 0], -9), ([0, -1, 0, 0, 2, -1, 0], -27), ([0, -1, 0, 1, 1, -1, 0], -18), ([0, -1, 1, -1, 1, -1, 1], -18), ([0, -1, 1, -1, 1, 0, 0], 36), ([0, -1, 1, -1, 2, -1, 0], -18), ([0, -1, 1, 0, 0, -1, 1], -27), ([0, -1, 1, 0, 1, -2, 1], 9), ([0, -1, 1, 0, 1, 0, -1], -36), ([0, -1, 1, 0, 2, -2, 0], -18), ([0, -1, 1, 0, 2, -1, -1], 18), ([0, -1, 1, 1, 0, -1, 0], 9), ([0, -1, 1, 1, 1, -2, 0], -9), ([0, -1, 2, -1, 1, -1, 0], 9), ([0, -1, 2, 0, 1, -1, -1], 9), ([0, 0, 0, 0, 1, -1, 0], 18), ([0, 0, 1, -1, 1, -1, 0], -27), ([0, 0, 1, 0, 1, -1, -1], -9), ([1, -2, 1, 0, 1, -1, 1], -9), ([1, -2, 1, 0, 1, 0, 0], -9)]

def combined101_part1 : Sparse := [([1, -2, 1, 0, 2, -1, 0], 27), ([1, -2, 1, 1, 1, -1, 0], -9), ([1, -1, 0, 0, 1, -1, 1], 27), ([1, -1, 0, 0, 1, 0, 0], -9), ([1, -1, 0, 0, 2, -1, 0], -27), ([1, -1, 0, 1, 1, -1, 0], 9), ([1, -1, 1, -1, 1, -1, 1], -18), ([1, -1, 1, -1, 1, 0, 0], 27), ([1, -1, 1, -1, 2, -1, 0], -9), ([1, -1, 1, 0, 0, -1, 1], 9), ([1, -1, 1, 0, 1, -2, 1], -9), ([1, -1, 1, 0, 1, 0, -1], -9), ([1, -1, 1, 0, 2, -1, -1], 9), ([1, -1, 1, 1, 0, -1, 0], -27), ([1, -1, 1, 1, 1, -2, 0], 9), ([1, -1, 1, 1, 1, -1, -1], 18), ([1, -1, 2, -1, 1, -1, 0], 9), ([1, -1, 2, 0, 0, -1, 0], 9), ([1, -1, 2, 0, 1, -2, 0], -27), ([1, -1, 2, 0, 1, -1, -1], 9), ([1, 0, 1, -1, 1, -1, 0], -9), ([1, 0, 1, 0, 0, -1, 0], 9), ([1, 0, 1, 0, 1, -2, 0], 27), ([1, 0, 1, 0, 1, -1, -1], -27)]

def combined101 : Sparse := combined101_part0 ++ combined101_part1

def combined102_part0 : Sparse := [([0, -2, 1, 0, 1, -1, 1], -9), ([0, -2, 1, 0, 2, -1, 0], 27), ([0, -2, 1, 1, 1, -1, 0], 9), ([0, -2, 2, 0, 1, -1, 0], -27), ([0, -1, 0, 0, 1, -1, 1], 18), ([0, -1, 0, 0, 1, 0, 0], -9), ([0, -1, 0, 0, 2, -1, 0], -9), ([0, -1, 0, 1, 1, -1, 0], -18), ([0, -1, 1, -1, 1, -1, 1], -9), ([0, -1, 1, -1, 1, 0, 0], 27), ([0, -1, 1, -1, 2, -1, 0], -18), ([0, -1, 1, 0, 0, -1, 1], -18), ([0, -1, 1, 0, 0, 0, 0], 9), ([0, -1, 1, 0, 1, -2, 1], 18), ([0, -1, 1, 0, 1, 0, -1], -27), ([0, -1, 1, 0, 2, -2, 0], -18), ([0, -1, 1, 0, 2, -1, -1], 18), ([0, -1, 1, 1, 0, -1, 0], 9), ([0, -1, 2, -1, 1, -1, 0], 18), ([0, -1, 2, 0, 1, -1, -1], 9), ([0, 0, 0, 0, 1, -1, 0], 18), ([0, 0, 1, -1, 1, -1, 0], -18), ([1, -2, 1, 0, 1, -1, 1], -9), ([1, -2, 1, 0, 2, -1, 0], 27)]

def combined102_part1 : Sparse := [([1, -1, 0, 0, 1, -1, 1], 27), ([1, -1, 0, 0, 1, 0, 0], -9), ([1, -1, 0, 0, 2, -1, 0], -9), ([1, -1, 0, 1, 1, -1, 0], 9), ([1, -1, 1, -1, 1, -1, 1], -9), ([1, -1, 1, -1, 1, 0, 0], 27), ([1, -1, 1, -1, 2, -1, 0], -9), ([1, -1, 1, 0, 0, -1, 1], 9), ([1, -1, 1, 0, 2, -1, -1], 9), ([1, -1, 1, 1, 0, -1, 0], -18), ([1, -1, 1, 1, 1, -2, 0], 18), ([1, -1, 1, 1, 1, -1, -1], 9), ([1, -1, 2, -1, 1, -1, 0], 9), ([1, -1, 2, 0, 0, -1, 0], 9), ([1, -1, 2, 0, 1, -2, 0], -18), ([1, -1, 2, 0, 1, -1, -1], 18), ([1, 0, 1, 0, 0, -1, 0], 18), ([1, 0, 1, 0, 1, -2, 0], 18), ([1, 0, 1, 0, 1, -1, -1], -18)]

def combined102 : Sparse := combined102_part0 ++ combined102_part1

def combined103_part0 : Sparse := [([0, -2, 1, 0, 1, -1, 1], -18), ([0, -2, 1, 0, 2, -1, 0], 18), ([0, -2, 1, 1, 1, -1, 0], 18), ([0, -2, 2, 0, 1, -1, 0], -18), ([0, -1, 0, 0, 1, -1, 1], 18), ([0, -1, 0, 0, 1, 0, 0], -18), ([0, -1, 0, 1, 1, -1, 0], -18), ([0, -1, 1, -1, 1, 0, 0], 18), ([0, -1, 1, -1, 2, -1, 0], -18), ([0, -1, 1, 0, 0, -1, 1], -18), ([0, -1, 1, 0, 0, 0, 0], 18), ([0, -1, 1, 0, 1, -2, 1], 18), ([0, -1, 1, 0, 1, 0, -1], -18), ([0, -1, 1, 0, 2, -2, 0], -18), ([0, -1, 1, 0, 2, -1, -1], 18), ([0, -1, 2, -1, 1, -1, 0], 18), ([0, 0, 0, 0, 1, -1, 0], 18), ([0, 0, 1, -1, 1, -1, 0], -18), ([1, -2, 1, 0, 1, -1, 1], -18), ([1, -2, 1, 0, 2, -1, 0], 18), ([1, -1, 0, 0, 1, -1, 1], 18), ([1, -1, 0, 0, 1, 0, 0], -18), ([1, -1, 1, -1, 1, 0, 0], 18), ([1, -1, 1, -1, 2, -1, 0], -18)]

def combined103_part1 : Sparse := [([1, -1, 1, 1, 0, -1, 0], -18), ([1, -1, 1, 1, 1, -2, 0], 18), ([1, -1, 2, 0, 1, -2, 0], -18), ([1, -1, 2, 0, 1, -1, -1], 18), ([1, 0, 1, 0, 0, -1, 0], 18), ([1, 0, 1, 0, 1, -1, -1], -18)]

def combined103 : Sparse := combined103_part0 ++ combined103_part1

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined104_part0 : Sparse := [([0, -2, 1, 0, 1, 0, 0], -18), ([0, -2, 1, 0, 2, 0, -1], -36), ([0, -2, 2, 0, 1, 0, -1], 36), ([0, -1, 0, 0, 1, 1, -1], -27), ([0, -1, 0, 1, 1, 0, -1], 9), ([0, -1, 1, -1, 1, 0, 0], 36), ([0, -1, 1, -1, 1, 1, -1], -27), ([0, -1, 1, -1, 2, 0, -1], 9), ([0, -1, 1, 0, 0, 1, -1], 27), ([0, -1, 1, 0, 1, -1, 0], -36), ([0, -1, 1, 0, 1, 1, -2], 9), ([0, -1, 1, 0, 2, -1, -1], 9), ([0, -1, 1, 1, 0, 0, -1], -27), ([0, -1, 2, -1, 1, 0, -1], -9), ([0, -1, 2, 0, 0, 0, -1], -27), ([0, -1, 2, 0, 1, -1, -1], 9), ([0, -1, 2, 0, 1, 0, -2], -27), ([0, 0, 1, -1, 1, 0, -1], -27), ([0, 0, 1, 0, 0, 0, -1], 9), ([1, -2, 1, 0, 1, 0, 0], -18), ([1, -2, 2, 0, 1, 0, -1], 36), ([1, -1, 0, 0, 1, 1, -1], 9), ([1, -1, 0, 0, 2, 0, -1], 27), ([1, -1, 0, 1, 1, 0, -1], -27)]

def combined104_part1 : Sparse := [([1, -1, 1, -1, 1, 0, 0], 36), ([1, -1, 1, -1, 1, 1, -1], -27), ([1, -1, 1, -1, 2, 0, -1], 9), ([1, -1, 1, 0, 0, 1, -1], 36), ([1, -1, 1, 0, 2, -1, -1], 9), ([1, -1, 1, 0, 2, 0, -2], -27), ([1, -1, 1, 1, 0, 0, -1], 9), ([1, -1, 1, 1, 1, -1, -1], 27), ([1, -1, 1, 1, 1, 0, -2], 9), ([1, -1, 2, 0, 0, 0, -1], -27), ([1, -1, 2, 0, 1, -1, -1], 9), ([1, 0, 0, 0, 1, 0, -1], 9), ([1, 0, 1, 0, 1, -1, -1], -27), ([1, 0, 1, 0, 1, 0, -2], 36)]

def combined104 : Sparse := combined104_part0 ++ combined104_part1

def combined105_part0 : Sparse := [([0, -2, 1, 0, 1, 0, 0], -9), ([0, -2, 1, 0, 1, 1, -1], -9), ([0, -2, 1, 0, 2, 0, -1], -27), ([0, -2, 1, 1, 1, 0, -1], 9), ([0, -2, 2, 0, 1, 0, -1], 36), ([0, -1, 0, 0, 1, 0, 0], 9), ([0, -1, 0, 0, 1, 1, -1], -18), ([0, -1, 0, 1, 1, 0, -1], 9), ([0, -1, 1, -1, 1, 0, 0], 27), ([0, -1, 1, -1, 1, 1, -1], -18), ([0, -1, 1, -1, 2, 0, -1], 18), ([0, -1, 1, 0, 0, 1, -1], 27), ([0, -1, 1, 0, 1, -1, 0], -27), ([0, -1, 1, 0, 1, 1, -2], 18), ([0, -1, 1, 0, 2, -1, -1], 9), ([0, -1, 1, 1, 0, 0, -1], -27), ([0, -1, 1, 1, 1, 0, -2], 9), ([0, -1, 2, -1, 1, 0, -1], -9), ([0, -1, 2, 0, 0, 0, -1], -9), ([0, -1, 2, 0, 1, -1, -1], 9), ([0, -1, 2, 0, 1, 0, -2], -27), ([0, 0, 1, -1, 1, 0, -1], -18), ([0, 0, 1, 0, 0, 0, -1], 9), ([0, 0, 1, 0, 1, -1, -1], 9)]

def combined105_part1 : Sparse := [([1, -2, 1, 0, 1, 0, 0], -9), ([1, -2, 1, 1, 1, 0, -1], 9), ([1, -2, 2, 0, 1, 0, -1], 36), ([1, -1, 0, 0, 1, 1, -1], 9), ([1, -1, 0, 0, 2, 0, -1], 27), ([1, -1, 0, 1, 1, 0, -1], -18), ([1, -1, 1, -1, 1, 0, 0], 36), ([1, -1, 1, -1, 1, 1, -1], -18), ([1, -1, 1, -1, 2, 0, -1], 9), ([1, -1, 1, 0, 0, 1, -1], 36), ([1, -1, 1, 0, 1, -1, 0], 9), ([1, -1, 1, 0, 1, 1, -2], 9), ([1, -1, 1, 0, 2, -1, -1], 18), ([1, -1, 1, 0, 2, 0, -2], -18), ([1, -1, 1, 1, 0, 0, -1], 9), ([1, -1, 1, 1, 1, -1, -1], 18), ([1, -1, 1, 1, 1, 0, -2], 18), ([1, -1, 2, 0, 0, 0, -1], -9), ([1, -1, 2, 0, 1, -1, -1], 9), ([1, 0, 0, 0, 1, 0, -1], 18), ([1, 0, 1, -1, 1, 0, -1], 9), ([1, 0, 1, 0, 1, -1, -1], -18), ([1, 0, 1, 0, 1, 0, -2], 27)]

def combined105 : Sparse := combined105_part0 ++ combined105_part1

def combined106_part0 : Sparse := [([0, -2, 1, 0, 1, 1, -1], -9), ([0, -2, 1, 0, 2, 0, -1], -27), ([0, -2, 1, 1, 1, 0, -1], 9), ([0, -2, 2, 0, 1, 0, -1], 27), ([0, -1, 0, 0, 1, 0, 0], 9), ([0, -1, 0, 0, 1, 1, -1], -18), ([0, -1, 0, 1, 1, 0, -1], 9), ([0, -1, 1, -1, 1, 0, 0], 27), ([0, -1, 1, -1, 1, 1, -1], -9), ([0, -1, 1, -1, 2, 0, -1], 18), ([0, -1, 1, 0, 0, 0, 0], -9), ([0, -1, 1, 0, 0, 1, -1], 18), ([0, -1, 1, 0, 1, -1, 0], -27), ([0, -1, 1, 0, 1, 1, -2], 18), ([0, -1, 1, 0, 2, -1, -1], 9), ([0, -1, 1, 1, 0, 0, -1], -18), ([0, -1, 2, -1, 1, 0, -1], -18), ([0, -1, 2, 0, 0, 0, -1], -9), ([0, -1, 2, 0, 1, -1, -1], 18), ([0, -1, 2, 0, 1, 0, -2], -18), ([0, 0, 1, -1, 1, 0, -1], -18), ([0, 0, 1, 0, 0, 0, -1], 18), ([1, -2, 1, 0, 1, 1, -1], -9), ([1, -2, 2, 0, 1, 0, -1], 27)]

def combined106_part1 : Sparse := [([1, -1, 0, 0, 1, 1, -1], 9), ([1, -1, 0, 0, 2, 0, -1], 9), ([1, -1, 0, 1, 1, 0, -1], -18), ([1, -1, 1, -1, 1, 0, 0], 27), ([1, -1, 1, -1, 1, 1, -1], -9), ([1, -1, 1, -1, 2, 0, -1], 9), ([1, -1, 1, 0, 0, 0, 0], -9), ([1, -1, 1, 0, 0, 1, -1], 27), ([1, -1, 1, 0, 2, -1, -1], 18), ([1, -1, 1, 0, 2, 0, -2], -18), ([1, -1, 1, 1, 0, 0, -1], 9), ([1, -1, 1, 1, 1, -1, -1], 9), ([1, -1, 1, 1, 1, 0, -2], 18), ([1, -1, 2, -1, 1, 0, -1], -9), ([1, -1, 2, 0, 0, 0, -1], -9), ([1, -1, 2, 0, 1, -1, -1], 9), ([1, 0, 0, 0, 1, 0, -1], 18), ([1, 0, 1, 0, 1, -1, -1], -18), ([1, 0, 1, 0, 1, 0, -2], 18)]

def combined106 : Sparse := combined106_part0 ++ combined106_part1

def combined107_part0 : Sparse := [([0, -2, 1, 0, 1, 1, -1], -18), ([0, -2, 1, 0, 2, 0, -1], -18), ([0, -2, 1, 1, 1, 0, -1], 18), ([0, -2, 2, 0, 1, 0, -1], 18), ([0, -1, 0, 0, 1, 0, 0], 18), ([0, -1, 0, 0, 1, 1, -1], -18), ([0, -1, 1, -1, 1, 0, 0], 18), ([0, -1, 1, -1, 2, 0, -1], 18), ([0, -1, 1, 0, 0, 0, 0], -18), ([0, -1, 1, 0, 0, 1, -1], 18), ([0, -1, 1, 0, 1, -1, 0], -18), ([0, -1, 1, 0, 1, 1, -2], 18), ([0, -1, 1, 1, 0, 0, -1], -18), ([0, -1, 2, -1, 1, 0, -1], -18), ([0, -1, 2, 0, 1, -1, -1], 18), ([0, -1, 2, 0, 1, 0, -2], -18), ([0, 0, 1, -1, 1, 0, -1], -18), ([0, 0, 1, 0, 0, 0, -1], 18), ([1, -2, 1, 0, 1, 1, -1], -18), ([1, -2, 2, 0, 1, 0, -1], 18), ([1, -1, 0, 1, 1, 0, -1], -18), ([1, -1, 1, -1, 1, 0, 0], 18), ([1, -1, 1, 0, 0, 0, 0], -18), ([1, -1, 1, 0, 0, 1, -1], 18)]

def combined107_part1 : Sparse := [([1, -1, 1, 0, 2, -1, -1], 18), ([1, -1, 1, 0, 2, 0, -2], -18), ([1, -1, 1, 1, 1, 0, -2], 18), ([1, -1, 2, -1, 1, 0, -1], -18), ([1, 0, 0, 0, 1, 0, -1], 18), ([1, 0, 1, 0, 1, -1, -1], -18)]

def combined107 : Sparse := combined107_part0 ++ combined107_part1

def combined108_part0 : Sparse := [([0, -2, 1, 2, -1, 0, 0], -36), ([0, -1, 0, 1, -1, 0, 1], -36), ([0, -1, 0, 1, -1, 1, 0], 36), ([0, -1, 0, 2, -1, 0, 0], -27), ([0, -1, 1, 0, -1, 0, 1], -9), ([0, -1, 1, 0, -1, 1, 0], -36), ([0, -1, 1, 1, -2, 0, 1], 9), ([0, -1, 1, 1, -2, 1, 0], -9), ([0, -1, 1, 1, -1, 1, -1], -27), ([0, -1, 1, 1, 0, 0, -1], -36), ([0, -1, 1, 2, -2, 0, 0], 27), ([0, -1, 2, 1, -2, 0, 0], -27), ([0, -1, 2, 1, -1, -1, 0], -9), ([0, 0, 0, 1, -1, 0, 0], -9), ([0, 0, 1, 0, -1, 0, 0], 9), ([0, 0, 1, 1, -2, 0, 0], -36), ([0, 0, 1, 1, -1, -1, 0], -27), ([0, 0, 1, 1, -1, 0, -1], 27), ([1, -2, 1, 1, 0, 0, 0], 18), ([1, -2, 2, 1, -1, 0, 0], -36), ([1, -1, 0, 1, -1, 0, 1], -9), ([1, -1, 0, 1, -1, 1, 0], 27), ([1, -1, 0, 2, -1, 0, 0], -27), ([1, -1, 1, 0, -1, 0, 1], -36)]

def combined108_part1 : Sparse := [([1, -1, 1, 0, -1, 1, 0], -9), ([1, -1, 1, 1, -2, 1, 0], -9), ([1, -1, 1, 1, -1, -1, 1], 27), ([1, -1, 1, 1, -1, 1, -1], -27), ([1, -1, 1, 1, 0, -1, 0], -36), ([1, -1, 1, 2, -2, 0, 0], 27), ([1, -1, 1, 2, -1, -1, 0], -9), ([1, -1, 1, 2, -1, 0, -1], -9), ([1, -1, 2, 0, -1, 0, 0], 27), ([1, -1, 2, 1, -1, 0, -1], -9), ([1, 0, 0, 1, -1, 0, 0], -9), ([1, 0, 1, 1, -2, 0, 0], -36), ([1, 0, 1, 1, -1, 0, -1], 27)]

def combined108 : Sparse := combined108_part0 ++ combined108_part1

def combined109_part0 : Sparse := [([0, -2, 1, 1, -1, 0, 1], -9), ([0, -2, 1, 2, -1, 0, 0], -27), ([0, -1, 0, 1, -1, 0, 1], -27), ([0, -1, 0, 1, -1, 1, 0], 27), ([0, -1, 0, 1, 0, 0, 0], 9), ([0, -1, 0, 2, -1, 0, 0], -27), ([0, -1, 1, 0, -1, 0, 1], -9), ([0, -1, 1, 0, -1, 1, 0], -36), ([0, -1, 1, 1, -2, 0, 1], 9), ([0, -1, 1, 1, -2, 1, 0], -9), ([0, -1, 1, 1, -1, 1, -1], -18), ([0, -1, 1, 1, 0, -1, 0], -9), ([0, -1, 1, 1, 0, 0, -1], -36), ([0, -1, 1, 2, -2, 0, 0], 18), ([0, -1, 1, 2, -1, -1, 0], 9), ([0, -1, 1, 2, -1, 0, -1], -9), ([0, -1, 2, 1, -2, 0, 0], -27), ([0, -1, 2, 1, -1, -1, 0], -9), ([0, 0, 0, 1, -1, 0, 0], -18), ([0, 0, 1, 0, -1, 0, 0], 9), ([0, 0, 1, 1, -2, 0, 0], -27), ([0, 0, 1, 1, -1, -1, 0], -27), ([0, 0, 1, 1, -1, 0, -1], 27), ([1, -2, 1, 1, -1, 1, 0], -9)]

def combined109_part1 : Sparse := [([1, -2, 1, 1, 0, 0, 0], 9), ([1, -2, 2, 1, -1, 0, 0], -36), ([1, -1, 0, 1, -1, 0, 1], -9), ([1, -1, 0, 1, -1, 1, 0], 18), ([1, -1, 0, 2, -1, 0, 0], -27), ([1, -1, 1, 0, -1, 0, 1], -36), ([1, -1, 1, 0, -1, 1, 0], -9), ([1, -1, 1, 1, -2, 0, 1], -9), ([1, -1, 1, 1, -2, 1, 0], -18), ([1, -1, 1, 1, -1, -1, 1], 18), ([1, -1, 1, 1, -1, 1, -1], -18), ([1, -1, 1, 1, 0, -1, 0], -36), ([1, -1, 1, 1, 0, 0, -1], -9), ([1, -1, 1, 2, -2, 0, 0], 18), ([1, -1, 1, 2, -1, -1, 0], -9), ([1, -1, 1, 2, -1, 0, -1], -18), ([1, -1, 2, 0, -1, 0, 0], 9), ([1, -1, 2, 1, -1, 0, -1], -9), ([1, 0, 0, 1, -1, 0, 0], -18), ([1, 0, 1, 1, -2, 0, 0], -27), ([1, 0, 1, 1, -1, -1, 0], -9), ([1, 0, 1, 1, -1, 0, -1], 18)]

def combined109 : Sparse := combined109_part0 ++ combined109_part1

def combined110_part0 : Sparse := [([0, -2, 1, 1, -1, 1, 0], 9), ([0, -2, 1, 2, -1, 0, 0], -27), ([0, -1, 0, 1, -1, 0, 1], -27), ([0, -1, 0, 1, -1, 1, 0], 27), ([0, -1, 0, 1, 0, 0, 0], 9), ([0, -1, 0, 2, -1, 0, 0], -9), ([0, -1, 1, 0, -1, 0, 1], -9), ([0, -1, 1, 0, -1, 1, 0], -27), ([0, -1, 1, 1, -2, 0, 1], 18), ([0, -1, 1, 1, -2, 1, 0], -18), ([0, -1, 1, 1, -1, 1, -1], -9), ([0, -1, 1, 1, 0, 0, -1], -27), ([0, -1, 1, 2, -2, 0, 0], 18), ([0, -1, 1, 2, -1, -1, 0], 9), ([0, -1, 1, 2, -1, 0, -1], -9), ([0, -1, 2, 1, -2, 0, 0], -18), ([0, -1, 2, 1, -1, -1, 0], -9), ([0, -1, 2, 1, -1, 0, -1], 9), ([0, 0, 0, 1, -1, 0, 0], -18), ([0, 0, 1, 0, -1, 0, 0], 18), ([0, 0, 1, 1, -2, 0, 0], -18), ([0, 0, 1, 1, -1, -1, 0], -18), ([0, 0, 1, 1, -1, 0, -1], 18), ([1, -2, 1, 1, -1, 0, 1], 9)]

def combined110_part1 : Sparse := [([1, -2, 2, 1, -1, 0, 0], -27), ([1, -1, 0, 1, -1, 0, 1], -9), ([1, -1, 0, 1, -1, 1, 0], 18), ([1, -1, 0, 2, -1, 0, 0], -9), ([1, -1, 1, 0, -1, 0, 1], -27), ([1, -1, 1, 0, -1, 1, 0], -9), ([1, -1, 1, 0, 0, 0, 0], 9), ([1, -1, 1, 1, -2, 1, 0], -18), ([1, -1, 1, 1, -1, -1, 1], 9), ([1, -1, 1, 1, -1, 1, -1], -9), ([1, -1, 1, 1, 0, -1, 0], -27), ([1, -1, 1, 2, -2, 0, 0], 18), ([1, -1, 1, 2, -1, -1, 0], -9), ([1, -1, 1, 2, -1, 0, -1], -18), ([1, -1, 2, 0, -1, 0, 0], 9), ([1, -1, 2, 1, -1, -1, 0], 9), ([1, -1, 2, 1, -1, 0, -1], -9), ([1, 0, 0, 1, -1, 0, 0], -18), ([1, 0, 1, 1, -2, 0, 0], -18), ([1, 0, 1, 1, -1, 0, -1], 18)]

def combined110 : Sparse := combined110_part0 ++ combined110_part1

def combined111_part0 : Sparse := [([0, -2, 1, 1, -1, 1, 0], 18), ([0, -2, 1, 2, -1, 0, 0], -18), ([0, -1, 0, 1, -1, 0, 1], -18), ([0, -1, 0, 1, -1, 1, 0], 18), ([0, -1, 0, 1, 0, 0, 0], 18), ([0, -1, 1, 0, -1, 1, 0], -18), ([0, -1, 1, 1, -2, 0, 1], 18), ([0, -1, 1, 1, -2, 1, 0], -18), ([0, -1, 1, 1, 0, 0, -1], -18), ([0, -1, 1, 2, -2, 0, 0], 18), ([0, -1, 1, 2, -1, -1, 0], 18), ([0, -1, 1, 2, -1, 0, -1], -18), ([0, -1, 2, 1, -2, 0, 0], -18), ([0, -1, 2, 1, -1, 0, -1], 18), ([0, 0, 0, 1, -1, 0, 0], -18), ([0, 0, 1, 0, -1, 0, 0], 18), ([0, 0, 1, 1, -1, -1, 0], -18), ([0, 0, 1, 1, -1, 0, -1], 18), ([1, -2, 1, 1, -1, 0, 1], 18), ([1, -2, 2, 1, -1, 0, 0], -18), ([1, -1, 0, 1, -1, 1, 0], 18), ([1, -1, 1, 0, -1, 0, 1], -18), ([1, -1, 1, 0, 0, 0, 0], 18), ([1, -1, 1, 1, -2, 1, 0], -18)]

def combined111_part1 : Sparse := [([1, -1, 1, 1, 0, -1, 0], -18), ([1, -1, 1, 2, -2, 0, 0], 18), ([1, -1, 1, 2, -1, 0, -1], -18), ([1, -1, 2, 1, -1, -1, 0], 18), ([1, 0, 0, 1, -1, 0, 0], -18), ([1, 0, 1, 1, -1, 0, -1], 18)]

def combined111 : Sparse := combined111_part0 ++ combined111_part1

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined112_part0 : Sparse := [([0, -2, 1, 2, 0, -1, 0], -36), ([0, -2, 2, 1, 0, -1, 0], -36), ([0, -1, 0, 1, 0, -1, 1], -27), ([0, -1, 0, 1, 1, -1, 0], -36), ([0, -1, 1, 0, 0, -1, 1], -36), ([0, -1, 1, 0, 1, -1, 0], -27), ([0, -1, 1, 1, -1, 0, 0], -36), ([0, -1, 1, 1, 0, -2, 1], -9), ([0, -1, 1, 1, 0, 0, -1], -36), ([0, -1, 1, 1, 1, -2, 0], -9), ([0, -1, 1, 2, 0, -2, 0], -27), ([0, -1, 1, 2, 0, -1, -1], -9), ([0, -1, 2, 1, -1, -1, 0], -9), ([0, -1, 2, 1, 0, -2, 0], -27), ([0, 0, 0, 1, 0, -1, 0], -9), ([0, 0, 1, 0, 0, -1, 0], -9), ([0, 0, 1, 1, -1, -1, 0], -27), ([0, 0, 1, 1, 0, -1, -1], -27), ([1, -2, 1, 1, 0, 0, 0], 18), ([1, -1, 0, 1, 0, -1, 1], 9), ([1, -1, 0, 1, 1, -1, 0], -9), ([1, -1, 0, 2, 0, -1, 0], 27), ([1, -1, 1, 0, 0, -1, 1], -9), ([1, -1, 1, 0, 1, -1, 0], 9)]

def combined112_part1 : Sparse := [([1, -1, 1, 1, -1, -1, 1], 27), ([1, -1, 1, 1, 0, -2, 1], -9), ([1, -1, 1, 1, 1, -2, 0], -9), ([1, -1, 1, 1, 1, -1, -1], 27), ([1, -1, 1, 2, -1, -1, 0], -9), ([1, -1, 2, 0, 0, -1, 0], 27), ([1, -1, 2, 1, 0, -1, -1], -9), ([1, 0, 0, 1, 0, -1, 0], -9), ([1, 0, 1, 0, 0, -1, 0], -9), ([1, 0, 1, 1, 0, -2, 0], 36)]

def combined112 : Sparse := combined112_part0 ++ combined112_part1

def combined113_part0 : Sparse := [([0, -2, 1, 1, 0, -1, 1], -9), ([0, -2, 1, 2, 0, -1, 0], -27), ([0, -2, 2, 1, 0, -1, 0], -36), ([0, -1, 0, 1, 0, -1, 1], -18), ([0, -1, 0, 1, 0, 0, 0], -9), ([0, -1, 0, 1, 1, -1, 0], -27), ([0, -1, 1, 0, 0, -1, 1], -36), ([0, -1, 1, 0, 1, -1, 0], -27), ([0, -1, 1, 1, -1, 0, 0], -36), ([0, -1, 1, 1, 0, -2, 1], -9), ([0, -1, 1, 1, 0, 0, -1], -27), ([0, -1, 1, 1, 1, -2, 0], -18), ([0, -1, 1, 2, -1, -1, 0], -9), ([0, -1, 1, 2, 0, -2, 0], -18), ([0, -1, 1, 2, 0, -1, -1], -18), ([0, -1, 2, 1, -1, -1, 0], -9), ([0, -1, 2, 1, 0, -2, 0], -27), ([0, 0, 0, 1, 0, -1, 0], -18), ([0, 0, 1, 0, 0, -1, 0], -9), ([0, 0, 1, 1, -1, -1, 0], -18), ([0, 0, 1, 1, 0, -1, -1], -27), ([1, -2, 1, 1, 0, 0, 0], 9), ([1, -2, 1, 1, 1, -1, 0], -9), ([1, -1, 0, 1, 0, -1, 1], 9)]

def combined113_part1 : Sparse := [([1, -1, 0, 1, 0, 0, 0], -9), ([1, -1, 0, 1, 1, -1, 0], -9), ([1, -1, 0, 2, 0, -1, 0], 27), ([1, -1, 1, 0, 0, -1, 1], -9), ([1, -1, 1, 0, 1, -1, 0], 9), ([1, -1, 1, 1, -1, -1, 1], 18), ([1, -1, 1, 1, -1, 0, 0], -9), ([1, -1, 1, 1, 0, -2, 1], -18), ([1, -1, 1, 1, 0, 0, -1], 9), ([1, -1, 1, 1, 1, -2, 0], -9), ([1, -1, 1, 1, 1, -1, -1], 18), ([1, -1, 1, 2, -1, -1, 0], -18), ([1, -1, 1, 2, 0, -1, -1], -9), ([1, -1, 2, 0, 0, -1, 0], 9), ([1, -1, 2, 1, 0, -1, -1], -9), ([1, 0, 0, 1, 0, -1, 0], -18), ([1, 0, 1, 0, 0, -1, 0], -9), ([1, 0, 1, 1, -1, -1, 0], 9), ([1, 0, 1, 1, 0, -2, 0], 27), ([1, 0, 1, 1, 0, -1, -1], -9)]

def combined113 : Sparse := combined113_part0 ++ combined113_part1

def combined114_part0 : Sparse := [([0, -2, 1, 1, 0, -1, 1], -9), ([0, -2, 1, 1, 1, -1, 0], -9), ([0, -2, 1, 2, 0, -1, 0], -27), ([0, -2, 2, 1, 0, -1, 0], -27), ([0, -1, 0, 1, 0, -1, 1], -18), ([0, -1, 0, 1, 0, 0, 0], -9), ([0, -1, 0, 1, 1, -1, 0], -27), ([0, -1, 1, 0, 0, -1, 1], -27), ([0, -1, 1, 0, 0, 0, 0], -9), ([0, -1, 1, 0, 1, -1, 0], -18), ([0, -1, 1, 1, -1, 0, 0], -27), ([0, -1, 1, 1, 0, -2, 1], -18), ([0, -1, 1, 1, 0, 0, -1], -27), ([0, -1, 1, 1, 1, -2, 0], -18), ([0, -1, 1, 2, -1, -1, 0], -9), ([0, -1, 1, 2, 0, -2, 0], -18), ([0, -1, 1, 2, 0, -1, -1], -18), ([0, -1, 2, 1, -1, -1, 0], -18), ([0, -1, 2, 1, 0, -2, 0], -18), ([0, -1, 2, 1, 0, -1, -1], -9), ([0, 0, 0, 1, 0, -1, 0], -18), ([0, 0, 1, 0, 0, -1, 0], -18), ([0, 0, 1, 1, -1, -1, 0], -18), ([0, 0, 1, 1, 0, -1, -1], -18)]

def combined114_part1 : Sparse := [([1, -2, 1, 1, 0, -1, 1], -9), ([1, -2, 1, 1, 1, -1, 0], -9), ([1, -1, 0, 1, 0, -1, 1], 9), ([1, -1, 0, 1, 0, 0, 0], -9), ([1, -1, 0, 1, 1, -1, 0], -9), ([1, -1, 0, 2, 0, -1, 0], 9), ([1, -1, 1, 0, 0, -1, 1], -9), ([1, -1, 1, 0, 0, 0, 0], -9), ([1, -1, 1, 0, 1, -1, 0], 9), ([1, -1, 1, 1, -1, -1, 1], 9), ([1, -1, 1, 1, 0, -2, 1], -18), ([1, -1, 1, 1, 1, -2, 0], -18), ([1, -1, 1, 1, 1, -1, -1], 9), ([1, -1, 1, 2, -1, -1, 0], -18), ([1, -1, 1, 2, 0, -1, -1], -9), ([1, -1, 2, 0, 0, -1, 0], 9), ([1, -1, 2, 1, -1, -1, 0], -9), ([1, -1, 2, 1, 0, -1, -1], -18), ([1, 0, 0, 1, 0, -1, 0], -18), ([1, 0, 1, 0, 0, -1, 0], -18), ([1, 0, 1, 1, 0, -2, 0], 18)]

def combined114 : Sparse := combined114_part0 ++ combined114_part1

def combined115_part0 : Sparse := [([0, -2, 1, 1, 0, -1, 1], -18), ([0, -2, 1, 1, 1, -1, 0], -18), ([0, -2, 1, 2, 0, -1, 0], -18), ([0, -2, 2, 1, 0, -1, 0], -18), ([0, -1, 0, 1, 0, -1, 1], -18), ([0, -1, 0, 1, 0, 0, 0], -18), ([0, -1, 0, 1, 1, -1, 0], -18), ([0, -1, 1, 0, 0, -1, 1], -18), ([0, -1, 1, 0, 0, 0, 0], -18), ([0, -1, 1, 0, 1, -1, 0], -18), ([0, -1, 1, 1, -1, 0, 0], -18), ([0, -1, 1, 1, 0, -2, 1], -18), ([0, -1, 1, 1, 0, 0, -1], -18), ([0, -1, 1, 1, 1, -2, 0], -18), ([0, -1, 1, 2, -1, -1, 0], -18), ([0, -1, 1, 2, 0, -2, 0], -18), ([0, -1, 1, 2, 0, -1, -1], -18), ([0, -1, 2, 1, -1, -1, 0], -18), ([0, -1, 2, 1, 0, -2, 0], -18), ([0, -1, 2, 1, 0, -1, -1], -18), ([0, 0, 0, 1, 0, -1, 0], -18), ([0, 0, 1, 0, 0, -1, 0], -18), ([0, 0, 1, 1, -1, -1, 0], -18), ([0, 0, 1, 1, 0, -1, -1], -18)]

def combined115_part1 : Sparse := [([1, -2, 1, 1, 0, -1, 1], -18), ([1, -2, 1, 1, 1, -1, 0], -18), ([1, -1, 0, 1, 0, 0, 0], -18), ([1, -1, 1, 0, 0, 0, 0], -18), ([1, -1, 1, 1, 0, -2, 1], -18), ([1, -1, 1, 1, 1, -2, 0], -18), ([1, -1, 1, 2, -1, -1, 0], -18), ([1, -1, 1, 2, 0, -1, -1], -18), ([1, -1, 2, 1, -1, -1, 0], -18), ([1, -1, 2, 1, 0, -1, -1], -18), ([1, 0, 0, 1, 0, -1, 0], -18), ([1, 0, 1, 0, 0, -1, 0], -18)]

def combined115 : Sparse := combined115_part0 ++ combined115_part1

def combined116_part0 : Sparse := [([0, -2, 2, 1, 0, 0, -1], -36), ([0, -1, 0, 1, 0, 1, -1], -36), ([0, -1, 0, 1, 1, 0, -1], -9), ([0, -1, 1, 0, 0, 1, -1], 36), ([0, -1, 1, 0, 1, 0, -1], -36), ([0, -1, 1, 1, -1, 0, 0], -36), ([0, -1, 1, 1, -1, 1, -1], -27), ([0, -1, 1, 1, 0, 1, -2], -9), ([0, -1, 1, 1, 1, 0, -2], 9), ([0, -1, 1, 2, 0, -1, -1], -9), ([0, -1, 1, 2, 0, 0, -2], -27), ([0, -1, 2, 0, 0, 0, -1], -27), ([0, -1, 2, 1, 0, 0, -2], 27), ([0, 0, 0, 1, 0, 0, -1], 9), ([0, 0, 1, 0, 0, 0, -1], -9), ([0, 0, 1, 1, -1, 0, -1], 27), ([0, 0, 1, 1, 0, -1, -1], -27), ([0, 0, 1, 1, 0, 0, -2], -36), ([1, -2, 1, 1, 0, 0, 0], 18), ([1, -2, 1, 2, 0, 0, -1], -36), ([1, -1, 0, 1, 0, 1, -1], -9), ([1, -1, 0, 1, 1, 0, -1], -36), ([1, -1, 0, 2, 0, 0, -1], 27), ([1, -1, 1, 0, 0, 1, -1], 27)]

def combined116_part1 : Sparse := [([1, -1, 1, 0, 1, 0, -1], -9), ([1, -1, 1, 1, -1, 1, -1], -27), ([1, -1, 1, 1, 0, -1, 0], -36), ([1, -1, 1, 1, 0, 1, -2], -9), ([1, -1, 1, 1, 1, -1, -1], 27), ([1, -1, 1, 2, -1, 0, -1], -9), ([1, -1, 2, 0, 0, 0, -1], -27), ([1, -1, 2, 1, -1, 0, -1], -9), ([1, -1, 2, 1, 0, -1, -1], -9), ([1, -1, 2, 1, 0, 0, -2], 27), ([1, 0, 1, 0, 0, 0, -1], -9), ([1, 0, 1, 1, -1, 0, -1], 27), ([1, 0, 1, 1, 0, 0, -2], -36)]

def combined116 : Sparse := combined116_part0 ++ combined116_part1

def combined117_part0 : Sparse := [([0, -2, 1, 1, 0, 1, -1], 9), ([0, -2, 1, 1, 1, 0, -1], 9), ([0, -2, 2, 1, 0, 0, -1], -36), ([0, -1, 0, 1, 0, 1, -1], -27), ([0, -1, 0, 1, 1, 0, -1], -9), ([0, -1, 1, 0, 0, 1, -1], 36), ([0, -1, 1, 0, 1, 0, -1], -36), ([0, -1, 1, 1, -1, 0, 0], -27), ([0, -1, 1, 1, -1, 1, -1], -18), ([0, -1, 1, 1, 0, -1, 0], 9), ([0, -1, 1, 1, 0, 1, -2], -18), ([0, -1, 1, 1, 1, 0, -2], 18), ([0, -1, 1, 2, -1, 0, -1], 9), ([0, -1, 1, 2, 0, -1, -1], -9), ([0, -1, 1, 2, 0, 0, -2], -18), ([0, -1, 2, 0, 0, 0, -1], -9), ([0, -1, 2, 1, 0, 0, -2], 27), ([0, 0, 0, 1, 0, 0, -1], 18), ([0, 0, 1, 0, 0, 0, -1], -9), ([0, 0, 1, 1, -1, 0, -1], 18), ([0, 0, 1, 1, 0, -1, -1], -18), ([0, 0, 1, 1, 0, 0, -2], -27), ([1, -2, 1, 1, 0, 0, 0], 9), ([1, -2, 1, 1, 0, 1, -1], 9)]

def combined117_part1 : Sparse := [([1, -2, 1, 1, 1, 0, -1], 9), ([1, -2, 1, 2, 0, 0, -1], -27), ([1, -1, 0, 1, 0, 0, 0], 9), ([1, -1, 0, 1, 0, 1, -1], -9), ([1, -1, 0, 1, 1, 0, -1], -27), ([1, -1, 0, 2, 0, 0, -1], 27), ([1, -1, 1, 0, 0, 1, -1], 27), ([1, -1, 1, 0, 1, 0, -1], -9), ([1, -1, 1, 1, -1, 0, 0], 9), ([1, -1, 1, 1, -1, 1, -1], -18), ([1, -1, 1, 1, 0, -1, 0], -27), ([1, -1, 1, 1, 0, 1, -2], -9), ([1, -1, 1, 1, 1, -1, -1], 18), ([1, -1, 1, 1, 1, 0, -2], 9), ([1, -1, 1, 2, -1, 0, -1], -9), ([1, -1, 1, 2, 0, -1, -1], 9), ([1, -1, 2, 0, 0, 0, -1], -9), ([1, -1, 2, 1, -1, 0, -1], -9), ([1, -1, 2, 1, 0, -1, -1], -9), ([1, -1, 2, 1, 0, 0, -2], 27), ([1, 0, 1, 0, 0, 0, -1], -9), ([1, 0, 1, 1, -1, 0, -1], 27), ([1, 0, 1, 1, 0, -1, -1], 9), ([1, 0, 1, 1, 0, 0, -2], -27)]

def combined117 : Sparse := combined117_part0 ++ combined117_part1

def combined118_part0 : Sparse := [([0, -2, 1, 1, 0, 1, -1], 9), ([0, -2, 2, 1, 0, 0, -1], -27), ([0, -1, 0, 1, 0, 1, -1], -27), ([0, -1, 0, 1, 1, 0, -1], -9), ([0, -1, 1, 0, 0, 0, 0], 9), ([0, -1, 1, 0, 0, 1, -1], 27), ([0, -1, 1, 0, 1, 0, -1], -27), ([0, -1, 1, 1, -1, 0, 0], -27), ([0, -1, 1, 1, -1, 1, -1], -9), ([0, -1, 1, 1, 0, 1, -2], -18), ([0, -1, 1, 1, 1, 0, -2], 18), ([0, -1, 1, 2, -1, 0, -1], 9), ([0, -1, 1, 2, 0, -1, -1], -9), ([0, -1, 1, 2, 0, 0, -2], -18), ([0, -1, 2, 0, 0, 0, -1], -9), ([0, -1, 2, 1, -1, 0, -1], -9), ([0, -1, 2, 1, 0, -1, -1], 9), ([0, -1, 2, 1, 0, 0, -2], 18), ([0, 0, 0, 1, 0, 0, -1], 18), ([0, 0, 1, 0, 0, 0, -1], -18), ([0, 0, 1, 1, -1, 0, -1], 18), ([0, 0, 1, 1, 0, -1, -1], -18), ([0, 0, 1, 1, 0, 0, -2], -18), ([1, -2, 1, 1, 1, 0, -1], 9)]

def combined118_part1 : Sparse := [([1, -2, 1, 2, 0, 0, -1], -27), ([1, -1, 0, 1, 0, 0, 0], 9), ([1, -1, 0, 1, 0, 1, -1], -9), ([1, -1, 0, 1, 1, 0, -1], -27), ([1, -1, 0, 2, 0, 0, -1], 9), ([1, -1, 1, 0, 0, 1, -1], 18), ([1, -1, 1, 0, 1, 0, -1], -9), ([1, -1, 1, 1, -1, 1, -1], -9), ([1, -1, 1, 1, 0, -1, 0], -27), ([1, -1, 1, 1, 0, 1, -2], -18), ([1, -1, 1, 1, 1, -1, -1], 9), ([1, -1, 1, 2, -1, 0, -1], -9), ([1, -1, 1, 2, 0, -1, -1], 9), ([1, -1, 2, 0, 0, 0, -1], -9), ([1, -1, 2, 1, -1, 0, -1], -18), ([1, -1, 2, 1, 0, -1, -1], -9), ([1, -1, 2, 1, 0, 0, -2], 18), ([1, 0, 1, 0, 0, 0, -1], -18), ([1, 0, 1, 1, -1, 0, -1], 18), ([1, 0, 1, 1, 0, 0, -2], -18)]

def combined118 : Sparse := combined118_part0 ++ combined118_part1

def combined119_part0 : Sparse := [([0, -2, 1, 1, 0, 1, -1], 18), ([0, -2, 2, 1, 0, 0, -1], -18), ([0, -1, 0, 1, 0, 1, -1], -18), ([0, -1, 1, 0, 0, 0, 0], 18), ([0, -1, 1, 0, 0, 1, -1], 18), ([0, -1, 1, 0, 1, 0, -1], -18), ([0, -1, 1, 1, -1, 0, 0], -18), ([0, -1, 1, 1, 0, 1, -2], -18), ([0, -1, 1, 1, 1, 0, -2], 18), ([0, -1, 1, 2, -1, 0, -1], 18), ([0, -1, 1, 2, 0, 0, -2], -18), ([0, -1, 2, 1, -1, 0, -1], -18), ([0, -1, 2, 1, 0, -1, -1], 18), ([0, -1, 2, 1, 0, 0, -2], 18), ([0, 0, 0, 1, 0, 0, -1], 18), ([0, 0, 1, 0, 0, 0, -1], -18), ([0, 0, 1, 1, -1, 0, -1], 18), ([0, 0, 1, 1, 0, -1, -1], -18), ([1, -2, 1, 1, 1, 0, -1], 18), ([1, -2, 1, 2, 0, 0, -1], -18), ([1, -1, 0, 1, 0, 0, 0], 18), ([1, -1, 0, 1, 1, 0, -1], -18), ([1, -1, 1, 0, 0, 1, -1], 18), ([1, -1, 1, 1, 0, -1, 0], -18)]

def combined119_part1 : Sparse := [([1, -1, 1, 1, 0, 1, -2], -18), ([1, -1, 1, 2, 0, -1, -1], 18), ([1, -1, 2, 1, -1, 0, -1], -18), ([1, -1, 2, 1, 0, 0, -2], 18), ([1, 0, 1, 0, 0, 0, -1], -18), ([1, 0, 1, 1, -1, 0, -1], 18)]

def combined119 : Sparse := combined119_part0 ++ combined119_part1

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined120_part0 : Sparse := [([0, -1, -1, -1, 0, 1, 2], 9), ([0, -1, -1, -1, 0, 2, 1], 9), ([0, -1, -1, 0, 0, 1, 1], -36), ([0, 0, -2, -1, 0, 1, 2], -36), ([0, 0, -2, -1, 0, 2, 1], 36), ([0, 0, -2, 0, 0, 1, 1], -18), ([0, 0, -1, -2, 0, 2, 1], -27), ([0, 0, -1, -1, -1, 1, 2], 9), ([0, 0, -1, -1, -1, 2, 1], -9), ([0, 0, -1, -1, 0, 2, 0], -27), ([0, 0, -1, -1, 1, 0, 1], 9), ([0, 0, -1, -1, 1, 1, 0], -27), ([0, 0, -1, 0, -1, 1, 1], 36), ([0, 0, 0, -1, -1, 1, 1], -27), ([0, 0, 0, -1, 0, 1, 0], 9), ([0, 1, -1, -2, 0, 1, 1], 9), ([0, 1, -1, -1, -1, 1, 1], -27), ([0, 1, -1, -1, 0, 0, 1], -27), ([0, 1, -1, -1, 0, 1, 0], 27), ([1, -1, -1, -1, 0, 1, 2], 9), ([1, -1, -1, -1, 0, 2, 1], 9), ([1, -1, -1, -1, 1, 1, 1], 27), ([1, -1, 0, -1, 0, 1, 1], -27), ([1, 0, -2, -1, 0, 2, 1], 36)]

def combined120_part1 : Sparse := [([1, 0, -2, 0, 0, 1, 1], -18), ([1, 0, -1, -2, 0, 1, 2], -27), ([1, 0, -1, -2, 1, 1, 1], 9), ([1, 0, -1, -1, -1, 1, 2], 9), ([1, 0, -1, -1, 0, 0, 2], 27), ([1, 0, -1, -1, 0, 2, 0], -27), ([1, 0, -1, -1, 1, 0, 1], -27), ([1, 0, -1, -1, 1, 1, 0], 9), ([1, 0, -1, 0, -1, 1, 1], 36), ([1, 0, 0, -2, 0, 1, 1], 36), ([1, 0, 0, -1, 0, 0, 1], 9), ([1, 1, -1, -1, -1, 1, 1], -27), ([1, 1, -1, -1, 0, 0, 1], 9), ([1, 1, -1, -1, 0, 1, 0], 36)]

def combined120 : Sparse := combined120_part0 ++ combined120_part1

def combined121_part0 : Sparse := [([0, -1, -1, -1, 0, 2, 1], 9), ([0, -1, -1, 0, 0, 1, 1], -27), ([0, 0, -2, -1, 0, 1, 2], -27), ([0, 0, -2, -1, 0, 2, 1], 27), ([0, 0, -2, -1, 1, 1, 1], 9), ([0, 0, -2, 0, 0, 1, 1], -18), ([0, 0, -1, -2, 0, 2, 1], -27), ([0, 0, -1, -1, -1, 1, 2], 9), ([0, 0, -1, -1, -1, 2, 1], -9), ([0, 0, -1, -1, 0, 2, 0], -18), ([0, 0, -1, -1, 1, 1, 0], -27), ([0, 0, -1, 0, -1, 1, 1], 27), ([0, 0, -1, 0, 0, 0, 1], 9), ([0, 0, -1, 0, 0, 1, 0], -9), ([0, 0, 0, -1, -1, 1, 1], -27), ([0, 0, 0, -1, 0, 1, 0], 9), ([0, 1, -2, -1, 0, 1, 1], -9), ([0, 1, -1, -2, 0, 1, 1], 9), ([0, 1, -1, -1, -1, 1, 1], -18), ([0, 1, -1, -1, 0, 0, 1], -27), ([0, 1, -1, -1, 0, 1, 0], 27), ([1, -1, -1, -1, 0, 1, 2], 9), ([1, -1, -1, -1, 1, 1, 1], 18), ([1, -1, 0, -1, 0, 1, 1], -27)]

def combined121_part1 : Sparse := [([1, 0, -2, -1, 0, 2, 1], 27), ([1, 0, -2, 0, 0, 1, 1], -18), ([1, 0, -1, -2, 0, 1, 2], -27), ([1, 0, -1, -2, 1, 1, 1], 9), ([1, 0, -1, -1, -1, 2, 1], -9), ([1, 0, -1, -1, 0, 0, 2], 18), ([1, 0, -1, -1, 0, 2, 0], -18), ([1, 0, -1, -1, 1, 0, 1], -27), ([1, 0, -1, 0, -1, 1, 1], 27), ([1, 0, -1, 0, 0, 1, 0], -9), ([1, 0, 0, -2, 0, 1, 1], 18), ([1, 0, 0, -1, 0, 0, 1], 9), ([1, 1, -2, -1, 0, 1, 1], -9), ([1, 1, -1, -1, -1, 1, 1], -18), ([1, 1, -1, -1, 0, 1, 0], 27)]

def combined121 : Sparse := combined121_part0 ++ combined121_part1

def combined122_part0 : Sparse := [([0, -1, -1, -1, 0, 2, 1], 9), ([0, -1, -1, 0, 0, 1, 1], -18), ([0, -1, 0, -1, 0, 1, 1], 9), ([0, 0, -2, -1, 0, 1, 2], -18), ([0, 0, -2, -1, 0, 2, 1], 27), ([0, 0, -2, -1, 1, 1, 1], 18), ([0, 0, -2, 0, 0, 1, 1], -9), ([0, 0, -1, -2, 0, 2, 1], -27), ([0, 0, -1, -2, 1, 1, 1], 9), ([0, 0, -1, -1, -1, 1, 2], 18), ([0, 0, -1, -1, -1, 2, 1], -9), ([0, 0, -1, -1, 1, 1, 0], -27), ([0, 0, -1, 0, -1, 1, 1], 18), ([0, 0, -1, 0, 0, 0, 1], 18), ([0, 0, -1, 0, 0, 1, 0], -9), ([0, 0, 0, -1, -1, 1, 1], -18), ([0, 0, 0, -1, 0, 1, 0], 9), ([0, 1, -2, -1, 0, 1, 1], -18), ([0, 1, -1, -2, 0, 1, 1], 18), ([0, 1, -1, -1, -1, 1, 1], -9), ([0, 1, -1, -1, 0, 0, 1], -18), ([0, 1, -1, -1, 0, 1, 0], 27), ([1, -1, -1, -1, 0, 1, 2], 18), ([1, -1, -1, -1, 1, 1, 1], 9)]

def combined122_part1 : Sparse := [([1, -1, -1, 0, 0, 1, 1], 9), ([1, -1, 0, -1, 0, 1, 1], -18), ([1, 0, -2, -1, 0, 2, 1], 27), ([1, 0, -2, -1, 1, 1, 1], 9), ([1, 0, -2, 0, 0, 1, 1], -9), ([1, 0, -1, -2, 0, 1, 2], -18), ([1, 0, -1, -2, 1, 1, 1], 18), ([1, 0, -1, -1, -1, 2, 1], -9), ([1, 0, -1, -1, 0, 0, 2], 18), ([1, 0, -1, -1, 1, 0, 1], -18), ([1, 0, -1, 0, -1, 1, 1], 27), ([1, 0, -1, 0, 0, 1, 0], -9), ([1, 0, 0, -2, 0, 1, 1], 9), ([1, 0, 0, -1, -1, 1, 1], 9), ([1, 0, 0, -1, 0, 0, 1], 18), ([1, 1, -2, -1, 0, 1, 1], -9), ([1, 1, -1, -2, 0, 1, 1], 9), ([1, 1, -1, -1, -1, 1, 1], -9), ([1, 1, -1, -1, 0, 1, 0], 27)]

def combined122 : Sparse := combined122_part0 ++ combined122_part1

def combined123_part0 : Sparse := [([0, -1, -1, -1, 0, 2, 1], 18), ([0, -1, -1, 0, 0, 1, 1], -18), ([0, 0, -2, -1, 0, 1, 2], -18), ([0, 0, -2, -1, 0, 2, 1], 18), ([0, 0, -2, -1, 1, 1, 1], 18), ([0, 0, -1, -2, 0, 2, 1], -18), ([0, 0, -1, -1, -1, 1, 2], 18), ([0, 0, -1, -1, -1, 2, 1], -18), ([0, 0, -1, -1, 1, 1, 0], -18), ([0, 0, -1, 0, -1, 1, 1], 18), ([0, 0, -1, 0, 0, 0, 1], 18), ([0, 0, -1, 0, 0, 1, 0], -18), ([0, 0, 0, -1, -1, 1, 1], -18), ([0, 0, 0, -1, 0, 1, 0], 18), ([0, 1, -2, -1, 0, 1, 1], -18), ([0, 1, -1, -2, 0, 1, 1], 18), ([0, 1, -1, -1, 0, 0, 1], -18), ([0, 1, -1, -1, 0, 1, 0], 18), ([1, -1, -1, -1, 0, 1, 2], 18), ([1, -1, 0, -1, 0, 1, 1], -18), ([1, 0, -2, -1, 0, 2, 1], 18), ([1, 0, -1, -2, 0, 1, 2], -18), ([1, 0, -1, -2, 1, 1, 1], 18), ([1, 0, -1, -1, -1, 2, 1], -18)]

def combined123_part1 : Sparse := [([1, 0, -1, -1, 1, 0, 1], -18), ([1, 0, -1, 0, -1, 1, 1], 18), ([1, 0, -1, 0, 0, 1, 0], -18), ([1, 0, 0, -1, 0, 0, 1], 18), ([1, 1, -2, -1, 0, 1, 1], -18), ([1, 1, -1, -1, 0, 1, 0], 18)]

def combined123 : Sparse := combined123_part0 ++ combined123_part1

def combined124_part0 : Sparse := [([0, -1, -1, -1, 2, 0, 1], -9), ([0, -1, -1, 0, 1, 0, 1], -36), ([0, -1, 0, -1, 1, 0, 1], -27), ([0, 0, -2, -1, 1, 0, 2], -36), ([0, 0, -2, -1, 2, 0, 1], -36), ([0, 0, -1, -2, 1, 0, 2], -27), ([0, 0, -1, -2, 1, 1, 1], -9), ([0, 0, -1, -2, 2, 0, 1], -27), ([0, 0, -1, -1, 0, 1, 1], -27), ([0, 0, -1, -1, 1, -1, 2], -9), ([0, 0, -1, -1, 1, 1, 0], -36), ([0, 0, -1, 0, 1, -1, 1], -36), ([0, 0, 0, -1, 0, 0, 1], -9), ([0, 0, 0, -1, 1, -1, 1], -27), ([0, 0, 0, -1, 1, 0, 0], -9), ([0, 1, -1, -2, 1, 0, 1], -9), ([0, 1, -1, -1, 0, 0, 1], -36), ([0, 1, -1, -1, 1, 0, 0], -27), ([1, -1, -1, -1, 1, 0, 2], -9), ([1, -1, -1, -1, 1, 1, 1], 27), ([1, 0, -2, 0, 1, 0, 1], 18), ([1, 0, -1, -2, 1, 1, 1], -9), ([1, 0, -1, -1, 0, 0, 2], 27), ([1, 0, -1, -1, 0, 1, 1], 9)]

def combined124_part1 : Sparse := [([1, 0, -1, -1, 1, 1, 0], -9), ([1, 0, -1, -1, 2, -1, 1], -9), ([1, 0, -1, -1, 2, 0, 0], 27), ([1, 0, 0, -2, 1, 0, 1], 36), ([1, 0, 0, -1, 0, 0, 1], -9), ([1, 0, 0, -1, 1, 0, 0], -9), ([1, 1, -1, -2, 1, 0, 1], -9), ([1, 1, -1, -1, 0, 0, 1], -9), ([1, 1, -1, -1, 1, -1, 1], 27), ([1, 1, -1, -1, 1, 0, 0], 9)]

def combined124 : Sparse := combined124_part0 ++ combined124_part1

def combined125_part0 : Sparse := [([0, -1, -1, -1, 1, 0, 2], -9), ([0, -1, -1, -1, 2, 0, 1], -9), ([0, -1, -1, 0, 1, 0, 1], -27), ([0, -1, 0, -1, 1, 0, 1], -27), ([0, 0, -2, -1, 1, 0, 2], -27), ([0, 0, -2, -1, 1, 1, 1], -9), ([0, 0, -2, -1, 2, 0, 1], -27), ([0, 0, -1, -2, 1, 0, 2], -27), ([0, 0, -1, -2, 1, 1, 1], -9), ([0, 0, -1, -2, 2, 0, 1], -27), ([0, 0, -1, -1, 0, 1, 1], -27), ([0, 0, -1, -1, 1, -1, 2], -9), ([0, 0, -1, -1, 1, 1, 0], -27), ([0, 0, -1, -1, 2, -1, 1], -9), ([0, 0, -1, 0, 0, 0, 1], -9), ([0, 0, -1, 0, 1, -1, 1], -27), ([0, 0, -1, 0, 1, 0, 0], -9), ([0, 0, 0, -1, 0, 0, 1], -9), ([0, 0, 0, -1, 1, -1, 1], -27), ([0, 0, 0, -1, 1, 0, 0], -9), ([0, 1, -2, -1, 1, 0, 1], -9), ([0, 1, -1, -2, 1, 0, 1], -9), ([0, 1, -1, -1, 0, 0, 1], -27), ([0, 1, -1, -1, 1, 0, 0], -27)]

def combined125_part1 : Sparse := [([1, -1, -1, -1, 1, 0, 2], -9), ([1, -1, -1, -1, 1, 1, 1], 18), ([1, -1, -1, -1, 2, 0, 1], -9), ([1, 0, -2, -1, 1, 1, 1], -9), ([1, 0, -2, 0, 1, 0, 1], 18), ([1, 0, -1, -2, 1, 1, 1], -9), ([1, 0, -1, -1, 0, 0, 2], 18), ([1, 0, -1, -1, 1, -1, 2], -9), ([1, 0, -1, -1, 2, -1, 1], -9), ([1, 0, -1, -1, 2, 0, 0], 18), ([1, 0, -1, 0, 0, 0, 1], -9), ([1, 0, -1, 0, 1, 0, 0], -9), ([1, 0, 0, -2, 1, 0, 1], 18), ([1, 0, 0, -1, 0, 0, 1], -9), ([1, 0, 0, -1, 1, 0, 0], -9), ([1, 1, -2, -1, 1, 0, 1], -9), ([1, 1, -1, -2, 1, 0, 1], -9), ([1, 1, -1, -1, 1, -1, 1], 18)]

def combined125 : Sparse := combined125_part0 ++ combined125_part1

def combined126_part0 : Sparse := [([0, -1, -1, -1, 1, 0, 2], -18), ([0, -1, -1, -1, 2, 0, 1], -9), ([0, -1, -1, 0, 1, 0, 1], -27), ([0, -1, 0, -1, 1, 0, 1], -18), ([0, 0, -2, -1, 1, 0, 2], -18), ([0, 0, -2, -1, 1, 1, 1], -18), ([0, 0, -2, -1, 2, 0, 1], -27), ([0, 0, -1, -2, 1, 0, 2], -18), ([0, 0, -1, -2, 1, 1, 1], -9), ([0, 0, -1, -2, 2, 0, 1], -27), ([0, 0, -1, -1, 0, 1, 1], -18), ([0, 0, -1, -1, 1, -1, 2], -18), ([0, 0, -1, -1, 1, 1, 0], -27), ([0, 0, -1, -1, 2, -1, 1], -9), ([0, 0, -1, 0, 0, 0, 1], -18), ([0, 0, -1, 0, 1, -1, 1], -18), ([0, 0, -1, 0, 1, 0, 0], -9), ([0, 0, 0, -1, 0, 0, 1], -18), ([0, 0, 0, -1, 1, -1, 1], -27), ([0, 0, 0, -1, 1, 0, 0], -9), ([0, 1, -2, -1, 1, 0, 1], -9), ([0, 1, -1, -2, 1, 0, 1], -18), ([0, 1, -1, -1, 0, 0, 1], -18), ([0, 1, -1, -1, 1, 0, 0], -27)]

def combined126_part1 : Sparse := [([1, -1, -1, -1, 1, 0, 2], -18), ([1, -1, -1, -1, 1, 1, 1], 9), ([1, -1, -1, -1, 2, 0, 1], -9), ([1, -1, -1, 0, 1, 0, 1], -9), ([1, -1, 0, -1, 1, 0, 1], 9), ([1, 0, -2, -1, 1, 1, 1], -9), ([1, 0, -2, 0, 1, 0, 1], 9), ([1, 0, -1, -2, 1, 1, 1], -18), ([1, 0, -1, -1, 0, 0, 2], 18), ([1, 0, -1, -1, 1, -1, 2], -18), ([1, 0, -1, -1, 2, -1, 1], -9), ([1, 0, -1, 0, 0, 0, 1], -18), ([1, 0, -1, 0, 1, -1, 1], 9), ([1, 0, -1, 0, 1, 0, 0], -9), ([1, 0, 0, -2, 1, 0, 1], 9), ([1, 0, 0, -1, 0, 0, 1], -18), ([1, 0, 0, -1, 1, -1, 1], -9), ([1, 0, 0, -1, 1, 0, 0], -9), ([1, 1, -2, -1, 1, 0, 1], -18), ([1, 1, -1, -2, 1, 0, 1], -9), ([1, 1, -1, -1, 1, -1, 1], 9)]

def combined126 : Sparse := combined126_part0 ++ combined126_part1

def combined127_part0 : Sparse := [([0, -1, -1, -1, 1, 0, 2], -18), ([0, -1, -1, -1, 2, 0, 1], -18), ([0, -1, -1, 0, 1, 0, 1], -18), ([0, -1, 0, -1, 1, 0, 1], -18), ([0, 0, -2, -1, 1, 0, 2], -18), ([0, 0, -2, -1, 1, 1, 1], -18), ([0, 0, -2, -1, 2, 0, 1], -18), ([0, 0, -1, -2, 1, 0, 2], -18), ([0, 0, -1, -2, 1, 1, 1], -18), ([0, 0, -1, -2, 2, 0, 1], -18), ([0, 0, -1, -1, 0, 1, 1], -18), ([0, 0, -1, -1, 1, -1, 2], -18), ([0, 0, -1, -1, 1, 1, 0], -18), ([0, 0, -1, -1, 2, -1, 1], -18), ([0, 0, -1, 0, 0, 0, 1], -18), ([0, 0, -1, 0, 1, -1, 1], -18), ([0, 0, -1, 0, 1, 0, 0], -18), ([0, 0, 0, -1, 0, 0, 1], -18), ([0, 0, 0, -1, 1, -1, 1], -18), ([0, 0, 0, -1, 1, 0, 0], -18), ([0, 1, -2, -1, 1, 0, 1], -18), ([0, 1, -1, -2, 1, 0, 1], -18), ([0, 1, -1, -1, 0, 0, 1], -18), ([0, 1, -1, -1, 1, 0, 0], -18)]

def combined127_part1 : Sparse := [([1, -1, -1, -1, 1, 0, 2], -18), ([1, -1, -1, -1, 2, 0, 1], -18), ([1, 0, -2, -1, 1, 1, 1], -18), ([1, 0, -1, -2, 1, 1, 1], -18), ([1, 0, -1, -1, 1, -1, 2], -18), ([1, 0, -1, -1, 2, -1, 1], -18), ([1, 0, -1, 0, 0, 0, 1], -18), ([1, 0, -1, 0, 1, 0, 0], -18), ([1, 0, 0, -1, 0, 0, 1], -18), ([1, 0, 0, -1, 1, 0, 0], -18), ([1, 1, -2, -1, 1, 0, 1], -18), ([1, 1, -1, -2, 1, 0, 1], -18)]

def combined127 : Sparse := combined127_part0 ++ combined127_part1

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined128_part0 : Sparse := [([0, -1, -1, -1, 2, 1, 0], -9), ([0, -1, 0, -1, 1, 1, 0], -27), ([0, 0, -2, -1, 1, 2, 0], -36), ([0, 0, -1, -2, 1, 1, 1], 9), ([0, 0, -1, -2, 1, 2, 0], 27), ([0, 0, -1, -2, 2, 1, 0], -27), ([0, 0, -1, -1, 0, 1, 1], -36), ([0, 0, -1, -1, 0, 2, 0], -27), ([0, 0, -1, -1, 1, 0, 1], -9), ([0, 0, -1, 0, 1, 1, -1], -36), ([0, 0, 0, -2, 1, 1, 0], -36), ([0, 0, 0, -1, 0, 1, 0], -9), ([0, 0, 0, -1, 1, 0, 0], 9), ([0, 0, 0, -1, 1, 1, -1], 27), ([0, 1, -1, -2, 1, 1, 0], -9), ([0, 1, -1, -1, 0, 1, 0], 36), ([0, 1, -1, -1, 1, 0, 0], -36), ([0, 1, -1, -1, 1, 1, -1], -27), ([1, -1, -1, -1, 1, 1, 1], 27), ([1, -1, -1, -1, 1, 2, 0], -9), ([1, -1, -1, 0, 1, 1, 0], -36), ([1, 0, -2, -1, 2, 1, 0], -36), ([1, 0, -2, 0, 1, 1, 0], 18), ([1, 0, -1, -2, 1, 2, 0], 27)]

def combined128_part1 : Sparse := [([1, 0, -1, -1, 0, 1, 1], -9), ([1, 0, -1, -1, 0, 2, 0], -27), ([1, 0, -1, -1, 1, 0, 1], -36), ([1, 0, -1, -1, 1, 2, -1], -9), ([1, 0, -1, -1, 2, 0, 0], 27), ([1, 0, -1, -1, 2, 1, -1], -9), ([1, 0, 0, -2, 1, 1, 0], -36), ([1, 0, 0, -1, 0, 1, 0], -9), ([1, 0, 0, -1, 1, 1, -1], 27), ([1, 1, -1, -2, 1, 1, 0], -9), ([1, 1, -1, -1, 0, 1, 0], 27), ([1, 1, -1, -1, 1, 0, 0], -9), ([1, 1, -1, -1, 1, 1, -1], -27)]

def combined128 : Sparse := combined128_part0 ++ combined128_part1

def combined129_part0 : Sparse := [([0, -1, -1, -1, 1, 2, 0], 9), ([0, -1, 0, -1, 1, 1, 0], -27), ([0, 0, -2, -1, 1, 2, 0], -27), ([0, 0, -1, -2, 1, 1, 1], 9), ([0, 0, -1, -2, 1, 2, 0], 27), ([0, 0, -1, -2, 2, 1, 0], -27), ([0, 0, -1, -1, 0, 1, 1], -27), ([0, 0, -1, -1, 0, 2, 0], -18), ([0, 0, -1, -1, 1, 2, -1], -9), ([0, 0, -1, -1, 2, 1, -1], 9), ([0, 0, -1, 0, 0, 1, 0], 9), ([0, 0, -1, 0, 1, 1, -1], -27), ([0, 0, 0, -2, 1, 1, 0], -18), ([0, 0, 0, -1, 0, 1, 0], -9), ([0, 0, 0, -1, 1, 0, 0], 9), ([0, 0, 0, -1, 1, 1, -1], 27), ([0, 1, -2, -1, 1, 1, 0], 9), ([0, 1, -1, -2, 1, 1, 0], -9), ([0, 1, -1, -1, 0, 1, 0], 27), ([0, 1, -1, -1, 1, 0, 0], -27), ([0, 1, -1, -1, 1, 1, -1], -18), ([1, -1, -1, -1, 1, 1, 1], 18), ([1, -1, -1, -1, 2, 1, 0], 9), ([1, -1, -1, 0, 1, 1, 0], -27)]

def combined129_part1 : Sparse := [([1, 0, -2, -1, 1, 1, 1], 9), ([1, 0, -2, -1, 2, 1, 0], -27), ([1, 0, -2, 0, 1, 1, 0], 18), ([1, 0, -1, -2, 1, 2, 0], 27), ([1, 0, -1, -1, 0, 2, 0], -18), ([1, 0, -1, -1, 1, 0, 1], -27), ([1, 0, -1, -1, 1, 2, -1], -9), ([1, 0, -1, -1, 2, 0, 0], 18), ([1, 0, -1, 0, 1, 0, 0], 9), ([1, 0, 0, -2, 1, 1, 0], -18), ([1, 0, 0, -1, 0, 1, 0], -9), ([1, 0, 0, -1, 1, 1, -1], 27), ([1, 1, -1, -2, 1, 1, 0], -9), ([1, 1, -1, -1, 0, 1, 0], 27), ([1, 1, -1, -1, 1, 1, -1], -18)]

def combined129 : Sparse := combined129_part0 ++ combined129_part1

def combined130_part0 : Sparse := [([0, -1, -1, -1, 1, 2, 0], 18), ([0, -1, -1, 0, 1, 1, 0], -9), ([0, -1, 0, -1, 1, 1, 0], -27), ([0, 0, -2, -1, 1, 1, 1], -9), ([0, 0, -2, -1, 1, 2, 0], -18), ([0, 0, -1, -2, 1, 1, 1], 9), ([0, 0, -1, -2, 1, 2, 0], 18), ([0, 0, -1, -2, 2, 1, 0], -27), ([0, 0, -1, -1, 0, 1, 1], -18), ([0, 0, -1, -1, 0, 2, 0], -18), ([0, 0, -1, -1, 1, 2, -1], -18), ([0, 0, -1, -1, 2, 1, -1], 9), ([0, 0, -1, 0, 0, 1, 0], 18), ([0, 0, -1, 0, 1, 1, -1], -27), ([0, 0, 0, -2, 1, 1, 0], -9), ([0, 0, 0, -1, 0, 1, 0], -18), ([0, 0, 0, -1, 1, 0, 0], 9), ([0, 0, 0, -1, 1, 1, -1], 27), ([0, 1, -2, -1, 1, 1, 0], 9), ([0, 1, -1, -2, 1, 1, 0], -9), ([0, 1, -1, -1, 0, 1, 0], 18), ([0, 1, -1, -1, 1, 0, 0], -27), ([0, 1, -1, -1, 1, 1, -1], -9), ([1, -1, -1, -1, 1, 1, 1], 9)]

def combined130_part1 : Sparse := [([1, -1, -1, -1, 2, 1, 0], 9), ([1, -1, -1, 0, 1, 1, 0], -27), ([1, -1, 0, -1, 1, 1, 0], -9), ([1, 0, -2, -1, 1, 1, 1], 9), ([1, 0, -2, -1, 2, 1, 0], -27), ([1, 0, -2, 0, 1, 1, 0], 9), ([1, 0, -1, -2, 1, 1, 1], -9), ([1, 0, -1, -2, 1, 2, 0], 18), ([1, 0, -1, -1, 0, 2, 0], -18), ([1, 0, -1, -1, 1, 0, 1], -27), ([1, 0, -1, -1, 1, 2, -1], -18), ([1, 0, -1, 0, 1, 0, 0], 9), ([1, 0, -1, 0, 1, 1, -1], -9), ([1, 0, 0, -2, 1, 1, 0], -9), ([1, 0, 0, -1, 0, 1, 0], -18), ([1, 0, 0, -1, 1, 1, -1], 18), ([1, 1, -2, -1, 1, 1, 0], -9), ([1, 1, -1, -2, 1, 1, 0], -18), ([1, 1, -1, -1, 0, 1, 0], 18), ([1, 1, -1, -1, 1, 1, -1], -9)]

def combined130 : Sparse := combined130_part0 ++ combined130_part1

def combined131_part0 : Sparse := [([0, -1, -1, -1, 1, 2, 0], 18), ([0, -1, 0, -1, 1, 1, 0], -18), ([0, 0, -2, -1, 1, 2, 0], -18), ([0, 0, -1, -2, 1, 1, 1], 18), ([0, 0, -1, -2, 1, 2, 0], 18), ([0, 0, -1, -2, 2, 1, 0], -18), ([0, 0, -1, -1, 0, 1, 1], -18), ([0, 0, -1, -1, 1, 2, -1], -18), ([0, 0, -1, -1, 2, 1, -1], 18), ([0, 0, -1, 0, 0, 1, 0], 18), ([0, 0, -1, 0, 1, 1, -1], -18), ([0, 0, 0, -1, 0, 1, 0], -18), ([0, 0, 0, -1, 1, 0, 0], 18), ([0, 0, 0, -1, 1, 1, -1], 18), ([0, 1, -2, -1, 1, 1, 0], 18), ([0, 1, -1, -2, 1, 1, 0], -18), ([0, 1, -1, -1, 0, 1, 0], 18), ([0, 1, -1, -1, 1, 0, 0], -18), ([1, -1, -1, -1, 2, 1, 0], 18), ([1, -1, -1, 0, 1, 1, 0], -18), ([1, 0, -2, -1, 1, 1, 1], 18), ([1, 0, -2, -1, 2, 1, 0], -18), ([1, 0, -1, -2, 1, 2, 0], 18), ([1, 0, -1, -1, 1, 0, 1], -18)]

def combined131_part1 : Sparse := [([1, 0, -1, -1, 1, 2, -1], -18), ([1, 0, -1, 0, 1, 0, 0], 18), ([1, 0, 0, -1, 0, 1, 0], -18), ([1, 0, 0, -1, 1, 1, -1], 18), ([1, 1, -1, -2, 1, 1, 0], -18), ([1, 1, -1, -1, 0, 1, 0], 18)]

def combined131 : Sparse := combined131_part0 ++ combined131_part1

def combined132_part0 : Sparse := [([0, -1, -1, 0, -1, 1, 2], -9), ([0, -1, -1, 0, -1, 2, 1], 9), ([0, -1, -1, 0, 0, 1, 1], -36), ([0, -1, -1, 1, -1, 1, 1], -27), ([0, -1, 0, 0, -1, 1, 1], -27), ([0, 0, -2, 0, -1, 1, 2], -36), ([0, 0, -2, 0, -1, 2, 1], -36), ([0, 0, -2, 0, 0, 1, 1], -18), ([0, 0, -1, -1, -1, 1, 2], 9), ([0, 0, -1, -1, -1, 2, 1], -9), ([0, 0, -1, -1, 0, 1, 1], -36), ([0, 0, -1, 0, -2, 1, 2], -27), ([0, 0, -1, 0, -2, 2, 1], -27), ([0, 0, -1, 0, -1, 0, 2], -27), ([0, 0, -1, 0, -1, 2, 0], -27), ([0, 0, -1, 1, -1, 0, 1], -27), ([0, 0, -1, 1, -1, 1, 0], -36), ([0, 0, 0, -1, -1, 1, 1], -27), ([0, 0, 0, 0, -2, 1, 1], -36), ([0, 1, -1, -1, -1, 1, 1], -27), ([0, 1, -1, 0, -1, 0, 1], -36), ([0, 1, -1, 0, -1, 1, 0], -27), ([1, -1, -1, 0, -1, 2, 1], 9), ([1, -1, -1, 1, -1, 1, 1], -27)]

def combined132_part1 : Sparse := [([1, 0, -2, 0, 0, 1, 1], -18), ([1, 0, -1, -1, -1, 1, 2], 9), ([1, 0, -1, 0, -1, 0, 2], -27), ([1, 0, -1, 0, -1, 2, 0], -27), ([1, 0, -1, 1, -2, 1, 1], 9), ([1, 0, -1, 1, -1, 0, 1], 9), ([1, 0, -1, 1, -1, 1, 0], -9), ([1, 0, 0, 0, -2, 1, 1], -36), ([1, 0, 0, 0, -1, 0, 1], 9), ([1, 0, 0, 0, -1, 1, 0], 9), ([1, 1, -1, -1, -1, 1, 1], -27), ([1, 1, -1, 0, -2, 1, 1], 9), ([1, 1, -1, 0, -1, 0, 1], -9), ([1, 1, -1, 0, -1, 1, 0], 9)]

def combined132 : Sparse := combined132_part0 ++ combined132_part1

def combined133_part0 : Sparse := [([0, -1, -1, 0, 0, 1, 1], -27), ([0, -1, -1, 1, -1, 1, 1], -18), ([0, -1, 0, 0, -1, 1, 1], -27), ([0, 0, -2, 0, -1, 1, 2], -27), ([0, 0, -2, 0, -1, 2, 1], -27), ([0, 0, -2, 0, 0, 1, 1], -18), ([0, 0, -1, -1, 0, 1, 1], -27), ([0, 0, -1, 0, -2, 1, 2], -27), ([0, 0, -1, 0, -2, 2, 1], -27), ([0, 0, -1, 0, -1, 0, 2], -18), ([0, 0, -1, 0, -1, 2, 0], -18), ([0, 0, -1, 1, -1, 0, 1], -27), ([0, 0, -1, 1, -1, 1, 0], -27), ([0, 0, 0, -1, -1, 1, 1], -27), ([0, 0, 0, 0, -2, 1, 1], -18), ([0, 1, -1, -1, -1, 1, 1], -18), ([0, 1, -1, 0, -1, 0, 1], -27), ([0, 1, -1, 0, -1, 1, 0], -27), ([1, -1, -1, 0, -1, 1, 2], 9), ([1, -1, -1, 0, -1, 2, 1], 9), ([1, -1, -1, 1, -1, 1, 1], -18), ([1, 0, -2, 0, 0, 1, 1], -18), ([1, 0, -2, 1, -1, 1, 1], 9), ([1, 0, -1, -1, -1, 1, 2], 9)]

def combined133_part1 : Sparse := [([1, 0, -1, -1, -1, 2, 1], 9), ([1, 0, -1, 0, -1, 0, 2], -18), ([1, 0, -1, 0, -1, 2, 0], -18), ([1, 0, -1, 0, 0, 0, 1], 9), ([1, 0, -1, 0, 0, 1, 0], 9), ([1, 0, -1, 1, -2, 1, 1], 9), ([1, 0, 0, 0, -2, 1, 1], -18), ([1, 0, 0, 0, -1, 0, 1], 9), ([1, 0, 0, 0, -1, 1, 0], 9), ([1, 1, -2, 0, -1, 1, 1], 9), ([1, 1, -1, -1, -1, 1, 1], -18), ([1, 1, -1, 0, -2, 1, 1], 9)]

def combined133 : Sparse := combined133_part0 ++ combined133_part1

def combined134_part0 : Sparse := [([0, -1, -1, 0, 0, 1, 1], -27), ([0, -1, -1, 1, -1, 1, 1], -9), ([0, -1, 0, 0, -1, 1, 1], -18), ([0, 0, -2, 0, -1, 1, 2], -18), ([0, 0, -2, 0, -1, 2, 1], -27), ([0, 0, -2, 0, 0, 1, 1], -9), ([0, 0, -2, 1, -1, 1, 1], 9), ([0, 0, -1, -1, 0, 1, 1], -18), ([0, 0, -1, 0, -2, 1, 2], -18), ([0, 0, -1, 0, -2, 2, 1], -27), ([0, 0, -1, 0, -1, 0, 2], -18), ([0, 0, -1, 1, -2, 1, 1], -9), ([0, 0, -1, 1, -1, 0, 1], -18), ([0, 0, -1, 1, -1, 1, 0], -27), ([0, 0, 0, -1, -1, 1, 1], -27), ([0, 0, 0, 0, -2, 1, 1], -9), ([0, 1, -2, 0, -1, 1, 1], -9), ([0, 1, -1, -1, -1, 1, 1], -9), ([0, 1, -1, 0, -2, 1, 1], 9), ([0, 1, -1, 0, -1, 0, 1], -18), ([0, 1, -1, 0, -1, 1, 0], -27), ([1, -1, -1, 0, -1, 1, 2], 18), ([1, -1, -1, 0, -1, 2, 1], 9), ([1, -1, -1, 0, 0, 1, 1], -9)]

def combined134_part1 : Sparse := [([1, -1, -1, 1, -1, 1, 1], -9), ([1, -1, 0, 0, -1, 1, 1], 9), ([1, 0, -2, 0, 0, 1, 1], -9), ([1, 0, -2, 1, -1, 1, 1], 18), ([1, 0, -1, -1, -1, 1, 2], 18), ([1, 0, -1, -1, -1, 2, 1], 9), ([1, 0, -1, -1, 0, 1, 1], 9), ([1, 0, -1, 0, -1, 0, 2], -18), ([1, 0, -1, 0, 0, 0, 1], 18), ([1, 0, -1, 0, 0, 1, 0], 9), ([1, 0, -1, 1, -2, 1, 1], 9), ([1, 0, 0, -1, -1, 1, 1], -9), ([1, 0, 0, 0, -2, 1, 1], -9), ([1, 0, 0, 0, -1, 0, 1], 18), ([1, 0, 0, 0, -1, 1, 0], 9), ([1, 1, -2, 0, -1, 1, 1], 9), ([1, 1, -1, -1, -1, 1, 1], -9), ([1, 1, -1, 0, -2, 1, 1], 18)]

def combined134 : Sparse := combined134_part0 ++ combined134_part1

def combined135 : Sparse := [([0, -1, -1, 0, 0, 1, 1], -18), ([0, -1, 0, 0, -1, 1, 1], -18), ([0, 0, -2, 0, -1, 1, 2], -18), ([0, 0, -2, 0, -1, 2, 1], -18), ([0, 0, -1, -1, 0, 1, 1], -18), ([0, 0, -1, 0, -2, 1, 2], -18), ([0, 0, -1, 0, -2, 2, 1], -18), ([0, 0, -1, 1, -1, 0, 1], -18), ([0, 0, -1, 1, -1, 1, 0], -18), ([0, 0, 0, -1, -1, 1, 1], -18), ([0, 1, -1, 0, -1, 0, 1], -18), ([0, 1, -1, 0, -1, 1, 0], -18), ([1, -1, -1, 0, -1, 1, 2], 18), ([1, -1, -1, 0, -1, 2, 1], 18), ([1, 0, -2, 1, -1, 1, 1], 18), ([1, 0, -1, -1, -1, 1, 2], 18), ([1, 0, -1, -1, -1, 2, 1], 18), ([1, 0, -1, 0, 0, 0, 1], 18), ([1, 0, -1, 0, 0, 1, 0], 18), ([1, 0, -1, 1, -2, 1, 1], 18), ([1, 0, 0, 0, -1, 0, 1], 18), ([1, 0, 0, 0, -1, 1, 0], 18), ([1, 1, -2, 0, -1, 1, 1], 18), ([1, 1, -1, 0, -2, 1, 1], 18)]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined136_part0 : Sparse := [([0, -1, -1, 0, 1, 0, 1], -36), ([0, -1, -1, 1, 1, -1, 1], -27), ([0, -1, 0, 0, 1, -1, 1], 27), ([0, 0, -2, 0, 2, -1, 1], -36), ([0, 0, -1, -1, 1, -1, 2], -9), ([0, 0, -1, 0, 1, -2, 2], -27), ([0, 0, -1, 0, 2, -2, 1], 27), ([0, 0, -1, 0, 2, -1, 0], -27), ([0, 0, -1, 1, 0, -1, 1], -36), ([0, 0, -1, 1, 1, -2, 1], -9), ([0, 0, -1, 1, 1, -1, 0], 36), ([0, 0, 0, -1, 1, -1, 1], -27), ([0, 0, 0, 0, 0, -1, 1], 9), ([0, 0, 0, 0, 1, -2, 1], -36), ([0, 0, 0, 0, 1, -1, 0], -9), ([0, 1, -1, 0, 0, -1, 1], -9), ([0, 1, -1, 0, 1, -2, 1], 9), ([0, 1, -1, 0, 1, -1, 0], -36), ([1, -1, -1, 0, 1, -1, 2], -9), ([1, -1, -1, 0, 2, -1, 1], -9), ([1, -1, -1, 1, 1, -1, 1], -27), ([1, -1, 0, 0, 1, -1, 1], 27), ([1, 0, -2, 0, 1, -1, 2], -36), ([1, 0, -2, 0, 1, 0, 1], 18)]

def combined136_part1 : Sparse := [([1, 0, -1, -1, 1, 0, 1], -36), ([1, 0, -1, -1, 2, -1, 1], -9), ([1, 0, -1, 0, 0, -1, 2], 27), ([1, 0, -1, 0, 2, -2, 1], 27), ([1, 0, -1, 0, 2, -1, 0], -27), ([1, 0, -1, 1, 0, -1, 1], -9), ([1, 0, -1, 1, 1, -2, 1], -9), ([1, 0, -1, 1, 1, -1, 0], 27), ([1, 0, 0, 0, 1, -2, 1], -36), ([1, 0, 0, 0, 1, -1, 0], -9), ([1, 1, -1, -1, 1, -1, 1], 27), ([1, 1, -1, 0, 0, -1, 1], -36), ([1, 1, -1, 0, 1, -1, 0], -9)]

def combined136 : Sparse := combined136_part0 ++ combined136_part1

def combined137_part0 : Sparse := [([0, -1, -1, 0, 1, -1, 2], 9), ([0, -1, -1, 0, 1, 0, 1], -27), ([0, -1, -1, 1, 1, -1, 1], -18), ([0, -1, 0, 0, 1, -1, 1], 18), ([0, 0, -2, 0, 2, -1, 1], -36), ([0, 0, -2, 1, 1, -1, 1], 9), ([0, 0, -1, -1, 1, -1, 2], -9), ([0, 0, -1, -1, 1, 0, 1], 9), ([0, 0, -1, 0, 1, -2, 2], -18), ([0, 0, -1, 0, 2, -2, 1], 27), ([0, 0, -1, 0, 2, -1, 0], -9), ([0, 0, -1, 1, 0, -1, 1], -27), ([0, 0, -1, 1, 1, -2, 1], -18), ([0, 0, -1, 1, 1, -1, 0], 36), ([0, 0, 0, -1, 1, -1, 1], -18), ([0, 0, 0, 0, 0, -1, 1], 18), ([0, 0, 0, 0, 1, -2, 1], -27), ([0, 0, 0, 0, 1, -1, 0], -9), ([0, 1, -2, 0, 1, -1, 1], 9), ([0, 1, -1, 0, 0, -1, 1], -9), ([0, 1, -1, 0, 1, -2, 1], 18), ([0, 1, -1, 0, 1, -1, 0], -36), ([1, -1, -1, 0, 1, -1, 2], -9), ([1, -1, -1, 0, 1, 0, 1], 9)]

def combined137_part1 : Sparse := [([1, -1, -1, 0, 2, -1, 1], -9), ([1, -1, -1, 1, 1, -1, 1], -18), ([1, -1, 0, 0, 1, -1, 1], 27), ([1, 0, -2, 0, 1, -1, 2], -27), ([1, 0, -2, 0, 1, 0, 1], 9), ([1, 0, -2, 1, 1, -1, 1], 9), ([1, 0, -1, -1, 1, -1, 2], 9), ([1, 0, -1, -1, 1, 0, 1], -27), ([1, 0, -1, -1, 2, -1, 1], -9), ([1, 0, -1, 0, 0, -1, 2], 27), ([1, 0, -1, 0, 0, 0, 1], 9), ([1, 0, -1, 0, 2, -2, 1], 27), ([1, 0, -1, 0, 2, -1, 0], -9), ([1, 0, -1, 1, 0, -1, 1], -9), ([1, 0, -1, 1, 1, -2, 1], -9), ([1, 0, -1, 1, 1, -1, 0], 27), ([1, 0, 0, -1, 1, -1, 1], 9), ([1, 0, 0, 0, 1, -2, 1], -27), ([1, 0, 0, 0, 1, -1, 0], -9), ([1, 1, -2, 0, 1, -1, 1], 9), ([1, 1, -1, -1, 1, -1, 1], 18), ([1, 1, -1, 0, 0, -1, 1], -27), ([1, 1, -1, 0, 1, -2, 1], 9), ([1, 1, -1, 0, 1, -1, 0], -9)]

def combined137 : Sparse := combined137_part0 ++ combined137_part1

def combined138_part0 : Sparse := [([0, -1, -1, 0, 1, -1, 2], 18), ([0, -1, -1, 0, 1, 0, 1], -18), ([0, -1, -1, 0, 2, -1, 1], -9), ([0, -1, -1, 1, 1, -1, 1], -9), ([0, -1, 0, 0, 1, -1, 1], 18), ([0, 0, -2, 0, 2, -1, 1], -27), ([0, 0, -2, 1, 1, -1, 1], 18), ([0, 0, -1, -1, 1, 0, 1], 9), ([0, 0, -1, -1, 2, -1, 1], 9), ([0, 0, -1, 0, 1, -2, 2], -18), ([0, 0, -1, 0, 1, 0, 0], 9), ([0, 0, -1, 0, 2, -2, 1], 27), ([0, 0, -1, 1, 0, -1, 1], -18), ([0, 0, -1, 1, 1, -2, 1], -18), ([0, 0, -1, 1, 1, -1, 0], 27), ([0, 0, 0, -1, 1, -1, 1], -18), ([0, 0, 0, 0, 0, -1, 1], 18), ([0, 0, 0, 0, 1, -2, 1], -9), ([0, 0, 0, 0, 1, -1, 0], -9), ([0, 1, -2, 0, 1, -1, 1], 9), ([0, 1, -1, 0, 1, -2, 1], 18), ([0, 1, -1, 0, 1, -1, 0], -27), ([1, -1, -1, 0, 1, 0, 1], 9), ([1, -1, -1, 0, 2, -1, 1], -9)]

def combined138_part1 : Sparse := [([1, -1, -1, 1, 1, -1, 1], -9), ([1, -1, 0, 0, 1, -1, 1], 27), ([1, 0, -2, 0, 1, -1, 2], -18), ([1, 0, -2, 0, 1, 0, 1], 9), ([1, 0, -2, 1, 1, -1, 1], 9), ([1, 0, -1, -1, 1, -1, 2], 18), ([1, 0, -1, -1, 1, 0, 1], -18), ([1, 0, -1, 0, 0, -1, 2], 18), ([1, 0, -1, 0, 0, 0, 1], 18), ([1, 0, -1, 0, 2, -2, 1], 27), ([1, 0, -1, 1, 1, -2, 1], -9), ([1, 0, -1, 1, 1, -1, 0], 27), ([1, 0, 0, -1, 1, -1, 1], 9), ([1, 0, 0, 0, 1, -2, 1], -9), ([1, 0, 0, 0, 1, -1, 0], -9), ([1, 1, -2, 0, 1, -1, 1], 18), ([1, 1, -1, -1, 1, -1, 1], 9), ([1, 1, -1, 0, 0, -1, 1], -18), ([1, 1, -1, 0, 1, -2, 1], 9)]

def combined138 : Sparse := combined138_part0 ++ combined138_part1

def combined139_part0 : Sparse := [([0, -1, -1, 0, 1, -1, 2], 18), ([0, -1, -1, 0, 1, 0, 1], -18), ([0, -1, -1, 0, 2, -1, 1], -18), ([0, -1, 0, 0, 1, -1, 1], 18), ([0, 0, -2, 0, 2, -1, 1], -18), ([0, 0, -2, 1, 1, -1, 1], 18), ([0, 0, -1, -1, 2, -1, 1], 18), ([0, 0, -1, 0, 1, -2, 2], -18), ([0, 0, -1, 0, 1, 0, 0], 18), ([0, 0, -1, 0, 2, -2, 1], 18), ([0, 0, -1, 1, 0, -1, 1], -18), ([0, 0, -1, 1, 1, -2, 1], -18), ([0, 0, -1, 1, 1, -1, 0], 18), ([0, 0, 0, -1, 1, -1, 1], -18), ([0, 0, 0, 0, 0, -1, 1], 18), ([0, 0, 0, 0, 1, -1, 0], -18), ([0, 1, -1, 0, 1, -2, 1], 18), ([0, 1, -1, 0, 1, -1, 0], -18), ([1, -1, -1, 0, 2, -1, 1], -18), ([1, -1, 0, 0, 1, -1, 1], 18), ([1, 0, -2, 0, 1, -1, 2], -18), ([1, 0, -1, -1, 1, -1, 2], 18), ([1, 0, -1, -1, 1, 0, 1], -18), ([1, 0, -1, 0, 0, 0, 1], 18)]

def combined139_part1 : Sparse := [([1, 0, -1, 0, 2, -2, 1], 18), ([1, 0, -1, 1, 1, -2, 1], -18), ([1, 0, -1, 1, 1, -1, 0], 18), ([1, 0, 0, 0, 1, -1, 0], -18), ([1, 1, -2, 0, 1, -1, 1], 18), ([1, 1, -1, 0, 0, -1, 1], -18)]

def combined139 : Sparse := combined139_part0 ++ combined139_part1

def combined140_part0 : Sparse := [([0, -1, -1, 0, 1, 2, -1], -9), ([0, -1, 0, 0, 1, 1, -1], -27), ([0, 0, -2, 0, 2, 1, -1], -36), ([0, 0, -1, -1, 1, 1, 0], -36), ([0, 0, -1, 0, 1, 2, -2], -27), ([0, 0, -1, 0, 2, 0, -1], -27), ([0, 0, -1, 0, 2, 1, -2], 27), ([0, 0, -1, 1, 0, 1, -1], -9), ([0, 0, -1, 1, 1, 0, -1], -36), ([0, 0, -1, 1, 1, 1, -2], 9), ([0, 0, 0, -1, 1, 1, -1], 27), ([0, 0, 0, 0, 0, 1, -1], 9), ([0, 0, 0, 0, 1, 0, -1], -9), ([0, 0, 0, 0, 1, 1, -2], -36), ([0, 1, -1, -1, 1, 1, -1], -27), ([0, 1, -1, 0, 0, 1, -1], -36), ([0, 1, -1, 0, 1, 0, -1], 36), ([0, 1, -1, 0, 1, 1, -2], -9), ([1, -1, -1, 0, 1, 1, 0], -36), ([1, -1, -1, 0, 2, 1, -1], -9), ([1, -1, -1, 1, 1, 1, -1], 27), ([1, 0, -2, 0, 1, 1, 0], 18), ([1, 0, -2, 0, 1, 2, -1], -36), ([1, 0, -1, -1, 1, 2, -1], -9)]

def combined140_part1 : Sparse := [([1, 0, -1, -1, 2, 1, -1], -9), ([1, 0, -1, 0, 0, 2, -1], 27), ([1, 0, -1, 0, 2, 0, -1], -27), ([1, 0, -1, 0, 2, 1, -2], 27), ([1, 0, -1, 1, 0, 1, -1], -36), ([1, 0, -1, 1, 1, 0, -1], -9), ([1, 0, 0, -1, 1, 1, -1], 27), ([1, 0, 0, 0, 1, 0, -1], -9), ([1, 0, 0, 0, 1, 1, -2], -36), ([1, 1, -1, -1, 1, 1, -1], -27), ([1, 1, -1, 0, 0, 1, -1], -9), ([1, 1, -1, 0, 1, 0, -1], 27), ([1, 1, -1, 0, 1, 1, -2], -9)]

def combined140 : Sparse := combined140_part0 ++ combined140_part1

def combined141_part0 : Sparse := [([0, -1, -1, 0, 1, 1, 0], 9), ([0, -1, -1, 0, 1, 2, -1], -9), ([0, -1, 0, 0, 1, 1, -1], -18), ([0, 0, -2, 0, 2, 1, -1], -36), ([0, 0, -2, 1, 1, 1, -1], 9), ([0, 0, -1, -1, 1, 1, 0], -27), ([0, 0, -1, -1, 1, 2, -1], 9), ([0, 0, -1, 0, 1, 2, -2], -18), ([0, 0, -1, 0, 2, 0, -1], -9), ([0, 0, -1, 0, 2, 1, -2], 27), ([0, 0, -1, 1, 0, 1, -1], -9), ([0, 0, -1, 1, 1, 0, -1], -36), ([0, 0, -1, 1, 1, 1, -2], 18), ([0, 0, 0, -1, 1, 1, -1], 18), ([0, 0, 0, 0, 0, 1, -1], 18), ([0, 0, 0, 0, 1, 0, -1], -9), ([0, 0, 0, 0, 1, 1, -2], -27), ([0, 1, -2, 0, 1, 1, -1], 9), ([0, 1, -1, -1, 1, 1, -1], -18), ([0, 1, -1, 0, 0, 1, -1], -27), ([0, 1, -1, 0, 1, 0, -1], 36), ([0, 1, -1, 0, 1, 1, -2], -18), ([1, -1, -1, 0, 1, 1, 0], -27), ([1, -1, -1, 0, 1, 2, -1], 9)]

def combined141_part1 : Sparse := [([1, -1, -1, 0, 2, 1, -1], -9), ([1, -1, -1, 1, 1, 1, -1], 18), ([1, -1, 0, 0, 1, 1, -1], 9), ([1, 0, -2, 0, 1, 1, 0], 9), ([1, 0, -2, 0, 1, 2, -1], -27), ([1, 0, -2, 1, 1, 1, -1], 9), ([1, 0, -1, -1, 1, 1, 0], 9), ([1, 0, -1, -1, 1, 2, -1], -9), ([1, 0, -1, -1, 2, 1, -1], -9), ([1, 0, -1, 0, 0, 1, 0], 9), ([1, 0, -1, 0, 0, 2, -1], 27), ([1, 0, -1, 0, 2, 0, -1], -9), ([1, 0, -1, 0, 2, 1, -2], 27), ([1, 0, -1, 1, 0, 1, -1], -27), ([1, 0, -1, 1, 1, 0, -1], -9), ([1, 0, -1, 1, 1, 1, -2], 9), ([1, 0, 0, -1, 1, 1, -1], 27), ([1, 0, 0, 0, 1, 0, -1], -9), ([1, 0, 0, 0, 1, 1, -2], -27), ([1, 1, -2, 0, 1, 1, -1], 9), ([1, 1, -1, -1, 1, 1, -1], -18), ([1, 1, -1, 0, 0, 1, -1], -9), ([1, 1, -1, 0, 1, 0, -1], 27), ([1, 1, -1, 0, 1, 1, -2], -9)]

def combined141 : Sparse := combined141_part0 ++ combined141_part1

def combined142_part0 : Sparse := [([0, -1, -1, 0, 1, 2, -1], -9), ([0, -1, -1, 0, 2, 1, -1], 9), ([0, -1, 0, 0, 1, 1, -1], -18), ([0, 0, -2, 0, 2, 1, -1], -27), ([0, 0, -1, -1, 1, 1, 0], -27), ([0, 0, -1, -1, 1, 2, -1], 9), ([0, 0, -1, -1, 2, 1, -1], -9), ([0, 0, -1, 0, 1, 0, 0], 9), ([0, 0, -1, 0, 1, 2, -2], -18), ([0, 0, -1, 0, 2, 0, -1], -9), ([0, 0, -1, 0, 2, 1, -2], 18), ([0, 0, -1, 1, 0, 1, -1], -9), ([0, 0, -1, 1, 1, 0, -1], -27), ([0, 0, -1, 1, 1, 1, -2], 18), ([0, 0, 0, -1, 1, 1, -1], 18), ([0, 0, 0, 0, 0, 1, -1], 18), ([0, 0, 0, 0, 1, 0, -1], -18), ([0, 0, 0, 0, 1, 1, -2], -18), ([0, 1, -2, 0, 1, 1, -1], 9), ([0, 1, -1, -1, 1, 1, -1], -9), ([0, 1, -1, 0, 0, 1, -1], -27), ([0, 1, -1, 0, 1, 0, -1], 27), ([0, 1, -1, 0, 1, 1, -2], -18), ([1, -1, -1, 0, 1, 1, 0], -27)]

def combined142_part1 : Sparse := [([1, -1, -1, 0, 1, 2, -1], 9), ([1, -1, -1, 0, 2, 1, -1], -9), ([1, -1, -1, 1, 1, 1, -1], 9), ([1, 0, -2, 0, 1, 2, -1], -27), ([1, 0, -2, 1, 1, 1, -1], 9), ([1, 0, -1, -1, 1, 2, -1], -9), ([1, 0, -1, -1, 2, 1, -1], -18), ([1, 0, -1, 0, 0, 1, 0], 9), ([1, 0, -1, 0, 0, 2, -1], 9), ([1, 0, -1, 0, 2, 0, -1], -9), ([1, 0, -1, 0, 2, 1, -2], 18), ([1, 0, -1, 1, 0, 1, -1], -27), ([1, 0, -1, 1, 1, 0, -1], -9), ([1, 0, 0, -1, 1, 1, -1], 18), ([1, 0, 0, 0, 1, 0, -1], -18), ([1, 0, 0, 0, 1, 1, -2], -18), ([1, 1, -1, -1, 1, 1, -1], -9), ([1, 1, -1, 0, 0, 1, -1], -9), ([1, 1, -1, 0, 1, 0, -1], 18), ([1, 1, -1, 0, 1, 1, -2], -18)]

def combined142 : Sparse := combined142_part0 ++ combined142_part1

def combined143_part0 : Sparse := [([0, -1, -1, 0, 2, 1, -1], 18), ([0, -1, 0, 0, 1, 1, -1], -18), ([0, 0, -2, 0, 2, 1, -1], -18), ([0, 0, -1, -1, 1, 1, 0], -18), ([0, 0, -1, -1, 1, 2, -1], 18), ([0, 0, -1, -1, 2, 1, -1], -18), ([0, 0, -1, 0, 1, 0, 0], 18), ([0, 0, -1, 0, 1, 2, -2], -18), ([0, 0, -1, 0, 2, 1, -2], 18), ([0, 0, -1, 1, 1, 0, -1], -18), ([0, 0, -1, 1, 1, 1, -2], 18), ([0, 0, 0, -1, 1, 1, -1], 18), ([0, 0, 0, 0, 0, 1, -1], 18), ([0, 0, 0, 0, 1, 0, -1], -18), ([0, 1, -2, 0, 1, 1, -1], 18), ([0, 1, -1, 0, 0, 1, -1], -18), ([0, 1, -1, 0, 1, 0, -1], 18), ([0, 1, -1, 0, 1, 1, -2], -18), ([1, -1, -1, 0, 1, 1, 0], -18), ([1, -1, -1, 0, 1, 2, -1], 18), ([1, 0, -2, 0, 1, 2, -1], -18), ([1, 0, -2, 1, 1, 1, -1], 18), ([1, 0, -1, -1, 2, 1, -1], -18), ([1, 0, -1, 0, 0, 1, 0], 18)]

def combined143_part1 : Sparse := [([1, 0, -1, 0, 2, 1, -2], 18), ([1, 0, -1, 1, 0, 1, -1], -18), ([1, 0, 0, -1, 1, 1, -1], 18), ([1, 0, 0, 0, 1, 0, -1], -18), ([1, 1, -1, 0, 1, 0, -1], 18), ([1, 1, -1, 0, 1, 1, -2], -18)]

def combined143 : Sparse := combined143_part0 ++ combined143_part1

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined144_part0 : Sparse := [([0, -1, -1, 1, -1, 0, 2], -9), ([0, -1, -1, 1, -1, 1, 1], -27), ([0, -1, -1, 1, 0, 0, 1], 36), ([0, -1, -1, 2, -1, 0, 1], 9), ([0, -1, 0, 1, -1, 0, 1], -27), ([0, 0, -2, 1, -1, 0, 2], 36), ([0, 0, -2, 1, 0, 0, 1], -18), ([0, 0, -2, 2, -1, 0, 1], -36), ([0, 0, -1, 0, -1, 0, 2], -27), ([0, 0, -1, 0, -1, 1, 1], 27), ([0, 0, -1, 1, -2, 0, 2], -27), ([0, 0, -1, 1, -2, 1, 1], 9), ([0, 0, -1, 1, -1, -1, 2], 9), ([0, 0, -1, 1, -1, 1, 0], -27), ([0, 0, -1, 1, 0, -1, 1], -36), ([0, 0, -1, 2, -1, -1, 1], 9), ([0, 0, 0, 0, -1, 0, 1], 9), ([0, 1, -1, 0, -1, 0, 1], -27), ([0, 1, -1, 1, -1, 0, 0], 9), ([1, -1, -1, 1, -1, 1, 1], -27), ([1, -1, -1, 1, 0, 0, 1], 36), ([1, -1, -1, 2, -1, 0, 1], 9), ([1, 0, -2, 1, -1, 0, 2], 36), ([1, 0, -2, 1, 0, 0, 1], -18)]

def combined144_part1 : Sparse := [([1, 0, -1, 0, -1, 0, 2], -27), ([1, 0, -1, 0, -1, 1, 1], 36), ([1, 0, -1, 1, -1, -1, 2], 9), ([1, 0, -1, 1, -1, 1, 0], 9), ([1, 0, -1, 2, -2, 0, 1], -27), ([1, 0, -1, 2, -1, -1, 1], 9), ([1, 0, -1, 2, -1, 0, 0], 27), ([1, 0, 0, 1, -2, 0, 1], 36), ([1, 0, 0, 1, -1, -1, 1], -27), ([1, 0, 0, 1, -1, 0, 0], 9), ([1, 1, -1, 0, -1, 0, 1], 9), ([1, 1, -1, 1, -2, 0, 1], 9), ([1, 1, -1, 1, -1, -1, 1], 27), ([1, 1, -1, 1, -1, 0, 0], -27)]

def combined144 : Sparse := combined144_part0 ++ combined144_part1

def combined145_part0 : Sparse := [([0, -1, -1, 1, -1, 0, 2], -18), ([0, -1, -1, 1, -1, 1, 1], -18), ([0, -1, -1, 1, 0, 0, 1], 36), ([0, -1, -1, 2, -1, 0, 1], 9), ([0, -1, 0, 1, -1, 0, 1], -27), ([0, 0, -2, 1, -1, 0, 2], 27), ([0, 0, -2, 1, 0, 0, 1], -9), ([0, 0, -2, 2, -1, 0, 1], -36), ([0, 0, -1, 0, -1, 0, 2], -27), ([0, 0, -1, 0, -1, 1, 1], 18), ([0, 0, -1, 0, 0, 0, 1], -9), ([0, 0, -1, 1, -2, 0, 2], -18), ([0, 0, -1, 1, -2, 1, 1], 9), ([0, 0, -1, 1, -1, -1, 2], 18), ([0, 0, -1, 1, -1, 1, 0], -27), ([0, 0, -1, 1, 0, -1, 1], -36), ([0, 0, -1, 2, -1, -1, 1], 9), ([0, 0, 0, 0, -1, 0, 1], 18), ([0, 0, 0, 1, -1, -1, 1], -9), ([0, 1, -1, 0, -1, 0, 1], -18), ([0, 1, -1, 1, -2, 0, 1], -9), ([0, 1, -1, 1, -1, 0, 0], 9), ([1, -1, -1, 1, -1, 0, 2], -9), ([1, -1, -1, 1, -1, 1, 1], -18)]

def combined145_part1 : Sparse := [([1, -1, -1, 1, 0, 0, 1], 27), ([1, -1, -1, 2, -1, 0, 1], 9), ([1, -1, 0, 1, -1, 0, 1], -9), ([1, 0, -2, 1, -1, 0, 2], 27), ([1, 0, -2, 1, -1, 1, 1], -9), ([1, 0, -2, 1, 0, 0, 1], -9), ([1, 0, -1, 0, -1, 0, 2], -27), ([1, 0, -1, 0, -1, 1, 1], 27), ([1, 0, -1, 0, 0, 0, 1], -9), ([1, 0, -1, 1, -2, 1, 1], -9), ([1, 0, -1, 1, -1, -1, 2], 9), ([1, 0, -1, 1, -1, 1, 0], 9), ([1, 0, -1, 1, 0, -1, 1], -9), ([1, 0, -1, 2, -2, 0, 1], -27), ([1, 0, -1, 2, -1, -1, 1], 9), ([1, 0, -1, 2, -1, 0, 0], 9), ([1, 0, 0, 1, -2, 0, 1], 27), ([1, 0, 0, 1, -1, -1, 1], -27), ([1, 0, 0, 1, -1, 0, 0], 9), ([1, 1, -2, 1, -1, 0, 1], -9), ([1, 1, -1, 0, -1, 0, 1], 9), ([1, 1, -1, 1, -2, 0, 1], 9), ([1, 1, -1, 1, -1, -1, 1], 18), ([1, 1, -1, 1, -1, 0, 0], -27)]

def combined145 : Sparse := combined145_part0 ++ combined145_part1

def combined146_part0 : Sparse := [([0, -1, -1, 1, -1, 0, 2], -18), ([0, -1, -1, 1, -1, 1, 1], -9), ([0, -1, -1, 1, 0, 0, 1], 27), ([0, -1, -1, 2, -1, 0, 1], 9), ([0, -1, 0, 1, -1, 0, 1], -27), ([0, 0, -2, 1, -1, 0, 2], 18), ([0, 0, -2, 1, -1, 1, 1], -9), ([0, 0, -2, 1, 0, 0, 1], -9), ([0, 0, -2, 2, -1, 0, 1], -27), ([0, 0, -1, 0, -1, 0, 2], -18), ([0, 0, -1, 0, -1, 1, 1], 18), ([0, 0, -1, 0, 0, 0, 1], -18), ([0, 0, -1, 1, -2, 0, 2], -18), ([0, 0, -1, 1, -2, 1, 1], 9), ([0, 0, -1, 1, -1, -1, 2], 18), ([0, 0, -1, 1, -1, 1, 0], -27), ([0, 0, -1, 1, 0, -1, 1], -27), ([0, 0, -1, 1, 0, 0, 0], 9), ([0, 0, 0, 0, -1, 0, 1], 18), ([0, 0, 0, 1, -1, -1, 1], -9), ([0, 1, -2, 1, -1, 0, 1], 9), ([0, 1, -1, 0, -1, 0, 1], -18), ([0, 1, -1, 1, -2, 0, 1], -9), ([1, -1, -1, 1, -1, 0, 2], -18)]

def combined146_part1 : Sparse := [([1, -1, -1, 1, -1, 1, 1], -9), ([1, -1, -1, 1, 0, 0, 1], 18), ([1, -1, 0, 1, -1, 0, 1], -9), ([1, 0, -2, 1, -1, 0, 2], 18), ([1, 0, -2, 1, -1, 1, 1], -18), ([1, 0, -2, 1, 0, 0, 1], -9), ([1, 0, -1, 0, -1, 0, 2], -18), ([1, 0, -1, 0, -1, 1, 1], 18), ([1, 0, -1, 0, 0, 0, 1], -18), ([1, 0, -1, 1, -2, 1, 1], -9), ([1, 0, -1, 1, 0, -1, 1], -9), ([1, 0, -1, 2, -2, 0, 1], -27), ([1, 0, -1, 2, -1, -1, 1], 9), ([1, 0, 0, 1, -2, 0, 1], 9), ([1, 0, 0, 1, -1, -1, 1], -27), ([1, 0, 0, 1, -1, 0, 0], 9), ([1, 1, -2, 1, -1, 0, 1], -9), ([1, 1, -1, 1, -2, 0, 1], 9), ([1, 1, -1, 1, -1, -1, 1], 9), ([1, 1, -1, 1, -1, 0, 0], -27)]

def combined146 : Sparse := combined146_part0 ++ combined146_part1

def combined147_part0 : Sparse := [([0, -1, -1, 1, -1, 0, 2], -18), ([0, -1, -1, 1, 0, 0, 1], 18), ([0, -1, -1, 2, -1, 0, 1], 18), ([0, -1, 0, 1, -1, 0, 1], -18), ([0, 0, -2, 1, -1, 0, 2], 18), ([0, 0, -2, 1, -1, 1, 1], -18), ([0, 0, -2, 2, -1, 0, 1], -18), ([0, 0, -1, 0, -1, 1, 1], 18), ([0, 0, -1, 0, 0, 0, 1], -18), ([0, 0, -1, 1, -2, 0, 2], -18), ([0, 0, -1, 1, -2, 1, 1], 18), ([0, 0, -1, 1, -1, -1, 2], 18), ([0, 0, -1, 1, -1, 1, 0], -18), ([0, 0, -1, 1, 0, -1, 1], -18), ([0, 0, -1, 1, 0, 0, 0], 18), ([0, 0, 0, 0, -1, 0, 1], 18), ([0, 1, -2, 1, -1, 0, 1], 18), ([0, 1, -1, 0, -1, 0, 1], -18), ([1, -1, -1, 1, -1, 0, 2], -18), ([1, -1, -1, 1, 0, 0, 1], 18), ([1, 0, -2, 1, -1, 0, 2], 18), ([1, 0, -2, 1, -1, 1, 1], -18), ([1, 0, -1, 0, -1, 1, 1], 18), ([1, 0, -1, 0, 0, 0, 1], -18)]

def combined147_part1 : Sparse := [([1, 0, -1, 2, -2, 0, 1], -18), ([1, 0, -1, 2, -1, -1, 1], 18), ([1, 0, 0, 1, -1, -1, 1], -18), ([1, 0, 0, 1, -1, 0, 0], 18), ([1, 1, -1, 1, -2, 0, 1], 18), ([1, 1, -1, 1, -1, 0, 0], -18)]

def combined147 : Sparse := combined147_part0 ++ combined147_part1

def combined148_part0 : Sparse := [([0, -1, -1, 1, -1, 1, 1], -27), ([0, -1, -1, 1, 0, 1, 0], -36), ([0, -1, 0, 1, -1, 1, 0], 27), ([0, 0, -2, 1, -1, 2, 0], -36), ([0, 0, -1, 0, -1, 1, 1], 36), ([0, 0, -1, 0, -1, 2, 0], -27), ([0, 0, -1, 1, -2, 1, 1], -9), ([0, 0, -1, 1, -2, 2, 0], 27), ([0, 0, -1, 1, -1, 0, 1], -36), ([0, 0, -1, 2, -2, 1, 0], -27), ([0, 0, -1, 2, -1, 1, -1], -9), ([0, 0, 0, 0, -1, 1, 0], -9), ([0, 0, 0, 1, -2, 1, 0], -36), ([0, 0, 0, 1, -1, 0, 0], 9), ([0, 0, 0, 1, -1, 1, -1], -27), ([0, 1, -1, 0, -1, 1, 0], -36), ([0, 1, -1, 1, -2, 1, 0], 9), ([0, 1, -1, 1, -1, 0, 0], -9), ([1, -1, -1, 1, -1, 1, 1], -27), ([1, -1, -1, 1, -1, 2, 0], -9), ([1, -1, -1, 2, -1, 1, 0], -9), ([1, -1, 0, 1, -1, 1, 0], 27), ([1, 0, -2, 1, 0, 1, 0], 18), ([1, 0, -2, 2, -1, 1, 0], -36)]

def combined148_part1 : Sparse := [([1, 0, -1, 0, -1, 1, 1], 27), ([1, 0, -1, 0, -1, 2, 0], -27), ([1, 0, -1, 1, -2, 1, 1], -9), ([1, 0, -1, 1, -2, 2, 0], 27), ([1, 0, -1, 1, -1, 0, 1], -9), ([1, 0, -1, 1, -1, 2, -1], -9), ([1, 0, -1, 1, 0, 1, -1], -36), ([1, 0, -1, 2, -1, 0, 0], 27), ([1, 0, 0, 0, -1, 1, 0], -9), ([1, 0, 0, 1, -2, 1, 0], -36), ([1, 1, -1, 0, -1, 1, 0], -9), ([1, 1, -1, 1, -1, 0, 0], -36), ([1, 1, -1, 1, -1, 1, -1], 27)]

def combined148 : Sparse := combined148_part0 ++ combined148_part1

def combined149_part0 : Sparse := [([0, -1, -1, 1, -1, 1, 1], -18), ([0, -1, -1, 1, -1, 2, 0], -9), ([0, -1, -1, 1, 0, 1, 0], -36), ([0, -1, 0, 1, -1, 1, 0], 27), ([0, 0, -2, 1, -1, 2, 0], -27), ([0, 0, -1, 0, -1, 1, 1], 27), ([0, 0, -1, 0, -1, 2, 0], -27), ([0, 0, -1, 0, 0, 1, 0], 9), ([0, 0, -1, 1, -2, 1, 1], -9), ([0, 0, -1, 1, -2, 2, 0], 18), ([0, 0, -1, 1, -1, 0, 1], -36), ([0, 0, -1, 1, -1, 2, -1], 9), ([0, 0, -1, 1, 0, 1, -1], -9), ([0, 0, -1, 2, -2, 1, 0], -27), ([0, 0, -1, 2, -1, 1, -1], -9), ([0, 0, 0, 0, -1, 1, 0], -18), ([0, 0, 0, 1, -2, 1, 0], -27), ([0, 0, 0, 1, -1, 0, 0], 9), ([0, 0, 0, 1, -1, 1, -1], -27), ([0, 1, -2, 1, -1, 1, 0], -9), ([0, 1, -1, 0, -1, 1, 0], -27), ([0, 1, -1, 1, -2, 1, 0], 9), ([0, 1, -1, 1, -1, 0, 0], -9), ([1, -1, -1, 1, -1, 1, 1], -18)]

def combined149_part1 : Sparse := [([1, -1, -1, 1, -1, 2, 0], -18), ([1, -1, -1, 1, 0, 1, 0], -9), ([1, -1, -1, 2, -1, 1, 0], -9), ([1, -1, 0, 1, -1, 1, 0], 18), ([1, 0, -2, 1, -1, 1, 1], -9), ([1, 0, -2, 1, 0, 1, 0], 9), ([1, 0, -2, 2, -1, 1, 0], -36), ([1, 0, -1, 0, -1, 1, 1], 18), ([1, 0, -1, 0, -1, 2, 0], -27), ([1, 0, -1, 1, -2, 1, 1], -18), ([1, 0, -1, 1, -2, 2, 0], 18), ([1, 0, -1, 1, -1, 0, 1], -9), ([1, 0, -1, 1, -1, 2, -1], -9), ([1, 0, -1, 1, 0, 1, -1], -36), ([1, 0, -1, 2, -1, 0, 0], 9), ([1, 0, 0, 0, -1, 1, 0], -18), ([1, 0, 0, 1, -2, 1, 0], -27), ([1, 0, 0, 1, -1, 1, -1], -9), ([1, 1, -1, 0, -1, 1, 0], -9), ([1, 1, -1, 1, -2, 1, 0], -9), ([1, 1, -1, 1, -1, 0, 0], -36), ([1, 1, -1, 1, -1, 1, -1], 18)]

def combined149 : Sparse := combined149_part0 ++ combined149_part1

def combined150_part0 : Sparse := [([0, -1, -1, 1, -1, 1, 1], -9), ([0, -1, -1, 1, -1, 2, 0], -18), ([0, -1, -1, 1, 0, 1, 0], -27), ([0, -1, -1, 2, -1, 1, 0], 9), ([0, -1, 0, 1, -1, 1, 0], 27), ([0, 0, -2, 1, -1, 1, 1], 9), ([0, 0, -2, 1, -1, 2, 0], -18), ([0, 0, -1, 0, -1, 1, 1], 18), ([0, 0, -1, 0, -1, 2, 0], -18), ([0, 0, -1, 0, 0, 1, 0], 18), ([0, 0, -1, 1, -2, 1, 1], -9), ([0, 0, -1, 1, -2, 2, 0], 18), ([0, 0, -1, 1, -1, 0, 1], -27), ([0, 0, -1, 1, -1, 2, -1], 18), ([0, 0, -1, 1, 0, 1, -1], -9), ([0, 0, -1, 2, -2, 1, 0], -27), ([0, 0, 0, 0, -1, 1, 0], -18), ([0, 0, 0, 1, -2, 1, 0], -9), ([0, 0, 0, 1, -1, 0, 0], 9), ([0, 0, 0, 1, -1, 1, -1], -27), ([0, 1, -2, 1, -1, 1, 0], -9), ([0, 1, -1, 0, -1, 1, 0], -18), ([0, 1, -1, 1, -2, 1, 0], 9), ([1, -1, -1, 1, -1, 1, 1], -9)]

def combined150_part1 : Sparse := [([1, -1, -1, 1, -1, 2, 0], -18), ([1, -1, -1, 1, 0, 1, 0], -9), ([1, -1, 0, 1, -1, 1, 0], 18), ([1, 0, -2, 1, -1, 1, 1], -9), ([1, 0, -2, 1, 0, 1, 0], 9), ([1, 0, -2, 2, -1, 1, 0], -27), ([1, 0, -1, 0, -1, 1, 1], 18), ([1, 0, -1, 0, -1, 2, 0], -18), ([1, 0, -1, 1, -2, 1, 1], -18), ([1, 0, -1, 1, -2, 2, 0], 18), ([1, 0, -1, 1, 0, 0, 0], 9), ([1, 0, -1, 1, 0, 1, -1], -27), ([1, 0, -1, 2, -1, 1, -1], 9), ([1, 0, 0, 0, -1, 1, 0], -18), ([1, 0, 0, 1, -2, 1, 0], -9), ([1, 0, 0, 1, -1, 1, -1], -9), ([1, 1, -2, 1, -1, 1, 0], 9), ([1, 1, -1, 1, -2, 1, 0], -9), ([1, 1, -1, 1, -1, 0, 0], -27), ([1, 1, -1, 1, -1, 1, -1], 9)]

def combined150 : Sparse := combined150_part0 ++ combined150_part1

def combined151_part0 : Sparse := [([0, -1, -1, 1, -1, 2, 0], -18), ([0, -1, -1, 1, 0, 1, 0], -18), ([0, -1, -1, 2, -1, 1, 0], 18), ([0, -1, 0, 1, -1, 1, 0], 18), ([0, 0, -2, 1, -1, 1, 1], 18), ([0, 0, -2, 1, -1, 2, 0], -18), ([0, 0, -1, 0, -1, 1, 1], 18), ([0, 0, -1, 0, 0, 1, 0], 18), ([0, 0, -1, 1, -2, 1, 1], -18), ([0, 0, -1, 1, -2, 2, 0], 18), ([0, 0, -1, 1, -1, 0, 1], -18), ([0, 0, -1, 1, -1, 2, -1], 18), ([0, 0, -1, 2, -2, 1, 0], -18), ([0, 0, 0, 0, -1, 1, 0], -18), ([0, 0, 0, 1, -1, 0, 0], 18), ([0, 0, 0, 1, -1, 1, -1], -18), ([0, 1, -1, 0, -1, 1, 0], -18), ([0, 1, -1, 1, -2, 1, 0], 18), ([1, -1, -1, 1, -1, 2, 0], -18), ([1, -1, 0, 1, -1, 1, 0], 18), ([1, 0, -2, 2, -1, 1, 0], -18), ([1, 0, -1, 0, -1, 1, 1], 18), ([1, 0, -1, 1, -2, 1, 1], -18), ([1, 0, -1, 1, -2, 2, 0], 18)]

def combined151_part1 : Sparse := [([1, 0, -1, 1, 0, 0, 0], 18), ([1, 0, -1, 1, 0, 1, -1], -18), ([1, 0, -1, 2, -1, 1, -1], 18), ([1, 0, 0, 0, -1, 1, 0], -18), ([1, 1, -2, 1, -1, 1, 0], 18), ([1, 1, -1, 1, -1, 0, 0], -18)]

def combined151 : Sparse := combined151_part0 ++ combined151_part1

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined152_part0 : Sparse := [([0, -1, -1, 1, 0, -1, 2], 9), ([0, -1, -1, 1, 0, 0, 1], 36), ([0, -1, -1, 1, 1, -1, 1], -27), ([0, -1, -1, 2, 0, -1, 1], -9), ([0, -1, 0, 1, 0, -1, 1], -27), ([0, 0, -2, 1, 0, -1, 2], -36), ([0, 0, -2, 1, 0, 0, 1], -18), ([0, 0, -2, 2, 0, -1, 1], 36), ([0, 0, -1, 0, 1, -1, 1], -27), ([0, 0, -1, 1, -1, -1, 2], 9), ([0, 0, -1, 1, -1, 0, 1], -36), ([0, 0, -1, 1, 1, -2, 1], 9), ([0, 0, -1, 1, 1, -1, 0], 27), ([0, 0, -1, 2, -1, -1, 1], 9), ([0, 0, -1, 2, 0, -2, 1], -27), ([0, 0, -1, 2, 0, -1, 0], -27), ([0, 0, 0, 1, 0, -1, 0], 9), ([0, 1, -1, 0, 0, -1, 1], 9), ([0, 1, -1, 1, 0, -1, 0], -27), ([1, -1, -1, 1, 0, -1, 2], 9), ([1, -1, -1, 1, 0, 0, 1], 36), ([1, -1, -1, 1, 1, -1, 1], -27), ([1, 0, -2, 1, 0, 0, 1], -18), ([1, 0, -2, 2, 0, -1, 1], 36)]

def combined152_part1 : Sparse := [([1, 0, -1, 0, 0, -1, 2], 27), ([1, 0, -1, 0, 1, -1, 1], 9), ([1, 0, -1, 1, -1, -1, 2], 9), ([1, 0, -1, 1, 0, -2, 2], -27), ([1, 0, -1, 1, 1, -1, 0], 36), ([1, 0, -1, 2, -1, -1, 1], 9), ([1, 0, -1, 2, 0, -1, 0], -27), ([1, 0, 0, 0, 0, -1, 1], 9), ([1, 0, 0, 1, -1, -1, 1], -27), ([1, 0, 0, 1, 0, -2, 1], 36), ([1, 1, -1, 0, 0, -1, 1], -27), ([1, 1, -1, 1, -1, -1, 1], 27), ([1, 1, -1, 1, 0, -2, 1], 9), ([1, 1, -1, 1, 0, -1, 0], 9)]

def combined152 : Sparse := combined152_part0 ++ combined152_part1

def combined153_part0 : Sparse := [([0, -1, -1, 1, 0, -1, 2], 18), ([0, -1, -1, 1, 0, 0, 1], 27), ([0, -1, -1, 1, 1, -1, 1], -18), ([0, -1, -1, 2, 0, -1, 1], -9), ([0, -1, 0, 1, 0, -1, 1], -18), ([0, 0, -2, 1, 0, -1, 2], -27), ([0, 0, -2, 1, 0, 0, 1], -9), ([0, 0, -2, 1, 1, -1, 1], -9), ([0, 0, -2, 2, 0, -1, 1], 36), ([0, 0, -1, 0, 0, 0, 1], 9), ([0, 0, -1, 0, 1, -1, 1], -18), ([0, 0, -1, 1, -1, -1, 2], 9), ([0, 0, -1, 1, -1, 0, 1], -27), ([0, 0, -1, 1, 1, -2, 1], 18), ([0, 0, -1, 1, 1, -1, 0], 27), ([0, 0, -1, 2, -1, -1, 1], 9), ([0, 0, -1, 2, 0, -2, 1], -27), ([0, 0, -1, 2, 0, -1, 0], -9), ([0, 0, 0, 1, -1, -1, 1], 9), ([0, 0, 0, 1, 0, -1, 0], 9), ([0, 1, -2, 1, 0, -1, 1], 9), ([0, 1, -1, 0, 0, -1, 1], 9), ([0, 1, -1, 1, 0, -2, 1], 9), ([0, 1, -1, 1, 0, -1, 0], -27)]

def combined153_part1 : Sparse := [([1, -1, -1, 1, 0, -1, 2], 9), ([1, -1, -1, 1, 0, 0, 1], 36), ([1, -1, -1, 1, 1, -1, 1], -18), ([1, -1, 0, 1, 0, -1, 1], 9), ([1, 0, -2, 1, 0, 0, 1], -9), ([1, 0, -2, 2, 0, -1, 1], 36), ([1, 0, -1, 0, 0, -1, 2], 27), ([1, 0, -1, 0, 1, -1, 1], 9), ([1, 0, -1, 1, -1, -1, 2], 18), ([1, 0, -1, 1, -1, 0, 1], 9), ([1, 0, -1, 1, 0, -2, 2], -18), ([1, 0, -1, 1, 1, -2, 1], 9), ([1, 0, -1, 1, 1, -1, 0], 36), ([1, 0, -1, 2, -1, -1, 1], 9), ([1, 0, -1, 2, 0, -1, 0], -9), ([1, 0, 0, 0, 0, -1, 1], 18), ([1, 0, 0, 1, -1, -1, 1], -18), ([1, 0, 0, 1, 0, -2, 1], 27), ([1, 1, -2, 1, 0, -1, 1], 9), ([1, 1, -1, 0, 0, -1, 1], -18), ([1, 1, -1, 1, -1, -1, 1], 18), ([1, 1, -1, 1, 0, -2, 1], 18), ([1, 1, -1, 1, 0, -1, 0], 9)]

def combined153 : Sparse := combined153_part0 ++ combined153_part1

def combined154_part0 : Sparse := [([0, -1, -1, 1, 0, -1, 2], 18), ([0, -1, -1, 1, 0, 0, 1], 18), ([0, -1, -1, 1, 1, -1, 1], -9), ([0, -1, -1, 2, 0, -1, 1], -9), ([0, -1, 0, 1, 0, -1, 1], -18), ([0, 0, -2, 1, 0, -1, 2], -18), ([0, 0, -2, 1, 0, 0, 1], -9), ([0, 0, -2, 1, 1, -1, 1], -18), ([0, 0, -2, 2, 0, -1, 1], 27), ([0, 0, -1, 0, 0, 0, 1], 18), ([0, 0, -1, 0, 1, -1, 1], -18), ([0, 0, -1, 1, -1, 0, 1], -18), ([0, 0, -1, 1, 0, 0, 0], -9), ([0, 0, -1, 1, 1, -2, 1], 18), ([0, 0, -1, 1, 1, -1, 0], 27), ([0, 0, -1, 2, -1, -1, 1], 9), ([0, 0, -1, 2, 0, -2, 1], -27), ([0, 0, 0, 1, -1, -1, 1], 9), ([0, 0, 0, 1, 0, -1, 0], 9), ([0, 1, -2, 1, 0, -1, 1], 18), ([0, 1, -1, 1, 0, -2, 1], 9), ([0, 1, -1, 1, 0, -1, 0], -27), ([1, -1, -1, 1, 0, 0, 1], 27), ([1, -1, -1, 1, 1, -1, 1], -9)]

def combined154_part1 : Sparse := [([1, -1, -1, 2, 0, -1, 1], -9), ([1, -1, 0, 1, 0, -1, 1], 9), ([1, 0, -2, 1, 0, 0, 1], -9), ([1, 0, -2, 1, 1, -1, 1], -9), ([1, 0, -2, 2, 0, -1, 1], 27), ([1, 0, -1, 0, 0, -1, 2], 18), ([1, 0, -1, 1, -1, -1, 2], 18), ([1, 0, -1, 1, -1, 0, 1], 9), ([1, 0, -1, 1, 0, -2, 2], -18), ([1, 0, -1, 1, 0, 0, 0], -9), ([1, 0, -1, 1, 1, -2, 1], 9), ([1, 0, -1, 1, 1, -1, 0], 27), ([1, 0, 0, 0, 0, -1, 1], 18), ([1, 0, 0, 1, -1, -1, 1], -18), ([1, 0, 0, 1, 0, -2, 1], 9), ([1, 1, -2, 1, 0, -1, 1], 9), ([1, 1, -1, 0, 0, -1, 1], -18), ([1, 1, -1, 1, -1, -1, 1], 9), ([1, 1, -1, 1, 0, -2, 1], 18)]

def combined154 : Sparse := combined154_part0 ++ combined154_part1

def combined155_part0 : Sparse := [([0, -1, -1, 1, 0, -1, 2], 18), ([0, -1, -1, 1, 0, 0, 1], 18), ([0, -1, -1, 2, 0, -1, 1], -18), ([0, -1, 0, 1, 0, -1, 1], -18), ([0, 0, -2, 1, 0, -1, 2], -18), ([0, 0, -2, 1, 1, -1, 1], -18), ([0, 0, -2, 2, 0, -1, 1], 18), ([0, 0, -1, 0, 0, 0, 1], 18), ([0, 0, -1, 0, 1, -1, 1], -18), ([0, 0, -1, 1, -1, 0, 1], -18), ([0, 0, -1, 1, 0, 0, 0], -18), ([0, 0, -1, 1, 1, -2, 1], 18), ([0, 0, -1, 1, 1, -1, 0], 18), ([0, 0, -1, 2, -1, -1, 1], 18), ([0, 0, -1, 2, 0, -2, 1], -18), ([0, 0, 0, 1, 0, -1, 0], 18), ([0, 1, -2, 1, 0, -1, 1], 18), ([0, 1, -1, 1, 0, -1, 0], -18), ([1, -1, -1, 1, 0, 0, 1], 18), ([1, -1, -1, 2, 0, -1, 1], -18), ([1, 0, -2, 1, 1, -1, 1], -18), ([1, 0, -2, 2, 0, -1, 1], 18), ([1, 0, -1, 1, -1, -1, 2], 18), ([1, 0, -1, 1, 0, -2, 2], -18)]

def combined155_part1 : Sparse := [([1, 0, -1, 1, 0, 0, 0], -18), ([1, 0, -1, 1, 1, -1, 0], 18), ([1, 0, 0, 0, 0, -1, 1], 18), ([1, 0, 0, 1, -1, -1, 1], -18), ([1, 1, -1, 0, 0, -1, 1], -18), ([1, 1, -1, 1, 0, -2, 1], 18)]

def combined155 : Sparse := combined155_part0 ++ combined155_part1

def combined156_part0 : Sparse := [([0, -1, -1, 1, 0, 1, 0], -36), ([0, -1, -1, 1, 0, 2, -1], -9), ([0, -1, 0, 1, 0, 1, -1], -27), ([0, 0, -2, 1, 0, 2, -1], -36), ([0, 0, -2, 2, 0, 1, -1], -36), ([0, 0, -1, 0, 1, 1, -1], -36), ([0, 0, -1, 1, -1, 1, 0], -36), ([0, 0, -1, 1, 0, 2, -2], -27), ([0, 0, -1, 1, 1, 0, -1], -27), ([0, 0, -1, 1, 1, 1, -2], -9), ([0, 0, -1, 2, -1, 1, -1], -9), ([0, 0, -1, 2, 0, 1, -2], -27), ([0, 0, 0, 0, 0, 1, -1], -9), ([0, 0, 0, 1, -1, 1, -1], -27), ([0, 0, 0, 1, 0, 0, -1], -9), ([0, 1, -1, 0, 0, 1, -1], -27), ([0, 1, -1, 1, 0, 0, -1], -36), ([0, 1, -1, 1, 0, 1, -2], -9), ([1, -1, -1, 1, 1, 1, -1], 27), ([1, -1, -1, 2, 0, 1, -1], -9), ([1, 0, -2, 1, 0, 1, 0], 18), ([1, 0, -1, 0, 0, 2, -1], 27), ([1, 0, -1, 0, 1, 1, -1], -9), ([1, 0, -1, 1, -1, 2, -1], -9)]

def combined156_part1 : Sparse := [([1, 0, -1, 1, 1, 0, -1], 9), ([1, 0, -1, 1, 1, 1, -2], -9), ([1, 0, -1, 2, 0, 0, -1], 27), ([1, 0, 0, 0, 0, 1, -1], -9), ([1, 0, 0, 1, 0, 0, -1], -9), ([1, 0, 0, 1, 0, 1, -2], 36), ([1, 1, -1, 0, 0, 1, -1], 9), ([1, 1, -1, 1, -1, 1, -1], 27), ([1, 1, -1, 1, 0, 0, -1], -9), ([1, 1, -1, 1, 0, 1, -2], -9)]

def combined156 : Sparse := combined156_part0 ++ combined156_part1

def combined157_part0 : Sparse := [([0, -1, -1, 1, 0, 1, 0], -27), ([0, -1, -1, 1, 0, 2, -1], -18), ([0, -1, 0, 1, 0, 1, -1], -27), ([0, 0, -2, 1, 0, 2, -1], -27), ([0, 0, -2, 2, 0, 1, -1], -36), ([0, 0, -1, 0, 0, 1, 0], -9), ([0, 0, -1, 0, 1, 1, -1], -27), ([0, 0, -1, 1, -1, 1, 0], -36), ([0, 0, -1, 1, -1, 2, -1], -9), ([0, 0, -1, 1, 0, 2, -2], -18), ([0, 0, -1, 1, 1, 0, -1], -27), ([0, 0, -1, 1, 1, 1, -2], -18), ([0, 0, -1, 2, -1, 1, -1], -9), ([0, 0, -1, 2, 0, 1, -2], -27), ([0, 0, 0, 0, 0, 1, -1], -18), ([0, 0, 0, 1, -1, 1, -1], -18), ([0, 0, 0, 1, 0, 0, -1], -9), ([0, 1, -2, 1, 0, 1, -1], -9), ([0, 1, -1, 0, 0, 1, -1], -18), ([0, 1, -1, 1, 0, 0, -1], -36), ([0, 1, -1, 1, 0, 1, -2], -9), ([1, -1, -1, 1, 0, 1, 0], 9), ([1, -1, -1, 1, 0, 2, -1], -9), ([1, -1, -1, 1, 1, 1, -1], 18)]

def combined157_part1 : Sparse := [([1, -1, -1, 2, 0, 1, -1], -9), ([1, -1, 0, 1, 0, 1, -1], -9), ([1, 0, -2, 1, 0, 1, 0], 9), ([1, 0, -2, 1, 1, 1, -1], -9), ([1, 0, -1, 0, 0, 1, 0], -9), ([1, 0, -1, 0, 0, 2, -1], 27), ([1, 0, -1, 0, 1, 1, -1], -9), ([1, 0, -1, 1, -1, 1, 0], -9), ([1, 0, -1, 1, -1, 2, -1], -18), ([1, 0, -1, 1, 1, 0, -1], 9), ([1, 0, -1, 1, 1, 1, -2], -9), ([1, 0, -1, 2, 0, 0, -1], 9), ([1, 0, 0, 0, 0, 1, -1], -18), ([1, 0, 0, 1, -1, 1, -1], 9), ([1, 0, 0, 1, 0, 0, -1], -9), ([1, 0, 0, 1, 0, 1, -2], 27), ([1, 1, -1, 0, 0, 1, -1], 9), ([1, 1, -1, 1, -1, 1, -1], 18), ([1, 1, -1, 1, 0, 0, -1], -9), ([1, 1, -1, 1, 0, 1, -2], -18)]

def combined157 : Sparse := combined157_part0 ++ combined157_part1

def combined158_part0 : Sparse := [([0, -1, -1, 1, 0, 1, 0], -27), ([0, -1, -1, 1, 0, 2, -1], -18), ([0, -1, -1, 2, 0, 1, -1], -9), ([0, -1, 0, 1, 0, 1, -1], -18), ([0, 0, -2, 1, 0, 2, -1], -27), ([0, 0, -2, 1, 1, 1, -1], -9), ([0, 0, -2, 2, 0, 1, -1], -27), ([0, 0, -1, 0, 0, 1, 0], -9), ([0, 0, -1, 0, 1, 1, -1], -27), ([0, 0, -1, 1, -1, 1, 0], -27), ([0, 0, -1, 1, -1, 2, -1], -9), ([0, 0, -1, 1, 0, 0, 0], -9), ([0, 0, -1, 1, 0, 2, -2], -18), ([0, 0, -1, 1, 1, 0, -1], -18), ([0, 0, -1, 1, 1, 1, -2], -18), ([0, 0, -1, 2, -1, 1, -1], -18), ([0, 0, -1, 2, 0, 1, -2], -18), ([0, 0, 0, 0, 0, 1, -1], -18), ([0, 0, 0, 1, -1, 1, -1], -18), ([0, 0, 0, 1, 0, 0, -1], -18), ([0, 1, -2, 1, 0, 1, -1], -9), ([0, 1, -1, 0, 0, 1, -1], -18), ([0, 1, -1, 1, 0, 0, -1], -27), ([0, 1, -1, 1, 0, 1, -2], -18)]

def combined158_part1 : Sparse := [([1, -1, -1, 1, 0, 2, -1], -9), ([1, -1, -1, 1, 1, 1, -1], 9), ([1, -1, -1, 2, 0, 1, -1], -18), ([1, 0, -2, 1, 1, 1, -1], -9), ([1, 0, -1, 0, 0, 1, 0], -9), ([1, 0, -1, 0, 0, 2, -1], 9), ([1, 0, -1, 0, 1, 1, -1], -9), ([1, 0, -1, 1, -1, 2, -1], -18), ([1, 0, -1, 1, 0, 0, 0], -9), ([1, 0, -1, 1, 1, 0, -1], 9), ([1, 0, -1, 1, 1, 1, -2], -18), ([1, 0, -1, 2, -1, 1, -1], -9), ([1, 0, -1, 2, 0, 0, -1], 9), ([1, 0, 0, 0, 0, 1, -1], -18), ([1, 0, 0, 1, 0, 0, -1], -18), ([1, 0, 0, 1, 0, 1, -2], 18), ([1, 1, -2, 1, 0, 1, -1], -9), ([1, 1, -1, 0, 0, 1, -1], 9), ([1, 1, -1, 1, -1, 1, -1], 9), ([1, 1, -1, 1, 0, 0, -1], -9), ([1, 1, -1, 1, 0, 1, -2], -18)]

def combined158 : Sparse := combined158_part0 ++ combined158_part1

def combined159_part0 : Sparse := [([0, -1, -1, 1, 0, 1, 0], -18), ([0, -1, -1, 1, 0, 2, -1], -18), ([0, -1, -1, 2, 0, 1, -1], -18), ([0, -1, 0, 1, 0, 1, -1], -18), ([0, 0, -2, 1, 0, 2, -1], -18), ([0, 0, -2, 1, 1, 1, -1], -18), ([0, 0, -2, 2, 0, 1, -1], -18), ([0, 0, -1, 0, 0, 1, 0], -18), ([0, 0, -1, 0, 1, 1, -1], -18), ([0, 0, -1, 1, -1, 1, 0], -18), ([0, 0, -1, 1, -1, 2, -1], -18), ([0, 0, -1, 1, 0, 0, 0], -18), ([0, 0, -1, 1, 0, 2, -2], -18), ([0, 0, -1, 1, 1, 0, -1], -18), ([0, 0, -1, 1, 1, 1, -2], -18), ([0, 0, -1, 2, -1, 1, -1], -18), ([0, 0, -1, 2, 0, 1, -2], -18), ([0, 0, 0, 0, 0, 1, -1], -18), ([0, 0, 0, 1, -1, 1, -1], -18), ([0, 0, 0, 1, 0, 0, -1], -18), ([0, 1, -2, 1, 0, 1, -1], -18), ([0, 1, -1, 0, 0, 1, -1], -18), ([0, 1, -1, 1, 0, 0, -1], -18), ([0, 1, -1, 1, 0, 1, -2], -18)]

def combined159_part1 : Sparse := [([1, -1, -1, 1, 0, 2, -1], -18), ([1, -1, -1, 2, 0, 1, -1], -18), ([1, 0, -2, 1, 1, 1, -1], -18), ([1, 0, -1, 0, 0, 1, 0], -18), ([1, 0, -1, 1, -1, 2, -1], -18), ([1, 0, -1, 1, 0, 0, 0], -18), ([1, 0, -1, 1, 1, 1, -2], -18), ([1, 0, -1, 2, -1, 1, -1], -18), ([1, 0, 0, 0, 0, 1, -1], -18), ([1, 0, 0, 1, 0, 0, -1], -18), ([1, 1, -2, 1, 0, 1, -1], -18), ([1, 1, -1, 1, 0, 1, -2], -18)]

def combined159 : Sparse := combined159_part0 ++ combined159_part1

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Tao_TaoTarget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6.TaoArithmetic

def OrderTwoValues (f : Charge → ℂ) : Prop :=
  ∀ a, Balanced a → order a = 2 → f a = -(g tao a) / 5

def knownTerms (ps : List (Charge × Coeff)) : Sparse :=
  ps.flatMap (fun p => monomial p.1 p.2)

def cubeTerms : Sparse :=
  offDiagonalPairs.flatMap (fun p => monomial ((3 : ℤ) • difference p.1 p.2) (36, 0))

end MUB6.TaoArithmetic

end

end OAI
end


