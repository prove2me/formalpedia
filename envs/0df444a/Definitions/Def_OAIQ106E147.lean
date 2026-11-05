-- Prove2me | Definitions.Def_OAIQ106E147
-- name    : OAIQ106E147
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T18:32:51.098438+00:00
-- url     : https://prove2.me/theorems/63507551-5d7f-4a58-afd7-7c38f45ae4f1
-- title:
--   Definitions bundle OAIQ106E147 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1659 declarations of OpenAI's Lean: 1574 definitions, 1 inductive type or structure, 8 instances and 76 theorems. The definitions and types are `OAI.MUB6.Certificate.PairSemantics.raw9679`, `OAI.MUB6.Certificate.PairSemantics.raw9679step0`, `OAI.MUB6.Certificate.PairSemantics.raw9680`, `OAI.MUB6.Certificate.PairSemantics.raw9680step0`, `OAI.MUB6.Certificate.PairSemantics.raw9681`, `OAI.MUB6.Certificate.PairSemantics.raw9681step0`, `OAI.MUB6.Certificate.PairSemantics.raw9682`, `OAI.MUB6.Certificate.PairSemantics.raw9682step0`, `OAI.MUB6.Certificate.PairSemantics.raw9683`, `OAI.MUB6.Certificate.PairSemantics.raw9683step0`, `OAI.MUB6.Certificate.PairSemantics.raw9684`, `OAI.MUB6.Certificate.PairSemantics.raw9684step0`, `OAI.MUB6.Certificate.PairSemantics.raw9685`, `OAI.MUB6.Certificate.PairSemantics.raw9685step0`, `OAI.MUB6.Certificate.PairSemantics.raw9686`, `OAI.MUB6.Certificate.PairSemantics.raw9686step0`, `OAI.MUB6.Certificate.PairSemantics.raw9687`, `OAI.MUB6.Certificate.PairSemantics.raw9687step0`, `OAI.MUB6.Certificate.PairSemantics.raw9688`, `OAI.MUB6.Certificate.PairSemantics.raw9688step0`, `OAI.MUB6.Certificate.PairSemantics.raw9689`, `OAI.MUB6.Certificate.PairSemantics.raw9689step0`, `OAI.MUB6.Certificate.PairSemantics.raw9689step1`, `OAI.MUB6.Certificate.PairSemantics.raw968step0`, `OAI.MUB6.Certificate.PairSemantics.raw969`, `OAI.MUB6.Certificate.PairSemantics.raw9690`, `OAI.MUB6.Certificate.PairSemantics.raw9690step0`, `OAI.MUB6.Certificate.PairSemantics.raw9691`, `OAI.MUB6.Certificate.PairSemantics.raw9691step0`, `OAI.MUB6.Certificate.PairSemantics.raw9691step1`, `OAI.MUB6.Certificate.PairSemantics.raw9692`, `OAI.MUB6.Certificate.PairSemantics.raw9692step0`, `OAI.MUB6.Certificate.PairSemantics.raw9692step1`, `OAI.MUB6.Certificate.PairSemantics.raw9693`, `OAI.MUB6.Certificate.PairSemantics.raw9693step0`, `OAI.MUB6.Certificate.PairSemantics.raw9693step1`, `OAI.MUB6.Certificate.PairSemantics.raw9694`, `OAI.MUB6.Certificate.PairSemantics.raw9694step0`, `OAI.MUB6.Certificate.PairSemantics.raw9694step1`, `OAI.MUB6.Certificate.PairSemantics.raw9695` and 1535 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_Bases_Families`, `MutuallyUnbiased_Certificate_Gram`, `MutuallyUnbiased_Completion_Complement`, `MutuallyUnbiased_Completion_Completion`, `MutuallyUnbiased_Completion_Frame`, `MutuallyUnbiased_Completion_JointBasis`, `MutuallyUnbiased_Completion_Kraus`, `MutuallyUnbiased_Completion_OrthogonalPinching`, `MutuallyUnbiased_Completion_ProjectionBasis`, `MutuallyUnbiased_Completion_Superoperator`, `MutuallyUnbiased_Cubic_CubicMultiplicityCore`, `MutuallyUnbiased_Cubic_CubicPattern`, `MutuallyUnbiased_Cubic_CubicSupport`, `MutuallyUnbiased_Cubic_CubicSymmetric`, `MutuallyUnbiased_Cubic_FiveCycle`, `MutuallyUnbiased_Cubic_NormalizedCodes`, `MutuallyUnbiased_Matrix_Definitions`, `MutuallyUnbiased_Moments_EqualityPatterns`, `MutuallyUnbiased_Moments_MomentContraction`, `MutuallyUnbiased_Moments_PartitionExpansion`, `MutuallyUnbiased_Moments_Sampling`, `MutuallyUnbiased_Moments_SmallPartitions`, `MutuallyUnbiased_PairMoments_PairCharges`, `MutuallyUnbiased_PairSemantics_Canonical0`, `MutuallyUnbiased_PairSemantics_Canonical3`, `MutuallyUnbiased_PairSemantics_Canonical30`, `MutuallyUnbiased_PairSemantics_Canonical302`, `MutuallyUnbiased_PairSemantics_Canonical303`, `MutuallyUnbiased_PairSemantics_Canonical304`, `MutuallyUnbiased_PairSemantics_Canonical305`, `MutuallyUnbiased_PairSemantics_Canonical306`, `MutuallyUnbiased_PairSemantics_Canonical307`, `MutuallyUnbiased_PairSemantics_Canonical308`, `MutuallyUnbiased_PairSemantics_Canonical309`, `MutuallyUnbiased_PairSemantics_Canonical31`, `MutuallyUnbiased_PairSemantics_Canonical310`, `MutuallyUnbiased_PairSemantics_Canonical311`, `MutuallyUnbiased_PairSemantics_Canonical312`, `MutuallyUnbiased_PairSources_Data`, `MutuallyUnbiased_PairTargets_ExtraCanonical0`, `MutuallyUnbiased_PairTargets_ExtraCanonical1`, `MutuallyUnbiased_PairTargets_ExtraCanonical2`, `MutuallyUnbiased_PairTargets_ExtraCanonical3`, `MutuallyUnbiased_PairTargets_ExtraCanonical4`, `MutuallyUnbiased_PairTargets_ExtraCanonical5`, `MutuallyUnbiased_PairTargets_ExtraCanonical6`, `MutuallyUnbiased_PairTargets_ExtraCanonical7`, `MutuallyUnbiased_PairTargets_ExtraCanonical8`, `MutuallyUnbiased_PairTargets_ExtraPermutations`.
--
--   **Imports.** It imports the published bundle `Def_MUBSix`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ106E149`, `OAIQ106E150`, `OAIQ106E154` and `OAIQ106E172`; the statements `OAI.MUB6.Certificate.GramData.Block3.entry_10_0_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_10_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_11_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_12_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_13_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_14_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_15_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_16_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_17_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_18_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_19_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_1_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_20_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_21_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_22_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_23_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_24_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_25_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_26_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_2_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_3_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_4_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_5_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_6_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_7_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_8_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_9_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_10_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_11_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_12_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_13_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_14_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_15_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_16_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_17_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_18_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_19_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_20_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_21_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_22_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_23_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_24_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_25_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_26_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_10_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_11_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_15_13_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_15_14_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_15_15_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_15_16_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_15_17_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_15_18_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_15_19_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_15_20_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_15_21_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_15_22_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_15_23_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_15_24_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_15_25_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_15_26_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_16_10_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_16_11_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_16_12_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_16_13_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_16_14_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_16_15_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_16_16_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_16_17_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_16_18_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_16_19_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_16_20_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_16_21_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_16_22_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_16_23_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_10_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_11_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_12_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_13_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_14_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_15_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_16_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_17_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_18_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_19_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_20_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_21_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_22_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_23_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_24_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_25_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_26_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_10_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_11_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_12_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_13_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_14_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_15_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_16_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_17_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_18_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_19_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_20_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_21_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_22_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_23_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_24_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_25_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_26_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_0_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_10_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_11_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_12_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_13_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_14_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_15_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_16_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_17_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_18_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_19_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_1_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_20_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_21_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_22_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_23_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_24_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_25_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_26_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_2_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_3_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_4_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_5_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_6_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_7_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_8_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_9_e`, `OAI.MUB6.Certificate.GramData.Block3.gram_e` and `OAI.MUB6.Certificate.PairTargetSemantics.pair_partition4_e`; the proofs of `OAI.MUB6.Certificate.GramData.Block3.entry_10_0_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_10_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_11_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_12_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_13_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_14_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_15_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_16_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_17_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_18_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_19_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_1_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_20_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_21_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_22_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_23_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_24_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_25_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_26_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_2_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_3_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_4_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_5_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_6_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_7_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_8_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_9_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_10_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_11_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_12_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_13_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_14_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_15_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_16_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_17_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_18_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_19_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_20_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_21_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_22_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_23_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_24_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_25_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_26_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_10_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_11_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_15_13_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_15_14_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_15_15_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_15_16_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_15_17_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_15_18_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_15_19_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_15_20_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_15_21_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_15_22_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_15_23_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_15_24_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_15_25_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_15_26_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_16_10_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_16_11_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_16_12_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_16_13_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_16_14_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_16_15_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_16_16_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_16_17_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_16_18_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_16_19_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_16_20_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_16_21_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_16_22_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_16_23_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_10_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_11_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_12_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_13_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_14_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_15_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_16_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_17_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_18_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_19_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_20_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_21_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_22_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_23_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_24_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_25_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_26_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_10_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_11_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_12_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_13_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_14_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_15_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_16_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_17_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_18_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_19_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_20_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_21_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_22_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_23_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_24_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_25_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_26_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_0_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_10_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_11_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_12_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_13_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_14_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_15_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_16_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_17_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_18_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_19_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_1_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_20_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_21_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_22_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_23_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_24_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_25_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_26_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_2_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_3_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_4_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_5_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_6_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_7_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_8_e`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_9_e`, `OAI.MUB6.Certificate.GramData.Block3.gram_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1162_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1163_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1164_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1165_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1170_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1172_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1265_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1266_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1267_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1298_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1299_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1339_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1340_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1341_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1342_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1343_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1395_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1396_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1397_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1399_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1409_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1410_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1411_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1412_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1414_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1441_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1475_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1477_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1478_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2357_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2358_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2526_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2527_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2528_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2530_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2531_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2570_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2572_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2574_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2576_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2593_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2594_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2595_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2599_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2636_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2766_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2828_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2901_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2903_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2904_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2936_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2937_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2939_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2941_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2943_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2957_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2958_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2959_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2960_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2961_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2963_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2986_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2987_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2988_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2990_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2996_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2998_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3003_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3081_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3082_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3087_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3088_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3089_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3094_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3100_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3106_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3109_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3139_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3140_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3184_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3185_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3190_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3191_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3203_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3204_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3205_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3206_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3209_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3210_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3211_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3223_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3226_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3227_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3711_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3727_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3735_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3737_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3739_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3818_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3821_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3823_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3829_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3830_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3847_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3851_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3852_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3853_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3882_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3925_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3936_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3937_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3938_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3965_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3966_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3967_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3969_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3970_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3977_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3980_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3981_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3982_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3984_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3990_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3992_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3994_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3995_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3998_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4003_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4023_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4026_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4031_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4032_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4033_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4053_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5167_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5168_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5169_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5172_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5174_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5292_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5386_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5387_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5388_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5415_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5416_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5417_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5418_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5433_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5434_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5435_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5439_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5450_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5452_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5464_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5465_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5476_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5482_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5483_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5485_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5490_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5492_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5500_e`, `OAI.MUB6.Certificate.MixedSourceBridge.allRowsSound_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound100_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound101_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound102_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound103_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound104_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound105_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound106_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound107_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound108_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound110_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound111_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound112_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound113_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound114_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound115_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound116_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound117_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound118_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound119_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound11_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound120_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound121_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound122_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound123_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound124_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound125_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound126_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound127_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound128_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound129_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound12_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound130_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound131_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound132_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound133_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound134_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound135_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound136_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound137_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound138_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound139_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound13_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound140_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound141_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound142_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound143_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound144_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound145_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound146_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound147_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound148_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound149_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound14_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound150_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound151_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound15_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound16_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound17_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound18_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound19_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound20_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound21_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound23_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound24_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound25_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound26_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound27_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound28_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound29_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound2_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound30_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound31_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound32_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound33_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound34_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound35_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound37_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound38_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound39_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound3_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound40_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound41_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound42_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound43_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound44_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound45_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound46_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound47_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound48_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound49_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound4_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound50_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound51_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound52_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound53_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound54_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound55_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound56_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound57_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound58_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound59_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound5_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound60_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound63_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound64_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound65_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound66_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound67_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound68_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound69_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound6_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound70_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound71_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound72_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound73_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound74_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound75_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound76_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound77_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound78_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound79_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound7_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound80_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound81_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound82_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound83_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound84_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound85_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound86_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound87_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound88_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound89_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound8_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound90_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound91_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound92_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound93_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound94_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound95_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound96_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound97_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound98_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound99_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1472_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero14_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero15_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1674_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1785_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero18_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1909_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero488_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero621_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero794_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero818_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound0_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1007_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1008_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound100_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1010_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1013_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1020_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1021_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1030_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1033_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1034_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1093_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1094_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1095_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1096_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1097_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1098_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1103_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1108_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound110_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1110_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1111_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1114_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1115_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound111_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1120_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1121_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1124_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1130_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1131_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound113_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound114_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1159_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound115_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1165_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1166_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1167_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound116_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1170_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1177_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1178_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1179_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1191_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1194_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1195_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1197_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1231_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1232_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1233_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound125_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1261_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1262_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1264_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1266_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1267_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1268_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1269_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound126_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1272_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1278_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1279_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound127_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1294_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound12_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1300_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1301_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1303_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1309_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound130_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1310_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1311_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1312_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1318_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1321_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1324_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1326_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1335_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1340_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound137_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound138_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound139_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound13_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1409_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound140_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1410_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1411_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1412_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1413_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1414_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1418_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1419_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound141_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1420_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1421_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1423_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1428_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1429_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1433_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1434_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1435_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1436_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1437_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1441_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1442_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound144_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1469_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1470_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1477_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1478_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1479_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1480_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1484_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1492_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1493_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1505_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1507_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1508_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1510_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1511_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1513_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1514_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1516_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1517_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound151_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1521_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1536_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1539_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound153_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1559_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1560_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1562_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1567_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1568_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1572_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1575_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1584_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1587_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1589_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1593_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1595_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1599_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound163_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1648_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1649_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1650_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1651_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1652_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1653_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1654_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1655_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1656_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1662_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1668_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1669_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1672_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1673_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1679_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1684_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1686_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1687_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound16_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1702_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1703_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1708_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1709_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1710_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1715_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1716_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1717_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1723_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1734_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1738_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1739_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1740_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1743_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1780_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1781_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1782_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1783_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1784_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1786_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1787_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1788_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1789_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1795_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1796_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound17_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1811_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1815_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1816_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1822_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1825_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1826_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1828_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1831_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1833_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1835_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1838_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1839_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1840_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1844_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1845_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1846_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1847_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1849_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound184_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1853_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1854_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1855_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1856_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1858_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1859_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1864_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1866_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1871_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1872_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1873_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1874_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1877_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1880_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1881_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound188_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1904_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1905_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1906_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1907_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1911_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1912_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1914_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1915_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1916_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1917_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1924_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1925_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1935_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1937_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1941_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1942_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1944_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1945_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1948_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1949_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1950_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1952_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1953_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1954_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1956_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1958_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1960_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1963_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1964_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1965_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1968_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1969_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1970_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1971_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1972_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1976_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1977_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1978_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1983_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1984_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1985_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1988_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1989_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1990_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1991_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1993_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1994_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1995_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1998_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1999_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound199_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound19_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2002_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2003_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2004_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2005_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2006_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2010_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2011_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2014_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2015_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2016_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2018_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2019_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2021_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2022_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2023_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2033_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2034_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2035_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2036_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2037_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2038_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2039_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2040_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2046_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2048_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2049_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2050_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2051_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2056_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2059_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2060_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2061_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2062_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2063_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2064_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2065_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2066_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2067_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2069_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2071_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2073_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2074_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2075_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2076_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2077_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2078_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound207_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2080_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2082_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2084_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2085_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2086_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2088_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2089_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2090_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2091_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2092_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2093_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2094_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2096_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2097_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2099_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound20_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2100_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2102_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2103_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2105_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2107_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2108_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound213_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound214_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2166_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2168_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2169_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2170_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2171_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2172_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2173_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2174_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2175_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2176_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2177_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2178_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2179_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2180_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2181_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2182_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2183_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2184_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2185_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2187_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2188_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2189_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2191_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2192_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2193_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2195_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2196_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2197_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2198_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2199_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound21_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2200_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2201_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2202_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2203_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2204_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2205_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2206_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2207_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2208_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2211_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2212_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2214_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2215_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2216_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2217_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2218_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2219_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2220_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2223_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2224_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2225_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2226_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2227_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2228_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2229_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2230_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2231_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2232_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2233_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2235_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2236_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2238_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2240_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2241_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2242_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2244_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2245_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2246_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2247_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2248_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2249_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2250_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2251_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2252_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2253_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2254_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2255_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2256_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2257_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2258_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2259_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2260_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2261_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2262_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2263_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2264_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2265_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2266_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2267_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2268_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound226_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2270_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2271_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2272_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2273_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2274_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2275_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2276_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2277_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2278_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2279_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2281_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2282_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2283_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2284_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2285_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2286_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2287_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2288_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2289_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2290_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2291_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2292_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2293_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2294_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2295_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2296_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2297_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2298_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2299_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2300_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2301_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2302_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2304_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2305_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2306_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2307_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2308_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2309_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2310_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2311_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2312_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2313_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2314_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2315_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2316_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2317_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2318_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2321_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2322_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2323_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2324_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2325_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2326_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2327_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2328_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2329_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2330_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2331_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2332_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2333_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2334_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2335_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2336_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2337_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2338_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2339_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2340_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2341_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2342_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2344_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2345_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2346_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2347_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2348_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2350_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2352_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2353_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2354_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2355_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2356_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2357_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2358_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2361_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2362_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2363_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2364_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2365_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2366_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2367_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2368_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2369_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound236_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2371_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2373_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2374_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2375_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2376_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2377_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2378_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2379_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2380_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2381_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2382_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2383_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2384_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2385_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2386_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2387_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2388_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2390_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2391_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2392_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2393_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2394_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2395_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2396_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2397_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2398_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2399_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2400_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2401_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2402_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2404_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2405_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2406_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2407_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2408_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2409_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2410_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2411_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2412_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2413_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2414_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2415_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2416_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2418_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2419_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2421_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2422_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2423_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2424_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound244_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound245_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound255_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound267_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound269_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound281_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound282_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound286_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound287_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound296_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound301_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound310_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound311_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound319_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound326_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound327_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound335_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound339_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound340_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound341_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound342_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound343_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound344_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound345_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound353_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound354_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound355_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound356_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound357_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound358_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound359_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound365_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound366_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound367_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound368_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound369_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound370_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound371_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound380_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound388_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound391_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound392_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound395_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound396_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound3_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound404_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound411_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound412_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound413_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound418_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound419_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound427_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound428_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound438_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound444_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound445_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound446_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound447_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound448_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound452_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound453_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound454_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound456_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound462_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound463_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound470_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound473_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound474_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound481_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound482_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound483_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound484_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound485_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound487_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound497_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound498_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound499_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound4_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound500_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound501_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound504_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound505_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound512_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound513_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound514_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound515_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound516_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound521_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound523_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound524_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound525_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound526_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound531_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound532_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound533_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound534_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound537_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound538_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound539_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound540_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound541_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound542_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound543_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound545_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound546_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound547_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound548_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound551_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound552_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound553_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound554_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound555_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound558_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound564_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound565_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound566_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound567_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound568_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound570_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound571_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound578_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound579_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound580_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound581_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound582_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound584_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound585_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound587_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound588_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound589_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound58_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound591_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound592_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound599_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound5_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound600_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound607_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound608_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound612_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound613_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound614_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound628_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound629_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound630_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound631_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound633_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound635_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound636_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound643_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound644_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound649_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound656_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound657_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound658_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound659_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound663_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound664_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound666_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound667_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound668_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound675_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound682_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound683_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound688_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound694_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound695_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound700_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound707_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound710_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound711_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound712_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound717_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound718_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound719_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound720_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound722_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound726_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound727_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound730_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound731_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound732_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound733_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound734_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound735_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound736_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound738_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound739_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound740_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound741_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound742_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound743_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound744_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound749_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound751_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound758_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound759_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound769_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound76_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound779_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound780_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound786_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound787_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound788_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound789_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound790_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound792_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound793_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound795_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound796_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound797_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound798_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound799_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound7_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound800_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound801_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound802_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound804_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound805_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound813_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound815_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound817_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound822_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound823_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound834_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound840_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound841_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound842_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound844_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound847_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound852_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound853_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound857_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound858_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound859_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound863_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound864_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound865_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound866_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound867_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound868_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound872_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound873_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound877_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound878_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound881_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound882_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound883_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound884_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound885_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound887_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound888_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound890_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound891_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound894_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound897_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound898_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound899_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound900_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound902_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound903_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound905_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound906_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound909_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound911_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound912_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound913_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound916_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound917_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound918_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound919_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound91_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound920_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound924_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound925_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound926_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound927_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound928_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound929_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound92_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound930_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound931_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound932_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound933_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound935_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound936_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound937_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound938_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound939_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound940_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound941_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound942_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound948_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound94_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound950_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound951_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound952_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound953_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound954_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound956_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound957_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound958_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound959_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound962_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound963_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound964_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound965_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound966_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound967_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound968_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound970_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound971_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound972_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound973_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound974_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound975_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound976_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound978_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound97_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound980_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound981_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound982_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound983_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound984_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound986_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound987_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound988_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound990_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound992_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound99_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.allKeyMoments_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound0_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound10_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound11_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound13_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound14_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound15_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound16_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound17_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound18_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound19_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound1_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound20_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound21_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound22_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound23_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound24_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound25_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound26_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound27_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound28_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound29_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound30_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound31_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound32_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound33_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound34_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound35_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound36_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound37_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound38_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound39_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound3_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound40_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound41_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound42_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound43_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound44_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound45_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound46_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound47_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound48_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound49_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound4_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound50_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound51_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound52_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound53_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound54_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound55_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound56_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound57_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound58_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound59_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound5_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound60_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound61_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound63_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound64_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound65_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound66_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound67_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound68_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound69_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound6_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound70_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound71_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound72_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound73_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound74_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound75_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound76_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound77_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound78_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound79_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound7_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound80_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound81_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound82_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound83_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound84_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound85_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound86_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound87_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound88_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound89_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound9_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.originalReductionEval_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval100_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval105_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1075_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval108_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval111_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval113_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval117_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval118_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1194_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1225_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval122_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval126_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1315_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval131_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval136_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval137_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval141_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1436_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval143_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1465_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval151_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1523_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval152_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1554_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1555_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval155_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval164_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval165_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval169_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval174_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval175_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1794_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval181_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval185_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval18_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval190_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1912_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval201_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval202_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval211_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval212_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval217_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval21_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval220_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval224_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval226_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval229_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval232_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval234_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval235_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval242_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval246_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval250_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval256_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval260_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval264_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval266_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval268_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval269_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval275_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval280_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval285_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval286_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval287_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval289_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval296_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval301_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval308_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval310_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval316_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval325_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval332_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval335_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval338_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval339_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval341_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval343_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval351_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval352_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval356_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval357_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval358_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval359_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval366_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval369_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval372_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval378_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval37_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval382_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval383_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval385_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval390_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval398_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval39_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval405_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval408_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval413_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval46_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval474_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval476_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval53_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval55_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval56_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval63_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval69_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval73_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval74_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval79_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval84_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval86_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval8_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval92_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval956_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval957_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval145_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval147_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval150_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval215_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval216_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval219_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval21_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval220_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval223_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval238_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval373_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval375_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval44_e`, `OAI.MUB6.Certificate.PairSemantics.boundarySound26_e`, `OAI.MUB6.Certificate.PairSemantics.boundarySound49_e`, `OAI.MUB6.Certificate.PairSemantics.boundarySound58_e`, `OAI.MUB6.Certificate.PairSemantics.boundarySound73_e`, `OAI.MUB6.Certificate.PairSemantics.sound1379_e`, `OAI.MUB6.Certificate.PairSemantics.sound1381_e`, `OAI.MUB6.Certificate.PairSemantics.sound1383_e`, `OAI.MUB6.Certificate.PairSemantics.sound1384_e`, `OAI.MUB6.Certificate.PairSemantics.sound1387_e`, `OAI.MUB6.Certificate.PairSemantics.sound1390_e`, `OAI.MUB6.Certificate.PairSemantics.sound1391_e`, `OAI.MUB6.Certificate.PairSemantics.sound1395_e`, `OAI.MUB6.Certificate.PairSemantics.sound1399_e`, `OAI.MUB6.Certificate.PairSemantics.sound1414_e`, `OAI.MUB6.Certificate.PairSemantics.sound1419_e`, `OAI.MUB6.Certificate.PairSemantics.sound1423_e`, `OAI.MUB6.Certificate.PairSemantics.sound1424_e`, `OAI.MUB6.Certificate.PairSemantics.sound1425_e`, `OAI.MUB6.Certificate.PairSemantics.sound1434_e`, `OAI.MUB6.Certificate.PairSemantics.sound1437_e`, `OAI.MUB6.Certificate.PairSemantics.sound1443_e`, `OAI.MUB6.Certificate.PairSemantics.sound1458_e`, `OAI.MUB6.Certificate.PairSemantics.sound1486_e`, `OAI.MUB6.Certificate.PairSemantics.sound1504_e`, `OAI.MUB6.Certificate.PairSemantics.sound1506_e`, `OAI.MUB6.Certificate.PairSemantics.sound1512_e`, `OAI.MUB6.Certificate.PairSemantics.sound1518_e`, `OAI.MUB6.Certificate.PairSemantics.sound1529_e`, `OAI.MUB6.Certificate.PairSemantics.sound1530_e`, `OAI.MUB6.Certificate.PairSemantics.sound1531_e`, `OAI.MUB6.Certificate.PairSemantics.sound1535_e`, `OAI.MUB6.Certificate.PairSemantics.sound1540_e`, `OAI.MUB6.Certificate.PairSemantics.sound1548_e`, `OAI.MUB6.Certificate.PairSemantics.sound1605_e`, `OAI.MUB6.Certificate.PairSemantics.sound1614_e`, `OAI.MUB6.Certificate.PairSemantics.sound1617_e`, `OAI.MUB6.Certificate.PairSemantics.sound1624_e`, `OAI.MUB6.Certificate.PairSemantics.sound1627_e`, `OAI.MUB6.Certificate.PairSemantics.sound1628_e`, `OAI.MUB6.Certificate.PairSemantics.sound1631_e`, `OAI.MUB6.Certificate.PairSemantics.sound1634_e`, `OAI.MUB6.Certificate.PairSemantics.sound1635_e`, `OAI.MUB6.Certificate.PairSemantics.sound1637_e`, `OAI.MUB6.Certificate.PairSemantics.sound1644_e`, `OAI.MUB6.Certificate.PairSemantics.sound1646_e`, `OAI.MUB6.Certificate.PairSemantics.sound1648_e`, `OAI.MUB6.Certificate.PairSemantics.sound1685_e`, `OAI.MUB6.Certificate.PairSemantics.sound1716_e`, `OAI.MUB6.Certificate.PairSemantics.sound1736_e`, `OAI.MUB6.Certificate.PairSemantics.sound1739_e`, `OAI.MUB6.Certificate.PairSemantics.sound1768_e`, `OAI.MUB6.Certificate.PairSemantics.sound1770_e`, `OAI.MUB6.Certificate.PairSemantics.sound1793_e`, `OAI.MUB6.Certificate.PairSemantics.sound1800_e`, `OAI.MUB6.Certificate.PairSemantics.sound1828_e`, `OAI.MUB6.Certificate.PairSemantics.sound1849_e`, `OAI.MUB6.Certificate.PairSemantics.sound1858_e`, `OAI.MUB6.Certificate.PairSemantics.sound1860_e`, `OAI.MUB6.Certificate.PairSemantics.sound1865_e`, `OAI.MUB6.Certificate.PairSemantics.sound1866_e`, `OAI.MUB6.Certificate.PairSemantics.sound1867_e`, `OAI.MUB6.Certificate.PairSemantics.sound1869_e`, `OAI.MUB6.Certificate.PairSemantics.sound1870_e`, `OAI.MUB6.Certificate.PairSemantics.sound1872_e`, `OAI.MUB6.Certificate.PairSemantics.sound1875_e`, `OAI.MUB6.Certificate.PairSemantics.sound1876_e`, `OAI.MUB6.Certificate.PairSemantics.sound1879_e`, `OAI.MUB6.Certificate.PairSemantics.sound1885_e`, `OAI.MUB6.Certificate.PairSemantics.sound1978_e`, `OAI.MUB6.Certificate.PairSemantics.sound1980_e`, `OAI.MUB6.Certificate.PairSemantics.sound1986_e`, `OAI.MUB6.Certificate.PairSemantics.sound1987_e`, `OAI.MUB6.Certificate.PairSemantics.sound2041_e`, `OAI.MUB6.Certificate.PairSemantics.sound2058_e`, `OAI.MUB6.Certificate.PairSemantics.sound2071_e`, `OAI.MUB6.Certificate.PairSemantics.sound2097_e`, `OAI.MUB6.Certificate.PairSemantics.sound2106_e`, `OAI.MUB6.Certificate.PairSemantics.sound2107_e`, `OAI.MUB6.Certificate.PairSemantics.sound2108_e`, `OAI.MUB6.Certificate.PairSemantics.sound2117_e`, `OAI.MUB6.Certificate.PairSemantics.sound2122_e`, `OAI.MUB6.Certificate.PairSemantics.sound2123_e`, `OAI.MUB6.Certificate.PairSemantics.sound2128_e`, `OAI.MUB6.Certificate.PairSemantics.sound2132_e`, `OAI.MUB6.Certificate.PairSemantics.sound2152_e`, `OAI.MUB6.Certificate.PairSemantics.sound2168_e`, `OAI.MUB6.Certificate.PairSemantics.sound2175_e`, `OAI.MUB6.Certificate.PairSemantics.sound2177_e`, `OAI.MUB6.Certificate.PairSemantics.sound2189_e`, `OAI.MUB6.Certificate.PairSemantics.sound2190_e`, `OAI.MUB6.Certificate.PairSemantics.sound2197_e`, `OAI.MUB6.Certificate.PairSemantics.sound2201_e`, `OAI.MUB6.Certificate.PairSemantics.sound2202_e`, `OAI.MUB6.Certificate.PairSemantics.sound2213_e`, `OAI.MUB6.Certificate.PairSemantics.sound2228_e`, `OAI.MUB6.Certificate.PairSemantics.sound2244_e`, `OAI.MUB6.Certificate.PairSemantics.sound2262_e`, `OAI.MUB6.Certificate.PairSemantics.sound2284_e`, `OAI.MUB6.Certificate.PairSemantics.sound2286_e`, `OAI.MUB6.Certificate.PairSemantics.sound2293_e`, `OAI.MUB6.Certificate.PairSemantics.sound2294_e`, `OAI.MUB6.Certificate.PairSemantics.sound2295_e`, `OAI.MUB6.Certificate.PairSemantics.sound2296_e`, `OAI.MUB6.Certificate.PairSemantics.sound2312_e`, `OAI.MUB6.Certificate.PairSemantics.sound2324_e`, `OAI.MUB6.Certificate.PairSemantics.sound2327_e`, `OAI.MUB6.Certificate.PairSemantics.sound2338_e`, `OAI.MUB6.Certificate.PairSemantics.sound2375_e`, `OAI.MUB6.Certificate.PairSemantics.sound2382_e`, `OAI.MUB6.Certificate.PairSemantics.sound2390_e`, `OAI.MUB6.Certificate.PairSemantics.sound2391_e`, `OAI.MUB6.Certificate.PairSemantics.sound2394_e`, `OAI.MUB6.Certificate.PairSemantics.sound2399_e`, `OAI.MUB6.Certificate.PairSemantics.sound2400_e`, `OAI.MUB6.Certificate.PairSemantics.sound2401_e`, `OAI.MUB6.Certificate.PairSemantics.sound2403_e`, `OAI.MUB6.Certificate.PairSemantics.sound2415_e`, `OAI.MUB6.Certificate.PairSemantics.sound2416_e`, `OAI.MUB6.Certificate.PairSemantics.sound2420_e`, `OAI.MUB6.Certificate.PairSemantics.sound2433_e`, `OAI.MUB6.Certificate.PairSemantics.sound2434_e`, `OAI.MUB6.Certificate.PairSemantics.sound2435_e`, `OAI.MUB6.Certificate.PairSemantics.sound2436_e`, `OAI.MUB6.Certificate.PairSemantics.sound2442_e`, `OAI.MUB6.Certificate.PairSemantics.sound2444_e`, `OAI.MUB6.Certificate.PairSemantics.sound2445_e`, `OAI.MUB6.Certificate.PairSemantics.sound2454_e`, `OAI.MUB6.Certificate.PairSemantics.sound2456_e`, `OAI.MUB6.Certificate.PairSemantics.sound2457_e`, `OAI.MUB6.Certificate.PairSemantics.sound2463_e`, `OAI.MUB6.Certificate.PairSemantics.sound2464_e`, `OAI.MUB6.Certificate.PairSemantics.sound2465_e`, `OAI.MUB6.Certificate.PairSemantics.sound2472_e`, `OAI.MUB6.Certificate.PairSemantics.sound2473_e`, `OAI.MUB6.Certificate.PairSemantics.sound2477_e`, `OAI.MUB6.Certificate.PairSemantics.sound2479_e`, `OAI.MUB6.Certificate.PairSemantics.sound2489_e`, `OAI.MUB6.Certificate.PairSemantics.sound2490_e`, `OAI.MUB6.Certificate.PairSemantics.sound2491_e`, `OAI.MUB6.Certificate.PairSemantics.sound2492_e`, `OAI.MUB6.Certificate.PairSemantics.sound2507_e`, `OAI.MUB6.Certificate.PairSemantics.sound2520_e`, `OAI.MUB6.Certificate.PairSemantics.sound2521_e`, `OAI.MUB6.Certificate.PairSemantics.sound2522_e`, `OAI.MUB6.Certificate.PairSemantics.sound2524_e`, `OAI.MUB6.Certificate.PairSemantics.sound2525_e`, `OAI.MUB6.Certificate.PairSemantics.sound2527_e`, `OAI.MUB6.Certificate.PairSemantics.sound2533_e`, `OAI.MUB6.Certificate.PairSemantics.sound2540_e`, `OAI.MUB6.Certificate.PairSemantics.sound2546_e`, `OAI.MUB6.Certificate.PairSemantics.sound2547_e`, `OAI.MUB6.Certificate.PairSemantics.sound2548_e`, `OAI.MUB6.Certificate.PairSemantics.sound2557_e`, `OAI.MUB6.Certificate.PairSemantics.sound2558_e`, `OAI.MUB6.Certificate.PairSemantics.sound2559_e`, `OAI.MUB6.Certificate.PairSemantics.sound2564_e`, `OAI.MUB6.Certificate.PairSemantics.sound2565_e`, `OAI.MUB6.Certificate.PairSemantics.sound2566_e`, `OAI.MUB6.Certificate.PairSemantics.sound2573_e`, `OAI.MUB6.Certificate.PairSemantics.sound2578_e`, `OAI.MUB6.Certificate.PairSemantics.sound2580_e`, `OAI.MUB6.Certificate.PairSemantics.sound2593_e`, `OAI.MUB6.Certificate.PairSemantics.sound2602_e`, `OAI.MUB6.Certificate.PairSemantics.sound2604_e`, `OAI.MUB6.Certificate.PairSemantics.sound2606_e`, `OAI.MUB6.Certificate.PairSemantics.sound2619_e`, `OAI.MUB6.Certificate.PairSemantics.sound2620_e`, `OAI.MUB6.Certificate.PairSemantics.sound2623_e`, `OAI.MUB6.Certificate.PairSemantics.sound2627_e`, `OAI.MUB6.Certificate.PairSemantics.sound2641_e`, `OAI.MUB6.Certificate.PairSemantics.sound2657_e`, `OAI.MUB6.Certificate.PairSemantics.sound2658_e`, `OAI.MUB6.Certificate.PairSemantics.sound2661_e`, `OAI.MUB6.Certificate.PairSemantics.sound2666_e`, `OAI.MUB6.Certificate.PairSemantics.sound2669_e`, `OAI.MUB6.Certificate.PairSemantics.sound2670_e`, `OAI.MUB6.Certificate.PairSemantics.sound2671_e`, `OAI.MUB6.Certificate.PairSemantics.sound2686_e`, `OAI.MUB6.Certificate.PairSemantics.sound2690_e`, `OAI.MUB6.Certificate.PairSemantics.sound2693_e`, `OAI.MUB6.Certificate.PairSemantics.sound2698_e`, `OAI.MUB6.Certificate.PairSemantics.sound2708_e`, `OAI.MUB6.Certificate.PairSemantics.sound2710_e`, `OAI.MUB6.Certificate.PairSemantics.sound2714_e`, `OAI.MUB6.Certificate.PairSemantics.sound2729_e`, `OAI.MUB6.Certificate.PairSemantics.sound2732_e`, `OAI.MUB6.Certificate.PairSemantics.sound2733_e`, `OAI.MUB6.Certificate.PairSemantics.sound2735_e`, `OAI.MUB6.Certificate.PairSemantics.sound2754_e`, `OAI.MUB6.Certificate.PairSemantics.sound2757_e`, `OAI.MUB6.Certificate.PairSemantics.sound2788_e`, `OAI.MUB6.Certificate.PairSemantics.sound2790_e`, `OAI.MUB6.Certificate.PairSemantics.sound2793_e`, `OAI.MUB6.Certificate.PairSemantics.sound2807_e`, `OAI.MUB6.Certificate.PairSemantics.sound2817_e`, `OAI.MUB6.Certificate.PairSemantics.sound2829_e`, `OAI.MUB6.Certificate.PairSemantics.sound2836_e`, `OAI.MUB6.Certificate.PairSemantics.sound2845_e`, `OAI.MUB6.Certificate.PairSemantics.sound2853_e`, `OAI.MUB6.Certificate.PairSemantics.sound2854_e`, `OAI.MUB6.Certificate.PairSemantics.sound2858_e`, `OAI.MUB6.Certificate.PairSemantics.sound2863_e`, `OAI.MUB6.Certificate.PairSemantics.sound2864_e`, `OAI.MUB6.Certificate.PairSemantics.sound2865_e`, `OAI.MUB6.Certificate.PairSemantics.sound2866_e`, `OAI.MUB6.Certificate.PairSemantics.sound2867_e`, `OAI.MUB6.Certificate.PairSemantics.sound2868_e`, `OAI.MUB6.Certificate.PairSemantics.sound2872_e`, `OAI.MUB6.Certificate.PairSemantics.sound2873_e`, `OAI.MUB6.Certificate.PairSemantics.sound2874_e`, `OAI.MUB6.Certificate.PairSemantics.sound2875_e`, `OAI.MUB6.Certificate.PairSemantics.sound2878_e`, `OAI.MUB6.Certificate.PairSemantics.sound2879_e`, `OAI.MUB6.Certificate.PairSemantics.sound2880_e`, `OAI.MUB6.Certificate.PairSemantics.sound2882_e`, `OAI.MUB6.Certificate.PairSemantics.sound2883_e`, `OAI.MUB6.Certificate.PairSemantics.sound2884_e`, `OAI.MUB6.Certificate.PairSemantics.sound2887_e`, `OAI.MUB6.Certificate.PairSemantics.sound2888_e`, `OAI.MUB6.Certificate.PairSemantics.sound2889_e`, `OAI.MUB6.Certificate.PairSemantics.sound2890_e`, `OAI.MUB6.Certificate.PairSemantics.sound2891_e`, `OAI.MUB6.Certificate.PairSemantics.sound2892_e`, `OAI.MUB6.Certificate.PairSemantics.sound2894_e`, `OAI.MUB6.Certificate.PairSemantics.sound2895_e`, `OAI.MUB6.Certificate.PairSemantics.sound2896_e`, `OAI.MUB6.Certificate.PairSemantics.sound2897_e`, `OAI.MUB6.Certificate.PairSemantics.sound2898_e`, `OAI.MUB6.Certificate.PairSemantics.sound2899_e`, `OAI.MUB6.Certificate.PairSemantics.sound2900_e`, `OAI.MUB6.Certificate.PairSemantics.sound2901_e`, `OAI.MUB6.Certificate.PairSemantics.sound2902_e`, `OAI.MUB6.Certificate.PairSemantics.sound2904_e`, `OAI.MUB6.Certificate.PairSemantics.sound2905_e`, `OAI.MUB6.Certificate.PairSemantics.sound2906_e`, `OAI.MUB6.Certificate.PairSemantics.sound2908_e`, `OAI.MUB6.Certificate.PairSemantics.sound2909_e`, `OAI.MUB6.Certificate.PairSemantics.sound2910_e`, `OAI.MUB6.Certificate.PairSemantics.sound2912_e`, `OAI.MUB6.Certificate.PairSemantics.sound2913_e`, `OAI.MUB6.Certificate.PairSemantics.sound2914_e`, `OAI.MUB6.Certificate.PairSemantics.sound2915_e`, `OAI.MUB6.Certificate.PairSemantics.sound2916_e`, `OAI.MUB6.Certificate.PairSemantics.sound2917_e`, `OAI.MUB6.Certificate.PairSemantics.sound2919_e`, `OAI.MUB6.Certificate.PairSemantics.sound2920_e`, `OAI.MUB6.Certificate.PairSemantics.sound2922_e`, `OAI.MUB6.Certificate.PairSemantics.sound2924_e`, `OAI.MUB6.Certificate.PairSemantics.sound2925_e`, `OAI.MUB6.Certificate.PairSemantics.sound2926_e`, `OAI.MUB6.Certificate.PairSemantics.sound2927_e`, `OAI.MUB6.Certificate.PairSemantics.sound2928_e`, `OAI.MUB6.Certificate.PairSemantics.sound2929_e`, `OAI.MUB6.Certificate.PairSemantics.sound2931_e`, `OAI.MUB6.Certificate.PairSemantics.sound2933_e`, `OAI.MUB6.Certificate.PairSemantics.sound2935_e`, `OAI.MUB6.Certificate.PairSemantics.sound2936_e`, `OAI.MUB6.Certificate.PairSemantics.sound2939_e`, `OAI.MUB6.Certificate.PairSemantics.sound2940_e`, `OAI.MUB6.Certificate.PairSemantics.sound2941_e`, `OAI.MUB6.Certificate.PairSemantics.sound2942_e`, `OAI.MUB6.Certificate.PairSemantics.sound2943_e`, `OAI.MUB6.Certificate.PairSemantics.sound2944_e`, `OAI.MUB6.Certificate.PairSemantics.sound2946_e`, `OAI.MUB6.Certificate.PairSemantics.sound2949_e`, `OAI.MUB6.Certificate.PairSemantics.sound2950_e`, `OAI.MUB6.Certificate.PairSemantics.sound2951_e`, `OAI.MUB6.Certificate.PairSemantics.sound2952_e`, `OAI.MUB6.Certificate.PairSemantics.sound2953_e`, `OAI.MUB6.Certificate.PairSemantics.sound2954_e`, `OAI.MUB6.Certificate.PairSemantics.sound2956_e`, `OAI.MUB6.Certificate.PairSemantics.sound2957_e`, `OAI.MUB6.Certificate.PairSemantics.sound2959_e`, `OAI.MUB6.Certificate.PairSemantics.sound2960_e`, `OAI.MUB6.Certificate.PairSemantics.sound2961_e`, `OAI.MUB6.Certificate.PairSemantics.sound2962_e`, `OAI.MUB6.Certificate.PairSemantics.sound2963_e`, `OAI.MUB6.Certificate.PairSemantics.sound2964_e`, `OAI.MUB6.Certificate.PairSemantics.sound2965_e`, `OAI.MUB6.Certificate.PairSemantics.sound2966_e`, `OAI.MUB6.Certificate.PairSemantics.sound2967_e`, `OAI.MUB6.Certificate.PairSemantics.sound2968_e`, `OAI.MUB6.Certificate.PairSemantics.sound2969_e`, `OAI.MUB6.Certificate.PairSemantics.sound2970_e`, `OAI.MUB6.Certificate.PairSemantics.sound2972_e`, `OAI.MUB6.Certificate.PairSemantics.sound2973_e`, `OAI.MUB6.Certificate.PairSemantics.sound2974_e`, `OAI.MUB6.Certificate.PairSemantics.sound2975_e`, `OAI.MUB6.Certificate.PairSemantics.sound2976_e`, `OAI.MUB6.Certificate.PairSemantics.sound2977_e`, `OAI.MUB6.Certificate.PairSemantics.sound2979_e`, `OAI.MUB6.Certificate.PairSemantics.sound2980_e`, `OAI.MUB6.Certificate.PairSemantics.sound2984_e`, `OAI.MUB6.Certificate.PairSemantics.sound2985_e`, `OAI.MUB6.Certificate.PairSemantics.sound2986_e`, `OAI.MUB6.Certificate.PairSemantics.sound2987_e`, `OAI.MUB6.Certificate.PairSemantics.sound2989_e`, `OAI.MUB6.Certificate.PairSemantics.sound2990_e`, `OAI.MUB6.Certificate.PairSemantics.sound2991_e`, `OAI.MUB6.Certificate.PairSemantics.sound2992_e`, `OAI.MUB6.Certificate.PairSemantics.sound2994_e`, `OAI.MUB6.Certificate.PairSemantics.sound2996_e`, `OAI.MUB6.Certificate.PairSemantics.sound2997_e`, `OAI.MUB6.Certificate.PairSemantics.sound2998_e`, `OAI.MUB6.Certificate.PairSemantics.sound2999_e`, `OAI.MUB6.Certificate.PairSemantics.sound3000_e`, `OAI.MUB6.Certificate.PairSemantics.sound3001_e`, `OAI.MUB6.Certificate.PairSemantics.sound3002_e`, `OAI.MUB6.Certificate.PairSemantics.sound3004_e`, `OAI.MUB6.Certificate.PairSemantics.sound3006_e`, `OAI.MUB6.Certificate.PairSemantics.sound3007_e`, `OAI.MUB6.Certificate.PairSemantics.sound3009_e`, `OAI.MUB6.Certificate.PairSemantics.sound3011_e`, `OAI.MUB6.Certificate.PairSemantics.sound3012_e`, `OAI.MUB6.Certificate.PairSemantics.sound3013_e`, `OAI.MUB6.Certificate.PairSemantics.sound3014_e`, `OAI.MUB6.Certificate.PairSemantics.sound3015_e`, `OAI.MUB6.Certificate.PairSemantics.sound3016_e`, `OAI.MUB6.Certificate.PairSemantics.sound3017_e`, `OAI.MUB6.Certificate.PairSemantics.sound3018_e`, `OAI.MUB6.Certificate.PairSemantics.sound3019_e`, `OAI.MUB6.Certificate.PairSemantics.sound3020_e`, `OAI.MUB6.Certificate.PairSemantics.sound3021_e`, `OAI.MUB6.Certificate.PairSemantics.sound3022_e`, `OAI.MUB6.Certificate.PairSemantics.sound3023_e`, `OAI.MUB6.Certificate.PairSemantics.sound3024_e`, `OAI.MUB6.Certificate.PairSemantics.sound3025_e`, `OAI.MUB6.Certificate.PairSemantics.sound3026_e`, `OAI.MUB6.Certificate.PairSemantics.sound3027_e`, `OAI.MUB6.Certificate.PairSemantics.sound3028_e`, `OAI.MUB6.Certificate.PairSemantics.sound3029_e`, `OAI.MUB6.Certificate.PairSemantics.sound3030_e`, `OAI.MUB6.Certificate.PairSemantics.sound3032_e`, `OAI.MUB6.Certificate.PairSemantics.sound3034_e`, `OAI.MUB6.Certificate.PairSemantics.sound3035_e`, `OAI.MUB6.Certificate.PairSemantics.sound3036_e`, `OAI.MUB6.Certificate.PairSemantics.sound3037_e`, `OAI.MUB6.Certificate.PairSemantics.sound3038_e`, `OAI.MUB6.Certificate.PairSemantics.sound3039_e`, `OAI.MUB6.Certificate.PairSemantics.sound3040_e`, `OAI.MUB6.Certificate.PairSemantics.sound3041_e`, `OAI.MUB6.Certificate.PairSemantics.sound3042_e`, `OAI.MUB6.Certificate.PairSemantics.sound3045_e`, `OAI.MUB6.Certificate.PairSemantics.sound3049_e`, `OAI.MUB6.Certificate.PairSemantics.sound3050_e`, `OAI.MUB6.Certificate.PairSemantics.sound3051_e`, `OAI.MUB6.Certificate.PairSemantics.sound3052_e`, `OAI.MUB6.Certificate.PairSemantics.sound3053_e`, `OAI.MUB6.Certificate.PairSemantics.sound3054_e`, `OAI.MUB6.Certificate.PairSemantics.sound3055_e`, `OAI.MUB6.Certificate.PairSemantics.sound3057_e`, `OAI.MUB6.Certificate.PairSemantics.sound3059_e`, `OAI.MUB6.Certificate.PairSemantics.sound3060_e`, `OAI.MUB6.Certificate.PairSemantics.sound3061_e`, `OAI.MUB6.Certificate.PairSemantics.sound3062_e`, `OAI.MUB6.Certificate.PairSemantics.sound3063_e`, `OAI.MUB6.Certificate.PairSemantics.sound3065_e`, `OAI.MUB6.Certificate.PairSemantics.sound3066_e`, `OAI.MUB6.Certificate.PairSemantics.sound3067_e`, `OAI.MUB6.Certificate.PairSemantics.sound3068_e`, `OAI.MUB6.Certificate.PairSemantics.sound3069_e`, `OAI.MUB6.Certificate.PairSemantics.sound3071_e`, `OAI.MUB6.Certificate.PairSemantics.sound3072_e`, `OAI.MUB6.Certificate.PairSemantics.sound3073_e`, `OAI.MUB6.Certificate.PairSemantics.sound3074_e`, `OAI.MUB6.Certificate.PairSemantics.sound3075_e`, `OAI.MUB6.Certificate.PairSemantics.sound3076_e`, `OAI.MUB6.Certificate.PairSemantics.sound3077_e`, `OAI.MUB6.Certificate.PairSemantics.sound3078_e`, `OAI.MUB6.Certificate.PairSemantics.sound3079_e`, `OAI.MUB6.Certificate.PairSemantics.sound3081_e`, `OAI.MUB6.Certificate.PairSemantics.sound3082_e`, `OAI.MUB6.Certificate.PairSemantics.sound3084_e`, `OAI.MUB6.Certificate.PairSemantics.sound3085_e`, `OAI.MUB6.Certificate.PairSemantics.sound3086_e`, `OAI.MUB6.Certificate.PairSemantics.sound3087_e`, `OAI.MUB6.Certificate.PairSemantics.sound3088_e`, `OAI.MUB6.Certificate.PairSemantics.sound3090_e`, `OAI.MUB6.Certificate.PairSemantics.sound3091_e`, `OAI.MUB6.Certificate.PairSemantics.sound3092_e`, `OAI.MUB6.Certificate.PairSemantics.sound3093_e`, `OAI.MUB6.Certificate.PairSemantics.sound3094_e`, `OAI.MUB6.Certificate.PairSemantics.sound3095_e`, `OAI.MUB6.Certificate.PairSemantics.sound3096_e`, `OAI.MUB6.Certificate.PairSemantics.sound3098_e`, `OAI.MUB6.Certificate.PairSemantics.sound3099_e`, `OAI.MUB6.Certificate.PairSemantics.sound3100_e`, `OAI.MUB6.Certificate.PairSemantics.sound3101_e`, `OAI.MUB6.Certificate.PairSemantics.sound3105_e`, `OAI.MUB6.Certificate.PairSemantics.sound3106_e`, `OAI.MUB6.Certificate.PairSemantics.sound3107_e`, `OAI.MUB6.Certificate.PairSemantics.sound3108_e`, `OAI.MUB6.Certificate.PairSemantics.sound3110_e`, `OAI.MUB6.Certificate.PairSemantics.sound3111_e`, `OAI.MUB6.Certificate.PairSemantics.sound3112_e`, `OAI.MUB6.Certificate.PairSemantics.sound3113_e`, `OAI.MUB6.Certificate.PairSemantics.sound3114_e`, `OAI.MUB6.Certificate.PairSemantics.sound3115_e`, `OAI.MUB6.Certificate.PairSemantics.sound3118_e`, `OAI.MUB6.Certificate.PairSemantics.sound3119_e`, `OAI.MUB6.Certificate.PairSemantics.sound3120_e`, `OAI.MUB6.Certificate.PairSemantics.sound3122_e`, `OAI.MUB6.Certificate.PairSemantics.sound3123_e`, `OAI.MUB6.Certificate.PairSemantics.sound3124_e`, `OAI.MUB6.Certificate.PairSemantics.sound3125_e`, `OAI.MUB6.Certificate.PairSemantics.sound3127_e`, `OAI.MUB6.Certificate.PairSemantics.sound3128_e`, `OAI.MUB6.Certificate.PairSemantics.sound3129_e`, `OAI.MUB6.Certificate.PairSemantics.sound3130_e`, `OAI.MUB6.Certificate.PairSemantics.sound3131_e`, `OAI.MUB6.Certificate.PairSemantics.sound3132_e`, `OAI.MUB6.Certificate.PairSemantics.sound3133_e`, `OAI.MUB6.Certificate.PairSemantics.sound3135_e`, `OAI.MUB6.Certificate.PairSemantics.sound3136_e`, `OAI.MUB6.Certificate.PairSemantics.sound3137_e`, `OAI.MUB6.Certificate.PairSemantics.sound3138_e`, `OAI.MUB6.Certificate.PairSemantics.sound3139_e`, `OAI.MUB6.Certificate.PairSemantics.sound3140_e`, `OAI.MUB6.Certificate.PairSemantics.sound3141_e`, `OAI.MUB6.Certificate.PairSemantics.sound3142_e`, `OAI.MUB6.Certificate.PairSemantics.sound3144_e`, `OAI.MUB6.Certificate.PairSemantics.sound3145_e`, `OAI.MUB6.Certificate.PairSemantics.sound3146_e`, `OAI.MUB6.Certificate.PairSemantics.sound3149_e`, `OAI.MUB6.Certificate.PairSemantics.sound3150_e`, `OAI.MUB6.Certificate.PairSemantics.sound3151_e`, `OAI.MUB6.Certificate.PairSemantics.sound3152_e`, `OAI.MUB6.Certificate.PairSemantics.sound3153_e`, `OAI.MUB6.Certificate.PairSemantics.sound3154_e`, `OAI.MUB6.Certificate.PairSemantics.sound3158_e`, `OAI.MUB6.Certificate.PairSemantics.sound3159_e`, `OAI.MUB6.Certificate.PairSemantics.sound3160_e`, `OAI.MUB6.Certificate.PairSemantics.sound3161_e`, `OAI.MUB6.Certificate.PairSemantics.sound3163_e`, `OAI.MUB6.Certificate.PairSemantics.sound3164_e`, `OAI.MUB6.Certificate.PairSemantics.sound3166_e`, `OAI.MUB6.Certificate.PairSemantics.sound3167_e`, `OAI.MUB6.Certificate.PairSemantics.sound3169_e`, `OAI.MUB6.Certificate.PairSemantics.sound3170_e`, `OAI.MUB6.Certificate.PairSemantics.sound3171_e`, `OAI.MUB6.Certificate.PairSemantics.sound3172_e`, `OAI.MUB6.Certificate.PairSemantics.sound3173_e`, `OAI.MUB6.Certificate.PairSemantics.sound3174_e`, `OAI.MUB6.Certificate.PairSemantics.sound3176_e`, `OAI.MUB6.Certificate.PairSemantics.sound3178_e`, `OAI.MUB6.Certificate.PairSemantics.sound3179_e`, `OAI.MUB6.Certificate.PairSemantics.sound3180_e`, `OAI.MUB6.Certificate.PairSemantics.sound3181_e`, `OAI.MUB6.Certificate.PairSemantics.sound3183_e`, `OAI.MUB6.Certificate.PairSemantics.sound3184_e`, `OAI.MUB6.Certificate.PairSemantics.sound3185_e`, `OAI.MUB6.Certificate.PairSemantics.sound3187_e`, `OAI.MUB6.Certificate.PairSemantics.sound3188_e`, `OAI.MUB6.Certificate.PairSemantics.sound3189_e`, `OAI.MUB6.Certificate.PairSemantics.sound3191_e`, `OAI.MUB6.Certificate.PairSemantics.sound3192_e`, `OAI.MUB6.Certificate.PairSemantics.sound3193_e`, `OAI.MUB6.Certificate.PairSemantics.sound3194_e`, `OAI.MUB6.Certificate.PairSemantics.sound3195_e`, `OAI.MUB6.Certificate.PairSemantics.sound3196_e`, `OAI.MUB6.Certificate.PairSemantics.sound3197_e`, `OAI.MUB6.Certificate.PairSemantics.sound3198_e`, `OAI.MUB6.Certificate.PairSemantics.sound3199_e`, `OAI.MUB6.Certificate.PairSemantics.sound3200_e`, `OAI.MUB6.Certificate.PairSemantics.sound3201_e`, `OAI.MUB6.Certificate.PairSemantics.sound3202_e`, `OAI.MUB6.Certificate.PairSemantics.sound3203_e`, `OAI.MUB6.Certificate.PairSemantics.sound3204_e`, `OAI.MUB6.Certificate.PairSemantics.sound3205_e`, `OAI.MUB6.Certificate.PairSemantics.sound3206_e`, `OAI.MUB6.Certificate.PairSemantics.sound3208_e`, `OAI.MUB6.Certificate.PairSemantics.sound3209_e`, `OAI.MUB6.Certificate.PairSemantics.sound3211_e`, `OAI.MUB6.Certificate.PairSemantics.sound3212_e`, `OAI.MUB6.Certificate.PairSemantics.sound3213_e`, `OAI.MUB6.Certificate.PairSemantics.sound3215_e`, `OAI.MUB6.Certificate.PairSemantics.sound3216_e`, `OAI.MUB6.Certificate.PairSemantics.sound3218_e`, `OAI.MUB6.Certificate.PairSemantics.sound3220_e`, `OAI.MUB6.Certificate.PairSemantics.sound3221_e`, `OAI.MUB6.Certificate.PairSemantics.sound3222_e`, `OAI.MUB6.Certificate.PairSemantics.sound3223_e`, `OAI.MUB6.Certificate.PairSemantics.sound3224_e`, `OAI.MUB6.Certificate.PairSemantics.sound3225_e`, `OAI.MUB6.Certificate.PairSemantics.sound3226_e`, `OAI.MUB6.Certificate.PairSemantics.sound3227_e`, `OAI.MUB6.Certificate.PairSemantics.sound3228_e`, `OAI.MUB6.Certificate.PairSemantics.sound3229_e`, `OAI.MUB6.Certificate.PairSemantics.sound3230_e`, `OAI.MUB6.Certificate.PairSemantics.sound3233_e`, `OAI.MUB6.Certificate.PairSemantics.sound3234_e`, `OAI.MUB6.Certificate.PairSemantics.sound3235_e`, `OAI.MUB6.Certificate.PairSemantics.sound3237_e`, `OAI.MUB6.Certificate.PairSemantics.sound3238_e`, `OAI.MUB6.Certificate.PairSemantics.sound3240_e`, `OAI.MUB6.Certificate.PairSemantics.sound3242_e`, `OAI.MUB6.Certificate.PairSemantics.sound3243_e`, `OAI.MUB6.Certificate.PairSemantics.sound3244_e`, `OAI.MUB6.Certificate.PairSemantics.sound3246_e`, `OAI.MUB6.Certificate.PairSemantics.sound3247_e`, `OAI.MUB6.Certificate.PairSemantics.sound3248_e`, `OAI.MUB6.Certificate.PairSemantics.sound3249_e`, `OAI.MUB6.Certificate.PairSemantics.sound3253_e`, `OAI.MUB6.Certificate.PairSemantics.sound3254_e`, `OAI.MUB6.Certificate.PairSemantics.sound3255_e`, `OAI.MUB6.Certificate.PairSemantics.sound3256_e`, `OAI.MUB6.Certificate.PairSemantics.sound3258_e`, `OAI.MUB6.Certificate.PairSemantics.sound3260_e`, `OAI.MUB6.Certificate.PairSemantics.sound3262_e`, `OAI.MUB6.Certificate.PairSemantics.sound3263_e`, `OAI.MUB6.Certificate.PairSemantics.sound3264_e`, `OAI.MUB6.Certificate.PairSemantics.sound3266_e`, `OAI.MUB6.Certificate.PairSemantics.sound3267_e`, `OAI.MUB6.Certificate.PairSemantics.sound3268_e`, `OAI.MUB6.Certificate.PairSemantics.sound3269_e`, `OAI.MUB6.Certificate.PairSemantics.sound3271_e`, `OAI.MUB6.Certificate.PairSemantics.sound3272_e`, `OAI.MUB6.Certificate.PairSemantics.sound3273_e`, `OAI.MUB6.Certificate.PairSemantics.sound3274_e`, `OAI.MUB6.Certificate.PairSemantics.sound3275_e`, `OAI.MUB6.Certificate.PairSemantics.sound3276_e`, `OAI.MUB6.Certificate.PairSemantics.sound3277_e`, `OAI.MUB6.Certificate.PairSemantics.sound3278_e`, `OAI.MUB6.Certificate.PairSemantics.sound3279_e`, `OAI.MUB6.Certificate.PairSemantics.sound3280_e`, `OAI.MUB6.Certificate.PairSemantics.sound3281_e`, `OAI.MUB6.Certificate.PairSemantics.sound3282_e`, `OAI.MUB6.Certificate.PairSemantics.sound3283_e`, `OAI.MUB6.Certificate.PairSemantics.sound3284_e`, `OAI.MUB6.Certificate.PairSemantics.sound3288_e`, `OAI.MUB6.Certificate.PairSemantics.sound3289_e`, `OAI.MUB6.Certificate.PairSemantics.sound3290_e`, `OAI.MUB6.Certificate.PairSemantics.sound3291_e`, `OAI.MUB6.Certificate.PairSemantics.sound3292_e`, `OAI.MUB6.Certificate.PairSemantics.sound3293_e`, `OAI.MUB6.Certificate.PairSemantics.sound3294_e`, `OAI.MUB6.Certificate.PairSemantics.sound3295_e`, `OAI.MUB6.Certificate.PairSemantics.sound3296_e`, `OAI.MUB6.Certificate.PairSemantics.sound3297_e`, `OAI.MUB6.Certificate.PairSemantics.sound3298_e`, `OAI.MUB6.Certificate.PairSemantics.sound3299_e`, `OAI.MUB6.Certificate.PairSemantics.sound3300_e`, `OAI.MUB6.Certificate.PairSemantics.sound3301_e`, `OAI.MUB6.Certificate.PairSemantics.sound3302_e`, `OAI.MUB6.Certificate.PairSemantics.sound3303_e`, `OAI.MUB6.Certificate.PairSemantics.sound3304_e`, `OAI.MUB6.Certificate.PairSemantics.sound3305_e`, `OAI.MUB6.Certificate.PairSemantics.sound3307_e`, `OAI.MUB6.Certificate.PairSemantics.sound3308_e`, `OAI.MUB6.Certificate.PairSemantics.sound3309_e`, `OAI.MUB6.Certificate.PairSemantics.sound3310_e`, `OAI.MUB6.Certificate.PairSemantics.sound3311_e`, `OAI.MUB6.Certificate.PairSemantics.sound3313_e`, `OAI.MUB6.Certificate.PairSemantics.sound3314_e`, `OAI.MUB6.Certificate.PairSemantics.sound3315_e`, `OAI.MUB6.Certificate.PairSemantics.sound3316_e`, `OAI.MUB6.Certificate.PairSemantics.sound3317_e`, `OAI.MUB6.Certificate.PairSemantics.sound3319_e`, `OAI.MUB6.Certificate.PairSemantics.sound3322_e`, `OAI.MUB6.Certificate.PairSemantics.sound3324_e`, `OAI.MUB6.Certificate.PairSemantics.sound3325_e`, `OAI.MUB6.Certificate.PairSemantics.sound3326_e`, `OAI.MUB6.Certificate.PairSemantics.sound3327_e`, `OAI.MUB6.Certificate.PairSemantics.sound3328_e`, `OAI.MUB6.Certificate.PairSemantics.sound3331_e`, `OAI.MUB6.Certificate.PairSemantics.sound3333_e`, `OAI.MUB6.Certificate.PairSemantics.sound3334_e`, `OAI.MUB6.Certificate.PairSemantics.sound3335_e`, `OAI.MUB6.Certificate.PairSemantics.sound3336_e`, `OAI.MUB6.Certificate.PairSemantics.sound3338_e`, `OAI.MUB6.Certificate.PairSemantics.sound3339_e`, `OAI.MUB6.Certificate.PairSemantics.sound3341_e`, `OAI.MUB6.Certificate.PairSemantics.sound3343_e`, `OAI.MUB6.Certificate.PairSemantics.sound3345_e`, `OAI.MUB6.Certificate.PairSemantics.sound3346_e`, `OAI.MUB6.Certificate.PairSemantics.sound3347_e`, `OAI.MUB6.Certificate.PairSemantics.sound3348_e`, `OAI.MUB6.Certificate.PairSemantics.sound3349_e`, `OAI.MUB6.Certificate.PairSemantics.sound3350_e`, `OAI.MUB6.Certificate.PairSemantics.sound3351_e`, `OAI.MUB6.Certificate.PairSemantics.sound3352_e`, `OAI.MUB6.Certificate.PairSemantics.sound3353_e`, `OAI.MUB6.Certificate.PairSemantics.sound3354_e`, `OAI.MUB6.Certificate.PairSemantics.sound3355_e`, `OAI.MUB6.Certificate.PairSemantics.sound3356_e`, `OAI.MUB6.Certificate.PairSemantics.sound3357_e`, `OAI.MUB6.Certificate.PairSemantics.sound3358_e`, `OAI.MUB6.Certificate.PairSemantics.sound3359_e`, `OAI.MUB6.Certificate.PairSemantics.sound3360_e`, `OAI.MUB6.Certificate.PairSemantics.sound3361_e`, `OAI.MUB6.Certificate.PairSemantics.sound3362_e`, `OAI.MUB6.Certificate.PairSemantics.sound3363_e`, `OAI.MUB6.Certificate.PairSemantics.sound3364_e`, `OAI.MUB6.Certificate.PairSemantics.sound3366_e`, `OAI.MUB6.Certificate.PairSemantics.sound3367_e`, `OAI.MUB6.Certificate.PairSemantics.sound3368_e`, `OAI.MUB6.Certificate.PairSemantics.sound3369_e`, `OAI.MUB6.Certificate.PairSemantics.sound3370_e`, `OAI.MUB6.Certificate.PairSemantics.sound3371_e`, `OAI.MUB6.Certificate.PairSemantics.sound3372_e`, `OAI.MUB6.Certificate.PairSemantics.sound3375_e`, `OAI.MUB6.Certificate.PairSemantics.sound3376_e`, `OAI.MUB6.Certificate.PairSemantics.sound3377_e`, `OAI.MUB6.Certificate.PairSemantics.sound3378_e`, `OAI.MUB6.Certificate.PairSemantics.sound3380_e`, `OAI.MUB6.Certificate.PairSemantics.sound3382_e`, `OAI.MUB6.Certificate.PairSemantics.sound3383_e`, `OAI.MUB6.Certificate.PairSemantics.sound3384_e`, `OAI.MUB6.Certificate.PairSemantics.sound3385_e`, `OAI.MUB6.Certificate.PairSemantics.sound3387_e`, `OAI.MUB6.Certificate.PairSemantics.sound3388_e`, `OAI.MUB6.Certificate.PairSemantics.sound3389_e`, `OAI.MUB6.Certificate.PairSemantics.sound3390_e`, `OAI.MUB6.Certificate.PairSemantics.sound3391_e`, `OAI.MUB6.Certificate.PairSemantics.sound3392_e`, `OAI.MUB6.Certificate.PairSemantics.sound3393_e`, `OAI.MUB6.Certificate.PairSemantics.sound3394_e`, `OAI.MUB6.Certificate.PairSemantics.sound3395_e`, `OAI.MUB6.Certificate.PairSemantics.sound3396_e`, `OAI.MUB6.Certificate.PairSemantics.sound3397_e`, `OAI.MUB6.Certificate.PairSemantics.sound3399_e`, `OAI.MUB6.Certificate.PairSemantics.sound3400_e`, `OAI.MUB6.Certificate.PairSemantics.sound3401_e`, `OAI.MUB6.Certificate.PairSemantics.sound3402_e`, `OAI.MUB6.Certificate.PairSemantics.sound3405_e`, `OAI.MUB6.Certificate.PairSemantics.sound3407_e`, `OAI.MUB6.Certificate.PairSemantics.sound3408_e`, `OAI.MUB6.Certificate.PairSemantics.sound3411_e`, `OAI.MUB6.Certificate.PairSemantics.sound3412_e`, `OAI.MUB6.Certificate.PairSemantics.sound3413_e`, `OAI.MUB6.Certificate.PairSemantics.sound3414_e`, `OAI.MUB6.Certificate.PairSemantics.sound3415_e`, `OAI.MUB6.Certificate.PairSemantics.sound3416_e`, `OAI.MUB6.Certificate.PairSemantics.sound3417_e`, `OAI.MUB6.Certificate.PairSemantics.sound3418_e`, `OAI.MUB6.Certificate.PairSemantics.sound3419_e`, `OAI.MUB6.Certificate.PairSemantics.sound3420_e`, `OAI.MUB6.Certificate.PairSemantics.sound3421_e`, `OAI.MUB6.Certificate.PairSemantics.sound3422_e`, `OAI.MUB6.Certificate.PairSemantics.sound3423_e`, `OAI.MUB6.Certificate.PairSemantics.sound3424_e`, `OAI.MUB6.Certificate.PairSemantics.sound3425_e`, `OAI.MUB6.Certificate.PairSemantics.sound3428_e`, `OAI.MUB6.Certificate.PairSemantics.sound3431_e`, `OAI.MUB6.Certificate.PairSemantics.sound3433_e`, `OAI.MUB6.Certificate.PairSemantics.sound3434_e`, `OAI.MUB6.Certificate.PairSemantics.sound3435_e`, `OAI.MUB6.Certificate.PairSemantics.sound3436_e`, `OAI.MUB6.Certificate.PairSemantics.sound3437_e`, `OAI.MUB6.Certificate.PairSemantics.sound3439_e`, `OAI.MUB6.Certificate.PairSemantics.sound3440_e`, `OAI.MUB6.Certificate.PairSemantics.sound3441_e`, `OAI.MUB6.Certificate.PairSemantics.sound3442_e`, `OAI.MUB6.Certificate.PairSemantics.sound3443_e`, `OAI.MUB6.Certificate.PairSemantics.sound3444_e`, `OAI.MUB6.Certificate.PairSemantics.sound3447_e`, `OAI.MUB6.Certificate.PairSemantics.sound3449_e`, `OAI.MUB6.Certificate.PairSemantics.sound3451_e`, `OAI.MUB6.Certificate.PairSemantics.sound3454_e`, `OAI.MUB6.Certificate.PairSemantics.sound3455_e`, `OAI.MUB6.Certificate.PairSemantics.sound3456_e`, `OAI.MUB6.Certificate.PairSemantics.sound3457_e`, `OAI.MUB6.Certificate.PairSemantics.sound3458_e`, `OAI.MUB6.Certificate.PairSemantics.sound3459_e`, `OAI.MUB6.Certificate.PairSemantics.sound3460_e`, `OAI.MUB6.Certificate.PairSemantics.sound3461_e`, `OAI.MUB6.Certificate.PairSemantics.sound3462_e`, `OAI.MUB6.Certificate.PairSemantics.sound3463_e`, `OAI.MUB6.Certificate.PairSemantics.sound3467_e`, `OAI.MUB6.Certificate.PairSemantics.sound3468_e`, `OAI.MUB6.Certificate.PairTargetSemantics.pair_partition4_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm11_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm12_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm13_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm14_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm16_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm17_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm18_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm19_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm21_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm22_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm23_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm24_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm25_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm26_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm6_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm7_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm8_e` and `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm9_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_MUBSix

section
-- module Solutions.OAIQ106_MUB.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434

/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
/-- `simp` closes `2 ≤ ∞` in `WithTop ℕ∞` (the smoothness order) in Mathlib d13f23b; ours has the
lemma only for `1` and casts (AffineBernstein, `isSymmSndFDerivAt (by simp)`, 2026-10-26). -/
@[simp]
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.LEInfty.out
section Y
instance closedSubmoduleNormedAddCommGroup {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedAddCommGroup K :=
  inferInstanceAs (NormedAddCommGroup K.toSubmodule)
instance closedSubmoduleNormedSpace {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedSpace 𝕜 K :=
  inferInstanceAs (NormedSpace 𝕜 K.toSubmodule)
instance closedSubmoduleInner {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : InnerProductSpace 𝕜 K :=
  inferInstanceAs (InnerProductSpace 𝕜 K.toSubmodule)
end Y

/-- The underlying ⋆-subalgebra of a von Neumann algebra is norm closed, found by instance search in
d13f23b (Kadison similarity, oaiq-075). -/
instance vonNeumannToStarSubalgebraIsClosed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P : VonNeumannAlgebra H) : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  have := Set.isClosed_centralizer (Set.centralizer (P.carrier))
  rw [P.centralizer_centralizer'] at this
  exact this
/-- A closed commutative ⋆-subalgebra of a C⋆-algebra is a commutative C⋆-algebra, found by instance search
in d13f23b (Kadison similarity, oaiq-075). A def, made a local instance by the port only in modules naming
`CommCStarAlgebra` or `IsMulCommutative` (`oaiport.comm_cstar_line`): as a global instance it made `whnf` time out in
FactorGeneration modules with their own `CStarAlgebra` instances on a subalgebra (oaiq-122). -/
@[reducible]
noncomputable def starSubalgebraCommCStarAlgebra {B : Type*} [CStarAlgebra B] (A : StarSubalgebra ℂ B)
    [IsClosed (A : Set B)] [IsMulCommutative A] : CommCStarAlgebra A :=
  { StarSubalgebra.cstarAlgebra A with
    mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
section OAIVecLookup
variable {α : Type _}
@[simp] theorem vecCons3_one (a b c : α) : (![a, b, c] : Fin 3 → α) 1 = b := rfl
@[simp] theorem vecCons3_two (a b c : α) : (![a, b, c] : Fin 3 → α) 2 = c := rfl
@[simp] theorem vecCons4_one (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 1 = b := rfl
@[simp] theorem vecCons4_two (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 2 = c := rfl
@[simp] theorem vecCons4_three (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 3 = d := rfl
end OAIVecLookup
section OAIVecTail
variable {α : Type _}
@[simp] theorem vecConsTail1_1 (x : α) (f : Fin 1 → α) : (Matrix.vecCons x f : Fin 2 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_1 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_2 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_1 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail3_2 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_3 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_1 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail4_2 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail4_3 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_4 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 4 = f 3 := rfl
end OAIVecTail
@[simp] theorem fin3_mk_0 (h : 0 < 3) : (⟨0, h⟩ : Fin 3) = 0 := rfl
@[simp] theorem fin3_mk_1 (h : 1 < 3) : (⟨1, h⟩ : Fin 3) = 1 := rfl
@[simp] theorem fin3_mk_2 (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl
@[simp] theorem fin4_mk_0 (h : 0 < 4) : (⟨0, h⟩ : Fin 4) = 0 := rfl
@[simp] theorem fin4_mk_1 (h : 1 < 4) : (⟨1, h⟩ : Fin 4) = 1 := rfl
@[simp] theorem fin4_mk_2 (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := rfl
@[simp] theorem fin4_mk_3 (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := rfl
@[simp] theorem fin5_mk_0 (h : 0 < 5) : (⟨0, h⟩ : Fin 5) = 0 := rfl
@[simp] theorem fin5_mk_1 (h : 1 < 5) : (⟨1, h⟩ : Fin 5) = 1 := rfl
@[simp] theorem fin5_mk_2 (h : 2 < 5) : (⟨2, h⟩ : Fin 5) = 2 := rfl
@[simp] theorem fin5_mk_3 (h : 3 < 5) : (⟨3, h⟩ : Fin 5) = 3 := rfl
@[simp] theorem fin5_mk_4 (h : 4 < 5) : (⟨4, h⟩ : Fin 5) = 4 := rfl
/-- `norm_num` cannot decide equalities of `Fin` literals here (oaiq-091). -/
@[simp] theorem fin3_lit_0_1 : ((0 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin3_lit_0_2 : ((0 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_1_0 : ((1 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_1_2 : ((1 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_2_0 : ((2 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_2_1 : ((2 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_1 : ((0 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_2 : ((0 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_0_3 : ((0 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_1_0 : ((1 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_1_2 : ((1 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_1_3 : ((1 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_2_0 : ((2 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_2_1 : ((2 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_2_3 : ((2 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_3_0 : ((3 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_3_1 : ((3 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_3_2 : ((3 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_1 : ((0 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_0_2 : ((0 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_3 : ((0 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_0_4 : ((0 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_1_0 : ((1 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_1_2 : ((1 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_1_3 : ((1 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_1_4 : ((1 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_2_0 : ((2 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_2_1 : ((2 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_2_3 : ((2 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_2_4 : ((2 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_3_0 : ((3 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_3_1 : ((3 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_3_2 : ((3 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_3_4 : ((3 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_4_0 : ((4 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_4_1 : ((4 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_4_2 : ((4 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_4_3 : ((4 : Fin 5) = 3) ↔ False := by decide
/-- Mathlib d13f23b's `MeasurableSpace Circle` (Mathlib.MeasureTheory.Group.Circle): the subtype structure. A def,
turned on as a local instance in the modules that use the characters `𝐞`/`fourierChar`/`probChar` (q141). -/
@[reducible] def circleMeasurableSpace : MeasurableSpace Circle :=
  inferInstanceAs <| MeasurableSpace <| Subtype (· ∈ Submonoid.unitSphere ℂ)
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Matrix_Definitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mathematical definitions for the exact Fourier companion.

The character normalization is exactly 1/6, not an unnormalized sum.
-/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

def order (a : Charge) : ℕ := ∑ i, (a i).toNat

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Bases_Families
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restriction and cardinality lemmas. These reductions do not establish the
no-seven or completion theorem, which remain separate proof obligations. -/

noncomputable section
namespace MUB6

/-- Precise completion statement, including preservation of the original bases. -/
def SixExtendToSeven : Prop :=
  ∀ B : Fin 6 → Basis, IsMUBFamily B →
    ∃ C : Fin 7 → Basis, IsMUBFamily C ∧ ∀ i : Fin 6, C i.castSucc = B i

end MUB6

end

end OAI
end

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

/-- Complete a table of strict lower triangular entries with unit diagonal. -/
def lowerUnit {n : ℕ} (entries : Matrix (Fin n) (Fin n) ℚ) :
    Matrix (Fin n) (Fin n) ℚ :=
  fun i j => if j < i then entries i j else if i = j then 1 else 0

@[simp] theorem lowerUnit_diag {n : ℕ} (entries : Matrix (Fin n) (Fin n) ℚ)
    (i : Fin n) : lowerUnit entries i i = 1 := by simp [lowerUnit]

@[simp] theorem lowerUnit_above {n : ℕ} (entries : Matrix (Fin n) (Fin n) ℚ)
    {i j : Fin n} (h : i < j) : lowerUnit entries i j = 0 := by
  simp [lowerUnit, not_lt_of_ge h.le, ne_of_lt h]

end MUB6.Certificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Completion_Kraus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite trace-preserving Kraus maps

The proof establishes the fixed-point commutation step needed in Weiner's completion
argument. It replaces the appeal to two-positivity and the multiplicative domain
with the squared Hilbert--Schmidt norm of each commutator.
-/

namespace MUB6.Weiner

open scoped BigOperators ComplexOrder
open Matrix

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]

/-- A finite Kraus sum, with the adjoint on the left. -/
def kraus (A : ι → Matrix n n ℂ) (X : Matrix n n ℂ) : Matrix n n ℂ :=
  ∑ i, (A i)ᴴ * X * A i

end MUB6.Weiner

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Completion_Superoperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Realignment of a self-adjoint projection

The complement operator in Weiner's argument is an orthogonal projection whose
matrix is invariant under realignment. Its columns therefore form a finite
Kraus family; choosing an orthonormal basis of its range is unnecessary.
-/

namespace MUB6.Weiner

open Matrix
open scoped BigOperators ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Apply a matrix on pairs of indices to an ordinary matrix. -/
def applySuper (C : Matrix (n × n) (n × n) ℂ) (X : Matrix n n ℂ) : Matrix n n ℂ :=
  fun i j => ∑ p, C (i, j) p * X p.1 p.2

/-- A column of a superoperator, reshaped as an ordinary matrix. -/
def superColumn (C : Matrix (n × n) (n × n) ℂ) (p : n × n) : Matrix n n ℂ :=
  fun i j => C (i, j) p

/-- The realignment symmetry relevant to a Kraus decomposition. -/
def IsRealigned (C : Matrix (n × n) (n × n) ℂ) : Prop :=
  ∀ i j k l, C (i, j) (k, l) = C (l, j) (k, i)

end MUB6.Weiner

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Completion_Complement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The concrete complement supermatrix

The Hermitian and realignment symmetries are algebraic identities for arbitrary
complex vectors. Orthonormality and mutual unbiasedness are needed for the
separate unitality and idempotence identities.
-/

namespace MUB6.Weiner

open Matrix
open scoped BigOperators

variable {n ι κ : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [Fintype κ]

/-- Supermatrix of the unnormalized trace map `X ↦ trace(X) I`. -/
def traceMatrix : Matrix (n × n) (n × n) ℂ :=
  fun p q => if p.1 = p.2 ∧ q.1 = q.2 then 1 else 0

/-- Supermatrix of the sum of rank-one pinching maps for a vector family. -/
def pinchingMatrix (v : κ → n → ℂ) : Matrix (n × n) (n × n) ℂ :=
  fun p q => ∑ a, v a p.1 * star (v a p.2) * star (v a q.1) * v a q.2

/-- Candidate missing-basis projection for six bases in dimension six. -/
def complementMatrix (v : ι → κ → n → ℂ) : Matrix (n × n) (n × n) ℂ :=
  1 + traceMatrix - ∑ r, pinchingMatrix (v r)

end MUB6.Weiner

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Completion_Frame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rank-one frame identities used to calculate the complement projection. -/

namespace MUB6.Weiner

open Matrix
open scoped BigOperators

variable {I κ η n : Type*} [Fintype I] [Fintype κ] [Fintype η] [Fintype n]

/-- Sum of the rank-one operators of a finite vector family. -/
def frameOperator (v : κ → I → ℂ) : Matrix I I ℂ :=
  ∑ a, Matrix.vecMulVec (v a) (star (v a))

/-- Flatten the rank-one matrix associated with an arbitrary complex vector. -/
def projectorVector (v : n → ℂ) : n × n → ℂ := fun p => v p.1 * star (v p.2)

end MUB6.Weiner

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Completion_OrthogonalPinching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact multiplication tables for six and seven unbiased pinching operators. -/

namespace MUB6.Weiner

open Matrix
open scoped BigOperators

abbrev SuperSix := Matrix (Fin 6 × Fin 6) (Fin 6 × Fin 6) ℂ

end MUB6.Weiner

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Completion_JointBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# An orthonormal eigenbasis for a commuting symmetric family

This is the finite-dimensional simultaneous spectral step in the completion
argument. It specializes mathlib's joint-eigenspace decomposition and retains
an explicit common eigenvalue for each basis vector and each operator.
-/

namespace MUB6.Weiner

open Module
open scoped Function

variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- Finite tuples of actual eigenvalues, excluding irrelevant scalar tuples. -/
abbrev JointIndex (T : ι → End ℂ E) := ∀ i, (T i).Eigenvalues

noncomputable def jointSubspace (T : ι → End ℂ E) (χ : JointIndex T) : Submodule ℂ E :=
  ⨅ i, (T i).eigenspace (χ i : ℂ)

end MUB6.Weiner

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Completion_ProjectionBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Rank-one projectors fixed by a realigned orthogonal projection

The fixed space of the complement operator contains the projectors of an
orthonormal basis. This is the spectral part of the completion argument.
-/

namespace MUB6.Weiner

open Matrix Module
open scoped BigOperators Function

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix of the orthogonal rank-one operator associated with a vector. -/
def projector (v : EuclideanSpace ℂ n) : Matrix n n ℂ :=
  Matrix.vecMulVec v (star v)

/-- The real and imaginary parts of the reshaped columns. -/
noncomputable def hermitianColumn (C : Matrix (n × n) (n × n) ℂ)
    (p : Bool × (n × n)) : Matrix n n ℂ :=
  if p.1 then (imaginaryPart (superColumn C p.2) : Matrix n n ℂ)
  else (realPart (superColumn C p.2) : Matrix n n ℂ)

end MUB6.Weiner

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Completion_Completion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Weiner completion in dimension six

The missing orthonormal basis is obtained by simultaneously diagonalizing the
commutative fixed space of the complementary Hilbert--Schmidt projection.
-/

namespace MUB6.Weiner

open Matrix
open scoped BigOperators

/-- Append the basis supplied by the completion theorem. -/
noncomputable def appendBasis (B : Fin 6 → MUB6.Basis) (b : MUB6.Basis) :
    Fin 7 → MUB6.Basis := Fin.lastCases b B

end MUB6.Weiner

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Cubic_CubicSymmetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary symmetric sums for the six-entry cubic classification. -/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

def elementarySum (v : (Fin 6) → ℂ) (k : ℕ) : ℂ :=
  ∑ s ∈ (Finset.univ : Finset (Fin 6)).powersetCard k, ∏ i ∈ s, v i

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Cubic_CubicMultiplicityCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Multiplicity counting once the two possible cubed values are known. -/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

def cubeClass (v : (Fin 6) → ℂ) (a : ℂ) : Finset (Fin 6) := by
  classical
  exact Finset.univ.filter (fun i => v i ^ 3 = a)

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Cubic_CubicSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The common-support step of the cubic classification in §3.

These lemmas concern two three-element supports avoiding coordinate zero.
The last theorem states that a quotient having the cubed-value pattern proved
for Hadamard row ratios forces the supports to coincide.
-/

noncomputable section

namespace MUB6

def TwoValuePattern (f : (Fin 6) → ℂ) : Prop := by
  classical
  exact (∃ a b : ℂ, ∀ i, f i = a ∨ f i = b) ∧
    ∀ a : ℂ, (∃ i, f i = a) → (∃ j, f j ≠ a) →
      (Finset.univ.filter (fun i => f i = a)).card = 3

def supportedValue (S : Finset (Fin 6)) (x : ℂ) (i : (Fin 6)) : ℂ :=
  if i ∈ S then x else 1

def supportedRatio (S U : Finset (Fin 6)) (x y : ℂ) (i : (Fin 6)) : ℂ :=
  supportedValue S x i / supportedValue U y i

end MUB6

end

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

def nonOneSupport (f : Fin 6 → ℂ) : Finset (Fin 6) := by
  classical
  exact Finset.univ.filter (fun i => f i ≠ 1)

@[simp] theorem mem_nonOneSupport (f : Fin 6 → ℂ) (i : Fin 6) :
    i ∈ nonOneSupport f ↔ f i ≠ 1 := by
  classical
  simp [nonOneSupport]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Cubic_FiveCycle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite, kernel-checked classification of simple two-regular graphs on
five vertices.  Ten Boolean edge choices are checked, not matrices over a
restricted alphabet. -/

namespace MUB6

def fiveGraph (b : Fin 10 → Bool) : Fin 5 → Fin 5 → Bool :=
  !![false, b 0, b 1, b 2, b 3;
     b 0, false, b 4, b 5, b 6;
     b 1, b 4, false, b 7, b 8;
     b 2, b 5, b 7, false, b 9;
     b 3, b 6, b 8, b 9, false]

def fiveCycleOrder : Fin 12 → Fin 5 → Fin 5 :=
  ![![0, 1, 2, 3, 4], ![0, 1, 2, 4, 3], ![0, 1, 3, 2, 4], ![0, 1, 3, 4, 2],
    ![0, 1, 4, 2, 3], ![0, 1, 4, 3, 2], ![0, 2, 1, 3, 4], ![0, 2, 1, 4, 3],
    ![0, 2, 3, 1, 4], ![0, 2, 4, 1, 3], ![0, 3, 1, 2, 4], ![0, 3, 2, 1, 4]]

def canonicalFiveCycle : Fin 5 → Fin 5 → Bool :=
  fiveGraph ![true, false, false, true, true, false, false, true, false, true]

theorem fiveCycleOrder_bijective : ∀ c, Function.Bijective (fiveCycleOrder c) := by
  decide +kernel

noncomputable def fiveCyclePermutation (c : Fin 12) : Equiv.Perm (Fin 5) :=
  Equiv.ofBijective (fiveCycleOrder c) (fiveCycleOrder_bijective c)

end MUB6

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Cubic_NormalizedCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A second finite presentation of the five-cycle classification.  A row has
two positive signs among four off-diagonal positions, hence six choices. -/

namespace MUB6

def fourChoices : Fin 6 → Fin 4 → Bool :=
  ![![true, true, false, false], ![true, false, true, false],
    ![true, false, false, true], ![false, true, true, false],
    ![false, true, false, true], ![false, false, true, true]]

def offDiagonalIndex (i j : Fin 5) (h : i ≠ j) : Fin 4 :=
  ⟨if j.val < i.val then j.val else j.val - 1, by
    have hn : i.val ≠ j.val := fun e => h (Fin.ext e)
    split_ifs <;> omega⟩

def fiveRowChoice (i : Fin 5) (a : Fin 6) (j : Fin 5) : Bool :=
  if h : i = j then false else fourChoices a (offDiagonalIndex i j h)

def normalizedCodeGraph (a : Fin 5 → Fin 6) (i j : Fin 5) : Bool :=
  fiveRowChoice i (a i) j

def normalizedCodeOrthogonal (a : Fin 5 → Fin 6) : Prop :=
  ∀ i j, i ≠ j →
    (Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j ∧
      normalizedCodeGraph a i k = normalizedCodeGraph a j k)).card = 1

def normalizedCodeClassified (a : Fin 5 → Fin 6) : Prop :=
  normalizedCodeOrthogonal a →
    ∃ c, ∀ i j, normalizedCodeGraph a (fiveCycleOrder c i) (fiveCycleOrder c j) =
      canonicalFiveCycle i j

end MUB6

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_EqualityPatterns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite set-partition expansion, presented by explicit surjective block
labels. This separates the finite combinatorics from complex matrix moments. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace MUB6.EqualityPatterns

variable {A P B V : Type*}

/-- Each `label p` is a surjection onto the blocks of one partition. -/
structure Family (A P : Type*) where
  blocks : P → ℕ
  label : (p : P) → A → Fin (blocks p)
  onto : ∀ p, Function.Surjective (label p)
  unique : ∀ p q, (∀ i j, label p i = label p j ↔ label q i = label q j) → p = q

namespace Family

def flatten (F : Family A P) (s : Σ p, Fin (F.blocks p) ↪ B) : A → B :=
  fun i => s.2 (F.label s.1 i)

theorem flatten_injective (F : Family A P) : Function.Injective (F.flatten (B := B)) := by
  rintro ⟨p, e⟩ ⟨q, f⟩ h
  have hpq : p = q := F.unique p q (by
    intro i j
    have hi := congrFun h i
    have hj := congrFun h j
    change e (F.label p i) = f (F.label q i) at hi
    change e (F.label p j) = f (F.label q j) at hj
    constructor
    · intro hij
      apply f.injective
      rw [← hi, ← hj, hij]
    · intro hij
      apply e.injective
      rw [hi, hj, hij])
  subst q
  congr 1
  ext b
  obtain ⟨i, rfl⟩ := F.onto p b
  exact congrFun h i

theorem flatten_surjective (F : Family A P)
    (cover : ∀ f : A → B, ∃ p, ∀ i j,
      F.label p i = F.label p j ↔ f i = f j) :
    Function.Surjective (F.flatten (B := B)) := by
  classical
  intro f
  obtain ⟨p, hp⟩ := cover f
  let r : Fin (F.blocks p) → A := Function.surjInv (F.onto p)
  have hr : ∀ b, F.label p (r b) = b := Function.rightInverse_surjInv (F.onto p)
  let e : Fin (F.blocks p) ↪ B :=
    ⟨fun b => f (r b), by
      intro b c h
      have hbc := (hp (r b) (r c)).mpr h
      simpa only [hr] using hbc⟩
  refine ⟨⟨p, e⟩, ?_⟩
  funext i
  exact (hp (r (F.label p i)) i).mp (hr _)

/-- Every function has exactly one equality pattern and an injection assigning
distinct values to its blocks. No probabilistic premise is used. -/
def assignmentsEquiv (F : Family A P)
    (cover : ∀ f : A → B, ∃ p, ∀ i j,
      F.label p i = F.label p j ↔ f i = f j) :
    (Σ p, Fin (F.blocks p) ↪ B) ≃ (A → B) :=
  Equiv.ofBijective F.flatten ⟨F.flatten_injective, F.flatten_surjective cover⟩

end Family

end MUB6.EqualityPatterns

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_Sampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite sampling identities. The splitting theorem below is the counting
step behind contraction of an order-one row; it is independent of the values
of the matrix entries and uses no certificate data. -/

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace MUB6.Sampling

variable {A B V : Type*} [Fintype A] [Fintype B] [AddCommMonoid V]

def dropFirst {p : ℕ} (e : Fin (p + 1) ↪ B) : Fin p ↪ B :=
  (Equiv.embeddingFinSucc p B e).1

omit [Fintype B] in
@[simp] theorem dropFirst_apply {p : ℕ} (e : Fin (p + 1) ↪ B) (i : Fin p) :
    dropFirst e i = e i.succ := rfl

end MUB6.Sampling

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_MomentContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Orthogonality relations for injective moments. The saturated relation uses
only six-row moments, even though its generating exponent array has seven rows. -/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

def mergeFirst {p q : ℕ} (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (j : Fin p) :
    Matrix (Fin p) (Fin q) ℤ :=
  fun u v => A u.succ v + if u = j then A 0 v else 0

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_PartitionExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
attribute [local instance] Classical.propDecidable

namespace MUB6

def groupedColumns {p n k : ℕ} (A : Matrix (Fin p) (Fin n) ℤ)
    (label : Fin n → Fin k) : Matrix (Fin p) (Fin k) ℤ :=
  fun i b => ∑ j with label j = b, A i j

end MUB6

end

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

def raw2 : Fin 2 → Fin 2 → ℕ := ![![0, 0], ![0, 1]]

def blocks3 : Fin 5 → ℕ := ![1, 2, 2, 2, 3]
def raw3 : Fin 5 → Fin 3 → ℕ := ![![0, 0, 0], ![0, 0, 1], ![0, 1, 0], ![0, 1, 1], ![0, 1, 2]]
def label3 (p : Fin 5) (i : Fin 3) : Fin (blocks3 p) :=
  ⟨raw3 p i, by fin_cases p <;> fin_cases i <;> decide⟩

def family3 : Family (Fin 3) (Fin 5) where
  blocks := blocks3
  label := label3
  onto := by decide +kernel
  unique := by decide +kernel

def blocks4 : Fin 15 → ℕ := ![1, 2, 2, 2, 3, 2, 2, 3, 2, 2, 3, 3, 3, 3, 4]
def raw4 : Fin 15 → Fin 4 → ℕ := ![![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 1, 0], ![0, 0, 1, 1], ![0, 0, 1, 2], ![0, 1, 0, 0], ![0, 1, 0, 1], ![0, 1, 0, 2], ![0, 1, 1, 0], ![0, 1, 1, 1], ![0, 1, 1, 2], ![0, 1, 2, 0], ![0, 1, 2, 1], ![0, 1, 2, 2], ![0, 1, 2, 3]]
def label4 (p : Fin 15) (i : Fin 4) : Fin (blocks4 p) :=
  ⟨raw4 p i, by fin_cases p <;> fin_cases i <;> decide⟩

def family4 : Family (Fin 4) (Fin 15) where
  blocks := blocks4
  label := label4
  onto := by decide +kernel
  unique := by decide +kernel

end MUB6.EqualityPatterns

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

def pairCoefficient : Fin 4 → ℂ := ![2, 1, 1, 1]

end MUB6

end

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

def raw9step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]

def raw9step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]

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

def raw96step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]

def raw96step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw97 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]

def raw97step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]

def raw97step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw98 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]

def raw98step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]

def raw98step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw99 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]

def raw99step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]

def raw99step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

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

def raw968step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, 0, -3]]

def raw969 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -1, -2]]

def raw969step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -1, -2]]

def raw970 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 1, -3]]

def raw971 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def raw972 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 1, -3]]

def raw973 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 1, -2], ![1, 1, 0, -2]]

def raw974 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, 1, -4]]

def raw974step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![-1, 1, -1, 1], ![5, -1, 0, -4]]

def raw974step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -4, 5], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw975 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw975step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw976 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw977 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw977step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw978 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, 0, -3]]

def raw978step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![-1, 1, 0, 0], ![5, -1, -1, -3]]

def raw978step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -3, 5], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw979 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, 1, -2], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw979step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw980 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, 1, -1, -2]]

def raw980step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![-1, 1, 1, -1], ![5, -1, -2, -2]]

def raw980step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw981 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw981step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 1, -3]]

def raw982 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw983 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw984 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, 1, 0, -3]]

def raw984step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![-1, 2, -1, 0], ![5, -2, 0, -3]]

def raw984step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![2, 0, -1, -1], ![1, -2, 1, 0], ![-5, 2, 0, 3]]

def raw984step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 2, 3, -5], ![1, -2, 0, 1]]

def raw985 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw986 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw987 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 1, -1, -1], ![1, 0, 0, -1]]

def raw987step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw988 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, 1, -1, -2]]

def raw988step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![-1, 2, 0, -1], ![5, -2, -1, -2]]

def raw988step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw989 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw989step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw990 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def raw991 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw991step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, 0, 0, -2]]

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

def raw9679 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1], ![0, -2, 1, 1], ![-2, 1, 2, -1]]

def raw9679step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw9680 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![0, -2, 3, -1]]

def raw9680step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw9681 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-1, 1, 1, -1], ![-1, -2, 2, 1]]

def raw9681step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw9682 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![0, -2, 0, 2], ![-2, 1, 3, -2]]

def raw9682step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw9683 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![0, -2, 1, 1], ![-2, 1, 2, -1]]

def raw9683step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9684 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-2, 1, -1, 2], ![0, -2, 3, -1]]

def raw9684step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def raw9685 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![0, -2, 2, 0]]

def raw9685step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw9686 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-1, 1, 0, 0], ![-1, -2, 2, 1]]

def raw9686step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw9687 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-1, 1, 1, -1], ![-1, -2, 1, 2]]

def raw9687step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw9688 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -2, -1, 3], ![-2, 1, 3, -2]]

def raw9688step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw9689 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -2, 0, 2], ![-2, 1, 2, -1]]

def raw9689step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 0, 1, 0], ![-1, 0, 0, 1], ![0, 2, 0, -2], ![2, -1, -2, 1]]

def raw9689step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw9690 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -2, 1, 1], ![-2, 1, 1, 0]]

def raw9690step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw9691 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, -1, 3]]

def raw9691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, -1, 3]]

def raw9691step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw9692 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![-2, -2, 4]]

def raw9692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![-2, -2, 4]]

def raw9692step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw9693 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![-3, 0, 3]]

def raw9693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![-3, 0, 3]]

def raw9693step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw9694 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![-3, -1, 4]]

def raw9694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![-3, -1, 4]]

def raw9694step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw9695 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, -2, 4]]

def raw9695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, -2, 4]]

def raw9695step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical303
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9696 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![-3, 0, 3]]

def raw9696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![-3, 0, 3]]

def raw9696step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw9697 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![-3, -1, 4]]

def raw9697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![-3, -1, 4]]

def raw9697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw9698 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-1, 2, -1], ![-2, -1, 3]]

def raw9698step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]

def raw9698step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]

def raw9698step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]

def raw9699 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 0, 0], ![-1, -2, 2, 1], ![1, 2, -2, -1]]

def raw9699step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![0, 2, -2], ![0, 1, -1]]

def raw9699step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]

def raw9699step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw9700 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -2, -2, 2]]

def raw9700step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -2, -2, 2]]

def raw9700step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9701 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 1, -2, 3]]

def raw9701step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 1, -2, 3]]

def raw9701step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw9702 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, -1, 0, 3], ![2, -1, 1, -2]]

def raw9702step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, -1, 0, 3], ![2, -1, 1, -2]]

def raw9702step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def raw9703 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![-2, 0, -1, 3], ![2, -2, 1, -1]]

def raw9703step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![-2, 0, -1, 3], ![2, -2, 1, -1]]

def raw9703step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def raw9704 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 0, -1], ![-2, -1, 0, 3]]

def raw9704step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, -1, 1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-2, 1, 0, 1], ![2, 1, 0, -3]]

def raw9704step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-2, 1, 0, 1], ![2, 1, 0, -3]]

def raw9704step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw9705 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2], ![-2, -2, 0, 4]]

def raw9705step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, -1, 1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-2, 0, 0, 2], ![2, 2, 0, -4]]

def raw9705step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-2, 0, 0, 2], ![2, 2, 0, -4]]

def raw9705step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw9706 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 0, -2], ![-2, -1, 0, 3]]

def raw9706step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, -1, 1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, -1, 0, 2], ![2, 1, 0, -3]]

def raw9706step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, -1, 0, 2], ![2, 1, 0, -3]]

def raw9706step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, -1, 2], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw9707 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, 0, 2], ![2, -2, -1, 1]]

def raw9707step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, 0, 2], ![2, -2, -1, 1]]

def raw9707step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw9708 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 0, -1, 3]]

def raw9708step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 0, -1, 3]]

def raw9708step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw9709 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0], ![-2, -1, 0, 3]]

def raw9709step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0], ![-2, -1, 0, 3]]

def raw9709step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -2, 3], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw9710 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1], ![-2, -2, 0, 4]]

def raw9710step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, -1, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-2, 0, 1, 1], ![2, 2, 0, -4]]

def raw9710step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-2, 0, 1, 1], ![2, 2, 0, -4]]

def raw9710step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw9711 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, -1, 2]]

def raw9711step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, -1, 2]]

def raw9711step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw9712 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, 0, -2], ![-2, -1, -1, 4]]

def raw9712step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, 0, -2], ![-2, -1, -1, 4]]

def raw9712step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw9713 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 0, -2], ![-2, -2, 0, 4]]

def raw9713step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, -1, 1], ![0, -1, 0, 1], ![-1, 0, 1, 0], ![-1, -1, 0, 2], ![2, 2, 0, -4]]

def raw9713step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 0, 1], ![-1, 0, 1, 0], ![-1, -1, 0, 2], ![2, 2, 0, -4]]

def raw9713step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, -1, 2], ![0, -1, 0, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw9714 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, -1, 3], ![-1, 2, 1, -2]]

def raw9714step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, 1, 1, -3], ![1, -2, -1, 2]]

def raw9714step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, 1, 1, -3], ![1, -2, -1, 2]]

def raw9714step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw9715 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, 0, -2], ![-2, -1, 0, 3]]

def raw9715step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![0, -2, 0, 2], ![2, 1, 0, -3]]

def raw9715step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![0, -2, 0, 2], ![2, 1, 0, -3]]

def raw9715step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw9716 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 2, 0, -1], ![-1, -1, -1, 3]]

def raw9716step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 2, 0, -1], ![-1, -1, -1, 3]]

def raw9716step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw9717 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, 2, -1, -1], ![-2, -1, 0, 3]]

def raw9717step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![0, -2, 1, 1], ![2, 1, 0, -3]]

def raw9717step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![0, -2, 1, 1], ![2, 1, 0, -3]]

def raw9717step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw9718 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, 2, 0, -2], ![-2, -1, -1, 4]]

def raw9718step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, 2, 0, -2], ![-2, -1, -1, 4]]

def raw9718step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw9719 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, -1, 0, 3], ![1, 0, 2, -3]]

def raw9719step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![2, 1, 0, -3], ![-1, 0, -2, 3]]

def raw9719step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![2, 1, 0, -3], ![-1, 0, -2, 3]]

def raw9719step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw9720 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 0, -1, 3], ![1, -1, 2, -2]]

def raw9720step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 0, -1, 3], ![1, -1, 2, -2]]

def raw9720step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, -1, -2]]

def raw9721 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 1, 1]]

def raw9721step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![2, 0, -1, -1]]

def raw9721step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![2, 0, -1, -1]]

def raw9721step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def raw9722 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, -1, 1, 2]]

def raw9722step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![2, 1, -1, -2]]

def raw9722step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![2, 1, -1, -2]]

def raw9722step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw9723 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, -1, 3], ![0, 1, 2, -3]]

def raw9723step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, -1, 3], ![0, 1, 2, -3]]

def raw9723step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw9724 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 0, 3], ![0, 1, 2, -3]]

def raw9724step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 0, 3], ![0, 1, 2, -3]]

def raw9724step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw9725 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, -1, 3], ![-1, 1, 2, -2]]

def raw9725step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![1, 1, 1, -3], ![1, -1, -2, 2]]

def raw9725step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![1, 1, 1, -3], ![1, -1, -2, 2]]

def raw9725step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw9726 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 1, 2]]

def raw9726step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![2, 1, -1, -2]]

def raw9726step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![2, 1, -1, -2]]

def raw9726step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw9727 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 1, -2], ![-2, -1, -1, 4]]

def raw9727step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 1, -2], ![-2, -1, -1, 4]]

def raw9727step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 1, 0, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical304
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9728 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![-2, 0, 2, 0], ![1, -2, -1, 2]]

def raw9728step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![-2, 0, 2, 0], ![1, -2, -1, 2]]

def raw9728step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9729 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-2, -2, 1, 3]]

def raw9729step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-2, -2, 1, 3]]

def raw9729step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

def raw9730 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2], ![-2, -2, 0, 4]]

def raw9730step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 0, 1, 0], ![-1, 0, -1, 2], ![2, 2, 0, -4]]

def raw9730step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 0, 1, 0], ![-1, 0, -1, 2], ![2, 2, 0, -4]]

def raw9730step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, 0, 0]]

def raw9731 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 1, 1, -1], ![-1, -1, -1, 3]]

def raw9731step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 1, 1, -1], ![-1, -1, -1, 3]]

def raw9731step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def raw9732 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, -1, 2, -1], ![-2, 1, -2, 3]]

def raw9732step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, -1, 2, -1], ![-2, 1, -2, 3]]

def raw9732step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw9733 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-1, 1, 1, -1], ![-1, -2, 0, 3]]

def raw9733step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, -1, 0, 1], ![-1, 0, 1, 0], ![-1, 0, 0, 1], ![1, -1, -1, 1], ![1, 2, 0, -3]]

def raw9733step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 1, 0], ![-1, 0, 0, 1], ![1, -1, -1, 1], ![1, 2, 0, -3]]

def raw9733step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw9734 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -2, 2, 0], ![-2, 1, -1, 2]]

def raw9734step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -2, 2, 0], ![-2, 1, -1, 2]]

def raw9734step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw9735 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-5, 2, 1, 2], ![5, -2, -2, -1]]

def raw9735step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -5, 5], ![0, 2, -2], ![1, 1, -2], ![-1, 2, -1]]

def raw9735step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 5, -5], ![1, -2, 1]]

def raw9736 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-4, 2, 1, 1], ![4, -2, -2, 0]]

def raw9736step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![0, 2, -2], ![1, 1, -2], ![-1, 1, 0]]

def raw9736step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![0, -2, 2], ![-1, -1, 2], ![1, -1, 0]]

def raw9736step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 4, -4], ![1, -1, 0]]

def raw9737 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-4, 3, 1, 0], ![4, -3, -2, 1]]

def raw9737step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![0, 3, -3], ![1, 1, -2], ![-1, 0, 1]]

def raw9737step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![0, -3, 3], ![-1, -1, 2], ![1, 0, -1]]

def raw9737step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -3, 3], ![0, 4, -4], ![1, 0, -1]]

def raw9738 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-3, 2, -2, 3], ![3, -2, 1, -2]]

def raw9738step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![0, 2, -2], ![1, -2, 1], ![-1, 3, -2]]

def raw9738step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -2, 2], ![0, 3, -3], ![1, 1, -2]]

def raw9739 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-3, 2, 1, 0], ![3, -2, -2, 1]]

def raw9739step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![0, 2, -2], ![1, 1, -2], ![-1, 0, 1]]

def raw9739step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, -2, 2], ![-1, -1, 2], ![1, 0, -1]]

def raw9739step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

def raw9740 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-3, 3, -2, 2], ![3, -3, 1, -1]]

def raw9740step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![0, 3, -3], ![1, -2, 1], ![-1, 2, -1]]

def raw9740step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -3, 3], ![0, 3, -3], ![1, 1, -2]]

def raw9741 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-3, 3, 1, -1], ![3, -3, -2, 2]]

def raw9741step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![0, 3, -3], ![1, 1, -2], ![-1, -1, 2]]

def raw9741step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -3, 3], ![0, 3, -3], ![1, 1, -2]]

def raw9742 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 1, 3], ![2, 2, -2, -2]]

def raw9742step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![1, 1, -2], ![-1, 3, -2]]

def raw9742step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1]]

def raw9743 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 2, -2, 2], ![2, -2, 1, -1]]

def raw9743step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 2, -2], ![1, -2, 1], ![-1, 2, -1]]

def raw9743step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

def raw9744 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 2, 1, -1], ![2, -2, -2, 2]]

def raw9744step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![-1, -1, 2]]

def raw9744step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

def raw9745 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 3, -2, 1], ![2, -3, 1, 0]]

def raw9745step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 3, -3], ![1, -2, 1], ![-1, 1, 0]]

def raw9745step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, -3, 3], ![-1, 2, -1], ![1, -1, 0]]

def raw9745step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

def raw9746 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 4, -2, 0], ![2, -4, 1, 1]]

def raw9746step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 4, -4], ![1, -2, 1], ![-1, 0, 1]]

def raw9746step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, -4, 4], ![-1, 2, -1], ![1, 0, -1]]

def raw9746step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 4, -4], ![1, -1, 0]]

def raw9747 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -3, 1, 3], ![1, 3, -2, -2]]

def raw9747step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, -3, 3], ![1, 1, -2], ![-1, 3, -2]]

def raw9747step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 3, -3], ![1, -2, 1]]

def raw9748 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -3, 3, 1], ![1, 3, -4, 0]]

def raw9748step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, -3, 3], ![1, 3, -4], ![-1, 1, 0]]

def raw9748step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, 3, -3], ![-1, -3, 4], ![1, -1, 0]]

def raw9748step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0]]

def raw9749 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, 1, 2], ![1, 2, -2, -1]]

def raw9749step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![1, 1, -2], ![-1, 2, -1]]

def raw9749step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1]]

def raw9750 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, 2, 1], ![1, 2, -3, 0]]

def raw9750step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![1, 2, -3], ![-1, 1, 0]]

def raw9750step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, 2, -2], ![-1, -2, 3], ![1, -1, 0]]

def raw9750step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def raw9751 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, 3, 0], ![1, 2, -4, 1]]

def raw9751step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![1, 3, -4], ![-1, 0, 1]]

def raw9751step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, 2, -2], ![-1, -3, 4], ![1, 0, -1]]

def raw9751step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

def raw9752 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 0, 1, 0], ![0, 1, -3, 2], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw9752step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw9753 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 0, 1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1]]

def raw9753step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![1, 0, -1, 0], ![0, -1, 1, 0], ![-1, 1, 1, -1]]

def raw9753step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw9754 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 0, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

def raw9754step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

def raw9755 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 0, 1, 0], ![0, 2, 0, -2], ![1, -2, -2, 3]]

def raw9755step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![1, 1, 0, -2], ![-1, 0, -2, 3]]

def raw9755step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, -2, 2], ![-1, -1, 0, 2], ![1, 0, 2, -3]]

def raw9755step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def raw9756 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 1, 1, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

def raw9756step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, 1, -2], ![1, 1, 0, -2], ![-1, -1, -1, 3]]

def raw9756step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw9757 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 2, -2, 1], ![1, -2, 1, 0]]

def raw9757step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![-1, 1, 0]]

def raw9757step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![1, -1, 0]]

def raw9757step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

def raw9758 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 2, 1, -2], ![1, -2, -2, 3]]

def raw9758step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![-1, -2, 3]]

def raw9758step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2]]

def raw9759 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 3, -2, 0], ![1, -3, 1, 1]]

def raw9759step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 3, -3], ![1, -2, 1], ![-1, 0, 1]]

def raw9759step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, -3, 3], ![-1, 2, -1], ![1, 0, -1]]

def raw9759step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical305
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9760 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 4, -3, 0], ![1, -4, 2, 1]]

def raw9760step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 4, -4], ![1, -3, 2], ![-1, 0, 1]]

def raw9760step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, -4, 4], ![-1, 3, -2], ![1, 0, -1]]

def raw9760step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0]]

def raw9761 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 4, -2, -1], ![1, -4, 1, 2]]

def raw9761step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 4, -4], ![1, -2, 1], ![-1, -1, 2]]

def raw9761step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 4, -4], ![1, -2, 1]]

def raw9762 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, -1, 2]]

def raw9762step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw9763 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-2, -1, 1, 2]]

def raw9763step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw9764 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -2, -2, 2]]

def raw9764step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -2, -2, 2]]

def raw9764step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9765 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 1, -2, 3]]

def raw9765step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 1, -2, 3]]

def raw9765step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw9766 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, -1, 0, 3], ![2, -1, 1, -2]]

def raw9766step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, -1, 0, 3], ![2, -1, 1, -2]]

def raw9766step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def raw9767 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![-2, 0, -1, 3], ![2, -2, 1, -1]]

def raw9767step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![-2, 0, -1, 3], ![2, -2, 1, -1]]

def raw9767step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def raw9768 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 0, -1], ![-2, -1, 0, 3]]

def raw9768step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-2, 1, 0, 1], ![2, 1, 0, -3]]

def raw9768step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-2, 1, 0, 1], ![2, 1, 0, -3]]

def raw9768step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw9769 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2], ![-2, -2, 0, 4]]

def raw9769step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-2, 0, 0, 2], ![2, 2, 0, -4]]

def raw9769step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-2, 0, 0, 2], ![2, 2, 0, -4]]

def raw9769step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw9770 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 0, -2], ![-2, -1, 0, 3]]

def raw9770step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, -1, 0, 2], ![2, 1, 0, -3]]

def raw9770step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, -1, 0, 2], ![2, 1, 0, -3]]

def raw9770step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, -1, 2], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw9771 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, 0, 2], ![2, -2, -1, 1]]

def raw9771step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, 0, 2], ![2, -2, -1, 1]]

def raw9771step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw9772 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 0, -1, 3]]

def raw9772step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 0, -1, 3]]

def raw9772step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw9773 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0], ![-2, -1, 0, 3]]

def raw9773step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0], ![-2, -1, 0, 3]]

def raw9773step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -2, 3], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw9774 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1], ![-2, -2, 0, 4]]

def raw9774step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-2, 0, 1, 1], ![2, 2, 0, -4]]

def raw9774step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-2, 0, 1, 1], ![2, 2, 0, -4]]

def raw9774step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw9775 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, -1, 2]]

def raw9775step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, -1, 2]]

def raw9775step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw9776 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, 0, -2], ![-2, -1, -1, 4]]

def raw9776step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, 0, -2], ![-2, -1, -1, 4]]

def raw9776step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw9777 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 0, -2], ![-2, -2, 0, 4]]

def raw9777step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, -1, 0, 1], ![-1, 0, 1, 0], ![-1, -1, 0, 2], ![2, 2, 0, -4]]

def raw9777step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 0, 1], ![-1, 0, 1, 0], ![-1, -1, 0, 2], ![2, 2, 0, -4]]

def raw9777step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, -1, 2], ![0, -1, 0, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw9778 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, -1, 3], ![-1, 2, 1, -2]]

def raw9778step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, 1, 1, -3], ![1, -2, -1, 2]]

def raw9778step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, 1, 1, -3], ![1, -2, -1, 2]]

def raw9778step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw9779 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, 0, -2], ![-2, -1, 0, 3]]

def raw9779step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![0, -2, 0, 2], ![2, 1, 0, -3]]

def raw9779step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![0, -2, 0, 2], ![2, 1, 0, -3]]

def raw9779step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw9780 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 2, 0, -1], ![-1, -1, -1, 3]]

def raw9780step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 2, 0, -1], ![-1, -1, -1, 3]]

def raw9780step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw9781 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, 2, -1, -1], ![-2, -1, 0, 3]]

def raw9781step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![0, -2, 1, 1], ![2, 1, 0, -3]]

def raw9781step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![0, -2, 1, 1], ![2, 1, 0, -3]]

def raw9781step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw9782 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, 2, 0, -2], ![-2, -1, -1, 4]]

def raw9782step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, 2, 0, -2], ![-2, -1, -1, 4]]

def raw9782step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw9783 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, -3, 3], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw9783step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw9784 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, -1, 1], ![1, -1, -1, 1]]

def raw9784step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 1, -1, -1], ![-1, -1, 1, 1]]

def raw9784step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 1, -1, -1]]

def raw9785 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![0, 1, 0, -1], ![1, -2, -2, 3]]

def raw9785step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

def raw9786 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 2, 0, -1], ![1, -2, -2, 3]]

def raw9786step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, 0, -2], ![-1, -1, -1, 3]]

def raw9786step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def raw9787 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, -1, 2]]

def raw9787step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw9788 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -2, -2, 2]]

def raw9788step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -2, -2, 2]]

def raw9788step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9789 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 1, -2, 3]]

def raw9789step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 1, -2, 3]]

def raw9789step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw9790 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![-2, 1, 0, 1], ![2, -2, -2, 2]]

def raw9790step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, -2, 2]]

def raw9791 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 0, 0], ![-2, 1, -2, 3]]

def raw9791step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 0, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical306
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9792 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, -1, 2], ![2, -2, -2, 2]]

def raw9792step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, -2, 2]]

def raw9793 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -2, -3, 3]]

def raw9793step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, -3, 3]]

def raw9794 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, -1, 1], ![-2, 1, -2, 3]]

def raw9794step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, -1, 1]]

def raw9795 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 1, -3, 4]]

def raw9795step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 0, 0]]

def raw9796 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -3, 2], ![-1, 1, 0, 0], ![1, -2, 1, 0]]

def raw9796step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw9797 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -3, 2], ![0, 1, 0, -1], ![0, -2, 1, 1]]

def raw9797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![-2, 1, 1]]

def raw9797step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]

def raw9798 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, -1, 0], ![-2, -1, 0, 3], ![2, -1, 1, -2]]

def raw9798step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def raw9799 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![-2, 0, -1, 3], ![2, -2, 1, -1]]

def raw9799step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def raw9800 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -1, 0, -1], ![-2, -1, 0, 3]]

def raw9800step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def raw9801 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, 0, 0, -2], ![-2, -2, 0, 4]]

def raw9801step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw9802 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 0, -2], ![-2, -1, 0, 3]]

def raw9802step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw9803 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, -1, -1, 2]]

def raw9803step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-1, -1, 2]]

def raw9803step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw9804 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -2, 1], ![-2, -1, 0, 3], ![2, -1, 1, -2]]

def raw9804step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def raw9805 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, -1, -1, 4], ![2, -1, 1, -2]]

def raw9805step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def raw9806 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, -1, 0, 3], ![2, -1, 0, -1]]

def raw9806step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def raw9807 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, 0, -1, 3], ![2, -2, 1, -1]]

def raw9807step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def raw9808 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 0, -1], ![-2, -1, 0, 3]]

def raw9808step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def raw9809 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2], ![-2, -2, 0, 4]]

def raw9809step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw9810 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![-2, 0, -2, 4], ![2, -2, 1, -1]]

def raw9810step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def raw9811 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![-2, 0, -1, 3], ![2, -2, 0, 0]]

def raw9811step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw9812 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![-2, 0, 0, 2], ![2, -2, -1, 1]]

def raw9812step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw9813 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 0, -1, 3]]

def raw9813step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw9814 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0], ![-2, -1, 0, 3]]

def raw9814step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw9815 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 0, -1], ![-2, -1, -1, 4]]

def raw9815step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw9816 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1], ![-2, -2, 0, 4]]

def raw9816step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw9817 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2], ![-2, -2, -1, 5]]

def raw9817step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw9818 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 0, -1], ![-2, 1, -1, 2]]

def raw9818step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def raw9819 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 0, -2], ![-2, -1, 0, 3]]

def raw9819step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def raw9820 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, -1, 2]]

def raw9820step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw9821 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 0, -1, 3]]

def raw9821step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -2, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0]]

def raw9822 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, -1, -1], ![-2, -1, 0, 3]]

def raw9822step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw9823 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 0, -2], ![-2, -1, -1, 4]]

def raw9823step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical307
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9824 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 0, -2], ![-2, -2, 0, 4]]

def raw9824step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw9825 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-1, 1, 0, 0], ![1, -2, -2, 3]]

def raw9825step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

def raw9826 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![-2, 0, 0, 2], ![2, -2, -1, 1]]

def raw9826step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw9827 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![2, -2, 0, 0], ![-2, 0, -1, 3]]

def raw9827step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw9828 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![2, -1, -1, 0], ![-2, -1, 0, 3]]

def raw9828step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw9829 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![2, 0, -1, -1], ![-2, -2, 0, 4]]

def raw9829step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw9830 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, -1, 3], ![2, -2, -1, 1]]

def raw9830step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -2, 1]]

def raw9831 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, 0, 2], ![2, -2, -2, 2]]

def raw9831step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9832 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![0, -2, -2, 4]]

def raw9832step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, -2, 4]]

def raw9832step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw9833 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -2, -1, 1], ![-2, 0, -1, 3]]

def raw9833step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -2, 1]]

def raw9834 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 0, -2, 4]]

def raw9834step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw9835 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -2, 1], ![-2, -1, 0, 3]]

def raw9835step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -2, 1]]

def raw9836 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0], ![-2, -1, -1, 4]]

def raw9836step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw9837 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0], ![-2, -2, 0, 4]]

def raw9837step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw9838 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1], ![-2, -2, -1, 5]]

def raw9838step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw9839 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 0, 0], ![-2, 1, -1, 2]]

def raw9839step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw9840 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, 0, -2], ![-2, -1, -1, 4]]

def raw9840step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def raw9841 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, -1, 1], ![-2, 1, -1, 2]]

def raw9841step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw9842 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, -2, 3]]

def raw9842step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9843 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -1, -1], ![-2, -1, -1, 4]]

def raw9843step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw9844 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, 0, -2], ![-2, -1, -2, 5]]

def raw9844step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9845 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 1, 0, -2], ![-2, -2, 0, 4]]

def raw9845step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw9846 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1], ![-2, -2, 0, 4]]

def raw9846step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw9847 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 0, -2], ![-2, -2, -1, 5]]

def raw9847step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw9848 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![0, -2, -2, 4]]

def raw9848step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![2, 0, -2], ![-2, -2, 4]]

def raw9848step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw9849 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 0, -1, 0], ![-1, -1, -1, 3], ![-1, 2, 1, -2]]

def raw9849step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 1, 1, -1], ![-1, 0, 1, 0], ![1, 1, 1, -3], ![1, -2, -1, 2]]

def raw9849step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 1, -1], ![1, 1, 1, -3]]

def raw9850 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 0, -1, 0], ![0, 2, 0, -2], ![-2, -1, 0, 3]]

def raw9850step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw9851 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 0, 0, -1], ![-1, 2, 0, -1], ![-1, -1, -1, 3]]

def raw9851step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 1, 1, -1], ![-1, 0, 0, 1], ![1, -2, 0, 1], ![1, 1, 1, -3]]

def raw9851step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def raw9852 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 0, 0, -1], ![0, 2, -1, -1], ![-2, -1, 0, 3]]

def raw9852step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw9853 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 0, 0, -1], ![0, 2, 0, -2], ![-2, -1, -1, 4]]

def raw9853step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw9854 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -2, 1], ![-1, -1, -1, 3], ![-1, 2, 1, -2]]

def raw9854step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 2, -1], ![1, 1, 1, -3], ![1, -2, -1, 2]]

def raw9854step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw9855 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -2, 1], ![0, 2, 0, -2], ![-2, -1, 0, 3]]

def raw9855step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -2, 1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical308
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9856 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, -2, 4], ![-1, 2, 1, -2]]

def raw9856step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, 1, 2, -4], ![1, -2, -1, 2]]

def raw9856step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw9857 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, -1, 3], ![-1, 2, 0, -1]]

def raw9857step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, 1, 1, -3], ![1, -2, 0, 1]]

def raw9857step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw9858 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, 2, 0, -1], ![-1, -1, -1, 3]]

def raw9858step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, -2, 0, 1], ![1, 1, 1, -3]]

def raw9858step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw9859 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, -1, -1], ![-2, -1, 0, 3]]

def raw9859step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw9860 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, 0, -2], ![-2, -1, -1, 4]]

def raw9860step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw9861 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 2, -1, 0], ![-1, -1, -1, 3]]

def raw9861step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![1, -2, 1, 0], ![1, 1, 1, -3]]

def raw9861step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw9862 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 2, 0, -1], ![-1, -1, -2, 4]]

def raw9862step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9863 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, 2, -2, 0], ![-2, -1, 0, 3]]

def raw9863step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw9864 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, 2, -1, -1], ![-2, -1, -1, 4]]

def raw9864step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw9865 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, 2, 0, -2], ![-2, -1, -2, 5]]

def raw9865step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9866 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, -1, 0, 3], ![1, 0, 2, -3]]

def raw9866step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw9867 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 0, -1, 3], ![1, -1, 2, -2]]

def raw9867step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw9868 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 1, 1]]

def raw9868step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw9869 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, -1, 1, 2]]

def raw9869step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw9870 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, -1, 3], ![0, 1, 2, -3]]

def raw9870step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw9871 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 0, 3], ![0, 1, 2, -3]]

def raw9871step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw9872 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, -1, 3], ![-1, 1, 2, -2]]

def raw9872step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 0, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -2, 1]]

def raw9873 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 0, 0, 0], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-2, -1, 1, 2]]

def raw9873step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-2, -1, 1, 2]]

def raw9873step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw9874 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -2, 1], ![1, -1, 0, 0], ![-2, -1, 0, 3], ![1, 0, 2, -3]]

def raw9874step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw9875 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![-2, -1, 0, 3], ![1, 0, 2, -3]]

def raw9875step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 2, -3]]

def raw9876 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, -1, -1, 4], ![1, 0, 2, -3]]

def raw9876step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw9877 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, -1, 0, 3], ![1, 0, 1, -2]]

def raw9877step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw9878 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, 0, -1, 3], ![1, -1, 2, -2]]

def raw9878step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw9879 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 1, 1]]

def raw9879step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![2, 0, -1, -1]]

def raw9879step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw9880 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, -1, 1, 2]]

def raw9880step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw9881 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![-2, 0, -1, 3], ![1, -1, 2, -2]]

def raw9881step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 2, -2]]

def raw9882 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 0, 0], ![-2, 0, 1, 1]]

def raw9882step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw9883 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1], ![-2, -1, 1, 2]]

def raw9883step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw9884 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 0, -2, 4], ![1, -1, 2, -2]]

def raw9884step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw9885 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 0, -1, 3], ![1, -1, 1, -1]]

def raw9885step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw9886 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, -1, 1], ![-2, 0, 1, 1]]

def raw9886step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw9887 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 0, 2]]

def raw9887step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical309
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9888 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 1, 2]]

def raw9888step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw9889 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, -1, 0, 3]]

def raw9889step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![2, 1, 0, -3]]

def raw9889step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw9890 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 1, -2], ![-2, -1, -1, 4]]

def raw9890step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw9891 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![-2, 0, 2, 0], ![1, -2, -1, 2]]

def raw9891step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 0, 1, 0], ![2, 0, -2, 0], ![-1, 2, 1, -2]]

def raw9891step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw9892 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, -1, 0, 0], ![-2, -1, 1, 2]]

def raw9892step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw9893 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-2, -2, 1, 3]]

def raw9893step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw9894 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2], ![-2, -2, 0, 4]]

def raw9894step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw9895 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, -1, 0, 0], ![-2, 0, -1, 3], ![0, 1, 2, -3]]

def raw9895step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw9896 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, -1, 0], ![-2, -1, 0, 3], ![0, 1, 2, -3]]

def raw9896step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw9897 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 0, -1], ![-1, -1, -1, 3], ![-1, 1, 2, -2]]

def raw9897step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw9898 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, -1, 1], ![-2, 0, -1, 3], ![0, 1, 2, -3]]

def raw9898step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw9899 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, -2, 4], ![0, 1, 2, -3]]

def raw9899step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw9900 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, -1, 3], ![0, 1, 1, -2]]

def raw9900step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw9901 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -2, 1], ![-2, -1, 0, 3], ![0, 1, 2, -3]]

def raw9901step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw9902 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, -1, 4], ![0, 1, 2, -3]]

def raw9902step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw9903 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 0, 3], ![0, 1, 1, -2]]

def raw9903step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw9904 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, -1, 3], ![-1, 1, 2, -2]]

def raw9904step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 0, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw9905 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, -2, 4], ![-1, 1, 2, -2]]

def raw9905step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 1, 0, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw9906 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, -1, 3], ![-1, 1, 1, -1]]

def raw9906step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw9907 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 1, 1, -1], ![-1, -1, -1, 3]]

def raw9907step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw9908 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, -1, 2, -1], ![-2, 1, -2, 3]]

def raw9908step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw9909 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-1, 1, 1, -1], ![-1, -2, 0, 3]]

def raw9909step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw9910 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -2, 2, 0], ![-2, 1, -1, 2]]

def raw9910step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 1, 0], ![-1, 0, 1, 0], ![-1, 0, 0, 1], ![0, 2, -2, 0], ![2, -1, 1, -2]]

def raw9910step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw9911 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![-1, 1, 1, -1], ![1, -2, -2, 3]]

def raw9911step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 0, 1, -2], ![-1, -1, -1, 3]]

def raw9911step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw9912 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 1, 2]]

def raw9912step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw9913 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 1, -2], ![-2, -1, -1, 4]]

def raw9913step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw9914 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 0, 2, 0], ![1, -2, -1, 2]]

def raw9914step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![-1, 0, 1, 0], ![2, 0, -2, 0], ![-1, 2, 1, -2]]

def raw9914step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw9915 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-2, -2, 1, 3]]

def raw9915step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw9916 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 1, -2], ![-2, -2, 0, 4]]

def raw9916step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw9917 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![0, -2, -1, 3]]

def raw9917step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, -1, 3]]

def raw9917step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw9918 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0], ![-2, -1, 1, 2]]

def raw9918step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw9919 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 1, -2], ![-2, -1, -1, 4]]

def raw9919step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, 0, -2]]

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

def raw992 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![1, 0, 0, -1], ![1, 2, -1, -2]]

def raw992step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 0, 0, 2], ![-1, 2, 0, -1], ![5, -2, -1, -2]]

def raw992step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw993 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def raw994 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![1, 1, 0, -2], ![1, 1, -1, -1]]

def raw994step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def raw995 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 2, -3]]

def raw996 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 0, 1, -2]]

def raw997 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 2, -4]]

def raw997step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![-1, -1, 0, 2], ![5, 0, -1, -4]]

def raw997step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![2, -1, -1, 0], ![1, 1, 0, -2], ![-5, 0, 1, 4]]

def raw997step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, -2, 1], ![1, 0, 4, -5]]

def raw998 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw999 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2], ![1, 0, 0, -1]]

def raw999step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 0, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical310
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9920 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -2, 1], ![-2, -1, 1, 2]]

def raw9920step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw9921 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 0, 3]]

def raw9921step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![2, 1, 0, -3]]

def raw9921step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw9922 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, -1, -1, 4]]

def raw9922step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw9923 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 1, -2], ![-2, -1, -2, 5]]

def raw9923step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw9924 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![-2, 0, 2, 0], ![1, -2, -1, 2]]

def raw9924step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 1, -2]]

def raw9925 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1], ![-2, -2, 1, 3]]

def raw9925step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9926 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 1, -2], ![-2, -2, 0, 4]]

def raw9926step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9927 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![1, -2, -1, 2]]

def raw9927step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9928 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![-2, 0, 2, 0], ![1, -2, -2, 3]]

def raw9928step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw9929 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, -2, 1, 3]]

def raw9929step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9930 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-2, -2, 0, 4]]

def raw9930step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 0, 1, 0], ![-1, 0, 0, 1], ![2, 2, 0, -4]]

def raw9930step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw9931 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2], ![-2, -2, -1, 5]]

def raw9931step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9932 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1], ![-1, 1, 1, -1], ![-1, -1, -1, 3]]

def raw9932step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, -1, 1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw9933 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1], ![0, -1, 2, -1], ![-2, 1, -2, 3]]

def raw9933step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw9934 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, 1, 1, -1], ![-1, -1, -1, 3]]

def raw9934step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 1, 0], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw9935 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, -1, 2, -1], ![-2, 1, -2, 3]]

def raw9935step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw9936 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 1, 0, 0], ![-1, -1, -1, 3]]

def raw9936step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw9937 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 1, 1, -1], ![-1, -1, -2, 4]]

def raw9937step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw9938 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, -1, 1, 0], ![-2, 1, -2, 3]]

def raw9938step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw9939 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, -1, 2, -1], ![-2, 1, -3, 4]]

def raw9939step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw9940 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1], ![-1, 1, 1, -1], ![-1, -2, 0, 3]]

def raw9940step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw9941 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1], ![0, -2, 2, 0], ![-2, 1, -1, 2]]

def raw9941step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def raw9942 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-1, 1, 1, -1], ![-1, -2, 0, 3]]

def raw9942step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw9943 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![0, -2, 2, 0], ![-2, 1, -1, 2]]

def raw9943step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 0, 1], ![-1, 0, 1, 0], ![-1, 0, 1, 0], ![0, 2, -2, 0], ![2, -1, 1, -2]]

def raw9943step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw9944 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-1, 1, 0, 0], ![-1, -2, 0, 3]]

def raw9944step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 0, 1], ![-1, 0, 1, 0], ![-1, 0, 0, 1], ![1, -1, 0, 0], ![1, 2, 0, -3]]

def raw9944step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw9945 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-1, 1, 1, -1], ![-1, -2, -1, 4]]

def raw9945step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw9946 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -2, 1, 1], ![-2, 1, -1, 2]]

def raw9946step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw9947 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -2, 2, 0], ![-2, 1, -2, 3]]

def raw9947step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, -1, 0]]

def raw9948 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, -3, 2, 0], ![-1, 3, -3, 1]]

def raw9948step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, -3, 3], ![1, 2, -3], ![-1, 0, 1]]

def raw9948step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 3, -3], ![-1, -2, 3], ![1, 0, -1]]

def raw9948step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1]]

def raw9949 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, -2, 2, -1], ![-1, 2, -3, 2]]

def raw9949step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, -2, 2], ![1, 2, -3], ![-1, -1, 2]]

def raw9949step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 2, -2], ![-1, -2, 3], ![1, 1, -2]]

def raw9949step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2]]

def raw9950 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![2, -3, 1, 0], ![-2, 3, -2, 1]]

def raw9950step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, -3, 3], ![1, 1, -2], ![-1, 0, 1]]

def raw9950step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 3, -3], ![-1, -1, 2], ![1, 0, -1]]

def raw9950step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

def raw9951 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![2, -2, 1, -1], ![-2, 2, -2, 2]]

def raw9951step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, -2, 2], ![1, 1, -2], ![-1, -1, 2]]

def raw9951step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical311
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9952 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-4, 2, -1, 3], ![4, -2, -1, -1]]

def raw9952step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![0, 2, -2], ![2, -1, -1], ![-2, 3, -1]]

def raw9952step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 4, -4], ![2, -1, -1]]

def raw9953 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-4, 2, 0, 2], ![4, -2, -2, 0]]

def raw9953step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![0, 2, -2], ![2, 0, -2], ![-2, 2, 0]]

def raw9953step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 4, -4], ![2, -2, 0]]

def raw9954 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-4, 3, -1, 2], ![4, -3, -1, 0]]

def raw9954step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![0, 3, -3], ![2, -1, -1], ![-2, 2, 0]]

def raw9954step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 4, -4], ![2, -1, -1]]

def raw9955 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-4, 3, 0, 1], ![4, -3, -2, 1]]

def raw9955step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![0, 3, -3], ![2, 0, -2], ![-2, 1, 1]]

def raw9955step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![0, -3, 3], ![-2, 0, 2], ![2, -1, -1]]

def raw9955step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 4, -4], ![2, -1, -1]]

def raw9956 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-3, 2, -1, 2], ![3, -2, -1, 0]]

def raw9956step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![0, 2, -2], ![2, -1, -1], ![-2, 2, 0]]

def raw9956step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

def raw9957 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-3, 2, 0, 1], ![3, -2, -2, 1]]

def raw9957step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![0, 2, -2], ![2, 0, -2], ![-2, 1, 1]]

def raw9957step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, -2, 2], ![-2, 0, 2], ![2, -1, -1]]

def raw9957step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

def raw9958 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-3, 3, -1, 1], ![3, -3, -1, 1]]

def raw9958step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![0, 3, -3], ![2, -1, -1], ![-2, 1, 1]]

def raw9958step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 3, -3], ![2, -1, -1]]

def raw9959 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-3, 3, 0, 0], ![3, -3, -2, 2]]

def raw9959step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![0, 3, -3], ![2, 0, -2], ![-2, 0, 2]]

def raw9959step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 3, -3], ![2, 0, -2]]

def raw9960 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-3, 4, -2, 1], ![3, -4, 0, 1]]

def raw9960step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![0, 4, -4], ![2, -2, 0], ![-2, 1, 1]]

def raw9960step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, -4, 4], ![-2, 2, 0], ![2, -1, -1]]

def raw9960step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 4, -4], ![2, -1, -1]]

def raw9961 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-2, -2, -1, 5], ![2, 2, -1, -3]]

def raw9961step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![2, -1, -1], ![-2, 5, -3]]

def raw9961step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 2, -2], ![2, -1, -1]]

def raw9962 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-2, -2, 0, 4], ![2, 2, -2, -2]]

def raw9962step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![2, 0, -2], ![-2, 4, -2]]

def raw9962step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 2, -2], ![2, -2, 0]]

def raw9963 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-2, -2, 1, 3], ![2, 2, -3, -1]]

def raw9963step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![2, 1, -3], ![-2, 3, -1]]

def raw9963step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 2, -2], ![2, -3, 1]]

def raw9964 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-2, -2, 2, 2], ![2, 2, -4, 0]]

def raw9964step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![2, 2, -4], ![-2, 2, 0]]

def raw9964step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, 2, -2], ![-2, -2, 4], ![2, -2, 0]]

def raw9964step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 2, -2], ![2, -2, 0]]

def raw9965 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-2, -2, 3, 1], ![2, 2, -5, 1]]

def raw9965step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![2, 3, -5], ![-2, 1, 1]]

def raw9965step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, 2, -2], ![-2, -3, 5], ![2, -1, -1]]

def raw9965step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 2, -2], ![2, -1, -1]]

def raw9966 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-2, 2, -1, 1], ![2, -2, -1, 1]]

def raw9966step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 2, -2], ![2, -1, -1], ![-2, 1, 1]]

def raw9966step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]

def raw9967 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-2, 2, 1, -1], ![2, -2, -3, 3]]

def raw9967step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 2, -2], ![2, 1, -3], ![-2, -1, 3]]

def raw9967step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![2, 1, -3]]

def raw9968 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-2, 3, -2, 1], ![2, -3, 0, 1]]

def raw9968step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 3, -3], ![2, -2, 0], ![-2, 1, 1]]

def raw9968step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, -3, 3], ![-2, 2, 0], ![2, -1, -1]]

def raw9968step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

def raw9969 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-2, 3, -1, 0], ![2, -3, -1, 2]]

def raw9969step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 3, -3], ![2, -1, -1], ![-2, 0, 2]]

def raw9969step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

def raw9970 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-2, 3, 0, -1], ![2, -3, -2, 3]]

def raw9970step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 3, -3], ![2, 0, -2], ![-2, -1, 3]]

def raw9970step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![2, 0, -2]]

def raw9971 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-2, 4, -3, 1], ![2, -4, 1, 1]]

def raw9971step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 4, -4], ![2, -3, 1], ![-2, 1, 1]]

def raw9971step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, -4, 4], ![-2, 3, -1], ![2, -1, -1]]

def raw9971step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 4, -4], ![2, -1, -1]]

def raw9972 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-2, 4, -2, 0], ![2, -4, 0, 2]]

def raw9972step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 4, -4], ![2, -2, 0], ![-2, 0, 2]]

def raw9972step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 4, -4], ![2, -2, 0]]

def raw9973 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-1, -2, -1, 4], ![1, 2, -1, -2]]

def raw9973step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![2, -1, -1], ![-2, 4, -2]]

def raw9973step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def raw9974 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-1, -2, 0, 3], ![1, 2, -2, -1]]

def raw9974step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![2, 0, -2], ![-2, 3, -1]]

def raw9974step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def raw9975 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-1, -2, 1, 2], ![1, 2, -3, 0]]

def raw9975step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![2, 1, -3], ![-2, 2, 0]]

def raw9975step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, 2, -2], ![-2, -1, 3], ![2, -2, 0]]

def raw9975step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def raw9976 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-1, -2, 2, 1], ![1, 2, -4, 1]]

def raw9976step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![2, 2, -4], ![-2, 1, 1]]

def raw9976step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, 2, -2], ![-2, -2, 4], ![2, -1, -1]]

def raw9976step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def raw9977 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-1, -2, 3, 0], ![1, 2, -5, 2]]

def raw9977step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![2, 3, -5], ![-2, 0, 2]]

def raw9977step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, 2, -2], ![-2, -3, 5], ![2, 0, -2]]

def raw9977step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

def raw9978 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-1, 2, 0, -1], ![1, -2, -2, 3]]

def raw9978step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 2, -2], ![2, 0, -2], ![-2, -1, 3]]

def raw9978step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

def raw9979 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-1, 2, 1, -2], ![1, -2, -3, 4]]

def raw9979step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 2, -2], ![2, 1, -3], ![-2, -2, 4]]

def raw9979step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 2, -2], ![2, 1, -3]]

def raw9980 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-1, 3, -2, 0], ![1, -3, 0, 2]]

def raw9980step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 3, -3], ![2, -2, 0], ![-2, 0, 2]]

def raw9980step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![2, -2, 0]]

def raw9981 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-1, 3, -1, -1], ![1, -3, -1, 3]]

def raw9981step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 3, -3], ![2, -1, -1], ![-2, -1, 3]]

def raw9981step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![2, -1, -1]]

def raw9982 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-1, 3, 0, -2], ![1, -3, -2, 4]]

def raw9982step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 3, -3], ![2, 0, -2], ![-2, -2, 4]]

def raw9982step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 3, -3], ![2, 0, -2]]

def raw9983 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-1, 4, -3, 0], ![1, -4, 1, 2]]

def raw9983step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 4, -4], ![2, -3, 1], ![-2, 0, 2]]

def raw9983step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, -4, 4], ![-2, 3, -1], ![2, 0, -2]]

def raw9983step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 4, -4], ![2, -2, 0]]

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

def raw9984 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![0, 2, 0, -2], ![0, -2, -2, 4]]

def raw9984step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-2, -2, 4]]

def raw9984step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![2, 0, -2]]

def raw9985 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![1, -3, 1, 1], ![-1, 3, -3, 1]]

def raw9985step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, -3, 3], ![2, 1, -3], ![-2, 1, 1]]

def raw9985step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 3, -3], ![-2, -1, 3], ![2, -1, -1]]

def raw9985step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![2, -1, -1]]

def raw9986 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![1, -2, 0, 1], ![-1, 2, -2, 1]]

def raw9986step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, -2, 2], ![2, 0, -2], ![-2, 1, 1]]

def raw9986step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 2, -2], ![-2, 0, 2], ![2, -1, -1]]

def raw9986step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

def raw9987 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![1, -2, 1, 0], ![-1, 2, -3, 2]]

def raw9987step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, -2, 2], ![2, 1, -3], ![-2, 0, 2]]

def raw9987step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 2, -2], ![-2, -1, 3], ![2, 0, -2]]

def raw9987step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

def raw9988 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![2, -3, 0, 1], ![-2, 3, -2, 1]]

def raw9988step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, -3, 3], ![2, 0, -2], ![-2, 1, 1]]

def raw9988step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 3, -3], ![-2, 0, 2], ![2, -1, -1]]

def raw9988step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

def raw9989 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![2, -3, 1, 0], ![-2, 3, -3, 2]]

def raw9989step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, -3, 3], ![2, 1, -3], ![-2, 0, 2]]

def raw9989step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 3, -3], ![-2, -1, 3], ![2, 0, -2]]

def raw9989step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![2, 0, -2]]

def raw9990 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![2, -2, 0, 0], ![-2, 2, -2, 2]]

def raw9990step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, -2, 2], ![2, 0, -2], ![-2, 0, 2]]

def raw9990step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![2, 0, -2]]

def raw9991 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![2, -2, 1, -1], ![-2, 2, -3, 3]]

def raw9991step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, -2, 2], ![2, 1, -3], ![-2, -1, 3]]

def raw9991step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![2, 1, -3]]

def raw9992 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![3, -3, 0, 0], ![-3, 3, -2, 2]]

def raw9992step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, -3, 3], ![2, 0, -2], ![-2, 0, 2]]

def raw9992step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 3, -3], ![2, 0, -2]]

def raw9993 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![3, -2, 0, -1], ![-3, 2, -2, 3]]

def raw9993step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, -2, 2], ![2, 0, -2], ![-2, -1, 3]]

def raw9993step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![2, 0, -2]]

def raw9994 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, -3, 2], ![-1, 1, 1, -1], ![1, -2, 2, -1]]

def raw9994step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![1, 1, -2], ![-3, 1, 2], ![2, -1, -1]]

def raw9994step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -1, 2], ![3, -1, -2], ![-2, 1, 1]]

def raw9994step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

def raw9995 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, -3, 2], ![0, 1, 1, -2], ![0, -2, 2, 0]]

def raw9995step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 3, -2], ![0, -1, -1, 2], ![0, 2, -2, 0]]

def raw9995step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![2, -2, 0]]

def raw9995step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]

def raw9996 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 0, -1, 3], ![0, -1, 3, -2]]

def raw9996step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw9997 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, -1, 3], ![-1, 0, 3, -2]]

def raw9997step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw9998 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 0, -1, 2], ![-1, -1, 3, -1]]

def raw9998step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw9999 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-1, -2, 3]]

def raw9999step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

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

def coordinateChunk0 : Array (Fin 909) := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64]

def coordinateChunk1 : Array (Fin 909) := #[65, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 89, 94, 95, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 110, 112, 113, 114, 115, 116, 119, 120, 122, 123, 124, 125, 126, 127, 128, 129, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 177]

def coordinateChunk2 : Array (Fin 909) := #[190, 191, 196, 197, 199, 201, 203, 204, 205, 207, 208, 209, 216, 217, 226, 228, 230, 231, 236, 237, 238, 239, 253, 256, 257, 259, 260, 262, 266, 267, 268, 271, 273, 275, 276, 277, 278, 279, 280, 281, 282, 284, 286, 287, 288, 289, 290, 291, 293, 299, 300, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318]

def coordinateChunk3 : Array (Fin 909) := #[319, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 352, 378, 379, 383, 392, 398, 399, 400, 425, 426, 428, 453, 460, 472, 489, 490, 492, 493, 494, 495, 498, 499, 500, 501, 502, 503, 505, 506, 507, 508, 517, 538, 539, 540, 541, 543, 545, 546, 640, 643, 702, 709, 721, 723, 726, 727, 728, 735, 736, 737, 738, 739, 745]

def coordinateChunk4 : Array (Fin 909) := #[751, 753, 760, 764, 783, 784, 794, 796, 798, 810, 811, 812, 818, 855, 870]

def coordinateMap (i : Fin 271) : Fin 909 :=
  ((#[coordinateChunk0, coordinateChunk1, coordinateChunk2, coordinateChunk3, coordinateChunk4])[i.val / 64]!)[i.val % 64]!

end MUB6.Certificate.PairSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_ExtraPermutations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

def extraPermutation0 : Equiv.Perm (Fin 2) where
  toFun := ![0, 1]
  invFun := ![0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation1 : Equiv.Perm (Fin 2) where
  toFun := ![1, 0]
  invFun := ![1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation2 : Equiv.Perm (Fin 3) where
  toFun := ![0, 1, 2]
  invFun := ![0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation3 : Equiv.Perm (Fin 3) where
  toFun := ![0, 2, 1]
  invFun := ![0, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation4 : Equiv.Perm (Fin 3) where
  toFun := ![1, 0, 2]
  invFun := ![1, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation5 : Equiv.Perm (Fin 3) where
  toFun := ![1, 2, 0]
  invFun := ![2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation6 : Equiv.Perm (Fin 3) where
  toFun := ![2, 0, 1]
  invFun := ![1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation7 : Equiv.Perm (Fin 3) where
  toFun := ![2, 1, 0]
  invFun := ![2, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation8 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation9 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 3, 2]
  invFun := ![0, 1, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation10 : Equiv.Perm (Fin 4) where
  toFun := ![0, 2, 1, 3]
  invFun := ![0, 2, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation11 : Equiv.Perm (Fin 4) where
  toFun := ![0, 2, 3, 1]
  invFun := ![0, 3, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation12 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation13 : Equiv.Perm (Fin 4) where
  toFun := ![1, 3, 0, 2]
  invFun := ![2, 0, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation14 : Equiv.Perm (Fin 4) where
  toFun := ![1, 3, 2, 0]
  invFun := ![3, 0, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation15 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation16 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 3, 1]
  invFun := ![1, 3, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation17 : Equiv.Perm (Fin 4) where
  toFun := ![2, 1, 0, 3]
  invFun := ![2, 1, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation18 : Equiv.Perm (Fin 4) where
  toFun := ![2, 3, 0, 1]
  invFun := ![2, 3, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation19 : Equiv.Perm (Fin 4) where
  toFun := ![2, 3, 1, 0]
  invFun := ![3, 2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation20 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation21 : Equiv.Perm (Fin 4) where
  toFun := ![3, 1, 0, 2]
  invFun := ![2, 1, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation22 : Equiv.Perm (Fin 4) where
  toFun := ![3, 2, 0, 1]
  invFun := ![2, 3, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation23 : Equiv.Perm (Fin 4) where
  toFun := ![3, 2, 1, 0]
  invFun := ![3, 2, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation24 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation25 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 4, 3]
  invFun := ![0, 1, 2, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation26 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 3, 2, 4]
  invFun := ![0, 1, 3, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation27 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 3, 4, 2]
  invFun := ![0, 1, 4, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation28 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 4, 2, 3]
  invFun := ![0, 1, 3, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation29 : Equiv.Perm (Fin 5) where
  toFun := ![0, 2, 1, 3, 4]
  invFun := ![0, 2, 1, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation30 : Equiv.Perm (Fin 5) where
  toFun := ![0, 2, 1, 4, 3]
  invFun := ![0, 2, 1, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation31 : Equiv.Perm (Fin 5) where
  toFun := ![0, 2, 3, 1, 4]
  invFun := ![0, 3, 1, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation32 : Equiv.Perm (Fin 5) where
  toFun := ![0, 2, 3, 4, 1]
  invFun := ![0, 4, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation33 : Equiv.Perm (Fin 5) where
  toFun := ![0, 2, 4, 1, 3]
  invFun := ![0, 3, 1, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation34 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation35 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 4, 3]
  invFun := ![1, 0, 2, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation36 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 3, 4, 2]
  invFun := ![1, 0, 4, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation37 : Equiv.Perm (Fin 5) where
  toFun := ![1, 2, 3, 4, 0]
  invFun := ![4, 0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation38 : Equiv.Perm (Fin 5) where
  toFun := ![1, 3, 4, 0, 2]
  invFun := ![3, 0, 4, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation39 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation40 : Equiv.Perm (Fin 5) where
  toFun := ![2, 3, 0, 1, 4]
  invFun := ![2, 3, 0, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation41 : Equiv.Perm (Fin 5) where
  toFun := ![2, 4, 0, 1, 3]
  invFun := ![2, 3, 0, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation42 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation43 : Equiv.Perm (Fin 5) where
  toFun := ![3, 2, 0, 1, 4]
  invFun := ![2, 3, 1, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation44 : Equiv.Perm (Fin 5) where
  toFun := ![3, 2, 4, 1, 0]
  invFun := ![4, 3, 1, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation45 : Equiv.Perm (Fin 5) where
  toFun := ![3, 4, 0, 1, 2]
  invFun := ![2, 3, 4, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation46 : Equiv.Perm (Fin 5) where
  toFun := ![3, 4, 1, 0, 2]
  invFun := ![3, 2, 4, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation47 : Equiv.Perm (Fin 5) where
  toFun := ![3, 4, 1, 2, 0]
  invFun := ![4, 2, 3, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation48 : Equiv.Perm (Fin 5) where
  toFun := ![3, 4, 2, 1, 0]
  invFun := ![4, 3, 2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation49 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation50 : Equiv.Perm (Fin 5) where
  toFun := ![4, 2, 0, 1, 3]
  invFun := ![2, 3, 1, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation51 : Equiv.Perm (Fin 5) where
  toFun := ![4, 2, 3, 1, 0]
  invFun := ![4, 3, 1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation52 : Equiv.Perm (Fin 5) where
  toFun := ![4, 3, 0, 1, 2]
  invFun := ![2, 3, 4, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation53 : Equiv.Perm (Fin 5) where
  toFun := ![4, 3, 1, 0, 2]
  invFun := ![3, 2, 4, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation54 : Equiv.Perm (Fin 5) where
  toFun := ![4, 3, 1, 2, 0]
  invFun := ![4, 2, 3, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation55 : Equiv.Perm (Fin 5) where
  toFun := ![4, 3, 2, 1, 0]
  invFun := ![4, 3, 2, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation56 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 4, 5, 3]
  invFun := ![0, 1, 2, 5, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation57 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 1, 3, 4, 5]
  invFun := ![0, 2, 1, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation58 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 3, 4, 5, 1]
  invFun := ![0, 5, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation59 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 5, 1, 2, 3]
  invFun := ![0, 3, 4, 5, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation60 : Equiv.Perm (Fin 6) where
  toFun := ![1, 2, 0, 3, 4, 5]
  invFun := ![2, 0, 1, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation61 : Equiv.Perm (Fin 6) where
  toFun := ![1, 2, 3, 4, 5, 0]
  invFun := ![5, 0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation62 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation63 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation64 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 0, 1, 2]
  invFun := ![3, 4, 5, 0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation65 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 1, 2, 0]
  invFun := ![5, 3, 4, 0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation66 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 2, 3, 5]
  invFun := ![1, 2, 3, 4, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation67 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_ExtraCanonical0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics

def extraRaw0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]

def extraRaw0step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]

def extraRaw0step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]

def extraRaw0step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

def extraRaw1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]

def extraRaw1step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]

def extraRaw1step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]

def extraRaw1step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

def extraRaw2 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![1, -1], ![0, 0], ![1, -1]]

def extraRaw2step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![1, -1], ![1, -1]]

def extraRaw2step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def extraRaw3 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]

def extraRaw3step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![-2, 1, 1]]

def extraRaw3step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-2, 0, 2], ![-2, 1, 1]]

def extraRaw3step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def extraRaw4 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![1, -1], ![1, -1], ![0, 0]]

def extraRaw4step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![1, -1], ![1, -1]]

def extraRaw4step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def extraRaw5 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]

def extraRaw5step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]

def extraRaw5step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]

def extraRaw5step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def extraRaw6 : Matrix (Fin 6) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![0, 0], ![-1, 1], ![-1, 1], ![-1, 1]]

def extraRaw6step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]

def extraRaw6step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def extraRaw7 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

def extraRaw7step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

def extraRaw8 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]

def extraRaw8step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]

def extraRaw8step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def extraRaw9 : Matrix (Fin 6) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![0, 0], ![-1, 1], ![0, 0], ![0, 0]]

def extraRaw9step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![0, 0], ![-1, 1], ![0, 0]]

def extraRaw9step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![0, 0], ![-1, 1]]

def extraRaw9step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![-1, 1]]

def extraRaw9step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![1, -1], ![-1, 1]]

def extraRaw9step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

def extraRaw10 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def extraRaw10step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def extraRaw10step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def extraRaw11 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]

def extraRaw11step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1]]

def extraRaw11step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1]]

def extraRaw11step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def extraRaw12 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]

def extraRaw12step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]

def extraRaw12step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]

def extraRaw12step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def extraRaw13 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def extraRaw13step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![0, 1, 0, -1], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def extraRaw13step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def extraRaw14 : Matrix (Fin 6) (Fin 2) ℤ := ![![1, -1], ![-1, 1], ![0, 0], ![0, 0], ![0, 0], ![0, 0]]

def extraRaw14step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![1, -1], ![-1, 1], ![0, 0], ![0, 0], ![0, 0]]

def extraRaw14step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![1, -1], ![-1, 1], ![0, 0], ![0, 0]]

def extraRaw14step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![1, -1], ![-1, 1], ![0, 0]]

def extraRaw14step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![1, -1], ![-1, 1]]

def extraRaw14step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

def extraRaw15 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]

def extraRaw15step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]

def extraRaw15step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1]]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_ExtraCanonical1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics

def extraRaw16 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![1, -1], ![0, 0], ![-1, 1], ![0, 0], ![0, 0]]

def extraRaw16step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![1, -1], ![0, 0], ![-1, 1], ![0, 0]]

def extraRaw16step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![1, -1], ![0, 0], ![-1, 1]]

def extraRaw16step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![1, -1], ![-1, 1]]

def extraRaw16step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![1, -1], ![-1, 1]]

def extraRaw16step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

def extraRaw17 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def extraRaw17step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def extraRaw17step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def extraRaw18 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]

def extraRaw18step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1]]

def extraRaw18step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1]]

def extraRaw18step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def extraRaw19 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]

def extraRaw19step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]

def extraRaw19step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1]]

def extraRaw19step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def extraRaw20 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![-1, -1, 0, 2], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def extraRaw20step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 2, -2, -1], ![1, 1, 0, -2], ![0, 0, 0, 0], ![0, -1, 0, 1], ![-1, -1, 1, 1], ![-1, -1, 1, 1]]

def extraRaw20step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 2, -2, -1], ![1, 1, 0, -2], ![0, -1, 0, 1], ![-1, -1, 1, 1], ![-1, -1, 1, 1]]

def extraRaw20step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def extraRaw21 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![0, 0], ![-1, 1], ![1, -1], ![0, 0]]

def extraRaw21step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![0, 0], ![-1, 1], ![1, -1]]

def extraRaw21step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-1, 1], ![1, -1]]

def extraRaw21step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![1, -1]]

def extraRaw21step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

def extraRaw22 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![0, 1, -1]]

def extraRaw22step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![0, -1, 1]]

def extraRaw22step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![-1, -1, 2], ![0, -1, 1]]

def extraRaw22step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def extraRaw23 : Matrix (Fin 6) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![0, 0], ![0, 0], ![-1, 1], ![0, 0]]

def extraRaw23step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![0, 0], ![0, 0], ![-1, 1]]

def extraRaw23step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![0, 0], ![-1, 1]]

def extraRaw23step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![-1, 1]]

def extraRaw23step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![1, -1], ![-1, 1]]

def extraRaw23step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

def extraRaw24 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]

def extraRaw24step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]

def extraRaw24step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1]]

def extraRaw24step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

def extraRaw25 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![-1, 1, 0], ![0, 1, -1]]

def extraRaw25step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![0, -1, 1]]

def extraRaw25step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![0, -1, 1]]

def extraRaw25step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def extraRaw26 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def extraRaw26step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def extraRaw26step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def extraRaw27 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![1, 1, 0, -2], ![1, 1, -1, -1]]

def extraRaw27step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 2, -1, -2], ![1, 1, -1, -1], ![0, 0, 0, 0], ![0, -1, 1, 0], ![-1, -1, 0, 2], ![-1, -1, 1, 1]]

def extraRaw27step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 2, -1, -2], ![1, 1, -1, -1], ![0, -1, 1, 0], ![-1, -1, 0, 2], ![-1, -1, 1, 1]]

def extraRaw27step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def extraRaw28 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![0, 0], ![-1, 1], ![0, 0], ![1, -1]]

def extraRaw28step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![0, 0], ![-1, 1], ![1, -1]]

def extraRaw28step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-1, 1], ![1, -1]]

def extraRaw28step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![1, -1]]

def extraRaw28step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

def extraRaw29 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]

def extraRaw29step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]

def extraRaw29step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]

def extraRaw29step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def extraRaw30 : Matrix (Fin 6) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![0, 0], ![0, 0], ![0, 0], ![-1, 1]]

def extraRaw30step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![0, 0], ![0, 0], ![-1, 1]]

def extraRaw30step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![0, 0], ![-1, 1]]

def extraRaw30step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![-1, 1]]

def extraRaw30step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![1, -1], ![-1, 1]]

def extraRaw30step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

def extraRaw31 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2]]

def extraRaw31step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2]]

def extraRaw31step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2]]

def extraRaw31step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_ExtraCanonical2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics

def extraRaw32 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]

def extraRaw32step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0]]

def extraRaw32step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0]]

def extraRaw32step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def extraRaw33 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]

def extraRaw33step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]

def extraRaw33step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def extraRaw34 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def extraRaw34step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 2, -1, -2], ![1, 1, -1, -1], ![0, 0, 0, 0], ![0, -1, 1, 0], ![-1, -1, 1, 1], ![-1, -1, 0, 2]]

def extraRaw34step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 2, -1, -2], ![1, 1, -1, -1], ![0, -1, 1, 0], ![-1, -1, 1, 1], ![-1, -1, 0, 2]]

def extraRaw34step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def extraRaw35 : Matrix (Fin 6) (Fin 2) ℤ := ![![1, -1], ![2, -2], ![0, 0], ![-1, 1], ![-1, 1], ![-1, 1]]

def extraRaw35step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![1, -1], ![2, -2], ![-1, 1], ![-1, 1], ![-1, 1]]

def extraRaw35step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def extraRaw36 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

def extraRaw36step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

def extraRaw37 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![0, 0], ![0, 0], ![0, 0], ![0, 0]]

def extraRaw37step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![0, 0], ![0, 0], ![0, 0]]

def extraRaw37step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![0, 0], ![0, 0]]

def extraRaw37step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![0, 0]]

def extraRaw37step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

def extraRaw38 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]

def extraRaw38step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]

def extraRaw38step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1]]

def extraRaw39 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def extraRaw39step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def extraRaw39step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def extraRaw40 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]

def extraRaw40step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1]]

def extraRaw40step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1]]

def extraRaw40step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def extraRaw41 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]

def extraRaw41step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1]]

def extraRaw41step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1]]

def extraRaw41step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1]]

def extraRaw41step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def extraRaw42 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -2, 1, 1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def extraRaw42step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -2, 1, 1], ![0, 1, 0, -1], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def extraRaw42step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def extraRaw43 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]

def extraRaw43step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]

def extraRaw43step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]

def extraRaw43step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def extraRaw44 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![0, 0], ![-1, 1], ![0, 0], ![0, 0]]

def extraRaw44step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![0, 0], ![-1, 1], ![0, 0]]

def extraRaw44step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![0, 0], ![-1, 1]]

def extraRaw44step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1]]

def extraRaw44step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def extraRaw45 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def extraRaw45step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def extraRaw45step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

def extraRaw46 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]

def extraRaw46step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1]]

def extraRaw46step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1]]

def extraRaw46step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

def extraRaw47 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]

def extraRaw47step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]

def extraRaw47step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]

def extraRaw47step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![1, 0, -1]]

def extraRaw47step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_ExtraCanonical3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics

def extraRaw48 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -2, 0, 2], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def extraRaw48step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -2, 0, 2], ![0, 1, 0, -1], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def extraRaw48step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def extraRaw49 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![0, 0], ![-1, 1], ![1, -1], ![0, 0]]

def extraRaw49step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![0, 0], ![-1, 1], ![1, -1]]

def extraRaw49step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![1, -1]]

def extraRaw49step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def extraRaw50 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![0, 1, -1]]

def extraRaw50step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -2, 1], ![-1, 1, 0], ![1, 1, -2], ![0, 1, -1]]

def extraRaw50step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def extraRaw51 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![1, -1], ![0, 0], ![0, 0], ![-1, 1], ![0, 0]]

def extraRaw51step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![1, -1], ![0, 0], ![0, 0], ![-1, 1]]

def extraRaw51step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![1, -1], ![0, 0], ![-1, 1]]

def extraRaw51step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![1, -1], ![-1, 1]]

def extraRaw51step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![1, -1], ![-1, 1]]

def extraRaw51step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

def extraRaw52 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]

def extraRaw52step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, 0, 1]]

def extraRaw52step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![-1, 0, 1]]

def extraRaw52step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, -1, 2], ![-1, 0, 1]]

def extraRaw52step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

def extraRaw53 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![-1, 1, 0], ![0, 1, -1]]

def extraRaw53step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![0, -1, 1]]

def extraRaw53step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![0, -1, 1]]

def extraRaw53step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def extraRaw54 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def extraRaw54step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def extraRaw55 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -2, 1, 1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![1, 1, 0, -2], ![1, 1, -1, -1]]

def extraRaw55step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 1, 0, -2], ![1, 1, -1, -1]]

def extraRaw55step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 1, 0], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def extraRaw56 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![0, 0], ![-1, 1], ![0, 0], ![1, -1]]

def extraRaw56step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![0, 0], ![-1, 1], ![1, -1]]

def extraRaw56step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![1, -1]]

def extraRaw56step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def extraRaw57 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]

def extraRaw57step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]

def extraRaw57step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def extraRaw58 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![1, -1], ![0, 0], ![0, 0], ![0, 0], ![-1, 1]]

def extraRaw58step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![1, -1], ![0, 0], ![0, 0], ![-1, 1]]

def extraRaw58step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![1, -1], ![0, 0], ![-1, 1]]

def extraRaw58step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![1, -1], ![-1, 1]]

def extraRaw58step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![1, -1], ![-1, 1]]

def extraRaw58step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

def extraRaw59 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2]]

def extraRaw59step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]

def extraRaw59step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]

def extraRaw59step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2]]

def extraRaw59step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

def extraRaw60 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]

def extraRaw60step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0]]

def extraRaw60step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0]]

def extraRaw60step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def extraRaw61 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]

def extraRaw61step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]

def extraRaw61step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def extraRaw62 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -2, 1, 1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def extraRaw62step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def extraRaw62step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 1, 0], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def extraRaw63 : Matrix (Fin 6) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![0, 0], ![0, 0], ![-2, 2], ![-1, 1]]

def extraRaw63step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![0, 0], ![-2, 2], ![-1, 1]]

def extraRaw63step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-2, 2], ![-1, 1]]

def extraRaw63step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_ExtraCanonical4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics

def extraRaw64 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![1, 1, -2]]

def extraRaw64step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![1, 0, -1], ![0, 2, -2], ![1, 1, -2]]

def extraRaw64step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def extraRaw65 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![0, 0], ![1, -1], ![-1, 1], ![0, 0]]

def extraRaw65step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![0, 0], ![1, -1], ![-1, 1]]

def extraRaw65step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![1, -1], ![-1, 1]]

def extraRaw65step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![1, -1], ![-1, 1]]

def extraRaw65step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![1, -1], ![-1, 1]]

def extraRaw65step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

def extraRaw66 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![0, 1, -1]]

def extraRaw66step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 2, -1], ![0, 1, -1]]

def extraRaw66step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def extraRaw67 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]

def extraRaw67step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]

def extraRaw67step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def extraRaw68 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1]]

def extraRaw68step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1]]

def extraRaw68step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1]]

def extraRaw68step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

def extraRaw69 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]

def extraRaw69step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]

def extraRaw69step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def extraRaw70 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![0, 0, 0, 0], ![1, 0, 0, -1], ![0, 2, -1, -1], ![1, 1, -1, -1]]

def extraRaw70step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![1, 0, 0, -1], ![0, 2, -1, -1], ![1, 1, -1, -1]]

def extraRaw70step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def extraRaw71 : Matrix (Fin 6) (Fin 2) ℤ := ![![1, -1], ![-1, 1], ![0, 0], ![1, -1], ![-1, 1], ![0, 0]]

def extraRaw71step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![1, -1], ![-1, 1], ![0, 0], ![1, -1], ![-1, 1]]

def extraRaw71step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![1, -1], ![-1, 1], ![1, -1], ![-1, 1]]

def extraRaw71step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def extraRaw72 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![0, 1, -1]]

def extraRaw72step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![1, 1, -2], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1]]

def extraRaw72step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![1, 1, -2], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1]]

def extraRaw72step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def extraRaw73 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]

def extraRaw73step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]

def extraRaw73step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def extraRaw74 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1]]

def extraRaw74step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1]]

def extraRaw74step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1]]

def extraRaw74step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

def extraRaw75 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]

def extraRaw75step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1]]

def extraRaw75step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1]]

def extraRaw75step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def extraRaw76 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![-1, -1, 0, 2], ![0, 0, 0, 0], ![1, 0, 0, -1], ![0, 2, -1, -1], ![1, 1, -1, -1]]

def extraRaw76step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 2, -2, -1], ![1, 1, 0, -2], ![0, 0, 0, 0], ![-1, 0, 0, 1], ![0, -2, 1, 1], ![-1, -1, 1, 1]]

def extraRaw76step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 2, -2, -1], ![1, 1, 0, -2], ![-1, 0, 0, 1], ![0, -2, 1, 1], ![-1, -1, 1, 1]]

def extraRaw76step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 1, 0], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def extraRaw77 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![0, 1, -1]]

def extraRaw77step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![0, 1, -1]]

def extraRaw77step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![0, 1, -1]]

def extraRaw77step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]

def extraRaw77step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def extraRaw78 : Matrix (Fin 6) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![0, 0], ![1, -1], ![-2, 2], ![0, 0]]

def extraRaw78step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![0, 0], ![1, -1], ![-2, 2]]

def extraRaw78step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![1, -1], ![-2, 2]]

def extraRaw78step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![1, -1], ![1, -1], ![-2, 2]]

def extraRaw78step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def extraRaw79 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1]]

def extraRaw79step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, 0, 1]]

def extraRaw79step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![0, -2, 2], ![-1, 0, 1]]

def extraRaw79step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_ExtraCanonical5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics

def extraRaw80 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![-2, 2, 0], ![0, 1, -1]]

def extraRaw80step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![-2, 2, 0], ![0, 1, -1]]

def extraRaw80step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def extraRaw81 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1]]

def extraRaw81step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]

def extraRaw81step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]

def extraRaw81step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def extraRaw82 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![0, 0, 0, 0], ![1, 0, -1, 0], ![0, 2, 0, -2], ![1, 1, -1, -1]]

def extraRaw82step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![1, 0, -1, 0], ![0, 2, 0, -2], ![1, 1, -1, -1]]

def extraRaw82step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def extraRaw83 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![0, 0], ![0, 0], ![-1, 1], ![1, -1]]

def extraRaw83step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![0, 0], ![-1, 1], ![1, -1]]

def extraRaw83step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-1, 1], ![1, -1]]

def extraRaw83step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![1, -1]]

def extraRaw83step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

def extraRaw84 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2]]

def extraRaw84step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2]]

def extraRaw84step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2]]

def extraRaw84step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1]]

def extraRaw85 : Matrix (Fin 6) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![0, 0], ![1, -1], ![-1, 1], ![-1, 1]]

def extraRaw85step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![1, -1], ![-1, 1], ![-1, 1]]

def extraRaw85step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![1, -1], ![1, -1], ![-1, 1], ![-1, 1]]

def extraRaw85step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def extraRaw86 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2]]

def extraRaw86step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2]]

def extraRaw86step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def extraRaw87 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![-1, 1, 0]]

def extraRaw87step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![-1, 2, -1], ![-1, 1, 0]]

def extraRaw87step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def extraRaw88 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]

def extraRaw88step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]

def extraRaw88step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def extraRaw89 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![0, 0, 0, 0], ![1, 0, -1, 0], ![0, 2, -1, -1], ![1, 1, 0, -2]]

def extraRaw89step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![1, 0, -1, 0], ![0, 2, -1, -1], ![1, 1, 0, -2]]

def extraRaw89step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, 0, 0], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def extraRaw90 : Matrix (Fin 6) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![0, 0], ![0, 0], ![-1, 1], ![-2, 2]]

def extraRaw90step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![0, 0], ![-1, 1], ![-2, 2]]

def extraRaw90step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-2, 2]]

def extraRaw90step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def extraRaw91 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![0, 2, -2]]

def extraRaw91step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![0, 2, -2]]

def extraRaw91step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def extraRaw92 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![0, 0], ![1, -1], ![0, 0], ![-1, 1]]

def extraRaw92step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![0, 0], ![1, -1], ![-1, 1]]

def extraRaw92step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![1, -1], ![-1, 1]]

def extraRaw92step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![1, -1], ![-1, 1]]

def extraRaw92step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![1, -1], ![-1, 1]]

def extraRaw92step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

def extraRaw93 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1]]

def extraRaw93step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1]]

def extraRaw93step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def extraRaw94 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]

def extraRaw94step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]

def extraRaw94step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def extraRaw95 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1]]

def extraRaw95step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1]]

def extraRaw95step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1]]

def extraRaw95step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_ExtraCanonical6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics

def extraRaw96 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]

def extraRaw96step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]

def extraRaw96step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def extraRaw97 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![0, 0, 0, 0], ![1, 0, 0, -1], ![1, 1, -1, -1], ![0, 2, -1, -1]]

def extraRaw97step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![1, 0, 0, -1], ![1, 1, -1, -1], ![0, 2, -1, -1]]

def extraRaw97step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def extraRaw98 : Matrix (Fin 6) (Fin 2) ℤ := ![![1, -1], ![-1, 1], ![0, 0], ![1, -1], ![0, 0], ![-1, 1]]

def extraRaw98step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![1, -1], ![-1, 1], ![0, 0], ![1, -1], ![-1, 1]]

def extraRaw98step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![1, -1], ![-1, 1], ![1, -1], ![-1, 1]]

def extraRaw98step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def extraRaw99 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1]]

def extraRaw99step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![1, 1, -2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]

def extraRaw99step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![1, 1, -2], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]

def extraRaw99step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def extraRaw100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]

def extraRaw100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]

def extraRaw100step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def extraRaw101 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1]]

def extraRaw101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1]]

def extraRaw101step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1]]

def extraRaw101step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

def extraRaw102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]

def extraRaw102step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1]]

def extraRaw102step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1]]

def extraRaw102step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def extraRaw103 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![-1, -1, 0, 2], ![0, 0, 0, 0], ![1, 0, 0, -1], ![1, 1, -1, -1], ![0, 2, -1, -1]]

def extraRaw103step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 2, -2, -1], ![1, 1, 0, -2], ![0, 0, 0, 0], ![-1, 0, 0, 1], ![-1, -1, 1, 1], ![0, -2, 1, 1]]

def extraRaw103step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 2, -2, -1], ![1, 1, 0, -2], ![-1, 0, 0, 1], ![-1, -1, 1, 1], ![0, -2, 1, 1]]

def extraRaw103step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 1, 0], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def extraRaw104 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![0, 0], ![0, 0], ![1, -1], ![-1, 1]]

def extraRaw104step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![0, 0], ![1, -1], ![-1, 1]]

def extraRaw104step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![1, -1], ![-1, 1]]

def extraRaw104step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![1, -1], ![-1, 1]]

def extraRaw104step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![1, -1], ![-1, 1]]

def extraRaw104step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

def extraRaw105 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![-1, 2, -1]]

def extraRaw105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![-1, 2, -1]]

def extraRaw105step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![-1, 2, -1]]

def extraRaw105step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1]]

def extraRaw106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1]]

def extraRaw106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1]]

def extraRaw106step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def extraRaw107 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]

def extraRaw107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]

def extraRaw107step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def extraRaw108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![0, 1, -1]]

def extraRaw108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![0, 1, -1]]

def extraRaw108step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def extraRaw109 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![0, 0, 0, 0], ![1, 0, -1, 0], ![1, 1, 0, -2], ![0, 2, -1, -1]]

def extraRaw109step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![1, 0, -1, 0], ![1, 1, 0, -2], ![0, 2, -1, -1]]

def extraRaw109step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, 0, 0], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def extraRaw110 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2]]

def extraRaw110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2]]

def extraRaw110step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2]]

def extraRaw110step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def extraRaw111 : Matrix (Fin 6) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![0, 0], ![1, -1], ![0, 0], ![-2, 2]]

def extraRaw111step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![0, 0], ![1, -1], ![-2, 2]]

def extraRaw111step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![1, -1], ![-2, 2]]

def extraRaw111step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![1, -1], ![1, -1], ![-2, 2]]

def extraRaw111step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_ExtraCanonical7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics

def extraRaw112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![0, 2, -2]]

def extraRaw112step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]

def extraRaw112step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]

def extraRaw112step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def extraRaw113 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0]]

def extraRaw113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0]]

def extraRaw113step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def extraRaw114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]

def extraRaw114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]

def extraRaw114step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]

def extraRaw114step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def extraRaw115 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![0, 0, 0, 0], ![1, 0, -1, 0], ![1, 1, -1, -1], ![0, 2, 0, -2]]

def extraRaw115step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![1, 0, -1, 0], ![1, 1, -1, -1], ![0, 2, 0, -2]]

def extraRaw115step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def extraRaw116 : Matrix (Fin 6) (Fin 2) ℤ := ![![2, -2], ![0, 0], ![0, 0], ![-2, 2], ![0, 0], ![0, 0]]

def extraRaw116step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![0, 0], ![0, 0], ![-2, 2], ![0, 0]]

def extraRaw116step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![2, -2], ![0, 0], ![0, 0], ![-2, 2]]

def extraRaw116step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![2, -2], ![0, 0], ![-2, 2]]

def extraRaw116step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![2, -2], ![-2, 2]]

def extraRaw116step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

def extraRaw117 : Matrix (Fin 6) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![1, -1], ![-3, 3], ![-1, 1], ![-1, 1]]

def extraRaw117step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![3, -3]]

def extraRaw118 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![1, -1, 0], ![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0]]

def extraRaw118step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]

def extraRaw119 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![2, -2], ![0, 0], ![0, 0]]

def extraRaw119step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![2, -2], ![0, 0]]

def extraRaw119step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![2, -2]]

def extraRaw119step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![2, -2]]

def extraRaw119step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

def extraRaw120 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0]]

def extraRaw120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, 0, 0]]

def extraRaw120step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2]]

def extraRaw120step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, -2, 2]]

def extraRaw120step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![0, 2, -2], ![0, -2, 2]]

def extraRaw120step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![2, -2], ![-2, 2]]

def extraRaw120step5 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

def extraRaw121 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![-1, 1], ![-1, 1]]

def extraRaw121step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def extraRaw122 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0]]

def extraRaw122step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def extraRaw123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1]]

def extraRaw123step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def extraRaw124 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]

def extraRaw124step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![1, -1], ![1, -1], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]

def extraRaw124step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def extraRaw125 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, 0, -1], ![-1, -2, 3], ![-1, 0, 1], ![-1, 0, 1]]

def extraRaw125step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]

def extraRaw126 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 2, -1, -2], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-1, -2, 1, 2], ![-1, 0, 1, 0], ![-1, 0, 1, 0]]

def extraRaw126step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, -2, 1, -1]]

def extraRaw127 : Matrix (Fin 6) (Fin 2) ℤ := ![![2, -2], ![-2, 2], ![0, 0], ![0, 0], ![0, 0], ![0, 0]]

def extraRaw127step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![-2, 2], ![0, 0], ![0, 0], ![0, 0]]

def extraRaw127step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![2, -2], ![-2, 2], ![0, 0], ![0, 0]]

def extraRaw127step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![2, -2], ![-2, 2], ![0, 0]]

def extraRaw127step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![2, -2], ![-2, 2]]

def extraRaw127step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_ExtraCanonical8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics

def extraRaw128 : Matrix (Fin 6) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]

def extraRaw128step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]

def extraRaw129 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![-1, -1, 2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]

def extraRaw129step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def extraRaw130 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![2, -2], ![0, 0], ![0, 0], ![0, 0], ![0, 0]]

def extraRaw130step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![2, -2], ![0, 0], ![0, 0], ![0, 0]]

def extraRaw130step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![2, -2], ![0, 0], ![0, 0]]

def extraRaw130step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![2, -2], ![0, 0]]

def extraRaw130step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

def extraRaw131 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]

def extraRaw131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]

def extraRaw131step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0]]

def extraRaw131step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 2, -2], ![0, -2, 2], ![0, 0, 0]]

def extraRaw131step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![0, 2, -2], ![0, -2, 2]]

def extraRaw131step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![2, -2], ![-2, 2]]

def extraRaw131step5 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

def extraRaw132 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]

def extraRaw132step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]

def extraRaw133 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, -3, 2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]

def extraRaw133step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]

def extraRaw133step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def extraRaw134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![3, -2, -1], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]

def extraRaw134step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def extraRaw135 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -2, 1], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]

def extraRaw135step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]

def extraRaw135step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def extraRaw136 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 2, -1, -2], ![1, -2, -1, 2], ![1, 0, -1, 0], ![-1, 0, 1, 0], ![-1, 0, 1, 0], ![-1, 0, 1, 0]]

def extraRaw136step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, -2, -1, 1]]

end MUB6.Certificate.PairTargetSemantics

end OAI
end


