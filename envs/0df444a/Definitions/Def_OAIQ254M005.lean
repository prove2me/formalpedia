-- Prove2me | Definitions.Def_OAIQ254M005
-- name    : OAIQ254M005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T05:49:44.016886+00:00
-- url     : https://prove2.me/theorems/a96d4ac9-dcd3-43c7-a4b5-2b80eae9a50d
-- title:
--   Definitions bundle OAIQ254M005 of the split of OpenAI, Staggered extraction for exact matrix multiplication over every field
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant`, carved from OpenAI's openai/math development (OpenAI, *Staggered extraction for exact matrix multiplication over every field*, OpenAI Math Release, September 24, 2026, result family 107, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3851 declarations of OpenAI's Lean: 3850 definitions and 1 theorem. The definitions and types are `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I2S2_0_2Entropy`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I2S2_0_2H`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I2S2_0_2MassTermLog`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I2S2_0_2Terms`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I2S2_0_2Value`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I2S3_0_1E_1`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I2S3_0_1E_1Log`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I2S3_0_1Entropy`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I2S3_0_1H`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I2S3_0_1Mass`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I2S3_0_1MassTerm`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I2S3_0_1MassTermLog`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I2S3_0_1Terms`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I2S3_0_1Value`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I2Singleton`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I0Entropy`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I0H`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I0Mass`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I0MassTerm`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I0MassTermLog`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I0MassTermLogWitness`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I0Value`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I1Group`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I1H`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I1PairEntropy`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I1PairH`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I1PairMass`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I1PairMassTerm`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I1PairMassTermLog`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I1PairMassTermLogWitness`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I1R0Entropy`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I1R0H`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I1R0Mass`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I1R0MassTerm`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I1R0MassTermLog`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I1R0MassTermLogWitness`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I1R0Value`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I1R10Entropy`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I1R10H`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I1R10Mass` and 3810 more.
--
--   **Sources.** They come from these modules of lean/OAI/LinearAlgebra, in whole or in part: `MatrixFields_CapacityB_CapB3_2_3I2`, `MatrixFields_CapacityB_CapB3_3_2I0`, `MatrixFields_CapacityB_CapB3_3_2I1`, `MatrixFields_CapacityB_CapB3_3_2I2`, `MatrixFields_CapacityB_CapB3_4_1I0`, `MatrixFields_CapacityB_CapB3_4_1I1`, `MatrixFields_CapacityB_CapB3_4_1I2`, `MatrixFields_CapacityB_CapB4_1_3I0`, `MatrixFields_CapacityB_CapB4_1_3I1`, `MatrixFields_CapacityB_CapB4_1_3I2`, `MatrixFields_CapacityB_CapB4_2_2I0`, `MatrixFields_CapacityB_CapB4_2_2I1`, `MatrixFields_CapacityB_CapB4_2_2I2`, `MatrixFields_CapacityB_CapB4_3_1I0`, `MatrixFields_CapacityB_CapB4_3_1I1`, `MatrixFields_CapacityB_CapB4_3_1I2`, `MatrixFields_CapacityB_CapB5_1_2I0`, `MatrixFields_CapacityB_CapB5_1_2I1`, `MatrixFields_CapacityB_CapB5_1_2I2`, `MatrixFields_CapacityB_CapB5_2_1I0`, `MatrixFields_CapacityB_CapB5_2_1I1`, `MatrixFields_CapacityB_CapB5_2_1I2`, `MatrixFields_CapacityB_CapB6_1_1I0`, `MatrixFields_CapacityB_CapB6_1_1I1`, `MatrixFields_CapacityB_CapB6_1_1I2`, `MatrixFields_Certificates_Four0_1_7`, `MatrixFields_Certificates_Four0_3_5`, `MatrixFields_Certificates_Four0_4_4`, `MatrixFields_Certificates_Four0_5_3`, `MatrixFields_Certificates_Four0_7_1`, `MatrixFields_Certificates_Four0_8_0`, `MatrixFields_Certificates_Four1_0_7`, `MatrixFields_Certificates_Four1_7_0`, `MatrixFields_Certificates_Four2_0_6`, `MatrixFields_Certificates_Four2_6_0`, `MatrixFields_Certificates_Four3_0_5`, `MatrixFields_Certificates_Four3_5_0`, `MatrixFields_Certificates_Four4_0_4`, `MatrixFields_Certificates_Four4_4_0`, `MatrixFields_Certificates_Four5_0_3`, `MatrixFields_Certificates_Four5_3_0`, `MatrixFields_Certificates_Four6_0_2`, `MatrixFields_Certificates_Four6_2_0`, `MatrixFields_Certificates_Four7_0_1`, `MatrixFields_Certificates_Four7_1_0`, `MatrixFields_Certificates_Four8_0_0`, `MatrixFields_Certificates_InitialProbabilities`, `MatrixFields_Certificates_NativeInterior`, `MatrixFields_Certificates_NativeSharp`, `MatrixFields_Certificates_SparseContraction`, `MatrixFields_Certificates_SplitA1_3_12`, `MatrixFields_Certificates_SplitB1_1_6`, `MatrixFields_Certificates_SplitB1_3_4`, `MatrixFields_Certificates_SplitB5_1_2`, `MatrixFields_Certificates_Terminal1_1_6`, `MatrixFields_Certificates_Weights2`, `MatrixFields_Certificates_Zero0_1_7`.
--
--   **Imports.** It imports the bundles `OAIQ254M000` and `OAIQ254M001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ254M010` and `OAIQ254M011`; the statements `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I0_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_4_1I0_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_4_1I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_4_1I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_1_3I0_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_1_3I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_1_3I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_2_2I0_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_2_2I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_2_2I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_3_1I0_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_3_1I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_3_1I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB5_1_2I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB5_1_2I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB5_2_1I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB5_2_1I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB6_1_1I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB6_1_1I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z0_5_3Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z0_7_1Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z0_8_0Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z1_0_7Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z1_7_0Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z2_0_6Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z2_6_0Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z3_0_5Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z3_5_0Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z4_0_4Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z4_4_0Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z5_0_3Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z5_3_0Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z6_0_2Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z6_2_0Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z7_0_1Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z8_0_0Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.fourRateBalls_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_0_0_16`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_0_1_15`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_0_2_14`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_0_3_13`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_0_4_12`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_0_5_11`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_0_6_10`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_1_1_14`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_1_2_13`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_1_3_12`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_1_4_11`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_1_5_10`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.nativeBBall_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.nativeLBBall_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.nativeS1Ball_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.nativeS2Ball_sound` and `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.nativeTBall_sound`; the proofs of `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A1_4_11Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A1_6_9Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A1_7_8Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A2_2_12Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A2_3_11Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A2_4_10Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A2_5_9Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A2_6_8Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A2_7_7Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A3_3_10Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A3_5_8Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A3_6_7Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A4_4_8Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A4_5_7Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A4_6_6Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A5_5_6Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.AProbsTable_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_1_6Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_1_6S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_1_6U0_0_4Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_1_6U0_1_3Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_1_6U1_0_3Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_1_6U1_1_2Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_2_5Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_3_4Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_3_4Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_3_4Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_3_4S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_3_4U0_0_4Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_4_3Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_4_3Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_4_3Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_4_3S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_4_3U0_1_3Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_4_3U0_4_0Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_4_3U1_0_3Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_4_3U1_3_0Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_5_2Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_5_2Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_5_2S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_5_2U0_2_2Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_5_2U0_3_1Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_5_2U0_4_0Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_5_2U1_1_2Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_6_1Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_1_5Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_2_4Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_3_3Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_3_3Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2U1_1_2Leaf_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2U1_2_1Leaf_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2U2_1_1Leaf_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_5_1Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_5_1S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_5_1Ttotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_1_4Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_2_3Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2U1_1_2Leaf_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2U1_2_1Leaf_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2U2_1_1Leaf_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_4_1Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B4_1_3Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B4_2_2Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B4_3_1Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B5_1_2Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B5_1_2S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B5_2_1Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B6_1_1Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B6_1_1S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_4_9I0_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_0_0_16`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_0_1_15`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_0_2_14`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_0_3_13`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_0_4_12`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_0_5_11`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_0_6_10`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_1_1_14`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_1_2_13`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_1_3_12`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_1_4_11`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_1_5_10`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.nativeBBall_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.nativeS1Ball_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.nativeS2Ball_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.native_denominator_gap` and `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.native_volume_positive`.
-- source:
--   OpenAI, Staggered extraction for exact matrix multiplication over every field, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 107; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/LinearAlgebra at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ254M000
import Definitions.Def_OAIQ254M001

section
-- module Solutions.OAIQ254_MF.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
@[simp] theorem fin3_lit_1_0 : ((1 : Fin 3) = 0) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SparseContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def logN1 : Ball := .exact 0
def logN2Witness : LogWitness := ⟨1, 1, 1⟩
def logN2 : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
def logN4Witness : LogWitness := ⟨2, 1, 1⟩
def logN4 : Ball := ⟨(6931471805599453094172319305033 / 5000000000000000000000000000000), (7940933881 / 12500000000000000000000000000000)⟩
def logN5Witness : LogWitness := ⟨2, 5, 4⟩
def logN5 : Ball := ⟨(40235947810852509365018973782911 / 25000000000000000000000000000000), (63527471049 / 100000000000000000000000000000000)⟩
def logN7Witness : LogWitness := ⟨2, 7, 4⟩
def logN7 : Ball := ⟨(194591014905531330510535236152357 / 100000000000000000000000000000000), (7940933881 / 12500000000000000000000000000000)⟩
def logN10Witness : LogWitness := ⟨3, 5, 4⟩
def logN10 : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def logN20Witness : LogWitness := ⟨4, 5, 4⟩
def logN20 : Ball := ⟨(18723326709712443708970142577019 / 6250000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
def logN25Witness : LogWitness := ⟨4, 25, 16⟩
def logN25 : Ball := ⟨(321887582486820074920151790263287 / 100000000000000000000000000000000), (52939559207 / 50000000000000000000000000000000)⟩
def logN50Witness : LogWitness := ⟨5, 25, 16⟩
def logN50 : Ball := ⟨(391202300542814605861874983313617 / 100000000000000000000000000000000), (127054942097 / 100000000000000000000000000000000)⟩
def logN100Witness : LogWitness := ⟨6, 25, 16⟩
def logN100 : Ball := ⟨(460517018598809136803598176363947 / 100000000000000000000000000000000), (7411538289 / 5000000000000000000000000000000)⟩
def logN250Witness : LogWitness := ⟨7, 125, 64⟩
def logN250 : Ball := ⟨(552146091786224643321950874544283 / 100000000000000000000000000000000), (21175823683 / 12500000000000000000000000000000)⟩
def logN625Witness : LogWitness := ⟨9, 625, 512⟩
def logN625 : Ball := ⟨(321887582486820074920151780715543 / 50000000000000000000000000000000), (211758236829 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Weights2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
def w50S5 : Ball := ⟨(2686314516477279869329472877877 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
abbrev w50 : Ball := w50S5
def w54S5 : Ball := ⟨(1559902010377734702891454847933 / 50000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
abbrev w54 : Ball := w54S5

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Zero0_1_7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
def w175Trace : List Ball := [
  ⟨(12415191351984113932732906117773 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(99660380500651059079072911866491 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49886729305329857561013634483801 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8319169679698320054082388153217 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4160999920316042561673130720447 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(416194361303583566199564560551 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(69376964051683336916536129013 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19824398148776138563838364003 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2478283955926034391062597277 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(275385703219024858214213941 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27540273888866403321074269 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(15648689574925252681249 / 625000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208658296057867120366611 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16051238310965442348689 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(573277088357842603873 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76439099532671271263 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w175S0 : Ball := ⟨(19729532967216784739084393457349 / 20000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w175S1 : Ball := ⟨(48656808888061743300257882980879 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w175S2 : Ball := ⟨(94699402046774570418621129554693 / 100000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
def w175S3 : Ball := ⟨(17935953496033303394176963409269 / 20000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩
def w175S4 : Ball := ⟨(80424606952967319568608763730587 / 100000000000000000000000000000000), (11 / 25000000000000000000000000000000)⟩
def w175S5 : Ball := ⟨(3234058701769639661254805874069 / 5000000000000000000000000000000), (71 / 100000000000000000000000000000000)⟩
abbrev w175 : Ball := w175S5

def w176Trace : List Ball := [
  ⟨(99323703498123134155078443956379 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49830734653602825322334315901173 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49887092652172136175932683973821 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8319215128923882961441659769091 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4161018108242338480622187941589 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(166478350981811608034371819 / 20000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(69377180697235508098493268879 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(309757067506038894548356277 / 1562500000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2478289975902669122205754733 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(137693152645528825192097429 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27540328628322341810300231 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1251897447003368529189103 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(52164661752146226184849 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16051263380496070396237 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(143319481013938810139 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76439204083737917237 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w176S0 : Ball := ⟨(98651980765830777166229913989293 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w176S1 : Ball := ⟨(48661066545109228056357597777893 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w176S2 : Ball := ⟨(94715975892301941778520323293643 / 100000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
def w176S3 : Ball := ⟨(89711160892311226160943282578631 / 100000000000000000000000000000000), (1 / 4000000000000000000000000000000)⟩
def w176S4 : Ball := ⟨(20120230971615377890151153703799 / 25000000000000000000000000000000), (23 / 50000000000000000000000000000000)⟩
def w176S5 : Ball := ⟨(506029617938938366762443058991 / 781250000000000000000000000000), (3 / 4000000000000000000000000000000)⟩
abbrev w176 : Ball := w176S5

def w177Trace : List Ball := [
  ⟨(99328049005208451402499580583609 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(99663646967923778076539612164563 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49887819357771038473846631443669 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8319306028567251070469974050063 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4161054484492536840115847644457 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(832397819569661411940712448203 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138755227983784401223028153737 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9912280332198390052244553533 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(619575503983728031598156193 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(34423438680287969177918121 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(6885109526958168332912129 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(156487751130635651530041 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208659348913309370965269 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3210262703955320934979 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(573279595458441677671 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(15287882637174241837 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w177S0 : Ball := ⟨(19732122638362183264540644182777 / 20000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w177S1 : Ball := ⟨(97339165953841342057706388054317 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w177S2 : Ball := ⟨(11843641535736831833207936343991 / 12500000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w177S3 : Ball := ⟨(44886990344649824138792427360347 / 50000000000000000000000000000000), (27 / 100000000000000000000000000000000)⟩
def w177S4 : Ball := ⟨(10074209511003432690114849384499 / 12500000000000000000000000000000), (49 / 100000000000000000000000000000000)⟩
def w177S5 : Ball := ⟨(32476703126909447167938135835733 / 50000000000000000000000000000000), (1 / 1250000000000000000000000000000)⟩
abbrev w177 : Ball := w177S5

def w178Trace : List Ball := [
  ⟨(99347916601702917217757537125577 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(99673602796783611329156016152539 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49891141642820336599032639688333 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16639443180077520090544685805351 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(260076298917091723161985778033 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(416212772348629267725376117597 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13875918965556977426603840671 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4956263991177057476970897693 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1239178528711639796144567009 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(275393014255639484656273141 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(5508187719151182056462029 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(500769145793524574071731 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208662557676466341962129 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3210308546327901178969 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(71660904534117072343 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(38220184540668843331 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w178S0 : Ball := ⟨(9870008533098918115455859601797 / 10000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w178S1 : Ball := ⟨(48708534221722728688122505851369 / 50000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w178S2 : Ball := ⟨(14828258162679588668233433511 / 15625000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w178S3 : Ball := ⟨(281442867378014528867241064857 / 312500000000000000000000000000), (27 / 100000000000000000000000000000000)⟩
def w178S4 : Ball := ⟨(81111129700309682879484067206857 / 100000000000000000000000000000000), (49 / 100000000000000000000000000000000)⟩
def w178S5 : Ball := ⟨(16447538403151148866018747980209 / 25000000000000000000000000000000), (1 / 1250000000000000000000000000000)⟩
abbrev w178 : Ball := w178S5

def w179Trace : List Ball := [
  ⟨(24855691545850327472253337341129 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49855552310818039275500189839387 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3118978443874995400805617503113 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3328514694739384385990648751571 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2080923549343674965801708723317 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(416264980669731503438529125617 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(17346763700303945074765605393 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19826921277379245907959318893 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(619641085693726828910162409 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(17213359069612341047331649 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1101712935809207575608713 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2504002808002377300209539 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208674641497578804110739 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16052405912388349816829 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1146632020860853128433 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76443968625203640911 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w179S0 : Ball := ⟨(1976977287111857413602752175699 / 2000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w179S1 : Ball := ⟨(19542195968780797505814619325357 / 20000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w179S2 : Ball := ⟨(19094871164111622638225973270799 / 20000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w179S3 : Ball := ⟨(22788381548376347167989621366387 / 25000000000000000000000000000000), (7 / 25000000000000000000000000000000)⟩
def w179S4 : Ball := ⟨(41544826687550364961716409983473 / 50000000000000000000000000000000), (13 / 25000000000000000000000000000000)⟩
def w179S5 : Ball := ⟨(69038904979943881194700567488221 / 100000000000000000000000000000000), (87 / 100000000000000000000000000000000)⟩
abbrev w179 : Ball := w179S5

def w180Trace : List Ball := [
  ⟨(24860080516341290896503129229441 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(99719899266785998037858901066621 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49906589436793222653202482562019 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(665732299023802917042440537947 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(832398790969932850090092400599 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(832554444009339192196822035087 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138777607838599757062146680857 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9913679313062968974806951597 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2478612943234444583940605351 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(34427325707919260346400427 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(344290816269095221313533 / 1250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2504039636217897100165593 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8347098984586386384801 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(401315207221960677399 / 2500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1146645513262806847721 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76444812501670140559 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w180S0 : Ball := ⟨(2472094413115887458356030841823 / 2500000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w180S1 : Ball := ⟨(9778001259774054473105372673371 / 10000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w180S2 : Ball := ⟨(47804654318071498153358495803553 / 50000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
def w180S3 : Ball := ⟨(45705699489406238682707231944411 / 50000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩
def w180S4 : Ball := ⟨(16712087726527277659411303666431 / 20000000000000000000000000000000), (9 / 20000000000000000000000000000000)⟩
def w180S5 : Ball := ⟨(69823469044785918019090333627239 / 100000000000000000000000000000000), (19 / 25000000000000000000000000000000)⟩
abbrev w180 : Ball := w180S5

def w181Trace : List Ball := [
  ⟨(9944249734620239086398353308017 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(99720988940880337353420578169773 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49906953000722217387040237938873 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16643398417490461792690810263043 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208100607500993842154109814411 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(416278738673209487711157379259 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138778041259136127180516456603 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1239213300757537265203267591 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1239309482324876609412041193 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(275419207866193834513376221 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27543320051885435384589649 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2504044199075285494496699 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(104338912812644651404107 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4013158340600871274999 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(286661796227143628697 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76444917052736786533 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w181S0 : Ball := ⟨(24722025696123673874062788081717 / 25000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w181S1 : Ball := ⟨(19557713744633575097632752799179 / 20000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w181S2 : Ball := ⟨(47813020864628632290757234996807 / 50000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w181S3 : Ball := ⟨(45721699284028258483278295221591 / 50000000000000000000000000000000), (27 / 100000000000000000000000000000000)⟩
def w181S4 : Ball := ⟨(10452368927095550822026725558767 / 12500000000000000000000000000000), (1 / 2000000000000000000000000000000)⟩
def w181S5 : Ball := ⟨(34960645180196030788867851759237 / 50000000000000000000000000000000), (21 / 25000000000000000000000000000000)⟩
abbrev w181 : Ball := w181S5

def w182Trace : List Ball := [
  ⟨(49725987955468187868242445671101 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9972573699195892199308204179439 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49908537147082719484644086320787 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(520118583550074013965957800471 / 3125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(65032678601928404196807084431 / 1562500000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(832570694250563197454787709119 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138779929761980938944896075307 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19827648911313040703838695657 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1239322600561893978056223769 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(275421831777938491707467463 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27543558609344749385176713 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2504064080275920137500161 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208679355041544954003991 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3210548522437469683851 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1146654468561374833113 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(38222686298335014853 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w182S0 : Ball := ⟨(12363369390736836453095105804009 / 12500000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w182S1 : Ball := ⟨(97825857722757462143876692269313 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w182S2 : Ball := ⟨(9569898439193185797117938531799 / 10000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w182S3 : Ball := ⟨(9158295613647217363758918206093 / 10000000000000000000000000000000), (7 / 25000000000000000000000000000000)⟩
def w182S4 : Ball := ⟨(41937189273474930827880170954463 / 50000000000000000000000000000000), (13 / 25000000000000000000000000000000)⟩
def w182S5 : Ball := ⟨(17587278441592607965700121886531 / 25000000000000000000000000000000), (11 / 12500000000000000000000000000000)⟩
abbrev w182 : Ball := w182S5

def w183Trace : List Ball := [
  ⟨(99458191853676996485506081143019 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19945770126357333866902966262183 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49909575972542889246622939607217 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16644054521872557423445111124777 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16648573676422106024498759631 / 400000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(416289680634124640043877726033 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(69390584074459890303400059103 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19827803733169197738514016953 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1239331202820227214472511967 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(275423552400479454266974319 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(6885928760630532463566227 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(313009639660875428068141 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(52170089487187941792693 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8026407126071682147023 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1146659244774286862811 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76445671314003303917 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w183S0 : Ball := ⟨(3956772770721128506515199771393 / 4000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w183S1 : Ball := ⟨(24462579311125244026594135025039 / 25000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w183S2 : Ball := ⟨(95746845848494850974174676572979 / 100000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
def w183S3 : Ball := ⟨(2864830778104823649683848641001 / 3125000000000000000000000000000), (29 / 100000000000000000000000000000000)⟩
def w183S4 : Ball := ⟨(84042295164689298634384866406393 / 100000000000000000000000000000000), (27 / 50000000000000000000000000000000)⟩
def w183S5 : Ball := ⟨(70631073765487582654707052568089 / 100000000000000000000000000000000), (23 / 25000000000000000000000000000000)⟩
abbrev w183 : Ball := w183S5

def w184Trace : List Ball := [
  ⟨(99490365565416636332292790703719 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(99744965790016130682756559516713 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4991495241274506514856327501649 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(130042182346995185683065724021 / 781250000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2081206238657653747694580254813 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(416312107778267525627513838843 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(69393788555183567295966301847 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3965720994123715599512081027 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1239375721224540406690124201 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(275432456934428447688871593 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13772262305121354050309369 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(62603614645541538537401 / 2500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208685548136579524730717 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16053184998451877457383 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(143335495284089101149 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(38223608588101498981 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w184S0 : Ball := ⟨(791866627227219229699209176743 / 800000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w184S1 : Ball := ⟨(97976993018158090480395401414837 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w184S2 : Ball := ⟨(5999681975550124505069906258251 / 6250000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w184S3 : Ball := ⟨(9215023054781707463539215963191 / 10000000000000000000000000000000), (27 / 100000000000000000000000000000000)⟩
def w184S4 : Ball := ⟨(84916649900158391512606545626333 / 100000000000000000000000000000000), (51 / 100000000000000000000000000000000)⟩
def w184S5 : Ball := ⟨(72108374302660701632463080306707 / 100000000000000000000000000000000), (11 / 12500000000000000000000000000000)⟩
abbrev w184 : Ball := w184S5

def w185Trace : List Ball := [
  ⟨(99521461163089908858700716103647 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(6235033705668939951782200603949 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49920147866467392101063783570821 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16646698847188617367810591099223 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2081336232239666330274977714023 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(416333778484326370471529758463 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(867461061473084547588034407 / 625000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19829379167762611033930166791 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2478837473819984033585000739 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(68860265211524437532664059 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27545306842716642588551163 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(250420977599959640519217 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(104345281519267472369117 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8026771611314142422567 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1146707844863531832381 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3822435538143468451 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w185S0 : Ball := ⟨(99045212320364130345477940283017 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w185S1 : Ball := ⟨(98099540835860105171601676853239 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w185S2 : Ball := ⟨(48117599561032921710168032712719 / 50000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
def w185S3 : Ball := ⟨(92612135500636624802178339361061 / 100000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩
def w185S4 : Ball := ⟨(85770076419882786148844074112819 / 100000000000000000000000000000000), (9 / 20000000000000000000000000000000)⟩
def w185S5 : Ball := ⟨(36782530045362665672288806008641 / 50000000000000000000000000000000), (39 / 50000000000000000000000000000000)⟩
abbrev w185 : Ball := w185S5

def w186Trace : List Ball := [
  ⟨(99568900662470816514208552130991 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3991371804971825401902736147063 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(24964036247883104802210062747163 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(26013563918188208166319893553 / 156250000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4163068997025895747572610255911 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(41636683003497074506258641661 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138803214672976366445830044263 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9915279960942922885652904213 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2478968682009807979274974929 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(17215886422020679279331659 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27546499825657994940562287 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1252154598526809344813827 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(104349105597475631398959 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8027044771613974010277 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(573372133805897008433 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76450988482535584883 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w186S0 : Ball := ⟨(9913965979132981403710742545553 / 10000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w186S1 : Ball := ⟨(98286721435406174665473615960613 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w186S2 : Ball := ⟨(12075349513151414514529855232981 / 12500000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
def w186S3 : Ball := ⟨(93321002153450306264064872946103 / 100000000000000000000000000000000), (3 / 10000000000000000000000000000000)⟩
def w186S4 : Ball := ⟨(43544047214621383495429087826007 / 50000000000000000000000000000000), (57 / 100000000000000000000000000000000)⟩
def w186S5 : Ball := ⟨(1185052529893235166451447015261 / 1562500000000000000000000000000), (1 / 1000000000000000000000000000000)⟩
abbrev w186 : Ball := w186S5

def w187Trace : List Ball := [
  ⟨(99602355209040861197807880258721 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(99801045574058366040375150752489 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49933659844174797709766085649909 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(666003132990266129407140142087 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1332271538498333634814041509 / 32000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208195065686215395939573398707 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138809873185066560009973585573 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19831392331878620590507498949 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2479061180541660695534655279 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(275463433303708409851846541 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13773670418885857095109159 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(78261852660207547756871 / 3125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208703602831146487300669 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16054474675326115496511 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(229353988793680458361 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76452594088201933771 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w187S0 : Ball := ⟨(6200393226992468235473533170609 / 6250000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w187S1 : Ball := ⟨(98418882993495228737242954611417 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w187S2 : Ball := ⟨(19372553059374608712680432468263 / 20000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w187S3 : Ball := ⟨(1876479060191422559033355299463 / 2000000000000000000000000000000), (7 / 25000000000000000000000000000000)⟩
def w187S4 : Ball := ⟨(88029341583422111182801317951789 / 100000000000000000000000000000000), (53 / 100000000000000000000000000000000)⟩
def w187S5 : Ball := ⟨(77491649796108092848828209234519 / 100000000000000000000000000000000), (47 / 50000000000000000000000000000000)⟩
abbrev w187 : Ball := w187S5

def w188Trace : List Ball := [
  ⟨(49802344833298945363222839682779 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(99802214350039422120222960963773 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(998680993883785744041853910733 / 2000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8325087912989386718081825748297 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4163368063215647937644855560767 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(832783514261138687952310759689 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(69405168876641626006794306193 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9915725204656331398851471713 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2479067634159456476737241001 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(137732039356046642104013173 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2754739951479222218145243 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(313048021890918220272639 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4174079580029300255807 / 2000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16054501545650998469549 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1146771735382375976313 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(191131765268004779 / 250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w188S0 : Ball := ⟨(99210942035792726320799598581467 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w188S1 : Ball := ⟨(98428110196294241913505639944541 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w188S2 : Ball := ⟨(24220232192034606273474291591403 / 25000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
def w188S3 : Ball := ⟨(11732392948721389376433911667343 / 12500000000000000000000000000000), (3 / 10000000000000000000000000000000)⟩
def w188S4 : Ball := ⟨(88095388354052721900922296256263 / 100000000000000000000000000000000), (57 / 100000000000000000000000000000000)⟩
def w188S5 : Ball := ⟨(77607974492513679419890243785447 / 100000000000000000000000000000000), (101 / 100000000000000000000000000000000)⟩
abbrev w188 : Ball := w188S5

def w189Trace : List Ball := [
  ⟨(99660888785280590661143702258429 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(99830348399458131034052693010717 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49943433462187736065444559862473 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(416313065775631533066716743527 / 2500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4163837539328160146604430715531 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(166572354797072018383717454197 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138821519182554970302428658273 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3966569646155280159571995787 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(247922296035046093285472851 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2754796123699652991146921 / 1000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27548811744208253433256087 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1252250933230869446363469 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(104356516273484419984907 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1605514825012690260507 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1146814850329197960663 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(238923131347295973 / 312500000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w189S0 : Ball := ⟨(124153659418400832569672287431 / 125000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w189S1 : Ball := ⟨(19730087868134745292034087073167 / 20000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w189S2 : Ball := ⟨(19463818364215892916364093655161 / 20000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
def w189S3 : Ball := ⟨(94710056328796959379104133535603 / 100000000000000000000000000000000), (3 / 10000000000000000000000000000000)⟩
def w189S4 : Ball := ⟨(89699947698038929789567959309211 / 100000000000000000000000000000000), (29 / 50000000000000000000000000000000)⟩
def w189S5 : Ball := ⟨(40230403085154597496901408538171 / 50000000000000000000000000000000), (21 / 20000000000000000000000000000000)⟩
abbrev w189 : Ball := w189S5

def w191Trace : List Ball := [
  ⟨(49881858544285669090431918402831 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49940905982279908932346249793997 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49960596223062461424570847875897 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4164203639369994761337080486481 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2082348044742429869134947581029 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(416502442654040348062669402193 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138841965760692082639695195677 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1983540425756671035928907259 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2479506981508443033953924069 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(275508015973421305673833101 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27551394002684640101491511 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2504717062615820794000957 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(10436479331066494145389 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16056330716452051496157 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1146893683302764908141 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76460330867133735851 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w191S0 : Ball := ⟨(49763996236642504205094356041887 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w191S1 : Ball := ⟨(99058212857622772855370888953607 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w191S2 : Ball := ⟨(1533207739772828380404245348957 / 1562500000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w191S3 : Ball := ⟨(96285735866339533992202794619269 / 100000000000000000000000000000000), (7 / 25000000000000000000000000000000)⟩
def w191S4 : Ball := ⟨(46354714656612516652688244278839 / 50000000000000000000000000000000), (11 / 20000000000000000000000000000000)⟩
def w191S5 : Ball := ⟨(85950382835838690706047952575689 / 100000000000000000000000000000000), (103 / 100000000000000000000000000000000)⟩
abbrev w191 : Ball := w191S5

def w192Trace : List Ball := [
  ⟨(49987032931739362099937440160927 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(24996758092795951927826195803241 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3124729835227057516919707719423 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2083198249195050257675416497151 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(416645053017679137671205574393 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(833297310362563680427653924047 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(69441871363186324201270914239 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1984062656863801965131724839 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2480087255215878646829690667 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(68891511182180145029458271 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(5511333889793856570685729 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1252578345268046513107889 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(104381702320677184448087 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16058746319502249357223 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(35845460164487008383 / 3125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76470397641265076781 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w192S0 : Ball := ⟨(99948138452751819441462357001721 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w192S1 : Ball := ⟨(99896303801704468635569351663811 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w192S2 : Ball := ⟨(49896357566212173366378600464419 / 50000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
def w192S3 : Ball := ⟨(155602906148456175041603885009 / 156250000000000000000000000000), (31 / 100000000000000000000000000000000)⟩
def w192S4 : Ball := ⟨(99173434989958187099241294743813 / 100000000000000000000000000000000), (63 / 100000000000000000000000000000000)⟩
def w192S5 : Ball := ⟨(49176851038537314210548640967583 / 50000000000000000000000000000000), (63 / 50000000000000000000000000000000)⟩
abbrev w192 : Ball := w192S5

def w193Trace : List Ball := [
  ⟨(24995234829194772061239991990961 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(99990469355602649390331992949819 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49996823068068772028889443570563 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16665872426113946809476351144877 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4166507817546791818048638896097 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(416653429179930801384316249029 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138885106736947224660119474937 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(620024908469545699903926497 / 3125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(620026550005079233602540067 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(55113587843382893113140779 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27556841675755855052048577 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2505171042809707586844313 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208764508665131335857699 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16058825178512442762287 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1147059982540784814409 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(38235363115165839207 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w193S0 : Ball := ⟨(49980941133327312484694549890891 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w193S1 : Ball := ⟨(9992377906292520382993342626511 / 10000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w193S2 : Ball := ⟨(4992380811108144663012011909347 / 5000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
def w193S3 : Ball := ⟨(99695464652483265607512618822371 / 100000000000000000000000000000000), (31 / 100000000000000000000000000000000)⟩
def w193S4 : Ball := ⟨(99391856722745402596868367365467 / 100000000000000000000000000000000), (63 / 100000000000000000000000000000000)⟩
def w193S5 : Ball := ⟨(19757482365589500963001701230393 / 20000000000000000000000000000000), (63 / 50000000000000000000000000000000)⟩
abbrev w193 : Ball := w193S5

def w194Trace : List Ball := [
  ⟨(12498984416258648195712197534271 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(99995937610023806799012010244939 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4999864586083939677525852383333 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8333164065250613793699487200691 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4166598959250206371597111195457 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208330512185523290939911413439 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27777455360417412154288189239 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3968213666038442948782014569 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1240068170009390345827669767 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(17223184576513134476304453 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27557115676983442485468489 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2505193876285133400992783 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208766265088941691417 / 100000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16058950637518462775011 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1147068346483992386111 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19117812246416227071 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w194S0 : Ball := ⟨(9998375132024098597819740729157 / 10000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w194S1 : Ball := ⟨(99967505280677911066314510992599 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w194S2 : Ball := ⟨(99935021120423660346027921790003 / 100000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
def w194S3 : Ball := ⟨(99870084463395230656561932324761 / 100000000000000000000000000000000), (31 / 100000000000000000000000000000000)⟩
def w194S4 : Ball := ⟨(49870168853628487182377852301003 / 50000000000000000000000000000000), (63 / 100000000000000000000000000000000)⟩
def w194S5 : Ball := ⟨(49740674829788337188473087934709 / 50000000000000000000000000000000), (127 / 100000000000000000000000000000000)⟩
abbrev w194 : Ball := w194S5

def w195 : Ball := .exact 1

def w196Trace : List Ball := [
  ⟨(800021250282229061397616355361 / 800000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4000053125470380727784538541189 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(50000442711273208977450530824507 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16666777344337974608219275549919 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2083344401090664519696625934459 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(166667404516688764876816954333 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27777883184873793893182729747 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2480166965085068351811042641 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1240083025045546297812448833 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(137786962116459195085845847 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(6889346442199022291779133 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2505216383944077523314819 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(104383998223921122037141 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16059074306043564476871 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1147076591054210974669 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76471764273064806299 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w196S0 : Ball := ⟨(4000212505644631206568430064813 / 4000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w196S1 : Ball := ⟨(25002656391118279144800146186637 / 25000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w196S2 : Ball := ⟨(3125664133061638652561663844491 / 3125000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
def w196S3 : Ball := ⟨(800340072260236504272132654903 / 800000000000000000000000000000), (31 / 100000000000000000000000000000000)⟩
def w196S4 : Ball := ⟨(100085036135237592062515148655159 / 100000000000000000000000000000000), (63 / 100000000000000000000000000000000)⟩
def w196S5 : Ball := ⟨(100170144581918145585494921142611 / 100000000000000000000000000000000), (127 / 100000000000000000000000000000000)⟩
abbrev w196 : Ball := w196S5

def w197Trace : List Ball := [
  ⟨(25003672144666522574407293810279 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(25001836027387740645404665729023 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(625030600081921839886205624879 / 1250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3333455732762132284527646393759 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(260424316593513179389490267511 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(166670746613383578114197118947 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(69445901564450170731102645181 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1240102132533009921872967449 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1240099602782911067946697043 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(275577239775163664581143607 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27557687181331442181544571 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2505241501627431402564057 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(41753985715097952471767 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8029606157523631435577 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(71692861977987983519 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19118084825982839789 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w197S0 : Ball := ⟨(10002937931487561289448862263219 / 10000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w197S1 : Ball := ⟨(20011753452238530278613660969213 / 20000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w197S2 : Ball := ⟨(100117569058295183639240950010957 / 100000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
def w197S3 : Ball := ⟨(100235276341425051441370822762279 / 100000000000000000000000000000000), (31 / 100000000000000000000000000000000)⟩
def w197S4 : Ball := ⟨(100471106232418446456510702275909 / 100000000000000000000000000000000), (63 / 100000000000000000000000000000000)⟩
def w197S5 : Ball := ⟨(4037777275026365117837262628101 / 4000000000000000000000000000000), (127 / 100000000000000000000000000000000)⟩
abbrev w197 : Ball := w197S5

def w198Trace : List Ball := [
  ⟨(100046104374801339061281256367671 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(25005762604116101033901758736749 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(100015366354024723989846549679 / 200000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1041786713540609481122012135647 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4167050810760745839788482570801 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(833397356646341688007385241263 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(34724508750294060502729724659 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19842413097986434234597417511 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2480285758032194725201724413 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(55117178994794943594601333 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(6889618503490954540188779 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2505307070757983886745053 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(104387486168959175421941 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8029786291374700237201 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1147109809433762731797 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76473840358531062069 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w198S0 : Ball := ⟨(100092230005736436346044576577509 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w198S1 : Ball := ⟨(20036909015042490824580426800099 / 20000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w198S2 : Ball := ⟨(100369430719272759949295620039269 / 100000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
def w198S3 : Ball := ⟨(100740226229108943786285637747531 / 100000000000000000000000000000000), (31 / 100000000000000000000000000000000)⟩
def w198S4 : Ball := ⟨(50742965903460248018971649086741 / 50000000000000000000000000000000), (63 / 100000000000000000000000000000000)⟩
def w198S5 : Ball := ⟨(102993943547189172179056608068133 / 100000000000000000000000000000000), (1 / 781250000000000000000000000000)⟩
abbrev w198 : Ball := w198S5

end MatrixMultiplication.NativeNumerics

namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def Z0_0_8Den : Ball := ⟨1, 0⟩
def Z0_0_8E_5_5Log : Ball := .exact 0
def Z0_0_8E_5_5 : Ball := ⟨0, 0⟩
def Z0_0_8Entropy : Ball := ⟨0, 0⟩
def Z0_0_8Labels : Ball := ⟨0, 0⟩
def Z0_0_8Four : Ball := ⟨0, 0⟩
def Z0_0_8H2E_5_5Log : Ball := .exact 0
def Z0_0_8H2E_5_5 : Ball := ⟨0, 0⟩
def Z0_0_8H2Entropy : Ball := ⟨0, 0⟩
def Z0_0_8H2Mass : Ball := ⟨1, 0⟩
def Z0_0_8H2MassTermLog : Ball := .exact 0
def Z0_0_8H2MassTerm : Ball := ⟨0, 0⟩
def Z0_1_7Den : Ball := ⟨2, 0⟩

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitB5_1_2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
def w150Trace : List Ball := [
  ⟨(98959204157366003351153005275457 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9947869463646324003316556506979 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(12456520036720668263666306576111 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(26597062364417979692773038269 / 160000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2078981548646564333740394195517 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(831882377399091917407720490597 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27736314155152514707055536169 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19815351314343164024966121289 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2477278559300095089619933339 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(137642573889370088899660261 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2753113128972317574696971 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(625757091104298819297701 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(52149919402069302614269 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4011762733662588650543 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1146274998447789459539 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3821081601830403087 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w150S0 : Ball := ⟨(97929240874592448813469267792491 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w150S1 : Ball := ⟨(95901362182739484089958458380911 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w150S2 : Ball := ⟨(18394142537009949728404824819527 / 20000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
def w150S3 : Ball := ⟨(84586119917959707453491417433721 / 100000000000000000000000000000000), (23 / 100000000000000000000000000000000)⟩
def w150S4 : Ball := ⟨(71548116827754599463824485091543 / 100000000000000000000000000000000), (1 / 2500000000000000000000000000000)⟩
def w150S5 : Ball := ⟨(10238266043196041778240362118913 / 20000000000000000000000000000000), (29 / 50000000000000000000000000000000)⟩
abbrev w150 : Ball := w150S5

def w151Trace : List Ball := [
  ⟨(98959822654324787871539121812971 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(12434875620743719407780970556231 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(24913091885247805750256332344387 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3324637982152081281287943789147 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(831593657501690572183100460147 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(166376648573127187111332761389 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138681694460002178282799893639 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19815366779362640151966072889 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(495456055606955034074299139 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(275285319684876352292938213 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3441393365003636971129463 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2503029667117263217847199 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(104299888913743438518221 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1002941130867380488099 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(229255095154128675347 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76421661908341389161 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w151S0 : Ball := ⟨(19586092999550827008102937488861 / 20000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w151S1 : Ball := ⟨(95903759746763478003858382709171 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w151S2 : Ball := ⟨(91975311335649308066233628913593 / 100000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w151S3 : Ball := ⟨(4229728947644810052656875620657 / 5000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
def w151S4 : Ball := ⟨(71562427882177889197978168586201 / 100000000000000000000000000000000), (9 / 20000000000000000000000000000000)⟩
def w151S5 : Ball := ⟨(51211810843919113717266306638877 / 100000000000000000000000000000000), (13 / 20000000000000000000000000000000)⟩
abbrev w151 : Ball := w151S5

def w152Trace : List Ball := [
  ⟨(49480065952126892699445810186087 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49739580065588740262284227339971 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(12456558895605846946045926937113 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16623202877284277746252173541207 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1039492720655041444890717499779 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(831883675599486957612835161809 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(69340878151097194403499983237 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(309615226748131662016326479 / 1562500000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1238640568701460127778783137 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(137642702819008821409504633 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13765577367594078639829061 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1251515159233883307584931 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208599827937125245833071 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16047061673494190400483 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(573137857216105179541 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9552709605526006609 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w152S0 : Ball := ⟨(979310770650730793831531242189 / 1000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w152S1 : Ball := ⟨(19180991710250564999263735763499 / 20000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w152S2 : Ball := ⟨(45988805373587611805931315798183 / 50000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w152S3 : Ball := ⟨(42299404393794415981700998922627 / 50000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
def w152S4 : Ball := ⟨(715695844827901737672838551853 / 1000000000000000000000000000000), (9 / 20000000000000000000000000000000)⟩
def w152S5 : Ball := ⟨(10244410846078480049421577074601 / 20000000000000000000000000000000), (13 / 20000000000000000000000000000000)⟩
abbrev w152 : Ball := w152S5

def w153Trace : List Ball := [
  ⟨(1979267581737113838921540428197 / 2000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49740394692784312079075295973587 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(24913389806273844563174475469239 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16623339026762477003549467592479 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(129937441608006187186082093829 / 3125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(415944109664114042263111789553 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138682405648127041018180042841 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2476931962955140149453843733 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1238645080400423413910090399 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(275286308148947635685391553 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1376561839730194464809187 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(625759289416736695122603 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13037522130604870384161 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8023549629776633163579 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(114627822038429962967 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76421833670808021833 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w153S0 : Ball := ⟨(489687520014435326413882344469 / 500000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w153S1 : Ball := ⟨(47958773451577599676843491263659 / 50000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w153S2 : Ball := ⟨(18400351607837955147964393903857 / 20000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w153S3 : Ball := ⟨(21160808705754051322286455320327 / 25000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
def w153S4 : Ball := ⟨(71644772013042631775180889902173 / 100000000000000000000000000000000), (9 / 20000000000000000000000000000000)⟩
def w153S5 : Ball := ⟨(10265946713601713519591380950439 / 20000000000000000000000000000000), (13 / 20000000000000000000000000000000)⟩
abbrev w153 : Ball := w153S5

def w154Trace : List Ball := [
  ⟨(49485478130313505717427853518031 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49742295558815157227518693120877 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(24914024525422866221757764749047 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16623656715820428421459383870093 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4158061713231491983785648007137 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(415949410763730894550750913829 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(34670980202333395331275061639 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4953911288345802145949059409 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(309663901953265088157488883 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(275288414028708492591919431 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13765714134158981687190871 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1251526557966273265284723 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(10430079089427658903997 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8023593480498451343117 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(573142033822932358121 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(38211099799770641371 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w154S0 : Ball := ⟨(765253920558042580483409467523 / 781250000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w154S1 : Ball := ⟨(95946926150361898155229298951251 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w154S2 : Ball := ⟨(92058126377029998536473445358587 / 100000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w154S3 : Ball := ⟨(8474698632049226364252595853363 / 10000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
def w154S4 : Ball := ⟨(35910258452028514313791019398413 / 50000000000000000000000000000000), (9 / 20000000000000000000000000000000)⟩
def w154S5 : Ball := ⟨(3223866655228713372649086705233 / 6250000000000000000000000000000), (13 / 20000000000000000000000000000000)⟩
abbrev w154 : Ball := w154S5

def w155Trace : List Ball := [
  ⟨(395884443611467931532306894623 / 400000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(24871167176504417390500712355337 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49828074958255247064235741099479 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8311831599685895066409253386727 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(415806301083562194633967844933 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(831899037901287355986169979633 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138683951731292567183040696223 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19815649019738010536764361099 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(495462329063957370274107729 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1101153828024605958698809 / 400000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1720714510998137790427207 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(312881680201674038036047 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(41720321368754399721233 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16047188750831599788367 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(114628418697831682377 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(38211103533737307299 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w155S0 : Ball := ⟨(24488201983368989429367489727839 / 25000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w155S1 : Ball := ⟨(95947525820524305222563544636317 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w155S2 : Ball := ⟨(92059277110801782501592279871339 / 100000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w155S3 : Ball := ⟨(21187276255408482467731770682511 / 25000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
def w155S4 : Ball := ⟨(35912054009839686944278492424623 / 50000000000000000000000000000000), (9 / 20000000000000000000000000000000)⟩
def w155S5 : Ball := ⟨(12896756232056427378688678611447 / 25000000000000000000000000000000), (13 / 20000000000000000000000000000000)⟩
abbrev w155 : Ball := w155S5

def w156Trace : List Ball := [
  ⟨(24742893707759167717571839583161 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(99484901471664244712226521630567 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(6228519085075638304395143523973 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8311841325025081733439023372001 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(259879181478253928588995904867 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(415949843511671547411472251249 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(69342022248620967854356993233 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19815660618810464829494793027 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1238656467200795179998878581 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(275288585938553686326632931 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27531443898933030127232013 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1251527209328199532058349 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208601682009461996470387 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8023597060168963565373 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1146284544975813170103 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19105557367818652541 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w156S0 : Ball := ⟨(97953726245354914261265277041379 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def w156S1 : Ball := ⟨(19189864970699864297603953346807 / 20000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
def w156S2 : Ball := ⟨(23015682349605856477323583035117 / 25000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
def w156S3 : Ball := ⟨(84755461442873369322191116754667 / 100000000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩
def w156S4 : Ball := ⟨(71834882443943943591879525160831 / 100000000000000000000000000000000), (7 / 25000000000000000000000000000000)⟩
def w156S5 : Ball := ⟨(25801251678676229010804343740993 / 50000000000000000000000000000000), (41 / 100000000000000000000000000000000)⟩
abbrev w156 : Ball := w156S5

def w157Trace : List Ball := [
  ⟨(99008696131407113842224392670897 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49751762539166181067784558549699 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9966874211646431406391626611839 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3325047764473635493939612362469 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4158378348656381126083297798903 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(415975809801030895024786336923 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2773829322502470833145615031 / 2000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3963317716744737397403008067 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(495483212971729642684657597 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(275298900886518976850263033 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27532381765614020106414963 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19555723315456827276001 / 781250000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(41721539085530462777061 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8023811845855754418869 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(229262637091207260323 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76424021775274255433 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w157S0 : Ball := ⟨(98027219096413099905522032838183 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w157S1 : Ball := ⟨(96093356837761771271104610780997 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w157S2 : Ball := ⟨(46169666141747084808672205786691 / 50000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w157S3 : Ball := ⟨(4263276143280774288544750682133 / 5000000000000000000000000000000), (27 / 100000000000000000000000000000000)⟩
def w157S4 : Ball := ⟨(18175523473866993100920101743149 / 25000000000000000000000000000000), (47 / 100000000000000000000000000000000)⟩
def w157S5 : Ball := ⟨(6606993070981801772863128225947 / 12500000000000000000000000000000), (69 / 100000000000000000000000000000000)⟩
abbrev w157 : Ball := w157S5

def w158Trace : List Ball := [
  ⟨(49516725699859785494417600037017 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9951594340081637180589960627711 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(24919258645231824664112932967329 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1039142275008691581558134268613 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4158586000267836472228403486109 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(831986244409801229164806235013 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138696414263279708471258514269 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1981720726992848572770909857 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2477484822790789408717762799 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(275305777908957530233815321 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27533007042612745612136031 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(500636939472742145097313 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208611704551984763824557 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4011977521138377542947 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(286583069964077930619 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76425216644607352279 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w158S0 : Ball := ⟨(784609959691249460344272007897 / 800000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w158S1 : Ball := ⟨(48094749128648758043500670970943 / 50000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w158S2 : Ball := ⟨(46262097874953209421565892989867 / 50000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w158S3 : Ball := ⟨(85607267991670010199468365755049 / 100000000000000000000000000000000), (27 / 100000000000000000000000000000000)⟩
def w158S4 : Ball := ⟨(3664302166498804330743316209753 / 5000000000000000000000000000000), (47 / 100000000000000000000000000000000)⟩
def w158S5 : Ball := ⟨(1342711036740783113535463371521 / 2500000000000000000000000000000), (7 / 10000000000000000000000000000000)⟩
abbrev w158 : Ball := w158S5

def w159Trace : List Ball := [
  ⟨(1547791831157559854570273448021 / 1562500000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(99528596693597944292350829185461 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9968548359402466641185174997691 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8313666769544585181516603947513 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2079398781562665977648572100617 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(832021520973767598958264972273 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138701455496790021484181575849 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1981783759181812968985302253 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(247755487346694386130485369 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4301762253074999876598447 / 1562500000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(6883411017582406694798197 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(625809447381830454043447 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208615788994554642674793 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16048201857072882054709 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(286587933222733710459 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19106608479435111173 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w159S0 : Ball := ⟨(49063107637208520143250629106451 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w159S1 : Ball := ⟨(96287541240812360649384801219427 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w159S2 : Ball := ⟨(46356452991005705783297221929571 / 50000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w159S3 : Ball := ⟨(85956829356292873833255561410963 / 100000000000000000000000000000000), (27 / 100000000000000000000000000000000)⟩
def w159S4 : Ball := ⟨(591086121038948190956164604429 / 800000000000000000000000000000), (47 / 100000000000000000000000000000000)⟩
def w159S5 : Ball := ⟨(682388286103261935988301163511 / 1250000000000000000000000000000), (7 / 10000000000000000000000000000000)⟩
abbrev w159 : Ball := w159S5

def w160Trace : List Ball := [
  ⟨(99080503463114817342427923617713 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(6221221494487027453126362532391 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4984639655832863328586733225921 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16628248083503839148326683712017 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2079490292981191791068089561563 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1300081309926096842098704929 / 156250000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(34676454144285639787880345683 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19818382868344220553992547457 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1238807736163502887616908509 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(137659422556123599260715117 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13767097570322490075396953 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(250328371755458747100547 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(41723864456495945867181 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4012113564310161196087 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(286592140215691882113 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76427486896340236287 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w160S0 : Ball := ⟨(157071138664068917000913565899 / 160000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w160S1 : Ball := ⟨(376454812640795371223596316491 / 390625000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w160S2 : Ball := ⟨(92876456565418456789494681015819 / 100000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w160S3 : Ball := ⟨(21565090460370152917232098213533 / 25000000000000000000000000000000), (27 / 100000000000000000000000000000000)⟩
def w160S4 : Ball := ⟨(18602125062557910955536927790521 / 25000000000000000000000000000000), (47 / 100000000000000000000000000000000)⟩
def w160S5 : Ball := ⟨(2768312454744361300648215750971 / 5000000000000000000000000000000), (71 / 100000000000000000000000000000000)⟩
abbrev w160 : Ball := w160S5

def w161Trace : List Ball := [
  ⟨(24777287015246801295851993805269 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9955390972030534007663625956193 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(24925596211330744801186823848833 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8314724069901052425429149074019 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4159220742678463788607622127133 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208023020449181157577636864919 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(69355769463032122802772755443 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19819098342547878704341177249 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1238847492758515969971997491 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(275326797745217395345695601 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27534918206839035292763847 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(50066879601841907692761 / 2000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(52155989581323355813813 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8024392715910824479099 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1146390640820326587061 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19107217116001657379 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w161S0 : Ball := ⟨(1964524645874936778595387103443 / 2000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w161S1 : Ball := ⟨(96483927106251143862515181564919 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w161S2 : Ball := ⟨(93091481898443842274841312010957 / 100000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w161S3 : Ball := ⟨(86660240020482975525921112717461 / 100000000000000000000000000000000), (27 / 100000000000000000000000000000000)⟩
def w161S4 : Ball := ⟨(75099972004077191504004519847199 / 100000000000000000000000000000000), (3 / 6250000000000000000000000000000)⟩
def w161S5 : Ball := ⟨(11280011590026355871190756294713 / 20000000000000000000000000000000), (73 / 100000000000000000000000000000000)⟩
abbrev w161 : Ball := w161S5

def w162Trace : List Ball := [
  ⟨(619434111109742672872101881827 / 625000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(99554065041458567318212628980773 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49851244273627408968369860664707 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8314730557070590414261063282771 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2079611669546806673581280761549 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(832092514716877638886863211217 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138711600791553614976572603437 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19819106077655074913960295067 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2477695845144186508964865621 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(137663441860955096051317891 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13767463011980544164187139 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1251672315796811133375203 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(104312004222860339133223 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1003049313259818519859 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1146390879526934542317 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(38214441699936646613 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w162S0 : Ball := ⟨(24556711552404289985960444543423 / 25000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w162S1 : Ball := ⟨(9648513316287781021461583728989 / 10000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w162S2 : Ball := ⟨(11636726151822829236426395337439 / 12500000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w162S3 : Ball := ⟨(33853348883129337947084460193 / 39062500000000000000000000000), (27 / 100000000000000000000000000000000)⟩
def w162S4 : Ball := ⟨(75107482376789976218464365803423 / 100000000000000000000000000000000), (3 / 6250000000000000000000000000000)⟩
def w162S5 : Ball := ⟨(1128226781795963371037633404631 / 2000000000000000000000000000000), (73 / 100000000000000000000000000000000)⟩
abbrev w162 : Ball := w162S5

def w163Trace : List Ball := [
  ⟨(99109612636207588383042761611299 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19910828540431287031887930425179 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(24925635099570361456902746281183 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1662946760131679510211124390033 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1039806159325550371919574181313 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(166418546235419795686819095227 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138711631724316410816252377121 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9909554972605342984570888507 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1238848137478982568804630471 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13766346335513744910679457 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2753492993252364075293387 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(500668991468900620510401 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208624033505942692182301 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3209758160465075830609 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(573195499440136762941 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(38214445433903312541 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w163S0 : Ball := ⟨(49113576584495594384791232407879 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w163S1 : Ball := ⟨(48242868098422278692006694584529 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w163S2 : Ball := ⟨(93094972894470800323293127473701 / 100000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
def w163S3 : Ball := ⟨(43333369891111265109535709654529 / 50000000000000000000000000000000), (23 / 100000000000000000000000000000000)⟩
def w163S4 : Ball := ⟨(15022247568958946689407675643123 / 20000000000000000000000000000000), (41 / 100000000000000000000000000000000)⟩
def w163S5 : Ball := ⟨(112833961011546491885255896167 / 200000000000000000000000000000), (31 / 50000000000000000000000000000000)⟩
abbrev w163 : Ball := w163S5

def w164Trace : List Ball := [
  ⟨(99110851514108511727445783934003 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(12444345498831186459821078600371 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(24925738801987869639265007531539 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2078689937358442567809446283023 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4159235022995227341200436946933 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(416047231431172874246590328011 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2774237583737068921265617493 / 2000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1981914088570388530250684267 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2477699713473026433525785411 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(55065454123526386661963749 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(6883740300265170489977517 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(156459222709647954144517 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(104312116993960038792921 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8024402561842530791283 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(143298994213478192113 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19107237652818319981 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w164S0 : Ball := ⟨(24557402219629163679022063086829 / 25000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w164S1 : Ball := ⟨(19298112120852716000513826513021 / 20000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w164S2 : Ball := ⟨(93104282857250628092398681973637 / 100000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w164S3 : Ball := ⟨(86684074863629331800622572506157 / 100000000000000000000000000000000), (27 / 100000000000000000000000000000000)⟩
def w164S4 : Ball := ⟨(3757064417481647279303531694389 / 5000000000000000000000000000000), (47 / 100000000000000000000000000000000)⟩
def w164S5 : Ball := ⟨(56462132148426838393857212178007 / 100000000000000000000000000000000), (71 / 100000000000000000000000000000000)⟩
abbrev w164 : Ball := w164S5

def w165Trace : List Ball := [
  ⟨(12391353819820282077942459534297 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49782391490975099421389581564271 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49854822185765659678062573426323 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8315178191335046182204493212229 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4159402498265178708594121176563 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(104015298392524905280765922373 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(34678967406739676741176426683 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3963927962603058223634744251 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2477755160714533214109736021 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(6883320405790426691742141 / 2500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27535465415209749018799647 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2503389585955010847487097 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(41725493361842105301341 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4012259014725993496217 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1146407350508321692401 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9553739246834136157 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w165S0 : Ball := ⟨(49134607836151902617603829092007 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w165S1 : Ball := ⟨(24142096872124399539864750993007 / 25000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w165S2 : Ball := ⟨(9325453462128619453896153019971 / 10000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
def w165S3 : Ball := ⟨(86964082274326654907249402101061 / 100000000000000000000000000000000), (23 / 100000000000000000000000000000000)⟩
def w165S4 : Ball := ⟨(18906879014539638748836480975341 / 25000000000000000000000000000000), (41 / 100000000000000000000000000000000)⟩
def w165S5 : Ball := ⟨(57195211851270301002772250899171 / 100000000000000000000000000000000), (63 / 100000000000000000000000000000000)⟩
abbrev w165 : Ball := w165S5

def w166Trace : List Ball := [
  ⟨(49567196568400074621563777287201 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(99566569455051129474903859162923 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(6231927317740769591605188167889 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(519703300049760126378485466887 / 3125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2079716179689007767369186270759 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(832127366056204966590266012787 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138716581121882587268706892411 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1981972877139342863344316069 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2477765046891460692809104417 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(137666902502916803511391127 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1101422212625389516795113 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2503397078493484707921743 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208628043213477450291081 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3209815446810398298077 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8956328872774181351 / 781250000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9553760717142465241 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w166S0 : Ball := ⟨(49138139513008242668839999607787 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w166S1 : Ball := ⟨(12072783773999309679959193925731 / 12500000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w166S2 : Ball := ⟨(93281349154394249540367986748103 / 100000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w166S3 : Ball := ⟨(43507050500320043868869479058439 / 50000000000000000000000000000000), (27 / 100000000000000000000000000000000)⟩
def w166S4 : Ball := ⟨(1183039652023374112206463771679 / 1562500000000000000000000000000), (3 / 6250000000000000000000000000000)⟩
def w166S5 : Ball := ⟨(2866345611795632347426066543241 / 5000000000000000000000000000000), (37 / 50000000000000000000000000000000)⟩
abbrev w166 : Ball := w166S5

def w167Trace : List Ball := [
  ⟨(49567428915178551333528701680047 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(99566802476434866585733114464997 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49855496328301633722497166409301 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(831526253254400445979261805857 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(519929531791515872417630635167 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3250500060483585382854515973 / 390625000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(34679168481509809676741427653 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(619366886709765085140004591 / 3125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(309720792049754293992057971 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(275333933976859620205857911 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(6883891760454200890926997 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(312924756973020519321437 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208628118396860758420671 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8024541302369005369087 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1146410453786454087371 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(38215054070469858747 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w167S0 : Ball := ⟨(49138600185225574765795132677093 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w167S1 : Ball := ⟨(19316816225307607125452119683619 / 20000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w167S2 : Ball := ⟨(46642423635288403906101606759247 / 50000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w167S3 : Ball := ⟨(2175515682573710327557842984451 / 2500000000000000000000000000000), (27 / 100000000000000000000000000000000)⟩
def w167S4 : Ball := ⟨(75725895761986508054144510231683 / 100000000000000000000000000000000), (3 / 6250000000000000000000000000000)⟩
def w167S5 : Ball := ⟨(11468822577910492362546082899621 / 20000000000000000000000000000000), (37 / 50000000000000000000000000000000)⟩
abbrev w167 : Ball := w167S5

def w168Trace : List Ball := [
  ⟨(99135012728693476893808538075059 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19913376030078229782825022732461 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49855522257133937942432959734661 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16630531552928006626421901046179 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(259964847040719713991119571851 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(832128231959855287338534336791 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138716704860782272782618307009 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9909872121244092447227734071 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2477766766233827382538325107 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(68833494241806509117514343 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27535570950546193440669937 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2503398381547880505022421 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(52157035864499927562303 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8024542197483714698641 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1146410573143620386769 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76430115608873049349 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w168S0 : Ball := ⟨(98277507487182176833730475631343 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w168S1 : Ball := ⟨(3863387391157259530180337093759 / 4000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w168S2 : Ball := ⟨(9328601333845559908157079455093 / 10000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w168S3 : Ball := ⟨(43511401422912579731222974757309 / 50000000000000000000000000000000), (27 / 100000000000000000000000000000000)⟩
def w168S4 : Ball := ⟨(75729682151433554724579209802973 / 100000000000000000000000000000000), (3 / 6250000000000000000000000000000)⟩
def w168S5 : Ball := ⟨(5734984758757153909776083780903 / 10000000000000000000000000000000), (73 / 100000000000000000000000000000000)⟩
abbrev w168 : Ball := w168S5

def w169Trace : List Ball := [
  ⟨(9913965979132981403710742545553 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(388942228151078645068975833847 / 390625000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49856300131514428914828098102571 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3326145238002368698373136143019 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(41594765025473475357379763121 / 1000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(832134726286481698799607038491 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138717632908688264301054014297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3963972055276663154224945337 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(154861228835627477154019213 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(275335266683894309248615899 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27535688212900950678601777 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9778938103499084066701 / 390625000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(52157223823692048600501 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16049138102023336286131 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(573207076934730604663 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4776896227929562813 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w169S0 : Ball := ⟨(98286721435406174665473615960613 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w169S1 : Ball := ⟨(12075349513151414514529855232981 / 12500000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w169S2 : Ball := ⟨(93321002153450306264064872946103 / 100000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w169S3 : Ball := ⟨(43544047214621383495429087826007 / 50000000000000000000000000000000), (27 / 100000000000000000000000000000000)⟩
def w169S4 : Ball := ⟨(1185052529893235166451447015261 / 1562500000000000000000000000000), (3 / 6250000000000000000000000000000)⟩
def w169S5 : Ball := ⟨(11504431092583276771638604143613 / 20000000000000000000000000000000), (37 / 50000000000000000000000000000000)⟩
abbrev w169 : Ball := w169S5

def w170Trace : List Ball := [
  ⟨(99140124509574268430126188159637 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9956944343630689428609364534693 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49856377919954343567951325848481 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8315372826960386874538760355739 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4159480397570375838077331521707 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208033843930981106259023555911 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2167464464282446711125582937 / 1562500000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19819871879839262020085360847 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(309722618861288217925225173 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(137667697828082667826008839 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27535699939186784706989133 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(625852282948607072717539 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208628970478721810464127 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1003071467046711257277 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1146414511943200487519 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(38215181025336500287 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w170S0 : Ball := ⟨(49143821438869442892049631528429 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w170S1 : Ball := ⟨(48302303712309677606392134685523 / 50000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w170S2 : Ball := ⟨(93324501756648210501504482580647 / 100000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w170S3 : Ball := ⟨(21773656570316587319270614068333 / 25000000000000000000000000000000), (27 / 100000000000000000000000000000000)⟩
def w170S4 : Ball := ⟨(37927369635367255362282465181161 / 50000000000000000000000000000000), (3 / 6250000000000000000000000000000)⟩
def w170S5 : Ball := ⟨(28769707349155561859531613298219 / 50000000000000000000000000000000), (73 / 100000000000000000000000000000000)⟩
abbrev w170 : Ball := w170S5

def w171Trace : List Ball := [
  ⟨(99201331441303695560929899221503 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(12450016503449796400157455627393 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49866621655698057520231330426331 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1663330872042930379032512220349 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1039998323846075645878237355477 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(416110446289264732889617755811 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138729946039453475179775116017 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3964279954741417530507195553 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1238975374138962887313613479 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(55070475592938652606248421 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13768621990063507051042087 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(100141512624169854269779 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(41727774027760455450923 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(20062313309230325407 / 125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3582692687979062273 / 312500000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76433311884339083413 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w171S0 : Ball := ⟨(49204520798636945722375134583359 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w171S1 : Ball := ⟨(3873735787237593239827223339173 / 4000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w171S2 : Ball := ⟨(2930825966665089109529771101407 / 3125000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
def w171S3 : Ball := ⟨(87958946272034345167561583735759 / 100000000000000000000000000000000), (1 / 4000000000000000000000000000000)⟩
def w171S4 : Ball := ⟨(38683881146433123137402527708601 / 50000000000000000000000000000000), (9 / 20000000000000000000000000000000)⟩
def w171S5 : Ball := ⟨(29928853211027280825078232274623 / 50000000000000000000000000000000), (71 / 100000000000000000000000000000000)⟩
abbrev w171 : Ball := w171S5

def w172Trace : List Ball := [
  ⟨(99256062268025073283179041298053 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(99627568207564992417956386115501 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49875778857167786672507404494561 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8317799896695598409213342067489 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4160451746453379969363636802819 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(832297329253711293981818971017 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(34685217145747289441786560093 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3964553077038205395074076199 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2478102508985383649585449243 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(275367556171116520739500293 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(6884655994723106459858533 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(312956603364131627925287 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(104323858957529464936743 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16050482677990865853451 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(573251899108516154297 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(7643594806480522833 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w172S0 : Ball := ⟨(98517658969540706545369648688137 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w172S1 : Ball := ⟨(48528645644193622145196793572853 / 50000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w172S2 : Ball := ⟨(23550294480597126156822101134191 / 25000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
def w172S3 : Ball := ⟨(88738619219654954251215815201959 / 100000000000000000000000000000000), (29 / 100000000000000000000000000000000)⟩
def w172S4 : Ball := ⟨(39372712705054578208852199755329 / 50000000000000000000000000000000), (13 / 25000000000000000000000000000000)⟩
def w172S5 : Ball := ⟨(31004210115095324025983705526571 / 50000000000000000000000000000000), (83 / 100000000000000000000000000000000)⟩
abbrev w172 : Ball := w172S5

def w173Trace : List Ball := [
  ⟨(99265057756270017574394851114287 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19926415419919032085884146869581 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9975456736246444616425757989447 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8317988139311292886843299488397 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4160527080748098179886321016463 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(166461977881119743250210384667 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(6937133168292257282991976263 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19822989779283132088877933221 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2478127445772903159613521919 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(275370050186248556375250827 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1721178170814235546048427 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1251835862444188318236803 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208649171723989464144729 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3210117305764728418469 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1146510722029740417409 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76436381204938475937 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w173S0 : Ball := ⟨(98535516913556223757709527547079 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w173S1 : Ball := ⟨(19418496186843449281079417032763 / 20000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w173S2 : Ball := ⟨(5891843658725837185815025154959 / 6250000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w173S3 : Ball := ⟨(88867383549101720075511005852219 / 100000000000000000000000000000000), (27 / 100000000000000000000000000000000)⟩
def w173S4 : Ball := ⟨(9871764823578943786663937431817 / 12500000000000000000000000000000), (49 / 100000000000000000000000000000000)⟩
def w173S5 : Ball := ⟨(31184557034256196846304679690331 / 50000000000000000000000000000000), (39 / 50000000000000000000000000000000)⟩
abbrev w173 : Ball := w173S5

def w174Trace : List Ball := [
  ⟨(24829839545287398291214359318369 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(99659291709965768586419616786887 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49886365962458957833778370256761 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16638248461740330904105018456463 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(832196346504456098808275201567 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(832385690324216536304283150789 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(17344186851828817735990529287 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9912171988714491033788485387 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(309784741996965495571705651 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(275385101149385554831538297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2754021914960994833729881 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(625946442496172601546883 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208657945108245628761047 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16051213241507906628761 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(573276252662217021773 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9554874372700578161 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w174S0 : Ball := ⟨(12330418636894358278756040958559 / 12500000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w174S1 : Ball := ⟨(97305103207085903662123915133933 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w174S2 : Ball := ⟨(94682831101416394142666610172997 / 100000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w174S3 : Ball := ⟨(44824192526896718123821350408031 / 50000000000000000000000000000000), (27 / 100000000000000000000000000000000)⟩
def w174S4 : Ball := ⟨(16073665885506428738593980307451 / 20000000000000000000000000000000), (49 / 100000000000000000000000000000000)⟩
def w174S5 : Ball := ⟨(64590683749723291475674939583937 / 100000000000000000000000000000000), (79 / 100000000000000000000000000000000)⟩
abbrev w174 : Ball := w174S5

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Four0_3_5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators

def w202Trace : List Ball := [
  ⟨(51713390685185762319526489215421 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(50851884553834533690268646719977 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(25283162421355108596361245630931 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16808008687374281364421925783323 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(83898064601069751960087028993 / 2000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(104754455154223451447541394857 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(174450302372631357707209257 / 125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1992514959647404271945143271 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(622368801366733070748750647 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(276504553758549412423486779 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27641966794746975267329611 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1256131638079534257425953 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(104654982228108140926653 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4024445019738765061811 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(574828300997153000947 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(38316337916283146111 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w202S0 : Ball := ⟨(21394198209269260544267878317171 / 20000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w202S1 : Ball := ⟨(1144279292543750086472332290649 / 1000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w202S2 : Ball := ⟨(65468754967221259612133124940191 / 50000000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩
def w202S3 : Ball := ⟨(171446315078322334150028919584107 / 100000000000000000000000000000000), (9 / 20000000000000000000000000000000)⟩
def w202S4 : Ball := ⟨(293938389539353761505766188389617 / 100000000000000000000000000000000), (31 / 20000000000000000000000000000000)⟩
def w202S5 : Ball := ⟨(10799972105623609100886591912781 / 1250000000000000000000000000000), (57 / 6250000000000000000000000000000)⟩
abbrev w202 : Ball := w202S5

def w203Trace : List Ball := [
  ⟨(103476244123961483680514706322297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(101728223106325997052099316244637 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(10114886036110087913521375368703 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3362005629193244840131698032459 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(262206637950722513016595328081 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(838102695415265963569707036261 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(69784904719636107711000682983 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19926344409937310525468007741 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(99584314489584496755577971 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1080147700146577521638151 / 390625000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27643171399431228570087641 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2512363616141576004545311 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(104658840016887089749977 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(50307284416386804559 / 312500000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1149693320081583450947 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76634961020165839941 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w203S0 : Ball := ⟨(13384166372502091849025456287829 / 12500000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w203S1 : Ball := ⟨(114646982071562114602890062248891 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w203S2 : Ball := ⟨(131439304981170849346400844756921 / 100000000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩
def w203S3 : Ball := ⟨(172762908939332440490557994868611 / 100000000000000000000000000000000), (9 / 20000000000000000000000000000000)⟩
def w203S4 : Ball := ⟨(298470227051800728781169252302483 / 100000000000000000000000000000000), (39 / 25000000000000000000000000000000)⟩
def w203S5 : Ball := ⟨(17816895287270695911769071124509 / 2000000000000000000000000000000), (233 / 25000000000000000000000000000000)⟩
abbrev w203 : Ball := w203S5
def w204S0 : Ball := ⟨(53587884411527097257720310770709 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w204S1 : Ball := ⟨(14358306778515944353807100067073 / 12500000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w204S2 : Ball := ⟨(26388604613885045236344938057137 / 20000000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩
def w204S3 : Ball := ⟨(174089613366988774345708680104477 / 100000000000000000000000000000000), (23 / 50000000000000000000000000000000)⟩
def w204S4 : Ball := ⟨(303071934822676365370582651560239 / 100000000000000000000000000000000), (161 / 100000000000000000000000000000000)⟩
def w204S5 : Ball := ⟨(918525976771605908947026239697719 / 100000000000000000000000000000000), (61 / 6250000000000000000000000000000)⟩
abbrev w204 : Ball := w204S5
def w205S0 : Ball := ⟨(13401702743683639964664889390029 / 12500000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w205S1 : Ball := ⟨(114947607315236866066441667858927 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w205S2 : Ball := ⟨(66064762137489479422041135891683 / 50000000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩
def w205S3 : Ball := ⟨(174582111851322539597817893821251 / 100000000000000000000000000000000), (23 / 50000000000000000000000000000000)⟩
def w205S4 : Ball := ⟨(304789137784676939344863442210539 / 100000000000000000000000000000000), (161 / 100000000000000000000000000000000)⟩
def w205S5 : Ball := ⟨(116120523139408479936453058760027 / 12500000000000000000000000000000), (491 / 50000000000000000000000000000000)⟩
abbrev w205 : Ball := w205S5
def w206S0 : Ball := ⟨(107216972427505987290765464338847 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w206S1 : Ball := ⟨(7184674485325361950708801541639 / 6250000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w206S2 : Ball := ⟨(13214604149781825186918545561921 / 10000000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩
def w206S3 : Ball := ⟨(87312881417715517459652138019057 / 50000000000000000000000000000000), (23 / 50000000000000000000000000000000)⟩
def w206S5 : Ball := ⟨(929893613937341743734618904774797 / 100000000000000000000000000000000), (983 / 100000000000000000000000000000000)⟩
abbrev w206 : Ball := w206S5
def w207S5 : Ball := ⟨(95076810167244095568735509015263 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000)⟩
abbrev w207 : Ball := w207S5
def w209S5 : Ball := ⟨(1008147922108215826536089331573577 / 100000000000000000000000000000000), (1049 / 100000000000000000000000000000000)⟩
abbrev w209 : Ball := w209S5
def w210S5 : Ball := ⟨(53948932918934241491393153621359 / 5000000000000000000000000000000), (69 / 6250000000000000000000000000000)⟩
abbrev w210 : Ball := w210S5
def w211S5 : Ball := ⟨(1090803856002985959588218424995479 / 100000000000000000000000000000000), (111 / 10000000000000000000000000000000)⟩
abbrev w211 : Ball := w211S5
def w212S5 : Ball := ⟨(444378121439028245820485065374781 / 25000000000000000000000000000000), (361 / 20000000000000000000000000000000)⟩
abbrev w212 : Ball := w212S5
def w213S5 : Ball := ⟨(1810340423737412958859742418376039 / 100000000000000000000000000000000), (183 / 10000000000000000000000000000000)⟩
abbrev w213 : Ball := w213S5
def w215S5 : Ball := ⟨(932923314825516689178279739912999 / 50000000000000000000000000000000), (523 / 25000000000000000000000000000000)⟩
abbrev w215 : Ball := w215S5
def w220S5 : Ball := ⟨(7990991997925512528741271791289959 / 100000000000000000000000000000000), (8243 / 100000000000000000000000000000000)⟩
abbrev w220 : Ball := w220S5
def w221S5 : Ball := ⟨(826570400741471888048801011204779 / 10000000000000000000000000000000), (1057 / 12500000000000000000000000000000)⟩
abbrev w221 : Ball := w221S5
def w222S5 : Ball := ⟨(9048643952716640880565939814702921 / 100000000000000000000000000000000), (7877 / 100000000000000000000000000000000)⟩
abbrev w222 : Ball := w222S5

end MatrixMultiplication.NativeNumerics

namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def Z0_3_5Den : Ball := ⟨(1170156342338406474588056742626719 / 50000000000000000000000000000000), (283 / 12500000000000000000000000000000)⟩
def Z0_3_5E_1_5LogWitness : LogWitness := ⟨-6, 1324789218043180893556977378811, 781250000000000000000000000000⟩
def Z0_3_5E_1_5Log : Ball := ⟨(-363076963936676832605430257687637 / 100000000000000000000000000000000), (29646153209 / 20000000000000000000000000000000)⟩
def Z0_3_5E_1_5 : Ball := ⟨(9620008942863245806376100207999 / 100000000000000000000000000000000), (3927490439 / 100000000000000000000000000000000)⟩
def Z0_3_5E_2_4LogWitness : LogWitness := ⟨-2, 43077488265096366404092710992583, 25000000000000000000000000000000⟩
def Z0_3_5E_2_4Log : Ball := ⟨(-21054240984169208151357583517443 / 25000000000000000000000000000000), (50821977 / 80000000000000000000000000000)⟩
def Z0_3_5E_2_4 : Ball := ⟨(4534819094630300182044972074441 / 12500000000000000000000000000000), (27366039047 / 100000000000000000000000000000000)⟩
def Z0_3_5E_3_4LogWitness : LogWitness := ⟨-5, 854586659763454361758666849959, 625000000000000000000000000000⟩
def Z0_3_5E_3_4Log : Ball := ⟨(-315286963936676832605430276783021 / 100000000000000000000000000000000), (25410988443 / 20000000000000000000000000000000)⟩
def Z0_3_5E_3_4 : Ball := ⟨(2694400333776053497620803489567 / 20000000000000000000000000000000), (108579459 / 2000000000000000000000000000000)⟩
def Z0_3_5E_4_2LogWitness : LogWitness := ⟨-2, 43077488265096366404092710992583, 25000000000000000000000000000000⟩
def Z0_3_5E_4_2Log : Ball := ⟨(-21054240984169208151357583517443 / 25000000000000000000000000000000), (50821977 / 80000000000000000000000000000)⟩
def Z0_3_5E_4_2 : Ball := ⟨(4534819094630300182044972074441 / 12500000000000000000000000000000), (27366039047 / 100000000000000000000000000000000)⟩
def Z0_3_5E_4_3LogWitness : LogWitness := ⟨-5, 854586659763454361758666849959, 625000000000000000000000000000⟩
def Z0_3_5E_4_3Log : Ball := ⟨(-315286963936676832605430276783021 / 100000000000000000000000000000000), (25410988443 / 20000000000000000000000000000000)⟩
def Z0_3_5E_4_3 : Ball := ⟨(2694400333776053497620803489567 / 20000000000000000000000000000000), (108579459 / 2000000000000000000000000000000)⟩
def Z0_3_5E_5_1LogWitness : LogWitness := ⟨-6, 1324789218043180893556977378811, 781250000000000000000000000000⟩
def Z0_3_5E_5_1Log : Ball := ⟨(-363076963936676832605430257687637 / 100000000000000000000000000000000), (29646153209 / 20000000000000000000000000000000)⟩
def Z0_3_5E_5_1 : Ball := ⟨(9620008942863245806376100207999 / 100000000000000000000000000000000), (3927490439 / 100000000000000000000000000000000)⟩
def Z0_3_5Entropy : Ball := ⟨(29685281684392957375419947125681 / 25000000000000000000000000000000), (9180625609 / 12500000000000000000000000000000)⟩
def Z0_3_5Labels : Ball := ⟨(128376055945530243441219837539503 / 25000000000000000000000000000000), (31897811419 / 20000000000000000000000000000000)⟩
def Z0_3_5Four : Ball := ⟨(4939416800935100025519993270787 / 781250000000000000000000000000), (232934061967 / 100000000000000000000000000000000)⟩
def Z0_3_5H2E_1_5LogWitness : LogWitness := ⟨-6, 1324789218043180893556977378811, 781250000000000000000000000000⟩
def Z0_3_5H2E_1_5Log : Ball := ⟨(-363076963936676832605430257687637 / 100000000000000000000000000000000), (29646153209 / 20000000000000000000000000000000)⟩
def Z0_3_5H2E_1_5 : Ball := ⟨(9620008942863245806376100207999 / 100000000000000000000000000000000), (3927490439 / 100000000000000000000000000000000)⟩
def Z0_3_5H2E_2_4LogWitness : LogWitness := ⟨-2, 43077488265096366404092710992583, 25000000000000000000000000000000⟩
def Z0_3_5H2E_2_4Log : Ball := ⟨(-21054240984169208151357583517443 / 25000000000000000000000000000000), (50821977 / 80000000000000000000000000000)⟩
def Z0_3_5H2E_2_4 : Ball := ⟨(4534819094630300182044972074441 / 12500000000000000000000000000000), (27366039047 / 100000000000000000000000000000000)⟩
def Z0_3_5H2E_3_4LogWitness : LogWitness := ⟨-5, 854586659763454361758666849959, 625000000000000000000000000000⟩
def Z0_3_5H2E_3_4Log : Ball := ⟨(-315286963936676832605430276783021 / 100000000000000000000000000000000), (25410988443 / 20000000000000000000000000000000)⟩
def Z0_3_5H2E_3_4 : Ball := ⟨(2694400333776053497620803489567 / 20000000000000000000000000000000), (108579459 / 2000000000000000000000000000000)⟩
def Z0_3_5H2E_4_2LogWitness : LogWitness := ⟨-2, 43077488265096366404092710992583, 25000000000000000000000000000000⟩
def Z0_3_5H2E_4_2Log : Ball := ⟨(-21054240984169208151357583517443 / 25000000000000000000000000000000), (50821977 / 80000000000000000000000000000)⟩
def Z0_3_5H2E_4_2 : Ball := ⟨(4534819094630300182044972074441 / 12500000000000000000000000000000), (27366039047 / 100000000000000000000000000000000)⟩
def Z0_3_5H2E_4_3LogWitness : LogWitness := ⟨-5, 854586659763454361758666849959, 625000000000000000000000000000⟩
def Z0_3_5H2E_4_3Log : Ball := ⟨(-315286963936676832605430276783021 / 100000000000000000000000000000000), (25410988443 / 20000000000000000000000000000000)⟩
def Z0_3_5H2E_4_3 : Ball := ⟨(2694400333776053497620803489567 / 20000000000000000000000000000000), (108579459 / 2000000000000000000000000000000)⟩
def Z0_3_5H2E_5_1LogWitness : LogWitness := ⟨-6, 1324789218043180893556977378811, 781250000000000000000000000000⟩
def Z0_3_5H2E_5_1Log : Ball := ⟨(-363076963936676832605430257687637 / 100000000000000000000000000000000), (29646153209 / 20000000000000000000000000000000)⟩
def Z0_3_5H2E_5_1 : Ball := ⟨(9620008942863245806376100207999 / 100000000000000000000000000000000), (3927490439 / 100000000000000000000000000000000)⟩
def Z0_3_5H2Entropy : Ball := ⟨(29685281684392957375419947125681 / 25000000000000000000000000000000), (9180625609 / 12500000000000000000000000000000)⟩
def Z0_3_5H2Mass : Ball := ⟨1, (99 / 50000000000000000000000000000000)⟩
def Z0_3_5H2MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def Z0_3_5H2MassTermLog : Ball := ⟨0, (529395597 / 2500000000000000000000000000000)⟩
def Z0_3_5H2MassTerm : Ball := ⟨0, (21175823881 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Four0_4_4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
def w100Trace : List Ball := [
  ⟨(97363808048856985660165450324797 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(24669008783652023299422619489561 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49557697616728292986202720009597 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8277971847405909721320013857111 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1036125599296733877895790875611 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(829636943913202670104224184279 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(69180290937057681209201526347 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9887603504943763630568931009 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(618204060192434284275661 / 25000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(137419382645792895122512207 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27490539647607580977378537 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(312455615292126214428737 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(52084839931333836241107 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8014226755796370619681 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1145034983417882232977 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76343950594090103019 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w100S0 : Ball := ⟨(47398555588873341724686046775559 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w100S1 : Ball := ⟨(89864922876460651932578619425867 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w100S2 : Ball := ⟨(5047315227245138132602455108267 / 6250000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
def w100S3 : Ball := ⟨(16304250242035609848233936841687 / 25000000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩
def w100S4 : Ball := ⟨(42532572152786918770779642257387 / 100000000000000000000000000000000), (27 / 100000000000000000000000000000000)⟩
def w100S5 : Ball := ⟨(18090196939320252698965158083619 / 100000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩
abbrev w100 : Ball := w100S5

def w101Trace : List Ball := [
  ⟨(3895599123548468284740572794943 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49344618433903682032105496895659 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3097632357775341925532331817753 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8278525829507818815695444470319 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1036181095602306844152453985853 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(103709248528603521478675284201 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(34591469734185622156975632523 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19775869630963970638737423483 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(494577981753009617233388509 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(274846135646728491105893797 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(6872802487348840077319109 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2499700799830994901321347 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(20834365924809551918189 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16028760698020866745539 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(229011093376800501783 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4771577192413948883 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w101S0 : Ball := ⟨(94848078321197464170988729902259 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w101S1 : Ball := ⟨(1405649681441251308336265589321 / 1562500000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w101S2 : Ball := ⟨(40465429031647053471787242492501 / 50000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
def w101S3 : Ball := ⟨(65498037868610567665806252872733 / 100000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
def w101S4 : Ball := ⟨(21449964823189719768081407158467 / 50000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩
def w101S5 : Ball := ⟨(18404039636643055441287351883573 / 100000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
abbrev w101 : Ball := w101S5

def w102Trace : List Ball := [
  ⟨(60878913648034409468052631867 / 62500000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(98697450764775831185808012854031 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49564867741451218329441213711879 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1034858810984676070060732001001 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4144862487875837400842557608431 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(41484851733547565632409171981 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138369174381621573131335512017 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9888140931419290232301599329 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3956697182567992423080141 / 160000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(137425360437312930472833923 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(5498325390916810406557127 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1249867780996989019973771 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(52086583508592306868843 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16028951802100474624337 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(572534104926856056703 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19086508536872422661 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w102S0 : Ball := ⟨(47439899225149827711648009783193 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w102S1 : Ball := ⟨(45010880769847424474168206678323 / 50000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w102S2 : Ball := ⟨(4051958775354841350593506941473 / 5000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w102S3 : Ball := ⟨(16418369917175105673666336203141 / 25000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩
def w102S4 : Ball := ⟨(8626011863590415562837422362351 / 20000000000000000000000000000000), (1 / 3125000000000000000000000000000)⟩
def w102S5 : Ball := ⟨(18602020167700648516904861253201 / 100000000000000000000000000000000), (7 / 25000000000000000000000000000000)⟩
abbrev w102 : Ball := w102S5

def w103Trace : List Ball := [
  ⟨(97461677405583320429892784906173 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(24681350052061302413683039502419 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(24787112328260887905542961829461 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16560086285388239495898441707087 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2072666181045074120074870073867 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(414887721937763384103098514643 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(6919019304151326895676799119 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19777684336183811864227296597 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2473091659377625013244781297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(137433160130880981787953733 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27493045638531965225528077 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2499853825008342345713443 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208355433784922537024077 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16029601945026421849607 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4580446247079516223 / 400000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(7634875247522248597 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w103S0 : Ball := ⟨(94987785627099903091492533052489 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def w103S1 : Ball := ⟨(45113397091699434650026722873749 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
def w103S2 : Ball := ⟨(40704371943067100169864190687187 / 50000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
def w103S3 : Ball := ⟨(66273835811181925431687419899547 / 100000000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩
def w103S4 : Ball := ⟨(43922213131274998201000278230563 / 100000000000000000000000000000000), (23 / 100000000000000000000000000000000)⟩
def w103S5 : Ball := ⟨(19291608063491458823510272196767 / 100000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
abbrev w103 : Ball := w103S5

def w104Trace : List Ball := [
  ⟨(24367056458004436300887556459291 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(98728702626653855089437939569527 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49575330181667849302931920271901 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16560363376345140514475446379693 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2072693937538896459979922729193 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(829784707340921148693978387759 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138381710647318923299242332883 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9888925012331768747678401287 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1236555039849939546370309859 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(137434081576428291290061171 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1099728529567358823028379 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2499867796321523835158437 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208356508804213203871251 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3205935750175274059761 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(572558341608467961737 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76349073596355755747 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w104S0 : Ball := ⟨(95000550468412112792381367549949 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w104S1 : Ball := ⟨(22562761473253292258216097161543 / 25000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w104S2 : Ball := ⟨(16290502569565538410855641806651 / 20000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
def w104S3 : Ball := ⟨(33172559246127676203892981796617 / 50000000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩
def w104S4 : Ball := ⟨(687761679336156738369940581373 / 1562500000000000000000000000000), (27 / 100000000000000000000000000000000)⟩
def w104S5 : Ball := ⟨(19374740584992378334820330188889 / 100000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩
abbrev w104 : Ball := w104S5

def w105Trace : List Ball := [
  ⟨(779916394708736003084630050167 / 800000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1974789114185250434156337250049 / 2000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49578929822516353674852998920349 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4140316396102717061425772661271 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(829113724726044609349663886589 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(207453717172503637348547037581 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138386023336038699671393628681 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19778389492632810914267854783 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1236585027276899814619765151 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(274874163419096538471127961 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(68734397321766770348597 / 250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(15624458033230706272989 / 625000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(26045001117300264636043 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(200374110264932499389 / 1250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(286283339498669107889 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1192970611047222117 / 1562500000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w105S0 : Ball := ⟨(1485033160975275615600053254807 / 1562500000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w105S1 : Ball := ⟨(90330050117477124487665552944853 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w105S2 : Ball := ⟨(81595179542259290714549823394629 / 100000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
def w105S3 : Ball := ⟨(66577733245335290745785998548529 / 100000000000000000000000000000000), (11 / 50000000000000000000000000000000)⟩
def w105S4 : Ball := ⟨(44325945640870240256900270583241 / 100000000000000000000000000000000), (3 / 10000000000000000000000000000000)⟩
def w105S5 : Ball := ⟨(1227993410598364658901849609783 / 6250000000000000000000000000000), (27 / 100000000000000000000000000000000)⟩
abbrev w105 : Ball := w105S5

def w106Trace : List Ball := [
  ⟨(6093334849905789442156207233017 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(98741376067256485032340612661157 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49579572656850469582200276780919 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(331228534025604071387730485889 / 2000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2072800450770492468126150003653 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(829820254843128421566729980361 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138386793483790455507241084659 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3955697165790575050835165963 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2473180764624746108566604101 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1374376174601400906221137 / 500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13746928187677238261257689 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1249960704256325574778183 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208360633973857689866493 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8014986738687510075361 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(286284083920422957299 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(7635030580535551187 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w106S0 : Ball := ⟨(9504954775827560844624340219581 / 10000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w106S1 : Ball := ⟨(90344165290527157429115168254217 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w106S2 : Ball := ⟨(40810341010210459899599711666827 / 50000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w106S3 : Ball := ⟨(16654839333696657006432334846111 / 25000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩
def w106S4 : Ball := ⟨(44381387716999888946266223964909 / 100000000000000000000000000000000), (33 / 100000000000000000000000000000000)⟩
def w106S5 : Ball := ⟨(19697075756866686146513677305887 / 100000000000000000000000000000000), (3 / 10000000000000000000000000000000)⟩
abbrev w106 : Ball := w106S5

def w107Trace : List Ball := [
  ⟨(48747288136539656265494084659123 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(98741990592354207781733581890681 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49579778366482358500554688710143 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16561478259208729579715452029597 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4145611230560978856381388492169 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(829821978424792079720304925103 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138387039932656094115289196819 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19778516656751564450015575127 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1236592095932544020211977867 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(68718894450565855594093199 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2749388755841553392993741 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2499924007945581777002379 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(104180416992969527736073 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2003748470925226035863 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1145137288544617278939 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9543795693602770839 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w107S0 : Ball := ⟨(95051924026672796537326677897943 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w107S1 : Ball := ⟨(90348682611723772593783151765771 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w107S2 : Ball := ⟨(81628844496739975780380322680573 / 100000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
def w107S3 : Ball := ⟨(66632682538729562298314907798171 / 100000000000000000000000000000000), (11 / 50000000000000000000000000000000)⟩
def w107S4 : Ball := ⟨(44399143823071155074751540684837 / 100000000000000000000000000000000), (3 / 10000000000000000000000000000000)⟩
def w107S5 : Ball := ⟨(3942567944443515008248530009517 / 20000000000000000000000000000000), (27 / 100000000000000000000000000000000)⟩
abbrev w107 : Ball := w107S5

def w108Trace : List Ball := [
  ⟨(3899917108269645427163782122097 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49371840281361323468566505717711 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49580344074582596055674457749879 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1656162004483804183069291731377 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1036409908896835034580988867453 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(207456679576508881718800733597 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(69193858835499664956633635233 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19778601433638635037173077051 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2473193616820126343198087539 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(274876520731728552785691713 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27493973312167872820136069 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2499931156411877212160093 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(813911656332038192193 / 390625000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16030027065098110504007 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(71571244307835223249 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76350529843355467529 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w108S0 : Ball := ⟨(95058459071089208081579451801823 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w108S1 : Ball := ⟨(45180553204849710742921267271791 / 50000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w108S2 : Ball := ⟨(40825647757925109369477027461183 / 50000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
def w108S3 : Ball := ⟨(33334670297083510191195896164257 / 50000000000000000000000000000000), (11 / 50000000000000000000000000000000)⟩
def w108S4 : Ball := ⟨(22224004876305232751778324710039 / 50000000000000000000000000000000), (3 / 10000000000000000000000000000000)⟩
def w108S5 : Ball := ⟨(1234765981855096909259414847717 / 6250000000000000000000000000000), (27 / 100000000000000000000000000000000)⟩
abbrev w108 : Ball := w108S5

def w109Trace : List Ball := [
  ⟨(97507525631389871537318249775667 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1234356502964035390705336250753 / 1250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49581964110522966193313356533743 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16562026078079833866500669704371 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1036430244762489044605640334733 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(165968058371854803469449173579 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138389658499316716051502902103 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9889422103695388632135432177 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(38644071981592178760929483 / 1562500000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(137439610485689598230468101 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(687355472061121767623613 / 2500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2499951627228721460455087 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(52090739784082377616681 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16030139600405272269499 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1145147412805440827763 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19087750080788843603 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w109S0 : Ball := ⟨(47538587773780763829984326129127 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w109S1 : Ball := ⟨(90396693101018316770119866638629 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w109S2 : Ball := ⟨(16343124247199385094190509277069 / 20000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w109S3 : Ball := ⟨(66774427539849116935937584105619 / 100000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩
def w109S4 : Ball := ⟨(2786765108296600119464703018341 / 6250000000000000000000000000000), (33 / 100000000000000000000000000000000)⟩
def w109S5 : Ball := ⟨(1242569563011097822718992583849 / 6250000000000000000000000000000), (3 / 10000000000000000000000000000000)⟩
abbrev w109 : Ball := w109S5

def w110Trace : List Ball := [
  ⟨(24389263436545781482875278548833 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49386745923393752095498354759849 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49590322702381535015610961361651 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16564120947363547287193425266481 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(518267581290640618981572557639 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(829910320208901224399214830679 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138399671466078066702624404489 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4945024173967499513697485881 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(309169981173002539901832421 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(274893151545536501984938507 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27495485777139358519565267 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2500057235566401232858267 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(41674217016529314221291 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16030720163120093424319 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(286296531192329775209 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76353427401488227381 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w110S0 : Ball := ⟨(47586893678178315425997572795663 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w110S1 : Ball := ⟨(22645124499382473221202193438177 / 25000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w110S2 : Ball := ⟨(41024133087402584673956860758699 / 50000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w110S3 : Ball := ⟨(16829794955729195240555475917429 / 25000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩
def w110S4 : Ball := ⟨(22659359860151029182956227654751 / 50000000000000000000000000000000), (33 / 100000000000000000000000000000000)⟩
def w110S5 : Ball := ⟨(20537863570872946752478267677131 / 100000000000000000000000000000000), (31 / 100000000000000000000000000000000)⟩
abbrev w110 : Ball := w110S5

def w111Trace : List Ball := [
  ⟨(24397686808340299350437115437549 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(24697619340223501776028070218387 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(6199500969277257282868883272437 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4141386425237742050732279041557 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4146426067276205586368036922141 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(414978972638874019449097786283 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27681296201622096854025716187 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19780948468617308816414472731 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2473454542389849448561644689 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(274902625069429427719694161 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27496347326682882865362643 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(625032263485471934338049 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208376611062394265628489 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8015557484094806019717 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1145212450312765144373 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(381775389073772837 / 500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w111S0 : Ball := ⟨(95239539455657962049596314293829 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w111S1 : Ball := ⟨(90705698757258297021902745980781 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w111S2 : Ball := ⟨(10284404733803111710957685166399 / 12500000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
def w111S3 : Ball := ⟨(33846073833174992976719001278833 / 50000000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩
def w111S4 : Ball := ⟨(11455567139207329623096061572967 / 25000000000000000000000000000000), (7 / 25000000000000000000000000000000)⟩
def w111S5 : Ball := ⟨(20996802956941888344896637178211 / 100000000000000000000000000000000), (27 / 100000000000000000000000000000000)⟩
abbrev w111 : Ball := w111S5

def w112Trace : List Ball := [
  ⟨(2440744783513884815630487181939 / 2500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(98810157767362475238374683582699 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(155008107430631157064267381097 / 312500000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(662687853587126193950079081121 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1036689181745824053305780496531 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(830013118639727084670961148193 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138414369717821726414682027739 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19781935219058362655835795723 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1236782120093353079843129093 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(274913599667493446332487519 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13748672691307143159680527 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(625053062757731455927721 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208383012537615582879683 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16031572321642810314461 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1145242946484806041943 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(38178494802843761177 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w112S0 : Ball := ⟨(95315761572003847278242151901881 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w112S1 : Ball := ⟨(90850944040510853236952602027213 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w112S2 : Ball := ⟨(82538940330520345192863283848431 / 100000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w112S3 : Ball := ⟨(68126766708851979905497606139467 / 100000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩
def w112S4 : Ball := ⟨(5801570427752928037235255587489 / 12500000000000000000000000000000), (17 / 50000000000000000000000000000000)⟩
def w112S5 : Ball := ⟨(21541260434033467135061329885171 / 100000000000000000000000000000000), (1 / 3125000000000000000000000000000)⟩
abbrev w112 : Ball := w112S5

def w113Trace : List Ball := [
  ⟨(97656338048605712805937164589279 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(24705884320930685930297382113281 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49607071973741205589583725787371 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3313663681718650977288384452269 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(518372687170440269994699724981 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(166010124575207330264910722941 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(6920986601231639496702529721 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19782605950975315001746505477 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1236819402704467373193081867 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8591283106859154492021341 / 3125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(6874505946669788176468889 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(500053760394153193784799 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208387363748832619052453 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8015941596486930866217 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1145263675224788170587 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3054331561043490607 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w113S0 : Ball := ⟨(47683801805317779196887858105789 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w113S1 : Ball := ⟨(90949798184353083940376255242911 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w113S2 : Ball := ⟨(41359328948872777620472942375029 / 50000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
def w113S3 : Ball := ⟨(34211881822021315602238959736387 / 50000000000000000000000000000000), (11 / 50000000000000000000000000000000)⟩
def w113S4 : Ball := ⟨(9363622862431620267308228420527 / 20000000000000000000000000000000), (31 / 100000000000000000000000000000000)⟩
def w113S5 : Ball := ⟨(2191935827746303246238151343337 / 10000000000000000000000000000000), (3 / 10000000000000000000000000000000)⟩
abbrev w113 : Ball := w113S5

def w114Trace : List Ball := [
  ⟨(97709758464289577222673794134833 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9885045743557260436260937103501 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(12404020117910932154201553439333 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3314115162503556585433277519661 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4147433683253681769637078753133 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(830126071237546135617498291161 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(17303814921970314085972712019 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(618248601465303751156181193 / 3125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(6184472012961557361043611 / 250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(274936065782884890756485777 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(5499877697105072730185399 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(50007651220309254172387 / 2000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(104198058348188160471767 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3206501708591692245519 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(286326343276540294553 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(38180451401376707263 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w114S0 : Ball := ⟨(95471968991498086802643485933219 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w114S1 : Ball := ⟨(45574484315567861068174292710759 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w114S2 : Ball := ⟨(41540672412598819398290787277163 / 50000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
def w114S3 : Ball := ⟨(69025098579633944746442227146727 / 100000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
def w114S4 : Ball := ⟨(23822321169640920082375148313019 / 50000000000000000000000000000000), (3 / 10000000000000000000000000000000)⟩
def w114S5 : Ball := ⟨(22700119436380877386136648698619 / 100000000000000000000000000000000), (3 / 10000000000000000000000000000000)⟩
abbrev w114 : Ball := w114S5

def w116Trace : List Ball := [
  ⟨(19557285924324712926249365025373 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(61805678580941934071008652049 / 62500000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49629005522508691280688280177571 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16573814434904200778968357277313 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4148082390616932020586207537771 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(207558576571097541035422352601 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138445994089322091487652566983 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9892945404256259136927475221 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(154625248519678894279825211 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(137478795898206902201990313 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(5500269214084397009901469 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(312568217584283697054161 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208408672116255248222151 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1603340555301372363313 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1145365184772456959947 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76364651705286005881 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w116S0 : Ball := ⟨(95621858181447385214965137983451 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def w116S1 : Ball := ⟨(91435397620728362399165453997559 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
def w116S2 : Ball := ⟨(41802159690303489377794156983269 / 50000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
def w116S3 : Ball := ⟨(69896822190945356758785291445181 / 100000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
def w116S4 : Ball := ⟨(48855657523926312626507541724637 / 100000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
def w116S5 : Ball := ⟨(2386875272095177720409624195233 / 10000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
abbrev w116 : Ball := w116S5

def w117Trace : List Ball := [
  ⟨(97798653689314581510578822656451 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(6180952718476536541965961936121 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(24815532879414074486471633234623 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16574330643688379707729149212597 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(32407701452438213862669329661 / 781250000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(830251557133805070672131183313 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138448460458942026054287239437 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1236637455978837104033832521 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1237019134824037182085065389 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(274961022519985155020208423 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(5500331611950034584212441 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1250285873608709397615931 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208410673109783283373811 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8016774255739579801549 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1145374717055397839997 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1193207017811758661 / 1562500000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w117S0 : Ball := ⟨(4782288331721242302570610247679 / 5000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w117S1 : Ball := ⟨(11435140843858571428167095920533 / 12500000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w117S2 : Ball := ⟨(83687965516084813478060763696919 / 100000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
def w117S3 : Ball := ⟨(17509188930553502202776224057417 / 25000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
def w117S4 : Ball := ⟨(49051471520930767069354643160821 / 100000000000000000000000000000000), (3 / 10000000000000000000000000000000)⟩
def w117S5 : Ball := ⟨(24060468583686820991892726149029 / 100000000000000000000000000000000), (3 / 10000000000000000000000000000000)⟩
abbrev w117 : Ball := w117S5

def w118Trace : List Ball := [
  ⟨(97837322362202445024817715127483 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49457360401287614668643690359859 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(24818791050948803835348972321179 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16575963323485392035540300785447 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4148512801830612729284225254077 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(830306116992390475577967845173 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27691252171849195503950724261 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9893587471287903817857902299 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1237073363974184443661036083 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2199774981565762138883957 / 800000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(275026447687221514793313 / 1000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2500653996197603863692723 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(52104250371677425141003 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16034000633289866788877 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1145404863883270115771 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76367138527085513693 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w118S0 : Ball := ⟨(95721416470055186173513887544197 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w118S1 : Ball := ⟨(45812947855168761291483100357037 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w118S2 : Ball := ⟨(41976523823608240110366878898297 / 50000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
def w118S3 : Ball := ⟨(17620285523139501462952088387209 / 25000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
def w118S4 : Ball := ⟨(12418978476678379789808138734467 / 25000000000000000000000000000000), (3 / 10000000000000000000000000000000)⟩
def w118S5 : Ball := ⟨(987078568986885443794057967137 / 4000000000000000000000000000000), (3 / 10000000000000000000000000000000)⟩
abbrev w118 : Ball := w118S5

def w119Trace : List Ball := [
  ⟨(48938385491804113902550017367019 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49467294156925162167308983262309 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9928845710022459786596307597303 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16577628534992987469371364297817 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(829769264960388587826625643451 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(207590440360815173306600065951 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3461605405253894554854686019 / 2500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2473521244896143835174069917 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(494851467702103772947575151 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(274982938103766156174816439 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1718978190295596216255561 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(625184468949122009096099 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208423455297972939011387 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16034461714827266083523 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1145435608036625420927 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76369065253885132357 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w119S0 : Ball := ⟨(19159724596355387066919815318401 / 20000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w119S1 : Ball := ⟨(45886880826023199983806758374853 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w119S2 : Ball := ⟨(84224233277666223682408489638391 / 100000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
def w119S3 : Ball := ⟨(17734303678026846291032782597533 / 25000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
def w119S4 : Ball := ⟨(6290110538889530564792147807987 / 12500000000000000000000000000000), (3 / 10000000000000000000000000000000)⟩
def w119S5 : Ball := ⟨(25321913978527449986390800664989 / 100000000000000000000000000000000), (31 / 100000000000000000000000000000000)⟩
abbrev w119 : Ball := w119S5

def w120Trace : List Ball := [
  ⟨(12238726246103792446425272336367 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19790245135713923726645545348043 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49649794046559958187310813393203 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(414475571790862416083067217157 / 2500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(414912558773495191509326928377 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1328653363863888276585466387 / 160000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138470877119463177686720802817 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9894501532378695516960392259 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(618587487387531455527602021 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(274992202789168979705630121 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(5500898712057891334618917 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(78150253267895524022093 / 3125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(20842885877429318964939 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16034847755617434080557 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1145461348522489241403 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(763706783274848131 / 1000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w120S0 : Ball := ⟨(95863308881324689403144852296653 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w120S1 : Ball := ⟨(91897739896762650732492304402069 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w120S2 : Ball := ⟨(42225972990665209240543624838329 / 50000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w120S3 : Ball := ⟨(35660655900167755098964590680273 / 50000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩
def w120S4 : Ball := ⟨(25433647584603386474386431416807 / 50000000000000000000000000000000), (7 / 20000000000000000000000000000000)⟩
def w120S5 : Ball := ⟨(5174963435662413399594860430483 / 20000000000000000000000000000000), (9 / 25000000000000000000000000000000)⟩
abbrev w120 : Ball := w120S5

def w121Trace : List Ball := [
  ⟨(24503779902084132319802811489177 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(618776523003186258526616489219 / 625000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(24833763715755869646733360765899 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16583465344282351506608855089179 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1037503825227217333742487132577 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(415278391590300533313833967323 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27698419417795194320409245731 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(618489283630141511717964669 / 3125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2474644974468104802002671433 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8594428634752329089684821 / 3125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2750717744384696591237699 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2501031820505949163386381 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(104223035790762101007359 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16036077482686008691863 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(229108668798811952593 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76375816265617129539 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w121S0 : Ball := ⟨(48034818359182579943855409263233 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w121S1 : Ball := ⟨(23073437747996638417592153396739 / 25000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w121S2 : Ball := ⟨(42590682360854094798332445616487 / 50000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
def w121S3 : Ball := ⟨(72558648958526725204917615031683 / 100000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
def w121S4 : Ball := ⟨(411309182709899330019232275643 / 781250000000000000000000000000), (31 / 100000000000000000000000000000000)⟩
def w121S5 : Ball := ⟨(13858835970579279869466542234599 / 50000000000000000000000000000000), (33 / 100000000000000000000000000000000)⟩
abbrev w121 : Ball := w121S5

def w122Trace : List Ball := [
  ⟨(98033958699397176287538926466877 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(99013726187111046268105686276237 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(6208837349001912067323347332473 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8292129883152746903700883606333 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(830034879306745828289827676429 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(830583324290212160782035103381 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27699178275063746188713679093 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9896065812279709041749913089 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(7733430391945732820497901 / 312500000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(17189187082454064119705413 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(6876914329164376585289069 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2501071820126373882331437 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(5211228728735278783473 / 2500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3207259470140015896057 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1145558004232174711117 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3818836741070847387 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w122S0 : Ball := ⟨(48053285291375556500693921401103 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w122S1 : Ball := ⟨(92364729091773216080904413271947 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w122S2 : Ball := ⟨(85312431801966574739646796033671 / 100000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
def w122S3 : Ball := ⟨(2274440943739124308348533594259 / 3125000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
def w122S4 : Ball := ⟨(6621544456392855586937891564517 / 12500000000000000000000000000000), (31 / 100000000000000000000000000000000)⟩
def w122S5 : Ball := ⟨(28060704632311652738271218766657 / 100000000000000000000000000000000), (33 / 100000000000000000000000000000000)⟩
abbrev w122 : Ball := w122S5

def w123Trace : List Ball := [
  ⟨(19621870256091549138729653628773 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(99051668345370232159881171244799 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2484169363797689168615137538181 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16587438063979915007059553968821 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2075405440386421993637529740549 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(207672375819550483190663858137 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8656941896304520532671580831 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1237126876282123006364098207 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1237454374744549260398127817 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(275048103189607750302716243 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(6877394240355680718493119 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2501231830421363645571343 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(52115365066250581975997 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16037176879039260673897 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(286404162178833339819 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(38190204522308110271 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w123S0 : Ball := ⟨(48127224043361279522551499696501 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w123S1 : Ball := ⟨(92649187764795681075883948667669 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w123S2 : Ball := ⟨(85838719934763657304963000931437 / 100000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w123S3 : Ball := ⟨(7368285840038791695409127702851 / 10000000000000000000000000000000), (1 / 4000000000000000000000000000000)⟩
def w123S4 : Ball := ⟨(5429163622051616219998684211497 / 10000000000000000000000000000000), (19 / 50000000000000000000000000000000)⟩
def w123S5 : Ball := ⟨(29475817635008624691846674652017 / 100000000000000000000000000000000), (21 / 50000000000000000000000000000000)⟩
abbrev w123 : Ball := w123S5

def w124Trace : List Ball := [
  ⟨(12273790611535785076337223241083 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19818481672429507343487628433517 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(24848504800888796237148742845051 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16590850005333745418344383841107 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4151494118161327765764973336617 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(415401738681420969245539494861 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138527363202814228186411696697 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19796067683759655166444473191 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1237567625193322474929408639 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(68767690240728389751423031 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2751163734129212976761497 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(500280713963158219765633 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208474673696414985738331 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16038120863299332170827 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(114567959054250122191 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(15276870422683088027 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w124S0 : Ball := ⟨(24103349756131836960033683747273 / 25000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w124S1 : Ball := ⟨(92955435114627309480469876285961 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w124S2 : Ball := ⟨(21601782293374219611032056969617 / 25000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w124S3 : Ball := ⟨(7466191972005375343739380987529 / 10000000000000000000000000000000), (1 / 4000000000000000000000000000000)⟩
def w124S4 : Ball := ⟨(55744022562837515480547442472997 / 100000000000000000000000000000000), (19 / 50000000000000000000000000000000)⟩
def w124S5 : Ball := ⟨(7768490128715345018830058107081 / 25000000000000000000000000000000), (43 / 100000000000000000000000000000000)⟩
abbrev w124 : Ball := w124S5

end MatrixMultiplication.NativeNumerics

namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def Z0_4_4Den : Ball := ⟨(2958740185226312087148034776690749 / 20000000000000000000000000000000), (14091 / 100000000000000000000000000000000)⟩
def Z0_4_4E_0_5LogWitness : LogWitness := ⟨-10, 7494452423922705001235812089, 3906250000000000000000000000⟩
def Z0_4_4E_0_5Log : Ball := ⟨(-627988657006593341151923689501087 / 100000000000000000000000000000000), (232934061047 / 100000000000000000000000000000000)⟩
def Z0_4_4E_0_5 : Ball := ⟨(588303889087378458388880598603 / 50000000000000000000000000000000), (109107079 / 25000000000000000000000000000000)⟩
def Z0_4_4E_1_4LogWitness : LogWitness := ⟨-3, 1261243984157612676036813528611, 1250000000000000000000000000000⟩
def Z0_4_4E_1_4Log : Ball := ⟨(-20704865700659334115192382203811 / 10000000000000000000000000000000), (16940658989 / 20000000000000000000000000000000)⟩
def Z0_4_4E_1_4 : Ball := ⟨(26113887307747879276296106837317 / 100000000000000000000000000000000), (427326087 / 4000000000000000000000000000000)⟩
def Z0_4_4E_2_2LogWitness : LogWitness := ⟨-1, 61165519013116834840287783186423, 50000000000000000000000000000000⟩
def Z0_4_4E_2_2Log : Ball := ⟨(-6144832125824167643990482528629 / 12500000000000000000000000000000), (10587911887 / 25000000000000000000000000000000)⟩
def Z0_4_4E_2_2 : Ball := ⟨(15034073848980370592136607206397 / 50000000000000000000000000000000), (25904605089 / 100000000000000000000000000000000)⟩
def Z0_4_4E_2_3LogWitness : LogWitness := ⟨-4, 784932206749518952016351104847, 781250000000000000000000000000⟩
def Z0_4_4E_2_3Log : Ball := ⟨(-17299291062912083821995237683913 / 6250000000000000000000000000000), (105879118637 / 100000000000000000000000000000000)⟩
def Z0_4_4E_2_3 : Ball := ⟨(543150828368552529862213075723 / 3125000000000000000000000000000), (6648634459 / 100000000000000000000000000000000)⟩
def Z0_4_4E_3_2LogWitness : LogWitness := ⟨-4, 784932206749518952016351104847, 781250000000000000000000000000⟩
def Z0_4_4E_3_2Log : Ball := ⟨(-17299291062912083821995237683913 / 6250000000000000000000000000000), (105879118637 / 100000000000000000000000000000000)⟩
def Z0_4_4E_3_2 : Ball := ⟨(543150828368552529862213075723 / 3125000000000000000000000000000), (6648634459 / 100000000000000000000000000000000)⟩
def Z0_4_4E_3_3LogWitness : LogWitness := ⟨-8, 675963374542473156652537959353, 390625000000000000000000000000⟩
def Z0_4_4E_3_3Log : Ball := ⟨(-49967865700659334115192372656099 / 10000000000000000000000000000000), (38116482659 / 20000000000000000000000000000000)⟩
def Z0_4_4E_3_3 : Ball := ⟨(1688822355885139167546274512777 / 50000000000000000000000000000000), (644133659 / 50000000000000000000000000000000)⟩
def Z0_4_4E_4_1LogWitness : LogWitness := ⟨-3, 1261243984157612676036813528611, 1250000000000000000000000000000⟩
def Z0_4_4E_4_1Log : Ball := ⟨(-20704865700659334115192382203811 / 10000000000000000000000000000000), (16940658989 / 20000000000000000000000000000000)⟩
def Z0_4_4E_4_1 : Ball := ⟨(26113887307747879276296106837317 / 100000000000000000000000000000000), (427326087 / 4000000000000000000000000000000)⟩
def Z0_4_4E_5_0LogWitness : LogWitness := ⟨-10, 7494452423922705001235812089, 3906250000000000000000000000⟩
def Z0_4_4E_5_0Log : Ball := ⟨(-627988657006593341151923689501087 / 100000000000000000000000000000000), (232934061047 / 100000000000000000000000000000000)⟩
def Z0_4_4E_5_0 : Ball := ⟨(588303889087378458388880598603 / 50000000000000000000000000000000), (109107079 / 25000000000000000000000000000000)⟩
def Z0_4_4Entropy : Ball := ⟨(61394217798581826908347568176833 / 50000000000000000000000000000000), (62729302307 / 100000000000000000000000000000000)⟩
def Z0_4_4Labels : Ball := ⟨(280000567309103515217519170238121 / 50000000000000000000000000000000), (91650101511 / 50000000000000000000000000000000)⟩
def Z0_4_4Four : Ball := ⟨(170697392553842671062933369207477 / 25000000000000000000000000000000), (246029505329 / 100000000000000000000000000000000)⟩
def Z0_4_4H2E_5_0LogWitness : LogWitness := ⟨-10, 7494452423922705001235812089, 3906250000000000000000000000⟩
def Z0_4_4H2E_5_0Log : Ball := ⟨(-627988657006593341151923689501087 / 100000000000000000000000000000000), (232934061047 / 100000000000000000000000000000000)⟩
def Z0_4_4H2E_5_0 : Ball := ⟨(588303889087378458388880598603 / 50000000000000000000000000000000), (109107079 / 25000000000000000000000000000000)⟩
def Z0_4_4H2E_4_1LogWitness : LogWitness := ⟨-3, 1261243984157612676036813528611, 1250000000000000000000000000000⟩
def Z0_4_4H2E_4_1Log : Ball := ⟨(-20704865700659334115192382203811 / 10000000000000000000000000000000), (16940658989 / 20000000000000000000000000000000)⟩
def Z0_4_4H2E_4_1 : Ball := ⟨(26113887307747879276296106837317 / 100000000000000000000000000000000), (427326087 / 4000000000000000000000000000000)⟩
def Z0_4_4H2E_2_2LogWitness : LogWitness := ⟨-1, 61165519013116834840287783186423, 50000000000000000000000000000000⟩
def Z0_4_4H2E_2_2Log : Ball := ⟨(-6144832125824167643990482528629 / 12500000000000000000000000000000), (10587911887 / 25000000000000000000000000000000)⟩
def Z0_4_4H2E_2_2 : Ball := ⟨(15034073848980370592136607206397 / 50000000000000000000000000000000), (25904605089 / 100000000000000000000000000000000)⟩
def Z0_4_4H2E_2_3LogWitness : LogWitness := ⟨-4, 784932206749518952016351104847, 781250000000000000000000000000⟩
def Z0_4_4H2E_2_3Log : Ball := ⟨(-17299291062912083821995237683913 / 6250000000000000000000000000000), (105879118637 / 100000000000000000000000000000000)⟩
def Z0_4_4H2E_2_3 : Ball := ⟨(543150828368552529862213075723 / 3125000000000000000000000000000), (6648634459 / 100000000000000000000000000000000)⟩
def Z0_4_4H2E_3_2LogWitness : LogWitness := ⟨-4, 784932206749518952016351104847, 781250000000000000000000000000⟩
def Z0_4_4H2E_3_2Log : Ball := ⟨(-17299291062912083821995237683913 / 6250000000000000000000000000000), (105879118637 / 100000000000000000000000000000000)⟩
def Z0_4_4H2E_3_2 : Ball := ⟨(543150828368552529862213075723 / 3125000000000000000000000000000), (6648634459 / 100000000000000000000000000000000)⟩
def Z0_4_4H2E_3_3LogWitness : LogWitness := ⟨-8, 675963374542473156652537959353, 390625000000000000000000000000⟩
def Z0_4_4H2E_3_3Log : Ball := ⟨(-49967865700659334115192372656099 / 10000000000000000000000000000000), (38116482659 / 20000000000000000000000000000000)⟩
def Z0_4_4H2E_3_3 : Ball := ⟨(1688822355885139167546274512777 / 50000000000000000000000000000000), (644133659 / 50000000000000000000000000000000)⟩
def Z0_4_4H2E_1_4LogWitness : LogWitness := ⟨-3, 1261243984157612676036813528611, 1250000000000000000000000000000⟩
def Z0_4_4H2E_1_4Log : Ball := ⟨(-20704865700659334115192382203811 / 10000000000000000000000000000000), (16940658989 / 20000000000000000000000000000000)⟩
def Z0_4_4H2E_1_4 : Ball := ⟨(26113887307747879276296106837317 / 100000000000000000000000000000000), (427326087 / 4000000000000000000000000000000)⟩
def Z0_4_4H2E_0_5LogWitness : LogWitness := ⟨-10, 7494452423922705001235812089, 3906250000000000000000000000⟩
def Z0_4_4H2E_0_5Log : Ball := ⟨(-627988657006593341151923689501087 / 100000000000000000000000000000000), (232934061047 / 100000000000000000000000000000000)⟩
def Z0_4_4H2E_0_5 : Ball := ⟨(588303889087378458388880598603 / 50000000000000000000000000000000), (109107079 / 25000000000000000000000000000000)⟩
def Z0_4_4H2Entropy : Ball := ⟨(61394217798581826908347568176833 / 50000000000000000000000000000000), (62729302307 / 100000000000000000000000000000000)⟩
def Z0_4_4H2Mass : Ball := ⟨(49999999999999999999999999999999 / 50000000000000000000000000000000), (197 / 100000000000000000000000000000000)⟩
def Z0_4_4H2MassTermLogWitness : LogWitness := ⟨-1, 49999999999999999999999999999999, 25000000000000000000000000000000⟩
def Z0_4_4H2MassTermLog : Ball := ⟨(-1 / 100000000000000000000000000000000), (42351647563 / 100000000000000000000000000000000)⟩
def Z0_4_4H2MassTerm : Ball := ⟨(1 / 100000000000000000000000000000000), (10587911891 / 25000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitB1_1_6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
def w43S5 : Ball := ⟨(428217439954036404979998637487 / 25000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
abbrev w43 : Ball := w43S5
def w49S5 : Ball := ⟨(2570679307560226830456392695549 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
abbrev w49 : Ball := w49S5

end MatrixMultiplication.NativeNumerics

namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def Z0_6_2Den : Ball := ⟨(37790811240383961412008118251139 / 25000000000000000000000000000000), (3 / 5000000000000000000000000000000)⟩
def Z0_6_2E_2_5LogWitness : LogWitness := ⟨-3, 15790050502703409550191718781019, 12500000000000000000000000000000⟩
def Z0_6_2E_2_5Log : Ball := ⟨(-184579015932771950225933227583663 / 100000000000000000000000000000000), (84703294883 / 100000000000000000000000000000000)⟩
def Z0_6_2E_2_5 : Ball := ⟨(29145119833177663734886171853233 / 100000000000000000000000000000000), (2674938617 / 20000000000000000000000000000000)⟩
def Z0_6_2E_3_5LogWitness : LogWitness := ⟨-7, 1133125820533948503508356844879, 781250000000000000000000000000⟩
def Z0_6_2E_3_5Log : Ball := ⟨(-448019015932771950225933151201643 / 100000000000000000000000000000000), (21175823727 / 12500000000000000000000000000000)⟩
def Z0_6_2E_3_5 : Ball := ⟨(1015323830087268728146699904139 / 20000000000000000000000000000000), (191958983 / 10000000000000000000000000000000)⟩
def Z0_6_2E_4_4LogWitness : LogWitness := ⟨-1, 16538411838381320973149962187051, 12500000000000000000000000000000⟩
def Z0_6_2E_4_4Log : Ball := ⟨(-10329753983192987556483316443661 / 25000000000000000000000000000000), (21175823703 / 50000000000000000000000000000000)⟩
def Z0_6_2E_4_4 : Ball := ⟨(6833509022528220411360048899287 / 25000000000000000000000000000000), (5603431897 / 20000000000000000000000000000000)⟩
def Z0_6_2E_5_2LogWitness : LogWitness := ⟨-3, 15790050502703409550191718781019, 12500000000000000000000000000000⟩
def Z0_6_2E_5_2Log : Ball := ⟨(-184579015932771950225933227583663 / 100000000000000000000000000000000), (84703294883 / 100000000000000000000000000000000)⟩
def Z0_6_2E_5_2 : Ball := ⟨(29145119833177663734886171853233 / 100000000000000000000000000000000), (2674938617 / 20000000000000000000000000000000)⟩
def Z0_6_2E_5_3LogWitness : LogWitness := ⟨-7, 1133125820533948503508356844879, 781250000000000000000000000000⟩
def Z0_6_2E_5_3Log : Ball := ⟨(-448019015932771950225933151201643 / 100000000000000000000000000000000), (21175823727 / 12500000000000000000000000000000)⟩
def Z0_6_2E_5_3 : Ball := ⟨(1015323830087268728146699904139 / 20000000000000000000000000000000), (191958983 / 10000000000000000000000000000000)⟩
def Z0_6_2Entropy : Ball := ⟨(23944378514335224099169884586251 / 25000000000000000000000000000000), (11721145063 / 20000000000000000000000000000000)⟩
def Z0_6_2Labels : Ball := ⟨(203936037047735086277507450911049 / 50000000000000000000000000000000), (132456585791 / 100000000000000000000000000000000)⟩
def Z0_6_2Four : Ball := ⟨(251824794076405534475847220083551 / 50000000000000000000000000000000), (95531155553 / 50000000000000000000000000000000)⟩
def Z0_6_2H2E_2_0LogWitness : LogWitness := ⟨-3, 15790050502703409550191718781019, 12500000000000000000000000000000⟩
def Z0_6_2H2E_2_0Log : Ball := ⟨(-184579015932771950225933227583663 / 100000000000000000000000000000000), (84703294883 / 100000000000000000000000000000000)⟩
def Z0_6_2H2E_2_0 : Ball := ⟨(29145119833177663734886171853233 / 100000000000000000000000000000000), (2674938617 / 20000000000000000000000000000000)⟩
def Z0_6_2H2E_3_0LogWitness : LogWitness := ⟨-7, 1133125820533948503508356844879, 781250000000000000000000000000⟩
def Z0_6_2H2E_3_0Log : Ball := ⟨(-448019015932771950225933151201643 / 100000000000000000000000000000000), (21175823727 / 12500000000000000000000000000000)⟩
def Z0_6_2H2E_3_0 : Ball := ⟨(1015323830087268728146699904139 / 20000000000000000000000000000000), (191958983 / 10000000000000000000000000000000)⟩
def Z0_6_2H2E_1_1LogWitness : LogWitness := ⟨-1, 16538411838381320973149962187051, 12500000000000000000000000000000⟩
def Z0_6_2H2E_1_1Log : Ball := ⟨(-10329753983192987556483316443661 / 25000000000000000000000000000000), (21175823703 / 50000000000000000000000000000000)⟩
def Z0_6_2H2E_1_1 : Ball := ⟨(6833509022528220411360048899287 / 25000000000000000000000000000000), (5603431897 / 20000000000000000000000000000000)⟩
def Z0_6_2H2E_0_2LogWitness : LogWitness := ⟨-3, 15790050502703409550191718781019, 12500000000000000000000000000000⟩
def Z0_6_2H2E_0_2Log : Ball := ⟨(-184579015932771950225933227583663 / 100000000000000000000000000000000), (84703294883 / 100000000000000000000000000000000)⟩
def Z0_6_2H2E_0_2 : Ball := ⟨(29145119833177663734886171853233 / 100000000000000000000000000000000), (2674938617 / 20000000000000000000000000000000)⟩
def Z0_6_2H2E_0_3LogWitness : LogWitness := ⟨-7, 1133125820533948503508356844879, 781250000000000000000000000000⟩
def Z0_6_2H2E_0_3Log : Ball := ⟨(-448019015932771950225933151201643 / 100000000000000000000000000000000), (21175823727 / 12500000000000000000000000000000)⟩
def Z0_6_2H2E_0_3 : Ball := ⟨(1015323830087268728146699904139 / 20000000000000000000000000000000), (191958983 / 10000000000000000000000000000000)⟩
def Z0_6_2H2Entropy : Ball := ⟨(23944378514335224099169884586251 / 25000000000000000000000000000000), (11721145063 / 20000000000000000000000000000000)⟩
def Z0_6_2H2Mass : Ball := ⟨1, (83 / 100000000000000000000000000000000)⟩
def Z0_6_2H2MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def Z0_6_2H2MassTermLog : Ball := ⟨0, (4235164753 / 20000000000000000000000000000000)⟩
def Z0_6_2H2MassTerm : Ball := ⟨0, (10587911883 / 50000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitA1_3_12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
def w125Trace : List Ball := [
  ⟨(98290253677927362218713350538661 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4957133487933714687068295982863 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(12428453258323185773439599061191 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3319011664268268913556698438909 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4152336777041419161477907235493 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(415472019577711485041498412207 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(69273728090179961955937560417 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9899290271746742107855918947 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(6188536417701484697570999 / 250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27509870164059246254651113 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27514178085577978309297819 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(500323069331591912405189 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208490967398376543148537 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16039284895791052992743 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(143219650488803889823 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76389213738014477929 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w125S0 : Ball := ⟨(96609739680713133557854615626679 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w125S1 : Ball := ⟨(11666802251468947246454152286789 / 12500000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w125S2 : Ball := ⟨(17422627171184754762532226925513 / 20000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w125S3 : Ball := ⟨(1897174609663158062077283709459 / 2500000000000000000000000000000), (1 / 4000000000000000000000000000000)⟩
def w125S4 : Ball := ⟨(449908937443819519461639439231 / 781250000000000000000000000000), (39 / 100000000000000000000000000000000)⟩
def w125S5 : Ball := ⟨(33164173638340887451836381694943 / 100000000000000000000000000000000), (23 / 50000000000000000000000000000000)⟩
abbrev w125 : Ball := w125S5

def w126Trace : List Ball := [
  ⟨(98360464126535214071982895600879 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(24794493360526063183623506981043 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9945122817642310962643140425893 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4149503391885749516586735282187 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(830585698282569077592142613761 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(33241709498849218797014376679 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(34640391109306062880512912791 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19800344902208687596959559919 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2475610680447859229139352603 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(275118318994082697364453787 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27515961937313219576221127 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(125088201656472064532907 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208502406940224535172533 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16040102137252453357613 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1145811694164763207797 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19098156645886783949 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w126S0 : Ball := ⟨(48373904515937103764651472114873 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w126S1 : Ball := ⟨(93601385524680004851586914085753 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w126S2 : Ball := ⟨(43806096860698877735598083518331 / 50000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
def w126S3 : Ball := ⟨(76758964886757282846332106534323 / 100000000000000000000000000000000), (11 / 50000000000000000000000000000000)⟩
def w126S4 : Ball := ⟨(7364923363108046859771657595043 / 12500000000000000000000000000000), (7 / 20000000000000000000000000000000)⟩
def w126S5 : Ball := ⟨(1735747076622551790485561787451 / 5000000000000000000000000000000), (21 / 50000000000000000000000000000000)⟩
abbrev w126 : Ball := w126S5

def w127Trace : List Ball := [
  ⟨(98384442411900865357167747832251 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19838005686558829075453595306201 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49729643420159915440185631250667 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8299511276748566686550076725481 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1038282627314402050138345597927 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(415538216701718069479179584299 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(34641595240171824635060088033 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19800947241847450415873323531 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2475677631459146828423411251 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(68781254022767924892516943 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(5503314183112288018485591 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(312726848998085649496271 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(104253156085546631927629 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16040381125877263965803 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(572915147946297270583 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76393791581146905221 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w127S0 : Ball := ⟨(96794985087006377646264820237291 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w127S1 : Ball := ⟨(9369269137993787045919186912917 / 10000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w127S2 : Ball := ⟨(21945801045040710341537423042823 / 25000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
def w127S3 : Ball := ⟨(77058909361361589461873636539439 / 100000000000000000000000000000000), (11 / 50000000000000000000000000000000)⟩
def w127S4 : Ball := ⟨(59380755119625408074579573935951 / 100000000000000000000000000000000), (7 / 20000000000000000000000000000000)⟩
def w127S5 : Ball := ⟨(35260740785769191116135010727999 / 100000000000000000000000000000000), (21 / 50000000000000000000000000000000)⟩
abbrev w127 : Ball := w127S5

def w128Trace : List Ball := [
  ⟨(384504630963177627416749480319 / 390625000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19842906163905758860982787069059 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(12434458184960216801599915380701 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4150268291823612048684491575279 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1038385267592258386127640099741 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(166228982496986211138973213213 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27715233857276297390304760107 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1237635707954494656634365703 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(77369177793463468272323327 / 3125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(275138625848963230446210587 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(5503561693345853186743189 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1250958971219937669856511 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(52128562054758686727041 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16040948072978672773309 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(229173619461418199141 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19099039729003275837 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w128S0 : Ball := ⟨(96890920129088333700150965974897 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w128S1 : Ball := ⟨(18775700806922749687226120723749 / 20000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w128S2 : Ball := ⟨(88131735197769898432306728134893 / 100000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w128S3 : Ball := ⟨(38836013744849167991694383656639 / 50000000000000000000000000000000), (1 / 4000000000000000000000000000000)⟩
def w128S4 : Ball := ⟨(7541179817950567485647685046759 / 12500000000000000000000000000000), (39 / 100000000000000000000000000000000)⟩
def w128S5 : Ball := ⟨(18198205774932785332745311308657 / 50000000000000000000000000000000), (3 / 6250000000000000000000000000000)⟩
abbrev w128 : Ball := w128S5

def w129Trace : List Ball := [
  ⟨(49225437164389253910410663527061 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(99223421695531925007441021353277 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49740804129260207689926574649977 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3320363436218316221917378383 / 20000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(415369002882853848389269826527 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(831169757446160626034805533803 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13857972055549766523796954557 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2475326928672727389266159481 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1237931525637218757790039829 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(34392945430685693755637083 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(859945545182859248351737 / 3125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(62548884122329391996373 / 2500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208517127365649168953801 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3208230751408433477021 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(71617613208355541581 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(38198508864173133353 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w129S0 : Ball := ⟨(48462873280504695014233486487611 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w129S1 : Ball := ⟨(9394600346409023597759780884083 / 10000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w129S2 : Ball := ⟨(17651703133749709236447940988101 / 20000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w129S3 : Ball := ⟨(15579131176101465272262818970067 / 20000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
def w129S4 : Ball := ⟨(15169333012636039034299519835369 / 25000000000000000000000000000000), (41 / 100000000000000000000000000000000)⟩
def w129S5 : Ball := ⟨(9204346561929982719369806348879 / 25000000000000000000000000000000), (1 / 2000000000000000000000000000000)⟩
abbrev w129 : Ball := w129S5

def w130Trace : List Ball := [
  ⟨(98462258369249929686705629429999 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(99229143343420548548941032950259 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(12435679073675361178608058878661 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16602295966028975878540962959071 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4153785885069782657839319707703 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(415592872656068040406435457581 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(17322750725527344387678307489 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19802901208800728370231351631 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(495178963102082188956395531 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(55029348153343354039844489 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13759273180629524544488719 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(100079177838994154834137 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208518980072950620804901 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8020643056434571073199 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(572945318087435466639 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76397570355412823997 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w130S0 : Ball := ⟨(1938963264634585564586809656723 / 2000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w130S1 : Ball := ⟨(46994731770030123644996817068433 / 50000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w130S2 : Ball := ⟨(88340192565483145525324845948141 / 100000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w130S3 : Ball := ⟨(78039896225066436167134633800741 / 100000000000000000000000000000000), (1 / 4000000000000000000000000000000)⟩
def w130S4 : Ball := ⟨(60902254028191385938025515685907 / 100000000000000000000000000000000), (1 / 2500000000000000000000000000000)⟩
def w130S5 : Ball := ⟨(37090845457143538948140706706749 / 100000000000000000000000000000000), (49 / 100000000000000000000000000000000)⟩
abbrev w130 : Ball := w130S5

def w131Trace : List Ball := [
  ⟨(98464104553902280151231873580993 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(99230071219719432991278105003489 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49743026385984543264891257598099 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3320474721782602674532508322567 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4153801429672734520759139355177 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(415594168994375801575685410529 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138582376391309036589542484997 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19802947552100289883070713821 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2475899966536734053417711757 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(68786814003571254794217213 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13759296606465167735250233 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2501983351055452908983039 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(52129820128713402336711 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16041307576168330806023 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1145892067242239830043 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76397659970612806261 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w131S0 : Ball := ⟨(96951798856017997441037978135213 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w131S1 : Ball := ⟨(93996513014177726773028738759521 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w131S2 : Ball := ⟨(17670688917648965516127791441633 / 20000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w131S3 : Ball := ⟨(78063311706080492099032563551957 / 100000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
def w131S4 : Ball := ⟨(30469403172603417950346524690897 / 50000000000000000000000000000000), (21 / 50000000000000000000000000000000)⟩
def w131S5 : Ball := ⟨(37135381187786209248200975562191 / 100000000000000000000000000000000), (13 / 25000000000000000000000000000000)⟩
abbrev w131 : Ball := w131S5

def w132Trace : List Ball := [
  ⟨(49242822966387930759960108016993 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19848179459828970453636324764463 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(6218330541512576136132510159203 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16603279485522238685392994560791 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4153982790542075365057356928189 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(6493895210214674180478055743 / 781250000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(69293350017777210145965946493 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19803488238179387881679027019 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2475960063269523696890785011 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(68788316841391961324984139 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27519139826569648208831353 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2502028911160676222057971 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(52130696432449812774767 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16041557985286991966123 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(572954381638259537793 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76398705481279266001 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w132S0 : Ball := ⟨(96994224547960905945108534835223 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w132S1 : Ball := ⟨(94078795956602620092267323084229 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w132S2 : Ball := ⟨(44254099243220347496675849573353 / 50000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w132S3 : Ball := ⟨(19584252998287957330207278722603 / 25000000000000000000000000000000), (1 / 4000000000000000000000000000000)⟩
def w132S4 : Ball := ⟨(30683437240076067713511909439451 / 50000000000000000000000000000000), (1 / 2500000000000000000000000000000)⟩
def w132S5 : Ball := ⟨(18829466417313737108541434657059 / 50000000000000000000000000000000), (1 / 2000000000000000000000000000000)⟩
abbrev w132 : Ball := w132S5

def w133Trace : List Ball := [
  ⟨(19698237181233974226695784257421 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(99243681403009504067162423047577 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49747574724965816753961896151159 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2075439054751763585102601018221 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4154029428328582830560067150571 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(415613182753014137113242050419 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(69293905933979333421557492131 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9901813637992914146726565323 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19343558727653122501613153 / 781250000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(55030962636043294042180751 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27519280387580600348246631 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2502040626863904908411169 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(52130921772118710693391 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16041622377382743254249 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1145913056616409135853 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9549871790859901599 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w133S0 : Ball := ⟨(3031410531626160831128468628201 / 3125000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w133S1 : Ball := ⟨(4704998303362049554717277293211 / 5000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w133S2 : Ball := ⟨(88548036138559059560897881994989 / 100000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w133S3 : Ball := ⟨(3136301881598224482979069072333 / 4000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
def w133S4 : Ball := ⟨(61477434328228520648830538515059 / 100000000000000000000000000000000), (21 / 50000000000000000000000000000000)⟩
def w133S5 : Ball := ⟨(18897374657908252689730974924039 / 50000000000000000000000000000000), (13 / 25000000000000000000000000000000)⟩
abbrev w133 : Ball := w133S5

def w134Trace : List Ball := [
  ⟨(2462572060724088118539873811751 / 2500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49624779649023418550819889122341 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49749538973485006727837365175439 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3320800848758974397847240267641 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4154127888745451994561612825323 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(83124278740184277472907172777 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27718031824196343623936763217 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19803920805944612833151708589 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2476008142546737050064139399 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(137579038309280585573460337 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27519577131815894172116389 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(625516340086952234363879 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208525589980555379304401 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8020879158918101933277 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(572961060216639165977 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(38199770944906216897 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w134S0 : Ball := ⟨(97028178468142111038605217486369 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w134S1 : Ball := ⟨(4707233708422818188728069977837 / 5000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w134S2 : Ball := ⟨(44316098371424074649702657023267 / 50000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w134S3 : Ball := ⟨(15711332598925884171415363747159 / 20000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
def w134S4 : Ball := ⟨(61711493008517794483379527494103 / 100000000000000000000000000000000), (21 / 50000000000000000000000000000000)⟩
def w134S5 : Ball := ⟨(9520770923350851573363953693631 / 25000000000000000000000000000000), (53 / 100000000000000000000000000000000)⟩
abbrev w134 : Ball := w134S5

def w135Trace : List Ball := [
  ⟨(49252287730902365926521024861231 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(99250410084514322726650231009489 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(24874911641130014256136687437887 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4151018857035718970886655592261 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(830828427983534194686888944909 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(831245164301280065189468314619 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138590498860737489585565900353 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19803963291184854726403885017 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(619003216177314834593132001 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27515854896415275628784243 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27519620082125495400569129 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(625517235057890730904323 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208525865401817949628543 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8020888996803157973523 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1145923432312676293871 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(38199812018539542101 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w135S0 : Ball := ⟨(485157569345519145080467474597 / 500000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w135S1 : Ball := ⟨(18830229367460177444782343866819 / 20000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w135S2 : Ball := ⟨(17728876901557985717937739404441 / 20000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w135S3 : Ball := ⟨(78578269047649071003244981757131 / 100000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
def w135S4 : Ball := ⟨(61745443665247240400566020662961 / 100000000000000000000000000000000), (21 / 50000000000000000000000000000000)⟩
def w135S5 : Ball := ⟨(19062499067091102843373918268659 / 50000000000000000000000000000000), (53 / 100000000000000000000000000000000)⟩
abbrev w135 : Ball := w135S5

def w136Trace : List Ball := [
  ⟨(98507653777886351512215597892381 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49625978496972619358932627500577 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49750340213555774765274529695703 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16604204855482089808199209679923 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4154168051348767475753140550329 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(207812371491621172832191480199 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1385911165731197010207985061 / 1000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(154719066699151963052261659 / 781250000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2476021450500841676934177823 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2149682873266383558132031 / 781250000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3439962271739050896171461 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(20016603593082763577931 / 800000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208526366169480969433131 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2005226720981152313997 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(572962908777589937977 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19099943348936430327 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w136S0 : Ball := ⟨(48518789264119635907549473128633 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w136S1 : Ball := ⟨(18832583293248406723756918876121 / 20000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w136S2 : Ball := ⟨(44333274187142375560056067392449 / 50000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
def w136S3 : Ball := ⟨(15723513601218755683616055299239 / 20000000000000000000000000000000), (11 / 50000000000000000000000000000000)⟩
def w136S4 : Ball := ⟨(12361443998385560156715702538411 / 20000000000000000000000000000000), (7 / 20000000000000000000000000000000)⟩
def w136S5 : Ball := ⟨(38201324431305596143587794426509 / 100000000000000000000000000000000), (11 / 25000000000000000000000000000000)⟩
abbrev w136 : Ball := w136S5

def w137Trace : List Ball := [
  ⟨(3945992911094184385146488487171 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19864676379150570980601935753199 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(24887102684952463337575033894429 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16610179685154819299305358060997 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4155364157193369553015805474529 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(83144897274829341799438654809 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138619629244315611140912937411 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3961521207514891004703653933 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1238208871554436646363224857 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(68799761836448110413039371 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27523302552015806780006103 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2502375869063641199169921 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(104274739513772076700317 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16043464911215550636677 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1146035906652981165281 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3820333314910551187 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w137S0 : Ball := ⟨(24329468835008680864435539425383 / 25000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w137S1 : Ball := ⟨(94707688606985385418638513278391 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w137S2 : Ball := ⟨(44847731406388546870037947562603 / 50000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w137S3 : Ball := ⟨(80452760491982785126734347652019 / 100000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
def w137S4 : Ball := ⟨(32363233353901730569562584859337 / 50000000000000000000000000000000), (43 / 100000000000000000000000000000000)⟩
def w137S5 : Ball := ⟨(837903098495277965038710547121 / 2000000000000000000000000000000), (57 / 100000000000000000000000000000000)⟩
abbrev w137 : Ball := w137S5

def w138Trace : List Ball := [
  ⟨(6166808627015515156832554081011 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19866596533608320756404995579463 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49777412832716135669777768857069 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16610982633124203747927697233667 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(519440611403572003162028292909 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(831475778961988161973158462283 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(69311730274073558215480263067 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1980808512998301924838528021 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2476470991553882198208181469 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(275204373496116456863974739 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(550475736929029345669333 / 2000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2502416233912191723184243 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208552584476130919475207 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4010921689366983524143 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4476760539202571951 / 390625000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19101898080486043449 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w138S0 : Ball := ⟨(19471118664823287365124477809939 / 20000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w138S1 : Ball := ⟨(23695278878726862303656187951393 / 25000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w138S2 : Ball := ⟨(89834598582502295818656978221721 / 100000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
def w138S3 : Ball := ⟨(80702551024793234972011857108923 / 100000000000000000000000000000000), (11 / 50000000000000000000000000000000)⟩
def w138S4 : Ball := ⟨(2605160696763742248072898176901 / 4000000000000000000000000000000), (9 / 25000000000000000000000000000000)⟩
def w138S5 : Ball := ⟨(10604472274941479671393272450057 / 25000000000000000000000000000000), (3 / 6250000000000000000000000000000)⟩
abbrev w138 : Ball := w138S5

def w139Trace : List Ball := [
  ⟨(98786948763039870536244696392459 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(99392240641977065267365805764431 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49797207673112050811148932372867 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16615937678695107011225615332849 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2078258372922684642316787456369 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(831641188788929010520896493981 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(34661775330263941875546574871 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2476380159601806546691480273 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2476799545698232446298002889 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(275237236553390853486075827 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27526774976258346598170997 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2502665285575239381288737 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208571744989988167781777 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16045055532378195699337 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(286535489815263603741 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76413305290943043093 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w139S0 : Ball := ⟨(97588612459114646074113179035643 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w139S1 : Ball := ⟨(38094149126781065317096667143 / 40000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w139S2 : Ball := ⟨(90697762355839662575616493377227 / 100000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
def w139S3 : Ball := ⟨(20565210240890915448772522252833 / 25000000000000000000000000000000), (11 / 50000000000000000000000000000000)⟩
def w139S4 : Ball := ⟨(33834229780163566769674837637283 / 50000000000000000000000000000000), (37 / 100000000000000000000000000000000)⟩
def w139S5 : Ball := ⟨(5723775524084535798695641695481 / 12500000000000000000000000000000), (51 / 100000000000000000000000000000000)⟩
abbrev w139 : Ball := w139S5

def w140Trace : List Ball := [
  ⟨(12351320980135496203127894302893 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(99404097898440773045858079026919 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9960233611854407172912755883313 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1661692897178075825008894925543 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1039178791034910766836613449707 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(166334855505226000651246681037 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13865183032255566066126325609 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19811632600322024768922041187 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(247686526594444510163310767 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(275243810021211353109516679 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13763686336800351676427829 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1251357550699913280821553 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(52143894371278471916531 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(641813172540848057587 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(35817506660781299863 / 3125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9551805985592852119 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w140S0 : Ball := ⟨(97635283170774575739408745135457 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w140S1 : Ball := ⟨(19065297039674674184416339773851 / 20000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w140S2 : Ball := ⟨(90871387802756973745585087630589 / 100000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
def w140S3 : Ball := ⟨(82576091211990489007865629761863 / 100000000000000000000000000000000), (11 / 50000000000000000000000000000000)⟩
def w140S4 : Ball := ⟨(34094054199254864339179956738849 / 50000000000000000000000000000000), (37 / 100000000000000000000000000000000)⟩
def w140S5 : Ball := ⟨(46496181269669129951514099374759 / 100000000000000000000000000000000), (51 / 100000000000000000000000000000000)⟩
abbrev w140 : Ball := w140S5

def w141Trace : List Ball := [
  ⟨(98821684655275165061384461607367 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(99409678437107086832842680106093 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49803031934018511334126645412663 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16617395495406373076581457407793 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2078404271459787612347345483727 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(83168984947779104430061264121 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(69327027916363365472003886047 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4952977720266974845897533251 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(495379238841096947026827739 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(275246903516618916616507069 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13763826975586181241913967 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2502738544774324807119257 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208577381057490778672597 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3209091630944769746439 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(286542200849266906361 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76414985575942710533 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w141S0 : Ball := ⟨(48828626790533235094367468405857 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w141S1 : Ball := ⟨(95369391769967199157147337259171 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w141S2 : Ball := ⟨(90953208865734873400351974812597 / 100000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w141S3 : Ball := ⟨(82724862029739927759686318982053 / 100000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
def w141S4 : Ball := ⟨(1710850699459876710126125776327 / 2500000000000000000000000000000), (11 / 25000000000000000000000000000000)⟩
def w141S5 : Ball := ⟨(23416080926738795065261535309587 / 50000000000000000000000000000000), (61 / 100000000000000000000000000000000)⟩
abbrev w141 : Ball := w141S5

def w142Trace : List Ball := [
  ⟨(49415165965497648626025178275289 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49707009572577009209015392272913 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49804481686776655041208219212643 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8308879180806160267379794416249 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2078440586638879443594277149251 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(831701961341431456307027307469 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13865578682831358523716554491 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19812127326453431222170006133 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2476920250000322776840474503 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(275249309612313998592019347 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1720492045391277203473283 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(156422298674397859148959 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8343151354241295713121 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16045558365883407305289 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(229235096957574189281 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76415403780209294429 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w142S0 : Ball := ⟨(97674345095907086404792978385569 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w142S1 : Ball := ⟨(23850694224785871750228218178689 / 25000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w142S2 : Ball := ⟨(18203379680135492345746030796811 / 20000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w142S3 : Ball := ⟨(82840757944792434906679005267601 / 100000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
def w142S4 : Ball := ⟨(34312955884338454618588856808207 / 50000000000000000000000000000000), (11 / 25000000000000000000000000000000)⟩
def w142S5 : Ball := ⟨(23547578830411139564977310630337 / 50000000000000000000000000000000), (61 / 100000000000000000000000000000000)⟩
abbrev w142 : Ball := w142S5

def w143Trace : List Ball := [
  ⟨(19767734218411076979536138933993 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49709102533744894695315369931931 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49805879722650453450551964570403 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4154527070081253064698457562269 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(259809450731163230994309350403 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(415856820462492060255411887353 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138657456038455886357158576953 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9906168022814447586102169551 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(619235861764496471630406411 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(275251629812243741768482487 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13764041845485917906504221 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(156423397613990580785859 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1629532316962670499911 / 781250000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3209130999835904607683 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1146181927626885904997 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(15283161409721842923 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w143S0 : Ball := ⟨(24422707258108762029586638939331 / 25000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w143S1 : Ball := ⟨(95434980770444544797243626288949 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w143S2 : Ball := ⟨(45539177773275600206264478339293 / 50000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w143S3 : Ball := ⟨(82952668490639938124151322006801 / 100000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
def w143S4 : Ball := ⟨(8601431512147510037792604593567 / 12500000000000000000000000000000), (11 / 25000000000000000000000000000000)⟩
def w143S5 : Ball := ⟨(47350159397225088716053119586929 / 100000000000000000000000000000000), (61 / 100000000000000000000000000000000)⟩
abbrev w143 : Ball := w143S5

def w144Trace : List Ball := [
  ⟨(98843149820809675677763590955863 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(99420453159904332782503261480827 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49806630544007925231356606992157 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8309148102251097887187560428321 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(519623603217090289153171049013 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(83171991341001560392519077747 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138658352480642785176747113289 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19812448137170186084428143377 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2476955904898525401423517829 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(275252875860218165200775723 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27528196988058875771502629 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2502783804658187709816261 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208580863036104111847467 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8022853447643472845811 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1146185387698147035497 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(38208011809337919209 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w144S0 : Ball := ⟨(97699682664990278210462489014863 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w144S1 : Ball := ⟨(19090455985679603741438997227579 / 20000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w144S2 : Ball := ⟨(91111377435292552712956713879161 / 100000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w144S3 : Ball := ⟨(83012830981563369405247503332129 / 100000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
def w144S4 : Ball := ⟨(68911301075736072007966723622513 / 100000000000000000000000000000000), (11 / 25000000000000000000000000000000)⟩
def w144S5 : Ball := ⟨(9497534831901487030266582364531 / 20000000000000000000000000000000), (61 / 100000000000000000000000000000000)⟩
abbrev w144 : Ball := w144S5

def w145Trace : List Ball := [
  ⟨(49430687853352556168317098843489 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49714800635061270606775377291173 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49809685785451442669875435570799 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16619060896585713095882280623357 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4157141881813383176696284311351 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(831745436771924352714518679499 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138662000177615990727436001387 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(990645212270806544752681137 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2477006596585433191989922847 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(68814486523061083154283169 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13764328999408330017869443 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2502822227903887947031927 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208583819045124232896907 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8022959030994979732851 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1146199466811200103977 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(38208452417404498671 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w145S0 : Ball := ⟨(97735716066223037496903551134477 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w145S1 : Ball := ⟨(95522701949773679752949234014577 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w145S2 : Ball := ⟨(91245865877852963594914898493647 / 100000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w145S3 : Ball := ⟨(1665161607959826356537772944251 / 2000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
def w145S4 : Ball := ⟨(1732976987889596529067532836753 / 2500000000000000000000000000000), (11 / 25000000000000000000000000000000)⟩
def w145S5 : Ball := ⟨(48051347848878380719513662951177 / 100000000000000000000000000000000), (31 / 50000000000000000000000000000000)⟩
abbrev w145 : Ball := w145S5

def w146Trace : List Ball := [
  ⟨(98876515013933829975835704073047 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(99437199707142693329435678778847 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49812223403218955768381355488573 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16619696022661915120444265981683 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2078634501662355800189215764719 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(831766635161283698585325380469 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27733005949710032878580827921 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19813283061372379675043499031 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(247704869788071092111372131 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(275262157092008307913144603 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2752904088291842234190253 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19553547965335576445021 / 781250000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(104293137047405561278861 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4011523360417474415799 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1146211159880907089699 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1910440917306887979 / 2500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w146S0 : Ball := ⟨(97765652213006820974204888804239 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w146S1 : Ball := ⟨(2986913360198314222297730641439 / 3125000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w146S2 : Ball := ⟨(18271542110886265651522624782247 / 20000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w146S3 : Ball := ⟨(16692462555494506622283495772909 / 20000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
def w146S4 : Ball := ⟨(69659576541646548644144525091763 / 100000000000000000000000000000000), (11 / 25000000000000000000000000000000)⟩
def w146S5 : Ball := ⟨(379098172184493291735152239011 / 781250000000000000000000000000), (31 / 50000000000000000000000000000000)⟩
abbrev w146 : Ball := w146S5

def w147Trace : List Ball := [
  ⟨(49440111476385135576824748327097 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(99439060666994097636231738770073 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1992513795608588943036976201767 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8309925784832587165837433864839 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(519662517013929068869698204401 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(831771826744808388207556560761 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138665771701951558276277847439 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19813375834590202868192941317 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(619264752149596817501396397 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(68815797093778575819578573 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27529134651942011689426399 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2502861954777651783514457 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8343475013586014453073 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16046136392341087522777 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1146214023523980717931 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76417815922675483687 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w147S0 : Ball := ⟨(97772984911895567611173062729087 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w147S1 : Ball := ⟨(764764526286540665199184831663 / 800000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w147S2 : Ball := ⟨(45692560989552886569036259340553 / 50000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w147S3 : Ball := ⟨(4175620259568020529345364322599 / 5000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
def w147S4 : Ball := ⟨(69743218208459612564189847472473 / 100000000000000000000000000000000), (11 / 25000000000000000000000000000000)⟩
def w147S5 : Ball := ⟨(4864116486072812449975073121731 / 10000000000000000000000000000000), (31 / 50000000000000000000000000000000)⟩
abbrev w147 : Ball := w147S5

def w148Trace : List Ball := [
  ⟨(9889011146948314339378418154309 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49722011726920637545717752514509 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9962900449155367254130667266649 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3324053274613601757857055767129 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2078691579388285140983355162671 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(831785671239211284890390374907 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27733550055665994777642262157 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(247670290420176397230942857 / 1250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1238543252111638980410081187 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(137632969248873488898058811 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13764692352767351732574913 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(500576559114092116499943 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208588478674958533321787 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16046250928513529469581 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(229244331994245641307 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(38209146935204361213 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w148S0 : Ball := ⟨(24448135366117003865237226941473 / 25000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w148S1 : Ball := ⟨(95633811660796961060374973094347 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w148S2 : Ball := ⟨(18291651865545569606994286557393 / 20000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
def w148S3 : Ball := ⟨(522788324953619870099728693281 / 625000000000000000000000000000), (11 / 50000000000000000000000000000000)⟩
def w148S4 : Ball := ⟨(69966753973199780903541916026673 / 100000000000000000000000000000000), (37 / 100000000000000000000000000000000)⟩
def w148S5 : Ball := ⟨(48953466615462673273822816782719 / 100000000000000000000000000000000), (53 / 100000000000000000000000000000000)⟩
abbrev w148 : Ball := w148S5

def w149Trace : List Ball := [
  ⟨(98910818754290297702077778422709 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19890883071884989889291534012451 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(24908986301043826099806759891327 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3324226984274578177981091142857 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(519694624554438884419585702749 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(831814659429245033298311969157 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(69335946541340563733319522961 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9907070621555664876580075541 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(495428814993504656182508379 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(68817924182208653277028623 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1376495413436637089267857 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1251463216009079398495837 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(26073979466549642043503 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(40116226858919319521 / 250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(286559412273061286747 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(15283858914695038207 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w149S0 : Ball := ⟨(97833500666440652793059199343149 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w149S1 : Ball := ⟨(23928484631626109135506645132787 / 25000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w149S2 : Ball := ⟨(3664463211302188107609541898023 / 4000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w149S3 : Ball := ⟨(41963408209334827898015839150367 / 50000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
def w149S4 : Ball := ⟨(35218552570865392544190245371007 / 50000000000000000000000000000000), (11 / 25000000000000000000000000000000)⟩
def w149S5 : Ball := ⟨(24806928903736187010464986272311 / 50000000000000000000000000000000), (63 / 100000000000000000000000000000000)⟩
abbrev w149 : Ball := w149S5

end MatrixMultiplication.NativeNumerics

namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def Z0_2_6Den : Ball := ⟨(4292524407740908366058292728641 / 2500000000000000000000000000000), (51 / 50000000000000000000000000000000)⟩
def Z0_2_6E_2_5LogWitness : LogWitness := ⟨-3, 9657537875187848339599195720457, 6250000000000000000000000000000⟩
def Z0_2_6E_2_5Log : Ball := ⟨(-32885685360713365998269732360853 / 20000000000000000000000000000000), (42351647467 / 50000000000000000000000000000000)⟩
def Z0_2_6E_2_5 : Ball := ⟨(1984967199516249315866366927071 / 6250000000000000000000000000000), (4090126411 / 25000000000000000000000000000000)⟩
def Z0_2_6E_3_5LogWitness : LogWitness := ⟨-6, 312906143484347380943417643667, 312500000000000000000000000000⟩
def Z0_2_6E_3_5Log : Ball := ⟨(-83151685360713365998269720903561 / 20000000000000000000000000000000), (37057691509 / 25000000000000000000000000000000)⟩
def Z0_2_6E_3_5 : Ball := ⟨(101635442150174547299056890093 / 1562500000000000000000000000000), (463823177 / 20000000000000000000000000000000)⟩
def Z0_2_6E_4_4LogWitness : LogWitness := ⟨-1, 58240787064405132832169040681501, 50000000000000000000000000000000⟩
def Z0_2_6E_4_4Log : Ball := ⟨(-54058426803566829991348699995259 / 100000000000000000000000000000000), (42351647427 / 100000000000000000000000000000000)⟩
def Z0_2_6E_4_4 : Ball := ⟨(6296810649006533489546320818881 / 20000000000000000000000000000000), (1541620801 / 6250000000000000000000000000000)⟩
def Z0_2_6E_5_2LogWitness : LogWitness := ⟨-3, 9657537875187848339599195720457, 6250000000000000000000000000000⟩
def Z0_2_6E_5_2Log : Ball := ⟨(-32885685360713365998269732360853 / 20000000000000000000000000000000), (42351647467 / 50000000000000000000000000000000)⟩
def Z0_2_6E_5_2 : Ball := ⟨(1984967199516249315866366927071 / 6250000000000000000000000000000), (4090126411 / 25000000000000000000000000000000)⟩
def Z0_2_6E_5_3LogWitness : LogWitness := ⟨-6, 312906143484347380943417643667, 312500000000000000000000000000⟩
def Z0_2_6E_5_3Log : Ball := ⟨(-83151685360713365998269720903561 / 20000000000000000000000000000000), (37057691509 / 25000000000000000000000000000000)⟩
def Z0_2_6E_5_3 : Ball := ⟨(101635442150174547299056890093 / 1562500000000000000000000000000), (463823177 / 20000000000000000000000000000000)⟩
def Z0_2_6Entropy : Ball := ⟨(108012340224774987609734627692581 / 100000000000000000000000000000000), (31012587937 / 50000000000000000000000000000000)⟩
def Z0_2_6Labels : Ball := ⟨(394723297085604726721740039214937 / 100000000000000000000000000000000), (128557238001 / 100000000000000000000000000000000)⟩
def Z0_2_6Four : Ball := ⟨(251367818655189857165737333453759 / 50000000000000000000000000000000), (1524659311 / 800000000000000000000000000000)⟩
def Z0_2_6H2E_2_5LogWitness : LogWitness := ⟨-3, 9657537875187848339599195720457, 6250000000000000000000000000000⟩
def Z0_2_6H2E_2_5Log : Ball := ⟨(-32885685360713365998269732360853 / 20000000000000000000000000000000), (42351647467 / 50000000000000000000000000000000)⟩
def Z0_2_6H2E_2_5 : Ball := ⟨(1984967199516249315866366927071 / 6250000000000000000000000000000), (4090126411 / 25000000000000000000000000000000)⟩
def Z0_2_6H2E_3_5LogWitness : LogWitness := ⟨-6, 312906143484347380943417643667, 312500000000000000000000000000⟩
def Z0_2_6H2E_3_5Log : Ball := ⟨(-83151685360713365998269720903561 / 20000000000000000000000000000000), (37057691509 / 25000000000000000000000000000000)⟩
def Z0_2_6H2E_3_5 : Ball := ⟨(101635442150174547299056890093 / 1562500000000000000000000000000), (463823177 / 20000000000000000000000000000000)⟩
def Z0_2_6H2E_4_4LogWitness : LogWitness := ⟨-1, 58240787064405132832169040681501, 50000000000000000000000000000000⟩
def Z0_2_6H2E_4_4Log : Ball := ⟨(-54058426803566829991348699995259 / 100000000000000000000000000000000), (42351647427 / 100000000000000000000000000000000)⟩
def Z0_2_6H2E_4_4 : Ball := ⟨(6296810649006533489546320818881 / 20000000000000000000000000000000), (1541620801 / 6250000000000000000000000000000)⟩
def Z0_2_6H2E_5_2LogWitness : LogWitness := ⟨-3, 9657537875187848339599195720457, 6250000000000000000000000000000⟩
def Z0_2_6H2E_5_2Log : Ball := ⟨(-32885685360713365998269732360853 / 20000000000000000000000000000000), (42351647467 / 50000000000000000000000000000000)⟩
def Z0_2_6H2E_5_2 : Ball := ⟨(1984967199516249315866366927071 / 6250000000000000000000000000000), (4090126411 / 25000000000000000000000000000000)⟩
def Z0_2_6H2E_5_3LogWitness : LogWitness := ⟨-6, 312906143484347380943417643667, 312500000000000000000000000000⟩
def Z0_2_6H2E_5_3Log : Ball := ⟨(-83151685360713365998269720903561 / 20000000000000000000000000000000), (37057691509 / 25000000000000000000000000000000)⟩
def Z0_2_6H2E_5_3 : Ball := ⟨(101635442150174547299056890093 / 1562500000000000000000000000000), (463823177 / 20000000000000000000000000000000)⟩
def Z0_2_6H2Entropy : Ball := ⟨(108012340224774987609734627692581 / 100000000000000000000000000000000), (31012587937 / 50000000000000000000000000000000)⟩
def Z0_2_6H2Mass : Ball := ⟨(99999999999999999999999999999999 / 100000000000000000000000000000000), (61 / 50000000000000000000000000000000)⟩
def Z0_2_6H2MassTermLogWitness : LogWitness := ⟨-1, 99999999999999999999999999999999, 50000000000000000000000000000000⟩
def Z0_2_6H2MassTermLog : Ball := ⟨0, (165436123 / 390625000000000000000000000000)⟩
def Z0_2_6H2MassTerm : Ball := ⟨0, (42351647489 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitB1_3_4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
def w0Trace : List Ball := [
  ⟨(82803229229590362204618185520663 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(91131351271525777834266467390707 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(46997890090448805051498392563943 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(7954584508208846431402785290537 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2007114747699524859116922641299 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(807814768661711078885531885437 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(135231277551032895972451160501 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19382886944007911455826332437 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2429121919745260254778172879 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(270460864988165426258764137 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27091905614671088604436493 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(308297497269058241696333 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(205777516359127300804089 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3169055647121571503399 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1132814314621218288769 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(75569735009710001443 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w0S0 : Ball := ⟨(68563747708480877283556233637117 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w0S1 : Ball := ⟨(23504937499161083753803736016069 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
def w0S2 : Ball := ⟨(22099283473578756085261927404661 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w0S3 : Ball := ⟨(4883783300455911313091891409461 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w0S4 : Ball := ⟨(238513393258120341145263563873 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def w0S5 : Ball := ⟨(22755455505401106321749899 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
abbrev w0 : Ball := w0S5

def w1Trace : List Ball := [
  ⟨(20837493786076897713733962490031 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(91422432674232072040023473511219 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(47097951993783986464978611101937 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(15934648192129657873450890498811 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2009693987987463870597027863499 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(808682047072812782498592987079 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13535598763476683311513428167 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19398555248358033727439975123 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(24308699485539973844509053 / 1000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(270636251711842821073819 / 100000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(5421578849894978790169157 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2467715503758110889817791 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(25735057077891513366681 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(15852644036027428658163 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(56665296465398772451 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(37800594972451887961 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w1S0 : Ball := ⟨(69472183565566932009629442199157 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w1S1 : Ball := ⟨(48263842893678281185090233240803 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
def w1S2 : Ball := ⟨(23293985308656595225584058076917 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w1S3 : Ball := ⟨(5426097515599092939405471064157 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w1S4 : Ball := ⟨(294425342487906486448830565873 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def w1S5 : Ball := ⟨(216715705747802581278708373 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
abbrev w1 : Ball := w1S5
def w2S5 : Ball := ⟨(1121736896394660095916143067 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
abbrev w2 : Ball := w2S5

def w10Trace : List Ball := [
  ⟨(88726973040179621243745661716269 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(94251152927379453467141878319327 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(24032385734945065717126494981129 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1011249689141385047680937470733 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4068948239782669415450004786023 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(817001008592755405479746088881 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(68275381681885051381458930667 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19548522966975271994323269517 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(244758843534154172978419041 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(10892505974290951834362609 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27260639662100522894982223 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1240234360183384052150687 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(206863087651387558792599 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3184586469843224747037 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(227599289511193376947 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9487497744688913257 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w10S0 : Ball := ⟨(78724757448727613401024974552239 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w10S1 : Ball := ⟨(61975874353609938497277403736921 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
def w10S2 : Ball := ⟨(19205045009472230559750080190707 / 50000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w10S3 : Ball := ⟨(14753350152634169135618964376373 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w10S4 : Ball := ⟨(2176613407262306617311576838851 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w10S5 : Ball := ⟨(4737645924674027849039197649 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
abbrev w10 : Ball := w10S5

def w11Trace : List Ball := [
  ⟨(88952403628367317885077802409629 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(94368449066319424397392110109409 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(12026161835845551444360450356289 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16190081952850732775042003735789 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(407098148580158147776125508197 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(408670891527778287994924284649 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(136599650015710916393014908209 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9777326883467930151615955069 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1224135708009101346898124833 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(136190546753627526277973687 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13633436474737510948164299 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2480988944623298328791599 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(10345157832843328690881 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(7962898817209613899869 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1138187623959312794013 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(75912109881242239047 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w11S0 : Ball := ⟨(39562650556319875899652914593389 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def w11S1 : Ball := ⟨(3130406638082954772029222168163 / 5000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
def w11S2 : Ball := ⟨(39197782879015309528139956418363 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w11S3 : Ball := ⟨(15364661826304257277610201392047 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
def w11S4 : Ball := ⟨(2360728330366912746332528641641 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def w11S5 : Ball := ⟨(55730382497969515299452328931 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
abbrev w11 : Ball := w11S5

def w12Trace : List Ball := [
  ⟨(89524643700483357732777803369781 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(23666436146888771007562149969429 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(48205640553018161827744931915587 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1013476106739247767441439189163 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4076127275582738323444357097393 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(818204042554562830588507827383 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(136723328133480962393226825867 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3914032429994557913650721079 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2449998904689538110930602167 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(34069274746333858005712017 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13641318358375792058184949 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2482304499152162992939139 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(25875559889306845033687 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(15933042771883463632687 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1138671018927091481099 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(15188551655927234631 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w12S0 : Ball := ⟨(10018327287123118184516723688243 / 12500000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w12S1 : Ball := ⟨(8029350530553252552316379660391 / 12500000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w12S2 : Ball := ⟨(4126110076319731087912757753237 / 10000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
def w12S3 : Ball := ⟨(8512392180953608551498385558867 / 50000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
def w12S4 : Ball := ⟨(1449216412847202647080426765947 / 50000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
def w12S5 : Ball := ⟨(84009128450628548223813961263 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
abbrev w12 : Ball := w12S5

def w13Trace : List Ball := [
  ⟨(44901791464017030681414471508929 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(18962085533883103714392120962301 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4825475150843493460525669297297 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(405700734647329560445348798217 / 2500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4078627608929810389018254403109 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(409311459933952387038776160319 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8548962481180060297712308879 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9788846864004063986944790479 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(245083776442337545815108291 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(272638249438855836502179679 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27290290323002874006187047 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1241471593580690215439527 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(41410733513450800798327 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(15936559870305698358221 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(569452836523750122401 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(18989406733724974259 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w13S0 : Ball := ⟨(4032341753356145359013450261071 / 5000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w13S1 : Ball := ⟨(6503912006343725044680424107743 / 10000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
def w13S2 : Ball := ⟨(5287608923282757365729742560173 / 12500000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w13S3 : Ball := ⟨(17893637200370842028309167400449 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w13S4 : Ball := ⟨(1600911261292476327131451328027 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w13S5 : Ball := ⟨(51258337330661348248937258371 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
abbrev w13 : Ball := w13S5

def w14Trace : List Ball := [
  ⟨(44937165551513774167289640393557 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4742354990166387900379992898827 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(6033399425302295783271296917333 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8115586845607358870479032442409 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4079260948250966885525139266497 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2046822531505593118572174757 / 250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(136798613507522795153407911329 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4894900271036589794027902079 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2451050194790026198126357499 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(136329766820128318964016009 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27292228375345069922083449 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2483104912259425795876721 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(51766530633873004911209 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(159374504155278579473 / 1000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1138965087859557370499 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(37980695386649576051 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w14S0 : Ball := ⟨(80773953912166249728956297702401 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def w14S1 : Ball := ⟨(32622158153023786998166123019621 / 50000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
def w14S2 : Ball := ⟨(21284104051217926756826426760943 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w14S3 : Ball := ⟨(18120523410522854485465151020969 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w14S4 : Ball := ⟨(3283533686713068219880629244423 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w14S5 : Ball := ⟨(107815934717795136372966683321 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
abbrev w14 : Ball := w14S5

def w15Trace : List Ball := [
  ⟨(9000136829460554017574762996961 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2372823115740071449370936658997 / 2500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(965790551031331750079061873801 / 2000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16236815932682457950342178822143 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2040198675115272529684165323083 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(163783873033974069417347868233 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(136825909206572302366030687583 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19583023044490817024803085623 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2451431303875283914869816517 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(68174429411480088068328179 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27295705197500403753232741 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2483395039389976647746697 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(207088465888743077756911 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1593904797556048860921 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(569535836068292028571 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(18992035446257787321 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w15S0 : Ball := ⟨(40501231474506136795924592711447 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w15S1 : Ball := ⟨(65613990038061061589390297318687 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w15S2 : Ball := ⟨(43051956887147762304799225580421 / 100000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
def w15S3 : Ball := ⟨(18534709918128296435205018594573 / 100000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
def w15S4 : Ball := ⟨(3435354717491634411440934649917 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
def w15S5 : Ball := ⟨(4720664813996810911203188651 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
abbrev w15 : Ball := w15S5

def w16Trace : List Ball := [
  ⟨(90351223704156172151854589729257 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(47547020460593564806531326598257 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(48350947217965398497642396658833 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16252329614434459969645910535381 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1020880352908205850554698035137 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2560758108775855876308926241 / 312500000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(136900930980905630990563909833 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19592427563357126103791102221 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2452478639073234566388051329 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(272802647058997491437197581 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27305259104858567503778853 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(310524031078657363982219 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(103574929513877067467227 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(15943437503359929608153 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1139364523321913123181 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4749167791468384123 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w16S0 : Ball := ⟨(16326687249676944339346245159911 / 20000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def w16S1 : Ball := ⟨(66640179137190926257108098333817 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
def w16S2 : Ball := ⟨(173473182634253780653137407731 / 390625000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w16S3 : Ball := ⟨(493042812407925431552203605237 / 2500000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w16S4 : Ball := ⟨(972364859468466991536108553409 / 25000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w16S5 : Ball := ⟨(18909868398582631231235721921 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
abbrev w16 : Ball := w16S5

def w17Trace : List Ball := [
  ⟨(45298387821582375935784030576739 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(380884073883296707469593257181 / 400000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(48393983934946073715053224648977 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(101644978089202783813343165521 / 625000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2042854625182367400676623133467 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(819808965573905378088781124177 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(68476727947610728916578961251 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3919802268784215046179074659 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(245321178942121588147930871 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(272876094872061161066185861 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27311946257030064302904893 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2484750223125090802005549 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(41438565428432741000249 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(7973254785296611336431 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(28489236873692992587 / 2500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(37999828231845789303 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w17S0 : Ball := ⟨(16415551513875860080278918234063 / 20000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def w17S1 : Ball := ⟨(13473516575235602085088246311929 / 20000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
def w17S2 : Ball := ⟨(45383912225787126955534400596353 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w17S3 : Ball := ⟨(20596994889179502519454289981099 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w17S4 : Ball := ⟨(4242361984648865472725574887741 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w17S5 : Ball := ⟨(179976352087938606848633619383 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
abbrev w17 : Ball := w17S5

def w18Trace : List Ball := [
  ⟨(45360007189952907876077061392377 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(95284702585555789552892804828379 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4841556120139729325935096356287 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8134321855142162920660532638359 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(255425362264260689124577747797 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(81999257320815019863295196973 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(136979776998880271586274449413 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4900577600253144798227371873 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(613394786561453086090150581 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(54582579147670986175469991 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27315296737779666856987241 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2485029779274890971825417 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(207214354532091248898109 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(7974024336344950122371 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1139672154213748968831 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19001538391422573177 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w18S0 : Ball := ⟨(82301210090903179917621139406909 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w18S1 : Ball := ⟨(677348918242698340839922830867 / 1000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w18S2 : Ball := ⟨(45880155704455364119553636602897 / 100000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
def w18S3 : Ball := ⟨(21049886874650680890304787931221 / 100000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
def w18S4 : Ball := ⟨(886195474871182020280804328573 / 20000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
def w18S5 : Ball := ⟨(98167802460269975445626015323 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
abbrev w18 : Ball := w18S5

def w19Trace : List Ball := [
  ⟨(90728803307005652024631704752233 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(11911155397381487385849517734689 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(48417099446061195529885965703519 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1016814500916221214481706336367 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4086883959667915501678102784189 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(820005660588747941876068104281 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(136981653094391278688428376781 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9801272771993050541157941743 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2453605329483269685015774579 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(136457759336866684684239803 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13657767768234143639209679 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(497009940777164108780597 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(207215888826620846736333 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3987039591604536590003 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(284919868065247848863 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(15201323315511373547 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w19S0 : Ball := ⟨(82317157495213197391111925511083 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w19S1 : Ball := ⟨(33880572090458671407342062120323 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w19S2 : Ball := ⟨(9183145321414136539714874890989 / 20000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
def w19S3 : Ball := ⟨(843301579942103450950470771321 / 4000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
def w19S4 : Ball := ⟨(2222367358540149679447878177467 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
def w19S5 : Ball := ⟨(39511333410437777570960140193 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
abbrev w19 : Ball := w19S5
def w20S5 : Ball := ⟨(226812903725915115968880020279 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
abbrev w20 : Ball := w20S5

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Four0_1_7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def Z0_1_7E_4_5LogWitness : LogWitness := ⟨-1, 1, 1⟩
def Z0_1_7E_4_5Log : Ball := ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
def Z0_1_7E_4_5 : Ball := ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
def Z0_1_7E_5_4LogWitness : LogWitness := ⟨-1, 1, 1⟩
def Z0_1_7E_5_4Log : Ball := ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
def Z0_1_7E_5_4 : Ball := ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
def Z0_1_7Entropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def Z0_1_7Labels : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def Z0_1_7Four : Ball := ⟨(18723326709712443708970142577019 / 6250000000000000000000000000000), (63527471049 / 50000000000000000000000000000000)⟩
def Z0_1_7H2E_4_5LogWitness : LogWitness := ⟨-1, 1, 1⟩
def Z0_1_7H2E_4_5Log : Ball := ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
def Z0_1_7H2E_4_5 : Ball := ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
def Z0_1_7H2E_5_4LogWitness : LogWitness := ⟨-1, 1, 1⟩
def Z0_1_7H2E_5_4Log : Ball := ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
def Z0_1_7H2E_5_4 : Ball := ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
def Z0_1_7H2Entropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def Z0_1_7H2Mass : Ball := ⟨1, 0⟩
def Z0_1_7H2MassTermLog : Ball := .exact 0
def Z0_1_7H2MassTerm : Ball := ⟨0, 0⟩

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Four0_5_3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def Z0_5_3Den : Ball := ⟨(1244512297472617284129636959856319 / 50000000000000000000000000000000), (59 / 2500000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def Z0_5_3E_1_5LogWitness : LogWitness := ⟨-6, 2157810797800214543118318532199, 1562500000000000000000000000000⟩
def Z0_5_3E_1_5Log : Ball := ⟨(-5993868746542471569477025801103 / 1562500000000000000000000000000), (148230766059 / 100000000000000000000000000000000)⟩
def Z0_5_3E_1_5 : Ball := ⟨(8277526209207412807813577207303 / 100000000000000000000000000000000), (6397079 / 200000000000000000000000000000)⟩
def Z0_5_3E_2_4LogWitness : LogWitness := ⟨-2, 4382455112007387232015528108533, 2500000000000000000000000000000⟩
def Z0_5_3E_2_4Log : Ball := ⟨(-41248799889359090223264863826827 / 50000000000000000000000000000000), (63527471247 / 100000000000000000000000000000000)⟩
def Z0_5_3E_2_4 : Ball := ⟨(18077101393929149380776110958019 / 50000000000000000000000000000000), (5568125837 / 20000000000000000000000000000000)⟩
def Z0_5_3E_3_4LogWitness : LogWitness := ⟨-5, 4017638082125913136726400382471, 3125000000000000000000000000000⟩
def Z0_5_3E_3_4Log : Ball := ⟨(-321447599778718180446529670366099 / 100000000000000000000000000000000), (127054942197 / 100000000000000000000000000000000)⟩
def Z0_5_3E_3_4 : Ball := ⟨(1614325147848684263111295424987 / 12500000000000000000000000000000), (5104607757 / 100000000000000000000000000000000)⟩
def Z0_5_3E_4_2LogWitness : LogWitness := ⟨-2, 4382455112007387232015528108533, 2500000000000000000000000000000⟩
def Z0_5_3E_4_2Log : Ball := ⟨(-41248799889359090223264863826827 / 50000000000000000000000000000000), (63527471247 / 100000000000000000000000000000000)⟩
def Z0_5_3E_4_2 : Ball := ⟨(18077101393929149380776110958019 / 50000000000000000000000000000000), (5568125837 / 20000000000000000000000000000000)⟩
def Z0_5_3E_4_3LogWitness : LogWitness := ⟨-5, 4017638082125913136726400382471, 3125000000000000000000000000000⟩
def Z0_5_3E_4_3Log : Ball := ⟨(-321447599778718180446529670366099 / 100000000000000000000000000000000), (127054942197 / 100000000000000000000000000000000)⟩
def Z0_5_3E_4_3 : Ball := ⟨(1614325147848684263111295424987 / 12500000000000000000000000000000), (5104607757 / 100000000000000000000000000000000)⟩
def Z0_5_3E_5_1LogWitness : LogWitness := ⟨-6, 2157810797800214543118318532199, 1562500000000000000000000000000⟩
def Z0_5_3E_5_1Log : Ball := ⟨(-5993868746542471569477025801103 / 1562500000000000000000000000000), (148230766059 / 100000000000000000000000000000000)⟩
def Z0_5_3E_5_1 : Ball := ⟨(8277526209207412807813577207303 / 100000000000000000000000000000000), (6397079 / 200000000000000000000000000000)⟩
def Z0_5_3Entropy : Ball := ⟨(57346330179855185674256162523237 / 50000000000000000000000000000000), (18071888221 / 25000000000000000000000000000000)⟩
def Z0_5_3Labels : Ball := ⟨(517959714589889087433695657320217 / 100000000000000000000000000000000), (160646509059 / 100000000000000000000000000000000)⟩
def Z0_5_3Four : Ball := ⟨(632652374949599458782207982366691 / 100000000000000000000000000000000), (232934061943 / 100000000000000000000000000000000)⟩
def Z0_5_3H2E_4_0LogWitness : LogWitness := ⟨-6, 2157810797800214543118318532199, 1562500000000000000000000000000⟩
def Z0_5_3H2E_4_0Log : Ball := ⟨(-5993868746542471569477025801103 / 1562500000000000000000000000000), (148230766059 / 100000000000000000000000000000000)⟩
def Z0_5_3H2E_4_0 : Ball := ⟨(8277526209207412807813577207303 / 100000000000000000000000000000000), (6397079 / 200000000000000000000000000000)⟩
def Z0_5_3H2E_2_1LogWitness : LogWitness := ⟨-2, 4382455112007387232015528108533, 2500000000000000000000000000000⟩
def Z0_5_3H2E_2_1Log : Ball := ⟨(-41248799889359090223264863826827 / 50000000000000000000000000000000), (63527471247 / 100000000000000000000000000000000)⟩
def Z0_5_3H2E_2_1 : Ball := ⟨(18077101393929149380776110958019 / 50000000000000000000000000000000), (5568125837 / 20000000000000000000000000000000)⟩
def Z0_5_3H2E_3_1LogWitness : LogWitness := ⟨-5, 4017638082125913136726400382471, 3125000000000000000000000000000⟩
def Z0_5_3H2E_3_1Log : Ball := ⟨(-321447599778718180446529670366099 / 100000000000000000000000000000000), (127054942197 / 100000000000000000000000000000000)⟩
def Z0_5_3H2E_3_1 : Ball := ⟨(1614325147848684263111295424987 / 12500000000000000000000000000000), (5104607757 / 100000000000000000000000000000000)⟩
def Z0_5_3H2E_1_2LogWitness : LogWitness := ⟨-2, 4382455112007387232015528108533, 2500000000000000000000000000000⟩
def Z0_5_3H2E_1_2Log : Ball := ⟨(-41248799889359090223264863826827 / 50000000000000000000000000000000), (63527471247 / 100000000000000000000000000000000)⟩
def Z0_5_3H2E_1_2 : Ball := ⟨(18077101393929149380776110958019 / 50000000000000000000000000000000), (5568125837 / 20000000000000000000000000000000)⟩
def Z0_5_3H2E_1_3LogWitness : LogWitness := ⟨-5, 4017638082125913136726400382471, 3125000000000000000000000000000⟩
def Z0_5_3H2E_1_3Log : Ball := ⟨(-321447599778718180446529670366099 / 100000000000000000000000000000000), (127054942197 / 100000000000000000000000000000000)⟩
def Z0_5_3H2E_1_3 : Ball := ⟨(1614325147848684263111295424987 / 12500000000000000000000000000000), (5104607757 / 100000000000000000000000000000000)⟩
def Z0_5_3H2E_0_4LogWitness : LogWitness := ⟨-6, 2157810797800214543118318532199, 1562500000000000000000000000000⟩
def Z0_5_3H2E_0_4Log : Ball := ⟨(-5993868746542471569477025801103 / 1562500000000000000000000000000), (148230766059 / 100000000000000000000000000000000)⟩
def Z0_5_3H2E_0_4 : Ball := ⟨(8277526209207412807813577207303 / 100000000000000000000000000000000), (6397079 / 200000000000000000000000000000)⟩
def Z0_5_3H2Entropy : Ball := ⟨(57346330179855185674256162523237 / 50000000000000000000000000000000), (18071888221 / 25000000000000000000000000000000)⟩
def Z0_5_3H2Mass : Ball := ⟨1, (97 / 50000000000000000000000000000000)⟩
def Z0_5_3H2MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def Z0_5_3H2MassTermLog : Ball := ⟨0, (5293955969 / 25000000000000000000000000000000)⟩
def Z0_5_3H2MassTerm : Ball := ⟨0, (21175823877 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Four0_7_1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def Z0_7_1Den : Ball := ⟨2, 0⟩
def Z0_7_1E_4_5LogWitness : LogWitness := ⟨-1, 1, 1⟩
def Z0_7_1E_4_5Log : Ball := ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
def Z0_7_1E_4_5 : Ball := ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
def Z0_7_1E_5_4LogWitness : LogWitness := ⟨-1, 1, 1⟩
def Z0_7_1E_5_4Log : Ball := ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
def Z0_7_1E_5_4 : Ball := ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
def Z0_7_1Entropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def Z0_7_1Labels : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def Z0_7_1Four : Ball := ⟨(18723326709712443708970142577019 / 6250000000000000000000000000000), (63527471049 / 50000000000000000000000000000000)⟩
def Z0_7_1H2E_1_0LogWitness : LogWitness := ⟨-1, 1, 1⟩
def Z0_7_1H2E_1_0Log : Ball := ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
def Z0_7_1H2E_1_0 : Ball := ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
def Z0_7_1H2E_0_1LogWitness : LogWitness := ⟨-1, 1, 1⟩
def Z0_7_1H2E_0_1Log : Ball := ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
def Z0_7_1H2E_0_1 : Ball := ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
def Z0_7_1H2Entropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def Z0_7_1H2Mass : Ball := ⟨1, 0⟩
def Z0_7_1H2MassTermLog : Ball := .exact 0
def Z0_7_1H2MassTerm : Ball := ⟨0, 0⟩

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Four0_8_0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def Z0_8_0Den : Ball := ⟨1, 0⟩
def Z0_8_0E_5_5Log : Ball := .exact 0
def Z0_8_0E_5_5 : Ball := ⟨0, 0⟩
def Z0_8_0Entropy : Ball := ⟨0, 0⟩
def Z0_8_0Labels : Ball := ⟨0, 0⟩
def Z0_8_0Four : Ball := ⟨0, 0⟩

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Four1_0_7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def Z1_0_7Den : Ball := ⟨2, 0⟩
def Z1_0_7E_4_5LogWitness : LogWitness := ⟨-1, 1, 1⟩
def Z1_0_7E_4_5Log : Ball := ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
def Z1_0_7E_4_5 : Ball := ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
def Z1_0_7E_5_4LogWitness : LogWitness := ⟨-1, 1, 1⟩
def Z1_0_7E_5_4Log : Ball := ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
def Z1_0_7E_5_4 : Ball := ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
def Z1_0_7Entropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def Z1_0_7Labels : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def Z1_0_7Four : Ball := ⟨(18723326709712443708970142577019 / 6250000000000000000000000000000), (63527471049 / 50000000000000000000000000000000)⟩
def Z1_0_7H2E_4_5LogWitness : LogWitness := ⟨-1, 1, 1⟩
def Z1_0_7H2E_4_5Log : Ball := ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
def Z1_0_7H2E_4_5 : Ball := ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
def Z1_0_7H2E_5_4LogWitness : LogWitness := ⟨-1, 1, 1⟩
def Z1_0_7H2E_5_4Log : Ball := ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
def Z1_0_7H2E_5_4 : Ball := ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
def Z1_0_7H2Entropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def Z1_0_7H2Mass : Ball := ⟨1, 0⟩
def Z1_0_7H2MassTermLog : Ball := .exact 0
def Z1_0_7H2MassTerm : Ball := ⟨0, 0⟩

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Four1_7_0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def Z1_7_0Den : Ball := ⟨2, 0⟩
def Z1_7_0E_4_5LogWitness : LogWitness := ⟨-1, 1, 1⟩
def Z1_7_0E_4_5Log : Ball := ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
def Z1_7_0E_4_5 : Ball := ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
def Z1_7_0E_5_4LogWitness : LogWitness := ⟨-1, 1, 1⟩
def Z1_7_0E_5_4Log : Ball := ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
def Z1_7_0E_5_4 : Ball := ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
def Z1_7_0Entropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def Z1_7_0Labels : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def Z1_7_0Four : Ball := ⟨(18723326709712443708970142577019 / 6250000000000000000000000000000), (63527471049 / 50000000000000000000000000000000)⟩
def Z1_7_0H1E_4_5LogWitness : LogWitness := ⟨-1, 1, 1⟩
def Z1_7_0H1E_4_5Log : Ball := ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
def Z1_7_0H1E_4_5 : Ball := ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
def Z1_7_0H1E_5_4LogWitness : LogWitness := ⟨-1, 1, 1⟩
def Z1_7_0H1E_5_4Log : Ball := ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
def Z1_7_0H1E_5_4 : Ball := ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
def Z1_7_0H1Entropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def Z1_7_0H1Mass : Ball := ⟨1, 0⟩
def Z1_7_0H1MassTermLog : Ball := .exact 0
def Z1_7_0H1MassTerm : Ball := ⟨0, 0⟩

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Four2_0_6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def Z2_0_6Den : Ball := ⟨(730569027616488524394965632979 / 400000000000000000000000000000), (3 / 3125000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def Z2_0_6E_2_5LogWitness : LogWitness := ⟨-3, 10457964405071752630514678883453, 6250000000000000000000000000000⟩
def Z2_0_6E_2_5Log : Ball := ⟨(-78232958663779813935933970438769 / 50000000000000000000000000000000), (10587911863 / 12500000000000000000000000000000)⟩
def Z2_0_6E_2_5 : Ball := ⟨(32726299880370363099063710099363 / 100000000000000000000000000000000), (17716480919 / 100000000000000000000000000000000)⟩
def Z2_0_6E_3_5LogWitness : LogWitness := ⟨-6, 1708150169428319858018410671529, 1562500000000000000000000000000⟩
def Z2_0_6E_3_5Log : Ball := ⟨(-203487958663779813935933941795503 / 50000000000000000000000000000000), (74115383007 / 50000000000000000000000000000000)⟩
def Z2_0_6E_3_5 : Ball := ⟨(1737939955340792184583902537331 / 25000000000000000000000000000000), (1266002049 / 50000000000000000000000000000000)⟩
def Z2_0_6E_4_4LogWitness : LogWitness := ⟨-1, 5475184204085634976190446312313, 5000000000000000000000000000000⟩
def Z2_0_6E_4_4Log : Ball := ⟨(-6023591732755962787186797906847 / 10000000000000000000000000000000), (2117582371 / 5000000000000000000000000000000)⟩
def Z2_0_6E_4_4 : Ball := ⟨(32980274307046266973832495616429 / 100000000000000000000000000000000), (5797076779 / 25000000000000000000000000000000)⟩
def Z2_0_6E_5_2LogWitness : LogWitness := ⟨-3, 10457964405071752630514678883453, 6250000000000000000000000000000⟩
def Z2_0_6E_5_2Log : Ball := ⟨(-78232958663779813935933970438769 / 50000000000000000000000000000000), (10587911863 / 12500000000000000000000000000000)⟩
def Z2_0_6E_5_2 : Ball := ⟨(32726299880370363099063710099363 / 100000000000000000000000000000000), (17716480919 / 100000000000000000000000000000000)⟩
def Z2_0_6E_5_3LogWitness : LogWitness := ⟨-6, 1708150169428319858018410671529, 1562500000000000000000000000000⟩
def Z2_0_6E_5_3Log : Ball := ⟨(-203487958663779813935933941795503 / 50000000000000000000000000000000), (74115383007 / 50000000000000000000000000000000)⟩
def Z2_0_6E_5_3 : Ball := ⟨(1737939955340792184583902537331 / 25000000000000000000000000000000), (1266002049 / 50000000000000000000000000000000)⟩
def Z2_0_6Entropy : Ball := ⟨(112336393710513330648631136113803 / 100000000000000000000000000000000), (1273705543 / 2000000000000000000000000000000)⟩
def Z2_0_6Labels : Ball := ⟨(389161104745575982126957038149479 / 100000000000000000000000000000000), (126897136649 / 100000000000000000000000000000000)⟩
def Z2_0_6Four : Ball := ⟨(250748749228044656387794087131641 / 50000000000000000000000000000000), (190582413799 / 100000000000000000000000000000000)⟩
def Z2_0_6H2E_2_5LogWitness : LogWitness := ⟨-3, 10457964405071752630514678883453, 6250000000000000000000000000000⟩
def Z2_0_6H2E_2_5Log : Ball := ⟨(-78232958663779813935933970438769 / 50000000000000000000000000000000), (10587911863 / 12500000000000000000000000000000)⟩
def Z2_0_6H2E_2_5 : Ball := ⟨(32726299880370363099063710099363 / 100000000000000000000000000000000), (17716480919 / 100000000000000000000000000000000)⟩
def Z2_0_6H2E_3_5LogWitness : LogWitness := ⟨-6, 1708150169428319858018410671529, 1562500000000000000000000000000⟩
def Z2_0_6H2E_3_5Log : Ball := ⟨(-203487958663779813935933941795503 / 50000000000000000000000000000000), (74115383007 / 50000000000000000000000000000000)⟩
def Z2_0_6H2E_3_5 : Ball := ⟨(1737939955340792184583902537331 / 25000000000000000000000000000000), (1266002049 / 50000000000000000000000000000000)⟩
def Z2_0_6H2E_4_4LogWitness : LogWitness := ⟨-1, 5475184204085634976190446312313, 5000000000000000000000000000000⟩
def Z2_0_6H2E_4_4Log : Ball := ⟨(-6023591732755962787186797906847 / 10000000000000000000000000000000), (2117582371 / 5000000000000000000000000000000)⟩
def Z2_0_6H2E_4_4 : Ball := ⟨(32980274307046266973832495616429 / 100000000000000000000000000000000), (5797076779 / 25000000000000000000000000000000)⟩
def Z2_0_6H2E_5_2LogWitness : LogWitness := ⟨-3, 10457964405071752630514678883453, 6250000000000000000000000000000⟩
def Z2_0_6H2E_5_2Log : Ball := ⟨(-78232958663779813935933970438769 / 50000000000000000000000000000000), (10587911863 / 12500000000000000000000000000000)⟩
def Z2_0_6H2E_5_2 : Ball := ⟨(32726299880370363099063710099363 / 100000000000000000000000000000000), (17716480919 / 100000000000000000000000000000000)⟩
def Z2_0_6H2E_5_3LogWitness : LogWitness := ⟨-6, 1708150169428319858018410671529, 1562500000000000000000000000000⟩
def Z2_0_6H2E_5_3Log : Ball := ⟨(-203487958663779813935933941795503 / 50000000000000000000000000000000), (74115383007 / 50000000000000000000000000000000)⟩
def Z2_0_6H2E_5_3 : Ball := ⟨(1737939955340792184583902537331 / 25000000000000000000000000000000), (1266002049 / 50000000000000000000000000000000)⟩
def Z2_0_6H2Entropy : Ball := ⟨(112336393710513330648631136113803 / 100000000000000000000000000000000), (1273705543 / 2000000000000000000000000000000)⟩
def Z2_0_6H2Mass : Ball := ⟨1, (11 / 10000000000000000000000000000000)⟩
def Z2_0_6H2MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def Z2_0_6H2MassTermLog : Ball := ⟨0, (1323488987 / 6250000000000000000000000000000)⟩
def Z2_0_6H2MassTerm : Ball := ⟨0, (21175823793 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Four2_6_0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def Z2_6_0Den : Ball := ⟨(40315691969935939784363805731103 / 25000000000000000000000000000000), (9 / 12500000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def Z2_6_0E_2_5LogWitness : LogWitness := ⟨-3, 8700304788653067056094286446733, 6250000000000000000000000000000⟩
def Z2_6_0E_2_5Log : Ball := ⟨(-87433247360137101787010999920051 / 50000000000000000000000000000000), (42351647449 / 50000000000000000000000000000000)⟩
def Z2_6_0E_2_5 : Ball := ⟨(30427836027795558418888937514137 / 100000000000000000000000000000000), (460590303 / 3125000000000000000000000000000)⟩
def Z2_6_0E_3_5LogWitness : LogWitness := ⟨-6, 1594093504259596830505224830177, 1562500000000000000000000000000⟩
def Z2_6_0E_3_5Log : Ball := ⟨(-20694324736013710178701097127681 / 5000000000000000000000000000000), (9264422873 / 6250000000000000000000000000000)⟩
def Z2_6_0E_3_5 : Ball := ⟨(1649434431835907568086056539411 / 25000000000000000000000000000000), (94517481 / 4000000000000000000000000000000)⟩
def Z2_6_0E_4_4LogWitness : LogWitness := ⟨-1, 12402118767373707622922480910543, 10000000000000000000000000000000⟩
def Z2_6_0E_4_4Log : Ball := ⟨(-47786494720274203574022038031033 / 100000000000000000000000000000000), (4235164741 / 10000000000000000000000000000000)⟩
def Z2_6_0E_4_4 : Ball := ⟨(14816344574932932322026713712577 / 50000000000000000000000000000000), (26262508073 / 100000000000000000000000000000000)⟩
def Z2_6_0E_5_2LogWitness : LogWitness := ⟨-3, 8700304788653067056094286446733, 6250000000000000000000000000000⟩
def Z2_6_0E_5_2Log : Ball := ⟨(-87433247360137101787010999920051 / 50000000000000000000000000000000), (42351647449 / 50000000000000000000000000000000)⟩
def Z2_6_0E_5_2 : Ball := ⟨(30427836027795558418888937514137 / 100000000000000000000000000000000), (460590303 / 3125000000000000000000000000000)⟩
def Z2_6_0E_5_3LogWitness : LogWitness := ⟨-6, 1594093504259596830505224830177, 1562500000000000000000000000000⟩
def Z2_6_0E_5_3Log : Ball := ⟨(-20694324736013710178701097127681 / 5000000000000000000000000000000), (9264422873 / 6250000000000000000000000000000)⟩
def Z2_6_0E_5_3 : Ball := ⟨(1649434431835907568086056539411 / 25000000000000000000000000000000), (94517481 / 4000000000000000000000000000000)⟩
def Z2_6_0Entropy : Ball := ⟨(25920959165036060506629938692179 / 25000000000000000000000000000000), (12093232303 / 20000000000000000000000000000000)⟩
def Z2_6_0Labels : Ball := ⟨(99950005950434599058581087087857 / 25000000000000000000000000000000), (130116252187 / 100000000000000000000000000000000)⟩
def Z2_6_0Four : Ball := ⟨(31467741278867664891302756445009 / 6250000000000000000000000000000), (95291206851 / 50000000000000000000000000000000)⟩
def Z2_6_0H1E_2_5LogWitness : LogWitness := ⟨-3, 8700304788653067056094286446733, 6250000000000000000000000000000⟩
def Z2_6_0H1E_2_5Log : Ball := ⟨(-87433247360137101787010999920051 / 50000000000000000000000000000000), (42351647449 / 50000000000000000000000000000000)⟩
def Z2_6_0H1E_2_5 : Ball := ⟨(30427836027795558418888937514137 / 100000000000000000000000000000000), (460590303 / 3125000000000000000000000000000)⟩
def Z2_6_0H1E_3_5LogWitness : LogWitness := ⟨-6, 1594093504259596830505224830177, 1562500000000000000000000000000⟩
def Z2_6_0H1E_3_5Log : Ball := ⟨(-20694324736013710178701097127681 / 5000000000000000000000000000000), (9264422873 / 6250000000000000000000000000000)⟩
def Z2_6_0H1E_3_5 : Ball := ⟨(1649434431835907568086056539411 / 25000000000000000000000000000000), (94517481 / 4000000000000000000000000000000)⟩
def Z2_6_0H1E_4_4LogWitness : LogWitness := ⟨-1, 12402118767373707622922480910543, 10000000000000000000000000000000⟩
def Z2_6_0H1E_4_4Log : Ball := ⟨(-47786494720274203574022038031033 / 100000000000000000000000000000000), (4235164741 / 10000000000000000000000000000000)⟩
def Z2_6_0H1E_4_4 : Ball := ⟨(14816344574932932322026713712577 / 50000000000000000000000000000000), (26262508073 / 100000000000000000000000000000000)⟩
def Z2_6_0H1E_5_2LogWitness : LogWitness := ⟨-3, 8700304788653067056094286446733, 6250000000000000000000000000000⟩
def Z2_6_0H1E_5_2Log : Ball := ⟨(-87433247360137101787010999920051 / 50000000000000000000000000000000), (42351647449 / 50000000000000000000000000000000)⟩
def Z2_6_0H1E_5_2 : Ball := ⟨(30427836027795558418888937514137 / 100000000000000000000000000000000), (460590303 / 3125000000000000000000000000000)⟩
def Z2_6_0H1E_5_3LogWitness : LogWitness := ⟨-6, 1594093504259596830505224830177, 1562500000000000000000000000000⟩
def Z2_6_0H1E_5_3Log : Ball := ⟨(-20694324736013710178701097127681 / 5000000000000000000000000000000), (9264422873 / 6250000000000000000000000000000)⟩
def Z2_6_0H1E_5_3 : Ball := ⟨(1649434431835907568086056539411 / 25000000000000000000000000000000), (94517481 / 4000000000000000000000000000000)⟩
def Z2_6_0H1Entropy : Ball := ⟨(25920959165036060506629938692179 / 25000000000000000000000000000000), (12093232303 / 20000000000000000000000000000000)⟩
def Z2_6_0H1Mass : Ball := ⟨(100000000000000000000000000000001 / 100000000000000000000000000000000), (23 / 25000000000000000000000000000000)⟩
def Z2_6_0H1MassTermLogWitness : LogWitness := ⟨0, 100000000000000000000000000000001, 100000000000000000000000000000000⟩
def Z2_6_0H1MassTermLog : Ball := ⟨(1 / 100000000000000000000000000000000), (10587911887 / 50000000000000000000000000000000)⟩
def Z2_6_0H1MassTerm : Ball := ⟨(-1 / 100000000000000000000000000000000), (847032951 / 4000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Four3_0_5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def Z3_0_5Den : Ball := ⟨(522229287310098961532365085049411 / 25000000000000000000000000000000), (1017 / 50000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def Z3_0_5E_1_5LogWitness : LogWitness := ⟨-5, 3851794993380545981064826935537, 3125000000000000000000000000000⟩
def Z3_0_5E_1_5Log : Ball := ⟨(-2605304731435115244590336352331 / 800000000000000000000000000000), (127054942357 / 100000000000000000000000000000000)⟩
def Z3_0_5E_1_5 : Ball := ⟨(6271937325482765530304899555359 / 50000000000000000000000000000000), (2446947971 / 50000000000000000000000000000000)⟩
def Z3_0_5E_2_4LogWitness : LogWitness := ⟨-2, 41361035729160865645318261676507, 25000000000000000000000000000000⟩
def Z3_0_5E_2_4Log : Ball := ⟨(-17656618285877881114758420265571 / 20000000000000000000000000000000), (31763735627 / 50000000000000000000000000000000)⟩
def Z3_0_5E_2_4 : Ball := ⟨(36514800988917506010651666724087 / 100000000000000000000000000000000), (26275620159 / 100000000000000000000000000000000)⟩
def Z3_0_5E_3_4LogWitness : LogWitness := ⟨-5, 1196792319364647093404227846989, 781250000000000000000000000000⟩
def Z3_0_5E_3_4Log : Ball := ⟨(-303923091429389405573792044041373 / 100000000000000000000000000000000), (63527471101 / 50000000000000000000000000000000)⟩
def Z3_0_5E_3_4 : Ball := ⟨(1454931286001010573435377377673 / 10000000000000000000000000000000), (3041167587 / 50000000000000000000000000000000)⟩
def Z3_0_5E_4_2LogWitness : LogWitness := ⟨-2, 41361035729160865645318261676507, 25000000000000000000000000000000⟩
def Z3_0_5E_4_2Log : Ball := ⟨(-17656618285877881114758420265571 / 20000000000000000000000000000000), (31763735627 / 50000000000000000000000000000000)⟩
def Z3_0_5E_4_2 : Ball := ⟨(36514800988917506010651666724087 / 100000000000000000000000000000000), (26275620159 / 100000000000000000000000000000000)⟩
def Z3_0_5E_4_3LogWitness : LogWitness := ⟨-5, 1196792319364647093404227846989, 781250000000000000000000000000⟩
def Z3_0_5E_4_3Log : Ball := ⟨(-303923091429389405573792044041373 / 100000000000000000000000000000000), (63527471101 / 50000000000000000000000000000000)⟩
def Z3_0_5E_4_3 : Ball := ⟨(1454931286001010573435377377673 / 10000000000000000000000000000000), (3041167587 / 50000000000000000000000000000000)⟩
def Z3_0_5E_5_1LogWitness : LogWitness := ⟨-5, 3851794993380545981064826935537, 3125000000000000000000000000000⟩
def Z3_0_5E_5_1Log : Ball := ⟨(-2605304731435115244590336352331 / 800000000000000000000000000000), (127054942357 / 100000000000000000000000000000000)⟩
def Z3_0_5E_5_1 : Ball := ⟨(6271937325482765530304899555359 / 50000000000000000000000000000000), (2446947971 / 50000000000000000000000000000000)⟩
def Z3_0_5Entropy : Ball := ⟨(12721597699978628561123047922307 / 10000000000000000000000000000000), (1490074051 / 2000000000000000000000000000000)⟩
def Z3_0_5Labels : Ball := ⟨(125791752768670849860793716024527 / 25000000000000000000000000000000), (78399530397 / 50000000000000000000000000000000)⟩
def Z3_0_5Four : Ball := ⟨(315191494037234842527202671660589 / 50000000000000000000000000000000), (14456422709 / 6250000000000000000000000000000)⟩
def Z3_0_5H2E_1_5LogWitness : LogWitness := ⟨-5, 3851794993380545981064826935537, 3125000000000000000000000000000⟩
def Z3_0_5H2E_1_5Log : Ball := ⟨(-2605304731435115244590336352331 / 800000000000000000000000000000), (127054942357 / 100000000000000000000000000000000)⟩
def Z3_0_5H2E_1_5 : Ball := ⟨(6271937325482765530304899555359 / 50000000000000000000000000000000), (2446947971 / 50000000000000000000000000000000)⟩
def Z3_0_5H2E_2_4LogWitness : LogWitness := ⟨-2, 41361035729160865645318261676507, 25000000000000000000000000000000⟩
def Z3_0_5H2E_2_4Log : Ball := ⟨(-17656618285877881114758420265571 / 20000000000000000000000000000000), (31763735627 / 50000000000000000000000000000000)⟩
def Z3_0_5H2E_2_4 : Ball := ⟨(36514800988917506010651666724087 / 100000000000000000000000000000000), (26275620159 / 100000000000000000000000000000000)⟩
def Z3_0_5H2E_3_4LogWitness : LogWitness := ⟨-5, 1196792319364647093404227846989, 781250000000000000000000000000⟩
def Z3_0_5H2E_3_4Log : Ball := ⟨(-303923091429389405573792044041373 / 100000000000000000000000000000000), (63527471101 / 50000000000000000000000000000000)⟩
def Z3_0_5H2E_3_4 : Ball := ⟨(1454931286001010573435377377673 / 10000000000000000000000000000000), (3041167587 / 50000000000000000000000000000000)⟩
def Z3_0_5H2E_4_2LogWitness : LogWitness := ⟨-2, 41361035729160865645318261676507, 25000000000000000000000000000000⟩
def Z3_0_5H2E_4_2Log : Ball := ⟨(-17656618285877881114758420265571 / 20000000000000000000000000000000), (31763735627 / 50000000000000000000000000000000)⟩
def Z3_0_5H2E_4_2 : Ball := ⟨(36514800988917506010651666724087 / 100000000000000000000000000000000), (26275620159 / 100000000000000000000000000000000)⟩
def Z3_0_5H2E_4_3LogWitness : LogWitness := ⟨-5, 1196792319364647093404227846989, 781250000000000000000000000000⟩
def Z3_0_5H2E_4_3Log : Ball := ⟨(-303923091429389405573792044041373 / 100000000000000000000000000000000), (63527471101 / 50000000000000000000000000000000)⟩
def Z3_0_5H2E_4_3 : Ball := ⟨(1454931286001010573435377377673 / 10000000000000000000000000000000), (3041167587 / 50000000000000000000000000000000)⟩
def Z3_0_5H2E_5_1LogWitness : LogWitness := ⟨-5, 3851794993380545981064826935537, 3125000000000000000000000000000⟩
def Z3_0_5H2E_5_1Log : Ball := ⟨(-2605304731435115244590336352331 / 800000000000000000000000000000), (127054942357 / 100000000000000000000000000000000)⟩
def Z3_0_5H2E_5_1 : Ball := ⟨(6271937325482765530304899555359 / 50000000000000000000000000000000), (2446947971 / 50000000000000000000000000000000)⟩
def Z3_0_5H2Entropy : Ball := ⟨(12721597699978628561123047922307 / 10000000000000000000000000000000), (1490074051 / 2000000000000000000000000000000)⟩
def Z3_0_5H2Mass : Ball := ⟨1, (1 / 500000000000000000000000000000)⟩
def Z3_0_5H2MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def Z3_0_5H2MassTermLog : Ball := ⟨0, (10587911941 / 50000000000000000000000000000000)⟩
def Z3_0_5H2MassTerm : Ball := ⟨0, (21175823883 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Four3_5_0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def Z3_5_0Den : Ball := ⟨(1107963313523711256690127341051801 / 50000000000000000000000000000000), (1063 / 50000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def Z3_5_0E_1_5LogWitness : LogWitness := ⟨-6, 645274206658629135363561930529, 390625000000000000000000000000⟩
def Z3_5_0E_1_5Log : Ball := ⟨(-365695575079275035532022819518357 / 100000000000000000000000000000000), (148230766013 / 100000000000000000000000000000000)⟩
def Z3_5_0E_1_5 : Ball := ⟨(1887791376702802768234330198239 / 20000000000000000000000000000000), (191298981 / 5000000000000000000000000000000)⟩
def Z3_5_0E_2_4LogWitness : LogWitness := ⟨-2, 21453059186785379874419022991011, 12500000000000000000000000000000⟩
def Z3_5_0E_2_4Log : Ball := ⟨(-21153893769818758883005723975117 / 25000000000000000000000000000000), (63527471251 / 100000000000000000000000000000000)⟩
def Z3_5_0E_2_4 : Ball := ⟨(4538157350748923372425986557083 / 12500000000000000000000000000000), (27257172089 / 100000000000000000000000000000000)⟩
def Z3_5_0E_3_4LogWitness : LogWitness := ⟨-5, 2256392399897361854853853147931, 1562500000000000000000000000000⟩
def Z3_5_0E_3_4Log : Ball := ⟨(-309825575079275035532022838613839 / 100000000000000000000000000000000), (31019273 / 24414062500000000000000000000)⟩
def Z3_5_0E_3_4 : Ball := ⟨(13981761458054113306784224791891 / 100000000000000000000000000000000), (716714517 / 12500000000000000000000000000000)⟩
def Z3_5_0E_4_2LogWitness : LogWitness := ⟨-2, 21453059186785379874419022991011, 12500000000000000000000000000000⟩
def Z3_5_0E_4_2Log : Ball := ⟨(-21153893769818758883005723975117 / 25000000000000000000000000000000), (63527471251 / 100000000000000000000000000000000)⟩
def Z3_5_0E_4_2 : Ball := ⟨(4538157350748923372425986557083 / 12500000000000000000000000000000), (27257172089 / 100000000000000000000000000000000)⟩
def Z3_5_0E_4_3LogWitness : LogWitness := ⟨-5, 2256392399897361854853853147931, 1562500000000000000000000000000⟩
def Z3_5_0E_4_3Log : Ball := ⟨(-309825575079275035532022838613839 / 100000000000000000000000000000000), (31019273 / 24414062500000000000000000000)⟩
def Z3_5_0E_4_3 : Ball := ⟨(13981761458054113306784224791891 / 100000000000000000000000000000000), (716714517 / 12500000000000000000000000000000)⟩
def Z3_5_0E_5_1LogWitness : LogWitness := ⟨-6, 645274206658629135363561930529, 390625000000000000000000000000⟩
def Z3_5_0E_5_1Log : Ball := ⟨(-365695575079275035532022819518357 / 100000000000000000000000000000000), (148230766013 / 100000000000000000000000000000000)⟩
def Z3_5_0E_5_1 : Ball := ⟨(1887791376702802768234330198239 / 20000000000000000000000000000000), (191298981 / 5000000000000000000000000000000)⟩
def Z3_5_0Entropy : Ball := ⟨(238903908590238056509455072959 / 200000000000000000000000000000), (7363373569 / 10000000000000000000000000000000)⟩
def Z3_5_0Labels : Ball := ⟨(256366745881774017426327259984771 / 50000000000000000000000000000000), (19912540783 / 12500000000000000000000000000000)⟩
def Z3_5_0Four : Ball := ⟨(316092723029333531553691028224521 / 50000000000000000000000000000000), (116467030977 / 50000000000000000000000000000000)⟩
def Z3_5_0H1E_1_5LogWitness : LogWitness := ⟨-6, 645274206658629135363561930529, 390625000000000000000000000000⟩
def Z3_5_0H1E_1_5Log : Ball := ⟨(-365695575079275035532022819518357 / 100000000000000000000000000000000), (148230766013 / 100000000000000000000000000000000)⟩
def Z3_5_0H1E_1_5 : Ball := ⟨(1887791376702802768234330198239 / 20000000000000000000000000000000), (191298981 / 5000000000000000000000000000000)⟩
def Z3_5_0H1E_2_4LogWitness : LogWitness := ⟨-2, 21453059186785379874419022991011, 12500000000000000000000000000000⟩
def Z3_5_0H1E_2_4Log : Ball := ⟨(-21153893769818758883005723975117 / 25000000000000000000000000000000), (63527471251 / 100000000000000000000000000000000)⟩
def Z3_5_0H1E_2_4 : Ball := ⟨(4538157350748923372425986557083 / 12500000000000000000000000000000), (27257172089 / 100000000000000000000000000000000)⟩
def Z3_5_0H1E_3_4LogWitness : LogWitness := ⟨-5, 2256392399897361854853853147931, 1562500000000000000000000000000⟩
def Z3_5_0H1E_3_4Log : Ball := ⟨(-309825575079275035532022838613839 / 100000000000000000000000000000000), (31019273 / 24414062500000000000000000000)⟩
def Z3_5_0H1E_3_4 : Ball := ⟨(13981761458054113306784224791891 / 100000000000000000000000000000000), (716714517 / 12500000000000000000000000000000)⟩
def Z3_5_0H1E_4_2LogWitness : LogWitness := ⟨-2, 21453059186785379874419022991011, 12500000000000000000000000000000⟩
def Z3_5_0H1E_4_2Log : Ball := ⟨(-21153893769818758883005723975117 / 25000000000000000000000000000000), (63527471251 / 100000000000000000000000000000000)⟩
def Z3_5_0H1E_4_2 : Ball := ⟨(4538157350748923372425986557083 / 12500000000000000000000000000000), (27257172089 / 100000000000000000000000000000000)⟩
def Z3_5_0H1E_4_3LogWitness : LogWitness := ⟨-5, 2256392399897361854853853147931, 1562500000000000000000000000000⟩
def Z3_5_0H1E_4_3Log : Ball := ⟨(-309825575079275035532022838613839 / 100000000000000000000000000000000), (31019273 / 24414062500000000000000000000)⟩
def Z3_5_0H1E_4_3 : Ball := ⟨(13981761458054113306784224791891 / 100000000000000000000000000000000), (716714517 / 12500000000000000000000000000000)⟩
def Z3_5_0H1E_5_1LogWitness : LogWitness := ⟨-6, 645274206658629135363561930529, 390625000000000000000000000000⟩
def Z3_5_0H1E_5_1Log : Ball := ⟨(-365695575079275035532022819518357 / 100000000000000000000000000000000), (148230766013 / 100000000000000000000000000000000)⟩
def Z3_5_0H1E_5_1 : Ball := ⟨(1887791376702802768234330198239 / 20000000000000000000000000000000), (191298981 / 5000000000000000000000000000000)⟩
def Z3_5_0H1Entropy : Ball := ⟨(238903908590238056509455072959 / 200000000000000000000000000000), (7363373569 / 10000000000000000000000000000000)⟩
def Z3_5_0H1Mass : Ball := ⟨1, (49 / 25000000000000000000000000000000)⟩
def Z3_5_0H1MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def Z3_5_0H1MassTermLog : Ball := ⟨0, (10587911939 / 50000000000000000000000000000000)⟩
def Z3_5_0H1MassTerm : Ball := ⟨0, (21175823879 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Four4_0_4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def Z4_0_4Den : Ball := ⟨(13646777938944276882364160176219867 / 100000000000000000000000000000000), (13969 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def Z4_0_4E_0_5LogWitness : LogWitness := ⟨-9, 55190951304569688595534186513, 39062500000000000000000000000⟩
def Z4_0_4E_0_5Log : Ball := ⟨(-589268853833220841124255600121907 / 100000000000000000000000000000000), (26469779649 / 12500000000000000000000000000000)⟩
def Z4_0_4E_0_5 : Ball := ⟨(1626115430860444246284949942957 / 100000000000000000000000000000000), (116871387 / 20000000000000000000000000000000)⟩
def Z4_0_4E_1_4LogWitness : LogWitness := ⟨-3, 6632849277085335226067309879167, 6250000000000000000000000000000⟩
def Z4_0_4E_1_4Log : Ball := ⟨(-201998853833220841124255714694749 / 100000000000000000000000000000000), (42351647471 / 50000000000000000000000000000000)⟩
def Z4_0_4E_1_4 : Ball := ⟨(837392469762340720305966731003 / 3125000000000000000000000000000), (1123648383 / 10000000000000000000000000000000)⟩
def Z4_0_4E_2_2LogWitness : LogWitness := ⟨-1, 5855588794422561384849059336303, 5000000000000000000000000000000⟩
def Z4_0_4E_2_2Log : Ball := ⟨(-53518853833220841124255752885733 / 100000000000000000000000000000000), (10587911893 / 25000000000000000000000000000000)⟩
def Z4_0_4E_2_2 : Ball := ⟨(31338440079614690320574653450617 / 100000000000000000000000000000000), (77498073 / 312500000000000000000000000000)⟩
def Z4_0_4E_2_3LogWitness : LogWitness := ⟨-4, 3407007932926322989871260497747, 3125000000000000000000000000000⟩
def Z4_0_4E_2_3Log : Ball := ⟨(-6715471345830521028106392389981 / 2500000000000000000000000000000), (52939559317 / 50000000000000000000000000000000)⟩
def Z4_0_4E_2_3 : Ball := ⟨(18303731318867196612732623716901 / 100000000000000000000000000000000), (7214619983 / 100000000000000000000000000000000)⟩
def Z4_0_4E_3_2LogWitness : LogWitness := ⟨-4, 3407007932926322989871260497747, 3125000000000000000000000000000⟩
def Z4_0_4E_3_2Log : Ball := ⟨(-6715471345830521028106392389981 / 2500000000000000000000000000000), (52939559317 / 50000000000000000000000000000000)⟩
def Z4_0_4E_3_2 : Ball := ⟨(18303731318867196612732623716901 / 100000000000000000000000000000000), (7214619983 / 100000000000000000000000000000000)⟩
def Z4_0_4E_3_3LogWitness : LogWitness := ⟨-8, 146554740536411280359956652837, 78125000000000000000000000000⟩
def Z4_0_4E_3_3Log : Ball := ⟨(-245804426916610420562127809721047 / 50000000000000000000000000000000), (190582413283 / 100000000000000000000000000000000)⟩
def Z4_0_4E_3_3 : Ball := ⟨(3602380400946510922725768272093 / 100000000000000000000000000000000), (349134453 / 25000000000000000000000000000000)⟩
def Z4_0_4E_4_1LogWitness : LogWitness := ⟨-3, 6632849277085335226067309879167, 6250000000000000000000000000000⟩
def Z4_0_4E_4_1Log : Ball := ⟨(-201998853833220841124255714694749 / 100000000000000000000000000000000), (42351647471 / 50000000000000000000000000000000)⟩
def Z4_0_4E_4_1 : Ball := ⟨(837392469762340720305966731003 / 3125000000000000000000000000000), (1123648383 / 10000000000000000000000000000000)⟩
def Z4_0_4E_5_0LogWitness : LogWitness := ⟨-9, 55190951304569688595534186513, 39062500000000000000000000000⟩
def Z4_0_4E_5_0Log : Ball := ⟨(-589268853833220841124255600121907 / 100000000000000000000000000000000), (26469779649 / 12500000000000000000000000000000)⟩
def Z4_0_4E_5_0 : Ball := ⟨(1626115430860444246284949942957 / 100000000000000000000000000000000), (116871387 / 20000000000000000000000000000000)⟩
def Z4_0_4Entropy : Ball := ⟨(64196816022403144530458719913309 / 50000000000000000000000000000000), (16066710667 / 25000000000000000000000000000000)⟩
def Z4_0_4Labels : Ball := ⟨(55347887687580346776034112349573 / 10000000000000000000000000000000), (565953783 / 312500000000000000000000000000)⟩
def Z4_0_4Four : Ball := ⟨(170468127230152439205314640830587 / 25000000000000000000000000000000), (61343013307 / 25000000000000000000000000000000)⟩
def Z4_0_4H2E_5_0LogWitness : LogWitness := ⟨-9, 55190951304569688595534186513, 39062500000000000000000000000⟩
def Z4_0_4H2E_5_0Log : Ball := ⟨(-589268853833220841124255600121907 / 100000000000000000000000000000000), (26469779649 / 12500000000000000000000000000000)⟩
def Z4_0_4H2E_5_0 : Ball := ⟨(1626115430860444246284949942957 / 100000000000000000000000000000000), (116871387 / 20000000000000000000000000000000)⟩
def Z4_0_4H2E_4_1LogWitness : LogWitness := ⟨-3, 6632849277085335226067309879167, 6250000000000000000000000000000⟩
def Z4_0_4H2E_4_1Log : Ball := ⟨(-201998853833220841124255714694749 / 100000000000000000000000000000000), (42351647471 / 50000000000000000000000000000000)⟩
def Z4_0_4H2E_4_1 : Ball := ⟨(837392469762340720305966731003 / 3125000000000000000000000000000), (1123648383 / 10000000000000000000000000000000)⟩
def Z4_0_4H2E_2_2LogWitness : LogWitness := ⟨-1, 5855588794422561384849059336303, 5000000000000000000000000000000⟩
def Z4_0_4H2E_2_2Log : Ball := ⟨(-53518853833220841124255752885733 / 100000000000000000000000000000000), (10587911893 / 25000000000000000000000000000000)⟩
def Z4_0_4H2E_2_2 : Ball := ⟨(31338440079614690320574653450617 / 100000000000000000000000000000000), (77498073 / 312500000000000000000000000000)⟩
def Z4_0_4H2E_2_3LogWitness : LogWitness := ⟨-4, 3407007932926322989871260497747, 3125000000000000000000000000000⟩
def Z4_0_4H2E_2_3Log : Ball := ⟨(-6715471345830521028106392389981 / 2500000000000000000000000000000), (52939559317 / 50000000000000000000000000000000)⟩
def Z4_0_4H2E_2_3 : Ball := ⟨(18303731318867196612732623716901 / 100000000000000000000000000000000), (7214619983 / 100000000000000000000000000000000)⟩
def Z4_0_4H2E_3_2LogWitness : LogWitness := ⟨-4, 3407007932926322989871260497747, 3125000000000000000000000000000⟩
def Z4_0_4H2E_3_2Log : Ball := ⟨(-6715471345830521028106392389981 / 2500000000000000000000000000000), (52939559317 / 50000000000000000000000000000000)⟩
def Z4_0_4H2E_3_2 : Ball := ⟨(18303731318867196612732623716901 / 100000000000000000000000000000000), (7214619983 / 100000000000000000000000000000000)⟩
def Z4_0_4H2E_3_3LogWitness : LogWitness := ⟨-8, 146554740536411280359956652837, 78125000000000000000000000000⟩
def Z4_0_4H2E_3_3Log : Ball := ⟨(-245804426916610420562127809721047 / 50000000000000000000000000000000), (190582413283 / 100000000000000000000000000000000)⟩
def Z4_0_4H2E_3_3 : Ball := ⟨(3602380400946510922725768272093 / 100000000000000000000000000000000), (349134453 / 25000000000000000000000000000000)⟩
def Z4_0_4H2E_1_4LogWitness : LogWitness := ⟨-3, 6632849277085335226067309879167, 6250000000000000000000000000000⟩
def Z4_0_4H2E_1_4Log : Ball := ⟨(-201998853833220841124255714694749 / 100000000000000000000000000000000), (42351647471 / 50000000000000000000000000000000)⟩
def Z4_0_4H2E_1_4 : Ball := ⟨(837392469762340720305966731003 / 3125000000000000000000000000000), (1123648383 / 10000000000000000000000000000000)⟩
def Z4_0_4H2E_0_5LogWitness : LogWitness := ⟨-9, 55190951304569688595534186513, 39062500000000000000000000000⟩
def Z4_0_4H2E_0_5Log : Ball := ⟨(-589268853833220841124255600121907 / 100000000000000000000000000000000), (26469779649 / 12500000000000000000000000000000)⟩
def Z4_0_4H2E_0_5 : Ball := ⟨(1626115430860444246284949942957 / 100000000000000000000000000000000), (116871387 / 20000000000000000000000000000000)⟩
def Z4_0_4H2Entropy : Ball := ⟨(64196816022403144530458719913309 / 50000000000000000000000000000000), (16066710667 / 25000000000000000000000000000000)⟩
def Z4_0_4H2Mass : Ball := ⟨(100000000000000000000000000000001 / 100000000000000000000000000000000), (21 / 10000000000000000000000000000000)⟩
def Z4_0_4H2MassTermLogWitness : LogWitness := ⟨0, 100000000000000000000000000000001, 100000000000000000000000000000000⟩
def Z4_0_4H2MassTermLog : Ball := ⟨(1 / 100000000000000000000000000000000), (5293955973 / 25000000000000000000000000000000)⟩
def Z4_0_4H2MassTerm : Ball := ⟨(-1 / 100000000000000000000000000000000), (21175823893 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Four4_4_0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def Z4_4_0Den : Ball := ⟨(1381673256774017391432963646374551 / 10000000000000000000000000000000), (7051 / 50000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def Z4_4_0E_0_5LogWitness : LogWitness := ⟨-9, 13333388289568308767749416709, 12207031250000000000000000000⟩
def Z4_4_0E_0_5Log : Ball := ⟨(-615006545557549166812452928547037 / 100000000000000000000000000000000), (105879118649 / 50000000000000000000000000000000)⟩
def Z4_4_0E_0_5 : Ball := ⟨(1312019371607181543741200578043 / 100000000000000000000000000000000), (18070111 / 4000000000000000000000000000000)⟩
def Z4_4_0E_1_4LogWitness : LogWitness := ⟨-3, 12864926472604064794547580018297, 12500000000000000000000000000000⟩
def Z4_4_0E_1_4Log : Ball := ⟨(-102533272778774583406226521559951 / 50000000000000000000000000000000), (84703294941 / 100000000000000000000000000000000)⟩
def Z4_4_0E_1_4 : Ball := ⟨(26381660305887817562778739090541 / 100000000000000000000000000000000), (1089701667 / 10000000000000000000000000000000)⟩
def Z4_4_0E_2_2LogWitness : LogWitness := ⟨-1, 59823869115870383240874620994737, 50000000000000000000000000000000⟩
def Z4_4_0E_2_2Log : Ball := ⟨(-51376545557549166812453081310857 / 100000000000000000000000000000000), (42351647571 / 100000000000000000000000000000000)⟩
def Z4_4_0E_2_2 : Ball := ⟨(480241208915683334342627678761 / 1562500000000000000000000000000), (1013455771 / 4000000000000000000000000000000)⟩
def Z4_4_0E_2_3LogWitness : LogWitness := ⟨-4, 1661981174399030590448466000577, 1562500000000000000000000000000⟩
def Z4_4_0E_2_3Log : Ball := ⟨(-135543272778774583406226512012229 / 50000000000000000000000000000000), (847032949 / 800000000000000000000000000000)⟩
def Z4_4_0E_2_3 : Ball := ⟨(3604325882796094985265170692573 / 20000000000000000000000000000000), (1407752823 / 20000000000000000000000000000000)⟩
def Z4_4_0E_3_2LogWitness : LogWitness := ⟨-4, 1661981174399030590448466000577, 1562500000000000000000000000000⟩
def Z4_4_0E_3_2Log : Ball := ⟨(-135543272778774583406226512012229 / 50000000000000000000000000000000), (847032949 / 800000000000000000000000000000)⟩
def Z4_4_0E_3_2 : Ball := ⟨(3604325882796094985265170692573 / 20000000000000000000000000000000), (1407752823 / 20000000000000000000000000000000)⟩
def Z4_4_0E_3_3LogWitness : LogWitness := ⟨-8, 180940029615764141468627407341, 97656250000000000000000000000⟩
def Z4_4_0E_3_3Log : Ball := ⟨(-15401454548673411462889154616633 / 3125000000000000000000000000000), (190582413423 / 100000000000000000000000000000000)⟩
def Z4_4_0E_3_3 : Ball := ⟨(1783513370984199948259882031059 / 50000000000000000000000000000000), (172419939 / 12500000000000000000000000000000)⟩
def Z4_4_0E_4_1LogWitness : LogWitness := ⟨-3, 12864926472604064794547580018297, 12500000000000000000000000000000⟩
def Z4_4_0E_4_1Log : Ball := ⟨(-102533272778774583406226521559951 / 50000000000000000000000000000000), (84703294941 / 100000000000000000000000000000000)⟩
def Z4_4_0E_4_1 : Ball := ⟨(26381660305887817562778739090541 / 100000000000000000000000000000000), (1089701667 / 10000000000000000000000000000000)⟩
def Z4_4_0E_5_0LogWitness : LogWitness := ⟨-9, 13333388289568308767749416709, 12207031250000000000000000000⟩
def Z4_4_0E_5_0Log : Ball := ⟨(-615006545557549166812452928547037 / 100000000000000000000000000000000), (105879118649 / 50000000000000000000000000000000)⟩
def Z4_4_0E_5_0 : Ball := ⟨(1312019371607181543741200578043 / 100000000000000000000000000000000), (18070111 / 4000000000000000000000000000000)⟩
def Z4_4_0Entropy : Ball := ⟨(3143327057388077034003488044143 / 2500000000000000000000000000000), (63490820907 / 100000000000000000000000000000000)⟩
def Z4_4_0Labels : Ball := ⟨(278319288524584121929550231720779 / 50000000000000000000000000000000), (182174349901 / 100000000000000000000000000000000)⟩
def Z4_4_0Four : Ball := ⟨(341185829672345662609619992603639 / 50000000000000000000000000000000), (30708146351 / 12500000000000000000000000000000)⟩
def Z4_4_0H1E_5_0LogWitness : LogWitness := ⟨-9, 13333388289568308767749416709, 12207031250000000000000000000⟩
def Z4_4_0H1E_5_0Log : Ball := ⟨(-615006545557549166812452928547037 / 100000000000000000000000000000000), (105879118649 / 50000000000000000000000000000000)⟩
def Z4_4_0H1E_5_0 : Ball := ⟨(1312019371607181543741200578043 / 100000000000000000000000000000000), (18070111 / 4000000000000000000000000000000)⟩
def Z4_4_0H1E_4_1LogWitness : LogWitness := ⟨-3, 12864926472604064794547580018297, 12500000000000000000000000000000⟩
def Z4_4_0H1E_4_1Log : Ball := ⟨(-102533272778774583406226521559951 / 50000000000000000000000000000000), (84703294941 / 100000000000000000000000000000000)⟩
def Z4_4_0H1E_4_1 : Ball := ⟨(26381660305887817562778739090541 / 100000000000000000000000000000000), (1089701667 / 10000000000000000000000000000000)⟩
def Z4_4_0H1E_2_2LogWitness : LogWitness := ⟨-1, 59823869115870383240874620994737, 50000000000000000000000000000000⟩
def Z4_4_0H1E_2_2Log : Ball := ⟨(-51376545557549166812453081310857 / 100000000000000000000000000000000), (42351647571 / 100000000000000000000000000000000)⟩
def Z4_4_0H1E_2_2 : Ball := ⟨(480241208915683334342627678761 / 1562500000000000000000000000000), (1013455771 / 4000000000000000000000000000000)⟩
def Z4_4_0H1E_2_3LogWitness : LogWitness := ⟨-4, 1661981174399030590448466000577, 1562500000000000000000000000000⟩
def Z4_4_0H1E_2_3Log : Ball := ⟨(-135543272778774583406226512012229 / 50000000000000000000000000000000), (847032949 / 800000000000000000000000000000)⟩
def Z4_4_0H1E_2_3 : Ball := ⟨(3604325882796094985265170692573 / 20000000000000000000000000000000), (1407752823 / 20000000000000000000000000000000)⟩
def Z4_4_0H1E_3_2LogWitness : LogWitness := ⟨-4, 1661981174399030590448466000577, 1562500000000000000000000000000⟩
def Z4_4_0H1E_3_2Log : Ball := ⟨(-135543272778774583406226512012229 / 50000000000000000000000000000000), (847032949 / 800000000000000000000000000000)⟩
def Z4_4_0H1E_3_2 : Ball := ⟨(3604325882796094985265170692573 / 20000000000000000000000000000000), (1407752823 / 20000000000000000000000000000000)⟩
def Z4_4_0H1E_3_3LogWitness : LogWitness := ⟨-8, 180940029615764141468627407341, 97656250000000000000000000000⟩
def Z4_4_0H1E_3_3Log : Ball := ⟨(-15401454548673411462889154616633 / 3125000000000000000000000000000), (190582413423 / 100000000000000000000000000000000)⟩
def Z4_4_0H1E_3_3 : Ball := ⟨(1783513370984199948259882031059 / 50000000000000000000000000000000), (172419939 / 12500000000000000000000000000000)⟩
def Z4_4_0H1E_1_4LogWitness : LogWitness := ⟨-3, 12864926472604064794547580018297, 12500000000000000000000000000000⟩
def Z4_4_0H1E_1_4Log : Ball := ⟨(-102533272778774583406226521559951 / 50000000000000000000000000000000), (84703294941 / 100000000000000000000000000000000)⟩
def Z4_4_0H1E_1_4 : Ball := ⟨(26381660305887817562778739090541 / 100000000000000000000000000000000), (1089701667 / 10000000000000000000000000000000)⟩
def Z4_4_0H1E_0_5LogWitness : LogWitness := ⟨-9, 13333388289568308767749416709, 12207031250000000000000000000⟩
def Z4_4_0H1E_0_5Log : Ball := ⟨(-615006545557549166812452928547037 / 100000000000000000000000000000000), (105879118649 / 50000000000000000000000000000000)⟩
def Z4_4_0H1E_0_5 : Ball := ⟨(1312019371607181543741200578043 / 100000000000000000000000000000000), (18070111 / 4000000000000000000000000000000)⟩
def Z4_4_0H1Entropy : Ball := ⟨(3143327057388077034003488044143 / 2500000000000000000000000000000), (63490820907 / 100000000000000000000000000000000)⟩
def Z4_4_0H1Mass : Ball := ⟨(99999999999999999999999999999999 / 100000000000000000000000000000000), (209 / 100000000000000000000000000000000)⟩
def Z4_4_0H1MassTermLogWitness : LogWitness := ⟨-1, 99999999999999999999999999999999, 50000000000000000000000000000000⟩
def Z4_4_0H1MassTermLog : Ball := ⟨0, (1694065903 / 4000000000000000000000000000000)⟩
def Z4_4_0H1MassTerm : Ball := ⟨0, (5293955947 / 12500000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Four5_0_3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def Z5_0_3Den : Ball := ⟨(518317484278105540989009344894649 / 25000000000000000000000000000000), (983 / 50000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def Z5_0_3E_1_5LogWitness : LogWitness := ⟨-6, 2208598281054095678468725843991, 1562500000000000000000000000000⟩
def Z5_0_3E_1_5Log : Ball := ⟨(-381281213365411604359879013926363 / 100000000000000000000000000000000), (148230766007 / 100000000000000000000000000000000)⟩
def Z5_0_3E_1_5 : Ball := ⟨(8420970324370679601710618565453 / 100000000000000000000000000000000), (327382217 / 10000000000000000000000000000000)⟩
def Z5_0_3E_2_4LogWitness : LogWitness := ⟨-2, 42968103111757469343913723803283, 25000000000000000000000000000000⟩
def Z5_0_3E_2_4Log : Ball := ⟨(-42235606682705802179939545154249 / 50000000000000000000000000000000), (63527471249 / 100000000000000000000000000000000)⟩
def Z5_0_3E_2_4 : Ball := ⟨(36295678058602714916587164090917 / 100000000000000000000000000000000), (1706034339 / 6250000000000000000000000000000)⟩
def Z5_0_3E_3_4LogWitness : LogWitness := ⟨-5, 2411649303594217488808775176363, 1562500000000000000000000000000⟩
def Z5_0_3E_3_4Log : Ball := ⟨(-303171213365411604359879033021803 / 100000000000000000000000000000000), (127054942201 / 100000000000000000000000000000000)⟩
def Z5_0_3E_3_4 : Ball := ⟨(7311426455825088170477182923379 / 50000000000000000000000000000000), (3064119637 / 50000000000000000000000000000000)⟩
def Z5_0_3E_4_2LogWitness : LogWitness := ⟨-2, 42968103111757469343913723803283, 25000000000000000000000000000000⟩
def Z5_0_3E_4_2Log : Ball := ⟨(-42235606682705802179939545154249 / 50000000000000000000000000000000), (63527471249 / 100000000000000000000000000000000)⟩
def Z5_0_3E_4_2 : Ball := ⟨(36295678058602714916587164090917 / 100000000000000000000000000000000), (1706034339 / 6250000000000000000000000000000)⟩
def Z5_0_3E_4_3LogWitness : LogWitness := ⟨-5, 2411649303594217488808775176363, 1562500000000000000000000000000⟩
def Z5_0_3E_4_3Log : Ball := ⟨(-303171213365411604359879033021803 / 100000000000000000000000000000000), (127054942201 / 100000000000000000000000000000000)⟩
def Z5_0_3E_4_3 : Ball := ⟨(7311426455825088170477182923379 / 50000000000000000000000000000000), (3064119637 / 50000000000000000000000000000000)⟩
def Z5_0_3E_5_1LogWitness : LogWitness := ⟨-6, 2208598281054095678468725843991, 1562500000000000000000000000000⟩
def Z5_0_3E_5_1Log : Ball := ⟨(-381281213365411604359879013926363 / 100000000000000000000000000000000), (148230766007 / 100000000000000000000000000000000)⟩
def Z5_0_3E_5_1 : Ball := ⟨(8420970324370679601710618565453 / 100000000000000000000000000000000), (327382217 / 10000000000000000000000000000000)⟩
def Z5_0_3Entropy : Ball := ⟨(7417437661827946357406518562891 / 6250000000000000000000000000000), (9174652717 / 12500000000000000000000000000000)⟩
def Z5_0_3Labels : Ball := ⟨(64195374706788471650300819324119 / 12500000000000000000000000000000), (311595391 / 195312500000000000000000000000)⟩
def Z5_0_3Four : Ball := ⟨(79030250030444364365113856449901 / 12500000000000000000000000000000), (29116757741 / 12500000000000000000000000000000)⟩
def Z5_0_3H2E_4_0LogWitness : LogWitness := ⟨-6, 2208598281054095678468725843991, 1562500000000000000000000000000⟩
def Z5_0_3H2E_4_0Log : Ball := ⟨(-381281213365411604359879013926363 / 100000000000000000000000000000000), (148230766007 / 100000000000000000000000000000000)⟩
def Z5_0_3H2E_4_0 : Ball := ⟨(8420970324370679601710618565453 / 100000000000000000000000000000000), (327382217 / 10000000000000000000000000000000)⟩
def Z5_0_3H2E_2_1LogWitness : LogWitness := ⟨-2, 42968103111757469343913723803283, 25000000000000000000000000000000⟩
def Z5_0_3H2E_2_1Log : Ball := ⟨(-42235606682705802179939545154249 / 50000000000000000000000000000000), (63527471249 / 100000000000000000000000000000000)⟩
def Z5_0_3H2E_2_1 : Ball := ⟨(36295678058602714916587164090917 / 100000000000000000000000000000000), (1706034339 / 6250000000000000000000000000000)⟩
def Z5_0_3H2E_3_1LogWitness : LogWitness := ⟨-5, 2411649303594217488808775176363, 1562500000000000000000000000000⟩
def Z5_0_3H2E_3_1Log : Ball := ⟨(-303171213365411604359879033021803 / 100000000000000000000000000000000), (127054942201 / 100000000000000000000000000000000)⟩
def Z5_0_3H2E_3_1 : Ball := ⟨(7311426455825088170477182923379 / 50000000000000000000000000000000), (3064119637 / 50000000000000000000000000000000)⟩
def Z5_0_3H2E_1_2LogWitness : LogWitness := ⟨-2, 42968103111757469343913723803283, 25000000000000000000000000000000⟩
def Z5_0_3H2E_1_2Log : Ball := ⟨(-42235606682705802179939545154249 / 50000000000000000000000000000000), (63527471249 / 100000000000000000000000000000000)⟩
def Z5_0_3H2E_1_2 : Ball := ⟨(36295678058602714916587164090917 / 100000000000000000000000000000000), (1706034339 / 6250000000000000000000000000000)⟩
def Z5_0_3H2E_1_3LogWitness : LogWitness := ⟨-5, 2411649303594217488808775176363, 1562500000000000000000000000000⟩
def Z5_0_3H2E_1_3Log : Ball := ⟨(-303171213365411604359879033021803 / 100000000000000000000000000000000), (127054942201 / 100000000000000000000000000000000)⟩
def Z5_0_3H2E_1_3 : Ball := ⟨(7311426455825088170477182923379 / 50000000000000000000000000000000), (3064119637 / 50000000000000000000000000000000)⟩
def Z5_0_3H2E_0_4LogWitness : LogWitness := ⟨-6, 2208598281054095678468725843991, 1562500000000000000000000000000⟩
def Z5_0_3H2E_0_4Log : Ball := ⟨(-381281213365411604359879013926363 / 100000000000000000000000000000000), (148230766007 / 100000000000000000000000000000000)⟩
def Z5_0_3H2E_0_4 : Ball := ⟨(8420970324370679601710618565453 / 100000000000000000000000000000000), (327382217 / 10000000000000000000000000000000)⟩
def Z5_0_3H2Entropy : Ball := ⟨(7417437661827946357406518562891 / 6250000000000000000000000000000), (9174652717 / 12500000000000000000000000000000)⟩
def Z5_0_3H2Mass : Ball := ⟨1, (3 / 1562500000000000000000000000000)⟩
def Z5_0_3H2MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def Z5_0_3H2MassTermLog : Ball := ⟨0, (10587911937 / 50000000000000000000000000000000)⟩
def Z5_0_3H2MassTerm : Ball := ⟨0, (169406591 / 800000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Four5_3_0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def Z5_3_0Den : Ball := ⟨(61678486063347289235346358275403 / 2500000000000000000000000000000), (587 / 25000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def Z5_3_0E_1_5LogWitness : LogWitness := ⟨-6, 2212727093860282562448201536591, 1562500000000000000000000000000⟩
def Z5_3_0E_1_5Log : Ball := ⟨(-190547222603130891450597651942923 / 50000000000000000000000000000000), (37057691513 / 25000000000000000000000000000000)⟩
def Z5_3_0E_1_5 : Ball := ⟨(2108145010568870815331944029893 / 25000000000000000000000000000000), (1639971173 / 50000000000000000000000000000000)⟩
def Z5_3_0E_2_4LogWitness : LogWitness := ⟨-2, 43733995727072191717374739083017, 25000000000000000000000000000000⟩
def Z5_3_0E_2_4Log : Ball := ⟨(-1033805565078272286264942253359 / 1250000000000000000000000000000), (3970466953 / 6250000000000000000000000000000)⟩
def Z5_3_0E_2_4 : Ball := ⟨(7233991706521058045956490938163 / 20000000000000000000000000000000), (13891550817 / 50000000000000000000000000000000)⟩
def Z5_3_0E_3_4LogWitness : LogWitness := ⟨-5, 506659647383440715022132422549, 390625000000000000000000000000⟩
def Z5_3_0E_3_4Log : Ball := ⟨(-160282222603130891450597661490659 / 50000000000000000000000000000000), (31763735549 / 25000000000000000000000000000000)⟩
def Z5_3_0E_3_4 : Ball := ⟨(2598673100349966355117959463809 / 20000000000000000000000000000000), (514988899 / 10000000000000000000000000000000)⟩
def Z5_3_0E_4_2LogWitness : LogWitness := ⟨-2, 43733995727072191717374739083017, 25000000000000000000000000000000⟩
def Z5_3_0E_4_2Log : Ball := ⟨(-1033805565078272286264942253359 / 1250000000000000000000000000000), (3970466953 / 6250000000000000000000000000000)⟩
def Z5_3_0E_4_2 : Ball := ⟨(7233991706521058045956490938163 / 20000000000000000000000000000000), (13891550817 / 50000000000000000000000000000000)⟩
def Z5_3_0E_4_3LogWitness : LogWitness := ⟨-5, 506659647383440715022132422549, 390625000000000000000000000000⟩
def Z5_3_0E_4_3Log : Ball := ⟨(-160282222603130891450597661490659 / 50000000000000000000000000000000), (31763735549 / 25000000000000000000000000000000)⟩
def Z5_3_0E_4_3 : Ball := ⟨(2598673100349966355117959463809 / 20000000000000000000000000000000), (514988899 / 10000000000000000000000000000000)⟩
def Z5_3_0E_5_1LogWitness : LogWitness := ⟨-6, 2212727093860282562448201536591, 1562500000000000000000000000000⟩
def Z5_3_0E_5_1Log : Ball := ⟨(-190547222603130891450597651942923 / 50000000000000000000000000000000), (37057691513 / 25000000000000000000000000000000)⟩
def Z5_3_0E_5_1 : Ball := ⟨(2108145010568870815331944029893 / 25000000000000000000000000000000), (1639971173 / 50000000000000000000000000000000)⟩
def Z5_3_0Entropy : Ball := ⟨(7199488009578825658337503516179 / 6250000000000000000000000000000), (3621293297 / 5000000000000000000000000000000)⟩
def Z5_3_0Labels : Ball := ⟨(64678268467290694076293789695021 / 12500000000000000000000000000000), (40127049 / 25000000000000000000000000000)⟩
def Z5_3_0Four : Ball := ⟨(79077244486448345392968796727379 / 12500000000000000000000000000000), (11646703097 / 5000000000000000000000000000000)⟩
def Z5_3_0H1E_4_0LogWitness : LogWitness := ⟨-6, 2212727093860282562448201536591, 1562500000000000000000000000000⟩
def Z5_3_0H1E_4_0Log : Ball := ⟨(-190547222603130891450597651942923 / 50000000000000000000000000000000), (37057691513 / 25000000000000000000000000000000)⟩
def Z5_3_0H1E_4_0 : Ball := ⟨(2108145010568870815331944029893 / 25000000000000000000000000000000), (1639971173 / 50000000000000000000000000000000)⟩
def Z5_3_0H1E_2_1LogWitness : LogWitness := ⟨-2, 43733995727072191717374739083017, 25000000000000000000000000000000⟩
def Z5_3_0H1E_2_1Log : Ball := ⟨(-1033805565078272286264942253359 / 1250000000000000000000000000000), (3970466953 / 6250000000000000000000000000000)⟩
def Z5_3_0H1E_2_1 : Ball := ⟨(7233991706521058045956490938163 / 20000000000000000000000000000000), (13891550817 / 50000000000000000000000000000000)⟩
def Z5_3_0H1E_3_1LogWitness : LogWitness := ⟨-5, 506659647383440715022132422549, 390625000000000000000000000000⟩
def Z5_3_0H1E_3_1Log : Ball := ⟨(-160282222603130891450597661490659 / 50000000000000000000000000000000), (31763735549 / 25000000000000000000000000000000)⟩
def Z5_3_0H1E_3_1 : Ball := ⟨(2598673100349966355117959463809 / 20000000000000000000000000000000), (514988899 / 10000000000000000000000000000000)⟩
def Z5_3_0H1E_1_2LogWitness : LogWitness := ⟨-2, 43733995727072191717374739083017, 25000000000000000000000000000000⟩
def Z5_3_0H1E_1_2Log : Ball := ⟨(-1033805565078272286264942253359 / 1250000000000000000000000000000), (3970466953 / 6250000000000000000000000000000)⟩
def Z5_3_0H1E_1_2 : Ball := ⟨(7233991706521058045956490938163 / 20000000000000000000000000000000), (13891550817 / 50000000000000000000000000000000)⟩
def Z5_3_0H1E_1_3LogWitness : LogWitness := ⟨-5, 506659647383440715022132422549, 390625000000000000000000000000⟩
def Z5_3_0H1E_1_3Log : Ball := ⟨(-160282222603130891450597661490659 / 50000000000000000000000000000000), (31763735549 / 25000000000000000000000000000000)⟩
def Z5_3_0H1E_1_3 : Ball := ⟨(2598673100349966355117959463809 / 20000000000000000000000000000000), (514988899 / 10000000000000000000000000000000)⟩
def Z5_3_0H1E_0_4LogWitness : LogWitness := ⟨-6, 2212727093860282562448201536591, 1562500000000000000000000000000⟩
def Z5_3_0H1E_0_4Log : Ball := ⟨(-190547222603130891450597651942923 / 50000000000000000000000000000000), (37057691513 / 25000000000000000000000000000000)⟩
def Z5_3_0H1E_0_4 : Ball := ⟨(2108145010568870815331944029893 / 25000000000000000000000000000000), (1639971173 / 50000000000000000000000000000000)⟩
def Z5_3_0H1Entropy : Ball := ⟨(7199488009578825658337503516179 / 6250000000000000000000000000000), (3621293297 / 5000000000000000000000000000000)⟩
def Z5_3_0H1Mass : Ball := ⟨1, (97 / 50000000000000000000000000000000)⟩
def Z5_3_0H1MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def Z5_3_0H1MassTermLog : Ball := ⟨0, (5293955969 / 25000000000000000000000000000000)⟩
def Z5_3_0H1MassTerm : Ball := ⟨0, (21175823877 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Four6_0_2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def Z6_0_2Den : Ball := ⟨(249298133952733756367028847637691 / 50000000000000000000000000000000), (253 / 50000000000000000000000000000000)⟩
def Z6_0_2E_2_5LogWitness : LogWitness := ⟨-3, 19726120793130810407094355236181, 12500000000000000000000000000000⟩
def Z6_0_2E_2_5Log : Ball := ⟨(-6492905999703497484642802902389 / 4000000000000000000000000000000), (16940658993 / 20000000000000000000000000000000)⟩
def Z6_0_2E_2_5 : Ball := ⟨(4002495251518592288865068392969 / 12500000000000000000000000000000), (4177168589 / 25000000000000000000000000000000)⟩
def Z6_0_2E_3_5LogWitness : LogWitness := ⟨-3, 20245725524523564193484784547927, 12500000000000000000000000000000⟩
def Z6_0_2E_3_5Log : Ball := ⟨(-79861324996293718558035036279851 / 50000000000000000000000000000000), (21175823741 / 25000000000000000000000000000000)⟩
def Z6_0_2E_3_5 : Ball := ⟨(6467401863598941893694372777521 / 20000000000000000000000000000000), (3429759337 / 20000000000000000000000000000000)⟩
def Z6_0_2E_4_4LogWitness : LogWitness := ⟨-3, 20056307364691250798841720431783, 12500000000000000000000000000000⟩
def Z6_0_2E_4_4Log : Ball := ⟨(-160662649992587437116070072559717 / 100000000000000000000000000000000), (21175823709 / 25000000000000000000000000000000)⟩
def Z6_0_2E_4_4 : Ball := ⟨(32222994902771441455963269141339 / 100000000000000000000000000000000), (3397670639 / 20000000000000000000000000000000)⟩
def Z6_0_2E_5_2LogWitness : LogWitness := ⟨-3, 19726120793130810407094355236181, 12500000000000000000000000000000⟩
def Z6_0_2E_5_2Log : Ball := ⟨(-6492905999703497484642802902389 / 4000000000000000000000000000000), (16940658993 / 20000000000000000000000000000000)⟩
def Z6_0_2E_5_2 : Ball := ⟨(4002495251518592288865068392969 / 12500000000000000000000000000000), (4177168589 / 25000000000000000000000000000000)⟩
def Z6_0_2E_5_3LogWitness : LogWitness := ⟨-3, 20245725524523564193484784547927, 12500000000000000000000000000000⟩
def Z6_0_2E_5_3Log : Ball := ⟨(-79861324996293718558035036279851 / 50000000000000000000000000000000), (21175823741 / 25000000000000000000000000000000)⟩
def Z6_0_2E_5_3 : Ball := ⟨(6467401863598941893694372777521 / 20000000000000000000000000000000), (3429759337 / 20000000000000000000000000000000)⟩
def Z6_0_2Entropy : Ball := ⟨(160936937563058337014748091204053 / 100000000000000000000000000000000), (84703295277 / 100000000000000000000000000000000)⟩
def Z6_0_2Labels : Ball := ⟨(49484222105438999677313478916931 / 20000000000000000000000000000000), (443250503 / 500000000000000000000000000000)⟩
def Z6_0_2Four : Ball := ⟨(102089512022563333850328871447177 / 25000000000000000000000000000000), (173353395877 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Four6_2_0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def Z6_2_0Den : Ball := ⟨(249651494241494819962441097012029 / 50000000000000000000000000000000), (127 / 25000000000000000000000000000000)⟩
def Z6_2_0E_2_5LogWitness : LogWitness := ⟨-3, 19924044508891583790197036118597, 12500000000000000000000000000000⟩
def Z6_2_0E_2_5Log : Ball := ⟨(-3226485833692046100593323447671 / 2000000000000000000000000000000), (84703294967 / 100000000000000000000000000000000)⟩
def Z6_2_0E_2_5 : Ball := ⟨(32142323678894247471214709989819 / 100000000000000000000000000000000), (8438161133 / 50000000000000000000000000000000)⟩
def Z6_2_0E_3_5LogWitness : LogWitness := ⟨-3, 4012399160127629130320676344027, 2500000000000000000000000000000⟩
def Z6_2_0E_3_5Log : Ball := ⟨(-160634291684602305029666172383581 / 100000000000000000000000000000000), (42351647483 / 50000000000000000000000000000000)⟩
def Z6_2_0E_3_5 : Ball := ⟨(32226444852149744429123998456101 / 100000000000000000000000000000000), (4248292889 / 25000000000000000000000000000000)⟩
def Z6_2_0E_4_4LogWitness : LogWitness := ⟨-3, 10013959690470270558199582161267, 6250000000000000000000000000000⟩
def Z6_2_0E_4_4Log : Ball := ⟨(-160804291684602305029666172383561 / 100000000000000000000000000000000), (21175823709 / 25000000000000000000000000000000)⟩
def Z6_2_0E_4_4 : Ball := ⟨(8051438474921156001297838292377 / 25000000000000000000000000000000), (16964307637 / 100000000000000000000000000000000)⟩
def Z6_2_0E_5_2LogWitness : LogWitness := ⟨-3, 19924044508891583790197036118597, 12500000000000000000000000000000⟩
def Z6_2_0E_5_2Log : Ball := ⟨(-3226485833692046100593323447671 / 2000000000000000000000000000000), (84703294967 / 100000000000000000000000000000000)⟩
def Z6_2_0E_5_2 : Ball := ⟨(32142323678894247471214709989819 / 100000000000000000000000000000000), (8438161133 / 50000000000000000000000000000000)⟩
def Z6_2_0E_5_3LogWitness : LogWitness := ⟨-3, 4012399160127629130320676344027, 2500000000000000000000000000000⟩
def Z6_2_0E_5_3Log : Ball := ⟨(-160634291684602305029666172383581 / 100000000000000000000000000000000), (42351647483 / 50000000000000000000000000000000)⟩
def Z6_2_0E_5_3 : Ball := ⟨(32226444852149744429123998456101 / 100000000000000000000000000000000), (4248292889 / 25000000000000000000000000000000)⟩
def Z6_2_0Entropy : Ball := ⟨(40235822740443151951467192515337 / 25000000000000000000000000000000), (84703295281 / 100000000000000000000000000000000)⟩
def Z6_2_0Labels : Ball := ⟨(12415492963912716150755123942433 / 5000000000000000000000000000000), (44435757761 / 50000000000000000000000000000000)⟩
def Z6_2_0Four : Ball := ⟨(51156643780003366352621406113751 / 12500000000000000000000000000000), (173574810803 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Four7_0_1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def Z7_0_1Den : Ball := ⟨2, 0⟩
def Z7_0_1E_4_5LogWitness : LogWitness := ⟨-1, 1, 1⟩
def Z7_0_1E_4_5Log : Ball := ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
def Z7_0_1E_4_5 : Ball := ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
def Z7_0_1E_5_4LogWitness : LogWitness := ⟨-1, 1, 1⟩
def Z7_0_1E_5_4Log : Ball := ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
def Z7_0_1E_5_4 : Ball := ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
def Z7_0_1Entropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def Z7_0_1Labels : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def Z7_0_1Four : Ball := ⟨(18723326709712443708970142577019 / 6250000000000000000000000000000), (63527471049 / 50000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Four7_1_0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def Z7_1_0Den : Ball := ⟨2, 0⟩
def Z7_1_0E_4_5LogWitness : LogWitness := ⟨-1, 1, 1⟩
def Z7_1_0E_4_5Log : Ball := ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
def Z7_1_0E_4_5 : Ball := ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
def Z7_1_0E_5_4LogWitness : LogWitness := ⟨-1, 1, 1⟩
def Z7_1_0E_5_4Log : Ball := ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
def Z7_1_0E_5_4 : Ball := ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
def Z7_1_0Entropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def Z7_1_0Labels : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def Z7_1_0Four : Ball := ⟨(18723326709712443708970142577019 / 6250000000000000000000000000000), (63527471049 / 50000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Four8_0_0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def Z8_0_0Den : Ball := ⟨1, 0⟩
def Z8_0_0E_5_5Log : Ball := .exact 0
def Z8_0_0E_5_5 : Ball := ⟨0, 0⟩
def Z8_0_0Entropy : Ball := ⟨0, 0⟩
def Z8_0_0Labels : Ball := ⟨0, 0⟩
def Z8_0_0Four : Ball := ⟨0, 0⟩

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_InitialProbabilities
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators

def initialProbs (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 16 => ⟨(13145890586460581196177 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 15 => ⟨(42540492515727185225981 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 2, 14 => ⟨(4900971162886037110823 / 2000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 3, 13 => ⟨(14604082434529236400348639 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 4, 12 => ⟨(87208931167140990526853381 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 5, 11 => ⟨(566490078566605123939237597 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 6, 10 => ⟨(15474579554896208143672879691 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 7, 9 => ⟨(21368287213656684042157621491 / 20000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 8, 8 => ⟨(42129637360788428263980836207 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 1, 14 => ⟨(135599977130724015865781 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 2, 13 => ⟨(21858745833413986207356271 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 3, 12 => ⟨(65898522138499345540285359 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 4, 11 => ⟨(5367158627758357107638360451 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 5, 10 => ⟨(18883866194706956799381439539 / 20000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 6, 9 => ⟨(440207333950294144127188221451 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 1, 7, 8 => ⟨(501647985135804550777153238571 / 50000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
  | 2, 2, 12 => ⟨(445614366045202627519431351 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 3, 11 => ⟨(18322793467082776251620533929 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 4, 10 => ⟨(202076397116939330043327073307 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 2, 5, 9 => ⟨(60673895984904206933988362677 / 5000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
  | 2, 6, 8 => ⟨(1867579803495739369034613847927 / 50000000000000000000000000000000), (7 / 25000000000000000000000000000000)⟩
  | 2, 7, 7 => ⟨(2698627660502582229985779719163 / 100000000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩
  | 3, 3, 10 => ⟨(25504648673098899027157162387 / 20000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 3, 4, 9 => ⟨(1920317525954107858922782450019 / 100000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 3, 5, 8 => ⟨(951656630773752719335842630811 / 12500000000000000000000000000000), (27 / 50000000000000000000000000000000)⟩
  | 3, 6, 7 => ⟨(7428644231760528410384248566849 / 50000000000000000000000000000000), (11 / 10000000000000000000000000000000)⟩
  | 4, 4, 8 => ⟨(4772848850473901186247710959367 / 100000000000000000000000000000000), (7 / 20000000000000000000000000000000)⟩
  | 4, 5, 7 => ⟨(23993682114587954796865544628907 / 100000000000000000000000000000000), (43 / 25000000000000000000000000000000)⟩
  | 4, 6, 6 => ⟨(1012633788103277317843835873381 / 6250000000000000000000000000000), (1 / 800000000000000000000000000000)⟩
  | 5, 5, 6 => ⟨(20868552691024433430449278430017 / 100000000000000000000000000000000), (153 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal1_1_6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def secondProbs (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(69961933900937038973810717 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(12225475568090238873041151441 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(237411073357556581276502992929 / 50000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(4230776649784552867243147046861 / 100000000000000000000000000000000), (51 / 100000000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(3547397943227606492584968866981 / 50000000000000000000000000000000), (81 / 100000000000000000000000000000000)⟩
  | 0, 5, 3 => ⟨(479798427065252805047798804001 / 50000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
  | 0, 6, 2 => ⟨(8873532193375516366129001309 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 7, 1 => ⟨(37761738676306841647289119 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 8, 0 => ⟨0, 0⟩
  | 1, 0, 7 => ⟨(6438692289104433119668731959 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(396449683591614668262742331113 / 100000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(7475754434060585075518103043991 / 100000000000000000000000000000000), (83 / 100000000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨(30737266894969885701115253765617 / 100000000000000000000000000000000), (59 / 20000000000000000000000000000000)⟩
  | 1, 4, 3 => ⟨(14261596080166754120520730143589 / 100000000000000000000000000000000), (31 / 20000000000000000000000000000000)⟩
  | 1, 5, 2 => ⟨(626067956486069015200470969959 / 100000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | 1, 6, 1 => ⟨(3285158323719550978069819523 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 7, 0 => ⟨(975621486089752789548109 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(90413820613809065387009577181 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(168682821311829360842363366021 / 5000000000000000000000000000000), (41 / 100000000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨(16597878638086061586510503770607 / 50000000000000000000000000000000), (311 / 100000000000000000000000000000000)⟩
  | 2, 3, 3 => ⟨(40531425822231342208196361227163 / 100000000000000000000000000000000), (363 / 100000000000000000000000000000000)⟩
  | 2, 4, 2 => ⟨(7081993762541297835979778514079 / 100000000000000000000000000000000), (17 / 20000000000000000000000000000000)⟩
  | 2, 5, 1 => ⟨(9821070435865618341900223303 / 10000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 2, 6, 0 => ⟨(40664393453437432199665563 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 3, 0, 5 => ⟨(66372901003719256392546735253 / 20000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 3, 1, 4 => ⟨(7458452229072232749356247455867 / 100000000000000000000000000000000), (43 / 50000000000000000000000000000000)⟩
  | 3, 2, 3 => ⟨(5834298510241192163399383030477 / 25000000000000000000000000000000), (229 / 100000000000000000000000000000000)⟩
  | 3, 3, 2 => ⟨(11105258047046141314482148827847 / 100000000000000000000000000000000), (61 / 50000000000000000000000000000000)⟩
  | 3, 4, 1 => ⟨(115877797524955486474569484493 / 20000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
  | 3, 5, 0 => ⟨(1474745044110606848348633769 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 4, 0, 4 => ⟨(127180720981131837029517845441 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 4, 1, 3 => ⟨(229386345126997321904071678101 / 10000000000000000000000000000000), (7 / 25000000000000000000000000000000)⟩
  | 4, 2, 2 => ⟨(596904226304951333077005521279 / 20000000000000000000000000000000), (37 / 100000000000000000000000000000000)⟩
  | 4, 3, 1 => ⟨(204433827117624377981263345963 / 50000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
  | 4, 4, 0 => ⟨(157961720646067031611604423 / 2000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 5, 0, 3 => ⟨(1281566078537013099196608213 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 5, 1, 2 => ⟨(9204811902836787308641159891 / 12500000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 5, 2, 1 => ⟨(3169349558485787912791048423 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 5, 3, 0 => ⟨(45111958926755639262102049 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 6, 0, 2 => ⟨0, 0⟩
  | 6, 1, 1 => ⟨0, 0⟩
  | 6, 2, 0 => ⟨0, 0⟩
  | 7, 0, 1 => ⟨0, 0⟩
  | 7, 1, 0 => ⟨0, 0⟩
  | 8, 0, 0 => ⟨0, 0⟩
  | _, _, _ => (.exact 0)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_NativeInterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def fourRateBalls (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => Z0_0_8Four
  | 0, 1, 7 => Z0_1_7Four
  | 0, 2, 6 => Z0_2_6Four
  | 0, 3, 5 => Z0_3_5Four
  | 0, 4, 4 => Z0_4_4Four
  | 0, 5, 3 => Z0_5_3Four
  | 0, 6, 2 => Z0_6_2Four
  | 0, 7, 1 => Z0_7_1Four
  | 0, 8, 0 => Z0_8_0Four
  | 1, 0, 7 => Z1_0_7Four
  | 1, 7, 0 => Z1_7_0Four
  | 2, 0, 6 => Z2_0_6Four
  | 2, 6, 0 => Z2_6_0Four
  | 3, 0, 5 => Z3_0_5Four
  | 3, 5, 0 => Z3_5_0Four
  | 4, 0, 4 => Z4_0_4Four
  | 4, 4, 0 => Z4_4_0Four
  | 5, 0, 3 => Z5_0_3Four
  | 5, 3, 0 => Z5_3_0Four
  | 6, 0, 2 => Z6_0_2Four
  | 6, 2, 0 => Z6_2_0Four
  | 7, 0, 1 => Z7_0_1Four
  | 7, 1, 0 => Z7_1_0Four
  | 8, 0, 0 => Z8_0_0Four
  | _, _, _ => (.exact 0)
def nativeS1Ball : Ball := ⟨(88236223598149624413852945550479 / 100000000000000000000000000000000), (32131158713 / 100000000000000000000000000000000)⟩
def nativeS2Ball : Ball := ⟨(233614080284104308981345775925091 / 20000000000000000000000000000000), (7783352389 / 1562500000000000000000000000000)⟩
def nativeSBall : Ball := ⟨(1259477032159467636236050651212461 / 100000000000000000000000000000000), (531265093341 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def nativeTBall : Ball := ⟨(7331109571865792290176153698167 / 3125000000000000000000000000000), (637 / 25000000000000000000000000000000)⟩
def nativeBBall : Ball := ⟨(926453577659126052246485196733 / 800000000000000000000000000000), (100635147743 / 100000000000000000000000000000000)⟩
def nativeHighBall : Ball := ⟨(81304606881836826911861830543749 / 50000000000000000000000000000000), (99355063329 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB3_2_3I2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB3_2_3I2S2_0_2Value (a : Fin 6) : ℝ := (littleLaw (shape 3 2 3) (shape 2 0 2) ((stageBPriority (shape 3 2 3)) 2) a : ℝ)
def CB3_2_3I2S2_0_2Terms (a : Fin 6) : Ball :=
  match a.val with
  | 2 => ⟨(5188625969804346635566112183549 / 50000000000000000000000000000000), (37690213299 / 100000000000000000000000000000000)⟩
  | 3 => ⟨(12143934705973138211003215087279 / 50000000000000000000000000000000), (11653585169 / 100000000000000000000000000000000)⟩
  | _ => (.exact 0)
def CB3_2_3I2S2_0_2Entropy : Ball := ⟨(4333140168944371211642331817707 / 12500000000000000000000000000000), (12335949617 / 25000000000000000000000000000000)⟩
def CB3_2_3I2S2_0_2MassTermLog : Ball := .exact 0
def CB3_2_3I2S2_0_2H : Ball := ⟨(4333140168944371211642331817707 / 12500000000000000000000000000000), (12335949617 / 25000000000000000000000000000000)⟩
def CB3_2_3I2S3_0_1Value (a : Fin 6) : ℝ := (littleLaw (shape 3 2 3) (shape 3 0 1) ((stageBPriority (shape 3 2 3)) 2) a : ℝ)
def CB3_2_3I2S3_0_1E_1Log : Ball := .exact 0
def CB3_2_3I2S3_0_1E_1 : Ball := ⟨0, 0⟩
def CB3_2_3I2S3_0_1Terms (a : Fin 6) : Ball :=
  match a.val with
  | 1 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB3_2_3I2S3_0_1Entropy : Ball := ⟨0, 0⟩
def CB3_2_3I2S3_0_1Mass : Ball := ⟨1, 0⟩
def CB3_2_3I2S3_0_1MassTermLog : Ball := .exact 0
def CB3_2_3I2S3_0_1MassTerm : Ball := ⟨0, 0⟩
def CB3_2_3I2S3_0_1H : Ball := ⟨0, 0⟩
def CB3_2_3I2Singleton : Ball := ⟨(2997173016171163830905521820877 / 50000000000000000000000000000000), (1068609679 / 12500000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB3_3_2I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB3_3_2I0Value (a : Fin 17) : ℝ := marginal (below (shape 3 3 2)) (fun u => (stageBLaw (shape 3 3 2) u : ℝ)) ((stageBPriority (shape 3 3 2)) 0) a
def CB3_3_2I0Entropy : Ball := ⟨(8152980245100155388073740378279 / 10000000000000000000000000000000), (16581803873 / 25000000000000000000000000000000)⟩
def CB3_3_2I0Mass : Ball := ⟨(50000000000000000000000000000001 / 50000000000000000000000000000000), (29 / 25000000000000000000000000000000)⟩
def CB3_3_2I0MassTermLogWitness : LogWitness := ⟨0, 50000000000000000000000000000001, 50000000000000000000000000000000⟩
def CB3_3_2I0MassTermLog : Ball := ⟨(1 / 50000000000000000000000000000000), (10587911899 / 50000000000000000000000000000000)⟩
def CB3_3_2I0MassTerm : Ball := ⟨(-1 / 50000000000000000000000000000000), (21175823799 / 100000000000000000000000000000000)⟩
def CB3_3_2I0H : Ball := ⟨(10191225306375194235092175472849 / 12500000000000000000000000000000), (87503039291 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB3_3_2I1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB3_3_2I1PairEntropy : Ball := ⟨(98531909890783673553573029138491 / 100000000000000000000000000000000), (1858951991 / 3125000000000000000000000000000)⟩
def CB3_3_2I1PairMass : Ball := ⟨(50000000000000000000000000000001 / 50000000000000000000000000000000), (3 / 2500000000000000000000000000000)⟩
def CB3_3_2I1PairMassTermLogWitness : LogWitness := ⟨0, 50000000000000000000000000000001, 50000000000000000000000000000000⟩
def CB3_3_2I1PairMassTermLog : Ball := ⟨(1 / 50000000000000000000000000000000), (10587911901 / 50000000000000000000000000000000)⟩
def CB3_3_2I1PairMassTerm : Ball := ⟨(-1 / 50000000000000000000000000000000), (21175823803 / 100000000000000000000000000000000)⟩
def CB3_3_2I1PairH : Ball := ⟨(98531909890783673553573029138493 / 100000000000000000000000000000000), (16132457503 / 20000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB3_3_2I1R0Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 3 2)) (fun u => (stageBLaw (shape 3 3 2) u : ℝ)) (stageBPriority (shape 3 3 2)) 1 (fun u a => (littleLaw (shape 3 3 2) u ((stageBPriority (shape 3 3 2)) 1) a : ℝ)) 0 a
def CB3_3_2I1R0Entropy : Ball := ⟨(7802482778836922680991273189919 / 25000000000000000000000000000000), (3132307647 / 20000000000000000000000000000000)⟩
def CB3_3_2I1R0Mass : Ball := ⟨(18489880681829481042841850473249 / 100000000000000000000000000000000), (39 / 100000000000000000000000000000000)⟩
def CB3_3_2I1R0MassTermLogWitness : LogWitness := ⟨-3, 18489880681829481042841850473249, 12500000000000000000000000000000⟩
def CB3_3_2I1R0MassTermLog : Ball := ⟨(-42198664843222266306978424190797 / 25000000000000000000000000000000), (42351647471 / 50000000000000000000000000000000)⟩
def CB3_3_2I1R0MassTerm : Ball := ⟨(7802482778836922680991273189919 / 25000000000000000000000000000000), (3132307647 / 20000000000000000000000000000000)⟩
def CB3_3_2I1R0H : Ball := ⟨0, (3132307647 / 10000000000000000000000000000000)⟩
def CB3_3_2I1R1Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 3 2)) (fun u => (stageBLaw (shape 3 3 2) u : ℝ)) (stageBPriority (shape 3 3 2)) 1 (fun u a => (littleLaw (shape 3 3 2) u ((stageBPriority (shape 3 3 2)) 1) a : ℝ)) 1 a
def CB3_3_2I1R1Entropy : Ball := ⟨(29183941801875615336802034527761 / 100000000000000000000000000000000), (3327726499 / 12500000000000000000000000000000)⟩
def CB3_3_2I1R1Mass : Ball := ⟨(31429488099598970025128198206017 / 50000000000000000000000000000000), (37 / 100000000000000000000000000000000)⟩
def CB3_3_2I1R1MassTermLogWitness : LogWitness := ⟨-1, 31429488099598970025128198206017, 25000000000000000000000000000000⟩
def CB3_3_2I1R1MassTermLog : Ball := ⟨(-23213822087550952568918865056779 / 50000000000000000000000000000000), (661744491 / 1562500000000000000000000000000)⟩
def CB3_3_2I1R1MassTerm : Ball := ⟨(29183941801875615336802034527761 / 100000000000000000000000000000000), (3327726499 / 12500000000000000000000000000000)⟩
def CB3_3_2I1R1H : Ball := ⟨0, (3327726499 / 6250000000000000000000000000000)⟩
def CB3_3_2I1R2Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 3 2)) (fun u => (stageBLaw (shape 3 3 2) u : ℝ)) (stageBPriority (shape 3 3 2)) 1 (fun u a => (littleLaw (shape 3 3 2) u ((stageBPriority (shape 3 3 2)) 1) a : ℝ)) 2 a
def CB3_3_2I1R2Entropy : Ball := ⟨(33467591687523526003549066835433 / 100000000000000000000000000000000), (15475282607 / 100000000000000000000000000000000)⟩
def CB3_3_2I1R2Mass : Ball := ⟨(1083200304972307881404701884791 / 6250000000000000000000000000000), (9 / 25000000000000000000000000000000)⟩
def CB3_3_2I1R2MassTermLogWitness : LogWitness := ⟨-3, 1083200304972307881404701884791, 781250000000000000000000000000⟩
def CB3_3_2I1R2MassTermLog : Ball := ⟨(-3505323118049849361698630637263 / 2000000000000000000000000000000), (84703294939 / 100000000000000000000000000000000)⟩
def CB3_3_2I1R2MassTerm : Ball := ⟨(6075147312796924816473816672937 / 20000000000000000000000000000000), (14680101649 / 100000000000000000000000000000000)⟩
def CB3_3_2I1R2H : Ball := ⟨(772963780884725480294995867687 / 25000000000000000000000000000000), (471177879 / 1562500000000000000000000000000)⟩
def CB3_3_2I1R3Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 3 2)) (fun u => (stageBLaw (shape 3 3 2) u : ℝ)) (stageBPriority (shape 3 3 2)) 1 (fun u a => (littleLaw (shape 3 3 2) u ((stageBPriority (shape 3 3 2)) 1) a : ℝ)) 3 a
def CB3_3_2I1R3Entropy : Ball := ⟨0, 0⟩
def CB3_3_2I1R3Mass : Ball := ⟨0, 0⟩
def CB3_3_2I1R3MassTerm : Ball := .exact 0
def CB3_3_2I1R3H : Ball := ⟨0, 0⟩
def CB3_3_2I1R4Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 3 2)) (fun u => (stageBLaw (shape 3 3 2) u : ℝ)) (stageBPriority (shape 3 3 2)) 1 (fun u a => (littleLaw (shape 3 3 2) u ((stageBPriority (shape 3 3 2)) 1) a : ℝ)) 4 a
def CB3_3_2I1R4Entropy : Ball := ⟨0, 0⟩
def CB3_3_2I1R4Mass : Ball := ⟨0, 0⟩
def CB3_3_2I1R4MassTerm : Ball := .exact 0
def CB3_3_2I1R4H : Ball := ⟨0, 0⟩
def CB3_3_2I1R5Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 3 2)) (fun u => (stageBLaw (shape 3 3 2) u : ℝ)) (stageBPriority (shape 3 3 2)) 1 (fun u a => (littleLaw (shape 3 3 2) u ((stageBPriority (shape 3 3 2)) 1) a : ℝ)) 5 a
def CB3_3_2I1R5Entropy : Ball := ⟨0, 0⟩
def CB3_3_2I1R5Mass : Ball := ⟨0, 0⟩
def CB3_3_2I1R5MassTerm : Ball := .exact 0
def CB3_3_2I1R5H : Ball := ⟨0, 0⟩
def CB3_3_2I1R6Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 3 2)) (fun u => (stageBLaw (shape 3 3 2) u : ℝ)) (stageBPriority (shape 3 3 2)) 1 (fun u a => (littleLaw (shape 3 3 2) u ((stageBPriority (shape 3 3 2)) 1) a : ℝ)) 6 a
def CB3_3_2I1R6Entropy : Ball := ⟨0, 0⟩
def CB3_3_2I1R6Mass : Ball := ⟨0, 0⟩
def CB3_3_2I1R6MassTerm : Ball := .exact 0
def CB3_3_2I1R6H : Ball := ⟨0, 0⟩
def CB3_3_2I1R7Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 3 2)) (fun u => (stageBLaw (shape 3 3 2) u : ℝ)) (stageBPriority (shape 3 3 2)) 1 (fun u a => (littleLaw (shape 3 3 2) u ((stageBPriority (shape 3 3 2)) 1) a : ℝ)) 7 a
def CB3_3_2I1R7Entropy : Ball := ⟨0, 0⟩
def CB3_3_2I1R7Mass : Ball := ⟨0, 0⟩
def CB3_3_2I1R7MassTerm : Ball := .exact 0
def CB3_3_2I1R7H : Ball := ⟨0, 0⟩
def CB3_3_2I1R8Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 3 2)) (fun u => (stageBLaw (shape 3 3 2) u : ℝ)) (stageBPriority (shape 3 3 2)) 1 (fun u a => (littleLaw (shape 3 3 2) u ((stageBPriority (shape 3 3 2)) 1) a : ℝ)) 8 a
def CB3_3_2I1R8Entropy : Ball := ⟨0, 0⟩
def CB3_3_2I1R8Mass : Ball := ⟨0, 0⟩
def CB3_3_2I1R8MassTerm : Ball := .exact 0
def CB3_3_2I1R8H : Ball := ⟨0, 0⟩
def CB3_3_2I1R9Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 3 2)) (fun u => (stageBLaw (shape 3 3 2) u : ℝ)) (stageBPriority (shape 3 3 2)) 1 (fun u a => (littleLaw (shape 3 3 2) u ((stageBPriority (shape 3 3 2)) 1) a : ℝ)) 9 a
def CB3_3_2I1R9Entropy : Ball := ⟨0, 0⟩
def CB3_3_2I1R9Mass : Ball := ⟨0, 0⟩
def CB3_3_2I1R9MassTerm : Ball := .exact 0
def CB3_3_2I1R9H : Ball := ⟨0, 0⟩
def CB3_3_2I1R10Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 3 2)) (fun u => (stageBLaw (shape 3 3 2) u : ℝ)) (stageBPriority (shape 3 3 2)) 1 (fun u a => (littleLaw (shape 3 3 2) u ((stageBPriority (shape 3 3 2)) 1) a : ℝ)) 10 a
def CB3_3_2I1R10Entropy : Ball := ⟨0, 0⟩
def CB3_3_2I1R10Mass : Ball := ⟨0, 0⟩
def CB3_3_2I1R10MassTerm : Ball := .exact 0
def CB3_3_2I1R10H : Ball := ⟨0, 0⟩
def CB3_3_2I1R11Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 3 2)) (fun u => (stageBLaw (shape 3 3 2) u : ℝ)) (stageBPriority (shape 3 3 2)) 1 (fun u a => (littleLaw (shape 3 3 2) u ((stageBPriority (shape 3 3 2)) 1) a : ℝ)) 11 a
def CB3_3_2I1R11Entropy : Ball := ⟨0, 0⟩
def CB3_3_2I1R11Mass : Ball := ⟨0, 0⟩
def CB3_3_2I1R11MassTerm : Ball := .exact 0
def CB3_3_2I1R11H : Ball := ⟨0, 0⟩
def CB3_3_2I1R12Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 3 2)) (fun u => (stageBLaw (shape 3 3 2) u : ℝ)) (stageBPriority (shape 3 3 2)) 1 (fun u a => (littleLaw (shape 3 3 2) u ((stageBPriority (shape 3 3 2)) 1) a : ℝ)) 12 a
def CB3_3_2I1R12Entropy : Ball := ⟨0, 0⟩
def CB3_3_2I1R12Mass : Ball := ⟨0, 0⟩
def CB3_3_2I1R12MassTerm : Ball := .exact 0
def CB3_3_2I1R12H : Ball := ⟨0, 0⟩
def CB3_3_2I1R13Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 3 2)) (fun u => (stageBLaw (shape 3 3 2) u : ℝ)) (stageBPriority (shape 3 3 2)) 1 (fun u a => (littleLaw (shape 3 3 2) u ((stageBPriority (shape 3 3 2)) 1) a : ℝ)) 13 a
def CB3_3_2I1R13Entropy : Ball := ⟨0, 0⟩
def CB3_3_2I1R13Mass : Ball := ⟨0, 0⟩
def CB3_3_2I1R13MassTerm : Ball := .exact 0
def CB3_3_2I1R13H : Ball := ⟨0, 0⟩
def CB3_3_2I1R14Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 3 2)) (fun u => (stageBLaw (shape 3 3 2) u : ℝ)) (stageBPriority (shape 3 3 2)) 1 (fun u a => (littleLaw (shape 3 3 2) u ((stageBPriority (shape 3 3 2)) 1) a : ℝ)) 14 a
def CB3_3_2I1R14Entropy : Ball := ⟨0, 0⟩
def CB3_3_2I1R14Mass : Ball := ⟨0, 0⟩
def CB3_3_2I1R14MassTerm : Ball := .exact 0
def CB3_3_2I1R14H : Ball := ⟨0, 0⟩
def CB3_3_2I1R15Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 3 2)) (fun u => (stageBLaw (shape 3 3 2) u : ℝ)) (stageBPriority (shape 3 3 2)) 1 (fun u a => (littleLaw (shape 3 3 2) u ((stageBPriority (shape 3 3 2)) 1) a : ℝ)) 15 a
def CB3_3_2I1R15Entropy : Ball := ⟨0, 0⟩
def CB3_3_2I1R15Mass : Ball := ⟨0, 0⟩
def CB3_3_2I1R15MassTerm : Ball := .exact 0
def CB3_3_2I1R15H : Ball := ⟨0, 0⟩
def CB3_3_2I1R16Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 3 2)) (fun u => (stageBLaw (shape 3 3 2) u : ℝ)) (stageBPriority (shape 3 3 2)) 1 (fun u a => (littleLaw (shape 3 3 2) u ((stageBPriority (shape 3 3 2)) 1) a : ℝ)) 16 a
def CB3_3_2I1R16Entropy : Ball := ⟨0, 0⟩
def CB3_3_2I1R16Mass : Ball := ⟨0, 0⟩
def CB3_3_2I1R16MassTerm : Ball := .exact 0
def CB3_3_2I1R16H : Ball := ⟨0, 0⟩
def CB3_3_2I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CB3_3_2I1R0H
  | 1 => CB3_3_2I1R1H
  | 2 => CB3_3_2I1R2H
  | 3 => CB3_3_2I1R3H
  | 4 => CB3_3_2I1R4H
  | 5 => CB3_3_2I1R5H
  | 6 => CB3_3_2I1R6H
  | 7 => CB3_3_2I1R7H
  | 8 => CB3_3_2I1R8H
  | 9 => CB3_3_2I1R9H
  | 10 => CB3_3_2I1R10H
  | 11 => CB3_3_2I1R11H
  | 12 => CB3_3_2I1R12H
  | 13 => CB3_3_2I1R13H
  | 14 => CB3_3_2I1R14H
  | 15 => CB3_3_2I1R15H
  | 16 => CB3_3_2I1R16H
  | _ => (.exact 0)
def CB3_3_2I1S2_0_2Value (a : Fin 6) : ℝ := (littleLaw (shape 3 3 2) (shape 2 0 2) ((stageBPriority (shape 3 3 2)) 1) a : ℝ)
def CB3_3_2I1S2_0_2E_2LogWitness : LogWitness := ⟨-1, 179521, 100000⟩
def CB3_3_2I1S2_0_2E_2Log : Ball := ⟨(-10802517381923768407763481952009 / 100000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def CB3_3_2I1S2_0_2E_2 : Ball := ⟨(9696393614601684141650540217533 / 100000000000000000000000000000000), (19007525217 / 50000000000000000000000000000000)⟩
def CB3_3_2I1S2_0_2E_3LogWitness : LogWitness := ⟨-4, 20479, 12500⟩
def CB3_3_2I1S2_0_2E_3Log : Ball := ⟨(-45578347913877226878717459404093 / 20000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
def CB3_3_2I1S2_0_2E_3 : Ball := ⟨(23334974673207293231231371278411 / 100000000000000000000000000000000), (10841492331 / 100000000000000000000000000000000)⟩
def CB3_3_2I1S2_0_2Terms (a : Fin 6) : Ball :=
  match a.val with
  | 2 => ⟨(9696393614601684141650540217533 / 100000000000000000000000000000000), (19007525217 / 50000000000000000000000000000000)⟩
  | 3 => ⟨(23334974673207293231231371278411 / 100000000000000000000000000000000), (10841492331 / 100000000000000000000000000000000)⟩
  | _ => (.exact 0)
def CB3_3_2I1S2_0_2Entropy : Ball := ⟨(4128921035976122171610238936993 / 12500000000000000000000000000000), (9771308553 / 20000000000000000000000000000000)⟩
def CB3_3_2I1S2_0_2Mass : Ball := ⟨1, 0⟩
def CB3_3_2I1S2_0_2MassTermLog : Ball := .exact 0
def CB3_3_2I1S2_0_2MassTerm : Ball := ⟨0, 0⟩
def CB3_3_2I1S2_0_2H : Ball := ⟨(4128921035976122171610238936993 / 12500000000000000000000000000000), (9771308553 / 20000000000000000000000000000000)⟩
def CB3_3_2I1S3_0_1Value (a : Fin 6) : ℝ := (littleLaw (shape 3 3 2) (shape 3 0 1) ((stageBPriority (shape 3 3 2)) 1) a : ℝ)
def CB3_3_2I1S3_0_1E_1Log : Ball := .exact 0
def CB3_3_2I1S3_0_1E_1 : Ball := ⟨0, 0⟩
def CB3_3_2I1S3_0_1Terms (a : Fin 6) : Ball :=
  match a.val with
  | 1 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB3_3_2I1S3_0_1Entropy : Ball := ⟨0, 0⟩
def CB3_3_2I1S3_0_1Mass : Ball := ⟨1, 0⟩
def CB3_3_2I1S3_0_1MassTermLog : Ball := .exact 0
def CB3_3_2I1S3_0_1MassTerm : Ball := ⟨0, 0⟩
def CB3_3_2I1S3_0_1H : Ball := ⟨0, 0⟩
def CB3_3_2I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 2, 0, 2 => CB3_3_2I1S2_0_2H
  | 3, 0, 1 => CB3_3_2I1S3_0_1H
  | _, _, _ => (.exact 0)
def CB3_3_2I1Singleton : Ball := ⟨(95681617877593240735588627781 / 25000000000000000000000000000000), (566088941 / 100000000000000000000000000000000)⟩
def CB3_3_2I1Group : Ball := ⟨(217161349690579680257646123867 / 6250000000000000000000000000000), (115288173651 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB3_3_2I1H : Ball := ⟨(91582746700685123785328353174749 / 100000000000000000000000000000000), (311238634817 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB3_3_2I2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB3_3_2I2PairEntropy : Ball := ⟨(24634116794242484698919585607647 / 25000000000000000000000000000000), (34900901067 / 50000000000000000000000000000000)⟩
def CB3_3_2I2PairMass : Ball := ⟨(50000000000000000000000000000001 / 50000000000000000000000000000000), (3 / 2500000000000000000000000000000)⟩
def CB3_3_2I2PairMassTermLogWitness : LogWitness := ⟨0, 50000000000000000000000000000001, 50000000000000000000000000000000⟩
def CB3_3_2I2PairMassTermLog : Ball := ⟨(1 / 50000000000000000000000000000000), (10587911901 / 50000000000000000000000000000000)⟩
def CB3_3_2I2PairMassTerm : Ball := ⟨(-1 / 50000000000000000000000000000000), (21175823803 / 100000000000000000000000000000000)⟩
def CB3_3_2I2PairH : Ball := ⟨(9853646717696993879567834243059 / 10000000000000000000000000000000), (90977625937 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB3_3_2I2R0Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 3 2)) (fun u => (stageBLaw (shape 3 3 2) u : ℝ)) (stageBPriority (shape 3 3 2)) 2 (fun u a => (littleLaw (shape 3 3 2) u ((stageBPriority (shape 3 3 2)) 2) a : ℝ)) 0 a
def CB3_3_2I2R0Entropy : Ball := ⟨(2856072620515310018139553368893 / 50000000000000000000000000000000), (1118031191 / 50000000000000000000000000000000)⟩
def CB3_3_2I2R0Mass : Ball := ⟨(1319938239415652804426522958063 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
def CB3_3_2I2R0MassTermLogWitness : LogWitness := ⟨-7, 1319938239415652804426522958063, 781250000000000000000000000000⟩
def CB3_3_2I2R0MassTermLog : Ball := ⟨(-432758523880589468654268795850129 / 100000000000000000000000000000000), (84703294921 / 50000000000000000000000000000000)⟩
def CB3_3_2I2R0MassTerm : Ball := ⟨(2856072620515310018139553368893 / 50000000000000000000000000000000), (1118031191 / 50000000000000000000000000000000)⟩
def CB3_3_2I2R0H : Ball := ⟨0, (1118031191 / 25000000000000000000000000000000)⟩
def CB3_3_2I2R1Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 3 2)) (fun u => (stageBLaw (shape 3 3 2) u : ℝ)) (stageBPriority (shape 3 3 2)) 2 (fun u a => (littleLaw (shape 3 3 2) u ((stageBPriority (shape 3 3 2)) 2) a : ℝ)) 1 a
def CB3_3_2I2R1Entropy : Ball := ⟨(35356016446905663631148847220423 / 100000000000000000000000000000000), (15093867457 / 50000000000000000000000000000000)⟩
def CB3_3_2I2R1Mass : Ball := ⟨(11879795595388115584820017693353 / 25000000000000000000000000000000), (3 / 6250000000000000000000000000000)⟩
def CB3_3_2I2R1MassTermLogWitness : LogWitness := ⟨-2, 11879795595388115584820017693353, 6250000000000000000000000000000⟩
def CB3_3_2I2R1MassTermLog : Ball := ⟨(-74403671685713407784409267822843 / 100000000000000000000000000000000), (1270549423 / 2000000000000000000000000000000)⟩
def CB3_3_2I2R1MassTerm : Ball := ⟨(35356016446905663631148847220423 / 100000000000000000000000000000000), (15093867457 / 50000000000000000000000000000000)⟩
def CB3_3_2I2R1H : Ball := ⟨0, (15093867457 / 25000000000000000000000000000000)⟩
def CB3_3_2I2R2Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 3 2)) (fun u => (stageBLaw (shape 3 3 2) u : ℝ)) (stageBPriority (shape 3 3 2)) 2 (fun u a => (littleLaw (shape 3 3 2) u ((stageBPriority (shape 3 3 2)) 2) a : ℝ)) 2 a
def CB3_3_2I2R2Entropy : Ball := ⟨(1866532131543782971708336586569 / 5000000000000000000000000000000), (1260880369 / 6250000000000000000000000000000)⟩
def CB3_3_2I2R2Mass : Ball := ⟨(15674428440513710546549123442641 / 50000000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩
def CB3_3_2I2R2MassTermLogWitness : LogWitness := ⟨-2, 15674428440513710546549123442641, 12500000000000000000000000000000⟩
def CB3_3_2I2R2MassTermLog : Ball := ⟨(-57999619134953985371965508531891 / 50000000000000000000000000000000), (7940933889 / 12500000000000000000000000000000)⟩
def CB3_3_2I2R2MassTerm : Ball := ⟨(9091108797078859624511383556729 / 25000000000000000000000000000000), (19915136023 / 100000000000000000000000000000000)⟩
def CB3_3_2I2R2H : Ball := ⟨(60387965160013808507574844029 / 6250000000000000000000000000000), (40089221927 / 100000000000000000000000000000000)⟩
def CB3_3_2I2R3Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 3 2)) (fun u => (stageBLaw (shape 3 3 2) u : ℝ)) (stageBPriority (shape 3 3 2)) 2 (fun u a => (littleLaw (shape 3 3 2) u ((stageBPriority (shape 3 3 2)) 2) a : ℝ)) 3 a
def CB3_3_2I2R3Entropy : Ball := ⟨0, 0⟩
def CB3_3_2I2R3Mass : Ball := ⟨0, 0⟩
def CB3_3_2I2R3MassTerm : Ball := .exact 0
def CB3_3_2I2R3H : Ball := ⟨0, 0⟩
def CB3_3_2I2R4Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 3 2)) (fun u => (stageBLaw (shape 3 3 2) u : ℝ)) (stageBPriority (shape 3 3 2)) 2 (fun u a => (littleLaw (shape 3 3 2) u ((stageBPriority (shape 3 3 2)) 2) a : ℝ)) 4 a
def CB3_3_2I2R4Entropy : Ball := ⟨0, 0⟩
def CB3_3_2I2R4Mass : Ball := ⟨0, 0⟩
def CB3_3_2I2R4MassTerm : Ball := .exact 0
def CB3_3_2I2R4H : Ball := ⟨0, 0⟩
def CB3_3_2I2R5Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 3 2)) (fun u => (stageBLaw (shape 3 3 2) u : ℝ)) (stageBPriority (shape 3 3 2)) 2 (fun u a => (littleLaw (shape 3 3 2) u ((stageBPriority (shape 3 3 2)) 2) a : ℝ)) 5 a
def CB3_3_2I2R5Entropy : Ball := ⟨0, 0⟩
def CB3_3_2I2R5Mass : Ball := ⟨0, 0⟩
def CB3_3_2I2R5MassTerm : Ball := .exact 0
def CB3_3_2I2R5H : Ball := ⟨0, 0⟩
def CB3_3_2I2R6Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 3 2)) (fun u => (stageBLaw (shape 3 3 2) u : ℝ)) (stageBPriority (shape 3 3 2)) 2 (fun u a => (littleLaw (shape 3 3 2) u ((stageBPriority (shape 3 3 2)) 2) a : ℝ)) 6 a
def CB3_3_2I2R6Entropy : Ball := ⟨0, 0⟩
def CB3_3_2I2R6Mass : Ball := ⟨0, 0⟩
def CB3_3_2I2R6MassTerm : Ball := .exact 0
def CB3_3_2I2R6H : Ball := ⟨0, 0⟩
def CB3_3_2I2R7Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 3 2)) (fun u => (stageBLaw (shape 3 3 2) u : ℝ)) (stageBPriority (shape 3 3 2)) 2 (fun u a => (littleLaw (shape 3 3 2) u ((stageBPriority (shape 3 3 2)) 2) a : ℝ)) 7 a
def CB3_3_2I2R7Entropy : Ball := ⟨0, 0⟩
def CB3_3_2I2R7Mass : Ball := ⟨0, 0⟩
def CB3_3_2I2R7MassTerm : Ball := .exact 0
def CB3_3_2I2R7H : Ball := ⟨0, 0⟩
def CB3_3_2I2R8Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 3 2)) (fun u => (stageBLaw (shape 3 3 2) u : ℝ)) (stageBPriority (shape 3 3 2)) 2 (fun u a => (littleLaw (shape 3 3 2) u ((stageBPriority (shape 3 3 2)) 2) a : ℝ)) 8 a
def CB3_3_2I2R8Entropy : Ball := ⟨0, 0⟩
def CB3_3_2I2R8Mass : Ball := ⟨0, 0⟩
def CB3_3_2I2R8MassTerm : Ball := .exact 0
def CB3_3_2I2R8H : Ball := ⟨0, 0⟩
def CB3_3_2I2R9Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 3 2)) (fun u => (stageBLaw (shape 3 3 2) u : ℝ)) (stageBPriority (shape 3 3 2)) 2 (fun u a => (littleLaw (shape 3 3 2) u ((stageBPriority (shape 3 3 2)) 2) a : ℝ)) 9 a
def CB3_3_2I2R9Entropy : Ball := ⟨0, 0⟩
def CB3_3_2I2R9Mass : Ball := ⟨0, 0⟩
def CB3_3_2I2R9MassTerm : Ball := .exact 0
def CB3_3_2I2R9H : Ball := ⟨0, 0⟩
def CB3_3_2I2R10Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 3 2)) (fun u => (stageBLaw (shape 3 3 2) u : ℝ)) (stageBPriority (shape 3 3 2)) 2 (fun u a => (littleLaw (shape 3 3 2) u ((stageBPriority (shape 3 3 2)) 2) a : ℝ)) 10 a
def CB3_3_2I2R10Entropy : Ball := ⟨0, 0⟩
def CB3_3_2I2R10Mass : Ball := ⟨0, 0⟩
def CB3_3_2I2R10MassTerm : Ball := .exact 0
def CB3_3_2I2R10H : Ball := ⟨0, 0⟩
def CB3_3_2I2R11Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 3 2)) (fun u => (stageBLaw (shape 3 3 2) u : ℝ)) (stageBPriority (shape 3 3 2)) 2 (fun u a => (littleLaw (shape 3 3 2) u ((stageBPriority (shape 3 3 2)) 2) a : ℝ)) 11 a
def CB3_3_2I2R11Entropy : Ball := ⟨0, 0⟩
def CB3_3_2I2R11Mass : Ball := ⟨0, 0⟩
def CB3_3_2I2R11MassTerm : Ball := .exact 0
def CB3_3_2I2R11H : Ball := ⟨0, 0⟩
def CB3_3_2I2R12Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 3 2)) (fun u => (stageBLaw (shape 3 3 2) u : ℝ)) (stageBPriority (shape 3 3 2)) 2 (fun u a => (littleLaw (shape 3 3 2) u ((stageBPriority (shape 3 3 2)) 2) a : ℝ)) 12 a
def CB3_3_2I2R12Entropy : Ball := ⟨0, 0⟩
def CB3_3_2I2R12Mass : Ball := ⟨0, 0⟩
def CB3_3_2I2R12MassTerm : Ball := .exact 0
def CB3_3_2I2R12H : Ball := ⟨0, 0⟩
def CB3_3_2I2R13Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 3 2)) (fun u => (stageBLaw (shape 3 3 2) u : ℝ)) (stageBPriority (shape 3 3 2)) 2 (fun u a => (littleLaw (shape 3 3 2) u ((stageBPriority (shape 3 3 2)) 2) a : ℝ)) 13 a
def CB3_3_2I2R13Entropy : Ball := ⟨0, 0⟩
def CB3_3_2I2R13Mass : Ball := ⟨0, 0⟩
def CB3_3_2I2R13MassTerm : Ball := .exact 0
def CB3_3_2I2R13H : Ball := ⟨0, 0⟩
def CB3_3_2I2R14Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 3 2)) (fun u => (stageBLaw (shape 3 3 2) u : ℝ)) (stageBPriority (shape 3 3 2)) 2 (fun u a => (littleLaw (shape 3 3 2) u ((stageBPriority (shape 3 3 2)) 2) a : ℝ)) 14 a
def CB3_3_2I2R14Entropy : Ball := ⟨0, 0⟩
def CB3_3_2I2R14Mass : Ball := ⟨0, 0⟩
def CB3_3_2I2R14MassTerm : Ball := .exact 0
def CB3_3_2I2R14H : Ball := ⟨0, 0⟩
def CB3_3_2I2R15Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 3 2)) (fun u => (stageBLaw (shape 3 3 2) u : ℝ)) (stageBPriority (shape 3 3 2)) 2 (fun u a => (littleLaw (shape 3 3 2) u ((stageBPriority (shape 3 3 2)) 2) a : ℝ)) 15 a
def CB3_3_2I2R15Entropy : Ball := ⟨0, 0⟩
def CB3_3_2I2R15Mass : Ball := ⟨0, 0⟩
def CB3_3_2I2R15MassTerm : Ball := .exact 0
def CB3_3_2I2R15H : Ball := ⟨0, 0⟩
def CB3_3_2I2R16Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 3 2)) (fun u => (stageBLaw (shape 3 3 2) u : ℝ)) (stageBPriority (shape 3 3 2)) 2 (fun u a => (littleLaw (shape 3 3 2) u ((stageBPriority (shape 3 3 2)) 2) a : ℝ)) 16 a
def CB3_3_2I2R16Entropy : Ball := ⟨0, 0⟩
def CB3_3_2I2R16Mass : Ball := ⟨0, 0⟩
def CB3_3_2I2R16MassTerm : Ball := .exact 0
def CB3_3_2I2R16H : Ball := ⟨0, 0⟩
def CB3_3_2I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CB3_3_2I2R0H
  | 1 => CB3_3_2I2R1H
  | 2 => CB3_3_2I2R2H
  | 3 => CB3_3_2I2R3H
  | 4 => CB3_3_2I2R4H
  | 5 => CB3_3_2I2R5H
  | 6 => CB3_3_2I2R6H
  | 7 => CB3_3_2I2R7H
  | 8 => CB3_3_2I2R8H
  | 9 => CB3_3_2I2R9H
  | 10 => CB3_3_2I2R10H
  | 11 => CB3_3_2I2R11H
  | 12 => CB3_3_2I2R12H
  | 13 => CB3_3_2I2R13H
  | 14 => CB3_3_2I2R14H
  | 15 => CB3_3_2I2R15H
  | 16 => CB3_3_2I2R16H
  | _ => (.exact 0)
def CB3_3_2I2S0_2_2Value (a : Fin 6) : ℝ := (littleLaw (shape 3 3 2) (shape 0 2 2) ((stageBPriority (shape 3 3 2)) 2) a : ℝ)
def CB3_3_2I2S0_2_2E_2LogWitness : LogWitness := ⟨-1, 447843, 250000⟩
def CB3_3_2I2S0_2_2E_2Log : Ball := ⟨(-1101653738564778545821473882577 / 10000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def CB3_3_2I2S0_2_2E_2 : Ball := ⟨(9867358304801322365926526559899 / 100000000000000000000000000000000), (4741722203 / 12500000000000000000000000000000)⟩
def CB3_3_2I2S0_2_2E_3LogWitness : LogWitness := ⟨-4, 52157, 31250⟩
def CB3_3_2I2S0_2_2E_3Log : Ball := ⟨(-226034969779528798511424963779123 / 100000000000000000000000000000000), (52939559207 / 50000000000000000000000000000000)⟩
def CB3_3_2I2S0_2_2E_3 : Ball := ⟨(4715722367516353417584156734331 / 20000000000000000000000000000000), (11044674359 / 100000000000000000000000000000000)⟩
def CB3_3_2I2S0_2_2Terms (a : Fin 6) : Ball :=
  match a.val with
  | 2 => ⟨(9867358304801322365926526559899 / 100000000000000000000000000000000), (4741722203 / 12500000000000000000000000000000)⟩
  | 3 => ⟨(4715722367516353417584156734331 / 20000000000000000000000000000000), (11044674359 / 100000000000000000000000000000000)⟩
  | _ => (.exact 0)
def CB3_3_2I2S0_2_2Entropy : Ball := ⟨(16722985071191544726923655115777 / 50000000000000000000000000000000), (48978451983 / 100000000000000000000000000000000)⟩
def CB3_3_2I2S0_2_2Mass : Ball := ⟨1, 0⟩
def CB3_3_2I2S0_2_2MassTermLog : Ball := .exact 0
def CB3_3_2I2S0_2_2MassTerm : Ball := ⟨0, 0⟩
def CB3_3_2I2S0_2_2H : Ball := ⟨(16722985071191544726923655115777 / 50000000000000000000000000000000), (48978451983 / 100000000000000000000000000000000)⟩
def CB3_3_2I2S0_3_1Value (a : Fin 6) : ℝ := (littleLaw (shape 3 3 2) (shape 0 3 1) ((stageBPriority (shape 3 3 2)) 2) a : ℝ)
def CB3_3_2I2S0_3_1E_4Log : Ball := .exact 0
def CB3_3_2I2S0_3_1E_4 : Ball := ⟨0, 0⟩
def CB3_3_2I2S0_3_1Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB3_3_2I2S0_3_1Entropy : Ball := ⟨0, 0⟩
def CB3_3_2I2S0_3_1Mass : Ball := ⟨1, 0⟩
def CB3_3_2I2S0_3_1MassTermLog : Ball := .exact 0
def CB3_3_2I2S0_3_1MassTerm : Ball := ⟨0, 0⟩
def CB3_3_2I2S0_3_1H : Ball := ⟨0, 0⟩
def CB3_3_2I2S1_3_0Value (a : Fin 6) : ℝ := (littleLaw (shape 3 3 2) (shape 1 3 0) ((stageBPriority (shape 3 3 2)) 2) a : ℝ)
def CB3_3_2I2S1_3_0E_4Log : Ball := .exact 0
def CB3_3_2I2S1_3_0E_4 : Ball := ⟨0, 0⟩
def CB3_3_2I2S1_3_0Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB3_3_2I2S1_3_0Entropy : Ball := ⟨0, 0⟩
def CB3_3_2I2S1_3_0Mass : Ball := ⟨1, 0⟩
def CB3_3_2I2S1_3_0MassTermLog : Ball := .exact 0
def CB3_3_2I2S1_3_0MassTerm : Ball := ⟨0, 0⟩
def CB3_3_2I2S1_3_0H : Ball := ⟨0, 0⟩
def CB3_3_2I2S2_2_0Value (a : Fin 6) : ℝ := (littleLaw (shape 3 3 2) (shape 2 2 0) ((stageBPriority (shape 3 3 2)) 2) a : ℝ)
def CB3_3_2I2S2_2_0E_2LogWitness : LogWitness := ⟨-1, 222483, 125000⟩
def CB3_3_2I2S2_2_0E_2Log : Ball := ⟨(-5830511183465280787305887930417 / 50000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
def CB3_3_2I2S2_2_0E_2 : Ball := ⟨(1297189619630906065402175864423 / 12500000000000000000000000000000), (9422521561 / 25000000000000000000000000000000)⟩
def CB3_3_2I2S2_2_0E_3LogWitness : LogWitness := ⟨-4, 27517, 15625⟩
def CB3_3_2I2S2_2_0E_3Log : Ball := ⟨(-220665692236720985729493316733689 / 100000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
def CB3_3_2I2S2_2_0E_3 : Ball := ⟨(6072057853277851364318467596561 / 25000000000000000000000000000000), (11653902807 / 100000000000000000000000000000000)⟩
def CB3_3_2I2S2_2_0Terms (a : Fin 6) : Ball :=
  match a.val with
  | 2 => ⟨(1297189619630906065402175864423 / 12500000000000000000000000000000), (9422521561 / 25000000000000000000000000000000)⟩
  | 3 => ⟨(6072057853277851364318467596561 / 25000000000000000000000000000000), (11653902807 / 100000000000000000000000000000000)⟩
  | _ => (.exact 0)
def CB3_3_2I2S2_2_0Entropy : Ball := ⟨(8666437092539663495122819325407 / 25000000000000000000000000000000), (49343989051 / 100000000000000000000000000000000)⟩
def CB3_3_2I2S2_2_0Mass : Ball := ⟨1, 0⟩
def CB3_3_2I2S2_2_0MassTermLog : Ball := .exact 0
def CB3_3_2I2S2_2_0MassTerm : Ball := ⟨0, 0⟩
def CB3_3_2I2S2_2_0H : Ball := ⟨(8666437092539663495122819325407 / 25000000000000000000000000000000), (49343989051 / 100000000000000000000000000000000)⟩
def CB3_3_2I2S3_1_0Value (a : Fin 6) : ℝ := (littleLaw (shape 3 3 2) (shape 3 1 0) ((stageBPriority (shape 3 3 2)) 2) a : ℝ)
def CB3_3_2I2S3_1_0E_1Log : Ball := .exact 0
def CB3_3_2I2S3_1_0E_1 : Ball := ⟨0, 0⟩
def CB3_3_2I2S3_1_0Terms (a : Fin 6) : Ball :=
  match a.val with
  | 1 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB3_3_2I2S3_1_0Entropy : Ball := ⟨0, 0⟩
def CB3_3_2I2S3_1_0Mass : Ball := ⟨1, 0⟩
def CB3_3_2I2S3_1_0MassTermLog : Ball := .exact 0
def CB3_3_2I2S3_1_0MassTerm : Ball := ⟨0, 0⟩
def CB3_3_2I2S3_1_0H : Ball := ⟨0, 0⟩
def CB3_3_2I2Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => CB3_3_2I2S0_2_2H
  | 0, 3, 1 => CB3_3_2I2S0_3_1H
  | 1, 3, 0 => CB3_3_2I2S1_3_0H
  | 2, 2, 0 => CB3_3_2I2S2_2_0H
  | 3, 1, 0 => CB3_3_2I2S3_1_0H
  | _, _, _ => (.exact 0)
def CB3_3_2I2Singleton : Ball := ⟨(1198766343829539023294750780397 / 20000000000000000000000000000000), (4273832203 / 50000000000000000000000000000000)⟩
def CB3_3_2I2Group : Ball := ⟨(6960039161707916052594951406449 / 100000000000000000000000000000000), (4539379237 / 4000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB3_3_2I2H : Ball := ⟨(21154097213388526672622109904423 / 25000000000000000000000000000000), (317946587787 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB3_4_1I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB3_4_1I0Value (a : Fin 17) : ℝ := marginal (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) ((stageBPriority (shape 3 4 1)) 0) a
def CB3_4_1I0Entropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (21175823729 / 50000000000000000000000000000000)⟩
def CB3_4_1I0Mass : Ball := ⟨1, (27 / 50000000000000000000000000000000)⟩
def CB3_4_1I0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB3_4_1I0MassTermLog : Ball := ⟨0, (2646977967 / 12500000000000000000000000000000)⟩
def CB3_4_1I0MassTerm : Ball := ⟨0, (21175823737 / 100000000000000000000000000000000)⟩
def CB3_4_1I0H : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (12705494239 / 20000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB3_4_1I1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB3_4_1I1PairEntropy : Ball := ⟨(55366266708463495221775925325553 / 50000000000000000000000000000000), (35912897829 / 50000000000000000000000000000000)⟩
def CB3_4_1I1PairMass : Ball := ⟨1, (7 / 12500000000000000000000000000000)⟩
def CB3_4_1I1PairMassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB3_4_1I1PairMassTermLog : Ball := ⟨0, (10587911869 / 50000000000000000000000000000000)⟩
def CB3_4_1I1PairMassTerm : Ball := ⟨0, (21175823739 / 100000000000000000000000000000000)⟩
def CB3_4_1I1PairH : Ball := ⟨(55366266708463495221775925325553 / 50000000000000000000000000000000), (93001619397 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB3_4_1I1R0Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) 0 a
def CB3_4_1I1R0Entropy : Ball := ⟨(1147279995329005976604244689539 / 20000000000000000000000000000000), (2248420661 / 100000000000000000000000000000000)⟩
def CB3_4_1I1R0Mass : Ball := ⟨(82952079780722940626225466023 / 6250000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def CB3_4_1I1R0MassTermLogWitness : LogWitness := ⟨-7, 82952079780722940626225466023, 48828125000000000000000000000⟩
def CB3_4_1I1R0MassTermLog : Ball := ⟨(-17288294614820796241404340152637 / 4000000000000000000000000000000), (42351647479 / 25000000000000000000000000000000)⟩
def CB3_4_1I1R0MassTerm : Ball := ⟨(1147279995329005976604244689539 / 20000000000000000000000000000000), (2248420661 / 100000000000000000000000000000000)⟩
def CB3_4_1I1R0H : Ball := ⟨0, (2248420661 / 50000000000000000000000000000000)⟩
def CB3_4_1I1R1Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) 1 a
def CB3_4_1I1R1Entropy : Ball := ⟨(35046850851307688181754010183329 / 100000000000000000000000000000000), (15460288913 / 50000000000000000000000000000000)⟩
def CB3_4_1I1R1Mass : Ball := ⟨(3042047920219277059373774533977 / 6250000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
def CB3_4_1I1R1MassTermLogWitness : LogWitness := ⟨-2, 3042047920219277059373774533977, 1562500000000000000000000000000⟩
def CB3_4_1I1R1MassTermLog : Ball := ⟨(-9000631464612332402682222967793 / 12500000000000000000000000000000), (15881867773 / 25000000000000000000000000000000)⟩
def CB3_4_1I1R1MassTerm : Ball := ⟨(35046850851307688181754010183329 / 100000000000000000000000000000000), (15460288913 / 50000000000000000000000000000000)⟩
def CB3_4_1I1R1H : Ball := ⟨0, (15460288913 / 25000000000000000000000000000000)⟩
def CB3_4_1I1R2Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) 2 a
def CB3_4_1I1R2Entropy : Ball := ⟨(24814933365909232669377350938929 / 50000000000000000000000000000000), (2104029823 / 6250000000000000000000000000000)⟩
def CB3_4_1I1R2Mass : Ball := ⟨(3042047920219277059373774533977 / 6250000000000000000000000000000), (11 / 50000000000000000000000000000000)⟩
def CB3_4_1I1R2MassTermLogWitness : LogWitness := ⟨-2, 3042047920219277059373774533977, 1562500000000000000000000000000⟩
def CB3_4_1I1R2MassTermLog : Ball := ⟨(-9000631464612332402682222967793 / 12500000000000000000000000000000), (31763735547 / 50000000000000000000000000000000)⟩
def CB3_4_1I1R2MassTerm : Ball := ⟨(35046850851307688181754010183329 / 100000000000000000000000000000000), (30920577827 / 100000000000000000000000000000000)⟩
def CB3_4_1I1R2H : Ball := ⟨(14583015880510777157000691694529 / 100000000000000000000000000000000), (12917010999 / 20000000000000000000000000000000)⟩
def CB3_4_1I1R3Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) 3 a
def CB3_4_1I1R3Entropy : Ball := ⟨(5625246599010449899116012778669 / 100000000000000000000000000000000), (2191954091 / 100000000000000000000000000000000)⟩
def CB3_4_1I1R3Mass : Ball := ⟨(80868831238226048857523902691 / 6250000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
def CB3_4_1I1R3MassTermLogWitness : LogWitness := ⟨-7, 80868831238226048857523902691, 48828125000000000000000000000⟩
def CB3_4_1I1R3MassTermLog : Ball := ⟨(-434750826807998994834781262470351 / 100000000000000000000000000000000), (3388131797 / 2000000000000000000000000000000)⟩
def CB3_4_1I1R3MassTerm : Ball := ⟨(5625246599010449899116012778669 / 100000000000000000000000000000000), (2191954091 / 100000000000000000000000000000000)⟩
def CB3_4_1I1R3H : Ball := ⟨0, (2191954091 / 50000000000000000000000000000000)⟩
def CB3_4_1I1R4Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) 4 a
def CB3_4_1I1R4Entropy : Ball := ⟨0, 0⟩
def CB3_4_1I1R4Mass : Ball := ⟨0, 0⟩
def CB3_4_1I1R4MassTerm : Ball := .exact 0
def CB3_4_1I1R4H : Ball := ⟨0, 0⟩
def CB3_4_1I1R5Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) 5 a
def CB3_4_1I1R5Entropy : Ball := ⟨0, 0⟩
def CB3_4_1I1R5Mass : Ball := ⟨0, 0⟩
def CB3_4_1I1R5MassTerm : Ball := .exact 0
def CB3_4_1I1R5H : Ball := ⟨0, 0⟩
def CB3_4_1I1R6Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) 6 a
def CB3_4_1I1R6Entropy : Ball := ⟨0, 0⟩
def CB3_4_1I1R6Mass : Ball := ⟨0, 0⟩
def CB3_4_1I1R6MassTerm : Ball := .exact 0
def CB3_4_1I1R6H : Ball := ⟨0, 0⟩
def CB3_4_1I1R7Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) 7 a
def CB3_4_1I1R7Entropy : Ball := ⟨0, 0⟩
def CB3_4_1I1R7Mass : Ball := ⟨0, 0⟩
def CB3_4_1I1R7MassTerm : Ball := .exact 0
def CB3_4_1I1R7H : Ball := ⟨0, 0⟩
def CB3_4_1I1R8Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) 8 a
def CB3_4_1I1R8Entropy : Ball := ⟨0, 0⟩
def CB3_4_1I1R8Mass : Ball := ⟨0, 0⟩
def CB3_4_1I1R8MassTerm : Ball := .exact 0
def CB3_4_1I1R8H : Ball := ⟨0, 0⟩
def CB3_4_1I1R9Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) 9 a
def CB3_4_1I1R9Entropy : Ball := ⟨0, 0⟩
def CB3_4_1I1R9Mass : Ball := ⟨0, 0⟩
def CB3_4_1I1R9MassTerm : Ball := .exact 0
def CB3_4_1I1R9H : Ball := ⟨0, 0⟩
def CB3_4_1I1R10Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) 10 a
def CB3_4_1I1R10Entropy : Ball := ⟨0, 0⟩
def CB3_4_1I1R10Mass : Ball := ⟨0, 0⟩
def CB3_4_1I1R10MassTerm : Ball := .exact 0
def CB3_4_1I1R10H : Ball := ⟨0, 0⟩
def CB3_4_1I1R11Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) 11 a
def CB3_4_1I1R11Entropy : Ball := ⟨0, 0⟩
def CB3_4_1I1R11Mass : Ball := ⟨0, 0⟩
def CB3_4_1I1R11MassTerm : Ball := .exact 0
def CB3_4_1I1R11H : Ball := ⟨0, 0⟩
def CB3_4_1I1R12Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) 12 a
def CB3_4_1I1R12Entropy : Ball := ⟨0, 0⟩
def CB3_4_1I1R12Mass : Ball := ⟨0, 0⟩
def CB3_4_1I1R12MassTerm : Ball := .exact 0
def CB3_4_1I1R12H : Ball := ⟨0, 0⟩
def CB3_4_1I1R13Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) 13 a
def CB3_4_1I1R13Entropy : Ball := ⟨0, 0⟩
def CB3_4_1I1R13Mass : Ball := ⟨0, 0⟩
def CB3_4_1I1R13MassTerm : Ball := .exact 0
def CB3_4_1I1R13H : Ball := ⟨0, 0⟩
def CB3_4_1I1R14Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) 14 a
def CB3_4_1I1R14Entropy : Ball := ⟨0, 0⟩
def CB3_4_1I1R14Mass : Ball := ⟨0, 0⟩
def CB3_4_1I1R14MassTerm : Ball := .exact 0
def CB3_4_1I1R14H : Ball := ⟨0, 0⟩
def CB3_4_1I1R15Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) 15 a
def CB3_4_1I1R15Entropy : Ball := ⟨0, 0⟩
def CB3_4_1I1R15Mass : Ball := ⟨0, 0⟩
def CB3_4_1I1R15MassTerm : Ball := .exact 0
def CB3_4_1I1R15H : Ball := ⟨0, 0⟩
def CB3_4_1I1R16Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) 16 a
def CB3_4_1I1R16Entropy : Ball := ⟨0, 0⟩
def CB3_4_1I1R16Mass : Ball := ⟨0, 0⟩
def CB3_4_1I1R16MassTerm : Ball := .exact 0
def CB3_4_1I1R16H : Ball := ⟨0, 0⟩
def CB3_4_1I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CB3_4_1I1R0H
  | 1 => CB3_4_1I1R1H
  | 2 => CB3_4_1I1R2H
  | 3 => CB3_4_1I1R3H
  | 4 => CB3_4_1I1R4H
  | 5 => CB3_4_1I1R5H
  | 6 => CB3_4_1I1R6H
  | 7 => CB3_4_1I1R7H
  | 8 => CB3_4_1I1R8H
  | 9 => CB3_4_1I1R9H
  | 10 => CB3_4_1I1R10H
  | 11 => CB3_4_1I1R11H
  | 12 => CB3_4_1I1R12H
  | 13 => CB3_4_1I1R13H
  | 14 => CB3_4_1I1R14H
  | 15 => CB3_4_1I1R15H
  | 16 => CB3_4_1I1R16H
  | _ => (.exact 0)
def CB3_4_1I1S3_0_1Value (a : Fin 6) : ℝ := (littleLaw (shape 3 4 1) (shape 3 0 1) ((stageBPriority (shape 3 4 1)) 1) a : ℝ)
def CB3_4_1I1S3_0_1E_4Log : Ball := .exact 0
def CB3_4_1I1S3_0_1E_4 : Ball := ⟨0, 0⟩
def CB3_4_1I1S3_0_1Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB3_4_1I1S3_0_1Entropy : Ball := ⟨0, 0⟩
def CB3_4_1I1S3_0_1Mass : Ball := ⟨1, 0⟩
def CB3_4_1I1S3_0_1MassTermLog : Ball := .exact 0
def CB3_4_1I1S3_0_1MassTerm : Ball := ⟨0, 0⟩
def CB3_4_1I1S3_0_1H : Ball := ⟨0, 0⟩
def CB3_4_1I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 3, 0, 1 => CB3_4_1I1S3_0_1H
  | _, _, _ => (.exact 0)
def CB3_4_1I1Singleton : Ball := ⟨0, 0⟩
def CB3_4_1I1Group : Ball := ⟨(14583015880510777157000691694529 / 100000000000000000000000000000000), (135306960151 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB3_4_1I1H : Ball := ⟨(2548953176747044879048452101939 / 3125000000000000000000000000000), (363615539699 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB3_4_1I2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB3_4_1I2PairEntropy : Ball := ⟨(44005784904449970927177466795641 / 50000000000000000000000000000000), (7446192891 / 12500000000000000000000000000000)⟩
def CB3_4_1I2PairMass : Ball := ⟨(100000000000000000000000000000001 / 100000000000000000000000000000000), (57 / 100000000000000000000000000000000)⟩
def CB3_4_1I2PairMassTermLogWitness : LogWitness := ⟨0, 100000000000000000000000000000001, 100000000000000000000000000000000⟩
def CB3_4_1I2PairMassTermLog : Ball := ⟨(1 / 100000000000000000000000000000000), (21175823739 / 100000000000000000000000000000000)⟩
def CB3_4_1I2PairMassTerm : Ball := ⟨(-1 / 100000000000000000000000000000000), (1058791187 / 5000000000000000000000000000000)⟩
def CB3_4_1I2PairH : Ball := ⟨(88011569808899941854354933591283 / 100000000000000000000000000000000), (20186341717 / 25000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB3_4_1I2R0Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 2 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 2) a : ℝ)) 0 a
def CB3_4_1I2R0Entropy : Ball := ⟨(16679338355112702564543320603 / 6250000000000000000000000000000), (91758177 / 100000000000000000000000000000000)⟩
def CB3_4_1I2R0Mass : Ball := ⟨(520812135624222942175390833 / 1562500000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def CB3_4_1I2R0MassTermLogWitness : LogWitness := ⟨-12, 520812135624222942175390833, 381469726562500000000000000⟩
def CB3_4_1I2R0MassTermLog : Ball := ⟨(-400320413403999497417390583495699 / 50000000000000000000000000000000), (137642855439 / 50000000000000000000000000000000)⟩
def CB3_4_1I2R0MassTerm : Ball := ⟨(16679338355112702564543320603 / 6250000000000000000000000000000), (91758177 / 100000000000000000000000000000000)⟩
def CB3_4_1I2R0H : Ball := ⟨0, (91758177 / 50000000000000000000000000000000)⟩
def CB3_4_1I2R1Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 2 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 2) a : ℝ)) 1 a
def CB3_4_1I2R1Entropy : Ball := ⟨(8938540382577431431906908594729 / 50000000000000000000000000000000), (1389927901 / 20000000000000000000000000000000)⟩
def CB3_4_1I2R1Mass : Ball := ⟨(3281874448442126136287678136153 / 50000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
def CB3_4_1I2R1MassTermLogWitness : LogWitness := ⟨-4, 3281874448442126136287678136153, 3125000000000000000000000000000⟩
def CB3_4_1I2R1MassTermLog : Ball := ⟨(-54472165361599798966956263951357 / 20000000000000000000000000000000), (52939559283 / 50000000000000000000000000000000)⟩
def CB3_4_1I2R1MassTerm : Ball := ⟨(8938540382577431431906908594729 / 50000000000000000000000000000000), (1389927901 / 20000000000000000000000000000000)⟩
def CB3_4_1I2R1H : Ball := ⟨0, (1389927901 / 10000000000000000000000000000000)⟩
def CB3_4_1I2R2Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 2 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 2) a : ℝ)) 2 a
def CB3_4_1I2R2Entropy : Ball := ⟨(3726892027084830127379551995689 / 10000000000000000000000000000000), (26961447727 / 100000000000000000000000000000000)⟩
def CB3_4_1I2R2Mass : Ball := ⟨(21054508913312090338702518135663 / 50000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
def CB3_4_1I2R2MassTermLogWitness : LogWitness := ⟨-2, 21054508913312090338702518135663, 12500000000000000000000000000000⟩
def CB3_4_1I2R2MassTermLog : Ball := ⟨(-43245413403999497417390678973909 / 50000000000000000000000000000000), (63527471079 / 100000000000000000000000000000000)⟩
def CB3_4_1I2R2MassTerm : Ball := ⟨(36420437678974942557542286102427 / 100000000000000000000000000000000), (13375397067 / 50000000000000000000000000000000)⟩
def CB3_4_1I2R2H : Ball := ⟨(848482591873358716253233854463 / 100000000000000000000000000000000), (53712241861 / 100000000000000000000000000000000)⟩
def CB3_4_1I2R3Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 2 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 2) a : ℝ)) 3 a
def CB3_4_1I2R3Entropy : Ball := ⟨0, 0⟩
def CB3_4_1I2R3Mass : Ball := ⟨0, 0⟩
def CB3_4_1I2R3MassTerm : Ball := .exact 0
def CB3_4_1I2R3H : Ball := ⟨0, 0⟩
def CB3_4_1I2R4Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 2 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 2) a : ℝ)) 4 a
def CB3_4_1I2R4Entropy : Ball := ⟨0, 0⟩
def CB3_4_1I2R4Mass : Ball := ⟨0, 0⟩
def CB3_4_1I2R4MassTerm : Ball := .exact 0
def CB3_4_1I2R4H : Ball := ⟨0, 0⟩
def CB3_4_1I2R5Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 2 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 2) a : ℝ)) 5 a
def CB3_4_1I2R5Entropy : Ball := ⟨0, 0⟩
def CB3_4_1I2R5Mass : Ball := ⟨0, 0⟩
def CB3_4_1I2R5MassTerm : Ball := .exact 0
def CB3_4_1I2R5H : Ball := ⟨0, 0⟩
def CB3_4_1I2R6Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 2 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 2) a : ℝ)) 6 a
def CB3_4_1I2R6Entropy : Ball := ⟨0, 0⟩
def CB3_4_1I2R6Mass : Ball := ⟨0, 0⟩
def CB3_4_1I2R6MassTerm : Ball := .exact 0
def CB3_4_1I2R6H : Ball := ⟨0, 0⟩
def CB3_4_1I2R7Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 2 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 2) a : ℝ)) 7 a
def CB3_4_1I2R7Entropy : Ball := ⟨0, 0⟩
def CB3_4_1I2R7Mass : Ball := ⟨0, 0⟩
def CB3_4_1I2R7MassTerm : Ball := .exact 0
def CB3_4_1I2R7H : Ball := ⟨0, 0⟩
def CB3_4_1I2R8Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 2 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 2) a : ℝ)) 8 a
def CB3_4_1I2R8Entropy : Ball := ⟨0, 0⟩
def CB3_4_1I2R8Mass : Ball := ⟨0, 0⟩
def CB3_4_1I2R8MassTerm : Ball := .exact 0
def CB3_4_1I2R8H : Ball := ⟨0, 0⟩
def CB3_4_1I2R9Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 2 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 2) a : ℝ)) 9 a
def CB3_4_1I2R9Entropy : Ball := ⟨0, 0⟩
def CB3_4_1I2R9Mass : Ball := ⟨0, 0⟩
def CB3_4_1I2R9MassTerm : Ball := .exact 0
def CB3_4_1I2R9H : Ball := ⟨0, 0⟩
def CB3_4_1I2R10Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 2 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 2) a : ℝ)) 10 a
def CB3_4_1I2R10Entropy : Ball := ⟨0, 0⟩
def CB3_4_1I2R10Mass : Ball := ⟨0, 0⟩
def CB3_4_1I2R10MassTerm : Ball := .exact 0
def CB3_4_1I2R10H : Ball := ⟨0, 0⟩
def CB3_4_1I2R11Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 2 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 2) a : ℝ)) 11 a
def CB3_4_1I2R11Entropy : Ball := ⟨0, 0⟩
def CB3_4_1I2R11Mass : Ball := ⟨0, 0⟩
def CB3_4_1I2R11MassTerm : Ball := .exact 0
def CB3_4_1I2R11H : Ball := ⟨0, 0⟩
def CB3_4_1I2R12Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 2 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 2) a : ℝ)) 12 a
def CB3_4_1I2R12Entropy : Ball := ⟨0, 0⟩
def CB3_4_1I2R12Mass : Ball := ⟨0, 0⟩
def CB3_4_1I2R12MassTerm : Ball := .exact 0
def CB3_4_1I2R12H : Ball := ⟨0, 0⟩
def CB3_4_1I2R13Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 2 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 2) a : ℝ)) 13 a
def CB3_4_1I2R13Entropy : Ball := ⟨0, 0⟩
def CB3_4_1I2R13Mass : Ball := ⟨0, 0⟩
def CB3_4_1I2R13MassTerm : Ball := .exact 0
def CB3_4_1I2R13H : Ball := ⟨0, 0⟩
def CB3_4_1I2R14Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 2 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 2) a : ℝ)) 14 a
def CB3_4_1I2R14Entropy : Ball := ⟨0, 0⟩
def CB3_4_1I2R14Mass : Ball := ⟨0, 0⟩
def CB3_4_1I2R14MassTerm : Ball := .exact 0
def CB3_4_1I2R14H : Ball := ⟨0, 0⟩
def CB3_4_1I2R15Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 2 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 2) a : ℝ)) 15 a
def CB3_4_1I2R15Entropy : Ball := ⟨0, 0⟩
def CB3_4_1I2R15Mass : Ball := ⟨0, 0⟩
def CB3_4_1I2R15MassTerm : Ball := .exact 0
def CB3_4_1I2R15H : Ball := ⟨0, 0⟩
def CB3_4_1I2R16Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 2 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 2) a : ℝ)) 16 a
def CB3_4_1I2R16Entropy : Ball := ⟨0, 0⟩
def CB3_4_1I2R16Mass : Ball := ⟨0, 0⟩
def CB3_4_1I2R16MassTerm : Ball := .exact 0
def CB3_4_1I2R16H : Ball := ⟨0, 0⟩
def CB3_4_1I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CB3_4_1I2R0H
  | 1 => CB3_4_1I2R1H
  | 2 => CB3_4_1I2R2H
  | 3 => CB3_4_1I2R3H
  | 4 => CB3_4_1I2R4H
  | 5 => CB3_4_1I2R5H
  | 6 => CB3_4_1I2R6H
  | 7 => CB3_4_1I2R7H
  | 8 => CB3_4_1I2R8H
  | 9 => CB3_4_1I2R9H
  | 10 => CB3_4_1I2R10H
  | 11 => CB3_4_1I2R11H
  | 12 => CB3_4_1I2R12H
  | 13 => CB3_4_1I2R13H
  | 14 => CB3_4_1I2R14H
  | 15 => CB3_4_1I2R15H
  | 16 => CB3_4_1I2R16H
  | _ => (.exact 0)
def CB3_4_1I2S0_3_1Value (a : Fin 6) : ℝ := (littleLaw (shape 3 4 1) (shape 0 3 1) ((stageBPriority (shape 3 4 1)) 2) a : ℝ)
def CB3_4_1I2S0_3_1E_4Log : Ball := .exact 0
def CB3_4_1I2S0_3_1E_4 : Ball := ⟨0, 0⟩
def CB3_4_1I2S0_3_1Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB3_4_1I2S0_3_1Entropy : Ball := ⟨0, 0⟩
def CB3_4_1I2S0_3_1Mass : Ball := ⟨1, 0⟩
def CB3_4_1I2S0_3_1MassTermLog : Ball := .exact 0
def CB3_4_1I2S0_3_1MassTerm : Ball := ⟨0, 0⟩
def CB3_4_1I2S0_3_1H : Ball := ⟨0, 0⟩
def CB3_4_1I2S0_4_0Value (a : Fin 6) : ℝ := (littleLaw (shape 3 4 1) (shape 0 4 0) ((stageBPriority (shape 3 4 1)) 2) a : ℝ)
def CB3_4_1I2S0_4_0E_5Log : Ball := .exact 0
def CB3_4_1I2S0_4_0E_5 : Ball := ⟨0, 0⟩
def CB3_4_1I2S0_4_0Terms (a : Fin 6) : Ball :=
  match a.val with
  | 5 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB3_4_1I2S0_4_0Entropy : Ball := ⟨0, 0⟩
def CB3_4_1I2S0_4_0Mass : Ball := ⟨1, 0⟩
def CB3_4_1I2S0_4_0MassTermLog : Ball := .exact 0
def CB3_4_1I2S0_4_0MassTerm : Ball := ⟨0, 0⟩
def CB3_4_1I2S0_4_0H : Ball := ⟨0, 0⟩
def CB3_4_1I2S1_3_0Value (a : Fin 6) : ℝ := (littleLaw (shape 3 4 1) (shape 1 3 0) ((stageBPriority (shape 3 4 1)) 2) a : ℝ)
def CB3_4_1I2S1_3_0E_4Log : Ball := .exact 0
def CB3_4_1I2S1_3_0E_4 : Ball := ⟨0, 0⟩
def CB3_4_1I2S1_3_0Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB3_4_1I2S1_3_0Entropy : Ball := ⟨0, 0⟩
def CB3_4_1I2S1_3_0Mass : Ball := ⟨1, 0⟩
def CB3_4_1I2S1_3_0MassTermLog : Ball := .exact 0
def CB3_4_1I2S1_3_0MassTerm : Ball := ⟨0, 0⟩
def CB3_4_1I2S1_3_0H : Ball := ⟨0, 0⟩
def CB3_4_1I2S2_2_0Value (a : Fin 6) : ℝ := (littleLaw (shape 3 4 1) (shape 2 2 0) ((stageBPriority (shape 3 4 1)) 2) a : ℝ)
def CB3_4_1I2S2_2_0E_2LogWitness : LogWitness := ⟨-1, 226, 125⟩
def CB3_4_1I2S2_2_0E_2Log : Ball := ⟨(-2523147964749013880503657881131 / 25000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
def CB3_4_1I2S2_2_0E_2 : Ball := ⟨(912370304053243419190122689817 / 10000000000000000000000000000000), (38285889219 / 100000000000000000000000000000000)⟩
def CB3_4_1I2S2_2_0E_3LogWitness : LogWitness := ⟨-4, 192, 125⟩
def CB3_4_1I2S2_2_0E_3Log : Ball := ⟨(-117170354375715040678628387801009 / 50000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
def CB3_4_1I2S2_2_0E_3 : Ball := ⟨(11248354020068643905148325228897 / 50000000000000000000000000000000), (10164395369 / 100000000000000000000000000000000)⟩
def CB3_4_1I2S2_2_0Terms (a : Fin 6) : Ball :=
  match a.val with
  | 2 => ⟨(912370304053243419190122689817 / 10000000000000000000000000000000), (38285889219 / 100000000000000000000000000000000)⟩
  | 3 => ⟨(11248354020068643905148325228897 / 50000000000000000000000000000000), (10164395369 / 100000000000000000000000000000000)⟩
  | _ => (.exact 0)
def CB3_4_1I2S2_2_0Entropy : Ball := ⟨(7905102770167430500549469338991 / 25000000000000000000000000000000), (12112571147 / 25000000000000000000000000000000)⟩
def CB3_4_1I2S2_2_0Mass : Ball := ⟨1, 0⟩
def CB3_4_1I2S2_2_0MassTermLog : Ball := .exact 0
def CB3_4_1I2S2_2_0MassTerm : Ball := ⟨0, 0⟩
def CB3_4_1I2S2_2_0H : Ball := ⟨(7905102770167430500549469338991 / 25000000000000000000000000000000), (12112571147 / 25000000000000000000000000000000)⟩
def CB3_4_1I2S3_1_0Value (a : Fin 6) : ℝ := (littleLaw (shape 3 4 1) (shape 3 1 0) ((stageBPriority (shape 3 4 1)) 2) a : ℝ)
def CB3_4_1I2S3_1_0E_1Log : Ball := .exact 0
def CB3_4_1I2S3_1_0E_1 : Ball := ⟨0, 0⟩
def CB3_4_1I2S3_1_0Terms (a : Fin 6) : Ball :=
  match a.val with
  | 1 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB3_4_1I2S3_1_0Entropy : Ball := ⟨0, 0⟩
def CB3_4_1I2S3_1_0Mass : Ball := ⟨1, 0⟩
def CB3_4_1I2S3_1_0MassTermLog : Ball := .exact 0
def CB3_4_1I2S3_1_0MassTerm : Ball := ⟨0, 0⟩
def CB3_4_1I2S3_1_0H : Ball := ⟨0, 0⟩
def CB3_4_1I2Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 3, 1 => CB3_4_1I2S0_3_1H
  | 0, 4, 0 => CB3_4_1I2S0_4_0H
  | 1, 3, 0 => CB3_4_1I2S1_3_0H
  | 2, 2, 0 => CB3_4_1I2S2_2_0H
  | 3, 1, 0 => CB3_4_1I2S3_1_0H
  | _, _, _ => (.exact 0)
def CB3_4_1I2Singleton : Ball := ⟨(13315044538811060974171729708563 / 100000000000000000000000000000000), (10200969489 / 50000000000000000000000000000000)⟩
def CB3_4_1I2Group : Ball := ⟨(7081763565342209845212481781513 / 50000000000000000000000000000000), (88196976203 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB3_4_1I2H : Ball := ⟨(59684515547531102473505006465231 / 100000000000000000000000000000000), (128569659637 / 50000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB4_1_3I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB4_1_3I0Value (a : Fin 17) : ℝ := marginal (below (shape 4 1 3)) (fun u => (stageBLaw (shape 4 1 3) u : ℝ)) ((stageBPriority (shape 4 1 3)) 0) a
def CB4_1_3I0Entropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (21175823727 / 50000000000000000000000000000000)⟩
def CB4_1_3I0Mass : Ball := ⟨1, (13 / 25000000000000000000000000000000)⟩
def CB4_1_3I0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB4_1_3I0MassTermLog : Ball := ⟨0, (10587911867 / 50000000000000000000000000000000)⟩
def CB4_1_3I0MassTerm : Ball := ⟨0, (4235164747 / 20000000000000000000000000000000)⟩
def CB4_1_3I0H : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (63527471189 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB4_1_3I1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB4_1_3I1PairEntropy : Ball := ⟨(55325698911127222661379268710923 / 50000000000000000000000000000000), (8975401589 / 12500000000000000000000000000000)⟩
def CB4_1_3I1PairMass : Ball := ⟨1, (27 / 50000000000000000000000000000000)⟩
def CB4_1_3I1PairMassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB4_1_3I1PairMassTermLog : Ball := ⟨0, (2646977967 / 12500000000000000000000000000000)⟩
def CB4_1_3I1PairMassTerm : Ball := ⟨0, (21175823737 / 100000000000000000000000000000000)⟩
def CB4_1_3I1PairH : Ball := ⟨(55325698911127222661379268710923 / 50000000000000000000000000000000), (92979036449 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB4_1_3I1R0Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 1 3)) (fun u => (stageBLaw (shape 4 1 3) u : ℝ)) (stageBPriority (shape 4 1 3)) 1 (fun u a => (littleLaw (shape 4 1 3) u ((stageBPriority (shape 4 1 3)) 1) a : ℝ)) 0 a
def CB4_1_3I1R0Entropy : Ball := ⟨(5728753851617104939935642134859 / 100000000000000000000000000000000), (561130649 / 25000000000000000000000000000000)⟩
def CB4_1_3I1R0Mass : Ball := ⟨(662466132560089079394730321331 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def CB4_1_3I1R0MassTermLogWitness : LogWitness := ⟨-7, 662466132560089079394730321331, 390625000000000000000000000000⟩
def CB4_1_3I1R0MassTermLog : Ball := ⟨(-13511902651626962495991387351859 / 3125000000000000000000000000000), (169406589917 / 100000000000000000000000000000000)⟩
def CB4_1_3I1R0MassTerm : Ball := ⟨(5728753851617104939935642134859 / 100000000000000000000000000000000), (561130649 / 25000000000000000000000000000000)⟩
def CB4_1_3I1R0H : Ball := ⟨0, (561130649 / 12500000000000000000000000000000)⟩
def CB4_1_3I1R1Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 1 3)) (fun u => (stageBLaw (shape 4 1 3) u : ℝ)) (stageBPriority (shape 4 1 3)) 1 (fun u a => (littleLaw (shape 4 1 3) u ((stageBPriority (shape 4 1 3)) 1) a : ℝ)) 1 a
def CB4_1_3I1R1Entropy : Ball := ⟨(3504620662997483087558516975869 / 10000000000000000000000000000000), (15461019799 / 50000000000000000000000000000000)⟩
def CB4_1_3I1R1Mass : Ball := ⟨(24337533867439910920605269678669 / 50000000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩
def CB4_1_3I1R1MassTermLogWitness : LogWitness := ⟨-2, 24337533867439910920605269678669, 12500000000000000000000000000000⟩
def CB4_1_3I1R1MassTermLog : Ball := ⟨(-18000081078912010444514153845647 / 25000000000000000000000000000000), (6352747109 / 10000000000000000000000000000000)⟩
def CB4_1_3I1R1MassTerm : Ball := ⟨(3504620662997483087558516975869 / 10000000000000000000000000000000), (15461019799 / 50000000000000000000000000000000)⟩
def CB4_1_3I1R1H : Ball := ⟨0, (15461019799 / 25000000000000000000000000000000)⟩
def CB4_1_3I1R2Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 1 3)) (fun u => (stageBLaw (shape 4 1 3) u : ℝ)) (stageBPriority (shape 4 1 3)) 1 (fun u a => (littleLaw (shape 4 1 3) u ((stageBPriority (shape 4 1 3)) 1) a : ℝ)) 2 a
def CB4_1_3I1R2Entropy : Ball := ⟨(774952266554845589397556665251 / 1562500000000000000000000000000), (420713547 / 1250000000000000000000000000000)⟩
def CB4_1_3I1R2Mass : Ball := ⟨(24337533867439910920605269678669 / 50000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
def CB4_1_3I1R2MassTermLogWitness : LogWitness := ⟨-2, 24337533867439910920605269678669, 12500000000000000000000000000000⟩
def CB4_1_3I1R2MassTermLog : Ball := ⟨(-18000081078912010444514153845647 / 25000000000000000000000000000000), (15881867773 / 25000000000000000000000000000000)⟩
def CB4_1_3I1R2MassTerm : Ball := ⟨(3504620662997483087558516975869 / 10000000000000000000000000000000), (77305099 / 250000000000000000000000000000)⟩
def CB4_1_3I1R2H : Ball := ⟨(7275369214767643422929228408687 / 50000000000000000000000000000000), (403619521 / 625000000000000000000000000000)⟩
def CB4_1_3I1R3Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 1 3)) (fun u => (stageBLaw (shape 4 1 3) u : ℝ)) (stageBPriority (shape 4 1 3)) 1 (fun u a => (littleLaw (shape 4 1 3) u ((stageBPriority (shape 4 1 3)) 1) a : ℝ)) 3 a
def CB4_1_3I1R3Entropy : Ball := ⟨(2808579081464389644802916826581 / 50000000000000000000000000000000), (136741371 / 6250000000000000000000000000000)⟩
def CB4_1_3I1R3Mass : Ball := ⟨(2066377148910784129369940729 / 160000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
def CB4_1_3I1R3MassTermLogWitness : LogWitness := ⟨-7, 2066377148910784129369940729, 1250000000000000000000000000⟩
def CB4_1_3I1R3MassTermLog : Ball := ⟨(-108734422772525543341333743967741 / 25000000000000000000000000000000), (169406589851 / 100000000000000000000000000000000)⟩
def CB4_1_3I1R3MassTerm : Ball := ⟨(2808579081464389644802916826581 / 50000000000000000000000000000000), (136741371 / 6250000000000000000000000000000)⟩
def CB4_1_3I1R3H : Ball := ⟨0, (136741371 / 3125000000000000000000000000000)⟩
def CB4_1_3I1R4Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 1 3)) (fun u => (stageBLaw (shape 4 1 3) u : ℝ)) (stageBPriority (shape 4 1 3)) 1 (fun u a => (littleLaw (shape 4 1 3) u ((stageBPriority (shape 4 1 3)) 1) a : ℝ)) 4 a
def CB4_1_3I1R4Entropy : Ball := ⟨0, 0⟩
def CB4_1_3I1R4Mass : Ball := ⟨0, 0⟩
def CB4_1_3I1R4MassTerm : Ball := .exact 0
def CB4_1_3I1R4H : Ball := ⟨0, 0⟩
def CB4_1_3I1R5Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 1 3)) (fun u => (stageBLaw (shape 4 1 3) u : ℝ)) (stageBPriority (shape 4 1 3)) 1 (fun u a => (littleLaw (shape 4 1 3) u ((stageBPriority (shape 4 1 3)) 1) a : ℝ)) 5 a
def CB4_1_3I1R5Entropy : Ball := ⟨0, 0⟩
def CB4_1_3I1R5Mass : Ball := ⟨0, 0⟩
def CB4_1_3I1R5MassTerm : Ball := .exact 0
def CB4_1_3I1R5H : Ball := ⟨0, 0⟩
def CB4_1_3I1R6Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 1 3)) (fun u => (stageBLaw (shape 4 1 3) u : ℝ)) (stageBPriority (shape 4 1 3)) 1 (fun u a => (littleLaw (shape 4 1 3) u ((stageBPriority (shape 4 1 3)) 1) a : ℝ)) 6 a
def CB4_1_3I1R6Entropy : Ball := ⟨0, 0⟩
def CB4_1_3I1R6Mass : Ball := ⟨0, 0⟩
def CB4_1_3I1R6MassTerm : Ball := .exact 0
def CB4_1_3I1R6H : Ball := ⟨0, 0⟩
def CB4_1_3I1R7Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 1 3)) (fun u => (stageBLaw (shape 4 1 3) u : ℝ)) (stageBPriority (shape 4 1 3)) 1 (fun u a => (littleLaw (shape 4 1 3) u ((stageBPriority (shape 4 1 3)) 1) a : ℝ)) 7 a
def CB4_1_3I1R7Entropy : Ball := ⟨0, 0⟩
def CB4_1_3I1R7Mass : Ball := ⟨0, 0⟩
def CB4_1_3I1R7MassTerm : Ball := .exact 0
def CB4_1_3I1R7H : Ball := ⟨0, 0⟩
def CB4_1_3I1R8Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 1 3)) (fun u => (stageBLaw (shape 4 1 3) u : ℝ)) (stageBPriority (shape 4 1 3)) 1 (fun u a => (littleLaw (shape 4 1 3) u ((stageBPriority (shape 4 1 3)) 1) a : ℝ)) 8 a
def CB4_1_3I1R8Entropy : Ball := ⟨0, 0⟩
def CB4_1_3I1R8Mass : Ball := ⟨0, 0⟩
def CB4_1_3I1R8MassTerm : Ball := .exact 0
def CB4_1_3I1R8H : Ball := ⟨0, 0⟩
def CB4_1_3I1R9Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 1 3)) (fun u => (stageBLaw (shape 4 1 3) u : ℝ)) (stageBPriority (shape 4 1 3)) 1 (fun u a => (littleLaw (shape 4 1 3) u ((stageBPriority (shape 4 1 3)) 1) a : ℝ)) 9 a
def CB4_1_3I1R9Entropy : Ball := ⟨0, 0⟩
def CB4_1_3I1R9Mass : Ball := ⟨0, 0⟩
def CB4_1_3I1R9MassTerm : Ball := .exact 0
def CB4_1_3I1R9H : Ball := ⟨0, 0⟩
def CB4_1_3I1R10Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 1 3)) (fun u => (stageBLaw (shape 4 1 3) u : ℝ)) (stageBPriority (shape 4 1 3)) 1 (fun u a => (littleLaw (shape 4 1 3) u ((stageBPriority (shape 4 1 3)) 1) a : ℝ)) 10 a
def CB4_1_3I1R10Entropy : Ball := ⟨0, 0⟩
def CB4_1_3I1R10Mass : Ball := ⟨0, 0⟩
def CB4_1_3I1R10MassTerm : Ball := .exact 0
def CB4_1_3I1R10H : Ball := ⟨0, 0⟩
def CB4_1_3I1R11Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 1 3)) (fun u => (stageBLaw (shape 4 1 3) u : ℝ)) (stageBPriority (shape 4 1 3)) 1 (fun u a => (littleLaw (shape 4 1 3) u ((stageBPriority (shape 4 1 3)) 1) a : ℝ)) 11 a
def CB4_1_3I1R11Entropy : Ball := ⟨0, 0⟩
def CB4_1_3I1R11Mass : Ball := ⟨0, 0⟩
def CB4_1_3I1R11MassTerm : Ball := .exact 0
def CB4_1_3I1R11H : Ball := ⟨0, 0⟩
def CB4_1_3I1R12Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 1 3)) (fun u => (stageBLaw (shape 4 1 3) u : ℝ)) (stageBPriority (shape 4 1 3)) 1 (fun u a => (littleLaw (shape 4 1 3) u ((stageBPriority (shape 4 1 3)) 1) a : ℝ)) 12 a
def CB4_1_3I1R12Entropy : Ball := ⟨0, 0⟩
def CB4_1_3I1R12Mass : Ball := ⟨0, 0⟩
def CB4_1_3I1R12MassTerm : Ball := .exact 0
def CB4_1_3I1R12H : Ball := ⟨0, 0⟩
def CB4_1_3I1R13Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 1 3)) (fun u => (stageBLaw (shape 4 1 3) u : ℝ)) (stageBPriority (shape 4 1 3)) 1 (fun u a => (littleLaw (shape 4 1 3) u ((stageBPriority (shape 4 1 3)) 1) a : ℝ)) 13 a
def CB4_1_3I1R13Entropy : Ball := ⟨0, 0⟩
def CB4_1_3I1R13Mass : Ball := ⟨0, 0⟩
def CB4_1_3I1R13MassTerm : Ball := .exact 0
def CB4_1_3I1R13H : Ball := ⟨0, 0⟩
def CB4_1_3I1R14Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 1 3)) (fun u => (stageBLaw (shape 4 1 3) u : ℝ)) (stageBPriority (shape 4 1 3)) 1 (fun u a => (littleLaw (shape 4 1 3) u ((stageBPriority (shape 4 1 3)) 1) a : ℝ)) 14 a
def CB4_1_3I1R14Entropy : Ball := ⟨0, 0⟩
def CB4_1_3I1R14Mass : Ball := ⟨0, 0⟩
def CB4_1_3I1R14MassTerm : Ball := .exact 0
def CB4_1_3I1R14H : Ball := ⟨0, 0⟩
def CB4_1_3I1R15Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 1 3)) (fun u => (stageBLaw (shape 4 1 3) u : ℝ)) (stageBPriority (shape 4 1 3)) 1 (fun u a => (littleLaw (shape 4 1 3) u ((stageBPriority (shape 4 1 3)) 1) a : ℝ)) 15 a
def CB4_1_3I1R15Entropy : Ball := ⟨0, 0⟩
def CB4_1_3I1R15Mass : Ball := ⟨0, 0⟩
def CB4_1_3I1R15MassTerm : Ball := .exact 0
def CB4_1_3I1R15H : Ball := ⟨0, 0⟩
def CB4_1_3I1R16Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 1 3)) (fun u => (stageBLaw (shape 4 1 3) u : ℝ)) (stageBPriority (shape 4 1 3)) 1 (fun u a => (littleLaw (shape 4 1 3) u ((stageBPriority (shape 4 1 3)) 1) a : ℝ)) 16 a
def CB4_1_3I1R16Entropy : Ball := ⟨0, 0⟩
def CB4_1_3I1R16Mass : Ball := ⟨0, 0⟩
def CB4_1_3I1R16MassTerm : Ball := .exact 0
def CB4_1_3I1R16H : Ball := ⟨0, 0⟩
def CB4_1_3I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CB4_1_3I1R0H
  | 1 => CB4_1_3I1R1H
  | 2 => CB4_1_3I1R2H
  | 3 => CB4_1_3I1R3H
  | 4 => CB4_1_3I1R4H
  | 5 => CB4_1_3I1R5H
  | 6 => CB4_1_3I1R6H
  | 7 => CB4_1_3I1R7H
  | 8 => CB4_1_3I1R8H
  | 9 => CB4_1_3I1R9H
  | 10 => CB4_1_3I1R10H
  | 11 => CB4_1_3I1R11H
  | 12 => CB4_1_3I1R12H
  | 13 => CB4_1_3I1R13H
  | 14 => CB4_1_3I1R14H
  | 15 => CB4_1_3I1R15H
  | 16 => CB4_1_3I1R16H
  | _ => (.exact 0)
def CB4_1_3I1S0_1_3Value (a : Fin 6) : ℝ := (littleLaw (shape 4 1 3) (shape 0 1 3) ((stageBPriority (shape 4 1 3)) 1) a : ℝ)
def CB4_1_3I1S0_1_3E_4Log : Ball := .exact 0
def CB4_1_3I1S0_1_3E_4 : Ball := ⟨0, 0⟩
def CB4_1_3I1S0_1_3Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB4_1_3I1S0_1_3Entropy : Ball := ⟨0, 0⟩
def CB4_1_3I1S0_1_3Mass : Ball := ⟨1, 0⟩
def CB4_1_3I1S0_1_3MassTermLog : Ball := .exact 0
def CB4_1_3I1S0_1_3MassTerm : Ball := ⟨0, 0⟩
def CB4_1_3I1S0_1_3H : Ball := ⟨0, 0⟩
def CB4_1_3I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 1, 3 => CB4_1_3I1S0_1_3H
  | _, _, _ => (.exact 0)
def CB4_1_3I1Singleton : Ball := ⟨0, 0⟩
def CB4_1_3I1Group : Ball := ⟨(7275369214767643422929228408687 / 50000000000000000000000000000000), (6764398581 / 5000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB4_1_3I1H : Ball := ⟨(40774960481591935815520811893549 / 50000000000000000000000000000000), (363554979689 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB4_1_3I2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB4_1_3I2PairEntropy : Ball := ⟨(87993428354621611323967130846053 / 100000000000000000000000000000000), (59558866919 / 100000000000000000000000000000000)⟩
def CB4_1_3I2PairMass : Ball := ⟨1, (7 / 12500000000000000000000000000000)⟩
def CB4_1_3I2PairMassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB4_1_3I2PairMassTermLog : Ball := ⟨0, (10587911869 / 50000000000000000000000000000000)⟩
def CB4_1_3I2PairMassTerm : Ball := ⟨0, (21175823739 / 100000000000000000000000000000000)⟩
def CB4_1_3I2PairH : Ball := ⟨(87993428354621611323967130846053 / 100000000000000000000000000000000), (40367345329 / 50000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB4_1_3I2R0Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 1 3)) (fun u => (stageBLaw (shape 4 1 3) u : ℝ)) (stageBPriority (shape 4 1 3)) 2 (fun u a => (littleLaw (shape 4 1 3) u ((stageBPriority (shape 4 1 3)) 2) a : ℝ)) 0 a
def CB4_1_3I2R0Entropy : Ball := ⟨(53534388759604419469623257687 / 20000000000000000000000000000000), (46036787 / 50000000000000000000000000000000)⟩
def CB4_1_3I2R0Mass : Ball := ⟨(33446547050938077933247687037 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def CB4_1_3I2R0MassTermLogWitness : LogWitness := ⟨-12, 33446547050938077933247687037, 24414062500000000000000000000⟩
def CB4_1_3I2R0MassTermLog : Ball := ⟨(-800297691090102173365334880393559 / 100000000000000000000000000000000), (68821427717 / 25000000000000000000000000000000)⟩
def CB4_1_3I2R0MassTerm : Ball := ⟨(53534388759604419469623257687 / 20000000000000000000000000000000), (46036787 / 50000000000000000000000000000000)⟩
def CB4_1_3I2R0H : Ball := ⟨0, (46036787 / 25000000000000000000000000000000)⟩
def CB4_1_3I2R1Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 1 3)) (fun u => (stageBLaw (shape 4 1 3) u : ℝ)) (stageBPriority (shape 4 1 3)) 2 (fun u a => (littleLaw (shape 4 1 3) u ((stageBPriority (shape 4 1 3)) 2) a : ℝ)) 1 a
def CB4_1_3I2R1Entropy : Ball := ⟨(3578655809697544406731761086259 / 20000000000000000000000000000000), (1739898511 / 25000000000000000000000000000000)⟩
def CB4_1_3I2R1Mass : Ball := ⟨(3286575346523891131058813407701 / 50000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
def CB4_1_3I2R1MassTermLogWitness : LogWitness := ⟨-4, 3286575346523891131058813407701, 3125000000000000000000000000000⟩
def CB4_1_3I2R1MassTermLog : Ball := ⟨(-68054422772525543341333758289357 / 25000000000000000000000000000000), (52939559283 / 50000000000000000000000000000000)⟩
def CB4_1_3I2R1MassTerm : Ball := ⟨(3578655809697544406731761086259 / 20000000000000000000000000000000), (1739898511 / 25000000000000000000000000000000)⟩
def CB4_1_3I2R1H : Ball := ⟨0, (1739898511 / 12500000000000000000000000000000)⟩
def CB4_1_3I2R2Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 1 3)) (fun u => (stageBLaw (shape 4 1 3) u : ℝ)) (stageBPriority (shape 4 1 3)) 2 (fun u a => (littleLaw (shape 4 1 3) u ((stageBPriority (shape 4 1 3)) 2) a : ℝ)) 2 a
def CB4_1_3I2R2Entropy : Ball := ⟨(37288811804975475508956451972967 / 100000000000000000000000000000000), (26962464481 / 100000000000000000000000000000000)⟩
def CB4_1_3I2R2Mass : Ball := ⟨(2631369815114502473693307033871 / 6250000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
def CB4_1_3I2R2MassTermLogWitness : LogWitness := ⟨-2, 2631369815114502473693307033871, 1562500000000000000000000000000⟩
def CB4_1_3I2R2MassTermLog : Ball := ⟨(-43253845545051086682667535674217 / 50000000000000000000000000000000), (63527471077 / 100000000000000000000000000000000)⟩
def CB4_1_3I2R2MassTerm : Ball := ⟨(36421396337559143821240452719497 / 100000000000000000000000000000000), (26746283183 / 100000000000000000000000000000000)⟩
def CB4_1_3I2R2H : Ball := ⟨(86741546741633168771599925347 / 10000000000000000000000000000000), (3356796729 / 6250000000000000000000000000000)⟩
def CB4_1_3I2R3Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 1 3)) (fun u => (stageBLaw (shape 4 1 3) u : ℝ)) (stageBPriority (shape 4 1 3)) 2 (fun u a => (littleLaw (shape 4 1 3) u ((stageBPriority (shape 4 1 3)) 2) a : ℝ)) 3 a
def CB4_1_3I2R3Entropy : Ball := ⟨0, 0⟩
def CB4_1_3I2R3Mass : Ball := ⟨0, 0⟩
def CB4_1_3I2R3MassTerm : Ball := .exact 0
def CB4_1_3I2R3H : Ball := ⟨0, 0⟩
def CB4_1_3I2R4Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 1 3)) (fun u => (stageBLaw (shape 4 1 3) u : ℝ)) (stageBPriority (shape 4 1 3)) 2 (fun u a => (littleLaw (shape 4 1 3) u ((stageBPriority (shape 4 1 3)) 2) a : ℝ)) 4 a
def CB4_1_3I2R4Entropy : Ball := ⟨0, 0⟩
def CB4_1_3I2R4Mass : Ball := ⟨0, 0⟩
def CB4_1_3I2R4MassTerm : Ball := .exact 0
def CB4_1_3I2R4H : Ball := ⟨0, 0⟩
def CB4_1_3I2R5Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 1 3)) (fun u => (stageBLaw (shape 4 1 3) u : ℝ)) (stageBPriority (shape 4 1 3)) 2 (fun u a => (littleLaw (shape 4 1 3) u ((stageBPriority (shape 4 1 3)) 2) a : ℝ)) 5 a
def CB4_1_3I2R5Entropy : Ball := ⟨0, 0⟩
def CB4_1_3I2R5Mass : Ball := ⟨0, 0⟩
def CB4_1_3I2R5MassTerm : Ball := .exact 0
def CB4_1_3I2R5H : Ball := ⟨0, 0⟩
def CB4_1_3I2R6Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 1 3)) (fun u => (stageBLaw (shape 4 1 3) u : ℝ)) (stageBPriority (shape 4 1 3)) 2 (fun u a => (littleLaw (shape 4 1 3) u ((stageBPriority (shape 4 1 3)) 2) a : ℝ)) 6 a
def CB4_1_3I2R6Entropy : Ball := ⟨0, 0⟩
def CB4_1_3I2R6Mass : Ball := ⟨0, 0⟩
def CB4_1_3I2R6MassTerm : Ball := .exact 0
def CB4_1_3I2R6H : Ball := ⟨0, 0⟩
def CB4_1_3I2R7Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 1 3)) (fun u => (stageBLaw (shape 4 1 3) u : ℝ)) (stageBPriority (shape 4 1 3)) 2 (fun u a => (littleLaw (shape 4 1 3) u ((stageBPriority (shape 4 1 3)) 2) a : ℝ)) 7 a
def CB4_1_3I2R7Entropy : Ball := ⟨0, 0⟩
def CB4_1_3I2R7Mass : Ball := ⟨0, 0⟩
def CB4_1_3I2R7MassTerm : Ball := .exact 0
def CB4_1_3I2R7H : Ball := ⟨0, 0⟩
def CB4_1_3I2R8Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 1 3)) (fun u => (stageBLaw (shape 4 1 3) u : ℝ)) (stageBPriority (shape 4 1 3)) 2 (fun u a => (littleLaw (shape 4 1 3) u ((stageBPriority (shape 4 1 3)) 2) a : ℝ)) 8 a
def CB4_1_3I2R8Entropy : Ball := ⟨0, 0⟩
def CB4_1_3I2R8Mass : Ball := ⟨0, 0⟩
def CB4_1_3I2R8MassTerm : Ball := .exact 0
def CB4_1_3I2R8H : Ball := ⟨0, 0⟩
def CB4_1_3I2R9Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 1 3)) (fun u => (stageBLaw (shape 4 1 3) u : ℝ)) (stageBPriority (shape 4 1 3)) 2 (fun u a => (littleLaw (shape 4 1 3) u ((stageBPriority (shape 4 1 3)) 2) a : ℝ)) 9 a
def CB4_1_3I2R9Entropy : Ball := ⟨0, 0⟩
def CB4_1_3I2R9Mass : Ball := ⟨0, 0⟩
def CB4_1_3I2R9MassTerm : Ball := .exact 0
def CB4_1_3I2R9H : Ball := ⟨0, 0⟩
def CB4_1_3I2R10Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 1 3)) (fun u => (stageBLaw (shape 4 1 3) u : ℝ)) (stageBPriority (shape 4 1 3)) 2 (fun u a => (littleLaw (shape 4 1 3) u ((stageBPriority (shape 4 1 3)) 2) a : ℝ)) 10 a
def CB4_1_3I2R10Entropy : Ball := ⟨0, 0⟩
def CB4_1_3I2R10Mass : Ball := ⟨0, 0⟩
def CB4_1_3I2R10MassTerm : Ball := .exact 0
def CB4_1_3I2R10H : Ball := ⟨0, 0⟩
def CB4_1_3I2R11Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 1 3)) (fun u => (stageBLaw (shape 4 1 3) u : ℝ)) (stageBPriority (shape 4 1 3)) 2 (fun u a => (littleLaw (shape 4 1 3) u ((stageBPriority (shape 4 1 3)) 2) a : ℝ)) 11 a
def CB4_1_3I2R11Entropy : Ball := ⟨0, 0⟩
def CB4_1_3I2R11Mass : Ball := ⟨0, 0⟩
def CB4_1_3I2R11MassTerm : Ball := .exact 0
def CB4_1_3I2R11H : Ball := ⟨0, 0⟩
def CB4_1_3I2R12Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 1 3)) (fun u => (stageBLaw (shape 4 1 3) u : ℝ)) (stageBPriority (shape 4 1 3)) 2 (fun u a => (littleLaw (shape 4 1 3) u ((stageBPriority (shape 4 1 3)) 2) a : ℝ)) 12 a
def CB4_1_3I2R12Entropy : Ball := ⟨0, 0⟩
def CB4_1_3I2R12Mass : Ball := ⟨0, 0⟩
def CB4_1_3I2R12MassTerm : Ball := .exact 0
def CB4_1_3I2R12H : Ball := ⟨0, 0⟩
def CB4_1_3I2R13Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 1 3)) (fun u => (stageBLaw (shape 4 1 3) u : ℝ)) (stageBPriority (shape 4 1 3)) 2 (fun u a => (littleLaw (shape 4 1 3) u ((stageBPriority (shape 4 1 3)) 2) a : ℝ)) 13 a
def CB4_1_3I2R13Entropy : Ball := ⟨0, 0⟩
def CB4_1_3I2R13Mass : Ball := ⟨0, 0⟩
def CB4_1_3I2R13MassTerm : Ball := .exact 0
def CB4_1_3I2R13H : Ball := ⟨0, 0⟩
def CB4_1_3I2R14Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 1 3)) (fun u => (stageBLaw (shape 4 1 3) u : ℝ)) (stageBPriority (shape 4 1 3)) 2 (fun u a => (littleLaw (shape 4 1 3) u ((stageBPriority (shape 4 1 3)) 2) a : ℝ)) 14 a
def CB4_1_3I2R14Entropy : Ball := ⟨0, 0⟩
def CB4_1_3I2R14Mass : Ball := ⟨0, 0⟩
def CB4_1_3I2R14MassTerm : Ball := .exact 0
def CB4_1_3I2R14H : Ball := ⟨0, 0⟩
def CB4_1_3I2R15Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 1 3)) (fun u => (stageBLaw (shape 4 1 3) u : ℝ)) (stageBPriority (shape 4 1 3)) 2 (fun u a => (littleLaw (shape 4 1 3) u ((stageBPriority (shape 4 1 3)) 2) a : ℝ)) 15 a
def CB4_1_3I2R15Entropy : Ball := ⟨0, 0⟩
def CB4_1_3I2R15Mass : Ball := ⟨0, 0⟩
def CB4_1_3I2R15MassTerm : Ball := .exact 0
def CB4_1_3I2R15H : Ball := ⟨0, 0⟩
def CB4_1_3I2R16Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 1 3)) (fun u => (stageBLaw (shape 4 1 3) u : ℝ)) (stageBPriority (shape 4 1 3)) 2 (fun u a => (littleLaw (shape 4 1 3) u ((stageBPriority (shape 4 1 3)) 2) a : ℝ)) 16 a
def CB4_1_3I2R16Entropy : Ball := ⟨0, 0⟩
def CB4_1_3I2R16Mass : Ball := ⟨0, 0⟩
def CB4_1_3I2R16MassTerm : Ball := .exact 0
def CB4_1_3I2R16H : Ball := ⟨0, 0⟩
def CB4_1_3I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CB4_1_3I2R0H
  | 1 => CB4_1_3I2R1H
  | 2 => CB4_1_3I2R2H
  | 3 => CB4_1_3I2R3H
  | 4 => CB4_1_3I2R4H
  | 5 => CB4_1_3I2R5H
  | 6 => CB4_1_3I2R6H
  | 7 => CB4_1_3I2R7H
  | 8 => CB4_1_3I2R8H
  | 9 => CB4_1_3I2R9H
  | 10 => CB4_1_3I2R10H
  | 11 => CB4_1_3I2R11H
  | 12 => CB4_1_3I2R12H
  | 13 => CB4_1_3I2R13H
  | 14 => CB4_1_3I2R14H
  | 15 => CB4_1_3I2R15H
  | 16 => CB4_1_3I2R16H
  | _ => (.exact 0)
def CB4_1_3I2S1_0_3Value (a : Fin 6) : ℝ := (littleLaw (shape 4 1 3) (shape 1 0 3) ((stageBPriority (shape 4 1 3)) 2) a : ℝ)
def CB4_1_3I2S1_0_3E_1Log : Ball := .exact 0
def CB4_1_3I2S1_0_3E_1 : Ball := ⟨0, 0⟩
def CB4_1_3I2S1_0_3Terms (a : Fin 6) : Ball :=
  match a.val with
  | 1 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB4_1_3I2S1_0_3Entropy : Ball := ⟨0, 0⟩
def CB4_1_3I2S1_0_3Mass : Ball := ⟨1, 0⟩
def CB4_1_3I2S1_0_3MassTermLog : Ball := .exact 0
def CB4_1_3I2S1_0_3MassTerm : Ball := ⟨0, 0⟩
def CB4_1_3I2S1_0_3H : Ball := ⟨0, 0⟩
def CB4_1_3I2S2_0_2Value (a : Fin 6) : ℝ := (littleLaw (shape 4 1 3) (shape 2 0 2) ((stageBPriority (shape 4 1 3)) 2) a : ℝ)
def CB4_1_3I2S2_0_2E_2LogWitness : LogWitness := ⟨-1, 904277, 500000⟩
def CB4_1_3I2S2_0_2E_2Log : Ball := ⟨(-10061954959653018265030300181801 / 100000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def CB4_1_3I2S2_0_2E_2 : Ball := ⟨(4549397222525076198823402378749 / 50000000000000000000000000000000), (19148810313 / 50000000000000000000000000000000)⟩
def CB4_1_3I2S2_0_2E_3LogWitness : LogWitness := ⟨-4, 95723, 62500⟩
def CB4_1_3I2S2_0_2E_3Log : Ball := ⟨(-234629667502064329567169639454029 / 100000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
def CB4_1_3I2S2_0_2E_3 : Ball := ⟨(11229727831150051909579089698729 / 50000000000000000000000000000000), (10135066853 / 100000000000000000000000000000000)⟩
def CB4_1_3I2S2_0_2Terms (a : Fin 6) : Ball :=
  match a.val with
  | 2 => ⟨(4549397222525076198823402378749 / 50000000000000000000000000000000), (19148810313 / 50000000000000000000000000000000)⟩
  | 3 => ⟨(11229727831150051909579089698729 / 50000000000000000000000000000000), (10135066853 / 100000000000000000000000000000000)⟩
  | _ => (.exact 0)
def CB4_1_3I2S2_0_2Entropy : Ball := ⟨(7889562526837564054201246038739 / 25000000000000000000000000000000), (48432687479 / 100000000000000000000000000000000)⟩
def CB4_1_3I2S2_0_2Mass : Ball := ⟨1, 0⟩
def CB4_1_3I2S2_0_2MassTermLog : Ball := .exact 0
def CB4_1_3I2S2_0_2MassTerm : Ball := ⟨0, 0⟩
def CB4_1_3I2S2_0_2H : Ball := ⟨(7889562526837564054201246038739 / 25000000000000000000000000000000), (48432687479 / 100000000000000000000000000000000)⟩
def CB4_1_3I2S3_0_1Value (a : Fin 6) : ℝ := (littleLaw (shape 4 1 3) (shape 3 0 1) ((stageBPriority (shape 4 1 3)) 2) a : ℝ)
def CB4_1_3I2S3_0_1E_4Log : Ball := .exact 0
def CB4_1_3I2S3_0_1E_4 : Ball := ⟨0, 0⟩
def CB4_1_3I2S3_0_1Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB4_1_3I2S3_0_1Entropy : Ball := ⟨0, 0⟩
def CB4_1_3I2S3_0_1Mass : Ball := ⟨1, 0⟩
def CB4_1_3I2S3_0_1MassTermLog : Ball := .exact 0
def CB4_1_3I2S3_0_1MassTerm : Ball := ⟨0, 0⟩
def CB4_1_3I2S3_0_1H : Ball := ⟨0, 0⟩
def CB4_1_3I2S3_1_0Value (a : Fin 6) : ℝ := (littleLaw (shape 4 1 3) (shape 3 1 0) ((stageBPriority (shape 4 1 3)) 2) a : ℝ)
def CB4_1_3I2S3_1_0E_4Log : Ball := .exact 0
def CB4_1_3I2S3_1_0E_4 : Ball := ⟨0, 0⟩
def CB4_1_3I2S3_1_0Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB4_1_3I2S3_1_0Entropy : Ball := ⟨0, 0⟩
def CB4_1_3I2S3_1_0Mass : Ball := ⟨1, 0⟩
def CB4_1_3I2S3_1_0MassTermLog : Ball := .exact 0
def CB4_1_3I2S3_1_0MassTerm : Ball := ⟨0, 0⟩
def CB4_1_3I2S3_1_0H : Ball := ⟨0, 0⟩
def CB4_1_3I2S4_0_0Value (a : Fin 6) : ℝ := (littleLaw (shape 4 1 3) (shape 4 0 0) ((stageBPriority (shape 4 1 3)) 2) a : ℝ)
def CB4_1_3I2S4_0_0E_5Log : Ball := .exact 0
def CB4_1_3I2S4_0_0E_5 : Ball := ⟨0, 0⟩
def CB4_1_3I2S4_0_0Terms (a : Fin 6) : Ball :=
  match a.val with
  | 5 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB4_1_3I2S4_0_0Entropy : Ball := ⟨0, 0⟩
def CB4_1_3I2S4_0_0Mass : Ball := ⟨1, 0⟩
def CB4_1_3I2S4_0_0MassTermLog : Ball := .exact 0
def CB4_1_3I2S4_0_0MassTerm : Ball := ⟨0, 0⟩
def CB4_1_3I2S4_0_0H : Ball := ⟨0, 0⟩
def CB4_1_3I2Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 1, 0, 3 => CB4_1_3I2S1_0_3H
  | 2, 0, 2 => CB4_1_3I2S2_0_2H
  | 3, 0, 1 => CB4_1_3I2S3_0_1H
  | 3, 1, 0 => CB4_1_3I2S3_1_0H
  | 4, 0, 0 => CB4_1_3I2S4_0_0H
  | _, _, _ => (.exact 0)
def CB4_1_3I2Singleton : Ball := ⟨(83041426750315471544140407637 / 625000000000000000000000000000), (20391089907 / 100000000000000000000000000000000)⟩
def CB4_1_3I2Group : Ball := ⟨(1415404374746680713477846447539 / 10000000000000000000000000000000), (88203172807 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB4_1_3I2H : Ball := ⟨(59685340859687997054410201895273 / 100000000000000000000000000000000), (16071314767 / 6250000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB4_2_2I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB4_2_2I0Value (a : Fin 17) : ℝ := marginal (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) ((stageBPriority (shape 4 2 2)) 0) a
def CB4_2_2I0Entropy : Ball := ⟨(45702156180640825687140250957659 / 50000000000000000000000000000000), (3623391103 / 6250000000000000000000000000000)⟩
def CB4_2_2I0Mass : Ball := ⟨(99999999999999999999999999999999 / 100000000000000000000000000000000), (231 / 100000000000000000000000000000000)⟩
def CB4_2_2I0MassTermLogWitness : LogWitness := ⟨-1, 99999999999999999999999999999999, 50000000000000000000000000000000⟩
def CB4_2_2I0MassTermLog : Ball := ⟨0, (42351647597 / 100000000000000000000000000000000)⟩
def CB4_2_2I0MassTerm : Ball := ⟨0, (21175823799 / 50000000000000000000000000000000)⟩
def CB4_2_2I0H : Ball := ⟨(45702156180640825687140250957659 / 50000000000000000000000000000000), (50162952623 / 50000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB4_2_2I1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB4_2_2I1PairEntropy : Ball := ⟨(102676506272855419519486975464929 / 100000000000000000000000000000000), (3757150683 / 6250000000000000000000000000000)⟩
def CB4_2_2I1PairMass : Ball := ⟨(99999999999999999999999999999999 / 100000000000000000000000000000000), (47 / 20000000000000000000000000000000)⟩
def CB4_2_2I1PairMassTermLogWitness : LogWitness := ⟨-1, 99999999999999999999999999999999, 50000000000000000000000000000000⟩
def CB4_2_2I1PairMassTermLog : Ball := ⟨0, (42351647601 / 100000000000000000000000000000000)⟩
def CB4_2_2I1PairMassTerm : Ball := ⟨0, (21175823801 / 50000000000000000000000000000000)⟩
def CB4_2_2I1PairH : Ball := ⟨(102676506272855419519486975464929 / 100000000000000000000000000000000), (10246605853 / 10000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB4_2_2I1R0Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 1 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 1) a : ℝ)) 0 a
def CB4_2_2I1R0Entropy : Ball := ⟨(15589670341870072259151924157867 / 50000000000000000000000000000000), (15623939561 / 100000000000000000000000000000000)⟩
def CB4_2_2I1R0Mass : Ball := ⟨(18445491906614111134966090741223 / 100000000000000000000000000000000), (69 / 100000000000000000000000000000000)⟩
def CB4_2_2I1R0MassTermLogWitness : LogWitness := ⟨-3, 18445491906614111134966090741223, 12500000000000000000000000000000⟩
def CB4_2_2I1R0MassTermLog : Ball := ⟨(-169035018646263266787855854619957 / 100000000000000000000000000000000), (42351647553 / 50000000000000000000000000000000)⟩
def CB4_2_2I1R0MassTerm : Ball := ⟨(15589670341870072259151924157867 / 50000000000000000000000000000000), (15623939561 / 100000000000000000000000000000000)⟩
def CB4_2_2I1R0H : Ball := ⟨0, (15623939561 / 50000000000000000000000000000000)⟩
def CB4_2_2I1R1Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 1 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 1) a : ℝ)) 1 a
def CB4_2_2I1R1Entropy : Ball := ⟨(29049492844469626210844809336407 / 100000000000000000000000000000000), (835240879 / 3125000000000000000000000000000)⟩
def CB4_2_2I1R1Mass : Ball := ⟨(63109016186771777730067818517553 / 100000000000000000000000000000000), (93 / 100000000000000000000000000000000)⟩
def CB4_2_2I1R1MassTermLogWitness : LogWitness := ⟨-1, 63109016186771777730067818517553, 50000000000000000000000000000000⟩
def CB4_2_2I1R1MassTermLog : Ball := ⟨(-46030653937778645685871837091337 / 100000000000000000000000000000000), (42351647513 / 100000000000000000000000000000000)⟩
def CB4_2_2I1R1MassTerm : Ball := ⟨(29049492844469626210844809336407 / 100000000000000000000000000000000), (835240879 / 3125000000000000000000000000000)⟩
def CB4_2_2I1R1H : Ball := ⟨0, (835240879 / 1562500000000000000000000000000)⟩
def CB4_2_2I1R2Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 1 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 1) a : ℝ)) 2 a
def CB4_2_2I1R2Entropy : Ball := ⟨(4597850558356589058786207844237 / 12500000000000000000000000000000), (16664138137 / 100000000000000000000000000000000)⟩
def CB4_2_2I1R2Mass : Ball := ⟨(4603141655656228021547855770833 / 25000000000000000000000000000000), (7 / 10000000000000000000000000000000)⟩
def CB4_2_2I1R2MassTermLogWitness : LogWitness := ⟨-3, 4603141655656228021547855770833, 3125000000000000000000000000000⟩
def CB4_2_2I1R2MassTermLog : Ball := ⟨(-16921367858691658829236060089209 / 10000000000000000000000000000000), (10587911889 / 12500000000000000000000000000000)⟩
def CB4_2_2I1R2MassTerm : Ball := ⟨(7789145326102600430969774397921 / 25000000000000000000000000000000), (15596050763 / 100000000000000000000000000000000)⟩
def CB4_2_2I1R2H : Ball := ⟨(1406555790610577686602641290553 / 25000000000000000000000000000000), (322601889 / 1000000000000000000000000000000)⟩
def CB4_2_2I1R3Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 1 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 1) a : ℝ)) 3 a
def CB4_2_2I1R3Entropy : Ball := ⟨0, 0⟩
def CB4_2_2I1R3Mass : Ball := ⟨0, 0⟩
def CB4_2_2I1R3MassTerm : Ball := .exact 0
def CB4_2_2I1R3H : Ball := ⟨0, 0⟩
def CB4_2_2I1R4Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 1 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 1) a : ℝ)) 4 a
def CB4_2_2I1R4Entropy : Ball := ⟨0, 0⟩
def CB4_2_2I1R4Mass : Ball := ⟨0, 0⟩
def CB4_2_2I1R4MassTerm : Ball := .exact 0
def CB4_2_2I1R4H : Ball := ⟨0, 0⟩
def CB4_2_2I1R5Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 1 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 1) a : ℝ)) 5 a
def CB4_2_2I1R5Entropy : Ball := ⟨0, 0⟩
def CB4_2_2I1R5Mass : Ball := ⟨0, 0⟩
def CB4_2_2I1R5MassTerm : Ball := .exact 0
def CB4_2_2I1R5H : Ball := ⟨0, 0⟩
def CB4_2_2I1R6Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 1 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 1) a : ℝ)) 6 a
def CB4_2_2I1R6Entropy : Ball := ⟨0, 0⟩
def CB4_2_2I1R6Mass : Ball := ⟨0, 0⟩
def CB4_2_2I1R6MassTerm : Ball := .exact 0
def CB4_2_2I1R6H : Ball := ⟨0, 0⟩
def CB4_2_2I1R7Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 1 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 1) a : ℝ)) 7 a
def CB4_2_2I1R7Entropy : Ball := ⟨0, 0⟩
def CB4_2_2I1R7Mass : Ball := ⟨0, 0⟩
def CB4_2_2I1R7MassTerm : Ball := .exact 0
def CB4_2_2I1R7H : Ball := ⟨0, 0⟩
def CB4_2_2I1R8Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 1 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 1) a : ℝ)) 8 a
def CB4_2_2I1R8Entropy : Ball := ⟨0, 0⟩
def CB4_2_2I1R8Mass : Ball := ⟨0, 0⟩
def CB4_2_2I1R8MassTerm : Ball := .exact 0
def CB4_2_2I1R8H : Ball := ⟨0, 0⟩
def CB4_2_2I1R9Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 1 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 1) a : ℝ)) 9 a
def CB4_2_2I1R9Entropy : Ball := ⟨0, 0⟩
def CB4_2_2I1R9Mass : Ball := ⟨0, 0⟩
def CB4_2_2I1R9MassTerm : Ball := .exact 0
def CB4_2_2I1R9H : Ball := ⟨0, 0⟩
def CB4_2_2I1R10Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 1 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 1) a : ℝ)) 10 a
def CB4_2_2I1R10Entropy : Ball := ⟨0, 0⟩
def CB4_2_2I1R10Mass : Ball := ⟨0, 0⟩
def CB4_2_2I1R10MassTerm : Ball := .exact 0
def CB4_2_2I1R10H : Ball := ⟨0, 0⟩
def CB4_2_2I1R11Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 1 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 1) a : ℝ)) 11 a
def CB4_2_2I1R11Entropy : Ball := ⟨0, 0⟩
def CB4_2_2I1R11Mass : Ball := ⟨0, 0⟩
def CB4_2_2I1R11MassTerm : Ball := .exact 0
def CB4_2_2I1R11H : Ball := ⟨0, 0⟩
def CB4_2_2I1R12Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 1 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 1) a : ℝ)) 12 a
def CB4_2_2I1R12Entropy : Ball := ⟨0, 0⟩
def CB4_2_2I1R12Mass : Ball := ⟨0, 0⟩
def CB4_2_2I1R12MassTerm : Ball := .exact 0
def CB4_2_2I1R12H : Ball := ⟨0, 0⟩
def CB4_2_2I1R13Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 1 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 1) a : ℝ)) 13 a
def CB4_2_2I1R13Entropy : Ball := ⟨0, 0⟩
def CB4_2_2I1R13Mass : Ball := ⟨0, 0⟩
def CB4_2_2I1R13MassTerm : Ball := .exact 0
def CB4_2_2I1R13H : Ball := ⟨0, 0⟩
def CB4_2_2I1R14Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 1 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 1) a : ℝ)) 14 a
def CB4_2_2I1R14Entropy : Ball := ⟨0, 0⟩
def CB4_2_2I1R14Mass : Ball := ⟨0, 0⟩
def CB4_2_2I1R14MassTerm : Ball := .exact 0
def CB4_2_2I1R14H : Ball := ⟨0, 0⟩
def CB4_2_2I1R15Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 1 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 1) a : ℝ)) 15 a
def CB4_2_2I1R15Entropy : Ball := ⟨0, 0⟩
def CB4_2_2I1R15Mass : Ball := ⟨0, 0⟩
def CB4_2_2I1R15MassTerm : Ball := .exact 0
def CB4_2_2I1R15H : Ball := ⟨0, 0⟩
def CB4_2_2I1R16Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 1 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 1) a : ℝ)) 16 a
def CB4_2_2I1R16Entropy : Ball := ⟨0, 0⟩
def CB4_2_2I1R16Mass : Ball := ⟨0, 0⟩
def CB4_2_2I1R16MassTerm : Ball := .exact 0
def CB4_2_2I1R16H : Ball := ⟨0, 0⟩
def CB4_2_2I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CB4_2_2I1R0H
  | 1 => CB4_2_2I1R1H
  | 2 => CB4_2_2I1R2H
  | 3 => CB4_2_2I1R3H
  | 4 => CB4_2_2I1R4H
  | 5 => CB4_2_2I1R5H
  | 6 => CB4_2_2I1R6H
  | 7 => CB4_2_2I1R7H
  | 8 => CB4_2_2I1R8H
  | 9 => CB4_2_2I1R9H
  | 10 => CB4_2_2I1R10H
  | 11 => CB4_2_2I1R11H
  | 12 => CB4_2_2I1R12H
  | 13 => CB4_2_2I1R13H
  | 14 => CB4_2_2I1R14H
  | 15 => CB4_2_2I1R15H
  | 16 => CB4_2_2I1R16H
  | _ => (.exact 0)
def CB4_2_2I1S0_2_2Value (a : Fin 6) : ℝ := (littleLaw (shape 4 2 2) (shape 0 2 2) ((stageBPriority (shape 4 2 2)) 1) a : ℝ)
def CB4_2_2I1S0_2_2E_2LogWitness : LogWitness := ⟨-1, 936679, 500000⟩
def CB4_2_2I1S0_2_2E_2Log : Ball := ⟨(-6541463814935642164057959379121 / 100000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def CB4_2_2I1S0_2_2E_2 : Ball := ⟨(1531812946177525591646911333319 / 25000000000000000000000000000000), (2479368669 / 6250000000000000000000000000000)⟩
def CB4_2_2I1S0_2_2E_3LogWitness : LogWitness := ⟨-4, 63321, 62500⟩
def CB4_2_2I1S0_2_2E_3Log : Ball := ⟨(-275953825129554669064816416181401 / 100000000000000000000000000000000), (52939559207 / 50000000000000000000000000000000)⟩
def CB4_2_2I1S0_2_2E_3 : Ball := ⟨(8736836080514265599926620144511 / 50000000000000000000000000000000), (3352185829 / 50000000000000000000000000000000)⟩
def CB4_2_2I1S0_2_2Terms (a : Fin 6) : Ball :=
  match a.val with
  | 2 => ⟨(1531812946177525591646911333319 / 25000000000000000000000000000000), (2479368669 / 6250000000000000000000000000000)⟩
  | 3 => ⟨(8736836080514265599926620144511 / 50000000000000000000000000000000), (3352185829 / 50000000000000000000000000000000)⟩
  | _ => (.exact 0)
def CB4_2_2I1S0_2_2Entropy : Ball := ⟨(11800461972869316783220442811149 / 50000000000000000000000000000000), (23187135181 / 50000000000000000000000000000000)⟩
def CB4_2_2I1S0_2_2Mass : Ball := ⟨1, 0⟩
def CB4_2_2I1S0_2_2MassTermLog : Ball := .exact 0
def CB4_2_2I1S0_2_2MassTerm : Ball := ⟨0, 0⟩
def CB4_2_2I1S0_2_2H : Ball := ⟨(11800461972869316783220442811149 / 50000000000000000000000000000000), (23187135181 / 50000000000000000000000000000000)⟩
def CB4_2_2I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => CB4_2_2I1S0_2_2H
  | _, _, _ => (.exact 0)
def CB4_2_2I1Singleton : Ball := ⟨(7770671233209326715362979197 / 100000000000000000000000000000000), (15268861 / 100000000000000000000000000000000)⟩
def CB4_2_2I1Group : Ball := ⟨(5633993833675520073125928141409 / 100000000000000000000000000000000), (116978753139 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB4_2_2I1H : Ball := ⟨(91408518605504379373235119182111 / 100000000000000000000000000000000), (42052945601 / 12500000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB4_2_2I2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB4_2_2I2PairEntropy : Ball := ⟨(85162052080008727387344059300039 / 100000000000000000000000000000000), (58730629971 / 100000000000000000000000000000000)⟩
def CB4_2_2I2PairMass : Ball := ⟨(99999999999999999999999999999999 / 100000000000000000000000000000000), (233 / 100000000000000000000000000000000)⟩
def CB4_2_2I2PairMassTermLogWitness : LogWitness := ⟨-1, 99999999999999999999999999999999, 50000000000000000000000000000000⟩
def CB4_2_2I2PairMassTermLog : Ball := ⟨0, (42351647599 / 100000000000000000000000000000000)⟩
def CB4_2_2I2PairMassTerm : Ball := ⟨0, (105879119 / 250000000000000000000000000000)⟩
def CB4_2_2I2PairH : Ball := ⟨(85162052080008727387344059300039 / 100000000000000000000000000000000), (101082277571 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB4_2_2I2R0Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) 0 a
def CB4_2_2I2R0Entropy : Ball := ⟨(264017467412789009261745911423 / 100000000000000000000000000000000), (90638611 / 100000000000000000000000000000000)⟩
def CB4_2_2I2R0Mass : Ball := ⟨(32925283989199048774667657891 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def CB4_2_2I2R0MassTermLogWitness : LogWitness := ⟨-12, 32925283989199048774667657891, 24414062500000000000000000000⟩
def CB4_2_2I2R0MassTermLog : Ball := ⟨(-801868459204174003272721095524521 / 100000000000000000000000000000000), (68821427729 / 25000000000000000000000000000000)⟩
def CB4_2_2I2R0MassTerm : Ball := ⟨(264017467412789009261745911423 / 100000000000000000000000000000000), (90638611 / 100000000000000000000000000000000)⟩
def CB4_2_2I2R0H : Ball := ⟨0, (90638611 / 50000000000000000000000000000000)⟩
def CB4_2_2I2R1Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) 1 a
def CB4_2_2I2R1Entropy : Ball := ⟨(19973363265378585772023469851697 / 100000000000000000000000000000000), (8310008839 / 100000000000000000000000000000000)⟩
def CB4_2_2I2R1Mass : Ball := ⟨(3924290670247618121826431431639 / 50000000000000000000000000000000), (3 / 10000000000000000000000000000000)⟩
def CB4_2_2I2R1MassTermLogWitness : LogWitness := ⟨-4, 3924290670247618121826431431639, 3125000000000000000000000000000⟩
def CB4_2_2I2R1MassTermLog : Ball := ⟨(-254483739148179485664331227253563 / 100000000000000000000000000000000), (26469779699 / 25000000000000000000000000000000)⟩
def CB4_2_2I2R1MassTerm : Ball := ⟨(19973363265378585772023469851697 / 100000000000000000000000000000000), (8310008839 / 100000000000000000000000000000000)⟩
def CB4_2_2I2R1H : Ball := ⟨0, (8310008839 / 50000000000000000000000000000000)⟩
def CB4_2_2I2R2Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) 2 a
def CB4_2_2I2R2Entropy : Ball := ⟨(2270812985169661110851307229101 / 6250000000000000000000000000000), (1523492799 / 6250000000000000000000000000000)⟩
def CB4_2_2I2R2Mass : Ball := ⟨(11052400912504742196751447679061 / 20000000000000000000000000000000), (13 / 20000000000000000000000000000000)⟩
def CB4_2_2I2R2MassTermLogWitness : LogWitness := ⟨-1, 11052400912504742196751447679061, 10000000000000000000000000000000⟩
def CB4_2_2I2R2MassTermLog : Ball := ⟨(-29654229602087001636360652787339 / 50000000000000000000000000000000), (42351647483 / 100000000000000000000000000000000)⟩
def CB4_2_2I2R2MassTerm : Ball := ⟨(4096880428921643937267339657819 / 12500000000000000000000000000000), (5851092351 / 25000000000000000000000000000000)⟩
def CB4_2_2I2R2H : Ball := ⟨(444745541417678284435274800383 / 12500000000000000000000000000000), (11945063547 / 25000000000000000000000000000000)⟩
def CB4_2_2I2R3Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) 3 a
def CB4_2_2I2R3Entropy : Ball := ⟨0, 0⟩
def CB4_2_2I2R3Mass : Ball := ⟨0, 0⟩
def CB4_2_2I2R3MassTerm : Ball := .exact 0
def CB4_2_2I2R3H : Ball := ⟨0, 0⟩
def CB4_2_2I2R4Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) 4 a
def CB4_2_2I2R4Entropy : Ball := ⟨0, 0⟩
def CB4_2_2I2R4Mass : Ball := ⟨0, 0⟩
def CB4_2_2I2R4MassTerm : Ball := .exact 0
def CB4_2_2I2R4H : Ball := ⟨0, 0⟩
def CB4_2_2I2R5Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) 5 a
def CB4_2_2I2R5Entropy : Ball := ⟨0, 0⟩
def CB4_2_2I2R5Mass : Ball := ⟨0, 0⟩
def CB4_2_2I2R5MassTerm : Ball := .exact 0
def CB4_2_2I2R5H : Ball := ⟨0, 0⟩
def CB4_2_2I2R6Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) 6 a
def CB4_2_2I2R6Entropy : Ball := ⟨0, 0⟩
def CB4_2_2I2R6Mass : Ball := ⟨0, 0⟩
def CB4_2_2I2R6MassTerm : Ball := .exact 0
def CB4_2_2I2R6H : Ball := ⟨0, 0⟩
def CB4_2_2I2R7Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) 7 a
def CB4_2_2I2R7Entropy : Ball := ⟨0, 0⟩
def CB4_2_2I2R7Mass : Ball := ⟨0, 0⟩
def CB4_2_2I2R7MassTerm : Ball := .exact 0
def CB4_2_2I2R7H : Ball := ⟨0, 0⟩
def CB4_2_2I2R8Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) 8 a
def CB4_2_2I2R8Entropy : Ball := ⟨0, 0⟩
def CB4_2_2I2R8Mass : Ball := ⟨0, 0⟩
def CB4_2_2I2R8MassTerm : Ball := .exact 0
def CB4_2_2I2R8H : Ball := ⟨0, 0⟩
def CB4_2_2I2R9Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) 9 a
def CB4_2_2I2R9Entropy : Ball := ⟨0, 0⟩
def CB4_2_2I2R9Mass : Ball := ⟨0, 0⟩
def CB4_2_2I2R9MassTerm : Ball := .exact 0
def CB4_2_2I2R9H : Ball := ⟨0, 0⟩
def CB4_2_2I2R10Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) 10 a
def CB4_2_2I2R10Entropy : Ball := ⟨0, 0⟩
def CB4_2_2I2R10Mass : Ball := ⟨0, 0⟩
def CB4_2_2I2R10MassTerm : Ball := .exact 0
def CB4_2_2I2R10H : Ball := ⟨0, 0⟩
def CB4_2_2I2R11Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) 11 a
def CB4_2_2I2R11Entropy : Ball := ⟨0, 0⟩
def CB4_2_2I2R11Mass : Ball := ⟨0, 0⟩
def CB4_2_2I2R11MassTerm : Ball := .exact 0
def CB4_2_2I2R11H : Ball := ⟨0, 0⟩
def CB4_2_2I2R12Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) 12 a
def CB4_2_2I2R12Entropy : Ball := ⟨0, 0⟩
def CB4_2_2I2R12Mass : Ball := ⟨0, 0⟩
def CB4_2_2I2R12MassTerm : Ball := .exact 0
def CB4_2_2I2R12H : Ball := ⟨0, 0⟩
def CB4_2_2I2R13Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) 13 a
def CB4_2_2I2R13Entropy : Ball := ⟨0, 0⟩
def CB4_2_2I2R13Mass : Ball := ⟨0, 0⟩
def CB4_2_2I2R13MassTerm : Ball := .exact 0
def CB4_2_2I2R13H : Ball := ⟨0, 0⟩
def CB4_2_2I2R14Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) 14 a
def CB4_2_2I2R14Entropy : Ball := ⟨0, 0⟩
def CB4_2_2I2R14Mass : Ball := ⟨0, 0⟩
def CB4_2_2I2R14MassTerm : Ball := .exact 0
def CB4_2_2I2R14H : Ball := ⟨0, 0⟩
def CB4_2_2I2R15Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) 15 a
def CB4_2_2I2R15Entropy : Ball := ⟨0, 0⟩
def CB4_2_2I2R15Mass : Ball := ⟨0, 0⟩
def CB4_2_2I2R15MassTerm : Ball := .exact 0
def CB4_2_2I2R15H : Ball := ⟨0, 0⟩
def CB4_2_2I2R16Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) 16 a
def CB4_2_2I2R16Entropy : Ball := ⟨0, 0⟩
def CB4_2_2I2R16Mass : Ball := ⟨0, 0⟩
def CB4_2_2I2R16MassTerm : Ball := .exact 0
def CB4_2_2I2R16H : Ball := ⟨0, 0⟩
def CB4_2_2I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CB4_2_2I2R0H
  | 1 => CB4_2_2I2R1H
  | 2 => CB4_2_2I2R2H
  | 3 => CB4_2_2I2R3H
  | 4 => CB4_2_2I2R4H
  | 5 => CB4_2_2I2R5H
  | 6 => CB4_2_2I2R6H
  | 7 => CB4_2_2I2R7H
  | 8 => CB4_2_2I2R8H
  | 9 => CB4_2_2I2R9H
  | 10 => CB4_2_2I2R10H
  | 11 => CB4_2_2I2R11H
  | 12 => CB4_2_2I2R12H
  | 13 => CB4_2_2I2R13H
  | 14 => CB4_2_2I2R14H
  | 15 => CB4_2_2I2R15H
  | 16 => CB4_2_2I2R16H
  | _ => (.exact 0)
def CB4_2_2I2S2_0_2Value (a : Fin 6) : ℝ := (littleLaw (shape 4 2 2) (shape 2 0 2) ((stageBPriority (shape 4 2 2)) 2) a : ℝ)
def CB4_2_2I2S2_0_2E_2LogWitness : LogWitness := ⟨-1, 447669, 250000⟩
def CB4_2_2I2S2_0_2E_2Log : Ball := ⟨(-11055397836918052136994139561117 / 100000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def CB4_2_2I2S2_0_2E_2 : Ball := ⟨(9898317788510534964232058926371 / 100000000000000000000000000000000), (151676157 / 400000000000000000000000000000)⟩
def CB4_2_2I2S2_0_2E_3LogWitness : LogWitness := ⟨-4, 52331, 31250⟩
def CB4_2_2I2S2_0_2E_3Log : Ball := ⟨(-14106369804520244990198383124901 / 6250000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
def CB4_2_2I2S2_0_2E_3 : Ball := ⟨(11811207011845583049313145396947 / 50000000000000000000000000000000), (2770380073 / 25000000000000000000000000000000)⟩
def CB4_2_2I2S2_0_2Terms (a : Fin 6) : Ball :=
  match a.val with
  | 2 => ⟨(9898317788510534964232058926371 / 100000000000000000000000000000000), (151676157 / 400000000000000000000000000000)⟩
  | 3 => ⟨(11811207011845583049313145396947 / 50000000000000000000000000000000), (2770380073 / 25000000000000000000000000000000)⟩
  | _ => (.exact 0)
def CB4_2_2I2S2_0_2Entropy : Ball := ⟨(6704146362440340212571669944053 / 20000000000000000000000000000000), (24500279771 / 50000000000000000000000000000000)⟩
def CB4_2_2I2S2_0_2Mass : Ball := ⟨1, 0⟩
def CB4_2_2I2S2_0_2MassTermLog : Ball := .exact 0
def CB4_2_2I2S2_0_2MassTerm : Ball := ⟨0, 0⟩
def CB4_2_2I2S2_0_2H : Ball := ⟨(6704146362440340212571669944053 / 20000000000000000000000000000000), (24500279771 / 50000000000000000000000000000000)⟩
def CB4_2_2I2S2_2_0Value (a : Fin 6) : ℝ := (littleLaw (shape 4 2 2) (shape 2 2 0) ((stageBPriority (shape 4 2 2)) 2) a : ℝ)
def CB4_2_2I2S2_2_0E_2LogWitness : LogWitness := ⟨-1, 447549, 250000⟩
def CB4_2_2I2S2_2_0E_2Log : Ball := ⟨(-692637934343495837134511622293 / 6250000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def CB4_2_2I2S2_2_0E_2 : Ball := ⟨(495983063803995549461941667273 / 5000000000000000000000000000000), (7581774971 / 20000000000000000000000000000000)⟩
def CB4_2_2I2S2_2_0E_3LogWitness : LogWitness := ⟨-4, 52451, 31250⟩
def CB4_2_2I2S2_2_0E_3Log : Ball := ⟨(-225472869798470476592187191794959 / 100000000000000000000000000000000), (52939559207 / 50000000000000000000000000000000)⟩
def CB4_2_2I2S2_2_0E_3 : Ball := ⟨(946102199503965997418944831747 / 4000000000000000000000000000000), (11106931281 / 100000000000000000000000000000000)⟩
def CB4_2_2I2S2_2_0Terms (a : Fin 6) : Ball :=
  match a.val with
  | 2 => ⟨(495983063803995549461941667273 / 5000000000000000000000000000000), (7581774971 / 20000000000000000000000000000000)⟩
  | 3 => ⟨(946102199503965997418944831747 / 4000000000000000000000000000000), (11106931281 / 100000000000000000000000000000000)⟩
  | _ => (.exact 0)
def CB4_2_2I2S2_2_0Entropy : Ball := ⟨(6714443252735812184942490827827 / 20000000000000000000000000000000), (6126975767 / 12500000000000000000000000000000)⟩
def CB4_2_2I2S2_2_0Mass : Ball := ⟨1, 0⟩
def CB4_2_2I2S2_2_0MassTermLog : Ball := .exact 0
def CB4_2_2I2S2_2_0MassTerm : Ball := ⟨0, 0⟩
def CB4_2_2I2S2_2_0H : Ball := ⟨(6714443252735812184942490827827 / 20000000000000000000000000000000), (6126975767 / 12500000000000000000000000000000)⟩
def CB4_2_2I2S3_0_1Value (a : Fin 6) : ℝ := (littleLaw (shape 4 2 2) (shape 3 0 1) ((stageBPriority (shape 4 2 2)) 2) a : ℝ)
def CB4_2_2I2S3_0_1E_4Log : Ball := .exact 0
def CB4_2_2I2S3_0_1E_4 : Ball := ⟨0, 0⟩
def CB4_2_2I2S3_0_1Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB4_2_2I2S3_0_1Entropy : Ball := ⟨0, 0⟩
def CB4_2_2I2S3_0_1Mass : Ball := ⟨1, 0⟩
def CB4_2_2I2S3_0_1MassTermLog : Ball := .exact 0
def CB4_2_2I2S3_0_1MassTerm : Ball := ⟨0, 0⟩
def CB4_2_2I2S3_0_1H : Ball := ⟨0, 0⟩
def CB4_2_2I2S3_1_0Value (a : Fin 6) : ℝ := (littleLaw (shape 4 2 2) (shape 3 1 0) ((stageBPriority (shape 4 2 2)) 2) a : ℝ)
def CB4_2_2I2S3_1_0E_4Log : Ball := .exact 0
def CB4_2_2I2S3_1_0E_4 : Ball := ⟨0, 0⟩
def CB4_2_2I2S3_1_0Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB4_2_2I2S3_1_0Entropy : Ball := ⟨0, 0⟩
def CB4_2_2I2S3_1_0Mass : Ball := ⟨1, 0⟩
def CB4_2_2I2S3_1_0MassTermLog : Ball := .exact 0
def CB4_2_2I2S3_1_0MassTerm : Ball := ⟨0, 0⟩
def CB4_2_2I2S3_1_0H : Ball := ⟨0, 0⟩
def CB4_2_2I2S4_0_0Value (a : Fin 6) : ℝ := (littleLaw (shape 4 2 2) (shape 4 0 0) ((stageBPriority (shape 4 2 2)) 2) a : ℝ)
def CB4_2_2I2S4_0_0E_5Log : Ball := .exact 0
def CB4_2_2I2S4_0_0E_5 : Ball := ⟨0, 0⟩
def CB4_2_2I2S4_0_0Terms (a : Fin 6) : Ball :=
  match a.val with
  | 5 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB4_2_2I2S4_0_0Entropy : Ball := ⟨0, 0⟩
def CB4_2_2I2S4_0_0Mass : Ball := ⟨1, 0⟩
def CB4_2_2I2S4_0_0MassTermLog : Ball := .exact 0
def CB4_2_2I2S4_0_0MassTerm : Ball := ⟨0, 0⟩
def CB4_2_2I2S4_0_0H : Ball := ⟨0, 0⟩
def CB4_2_2I2Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 2, 0, 2 => CB4_2_2I2S2_0_2H
  | 2, 2, 0 => CB4_2_2I2S2_2_0H
  | 3, 0, 1 => CB4_2_2I2S3_0_1H
  | 3, 1, 0 => CB4_2_2I2S3_1_0H
  | 4, 0, 0 => CB4_2_2I2S4_0_0H
  | _, _, _ => (.exact 0)
def CB4_2_2I2Singleton : Ball := ⟨(388803395094619629894314275621 / 4000000000000000000000000000000), (2840022457 / 20000000000000000000000000000000)⟩
def CB4_2_2I2Group : Ball := ⟨(13278049208706917022840055293589 / 100000000000000000000000000000000), (78781661373 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB4_2_2I2H : Ball := ⟨(58605953662594893341663948712861 / 100000000000000000000000000000000), (258645600317 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB4_3_1I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB4_3_1I0Value (a : Fin 17) : ℝ := marginal (below (shape 4 3 1)) (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) ((stageBPriority (shape 4 3 1)) 0) a
def CB4_3_1I0Entropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (2646977967 / 6250000000000000000000000000000)⟩
def CB4_3_1I0Mass : Ball := ⟨(50000000000000000000000000000001 / 50000000000000000000000000000000), (31 / 50000000000000000000000000000000)⟩
def CB4_3_1I0MassTermLogWitness : LogWitness := ⟨0, 50000000000000000000000000000001, 50000000000000000000000000000000⟩
def CB4_3_1I0MassTermLog : Ball := ⟨(1 / 50000000000000000000000000000000), (165436123 / 781250000000000000000000000000)⟩
def CB4_3_1I0MassTerm : Ball := ⟨(-1 / 50000000000000000000000000000000), (4235164749 / 20000000000000000000000000000000)⟩
def CB4_3_1I0H : Ball := ⟨(17328679513998632735430798262583 / 25000000000000000000000000000000), (63527471217 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB4_3_1I1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB4_3_1I1PairEntropy : Ball := ⟨(27684897679285330046180207348117 / 25000000000000000000000000000000), (35913846749 / 50000000000000000000000000000000)⟩
def CB4_3_1I1PairMass : Ball := ⟨(50000000000000000000000000000001 / 50000000000000000000000000000000), (1 / 1562500000000000000000000000000)⟩
def CB4_3_1I1PairMassTermLogWitness : LogWitness := ⟨0, 50000000000000000000000000000001, 50000000000000000000000000000000⟩
def CB4_3_1I1PairMassTermLog : Ball := ⟨(1 / 50000000000000000000000000000000), (10587911873 / 50000000000000000000000000000000)⟩
def CB4_3_1I1PairMassTerm : Ball := ⟨(-1 / 50000000000000000000000000000000), (21175823747 / 100000000000000000000000000000000)⟩
def CB4_3_1I1PairH : Ball := ⟨(11073959071714132018472082939247 / 10000000000000000000000000000000), (18600703449 / 20000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB4_3_1I1R0Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 3 1)) (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 1 (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 1) a : ℝ)) 0 a
def CB4_3_1I1R0Entropy : Ball := ⟨(1147190843975657773974584037547 / 20000000000000000000000000000000), (1124096677 / 50000000000000000000000000000000)⟩
def CB4_3_1I1R0Mass : Ball := ⟨(663549549127581616184973285819 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def CB4_3_1I1R0MassTermLogWitness : LogWitness := ⟨-7, 663549549127581616184973285819, 390625000000000000000000000000⟩
def CB4_3_1I1R0MassTermLog : Ball := ⟨(-216108737750623834291693366203169 / 50000000000000000000000000000000), (42351647479 / 25000000000000000000000000000000)⟩
def CB4_3_1I1R0MassTerm : Ball := ⟨(1147190843975657773974584037547 / 20000000000000000000000000000000), (1124096677 / 50000000000000000000000000000000)⟩
def CB4_3_1I1R0H : Ball := ⟨0, (1124096677 / 25000000000000000000000000000000)⟩
def CB4_3_1I1R1Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 3 1)) (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 1 (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 1) a : ℝ)) 1 a
def CB4_3_1I1R1Entropy : Ball := ⟨(273803228812459785691571806703 / 781250000000000000000000000000), (966270721 / 3125000000000000000000000000000)⟩
def CB4_3_1I1R1Mass : Ball := ⟨(48672900901744836767630053428363 / 100000000000000000000000000000000), (1 / 4000000000000000000000000000000)⟩
def CB4_3_1I1R1MassTermLogWitness : LogWitness := ⟨-2, 48672900901744836767630053428363, 25000000000000000000000000000000⟩
def CB4_3_1I1R1MassTermLog : Ball := ⟨(-3600238802156385008240902157601 / 5000000000000000000000000000000), (635274711 / 1000000000000000000000000000000)⟩
def CB4_3_1I1R1MassTerm : Ball := ⟨(273803228812459785691571806703 / 781250000000000000000000000000), (966270721 / 3125000000000000000000000000000)⟩
def CB4_3_1I1R1H : Ball := ⟨0, (966270721 / 1562500000000000000000000000000)⟩
def CB4_3_1I1R2Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 3 1)) (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 1 (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 1) a : ℝ)) 2 a
def CB4_3_1I1R2Entropy : Ball := ⟨(49633841138692371222487494508499 / 100000000000000000000000000000000), (6733130679 / 20000000000000000000000000000000)⟩
def CB4_3_1I1R2Mass : Ball := ⟨(48672900901744836767630053428363 / 100000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
def CB4_3_1I1R2MassTermLogWitness : LogWitness := ⟨-2, 48672900901744836767630053428363, 25000000000000000000000000000000⟩
def CB4_3_1I1R2MassTermLog : Ball := ⟨(-3600238802156385008240902157601 / 5000000000000000000000000000000), (31763735551 / 50000000000000000000000000000000)⟩
def CB4_3_1I1R2MassTerm : Ball := ⟨(273803228812459785691571806703 / 781250000000000000000000000000), (15460331537 / 50000000000000000000000000000000)⟩
def CB4_3_1I1R2H : Ball := ⟨(2917405570139503730793260650103 / 20000000000000000000000000000000), (64586316469 / 100000000000000000000000000000000)⟩
def CB4_3_1I1R3Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 3 1)) (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 1 (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 1) a : ℝ)) 3 a
def CB4_3_1I1R3Entropy : Ball := ⟨(5624416465391076871446041112211 / 100000000000000000000000000000000), (2191533999 / 100000000000000000000000000000000)⟩
def CB4_3_1I1R3Mass : Ball := ⟨(1293653321378517322144444232489 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
def CB4_3_1I1R3MassTermLogWitness : LogWitness := ⟨-7, 1293653321378517322144444232489, 781250000000000000000000000000⟩
def CB4_3_1I1R3MassTermLog : Ball := ⟨(-434769993818567805721764350077799 / 100000000000000000000000000000000), (3388131797 / 2000000000000000000000000000000)⟩
def CB4_3_1I1R3MassTerm : Ball := ⟨(5624416465391076871446041112211 / 100000000000000000000000000000000), (2191533999 / 100000000000000000000000000000000)⟩
def CB4_3_1I1R3H : Ball := ⟨0, (2191533999 / 50000000000000000000000000000000)⟩
def CB4_3_1I1R4Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 3 1)) (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 1 (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 1) a : ℝ)) 4 a
def CB4_3_1I1R4Entropy : Ball := ⟨0, 0⟩
def CB4_3_1I1R4Mass : Ball := ⟨0, 0⟩
def CB4_3_1I1R4MassTerm : Ball := .exact 0
def CB4_3_1I1R4H : Ball := ⟨0, 0⟩
def CB4_3_1I1R5Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 3 1)) (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 1 (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 1) a : ℝ)) 5 a
def CB4_3_1I1R5Entropy : Ball := ⟨0, 0⟩
def CB4_3_1I1R5Mass : Ball := ⟨0, 0⟩
def CB4_3_1I1R5MassTerm : Ball := .exact 0
def CB4_3_1I1R5H : Ball := ⟨0, 0⟩
def CB4_3_1I1R6Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 3 1)) (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 1 (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 1) a : ℝ)) 6 a
def CB4_3_1I1R6Entropy : Ball := ⟨0, 0⟩
def CB4_3_1I1R6Mass : Ball := ⟨0, 0⟩
def CB4_3_1I1R6MassTerm : Ball := .exact 0
def CB4_3_1I1R6H : Ball := ⟨0, 0⟩
def CB4_3_1I1R7Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 3 1)) (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 1 (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 1) a : ℝ)) 7 a
def CB4_3_1I1R7Entropy : Ball := ⟨0, 0⟩
def CB4_3_1I1R7Mass : Ball := ⟨0, 0⟩
def CB4_3_1I1R7MassTerm : Ball := .exact 0
def CB4_3_1I1R7H : Ball := ⟨0, 0⟩
def CB4_3_1I1R8Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 3 1)) (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 1 (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 1) a : ℝ)) 8 a
def CB4_3_1I1R8Entropy : Ball := ⟨0, 0⟩
def CB4_3_1I1R8Mass : Ball := ⟨0, 0⟩
def CB4_3_1I1R8MassTerm : Ball := .exact 0
def CB4_3_1I1R8H : Ball := ⟨0, 0⟩
def CB4_3_1I1R9Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 3 1)) (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 1 (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 1) a : ℝ)) 9 a
def CB4_3_1I1R9Entropy : Ball := ⟨0, 0⟩
def CB4_3_1I1R9Mass : Ball := ⟨0, 0⟩
def CB4_3_1I1R9MassTerm : Ball := .exact 0
def CB4_3_1I1R9H : Ball := ⟨0, 0⟩
def CB4_3_1I1R10Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 3 1)) (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 1 (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 1) a : ℝ)) 10 a
def CB4_3_1I1R10Entropy : Ball := ⟨0, 0⟩
def CB4_3_1I1R10Mass : Ball := ⟨0, 0⟩
def CB4_3_1I1R10MassTerm : Ball := .exact 0
def CB4_3_1I1R10H : Ball := ⟨0, 0⟩
def CB4_3_1I1R11Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 3 1)) (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 1 (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 1) a : ℝ)) 11 a
def CB4_3_1I1R11Entropy : Ball := ⟨0, 0⟩
def CB4_3_1I1R11Mass : Ball := ⟨0, 0⟩
def CB4_3_1I1R11MassTerm : Ball := .exact 0
def CB4_3_1I1R11H : Ball := ⟨0, 0⟩
def CB4_3_1I1R12Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 3 1)) (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 1 (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 1) a : ℝ)) 12 a
def CB4_3_1I1R12Entropy : Ball := ⟨0, 0⟩
def CB4_3_1I1R12Mass : Ball := ⟨0, 0⟩
def CB4_3_1I1R12MassTerm : Ball := .exact 0
def CB4_3_1I1R12H : Ball := ⟨0, 0⟩
def CB4_3_1I1R13Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 3 1)) (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 1 (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 1) a : ℝ)) 13 a
def CB4_3_1I1R13Entropy : Ball := ⟨0, 0⟩
def CB4_3_1I1R13Mass : Ball := ⟨0, 0⟩
def CB4_3_1I1R13MassTerm : Ball := .exact 0
def CB4_3_1I1R13H : Ball := ⟨0, 0⟩
def CB4_3_1I1R14Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 3 1)) (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 1 (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 1) a : ℝ)) 14 a
def CB4_3_1I1R14Entropy : Ball := ⟨0, 0⟩
def CB4_3_1I1R14Mass : Ball := ⟨0, 0⟩
def CB4_3_1I1R14MassTerm : Ball := .exact 0
def CB4_3_1I1R14H : Ball := ⟨0, 0⟩
def CB4_3_1I1R15Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 3 1)) (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 1 (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 1) a : ℝ)) 15 a
def CB4_3_1I1R15Entropy : Ball := ⟨0, 0⟩
def CB4_3_1I1R15Mass : Ball := ⟨0, 0⟩
def CB4_3_1I1R15MassTerm : Ball := .exact 0
def CB4_3_1I1R15H : Ball := ⟨0, 0⟩
def CB4_3_1I1R16Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 3 1)) (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 1 (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 1) a : ℝ)) 16 a
def CB4_3_1I1R16Entropy : Ball := ⟨0, 0⟩
def CB4_3_1I1R16Mass : Ball := ⟨0, 0⟩
def CB4_3_1I1R16MassTerm : Ball := .exact 0
def CB4_3_1I1R16H : Ball := ⟨0, 0⟩
def CB4_3_1I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CB4_3_1I1R0H
  | 1 => CB4_3_1I1R1H
  | 2 => CB4_3_1I1R2H
  | 3 => CB4_3_1I1R3H
  | 4 => CB4_3_1I1R4H
  | 5 => CB4_3_1I1R5H
  | 6 => CB4_3_1I1R6H
  | 7 => CB4_3_1I1R7H
  | 8 => CB4_3_1I1R8H
  | 9 => CB4_3_1I1R9H
  | 10 => CB4_3_1I1R10H
  | 11 => CB4_3_1I1R11H
  | 12 => CB4_3_1I1R12H
  | 13 => CB4_3_1I1R13H
  | 14 => CB4_3_1I1R14H
  | 15 => CB4_3_1I1R15H
  | 16 => CB4_3_1I1R16H
  | _ => (.exact 0)
def CB4_3_1I1S0_3_1Value (a : Fin 6) : ℝ := (littleLaw (shape 4 3 1) (shape 0 3 1) ((stageBPriority (shape 4 3 1)) 1) a : ℝ)
def CB4_3_1I1S0_3_1E_4Log : Ball := .exact 0
def CB4_3_1I1S0_3_1E_4 : Ball := ⟨0, 0⟩
def CB4_3_1I1S0_3_1Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB4_3_1I1S0_3_1Entropy : Ball := ⟨0, 0⟩
def CB4_3_1I1S0_3_1Mass : Ball := ⟨1, 0⟩
def CB4_3_1I1S0_3_1MassTermLog : Ball := .exact 0
def CB4_3_1I1S0_3_1MassTerm : Ball := ⟨0, 0⟩
def CB4_3_1I1S0_3_1H : Ball := ⟨0, 0⟩
def CB4_3_1I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 3, 1 => CB4_3_1I1S0_3_1H
  | _, _, _ => (.exact 0)
def CB4_3_1I1Singleton : Ball := ⟨0, 0⟩
def CB4_3_1I1Group : Ball := ⟨(2917405570139503730793260650103 / 20000000000000000000000000000000), (135307097319 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB4_3_1I1H : Ball := ⟨(1019569187696828535959852786143 / 1250000000000000000000000000000), (363617711883 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB4_3_1I2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB4_3_1I2PairEntropy : Ball := ⟨(22010520911503647441395826369933 / 25000000000000000000000000000000), (29789141629 / 50000000000000000000000000000000)⟩
def CB4_3_1I2PairMass : Ball := ⟨(100000000000000000000000000000003 / 100000000000000000000000000000000), (13 / 20000000000000000000000000000000)⟩
def CB4_3_1I2PairMassTermLogWitness : LogWitness := ⟨0, 100000000000000000000000000000003, 100000000000000000000000000000000⟩
def CB4_3_1I2PairMassTermLog : Ball := ⟨(3 / 100000000000000000000000000000000), (21175823747 / 100000000000000000000000000000000)⟩
def CB4_3_1I2PairMassTerm : Ball := ⟨(-3 / 100000000000000000000000000000000), (5293955937 / 25000000000000000000000000000000)⟩
def CB4_3_1I2PairH : Ball := ⟨(17608416729202917953116661095947 / 20000000000000000000000000000000), (40377053503 / 50000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB4_3_1I2R0Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 3 1)) (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 2 (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 2) a : ℝ)) 0 a
def CB4_3_1I2R0Entropy : Ball := ⟨(66916637569092300013809787887 / 25000000000000000000000000000000), (46035727 / 50000000000000000000000000000000)⟩
def CB4_3_1I2R0Mass : Ball := ⟨(33445776876645910225502339149 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def CB4_3_1I2R0MassTermLogWitness : LogWitness := ⟨-12, 33445776876645910225502339149, 24414062500000000000000000000⟩
def CB4_3_1I2R0MassTermLog : Ball := ⟨(-160059998763713561144352850920053 / 20000000000000000000000000000000), (68821427717 / 25000000000000000000000000000000)⟩
def CB4_3_1I2R0MassTerm : Ball := ⟨(66916637569092300013809787887 / 25000000000000000000000000000000), (46035727 / 50000000000000000000000000000000)⟩
def CB4_3_1I2R0H : Ball := ⟨0, (46035727 / 25000000000000000000000000000000)⟩
def CB4_3_1I2R1Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 3 1)) (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 2 (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 2) a : ℝ)) 1 a
def CB4_3_1I2R1Entropy : Ball := ⟨(17883963881894316763402895444343 / 100000000000000000000000000000000), (869233559 / 12500000000000000000000000000000)⟩
def CB4_3_1I2R1Mass : Ball := ⟨(205241969884719280749621373729 / 3125000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
def CB4_3_1I2R1MassTermLogWitness : LogWitness := ⟨-4, 205241969884719280749621373729, 195312500000000000000000000000⟩
def CB4_3_1I2R1MassTermLog : Ball := ⟨(-13614999690928390286088220368213 / 5000000000000000000000000000000), (105879118597 / 100000000000000000000000000000000)⟩
def CB4_3_1I2R1MassTerm : Ball := ⟨(17883963881894316763402895444343 / 100000000000000000000000000000000), (869233559 / 12500000000000000000000000000000)⟩
def CB4_3_1I2R1H : Ball := ⟨0, (869233559 / 6250000000000000000000000000000)⟩
def CB4_3_1I2R2Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 3 1)) (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 2 (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 2) a : ℝ)) 2 a
def CB4_3_1I2R2Entropy : Ball := ⟨(37272794259826996477070636805221 / 100000000000000000000000000000000), (2695997489 / 10000000000000000000000000000000)⟩
def CB4_3_1I2R2Mass : Ball := ⟨(8421031573086763956728433893807 / 20000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
def CB4_3_1I2R2MassTermLogWitness : LogWitness := ⟨-2, 8421031573086763956728433893807, 5000000000000000000000000000000⟩
def CB4_3_1I2R2MassTermLog : Ball := ⟨(-86499993818567805721764445555273 / 100000000000000000000000000000000), (15881867771 / 25000000000000000000000000000000)⟩
def CB4_3_1I2R2MassTerm : Ball := ⟨(9105239737724617591812405821 / 25000000000000000000000000000), (13374171001 / 50000000000000000000000000000000)⟩
def CB4_3_1I2R2H : Ball := ⟨(851835308928526109821013521221 / 100000000000000000000000000000000), (13427079223 / 25000000000000000000000000000000)⟩
def CB4_3_1I2R3Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 3 1)) (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 2 (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 2) a : ℝ)) 3 a
def CB4_3_1I2R3Entropy : Ball := ⟨0, 0⟩
def CB4_3_1I2R3Mass : Ball := ⟨0, 0⟩
def CB4_3_1I2R3MassTerm : Ball := .exact 0
def CB4_3_1I2R3H : Ball := ⟨0, 0⟩
def CB4_3_1I2R4Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 3 1)) (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 2 (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 2) a : ℝ)) 4 a
def CB4_3_1I2R4Entropy : Ball := ⟨0, 0⟩
def CB4_3_1I2R4Mass : Ball := ⟨0, 0⟩
def CB4_3_1I2R4MassTerm : Ball := .exact 0
def CB4_3_1I2R4H : Ball := ⟨0, 0⟩
def CB4_3_1I2R5Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 3 1)) (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 2 (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 2) a : ℝ)) 5 a
def CB4_3_1I2R5Entropy : Ball := ⟨0, 0⟩
def CB4_3_1I2R5Mass : Ball := ⟨0, 0⟩
def CB4_3_1I2R5MassTerm : Ball := .exact 0
def CB4_3_1I2R5H : Ball := ⟨0, 0⟩
def CB4_3_1I2R6Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 3 1)) (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 2 (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 2) a : ℝ)) 6 a
def CB4_3_1I2R6Entropy : Ball := ⟨0, 0⟩
def CB4_3_1I2R6Mass : Ball := ⟨0, 0⟩
def CB4_3_1I2R6MassTerm : Ball := .exact 0
def CB4_3_1I2R6H : Ball := ⟨0, 0⟩
def CB4_3_1I2R7Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 3 1)) (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 2 (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 2) a : ℝ)) 7 a
def CB4_3_1I2R7Entropy : Ball := ⟨0, 0⟩
def CB4_3_1I2R7Mass : Ball := ⟨0, 0⟩
def CB4_3_1I2R7MassTerm : Ball := .exact 0
def CB4_3_1I2R7H : Ball := ⟨0, 0⟩
def CB4_3_1I2R8Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 3 1)) (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 2 (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 2) a : ℝ)) 8 a
def CB4_3_1I2R8Entropy : Ball := ⟨0, 0⟩
def CB4_3_1I2R8Mass : Ball := ⟨0, 0⟩
def CB4_3_1I2R8MassTerm : Ball := .exact 0
def CB4_3_1I2R8H : Ball := ⟨0, 0⟩
def CB4_3_1I2R9Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 3 1)) (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 2 (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 2) a : ℝ)) 9 a
def CB4_3_1I2R9Entropy : Ball := ⟨0, 0⟩
def CB4_3_1I2R9Mass : Ball := ⟨0, 0⟩
def CB4_3_1I2R9MassTerm : Ball := .exact 0
def CB4_3_1I2R9H : Ball := ⟨0, 0⟩
def CB4_3_1I2R10Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 3 1)) (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 2 (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 2) a : ℝ)) 10 a
def CB4_3_1I2R10Entropy : Ball := ⟨0, 0⟩
def CB4_3_1I2R10Mass : Ball := ⟨0, 0⟩
def CB4_3_1I2R10MassTerm : Ball := .exact 0
def CB4_3_1I2R10H : Ball := ⟨0, 0⟩
def CB4_3_1I2R11Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 3 1)) (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 2 (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 2) a : ℝ)) 11 a
def CB4_3_1I2R11Entropy : Ball := ⟨0, 0⟩
def CB4_3_1I2R11Mass : Ball := ⟨0, 0⟩
def CB4_3_1I2R11MassTerm : Ball := .exact 0
def CB4_3_1I2R11H : Ball := ⟨0, 0⟩
def CB4_3_1I2R12Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 3 1)) (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 2 (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 2) a : ℝ)) 12 a
def CB4_3_1I2R12Entropy : Ball := ⟨0, 0⟩
def CB4_3_1I2R12Mass : Ball := ⟨0, 0⟩
def CB4_3_1I2R12MassTerm : Ball := .exact 0
def CB4_3_1I2R12H : Ball := ⟨0, 0⟩
def CB4_3_1I2R13Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 3 1)) (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 2 (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 2) a : ℝ)) 13 a
def CB4_3_1I2R13Entropy : Ball := ⟨0, 0⟩
def CB4_3_1I2R13Mass : Ball := ⟨0, 0⟩
def CB4_3_1I2R13MassTerm : Ball := .exact 0
def CB4_3_1I2R13H : Ball := ⟨0, 0⟩
def CB4_3_1I2R14Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 3 1)) (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 2 (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 2) a : ℝ)) 14 a
def CB4_3_1I2R14Entropy : Ball := ⟨0, 0⟩
def CB4_3_1I2R14Mass : Ball := ⟨0, 0⟩
def CB4_3_1I2R14MassTerm : Ball := .exact 0
def CB4_3_1I2R14H : Ball := ⟨0, 0⟩
def CB4_3_1I2R15Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 3 1)) (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 2 (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 2) a : ℝ)) 15 a
def CB4_3_1I2R15Entropy : Ball := ⟨0, 0⟩
def CB4_3_1I2R15Mass : Ball := ⟨0, 0⟩
def CB4_3_1I2R15MassTerm : Ball := .exact 0
def CB4_3_1I2R15H : Ball := ⟨0, 0⟩
def CB4_3_1I2R16Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 3 1)) (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 2 (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 2) a : ℝ)) 16 a
def CB4_3_1I2R16Entropy : Ball := ⟨0, 0⟩
def CB4_3_1I2R16Mass : Ball := ⟨0, 0⟩
def CB4_3_1I2R16MassTerm : Ball := .exact 0
def CB4_3_1I2R16H : Ball := ⟨0, 0⟩
def CB4_3_1I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CB4_3_1I2R0H
  | 1 => CB4_3_1I2R1H
  | 2 => CB4_3_1I2R2H
  | 3 => CB4_3_1I2R3H
  | 4 => CB4_3_1I2R4H
  | 5 => CB4_3_1I2R5H
  | 6 => CB4_3_1I2R6H
  | 7 => CB4_3_1I2R7H
  | 8 => CB4_3_1I2R8H
  | 9 => CB4_3_1I2R9H
  | 10 => CB4_3_1I2R10H
  | 11 => CB4_3_1I2R11H
  | 12 => CB4_3_1I2R12H
  | 13 => CB4_3_1I2R13H
  | 14 => CB4_3_1I2R14H
  | 15 => CB4_3_1I2R15H
  | 16 => CB4_3_1I2R16H
  | _ => (.exact 0)
def CB4_3_1I2S1_3_0Value (a : Fin 6) : ℝ := (littleLaw (shape 4 3 1) (shape 1 3 0) ((stageBPriority (shape 4 3 1)) 2) a : ℝ)
def CB4_3_1I2S1_3_0E_1Log : Ball := .exact 0
def CB4_3_1I2S1_3_0E_1 : Ball := ⟨0, 0⟩
def CB4_3_1I2S1_3_0Terms (a : Fin 6) : Ball :=
  match a.val with
  | 1 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB4_3_1I2S1_3_0Entropy : Ball := ⟨0, 0⟩
def CB4_3_1I2S1_3_0Mass : Ball := ⟨1, 0⟩
def CB4_3_1I2S1_3_0MassTermLog : Ball := .exact 0
def CB4_3_1I2S1_3_0MassTerm : Ball := ⟨0, 0⟩
def CB4_3_1I2S1_3_0H : Ball := ⟨0, 0⟩
def CB4_3_1I2S2_2_0Value (a : Fin 6) : ℝ := (littleLaw (shape 4 3 1) (shape 2 2 0) ((stageBPriority (shape 4 3 1)) 2) a : ℝ)
def CB4_3_1I2S2_2_0E_2LogWitness : LogWitness := ⟨-1, 451979, 250000⟩
def CB4_3_1I2S2_2_0E_2Log : Ball := ⟨(-1009723798462591586934335088673 / 10000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def CB4_3_1I2S2_2_0E_2 : Ball := ⟨(9127479054106473657419876780867 / 100000000000000000000000000000000), (765682209 / 2000000000000000000000000000000)⟩
def CB4_3_1I2S2_2_0E_3LogWitness : LogWitness := ⟨-4, 48021, 31250⟩
def CB4_3_1I2S2_2_0E_3Log : Ball := ⟨(-234296968318952155799785664084377 / 100000000000000000000000000000000), (52939559207 / 50000000000000000000000000000000)⟩
def CB4_3_1I2S2_2_0E_3 : Ball := ⟨(2812793678911100368415376843749 / 12500000000000000000000000000000), (10168842291 / 100000000000000000000000000000000)⟩
def CB4_3_1I2S2_2_0Terms (a : Fin 6) : Ball :=
  match a.val with
  | 2 => ⟨(9127479054106473657419876780867 / 100000000000000000000000000000000), (765682209 / 2000000000000000000000000000000)⟩
  | 3 => ⟨(2812793678911100368415376843749 / 12500000000000000000000000000000), (10168842291 / 100000000000000000000000000000000)⟩
  | _ => (.exact 0)
def CB4_3_1I2S2_2_0Entropy : Ball := ⟨(31629828485395276604742891530859 / 100000000000000000000000000000000), (48452952741 / 100000000000000000000000000000000)⟩
def CB4_3_1I2S2_2_0Mass : Ball := ⟨1, 0⟩
def CB4_3_1I2S2_2_0MassTermLog : Ball := .exact 0
def CB4_3_1I2S2_2_0MassTerm : Ball := ⟨0, 0⟩
def CB4_3_1I2S2_2_0H : Ball := ⟨(31629828485395276604742891530859 / 100000000000000000000000000000000), (48452952741 / 100000000000000000000000000000000)⟩
def CB4_3_1I2S3_0_1Value (a : Fin 6) : ℝ := (littleLaw (shape 4 3 1) (shape 3 0 1) ((stageBPriority (shape 4 3 1)) 2) a : ℝ)
def CB4_3_1I2S3_0_1E_4Log : Ball := .exact 0
def CB4_3_1I2S3_0_1E_4 : Ball := ⟨0, 0⟩
def CB4_3_1I2S3_0_1Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB4_3_1I2S3_0_1Entropy : Ball := ⟨0, 0⟩
def CB4_3_1I2S3_0_1Mass : Ball := ⟨1, 0⟩
def CB4_3_1I2S3_0_1MassTermLog : Ball := .exact 0
def CB4_3_1I2S3_0_1MassTerm : Ball := ⟨0, 0⟩
def CB4_3_1I2S3_0_1H : Ball := ⟨0, 0⟩
def CB4_3_1I2S3_1_0Value (a : Fin 6) : ℝ := (littleLaw (shape 4 3 1) (shape 3 1 0) ((stageBPriority (shape 4 3 1)) 2) a : ℝ)
def CB4_3_1I2S3_1_0E_4Log : Ball := .exact 0
def CB4_3_1I2S3_1_0E_4 : Ball := ⟨0, 0⟩
def CB4_3_1I2S3_1_0Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB4_3_1I2S3_1_0Entropy : Ball := ⟨0, 0⟩
def CB4_3_1I2S3_1_0Mass : Ball := ⟨1, 0⟩
def CB4_3_1I2S3_1_0MassTermLog : Ball := .exact 0
def CB4_3_1I2S3_1_0MassTerm : Ball := ⟨0, 0⟩
def CB4_3_1I2S3_1_0H : Ball := ⟨0, 0⟩
def CB4_3_1I2S4_0_0Value (a : Fin 6) : ℝ := (littleLaw (shape 4 3 1) (shape 4 0 0) ((stageBPriority (shape 4 3 1)) 2) a : ℝ)
def CB4_3_1I2S4_0_0E_5Log : Ball := .exact 0
def CB4_3_1I2S4_0_0E_5 : Ball := ⟨0, 0⟩
def CB4_3_1I2S4_0_0Terms (a : Fin 6) : Ball :=
  match a.val with
  | 5 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB4_3_1I2S4_0_0Entropy : Ball := ⟨0, 0⟩
def CB4_3_1I2S4_0_0Mass : Ball := ⟨1, 0⟩
def CB4_3_1I2S4_0_0MassTermLog : Ball := .exact 0
def CB4_3_1I2S4_0_0MassTerm : Ball := ⟨0, 0⟩
def CB4_3_1I2S4_0_0H : Ball := ⟨0, 0⟩
def CB4_3_1I2Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 1, 3, 0 => CB4_3_1I2S1_3_0H
  | 2, 2, 0 => CB4_3_1I2S2_2_0H
  | 3, 0, 1 => CB4_3_1I2S3_0_1H
  | 3, 1, 0 => CB4_3_1I2S3_1_0H
  | 4, 0, 0 => CB4_3_1I2S4_0_0H
  | _, _, _ => (.exact 0)
def CB4_3_1I2Singleton : Ball := ⟨(6658894608170818068591068816867 / 50000000000000000000000000000000), (20401192247 / 100000000000000000000000000000000)⟩
def CB4_3_1I2Group : Ball := ⟨(2833924905054032449400630230991 / 20000000000000000000000000000000), (88201388991 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB4_3_1I2H : Ball := ⟨(2388113383818970610863080126793 / 4000000000000000000000000000000), (64289221247 / 25000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB5_1_2I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB5_1_2I0Value (a : Fin 17) : ℝ := marginal (below (shape 5 1 2)) (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) ((stageBPriority (shape 5 1 2)) 0) a
def CB5_1_2I0Entropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (21175823773 / 50000000000000000000000000000000)⟩
def CB5_1_2I0Mass : Ball := ⟨1, (53 / 50000000000000000000000000000000)⟩
def CB5_1_2I0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB5_1_2I0MassTermLog : Ball := ⟨0, (5293955947 / 25000000000000000000000000000000)⟩
def CB5_1_2I0MassTerm : Ball := ⟨0, (21175823789 / 100000000000000000000000000000000)⟩
def CB5_1_2I0H : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (12705494267 / 20000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB5_1_2I1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB5_1_2I1PairEntropy : Ball := ⟨(104111218085567555428709426956563 / 100000000000000000000000000000000), (3783178731 / 6250000000000000000000000000000)⟩
def CB5_1_2I1PairMass : Ball := ⟨1, (11 / 10000000000000000000000000000000)⟩
def CB5_1_2I1PairMassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB5_1_2I1PairMassTermLog : Ball := ⟨0, (1323488987 / 6250000000000000000000000000000)⟩
def CB5_1_2I1PairMassTerm : Ball := ⟨0, (21175823793 / 100000000000000000000000000000000)⟩
def CB5_1_2I1PairH : Ball := ⟨(104111218085567555428709426956563 / 100000000000000000000000000000000), (81706683489 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB5_1_2I1R0Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 1 2)) (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (stageBPriority (shape 5 1 2)) 1 (fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 1) a : ℝ)) 0 a
def CB5_1_2I1R0Entropy : Ball := ⟨(31208650321412316625707562012269 / 100000000000000000000000000000000), (15659961367 / 100000000000000000000000000000000)⟩
def CB5_1_2I1R0Mass : Ball := ⟨(18488019054449901590258895332411 / 100000000000000000000000000000000), (9 / 25000000000000000000000000000000)⟩
def CB5_1_2I1R0MassTermLogWitness : LogWitness := ⟨-3, 18488019054449901590258895332411, 12500000000000000000000000000000⟩
def CB5_1_2I1R0MassTermLog : Ball := ⟨(-168804728237775546533865029872577 / 100000000000000000000000000000000), (42351647463 / 50000000000000000000000000000000)⟩
def CB5_1_2I1R0MassTerm : Ball := ⟨(31208650321412316625707562012269 / 100000000000000000000000000000000), (15659961367 / 100000000000000000000000000000000)⟩
def CB5_1_2I1R0H : Ball := ⟨0, (15659961367 / 50000000000000000000000000000000)⟩
def CB5_1_2I1R1Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 1 2)) (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (stageBPriority (shape 5 1 2)) 1 (fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 1) a : ℝ)) 1 a
def CB5_1_2I1R1Entropy : Ball := ⟨(29095338750505488883321329985571 / 100000000000000000000000000000000), (13345843073 / 50000000000000000000000000000000)⟩
def CB5_1_2I1R1Mass : Ball := ⟨(31511980945550098409741104667589 / 50000000000000000000000000000000), (17 / 50000000000000000000000000000000)⟩
def CB5_1_2I1R1MassTermLogWitness : LogWitness := ⟨-1, 31511980945550098409741104667589, 25000000000000000000000000000000⟩
def CB5_1_2I1R1MassTermLog : Ball := ⟨(-9233103688650880947564362099801 / 20000000000000000000000000000000), (42351647419 / 100000000000000000000000000000000)⟩
def CB5_1_2I1R1MassTerm : Ball := ⟨(29095338750505488883321329985571 / 100000000000000000000000000000000), (13345843073 / 50000000000000000000000000000000)⟩
def CB5_1_2I1R1H : Ball := ⟨0, (13345843073 / 25000000000000000000000000000000)⟩
def CB5_1_2I1R2Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 1 2)) (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (stageBPriority (shape 5 1 2)) 1 (fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 1) a : ℝ)) 2 a
def CB5_1_2I1R2Entropy : Ball := ⟨(4688492458441379159086756060687 / 12500000000000000000000000000000), (676783471 / 4000000000000000000000000000000)⟩
def CB5_1_2I1R2Mass : Ball := ⟨(18488019054449901590258895332411 / 100000000000000000000000000000000), (19 / 50000000000000000000000000000000)⟩
def CB5_1_2I1R2MassTermLogWitness : LogWitness := ⟨-3, 18488019054449901590258895332411, 12500000000000000000000000000000⟩
def CB5_1_2I1R2MassTermLog : Ball := ⟨(-168804728237775546533865029872577 / 100000000000000000000000000000000), (84703294937 / 100000000000000000000000000000000)⟩
def CB5_1_2I1R2MassTerm : Ball := ⟨(31208650321412316625707562012269 / 100000000000000000000000000000000), (15659961373 / 100000000000000000000000000000000)⟩
def CB5_1_2I1R2H : Ball := ⟨(6299289346118716646986486473227 / 100000000000000000000000000000000), (8144887037 / 25000000000000000000000000000000)⟩
def CB5_1_2I1R3Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 1 2)) (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (stageBPriority (shape 5 1 2)) 1 (fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 1) a : ℝ)) 3 a
def CB5_1_2I1R3Entropy : Ball := ⟨0, 0⟩
def CB5_1_2I1R3Mass : Ball := ⟨0, 0⟩
def CB5_1_2I1R3MassTerm : Ball := .exact 0
def CB5_1_2I1R3H : Ball := ⟨0, 0⟩
def CB5_1_2I1R4Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 1 2)) (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (stageBPriority (shape 5 1 2)) 1 (fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 1) a : ℝ)) 4 a
def CB5_1_2I1R4Entropy : Ball := ⟨0, 0⟩
def CB5_1_2I1R4Mass : Ball := ⟨0, 0⟩
def CB5_1_2I1R4MassTerm : Ball := .exact 0
def CB5_1_2I1R4H : Ball := ⟨0, 0⟩
def CB5_1_2I1R5Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 1 2)) (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (stageBPriority (shape 5 1 2)) 1 (fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 1) a : ℝ)) 5 a
def CB5_1_2I1R5Entropy : Ball := ⟨0, 0⟩
def CB5_1_2I1R5Mass : Ball := ⟨0, 0⟩
def CB5_1_2I1R5MassTerm : Ball := .exact 0
def CB5_1_2I1R5H : Ball := ⟨0, 0⟩
def CB5_1_2I1R6Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 1 2)) (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (stageBPriority (shape 5 1 2)) 1 (fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 1) a : ℝ)) 6 a
def CB5_1_2I1R6Entropy : Ball := ⟨0, 0⟩
def CB5_1_2I1R6Mass : Ball := ⟨0, 0⟩
def CB5_1_2I1R6MassTerm : Ball := .exact 0
def CB5_1_2I1R6H : Ball := ⟨0, 0⟩
def CB5_1_2I1R7Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 1 2)) (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (stageBPriority (shape 5 1 2)) 1 (fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 1) a : ℝ)) 7 a
def CB5_1_2I1R7Entropy : Ball := ⟨0, 0⟩
def CB5_1_2I1R7Mass : Ball := ⟨0, 0⟩
def CB5_1_2I1R7MassTerm : Ball := .exact 0
def CB5_1_2I1R7H : Ball := ⟨0, 0⟩
def CB5_1_2I1R8Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 1 2)) (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (stageBPriority (shape 5 1 2)) 1 (fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 1) a : ℝ)) 8 a
def CB5_1_2I1R8Entropy : Ball := ⟨0, 0⟩
def CB5_1_2I1R8Mass : Ball := ⟨0, 0⟩
def CB5_1_2I1R8MassTerm : Ball := .exact 0
def CB5_1_2I1R8H : Ball := ⟨0, 0⟩
def CB5_1_2I1R9Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 1 2)) (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (stageBPriority (shape 5 1 2)) 1 (fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 1) a : ℝ)) 9 a
def CB5_1_2I1R9Entropy : Ball := ⟨0, 0⟩
def CB5_1_2I1R9Mass : Ball := ⟨0, 0⟩
def CB5_1_2I1R9MassTerm : Ball := .exact 0
def CB5_1_2I1R9H : Ball := ⟨0, 0⟩
def CB5_1_2I1R10Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 1 2)) (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (stageBPriority (shape 5 1 2)) 1 (fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 1) a : ℝ)) 10 a
def CB5_1_2I1R10Entropy : Ball := ⟨0, 0⟩
def CB5_1_2I1R10Mass : Ball := ⟨0, 0⟩
def CB5_1_2I1R10MassTerm : Ball := .exact 0
def CB5_1_2I1R10H : Ball := ⟨0, 0⟩
def CB5_1_2I1R11Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 1 2)) (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (stageBPriority (shape 5 1 2)) 1 (fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 1) a : ℝ)) 11 a
def CB5_1_2I1R11Entropy : Ball := ⟨0, 0⟩
def CB5_1_2I1R11Mass : Ball := ⟨0, 0⟩
def CB5_1_2I1R11MassTerm : Ball := .exact 0
def CB5_1_2I1R11H : Ball := ⟨0, 0⟩
def CB5_1_2I1R12Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 1 2)) (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (stageBPriority (shape 5 1 2)) 1 (fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 1) a : ℝ)) 12 a
def CB5_1_2I1R12Entropy : Ball := ⟨0, 0⟩
def CB5_1_2I1R12Mass : Ball := ⟨0, 0⟩
def CB5_1_2I1R12MassTerm : Ball := .exact 0
def CB5_1_2I1R12H : Ball := ⟨0, 0⟩
def CB5_1_2I1R13Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 1 2)) (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (stageBPriority (shape 5 1 2)) 1 (fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 1) a : ℝ)) 13 a
def CB5_1_2I1R13Entropy : Ball := ⟨0, 0⟩
def CB5_1_2I1R13Mass : Ball := ⟨0, 0⟩
def CB5_1_2I1R13MassTerm : Ball := .exact 0
def CB5_1_2I1R13H : Ball := ⟨0, 0⟩
def CB5_1_2I1R14Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 1 2)) (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (stageBPriority (shape 5 1 2)) 1 (fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 1) a : ℝ)) 14 a
def CB5_1_2I1R14Entropy : Ball := ⟨0, 0⟩
def CB5_1_2I1R14Mass : Ball := ⟨0, 0⟩
def CB5_1_2I1R14MassTerm : Ball := .exact 0
def CB5_1_2I1R14H : Ball := ⟨0, 0⟩
def CB5_1_2I1R15Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 1 2)) (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (stageBPriority (shape 5 1 2)) 1 (fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 1) a : ℝ)) 15 a
def CB5_1_2I1R15Entropy : Ball := ⟨0, 0⟩
def CB5_1_2I1R15Mass : Ball := ⟨0, 0⟩
def CB5_1_2I1R15MassTerm : Ball := .exact 0
def CB5_1_2I1R15H : Ball := ⟨0, 0⟩
def CB5_1_2I1R16Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 1 2)) (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (stageBPriority (shape 5 1 2)) 1 (fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 1) a : ℝ)) 16 a
def CB5_1_2I1R16Entropy : Ball := ⟨0, 0⟩
def CB5_1_2I1R16Mass : Ball := ⟨0, 0⟩
def CB5_1_2I1R16MassTerm : Ball := .exact 0
def CB5_1_2I1R16H : Ball := ⟨0, 0⟩
def CB5_1_2I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CB5_1_2I1R0H
  | 1 => CB5_1_2I1R1H
  | 2 => CB5_1_2I1R2H
  | 3 => CB5_1_2I1R3H
  | 4 => CB5_1_2I1R4H
  | 5 => CB5_1_2I1R5H
  | 6 => CB5_1_2I1R6H
  | 7 => CB5_1_2I1R7H
  | 8 => CB5_1_2I1R8H
  | 9 => CB5_1_2I1R9H
  | 10 => CB5_1_2I1R10H
  | 11 => CB5_1_2I1R11H
  | 12 => CB5_1_2I1R12H
  | 13 => CB5_1_2I1R13H
  | 14 => CB5_1_2I1R14H
  | 15 => CB5_1_2I1R15H
  | 16 => CB5_1_2I1R16H
  | _ => (.exact 0)
def CB5_1_2I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | _, _, _ => (.exact 0)
def CB5_1_2I1Singleton : Ball := ⟨0, 0⟩
def CB5_1_2I1Group : Ball := ⟨(6299289346118716646986486473227 / 100000000000000000000000000000000), (58641421587 / 50000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB5_1_2I1H : Ball := ⟨(91512639393330122134736454010109 / 100000000000000000000000000000000), (316272369837 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB5_1_2I2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB5_1_2I2PairEntropy : Ball := ⟨(23509605587503986644313777493071 / 25000000000000000000000000000000), (8608226989 / 12500000000000000000000000000000)⟩
def CB5_1_2I2PairMass : Ball := ⟨1, (11 / 10000000000000000000000000000000)⟩
def CB5_1_2I2PairMassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB5_1_2I2PairMassTermLog : Ball := ⟨0, (1323488987 / 6250000000000000000000000000000)⟩
def CB5_1_2I2PairMassTerm : Ball := ⟨0, (21175823793 / 100000000000000000000000000000000)⟩
def CB5_1_2I2PairH : Ball := ⟨(23509605587503986644313777493071 / 25000000000000000000000000000000), (18008327941 / 20000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB5_1_2I2R0Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 1 2)) (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (stageBPriority (shape 5 1 2)) 2 (fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 2) a : ℝ)) 0 a
def CB5_1_2I2R0Entropy : Ball := ⟨0, 0⟩
def CB5_1_2I2R0Mass : Ball := ⟨0, 0⟩
def CB5_1_2I2R0MassTerm : Ball := .exact 0
def CB5_1_2I2R0H : Ball := ⟨0, 0⟩
def CB5_1_2I2R1Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 1 2)) (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (stageBPriority (shape 5 1 2)) 2 (fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 2) a : ℝ)) 1 a
def CB5_1_2I2R1Entropy : Ball := ⟨(3533519351837877097933777673677 / 100000000000000000000000000000000), (1363128417 / 100000000000000000000000000000000)⟩
def CB5_1_2I2R1Mass : Ball := ⟨(715243539925161855344559597823 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def CB5_1_2I2R1MassTermLogWitness : LogWitness := ⟨-8, 715243539925161855344559597823, 390625000000000000000000000000⟩
def CB5_1_2I2R1MassTermLog : Ball := ⟨(-247015118249624467839772444506523 / 50000000000000000000000000000000), (95291206783 / 50000000000000000000000000000000)⟩
def CB5_1_2I2R1MassTerm : Ball := ⟨(3533519351837877097933777673677 / 100000000000000000000000000000000), (1363128417 / 100000000000000000000000000000000)⟩
def CB5_1_2I2R1H : Ball := ⟨0, (1363128417 / 50000000000000000000000000000000)⟩
def CB5_1_2I2R2Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 1 2)) (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (stageBPriority (shape 5 1 2)) 2 (fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 2) a : ℝ)) 2 a
def CB5_1_2I2R2Entropy : Ball := ⟨(37209439399359607978313598813761 / 100000000000000000000000000000000), (1011577537 / 5000000000000000000000000000000)⟩
def CB5_1_2I2R2Mass : Ball := ⟨(31511980945550098409741104667589 / 100000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
def CB5_1_2I2R2MassTermLogWitness : LogWitness := ⟨-2, 31511980945550098409741104667589, 25000000000000000000000000000000⟩
def CB5_1_2I2R2MassTermLog : Ball := ⟨(-23096047299849787135909000709867 / 20000000000000000000000000000000), (12705494221 / 20000000000000000000000000000000)⟩
def CB5_1_2I2R2MassTerm : Ball := ⟨(36390110121519514624001162896127 / 100000000000000000000000000000000), (20018764611 / 100000000000000000000000000000000)⟩
def CB5_1_2I2R2H : Ball := ⟨(409664638920046677156217958817 / 50000000000000000000000000000000), (40250315351 / 100000000000000000000000000000000)⟩
def CB5_1_2I2R3Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 1 2)) (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (stageBPriority (shape 5 1 2)) 2 (fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 2) a : ℝ)) 3 a
def CB5_1_2I2R3Entropy : Ball := ⟨0, 0⟩
def CB5_1_2I2R3Mass : Ball := ⟨0, 0⟩
def CB5_1_2I2R3MassTerm : Ball := .exact 0
def CB5_1_2I2R3H : Ball := ⟨0, 0⟩
def CB5_1_2I2R4Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 1 2)) (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (stageBPriority (shape 5 1 2)) 2 (fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 2) a : ℝ)) 4 a
def CB5_1_2I2R4Entropy : Ball := ⟨0, 0⟩
def CB5_1_2I2R4Mass : Ball := ⟨0, 0⟩
def CB5_1_2I2R4MassTerm : Ball := .exact 0
def CB5_1_2I2R4H : Ball := ⟨0, 0⟩
def CB5_1_2I2R5Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 1 2)) (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (stageBPriority (shape 5 1 2)) 2 (fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 2) a : ℝ)) 5 a
def CB5_1_2I2R5Entropy : Ball := ⟨0, 0⟩
def CB5_1_2I2R5Mass : Ball := ⟨0, 0⟩
def CB5_1_2I2R5MassTerm : Ball := .exact 0
def CB5_1_2I2R5H : Ball := ⟨0, 0⟩
def CB5_1_2I2R6Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 1 2)) (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (stageBPriority (shape 5 1 2)) 2 (fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 2) a : ℝ)) 6 a
def CB5_1_2I2R6Entropy : Ball := ⟨0, 0⟩
def CB5_1_2I2R6Mass : Ball := ⟨0, 0⟩
def CB5_1_2I2R6MassTerm : Ball := .exact 0
def CB5_1_2I2R6H : Ball := ⟨0, 0⟩
def CB5_1_2I2R7Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 1 2)) (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (stageBPriority (shape 5 1 2)) 2 (fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 2) a : ℝ)) 7 a
def CB5_1_2I2R7Entropy : Ball := ⟨0, 0⟩
def CB5_1_2I2R7Mass : Ball := ⟨0, 0⟩
def CB5_1_2I2R7MassTerm : Ball := .exact 0
def CB5_1_2I2R7H : Ball := ⟨0, 0⟩
def CB5_1_2I2R8Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 1 2)) (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (stageBPriority (shape 5 1 2)) 2 (fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 2) a : ℝ)) 8 a
def CB5_1_2I2R8Entropy : Ball := ⟨0, 0⟩
def CB5_1_2I2R8Mass : Ball := ⟨0, 0⟩
def CB5_1_2I2R8MassTerm : Ball := .exact 0
def CB5_1_2I2R8H : Ball := ⟨0, 0⟩
def CB5_1_2I2R9Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 1 2)) (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (stageBPriority (shape 5 1 2)) 2 (fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 2) a : ℝ)) 9 a
def CB5_1_2I2R9Entropy : Ball := ⟨0, 0⟩
def CB5_1_2I2R9Mass : Ball := ⟨0, 0⟩
def CB5_1_2I2R9MassTerm : Ball := .exact 0
def CB5_1_2I2R9H : Ball := ⟨0, 0⟩
def CB5_1_2I2R10Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 1 2)) (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (stageBPriority (shape 5 1 2)) 2 (fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 2) a : ℝ)) 10 a
def CB5_1_2I2R10Entropy : Ball := ⟨0, 0⟩
def CB5_1_2I2R10Mass : Ball := ⟨0, 0⟩
def CB5_1_2I2R10MassTerm : Ball := .exact 0
def CB5_1_2I2R10H : Ball := ⟨0, 0⟩
def CB5_1_2I2R11Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 1 2)) (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (stageBPriority (shape 5 1 2)) 2 (fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 2) a : ℝ)) 11 a
def CB5_1_2I2R11Entropy : Ball := ⟨0, 0⟩
def CB5_1_2I2R11Mass : Ball := ⟨0, 0⟩
def CB5_1_2I2R11MassTerm : Ball := .exact 0
def CB5_1_2I2R11H : Ball := ⟨0, 0⟩
def CB5_1_2I2R12Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 1 2)) (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (stageBPriority (shape 5 1 2)) 2 (fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 2) a : ℝ)) 12 a
def CB5_1_2I2R12Entropy : Ball := ⟨0, 0⟩
def CB5_1_2I2R12Mass : Ball := ⟨0, 0⟩
def CB5_1_2I2R12MassTerm : Ball := .exact 0
def CB5_1_2I2R12H : Ball := ⟨0, 0⟩
def CB5_1_2I2R13Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 1 2)) (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (stageBPriority (shape 5 1 2)) 2 (fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 2) a : ℝ)) 13 a
def CB5_1_2I2R13Entropy : Ball := ⟨0, 0⟩
def CB5_1_2I2R13Mass : Ball := ⟨0, 0⟩
def CB5_1_2I2R13MassTerm : Ball := .exact 0
def CB5_1_2I2R13H : Ball := ⟨0, 0⟩
def CB5_1_2I2R14Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 1 2)) (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (stageBPriority (shape 5 1 2)) 2 (fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 2) a : ℝ)) 14 a
def CB5_1_2I2R14Entropy : Ball := ⟨0, 0⟩
def CB5_1_2I2R14Mass : Ball := ⟨0, 0⟩
def CB5_1_2I2R14MassTerm : Ball := .exact 0
def CB5_1_2I2R14H : Ball := ⟨0, 0⟩
def CB5_1_2I2R15Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 1 2)) (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (stageBPriority (shape 5 1 2)) 2 (fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 2) a : ℝ)) 15 a
def CB5_1_2I2R15Entropy : Ball := ⟨0, 0⟩
def CB5_1_2I2R15Mass : Ball := ⟨0, 0⟩
def CB5_1_2I2R15MassTerm : Ball := .exact 0
def CB5_1_2I2R15H : Ball := ⟨0, 0⟩
def CB5_1_2I2R16Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 1 2)) (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (stageBPriority (shape 5 1 2)) 2 (fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 2) a : ℝ)) 16 a
def CB5_1_2I2R16Entropy : Ball := ⟨0, 0⟩
def CB5_1_2I2R16Mass : Ball := ⟨0, 0⟩
def CB5_1_2I2R16MassTerm : Ball := .exact 0
def CB5_1_2I2R16H : Ball := ⟨0, 0⟩
def CB5_1_2I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CB5_1_2I2R0H
  | 1 => CB5_1_2I2R1H
  | 2 => CB5_1_2I2R2H
  | 3 => CB5_1_2I2R3H
  | 4 => CB5_1_2I2R4H
  | 5 => CB5_1_2I2R5H
  | 6 => CB5_1_2I2R6H
  | 7 => CB5_1_2I2R7H
  | 8 => CB5_1_2I2R8H
  | 9 => CB5_1_2I2R9H
  | 10 => CB5_1_2I2R10H
  | 11 => CB5_1_2I2R11H
  | 12 => CB5_1_2I2R12H
  | 13 => CB5_1_2I2R13H
  | 14 => CB5_1_2I2R14H
  | 15 => CB5_1_2I2R15H
  | 16 => CB5_1_2I2R16H
  | _ => (.exact 0)
def CB5_1_2I2S2_0_2Value (a : Fin 6) : ℝ := (littleLaw (shape 5 1 2) (shape 2 0 2) ((stageBPriority (shape 5 1 2)) 2) a : ℝ)
def CB5_1_2I2S2_0_2E_2LogWitness : LogWitness := ⟨-1, 55633, 31250⟩
def CB5_1_2I2S2_0_2E_2Log : Ball := ⟨(-2327800127447388996729312677817 / 20000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def CB5_1_2I2S2_0_2E_2 : Ball := ⟨(10360200359222447364403348176399 / 100000000000000000000000000000000), (1178074599 / 3125000000000000000000000000000)⟩
def CB5_1_2I2S2_0_2E_3LogWitness : LogWitness := ⟨-4, 27468, 15625⟩
def CB5_1_2I2S2_0_2E_3Log : Ball := ⟨(-22084392271038164781658598089709 / 10000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
def CB5_1_2I2S2_0_2E_3 : Ball := ⟨(38823301561656083854246295829 / 160000000000000000000000000000), (11633150499 / 100000000000000000000000000000000)⟩
def CB5_1_2I2S2_0_2Terms (a : Fin 6) : Ball :=
  match a.val with
  | 2 => ⟨(10360200359222447364403348176399 / 100000000000000000000000000000000), (1178074599 / 3125000000000000000000000000000)⟩
  | 3 => ⟨(38823301561656083854246295829 / 160000000000000000000000000000), (11633150499 / 100000000000000000000000000000000)⟩
  | _ => (.exact 0)
def CB5_1_2I2S2_0_2Entropy : Ball := ⟨(8656190958814374943326820767381 / 25000000000000000000000000000000), (49331537667 / 100000000000000000000000000000000)⟩
def CB5_1_2I2S2_0_2Mass : Ball := ⟨1, 0⟩
def CB5_1_2I2S2_0_2MassTermLog : Ball := .exact 0
def CB5_1_2I2S2_0_2MassTerm : Ball := ⟨0, 0⟩
def CB5_1_2I2S2_0_2H : Ball := ⟨(8656190958814374943326820767381 / 25000000000000000000000000000000), (49331537667 / 100000000000000000000000000000000)⟩
def CB5_1_2I2S3_0_1Value (a : Fin 6) : ℝ := (littleLaw (shape 5 1 2) (shape 3 0 1) ((stageBPriority (shape 5 1 2)) 2) a : ℝ)
def CB5_1_2I2S3_0_1E_4Log : Ball := .exact 0
def CB5_1_2I2S3_0_1E_4 : Ball := ⟨0, 0⟩
def CB5_1_2I2S3_0_1Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB5_1_2I2S3_0_1Entropy : Ball := ⟨0, 0⟩
def CB5_1_2I2S3_0_1Mass : Ball := ⟨1, 0⟩
def CB5_1_2I2S3_0_1MassTermLog : Ball := .exact 0
def CB5_1_2I2S3_0_1MassTerm : Ball := ⟨0, 0⟩
def CB5_1_2I2S3_0_1H : Ball := ⟨0, 0⟩
def CB5_1_2I2S3_1_0Value (a : Fin 6) : ℝ := (littleLaw (shape 5 1 2) (shape 3 1 0) ((stageBPriority (shape 5 1 2)) 2) a : ℝ)
def CB5_1_2I2S3_1_0E_4Log : Ball := .exact 0
def CB5_1_2I2S3_1_0E_4 : Ball := ⟨0, 0⟩
def CB5_1_2I2S3_1_0Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB5_1_2I2S3_1_0Entropy : Ball := ⟨0, 0⟩
def CB5_1_2I2S3_1_0Mass : Ball := ⟨1, 0⟩
def CB5_1_2I2S3_1_0MassTermLog : Ball := .exact 0
def CB5_1_2I2S3_1_0MassTerm : Ball := ⟨0, 0⟩
def CB5_1_2I2S3_1_0H : Ball := ⟨0, 0⟩
def CB5_1_2I2S4_0_0Value (a : Fin 6) : ℝ := (littleLaw (shape 5 1 2) (shape 4 0 0) ((stageBPriority (shape 5 1 2)) 2) a : ℝ)
def CB5_1_2I2S4_0_0E_5Log : Ball := .exact 0
def CB5_1_2I2S4_0_0E_5 : Ball := ⟨0, 0⟩
def CB5_1_2I2S4_0_0Terms (a : Fin 6) : Ball :=
  match a.val with
  | 5 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB5_1_2I2S4_0_0Entropy : Ball := ⟨0, 0⟩
def CB5_1_2I2S4_0_0Mass : Ball := ⟨1, 0⟩
def CB5_1_2I2S4_0_0MassTermLog : Ball := .exact 0
def CB5_1_2I2S4_0_0MassTerm : Ball := ⟨0, 0⟩
def CB5_1_2I2S4_0_0H : Ball := ⟨0, 0⟩
def CB5_1_2I2Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 2, 0, 2 => CB5_1_2I2S2_0_2H
  | 3, 0, 1 => CB5_1_2I2S3_0_1H
  | 3, 1, 0 => CB5_1_2I2S3_1_0H
  | 4, 0, 0 => CB5_1_2I2S4_0_0H
  | _, _, _ => (.exact 0)
def CB5_1_2I2Singleton : Ball := ⟨(6153781548874662112522807304647 / 100000000000000000000000000000000), (8767583459 / 100000000000000000000000000000000)⟩
def CB5_1_2I2Group : Ball := ⟨(6973110826714755466835243222281 / 100000000000000000000000000000000), (12936038911 / 25000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB5_1_2I2H : Ball := ⟨(40046100348293217821792311763861 / 50000000000000000000000000000000), (193529950993 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB5_2_1I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB5_2_1I0Value (a : Fin 17) : ℝ := marginal (below (shape 5 2 1)) (fun u => (stageBLaw (shape 5 2 1) u : ℝ)) ((stageBPriority (shape 5 2 1)) 0) a
def CB5_2_1I0Entropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (21175823773 / 50000000000000000000000000000000)⟩
def CB5_2_1I0Mass : Ball := ⟨1, (53 / 50000000000000000000000000000000)⟩
def CB5_2_1I0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB5_2_1I0MassTermLog : Ball := ⟨0, (5293955947 / 25000000000000000000000000000000)⟩
def CB5_2_1I0MassTerm : Ball := ⟨0, (21175823789 / 100000000000000000000000000000000)⟩
def CB5_2_1I0H : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (12705494267 / 20000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB5_2_1I1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB5_2_1I1PairEntropy : Ball := ⟨(26033847282104103121698443482011 / 25000000000000000000000000000000), (60538191037 / 100000000000000000000000000000000)⟩
def CB5_2_1I1PairMass : Ball := ⟨1, (27 / 25000000000000000000000000000000)⟩
def CB5_2_1I1PairMassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB5_2_1I1PairMassTermLog : Ball := ⟨0, (2117582379 / 10000000000000000000000000000000)⟩
def CB5_2_1I1PairMassTerm : Ball := ⟨0, (21175823791 / 100000000000000000000000000000000)⟩
def CB5_2_1I1PairH : Ball := ⟨(26033847282104103121698443482011 / 25000000000000000000000000000000), (20428503707 / 25000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB5_2_1I1R0Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 2 1)) (fun u => (stageBLaw (shape 5 2 1) u : ℝ)) (stageBPriority (shape 5 2 1)) 1 (fun u a => (littleLaw (shape 5 2 1) u ((stageBPriority (shape 5 2 1)) 1) a : ℝ)) 0 a
def CB5_2_1I1R0Entropy : Ball := ⟨(15604971828411725998343746085051 / 50000000000000000000000000000000), (15661553669 / 100000000000000000000000000000000)⟩
def CB5_2_1I1R0Mass : Ball := ⟨(1848989891214686729494209052139 / 10000000000000000000000000000000), (9 / 25000000000000000000000000000000)⟩
def CB5_2_1I1R0MassTermLogWitness : LogWitness := ⟨-3, 1848989891214686729494209052139, 1250000000000000000000000000000⟩
def CB5_2_1I1R0MassTermLog : Ball := ⟨(-4219864019418759598795757864871 / 2500000000000000000000000000000), (42351647463 / 50000000000000000000000000000000)⟩
def CB5_2_1I1R0MassTerm : Ball := ⟨(15604971828411725998343746085051 / 50000000000000000000000000000000), (15661553669 / 100000000000000000000000000000000)⟩
def CB5_2_1I1R0H : Ball := ⟨0, (15661553669 / 50000000000000000000000000000000)⟩
def CB5_2_1I1R1Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 2 1)) (fun u => (stageBLaw (shape 5 2 1) u : ℝ)) (stageBPriority (shape 5 2 1)) 1 (fun u a => (littleLaw (shape 5 2 1) u ((stageBPriority (shape 5 2 1)) 1) a : ℝ)) 1 a
def CB5_2_1I1R1Entropy : Ball := ⟨(363717033270625690470714504197 / 1250000000000000000000000000000), (5338018769 / 20000000000000000000000000000000)⟩
def CB5_2_1I1R1Mass : Ball := ⟨(3151010108785313270505790947861 / 5000000000000000000000000000000), (17 / 50000000000000000000000000000000)⟩
def CB5_2_1I1R1MassTermLogWitness : LogWitness := ⟨-1, 3151010108785313270505790947861, 2500000000000000000000000000000⟩
def CB5_2_1I1R1MassTermLog : Ball := ⟨(-1442858879826140153114781181427 / 3125000000000000000000000000000), (42351647419 / 100000000000000000000000000000000)⟩
def CB5_2_1I1R1MassTerm : Ball := ⟨(363717033270625690470714504197 / 1250000000000000000000000000000), (5338018769 / 20000000000000000000000000000000)⟩
def CB5_2_1I1R1H : Ball := ⟨0, (5338018769 / 10000000000000000000000000000000)⟩
def CB5_2_1I1R2Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 2 1)) (fun u => (stageBLaw (shape 5 2 1) u : ℝ)) (stageBPriority (shape 5 2 1)) 1 (fun u a => (littleLaw (shape 5 2 1) u ((stageBPriority (shape 5 2 1)) 1) a : ℝ)) 2 a
def CB5_2_1I1R2Entropy : Ball := ⟨(18759506616691589312284153398071 / 50000000000000000000000000000000), (4231012149 / 25000000000000000000000000000000)⟩
def CB5_2_1I1R2Mass : Ball := ⟨(1848989891214686729494209052139 / 10000000000000000000000000000000), (37 / 100000000000000000000000000000000)⟩
def CB5_2_1I1R2MassTermLogWitness : LogWitness := ⟨-3, 1848989891214686729494209052139, 1250000000000000000000000000000⟩
def CB5_2_1I1R2MassTermLog : Ball := ⟨(-4219864019418759598795757864871 / 2500000000000000000000000000000), (84703294931 / 100000000000000000000000000000000)⟩
def CB5_2_1I1R2MassTerm : Ball := ⟨(15604971828411725998343746085051 / 50000000000000000000000000000000), (15661553671 / 100000000000000000000000000000000)⟩
def CB5_2_1I1R2H : Ball := ⟨(157726739413993165697020365651 / 2500000000000000000000000000000), (32585602267 / 100000000000000000000000000000000)⟩
def CB5_2_1I1R3Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 2 1)) (fun u => (stageBLaw (shape 5 2 1) u : ℝ)) (stageBPriority (shape 5 2 1)) 1 (fun u a => (littleLaw (shape 5 2 1) u ((stageBPriority (shape 5 2 1)) 1) a : ℝ)) 3 a
def CB5_2_1I1R3Entropy : Ball := ⟨0, 0⟩
def CB5_2_1I1R3Mass : Ball := ⟨0, 0⟩
def CB5_2_1I1R3MassTerm : Ball := .exact 0
def CB5_2_1I1R3H : Ball := ⟨0, 0⟩
def CB5_2_1I1R4Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 2 1)) (fun u => (stageBLaw (shape 5 2 1) u : ℝ)) (stageBPriority (shape 5 2 1)) 1 (fun u a => (littleLaw (shape 5 2 1) u ((stageBPriority (shape 5 2 1)) 1) a : ℝ)) 4 a
def CB5_2_1I1R4Entropy : Ball := ⟨0, 0⟩
def CB5_2_1I1R4Mass : Ball := ⟨0, 0⟩
def CB5_2_1I1R4MassTerm : Ball := .exact 0
def CB5_2_1I1R4H : Ball := ⟨0, 0⟩
def CB5_2_1I1R5Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 2 1)) (fun u => (stageBLaw (shape 5 2 1) u : ℝ)) (stageBPriority (shape 5 2 1)) 1 (fun u a => (littleLaw (shape 5 2 1) u ((stageBPriority (shape 5 2 1)) 1) a : ℝ)) 5 a
def CB5_2_1I1R5Entropy : Ball := ⟨0, 0⟩
def CB5_2_1I1R5Mass : Ball := ⟨0, 0⟩
def CB5_2_1I1R5MassTerm : Ball := .exact 0
def CB5_2_1I1R5H : Ball := ⟨0, 0⟩
def CB5_2_1I1R6Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 2 1)) (fun u => (stageBLaw (shape 5 2 1) u : ℝ)) (stageBPriority (shape 5 2 1)) 1 (fun u a => (littleLaw (shape 5 2 1) u ((stageBPriority (shape 5 2 1)) 1) a : ℝ)) 6 a
def CB5_2_1I1R6Entropy : Ball := ⟨0, 0⟩
def CB5_2_1I1R6Mass : Ball := ⟨0, 0⟩
def CB5_2_1I1R6MassTerm : Ball := .exact 0
def CB5_2_1I1R6H : Ball := ⟨0, 0⟩
def CB5_2_1I1R7Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 2 1)) (fun u => (stageBLaw (shape 5 2 1) u : ℝ)) (stageBPriority (shape 5 2 1)) 1 (fun u a => (littleLaw (shape 5 2 1) u ((stageBPriority (shape 5 2 1)) 1) a : ℝ)) 7 a
def CB5_2_1I1R7Entropy : Ball := ⟨0, 0⟩
def CB5_2_1I1R7Mass : Ball := ⟨0, 0⟩
def CB5_2_1I1R7MassTerm : Ball := .exact 0
def CB5_2_1I1R7H : Ball := ⟨0, 0⟩
def CB5_2_1I1R8Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 2 1)) (fun u => (stageBLaw (shape 5 2 1) u : ℝ)) (stageBPriority (shape 5 2 1)) 1 (fun u a => (littleLaw (shape 5 2 1) u ((stageBPriority (shape 5 2 1)) 1) a : ℝ)) 8 a
def CB5_2_1I1R8Entropy : Ball := ⟨0, 0⟩
def CB5_2_1I1R8Mass : Ball := ⟨0, 0⟩
def CB5_2_1I1R8MassTerm : Ball := .exact 0
def CB5_2_1I1R8H : Ball := ⟨0, 0⟩
def CB5_2_1I1R9Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 2 1)) (fun u => (stageBLaw (shape 5 2 1) u : ℝ)) (stageBPriority (shape 5 2 1)) 1 (fun u a => (littleLaw (shape 5 2 1) u ((stageBPriority (shape 5 2 1)) 1) a : ℝ)) 9 a
def CB5_2_1I1R9Entropy : Ball := ⟨0, 0⟩
def CB5_2_1I1R9Mass : Ball := ⟨0, 0⟩
def CB5_2_1I1R9MassTerm : Ball := .exact 0
def CB5_2_1I1R9H : Ball := ⟨0, 0⟩
def CB5_2_1I1R10Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 2 1)) (fun u => (stageBLaw (shape 5 2 1) u : ℝ)) (stageBPriority (shape 5 2 1)) 1 (fun u a => (littleLaw (shape 5 2 1) u ((stageBPriority (shape 5 2 1)) 1) a : ℝ)) 10 a
def CB5_2_1I1R10Entropy : Ball := ⟨0, 0⟩
def CB5_2_1I1R10Mass : Ball := ⟨0, 0⟩
def CB5_2_1I1R10MassTerm : Ball := .exact 0
def CB5_2_1I1R10H : Ball := ⟨0, 0⟩
def CB5_2_1I1R11Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 2 1)) (fun u => (stageBLaw (shape 5 2 1) u : ℝ)) (stageBPriority (shape 5 2 1)) 1 (fun u a => (littleLaw (shape 5 2 1) u ((stageBPriority (shape 5 2 1)) 1) a : ℝ)) 11 a
def CB5_2_1I1R11Entropy : Ball := ⟨0, 0⟩
def CB5_2_1I1R11Mass : Ball := ⟨0, 0⟩
def CB5_2_1I1R11MassTerm : Ball := .exact 0
def CB5_2_1I1R11H : Ball := ⟨0, 0⟩
def CB5_2_1I1R12Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 2 1)) (fun u => (stageBLaw (shape 5 2 1) u : ℝ)) (stageBPriority (shape 5 2 1)) 1 (fun u a => (littleLaw (shape 5 2 1) u ((stageBPriority (shape 5 2 1)) 1) a : ℝ)) 12 a
def CB5_2_1I1R12Entropy : Ball := ⟨0, 0⟩
def CB5_2_1I1R12Mass : Ball := ⟨0, 0⟩
def CB5_2_1I1R12MassTerm : Ball := .exact 0
def CB5_2_1I1R12H : Ball := ⟨0, 0⟩
def CB5_2_1I1R13Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 2 1)) (fun u => (stageBLaw (shape 5 2 1) u : ℝ)) (stageBPriority (shape 5 2 1)) 1 (fun u a => (littleLaw (shape 5 2 1) u ((stageBPriority (shape 5 2 1)) 1) a : ℝ)) 13 a
def CB5_2_1I1R13Entropy : Ball := ⟨0, 0⟩
def CB5_2_1I1R13Mass : Ball := ⟨0, 0⟩
def CB5_2_1I1R13MassTerm : Ball := .exact 0
def CB5_2_1I1R13H : Ball := ⟨0, 0⟩
def CB5_2_1I1R14Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 2 1)) (fun u => (stageBLaw (shape 5 2 1) u : ℝ)) (stageBPriority (shape 5 2 1)) 1 (fun u a => (littleLaw (shape 5 2 1) u ((stageBPriority (shape 5 2 1)) 1) a : ℝ)) 14 a
def CB5_2_1I1R14Entropy : Ball := ⟨0, 0⟩
def CB5_2_1I1R14Mass : Ball := ⟨0, 0⟩
def CB5_2_1I1R14MassTerm : Ball := .exact 0
def CB5_2_1I1R14H : Ball := ⟨0, 0⟩
def CB5_2_1I1R15Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 2 1)) (fun u => (stageBLaw (shape 5 2 1) u : ℝ)) (stageBPriority (shape 5 2 1)) 1 (fun u a => (littleLaw (shape 5 2 1) u ((stageBPriority (shape 5 2 1)) 1) a : ℝ)) 15 a
def CB5_2_1I1R15Entropy : Ball := ⟨0, 0⟩
def CB5_2_1I1R15Mass : Ball := ⟨0, 0⟩
def CB5_2_1I1R15MassTerm : Ball := .exact 0
def CB5_2_1I1R15H : Ball := ⟨0, 0⟩
def CB5_2_1I1R16Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 2 1)) (fun u => (stageBLaw (shape 5 2 1) u : ℝ)) (stageBPriority (shape 5 2 1)) 1 (fun u a => (littleLaw (shape 5 2 1) u ((stageBPriority (shape 5 2 1)) 1) a : ℝ)) 16 a
def CB5_2_1I1R16Entropy : Ball := ⟨0, 0⟩
def CB5_2_1I1R16Mass : Ball := ⟨0, 0⟩
def CB5_2_1I1R16MassTerm : Ball := .exact 0
def CB5_2_1I1R16H : Ball := ⟨0, 0⟩
def CB5_2_1I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CB5_2_1I1R0H
  | 1 => CB5_2_1I1R1H
  | 2 => CB5_2_1I1R2H
  | 3 => CB5_2_1I1R3H
  | 4 => CB5_2_1I1R4H
  | 5 => CB5_2_1I1R5H
  | 6 => CB5_2_1I1R6H
  | 7 => CB5_2_1I1R7H
  | 8 => CB5_2_1I1R8H
  | 9 => CB5_2_1I1R9H
  | 10 => CB5_2_1I1R10H
  | 11 => CB5_2_1I1R11H
  | 12 => CB5_2_1I1R12H
  | 13 => CB5_2_1I1R13H
  | 14 => CB5_2_1I1R14H
  | 15 => CB5_2_1I1R15H
  | 16 => CB5_2_1I1R16H
  | _ => (.exact 0)
def CB5_2_1I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | _, _, _ => (.exact 0)
def CB5_2_1I1Singleton : Ball := ⟨0, 0⟩
def CB5_2_1I1Group : Ball := ⟨(157726739413993165697020365651 / 2500000000000000000000000000000), (23457779459 / 20000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB5_2_1I1H : Ball := ⟨(22879312493824239807758036168991 / 25000000000000000000000000000000), (158145904709 / 50000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB5_2_1I2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB5_2_1I2PairEntropy : Ball := ⟨(11753875141976755788953314120853 / 12500000000000000000000000000000), (34431819137 / 50000000000000000000000000000000)⟩
def CB5_2_1I2PairMass : Ball := ⟨1, (27 / 25000000000000000000000000000000)⟩
def CB5_2_1I2PairMassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB5_2_1I2PairMassTermLog : Ball := ⟨0, (2117582379 / 10000000000000000000000000000000)⟩
def CB5_2_1I2PairMassTerm : Ball := ⟨0, (21175823791 / 100000000000000000000000000000000)⟩
def CB5_2_1I2PairH : Ball := ⟨(11753875141976755788953314120853 / 12500000000000000000000000000000), (18007892413 / 20000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB5_2_1I2R0Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 2 1)) (fun u => (stageBLaw (shape 5 2 1) u : ℝ)) (stageBPriority (shape 5 2 1)) 2 (fun u a => (littleLaw (shape 5 2 1) u ((stageBPriority (shape 5 2 1)) 2) a : ℝ)) 0 a
def CB5_2_1I2R0Entropy : Ball := ⟨0, 0⟩
def CB5_2_1I2R0Mass : Ball := ⟨0, 0⟩
def CB5_2_1I2R0MassTerm : Ball := .exact 0
def CB5_2_1I2R0H : Ball := ⟨0, 0⟩
def CB5_2_1I2R1Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 2 1)) (fun u => (stageBLaw (shape 5 2 1) u : ℝ)) (stageBPriority (shape 5 2 1)) 2 (fun u a => (littleLaw (shape 5 2 1) u ((stageBPriority (shape 5 2 1)) 2) a : ℝ)) 1 a
def CB5_2_1I2R1Entropy : Ball := ⟨(1765548688963737013294197353 / 50000000000000000000000000000), (1361957097 / 100000000000000000000000000000000)⟩
def CB5_2_1I2R1Mass : Ball := ⟨(357314469969927548416673592027 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def CB5_2_1I2R1MassTermLogWitness : LogWitness := ⟨-8, 357314469969927548416673592027, 195312500000000000000000000000⟩
def CB5_2_1I2R1MassTermLog : Ball := ⟨(-386028282976899231126090684623 / 78125000000000000000000000000), (190582413567 / 100000000000000000000000000000000)⟩
def CB5_2_1I2R1MassTerm : Ball := ⟨(1765548688963737013294197353 / 50000000000000000000000000000), (1361957097 / 100000000000000000000000000000000)⟩
def CB5_2_1I2R1H : Ball := ⟨0, (1361957097 / 50000000000000000000000000000000)⟩
def CB5_2_1I2R2Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 2 1)) (fun u => (stageBLaw (shape 5 2 1) u : ℝ)) (stageBPriority (shape 5 2 1)) 2 (fun u a => (littleLaw (shape 5 2 1) u ((stageBPriority (shape 5 2 1)) 2) a : ℝ)) 2 a
def CB5_2_1I2R2Entropy : Ball := ⟨(7436512738790305734810412409469 / 20000000000000000000000000000000), (20222230031 / 100000000000000000000000000000000)⟩
def CB5_2_1I2R2Mass : Ball := ⟨(3151010108785313270505790947861 / 10000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
def CB5_2_1I2R2MassTermLogWitness : LogWitness := ⟨-2, 3151010108785313270505790947861, 2500000000000000000000000000000⟩
def CB5_2_1I2R2MassTermLog : Ball := ⟨(-57743101105215507920698095427997 / 50000000000000000000000000000000), (31763735553 / 50000000000000000000000000000000)⟩
def CB5_2_1I2R2MassTerm : Ball := ⟨(2274363691189330756931963794129 / 6250000000000000000000000000000), (10008785193 / 50000000000000000000000000000000)⟩
def CB5_2_1I2R2H : Ball := ⟨(792744634922236563140641341281 / 100000000000000000000000000000000), (40239800417 / 100000000000000000000000000000000)⟩
def CB5_2_1I2R3Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 2 1)) (fun u => (stageBLaw (shape 5 2 1) u : ℝ)) (stageBPriority (shape 5 2 1)) 2 (fun u a => (littleLaw (shape 5 2 1) u ((stageBPriority (shape 5 2 1)) 2) a : ℝ)) 3 a
def CB5_2_1I2R3Entropy : Ball := ⟨0, 0⟩
def CB5_2_1I2R3Mass : Ball := ⟨0, 0⟩
def CB5_2_1I2R3MassTerm : Ball := .exact 0
def CB5_2_1I2R3H : Ball := ⟨0, 0⟩
def CB5_2_1I2R4Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 2 1)) (fun u => (stageBLaw (shape 5 2 1) u : ℝ)) (stageBPriority (shape 5 2 1)) 2 (fun u a => (littleLaw (shape 5 2 1) u ((stageBPriority (shape 5 2 1)) 2) a : ℝ)) 4 a
def CB5_2_1I2R4Entropy : Ball := ⟨0, 0⟩
def CB5_2_1I2R4Mass : Ball := ⟨0, 0⟩
def CB5_2_1I2R4MassTerm : Ball := .exact 0
def CB5_2_1I2R4H : Ball := ⟨0, 0⟩
def CB5_2_1I2R5Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 2 1)) (fun u => (stageBLaw (shape 5 2 1) u : ℝ)) (stageBPriority (shape 5 2 1)) 2 (fun u a => (littleLaw (shape 5 2 1) u ((stageBPriority (shape 5 2 1)) 2) a : ℝ)) 5 a
def CB5_2_1I2R5Entropy : Ball := ⟨0, 0⟩
def CB5_2_1I2R5Mass : Ball := ⟨0, 0⟩
def CB5_2_1I2R5MassTerm : Ball := .exact 0
def CB5_2_1I2R5H : Ball := ⟨0, 0⟩
def CB5_2_1I2R6Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 2 1)) (fun u => (stageBLaw (shape 5 2 1) u : ℝ)) (stageBPriority (shape 5 2 1)) 2 (fun u a => (littleLaw (shape 5 2 1) u ((stageBPriority (shape 5 2 1)) 2) a : ℝ)) 6 a
def CB5_2_1I2R6Entropy : Ball := ⟨0, 0⟩
def CB5_2_1I2R6Mass : Ball := ⟨0, 0⟩
def CB5_2_1I2R6MassTerm : Ball := .exact 0
def CB5_2_1I2R6H : Ball := ⟨0, 0⟩
def CB5_2_1I2R7Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 2 1)) (fun u => (stageBLaw (shape 5 2 1) u : ℝ)) (stageBPriority (shape 5 2 1)) 2 (fun u a => (littleLaw (shape 5 2 1) u ((stageBPriority (shape 5 2 1)) 2) a : ℝ)) 7 a
def CB5_2_1I2R7Entropy : Ball := ⟨0, 0⟩
def CB5_2_1I2R7Mass : Ball := ⟨0, 0⟩
def CB5_2_1I2R7MassTerm : Ball := .exact 0
def CB5_2_1I2R7H : Ball := ⟨0, 0⟩
def CB5_2_1I2R8Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 2 1)) (fun u => (stageBLaw (shape 5 2 1) u : ℝ)) (stageBPriority (shape 5 2 1)) 2 (fun u a => (littleLaw (shape 5 2 1) u ((stageBPriority (shape 5 2 1)) 2) a : ℝ)) 8 a
def CB5_2_1I2R8Entropy : Ball := ⟨0, 0⟩
def CB5_2_1I2R8Mass : Ball := ⟨0, 0⟩
def CB5_2_1I2R8MassTerm : Ball := .exact 0
def CB5_2_1I2R8H : Ball := ⟨0, 0⟩
def CB5_2_1I2R9Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 2 1)) (fun u => (stageBLaw (shape 5 2 1) u : ℝ)) (stageBPriority (shape 5 2 1)) 2 (fun u a => (littleLaw (shape 5 2 1) u ((stageBPriority (shape 5 2 1)) 2) a : ℝ)) 9 a
def CB5_2_1I2R9Entropy : Ball := ⟨0, 0⟩
def CB5_2_1I2R9Mass : Ball := ⟨0, 0⟩
def CB5_2_1I2R9MassTerm : Ball := .exact 0
def CB5_2_1I2R9H : Ball := ⟨0, 0⟩
def CB5_2_1I2R10Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 2 1)) (fun u => (stageBLaw (shape 5 2 1) u : ℝ)) (stageBPriority (shape 5 2 1)) 2 (fun u a => (littleLaw (shape 5 2 1) u ((stageBPriority (shape 5 2 1)) 2) a : ℝ)) 10 a
def CB5_2_1I2R10Entropy : Ball := ⟨0, 0⟩
def CB5_2_1I2R10Mass : Ball := ⟨0, 0⟩
def CB5_2_1I2R10MassTerm : Ball := .exact 0
def CB5_2_1I2R10H : Ball := ⟨0, 0⟩
def CB5_2_1I2R11Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 2 1)) (fun u => (stageBLaw (shape 5 2 1) u : ℝ)) (stageBPriority (shape 5 2 1)) 2 (fun u a => (littleLaw (shape 5 2 1) u ((stageBPriority (shape 5 2 1)) 2) a : ℝ)) 11 a
def CB5_2_1I2R11Entropy : Ball := ⟨0, 0⟩
def CB5_2_1I2R11Mass : Ball := ⟨0, 0⟩
def CB5_2_1I2R11MassTerm : Ball := .exact 0
def CB5_2_1I2R11H : Ball := ⟨0, 0⟩
def CB5_2_1I2R12Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 2 1)) (fun u => (stageBLaw (shape 5 2 1) u : ℝ)) (stageBPriority (shape 5 2 1)) 2 (fun u a => (littleLaw (shape 5 2 1) u ((stageBPriority (shape 5 2 1)) 2) a : ℝ)) 12 a
def CB5_2_1I2R12Entropy : Ball := ⟨0, 0⟩
def CB5_2_1I2R12Mass : Ball := ⟨0, 0⟩
def CB5_2_1I2R12MassTerm : Ball := .exact 0
def CB5_2_1I2R12H : Ball := ⟨0, 0⟩
def CB5_2_1I2R13Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 2 1)) (fun u => (stageBLaw (shape 5 2 1) u : ℝ)) (stageBPriority (shape 5 2 1)) 2 (fun u a => (littleLaw (shape 5 2 1) u ((stageBPriority (shape 5 2 1)) 2) a : ℝ)) 13 a
def CB5_2_1I2R13Entropy : Ball := ⟨0, 0⟩
def CB5_2_1I2R13Mass : Ball := ⟨0, 0⟩
def CB5_2_1I2R13MassTerm : Ball := .exact 0
def CB5_2_1I2R13H : Ball := ⟨0, 0⟩
def CB5_2_1I2R14Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 2 1)) (fun u => (stageBLaw (shape 5 2 1) u : ℝ)) (stageBPriority (shape 5 2 1)) 2 (fun u a => (littleLaw (shape 5 2 1) u ((stageBPriority (shape 5 2 1)) 2) a : ℝ)) 14 a
def CB5_2_1I2R14Entropy : Ball := ⟨0, 0⟩
def CB5_2_1I2R14Mass : Ball := ⟨0, 0⟩
def CB5_2_1I2R14MassTerm : Ball := .exact 0
def CB5_2_1I2R14H : Ball := ⟨0, 0⟩
def CB5_2_1I2R15Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 2 1)) (fun u => (stageBLaw (shape 5 2 1) u : ℝ)) (stageBPriority (shape 5 2 1)) 2 (fun u a => (littleLaw (shape 5 2 1) u ((stageBPriority (shape 5 2 1)) 2) a : ℝ)) 15 a
def CB5_2_1I2R15Entropy : Ball := ⟨0, 0⟩
def CB5_2_1I2R15Mass : Ball := ⟨0, 0⟩
def CB5_2_1I2R15MassTerm : Ball := .exact 0
def CB5_2_1I2R15H : Ball := ⟨0, 0⟩
def CB5_2_1I2R16Value (a : Fin 6) : ℝ := residualLaw (below (shape 5 2 1)) (fun u => (stageBLaw (shape 5 2 1) u : ℝ)) (stageBPriority (shape 5 2 1)) 2 (fun u a => (littleLaw (shape 5 2 1) u ((stageBPriority (shape 5 2 1)) 2) a : ℝ)) 16 a
def CB5_2_1I2R16Entropy : Ball := ⟨0, 0⟩
def CB5_2_1I2R16Mass : Ball := ⟨0, 0⟩
def CB5_2_1I2R16MassTerm : Ball := .exact 0
def CB5_2_1I2R16H : Ball := ⟨0, 0⟩
def CB5_2_1I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CB5_2_1I2R0H
  | 1 => CB5_2_1I2R1H
  | 2 => CB5_2_1I2R2H
  | 3 => CB5_2_1I2R3H
  | 4 => CB5_2_1I2R4H
  | 5 => CB5_2_1I2R5H
  | 6 => CB5_2_1I2R6H
  | 7 => CB5_2_1I2R7H
  | 8 => CB5_2_1I2R8H
  | 9 => CB5_2_1I2R9H
  | 10 => CB5_2_1I2R10H
  | 11 => CB5_2_1I2R11H
  | 12 => CB5_2_1I2R12H
  | 13 => CB5_2_1I2R13H
  | 14 => CB5_2_1I2R14H
  | 15 => CB5_2_1I2R15H
  | 16 => CB5_2_1I2R16H
  | _ => (.exact 0)
def CB5_2_1I2S2_2_0Value (a : Fin 6) : ℝ := (littleLaw (shape 5 2 1) (shape 2 2 0) ((stageBPriority (shape 5 2 1)) 2) a : ℝ)
def CB5_2_1I2S2_2_0E_2LogWitness : LogWitness := ⟨-1, 444947, 250000⟩
def CB5_2_1I2S2_2_0E_2Log : Ball := ⟨(-11665292447264905939613678307427 / 100000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
def CB5_2_1I2S2_2_0E_2 : Ball := ⟨(10380873757066356206226574643709 / 100000000000000000000000000000000), (37688476881 / 100000000000000000000000000000000)⟩
def CB5_2_1I2S2_2_0E_3LogWitness : LogWitness := ⟨-4, 55053, 31250⟩
def CB5_2_1I2S2_2_0E_3Log : Ball := ⟨(-110315587041277227232948872211851 / 50000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
def CB5_2_1I2S2_2_0E_3 : Ball := ⟨(6073204013383435190855534261879 / 25000000000000000000000000000000), (11657926213 / 100000000000000000000000000000000)⟩
def CB5_2_1I2S2_2_0Terms (a : Fin 6) : Ball :=
  match a.val with
  | 2 => ⟨(10380873757066356206226574643709 / 100000000000000000000000000000000), (37688476881 / 100000000000000000000000000000000)⟩
  | 3 => ⟨(6073204013383435190855534261879 / 25000000000000000000000000000000), (11657926213 / 100000000000000000000000000000000)⟩
  | _ => (.exact 0)
def CB5_2_1I2S2_2_0Entropy : Ball := ⟨(1386947592424003878785948467649 / 4000000000000000000000000000000), (24673201547 / 50000000000000000000000000000000)⟩
def CB5_2_1I2S2_2_0Mass : Ball := ⟨1, 0⟩
def CB5_2_1I2S2_2_0MassTermLog : Ball := .exact 0
def CB5_2_1I2S2_2_0MassTerm : Ball := ⟨0, 0⟩
def CB5_2_1I2S2_2_0H : Ball := ⟨(1386947592424003878785948467649 / 4000000000000000000000000000000), (24673201547 / 50000000000000000000000000000000)⟩
def CB5_2_1I2S3_0_1Value (a : Fin 6) : ℝ := (littleLaw (shape 5 2 1) (shape 3 0 1) ((stageBPriority (shape 5 2 1)) 2) a : ℝ)
def CB5_2_1I2S3_0_1E_4Log : Ball := .exact 0
def CB5_2_1I2S3_0_1E_4 : Ball := ⟨0, 0⟩
def CB5_2_1I2S3_0_1Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB5_2_1I2S3_0_1Entropy : Ball := ⟨0, 0⟩
def CB5_2_1I2S3_0_1Mass : Ball := ⟨1, 0⟩
def CB5_2_1I2S3_0_1MassTermLog : Ball := .exact 0
def CB5_2_1I2S3_0_1MassTerm : Ball := ⟨0, 0⟩
def CB5_2_1I2S3_0_1H : Ball := ⟨0, 0⟩
def CB5_2_1I2S3_1_0Value (a : Fin 6) : ℝ := (littleLaw (shape 5 2 1) (shape 3 1 0) ((stageBPriority (shape 5 2 1)) 2) a : ℝ)
def CB5_2_1I2S3_1_0E_4Log : Ball := .exact 0
def CB5_2_1I2S3_1_0E_4 : Ball := ⟨0, 0⟩
def CB5_2_1I2S3_1_0Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB5_2_1I2S3_1_0Entropy : Ball := ⟨0, 0⟩
def CB5_2_1I2S3_1_0Mass : Ball := ⟨1, 0⟩
def CB5_2_1I2S3_1_0MassTermLog : Ball := .exact 0
def CB5_2_1I2S3_1_0MassTerm : Ball := ⟨0, 0⟩
def CB5_2_1I2S3_1_0H : Ball := ⟨0, 0⟩
def CB5_2_1I2S4_0_0Value (a : Fin 6) : ℝ := (littleLaw (shape 5 2 1) (shape 4 0 0) ((stageBPriority (shape 5 2 1)) 2) a : ℝ)
def CB5_2_1I2S4_0_0E_5Log : Ball := .exact 0
def CB5_2_1I2S4_0_0E_5 : Ball := ⟨0, 0⟩
def CB5_2_1I2S4_0_0Terms (a : Fin 6) : Ball :=
  match a.val with
  | 5 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB5_2_1I2S4_0_0Entropy : Ball := ⟨0, 0⟩
def CB5_2_1I2S4_0_0Mass : Ball := ⟨1, 0⟩
def CB5_2_1I2S4_0_0MassTermLog : Ball := .exact 0
def CB5_2_1I2S4_0_0MassTerm : Ball := ⟨0, 0⟩
def CB5_2_1I2S4_0_0H : Ball := ⟨0, 0⟩
def CB5_2_1I2Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 2, 2, 0 => CB5_2_1I2S2_2_0H
  | 3, 0, 1 => CB5_2_1I2S3_0_1H
  | 3, 1, 0 => CB5_2_1I2S3_1_0H
  | 4, 0, 0 => CB5_2_1I2S4_0_0H
  | _, _, _ => (.exact 0)
def CB5_2_1I2Singleton : Ball := ⟨(308167098657990073854559001417 / 5000000000000000000000000000000), (68527003 / 781250000000000000000000000000)⟩
def CB5_2_1I2Group : Ball := ⟨(6956086608082038040231821369621 / 100000000000000000000000000000000), (10347034199 / 20000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB5_2_1I2H : Ball := ⟨(40059413959824985115581435113791 / 50000000000000000000000000000000), (38701960811 / 20000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB6_1_1I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB6_1_1I0Value (a : Fin 17) : ℝ := marginal (below (shape 6 1 1)) (fun u => (stageBLaw (shape 6 1 1) u : ℝ)) ((stageBPriority (shape 6 1 1)) 0) a
def CB6_1_1I0Entropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (21175823793 / 50000000000000000000000000000000)⟩
def CB6_1_1I0Mass : Ball := ⟨1, (13 / 10000000000000000000000000000000)⟩
def CB6_1_1I0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB6_1_1I0MassTermLog : Ball := ⟨0, (5293955953 / 25000000000000000000000000000000)⟩
def CB6_1_1I0MassTerm : Ball := ⟨0, (21175823813 / 100000000000000000000000000000000)⟩
def CB6_1_1I0H : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (63527471399 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB6_1_1I1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB6_1_1I1PairEntropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (21175823793 / 50000000000000000000000000000000)⟩
def CB6_1_1I1PairMass : Ball := ⟨1, (13 / 10000000000000000000000000000000)⟩
def CB6_1_1I1PairMassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB6_1_1I1PairMassTermLog : Ball := ⟨0, (5293955953 / 25000000000000000000000000000000)⟩
def CB6_1_1I1PairMassTerm : Ball := ⟨0, (21175823813 / 100000000000000000000000000000000)⟩
def CB6_1_1I1PairH : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (63527471399 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB6_1_1I1R0Value (a : Fin 6) : ℝ := residualLaw (below (shape 6 1 1)) (fun u => (stageBLaw (shape 6 1 1) u : ℝ)) (stageBPriority (shape 6 1 1)) 1 (fun u a => (littleLaw (shape 6 1 1) u ((stageBPriority (shape 6 1 1)) 1) a : ℝ)) 0 a
def CB6_1_1I1R0Entropy : Ball := ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823793 / 100000000000000000000000000000000)⟩
def CB6_1_1I1R0Mass : Ball := ⟨(1 / 2), (13 / 20000000000000000000000000000000)⟩
def CB6_1_1I1R0MassTermLogWitness : LogWitness := ⟨-1, 1, 1⟩
def CB6_1_1I1R0MassTermLog : Ball := ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (8470329499 / 20000000000000000000000000000000)⟩
def CB6_1_1I1R0MassTerm : Ball := ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823793 / 100000000000000000000000000000000)⟩
def CB6_1_1I1R0H : Ball := ⟨0, (21175823793 / 50000000000000000000000000000000)⟩
def CB6_1_1I1R1Value (a : Fin 6) : ℝ := residualLaw (below (shape 6 1 1)) (fun u => (stageBLaw (shape 6 1 1) u : ℝ)) (stageBPriority (shape 6 1 1)) 1 (fun u a => (littleLaw (shape 6 1 1) u ((stageBPriority (shape 6 1 1)) 1) a : ℝ)) 1 a
def CB6_1_1I1R1Entropy : Ball := ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823793 / 100000000000000000000000000000000)⟩
def CB6_1_1I1R1Mass : Ball := ⟨(1 / 2), (13 / 20000000000000000000000000000000)⟩
def CB6_1_1I1R1MassTermLogWitness : LogWitness := ⟨-1, 1, 1⟩
def CB6_1_1I1R1MassTermLog : Ball := ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (8470329499 / 20000000000000000000000000000000)⟩
def CB6_1_1I1R1MassTerm : Ball := ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823793 / 100000000000000000000000000000000)⟩
def CB6_1_1I1R1H : Ball := ⟨0, (21175823793 / 50000000000000000000000000000000)⟩
def CB6_1_1I1R2Value (a : Fin 6) : ℝ := residualLaw (below (shape 6 1 1)) (fun u => (stageBLaw (shape 6 1 1) u : ℝ)) (stageBPriority (shape 6 1 1)) 1 (fun u a => (littleLaw (shape 6 1 1) u ((stageBPriority (shape 6 1 1)) 1) a : ℝ)) 2 a
def CB6_1_1I1R2Entropy : Ball := ⟨0, 0⟩
def CB6_1_1I1R2Mass : Ball := ⟨0, 0⟩
def CB6_1_1I1R2MassTerm : Ball := .exact 0
def CB6_1_1I1R2H : Ball := ⟨0, 0⟩
def CB6_1_1I1R3Value (a : Fin 6) : ℝ := residualLaw (below (shape 6 1 1)) (fun u => (stageBLaw (shape 6 1 1) u : ℝ)) (stageBPriority (shape 6 1 1)) 1 (fun u a => (littleLaw (shape 6 1 1) u ((stageBPriority (shape 6 1 1)) 1) a : ℝ)) 3 a
def CB6_1_1I1R3Entropy : Ball := ⟨0, 0⟩
def CB6_1_1I1R3Mass : Ball := ⟨0, 0⟩
def CB6_1_1I1R3MassTerm : Ball := .exact 0
def CB6_1_1I1R3H : Ball := ⟨0, 0⟩
def CB6_1_1I1R4Value (a : Fin 6) : ℝ := residualLaw (below (shape 6 1 1)) (fun u => (stageBLaw (shape 6 1 1) u : ℝ)) (stageBPriority (shape 6 1 1)) 1 (fun u a => (littleLaw (shape 6 1 1) u ((stageBPriority (shape 6 1 1)) 1) a : ℝ)) 4 a
def CB6_1_1I1R4Entropy : Ball := ⟨0, 0⟩
def CB6_1_1I1R4Mass : Ball := ⟨0, 0⟩
def CB6_1_1I1R4MassTerm : Ball := .exact 0
def CB6_1_1I1R4H : Ball := ⟨0, 0⟩
def CB6_1_1I1R5Value (a : Fin 6) : ℝ := residualLaw (below (shape 6 1 1)) (fun u => (stageBLaw (shape 6 1 1) u : ℝ)) (stageBPriority (shape 6 1 1)) 1 (fun u a => (littleLaw (shape 6 1 1) u ((stageBPriority (shape 6 1 1)) 1) a : ℝ)) 5 a
def CB6_1_1I1R5Entropy : Ball := ⟨0, 0⟩
def CB6_1_1I1R5Mass : Ball := ⟨0, 0⟩
def CB6_1_1I1R5MassTerm : Ball := .exact 0
def CB6_1_1I1R5H : Ball := ⟨0, 0⟩
def CB6_1_1I1R6Value (a : Fin 6) : ℝ := residualLaw (below (shape 6 1 1)) (fun u => (stageBLaw (shape 6 1 1) u : ℝ)) (stageBPriority (shape 6 1 1)) 1 (fun u a => (littleLaw (shape 6 1 1) u ((stageBPriority (shape 6 1 1)) 1) a : ℝ)) 6 a
def CB6_1_1I1R6Entropy : Ball := ⟨0, 0⟩
def CB6_1_1I1R6Mass : Ball := ⟨0, 0⟩
def CB6_1_1I1R6MassTerm : Ball := .exact 0
def CB6_1_1I1R6H : Ball := ⟨0, 0⟩
def CB6_1_1I1R7Value (a : Fin 6) : ℝ := residualLaw (below (shape 6 1 1)) (fun u => (stageBLaw (shape 6 1 1) u : ℝ)) (stageBPriority (shape 6 1 1)) 1 (fun u a => (littleLaw (shape 6 1 1) u ((stageBPriority (shape 6 1 1)) 1) a : ℝ)) 7 a
def CB6_1_1I1R7Entropy : Ball := ⟨0, 0⟩
def CB6_1_1I1R7Mass : Ball := ⟨0, 0⟩
def CB6_1_1I1R7MassTerm : Ball := .exact 0
def CB6_1_1I1R7H : Ball := ⟨0, 0⟩
def CB6_1_1I1R8Value (a : Fin 6) : ℝ := residualLaw (below (shape 6 1 1)) (fun u => (stageBLaw (shape 6 1 1) u : ℝ)) (stageBPriority (shape 6 1 1)) 1 (fun u a => (littleLaw (shape 6 1 1) u ((stageBPriority (shape 6 1 1)) 1) a : ℝ)) 8 a
def CB6_1_1I1R8Entropy : Ball := ⟨0, 0⟩
def CB6_1_1I1R8Mass : Ball := ⟨0, 0⟩
def CB6_1_1I1R8MassTerm : Ball := .exact 0
def CB6_1_1I1R8H : Ball := ⟨0, 0⟩
def CB6_1_1I1R9Value (a : Fin 6) : ℝ := residualLaw (below (shape 6 1 1)) (fun u => (stageBLaw (shape 6 1 1) u : ℝ)) (stageBPriority (shape 6 1 1)) 1 (fun u a => (littleLaw (shape 6 1 1) u ((stageBPriority (shape 6 1 1)) 1) a : ℝ)) 9 a
def CB6_1_1I1R9Entropy : Ball := ⟨0, 0⟩
def CB6_1_1I1R9Mass : Ball := ⟨0, 0⟩
def CB6_1_1I1R9MassTerm : Ball := .exact 0
def CB6_1_1I1R9H : Ball := ⟨0, 0⟩
def CB6_1_1I1R10Value (a : Fin 6) : ℝ := residualLaw (below (shape 6 1 1)) (fun u => (stageBLaw (shape 6 1 1) u : ℝ)) (stageBPriority (shape 6 1 1)) 1 (fun u a => (littleLaw (shape 6 1 1) u ((stageBPriority (shape 6 1 1)) 1) a : ℝ)) 10 a
def CB6_1_1I1R10Entropy : Ball := ⟨0, 0⟩
def CB6_1_1I1R10Mass : Ball := ⟨0, 0⟩
def CB6_1_1I1R10MassTerm : Ball := .exact 0
def CB6_1_1I1R10H : Ball := ⟨0, 0⟩
def CB6_1_1I1R11Value (a : Fin 6) : ℝ := residualLaw (below (shape 6 1 1)) (fun u => (stageBLaw (shape 6 1 1) u : ℝ)) (stageBPriority (shape 6 1 1)) 1 (fun u a => (littleLaw (shape 6 1 1) u ((stageBPriority (shape 6 1 1)) 1) a : ℝ)) 11 a
def CB6_1_1I1R11Entropy : Ball := ⟨0, 0⟩
def CB6_1_1I1R11Mass : Ball := ⟨0, 0⟩
def CB6_1_1I1R11MassTerm : Ball := .exact 0
def CB6_1_1I1R11H : Ball := ⟨0, 0⟩
def CB6_1_1I1R12Value (a : Fin 6) : ℝ := residualLaw (below (shape 6 1 1)) (fun u => (stageBLaw (shape 6 1 1) u : ℝ)) (stageBPriority (shape 6 1 1)) 1 (fun u a => (littleLaw (shape 6 1 1) u ((stageBPriority (shape 6 1 1)) 1) a : ℝ)) 12 a
def CB6_1_1I1R12Entropy : Ball := ⟨0, 0⟩
def CB6_1_1I1R12Mass : Ball := ⟨0, 0⟩
def CB6_1_1I1R12MassTerm : Ball := .exact 0
def CB6_1_1I1R12H : Ball := ⟨0, 0⟩
def CB6_1_1I1R13Value (a : Fin 6) : ℝ := residualLaw (below (shape 6 1 1)) (fun u => (stageBLaw (shape 6 1 1) u : ℝ)) (stageBPriority (shape 6 1 1)) 1 (fun u a => (littleLaw (shape 6 1 1) u ((stageBPriority (shape 6 1 1)) 1) a : ℝ)) 13 a
def CB6_1_1I1R13Entropy : Ball := ⟨0, 0⟩
def CB6_1_1I1R13Mass : Ball := ⟨0, 0⟩
def CB6_1_1I1R13MassTerm : Ball := .exact 0
def CB6_1_1I1R13H : Ball := ⟨0, 0⟩
def CB6_1_1I1R14Value (a : Fin 6) : ℝ := residualLaw (below (shape 6 1 1)) (fun u => (stageBLaw (shape 6 1 1) u : ℝ)) (stageBPriority (shape 6 1 1)) 1 (fun u a => (littleLaw (shape 6 1 1) u ((stageBPriority (shape 6 1 1)) 1) a : ℝ)) 14 a
def CB6_1_1I1R14Entropy : Ball := ⟨0, 0⟩
def CB6_1_1I1R14Mass : Ball := ⟨0, 0⟩
def CB6_1_1I1R14MassTerm : Ball := .exact 0
def CB6_1_1I1R14H : Ball := ⟨0, 0⟩
def CB6_1_1I1R15Value (a : Fin 6) : ℝ := residualLaw (below (shape 6 1 1)) (fun u => (stageBLaw (shape 6 1 1) u : ℝ)) (stageBPriority (shape 6 1 1)) 1 (fun u a => (littleLaw (shape 6 1 1) u ((stageBPriority (shape 6 1 1)) 1) a : ℝ)) 15 a
def CB6_1_1I1R15Entropy : Ball := ⟨0, 0⟩
def CB6_1_1I1R15Mass : Ball := ⟨0, 0⟩
def CB6_1_1I1R15MassTerm : Ball := .exact 0
def CB6_1_1I1R15H : Ball := ⟨0, 0⟩
def CB6_1_1I1R16Value (a : Fin 6) : ℝ := residualLaw (below (shape 6 1 1)) (fun u => (stageBLaw (shape 6 1 1) u : ℝ)) (stageBPriority (shape 6 1 1)) 1 (fun u a => (littleLaw (shape 6 1 1) u ((stageBPriority (shape 6 1 1)) 1) a : ℝ)) 16 a
def CB6_1_1I1R16Entropy : Ball := ⟨0, 0⟩
def CB6_1_1I1R16Mass : Ball := ⟨0, 0⟩
def CB6_1_1I1R16MassTerm : Ball := .exact 0
def CB6_1_1I1R16H : Ball := ⟨0, 0⟩
def CB6_1_1I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CB6_1_1I1R0H
  | 1 => CB6_1_1I1R1H
  | 2 => CB6_1_1I1R2H
  | 3 => CB6_1_1I1R3H
  | 4 => CB6_1_1I1R4H
  | 5 => CB6_1_1I1R5H
  | 6 => CB6_1_1I1R6H
  | 7 => CB6_1_1I1R7H
  | 8 => CB6_1_1I1R8H
  | 9 => CB6_1_1I1R9H
  | 10 => CB6_1_1I1R10H
  | 11 => CB6_1_1I1R11H
  | 12 => CB6_1_1I1R12H
  | 13 => CB6_1_1I1R13H
  | 14 => CB6_1_1I1R14H
  | 15 => CB6_1_1I1R15H
  | 16 => CB6_1_1I1R16H
  | _ => (.exact 0)
def CB6_1_1I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | _, _, _ => (.exact 0)
def CB6_1_1I1Singleton : Ball := ⟨0, 0⟩
def CB6_1_1I1Group : Ball := ⟨0, (21175823793 / 25000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB6_1_1I1H : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (232934061743 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB6_1_1I2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB6_1_1I2PairEntropy : Ball := ⟨(57536536866335857820744452350201 / 50000000000000000000000000000000), (13186943351 / 20000000000000000000000000000000)⟩
def CB6_1_1I2PairMass : Ball := ⟨1, (33 / 25000000000000000000000000000000)⟩
def CB6_1_1I2PairMassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB6_1_1I2PairMassTermLog : Ball := ⟨0, (10587911907 / 50000000000000000000000000000000)⟩
def CB6_1_1I2PairMassTerm : Ball := ⟨0, (4235164763 / 20000000000000000000000000000000)⟩
def CB6_1_1I2PairH : Ball := ⟨(57536536866335857820744452350201 / 50000000000000000000000000000000), (8711054057 / 10000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB6_1_1I2R0Value (a : Fin 6) : ℝ := residualLaw (below (shape 6 1 1)) (fun u => (stageBLaw (shape 6 1 1) u : ℝ)) (stageBPriority (shape 6 1 1)) 2 (fun u a => (littleLaw (shape 6 1 1) u ((stageBPriority (shape 6 1 1)) 2) a : ℝ)) 0 a
def CB6_1_1I2R0Entropy : Ball := ⟨0, 0⟩
def CB6_1_1I2R0Mass : Ball := ⟨0, 0⟩
def CB6_1_1I2R0MassTerm : Ball := .exact 0
def CB6_1_1I2R0H : Ball := ⟨0, 0⟩
def CB6_1_1I2R1Value (a : Fin 6) : ℝ := residualLaw (below (shape 6 1 1)) (fun u => (stageBLaw (shape 6 1 1) u : ℝ)) (stageBPriority (shape 6 1 1)) 2 (fun u a => (littleLaw (shape 6 1 1) u ((stageBPriority (shape 6 1 1)) 2) a : ℝ)) 1 a
def CB6_1_1I2R1Entropy : Ball := ⟨0, 0⟩
def CB6_1_1I2R1Mass : Ball := ⟨0, 0⟩
def CB6_1_1I2R1MassTerm : Ball := .exact 0
def CB6_1_1I2R1H : Ball := ⟨0, 0⟩
def CB6_1_1I2R2Value (a : Fin 6) : ℝ := residualLaw (below (shape 6 1 1)) (fun u => (stageBLaw (shape 6 1 1) u : ℝ)) (stageBPriority (shape 6 1 1)) 2 (fun u a => (littleLaw (shape 6 1 1) u ((stageBPriority (shape 6 1 1)) 2) a : ℝ)) 2 a
def CB6_1_1I2R2Entropy : Ball := ⟨(40255115997512766494097133581823 / 100000000000000000000000000000000), (11157430523 / 50000000000000000000000000000000)⟩
def CB6_1_1I2R2Mass : Ball := ⟨(124237509457400902736572326499 / 500000000000000000000000000000), (49 / 100000000000000000000000000000000)⟩
def CB6_1_1I2R2MassTermLogWitness : LogWitness := ⟨-3, 124237509457400902736572326499, 62500000000000000000000000000⟩
def CB6_1_1I2R2MassTermLog : Ball := ⟨(-139241296600450975538540600627167 / 100000000000000000000000000000000), (84703294929 / 100000000000000000000000000000000)⟩
def CB6_1_1I2R2MassTerm : Ball := ⟨(17298991903259292240785313317123 / 50000000000000000000000000000000), (10523326439 / 50000000000000000000000000000000)⟩
def CB6_1_1I2R2H : Ball := ⟨(5657132190994182012526506947577 / 100000000000000000000000000000000), (10840378481 / 25000000000000000000000000000000)⟩
def CB6_1_1I2R3Value (a : Fin 6) : ℝ := residualLaw (below (shape 6 1 1)) (fun u => (stageBLaw (shape 6 1 1) u : ℝ)) (stageBPriority (shape 6 1 1)) 2 (fun u a => (littleLaw (shape 6 1 1) u ((stageBPriority (shape 6 1 1)) 2) a : ℝ)) 3 a
def CB6_1_1I2R3Entropy : Ball := ⟨0, 0⟩
def CB6_1_1I2R3Mass : Ball := ⟨0, 0⟩
def CB6_1_1I2R3MassTerm : Ball := .exact 0
def CB6_1_1I2R3H : Ball := ⟨0, 0⟩
def CB6_1_1I2R4Value (a : Fin 6) : ℝ := residualLaw (below (shape 6 1 1)) (fun u => (stageBLaw (shape 6 1 1) u : ℝ)) (stageBPriority (shape 6 1 1)) 2 (fun u a => (littleLaw (shape 6 1 1) u ((stageBPriority (shape 6 1 1)) 2) a : ℝ)) 4 a
def CB6_1_1I2R4Entropy : Ball := ⟨0, 0⟩
def CB6_1_1I2R4Mass : Ball := ⟨0, 0⟩
def CB6_1_1I2R4MassTerm : Ball := .exact 0
def CB6_1_1I2R4H : Ball := ⟨0, 0⟩
def CB6_1_1I2R5Value (a : Fin 6) : ℝ := residualLaw (below (shape 6 1 1)) (fun u => (stageBLaw (shape 6 1 1) u : ℝ)) (stageBPriority (shape 6 1 1)) 2 (fun u a => (littleLaw (shape 6 1 1) u ((stageBPriority (shape 6 1 1)) 2) a : ℝ)) 5 a
def CB6_1_1I2R5Entropy : Ball := ⟨0, 0⟩
def CB6_1_1I2R5Mass : Ball := ⟨0, 0⟩
def CB6_1_1I2R5MassTerm : Ball := .exact 0
def CB6_1_1I2R5H : Ball := ⟨0, 0⟩
def CB6_1_1I2R6Value (a : Fin 6) : ℝ := residualLaw (below (shape 6 1 1)) (fun u => (stageBLaw (shape 6 1 1) u : ℝ)) (stageBPriority (shape 6 1 1)) 2 (fun u a => (littleLaw (shape 6 1 1) u ((stageBPriority (shape 6 1 1)) 2) a : ℝ)) 6 a
def CB6_1_1I2R6Entropy : Ball := ⟨0, 0⟩
def CB6_1_1I2R6Mass : Ball := ⟨0, 0⟩
def CB6_1_1I2R6MassTerm : Ball := .exact 0
def CB6_1_1I2R6H : Ball := ⟨0, 0⟩
def CB6_1_1I2R7Value (a : Fin 6) : ℝ := residualLaw (below (shape 6 1 1)) (fun u => (stageBLaw (shape 6 1 1) u : ℝ)) (stageBPriority (shape 6 1 1)) 2 (fun u a => (littleLaw (shape 6 1 1) u ((stageBPriority (shape 6 1 1)) 2) a : ℝ)) 7 a
def CB6_1_1I2R7Entropy : Ball := ⟨0, 0⟩
def CB6_1_1I2R7Mass : Ball := ⟨0, 0⟩
def CB6_1_1I2R7MassTerm : Ball := .exact 0
def CB6_1_1I2R7H : Ball := ⟨0, 0⟩
def CB6_1_1I2R8Value (a : Fin 6) : ℝ := residualLaw (below (shape 6 1 1)) (fun u => (stageBLaw (shape 6 1 1) u : ℝ)) (stageBPriority (shape 6 1 1)) 2 (fun u a => (littleLaw (shape 6 1 1) u ((stageBPriority (shape 6 1 1)) 2) a : ℝ)) 8 a
def CB6_1_1I2R8Entropy : Ball := ⟨0, 0⟩
def CB6_1_1I2R8Mass : Ball := ⟨0, 0⟩
def CB6_1_1I2R8MassTerm : Ball := .exact 0
def CB6_1_1I2R8H : Ball := ⟨0, 0⟩
def CB6_1_1I2R9Value (a : Fin 6) : ℝ := residualLaw (below (shape 6 1 1)) (fun u => (stageBLaw (shape 6 1 1) u : ℝ)) (stageBPriority (shape 6 1 1)) 2 (fun u a => (littleLaw (shape 6 1 1) u ((stageBPriority (shape 6 1 1)) 2) a : ℝ)) 9 a
def CB6_1_1I2R9Entropy : Ball := ⟨0, 0⟩
def CB6_1_1I2R9Mass : Ball := ⟨0, 0⟩
def CB6_1_1I2R9MassTerm : Ball := .exact 0
def CB6_1_1I2R9H : Ball := ⟨0, 0⟩
def CB6_1_1I2R10Value (a : Fin 6) : ℝ := residualLaw (below (shape 6 1 1)) (fun u => (stageBLaw (shape 6 1 1) u : ℝ)) (stageBPriority (shape 6 1 1)) 2 (fun u a => (littleLaw (shape 6 1 1) u ((stageBPriority (shape 6 1 1)) 2) a : ℝ)) 10 a
def CB6_1_1I2R10Entropy : Ball := ⟨0, 0⟩
def CB6_1_1I2R10Mass : Ball := ⟨0, 0⟩
def CB6_1_1I2R10MassTerm : Ball := .exact 0
def CB6_1_1I2R10H : Ball := ⟨0, 0⟩
def CB6_1_1I2R11Value (a : Fin 6) : ℝ := residualLaw (below (shape 6 1 1)) (fun u => (stageBLaw (shape 6 1 1) u : ℝ)) (stageBPriority (shape 6 1 1)) 2 (fun u a => (littleLaw (shape 6 1 1) u ((stageBPriority (shape 6 1 1)) 2) a : ℝ)) 11 a
def CB6_1_1I2R11Entropy : Ball := ⟨0, 0⟩
def CB6_1_1I2R11Mass : Ball := ⟨0, 0⟩
def CB6_1_1I2R11MassTerm : Ball := .exact 0
def CB6_1_1I2R11H : Ball := ⟨0, 0⟩
def CB6_1_1I2R12Value (a : Fin 6) : ℝ := residualLaw (below (shape 6 1 1)) (fun u => (stageBLaw (shape 6 1 1) u : ℝ)) (stageBPriority (shape 6 1 1)) 2 (fun u a => (littleLaw (shape 6 1 1) u ((stageBPriority (shape 6 1 1)) 2) a : ℝ)) 12 a
def CB6_1_1I2R12Entropy : Ball := ⟨0, 0⟩
def CB6_1_1I2R12Mass : Ball := ⟨0, 0⟩
def CB6_1_1I2R12MassTerm : Ball := .exact 0
def CB6_1_1I2R12H : Ball := ⟨0, 0⟩
def CB6_1_1I2R13Value (a : Fin 6) : ℝ := residualLaw (below (shape 6 1 1)) (fun u => (stageBLaw (shape 6 1 1) u : ℝ)) (stageBPriority (shape 6 1 1)) 2 (fun u a => (littleLaw (shape 6 1 1) u ((stageBPriority (shape 6 1 1)) 2) a : ℝ)) 13 a
def CB6_1_1I2R13Entropy : Ball := ⟨0, 0⟩
def CB6_1_1I2R13Mass : Ball := ⟨0, 0⟩
def CB6_1_1I2R13MassTerm : Ball := .exact 0
def CB6_1_1I2R13H : Ball := ⟨0, 0⟩
def CB6_1_1I2R14Value (a : Fin 6) : ℝ := residualLaw (below (shape 6 1 1)) (fun u => (stageBLaw (shape 6 1 1) u : ℝ)) (stageBPriority (shape 6 1 1)) 2 (fun u a => (littleLaw (shape 6 1 1) u ((stageBPriority (shape 6 1 1)) 2) a : ℝ)) 14 a
def CB6_1_1I2R14Entropy : Ball := ⟨0, 0⟩
def CB6_1_1I2R14Mass : Ball := ⟨0, 0⟩
def CB6_1_1I2R14MassTerm : Ball := .exact 0
def CB6_1_1I2R14H : Ball := ⟨0, 0⟩
def CB6_1_1I2R15Value (a : Fin 6) : ℝ := residualLaw (below (shape 6 1 1)) (fun u => (stageBLaw (shape 6 1 1) u : ℝ)) (stageBPriority (shape 6 1 1)) 2 (fun u a => (littleLaw (shape 6 1 1) u ((stageBPriority (shape 6 1 1)) 2) a : ℝ)) 15 a
def CB6_1_1I2R15Entropy : Ball := ⟨0, 0⟩
def CB6_1_1I2R15Mass : Ball := ⟨0, 0⟩
def CB6_1_1I2R15MassTerm : Ball := .exact 0
def CB6_1_1I2R15H : Ball := ⟨0, 0⟩
def CB6_1_1I2R16Value (a : Fin 6) : ℝ := residualLaw (below (shape 6 1 1)) (fun u => (stageBLaw (shape 6 1 1) u : ℝ)) (stageBPriority (shape 6 1 1)) 2 (fun u a => (littleLaw (shape 6 1 1) u ((stageBPriority (shape 6 1 1)) 2) a : ℝ)) 16 a
def CB6_1_1I2R16Entropy : Ball := ⟨0, 0⟩
def CB6_1_1I2R16Mass : Ball := ⟨0, 0⟩
def CB6_1_1I2R16MassTerm : Ball := .exact 0
def CB6_1_1I2R16H : Ball := ⟨0, 0⟩
def CB6_1_1I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CB6_1_1I2R0H
  | 1 => CB6_1_1I2R1H
  | 2 => CB6_1_1I2R2H
  | 3 => CB6_1_1I2R3H
  | 4 => CB6_1_1I2R4H
  | 5 => CB6_1_1I2R5H
  | 6 => CB6_1_1I2R6H
  | 7 => CB6_1_1I2R7H
  | 8 => CB6_1_1I2R8H
  | 9 => CB6_1_1I2R9H
  | 10 => CB6_1_1I2R10H
  | 11 => CB6_1_1I2R11H
  | 12 => CB6_1_1I2R12H
  | 13 => CB6_1_1I2R13H
  | 14 => CB6_1_1I2R14H
  | 15 => CB6_1_1I2R15H
  | 16 => CB6_1_1I2R16H
  | _ => (.exact 0)
def CB6_1_1I2S3_0_1Value (a : Fin 6) : ℝ := (littleLaw (shape 6 1 1) (shape 3 0 1) ((stageBPriority (shape 6 1 1)) 2) a : ℝ)
def CB6_1_1I2S3_0_1E_4Log : Ball := .exact 0
def CB6_1_1I2S3_0_1E_4 : Ball := ⟨0, 0⟩
def CB6_1_1I2S3_0_1Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB6_1_1I2S3_0_1Entropy : Ball := ⟨0, 0⟩
def CB6_1_1I2S3_0_1Mass : Ball := ⟨1, 0⟩
def CB6_1_1I2S3_0_1MassTermLog : Ball := .exact 0
def CB6_1_1I2S3_0_1MassTerm : Ball := ⟨0, 0⟩
def CB6_1_1I2S3_0_1H : Ball := ⟨0, 0⟩
def CB6_1_1I2S3_1_0Value (a : Fin 6) : ℝ := (littleLaw (shape 6 1 1) (shape 3 1 0) ((stageBPriority (shape 6 1 1)) 2) a : ℝ)
def CB6_1_1I2S3_1_0E_4Log : Ball := .exact 0
def CB6_1_1I2S3_1_0E_4 : Ball := ⟨0, 0⟩
def CB6_1_1I2S3_1_0Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB6_1_1I2S3_1_0Entropy : Ball := ⟨0, 0⟩
def CB6_1_1I2S3_1_0Mass : Ball := ⟨1, 0⟩
def CB6_1_1I2S3_1_0MassTermLog : Ball := .exact 0
def CB6_1_1I2S3_1_0MassTerm : Ball := ⟨0, 0⟩
def CB6_1_1I2S3_1_0H : Ball := ⟨0, 0⟩
def CB6_1_1I2S4_0_0Value (a : Fin 6) : ℝ := (littleLaw (shape 6 1 1) (shape 4 0 0) ((stageBPriority (shape 6 1 1)) 2) a : ℝ)
def CB6_1_1I2S4_0_0E_5Log : Ball := .exact 0
def CB6_1_1I2S4_0_0E_5 : Ball := ⟨0, 0⟩
def CB6_1_1I2S4_0_0Terms (a : Fin 6) : Ball :=
  match a.val with
  | 5 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB6_1_1I2S4_0_0Entropy : Ball := ⟨0, 0⟩
def CB6_1_1I2S4_0_0Mass : Ball := ⟨1, 0⟩
def CB6_1_1I2S4_0_0MassTermLog : Ball := .exact 0
def CB6_1_1I2S4_0_0MassTerm : Ball := ⟨0, 0⟩
def CB6_1_1I2S4_0_0H : Ball := ⟨0, 0⟩
def CB6_1_1I2Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 3, 0, 1 => CB6_1_1I2S3_0_1H
  | 3, 1, 0 => CB6_1_1I2S3_1_0H
  | 4, 0, 0 => CB6_1_1I2S4_0_0H
  | _, _, _ => (.exact 0)
def CB6_1_1I2Singleton : Ball := ⟨0, 0⟩
def CB6_1_1I2Group : Ball := ⟨(5657132190994182012526506947577 / 100000000000000000000000000000000), (10840378481 / 25000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB6_1_1I2H : Ball := ⟨(202653924513053421125851349229 / 195312500000000000000000000000), (86916784209 / 50000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_NativeSharp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def nativeLABall (i : Fin 3) : Ball := (Matrix.vecCons (⟨(117985629820354604769702009255473 / 100000000000000000000000000000000), (25286853793 / 25000000000000000000000000000000)⟩) (Matrix.vecCons (⟨(14553362614718917509713695395419 / 12500000000000000000000000000000), (495362055017 / 100000000000000000000000000000000)⟩) (Matrix.vecCons (⟨(13508474414138305071843256242429 / 12500000000000000000000000000000), (467443928227 / 100000000000000000000000000000000)⟩) Matrix.vecEmpty))) i
def nativeLBBall (i : Fin 3) : Ball := (Matrix.vecCons (⟨(36915911542259422191174414642177 / 25000000000000000000000000000000), (143554434849 / 100000000000000000000000000000000)⟩) (Matrix.vecCons (⟨(32908978604932824344186869459233 / 20000000000000000000000000000000), (610647767219 / 100000000000000000000000000000000)⟩) (Matrix.vecCons (⟨(64721008843697680778152495140253 / 50000000000000000000000000000000), (102799797137 / 20000000000000000000000000000000)⟩) Matrix.vecEmpty))) i

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
open AllFieldInitialEntropy
def nativeCstarBall : Ball := ⟨(23573978636551704730344303484969 / 6250000000000000000000000000000), (4390100049 / 500000000000000000000000000000)⟩
def nativeCBall (i : Fin 3) : Ball := (Matrix.vecCons (⟨(111534382195434982151109187935323 / 100000000000000000000000000000000), (1122721859821 / 100000000000000000000000000000000)⟩) (Matrix.vecCons (⟨(96211864242411813886864945299987 / 100000000000000000000000000000000), (496007458009 / 25000000000000000000000000000000)⟩) (Matrix.vecCons (⟨(69836922592162736777228907769783 / 50000000000000000000000000000000), (29054108183 / 1562500000000000000000000000000)⟩) Matrix.vecEmpty))) i
def nativeGapBall : Ball := ⟨(132303397031313521 / 100000000000000000000000000000000), (970498095253 / 50000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end


