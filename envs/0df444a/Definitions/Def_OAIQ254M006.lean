-- Prove2me | Definitions.Def_OAIQ254M006
-- name    : OAIQ254M006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T05:48:38.623487+00:00
-- url     : https://prove2.me/theorems/9f766b07-364b-4e51-a947-5721603ea01d
-- title:
--   Definitions bundle OAIQ254M006 of the split of OpenAI, Staggered extraction for exact matrix multiplication over every field
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant`, carved from OpenAI's openai/math development (OpenAI, *Staggered extraction for exact matrix multiplication over every field*, OpenAI Math Release, September 24, 2026, result family 107, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 742 declarations of OpenAI's Lean: 709 definitions and 33 theorems. The definitions and types are `OAI.MatrixAllFields.MatrixMultiplication.AllFieldStageCCapacity.symbolicMarginal`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.w204Trace`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.w205Trace`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.w206S4`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.w206Trace`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.w207S0`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.w207S1`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.w207S2`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.w207S3`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.w207S4`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.w207Trace`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.w209S0`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.w209S1`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.w209S2`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.w209S3`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.w209S4`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.w209Trace`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.w20S0`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.w20S1`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.w20S2`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.w20S3`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.w20S4`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.w20Trace`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.w21`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.w210S0`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.w210S1`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.w210S2`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.w210S3`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.w210S4`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.w210Trace`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.w211S0`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.w211S1`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.w211S2`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.w211S3`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.w211S4`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.w211Trace`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.w212S0`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.w212S1`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.w212S2`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.w212S3` and 669 more.
--
--   **Sources.** They come from these modules of lean/OAI/LinearAlgebra, in whole or in part: [`MatrixFields_Certificates_Four0_3_5`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Certificates/Four0_3_5.lean), [`MatrixFields_Certificates_SplitB1_1_6`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Certificates/SplitB1_1_6.lean), [`MatrixFields_Certificates_SplitB1_3_4`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Certificates/SplitB1_3_4.lean), [`MatrixFields_Certificates_SplitB2_3_3`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Certificates/SplitB2_3_3.lean), [`MatrixFields_Certificates_Weights2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Certificates/Weights2.lean), [`MatrixFields_Parameters_StageCCapacity`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Parameters/StageCCapacity.lean).
--
--   **Imports.** It imports the bundle `OAIQ254M000` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionFamily.fixed_allocation_constraint`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupNativeDegreeBound.exists_threshold_eventually_counts_le`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupNativeDegreeBound.nativeCompatibilityRate_eq`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A1_4_11Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A1_6_9Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A1_7_8Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A2_2_12Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A2_3_11Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A2_4_10Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A2_5_9Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A2_6_8Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A2_7_7Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A3_3_10Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A3_5_8Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A3_6_7Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A4_4_8Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A4_5_7Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A4_6_6Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A5_5_6Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.AProbsTable_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_1_6Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_1_6U0_0_4Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_1_6U0_1_3Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_1_6U1_0_3Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_1_6U1_1_2Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_2_5Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_2_5Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_3_4Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_3_4Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_4_3Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_4_3Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_5_2Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_5_2Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_1_5Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_1_5Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_2_4Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_2_4Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_3_3Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_3_3Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_5_1Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_5_1Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_5_1S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_5_1Ttotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_1_4Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_1_4Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_2_3Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_2_3Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_4_1Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_4_1Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B4_1_3Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B4_1_3Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B4_2_2Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B4_2_2Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B4_3_1Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B4_3_1Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B5_1_2Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B5_1_2Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B5_1_2S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B5_2_1Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B5_2_1Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_2_13I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_2_13I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_3_12I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_3_12I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_3_12I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_4_11I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_4_11I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_4_11I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I1PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I2PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I1PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I2PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I2Singles_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_2_12I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_2_12I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_2_12I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_3_11I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_3_11I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_3_11I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_4_10I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_5_9I1Group_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_5_9I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_5_9I2PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_5_9I2Singles_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_5_9I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_6_8I1Group_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_6_8I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_7_7I1Group_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_7_7I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_3_10I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_4_9I0_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_4_9I1Group_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_4_9I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_4_9I2PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_4_9I2Singles_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_4_9I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_5_8I1Group_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_5_8I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_6_7I1Group_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_6_7I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_4_8I1Group_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_4_8I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_5_7I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_5_7I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_6_6I1Group_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_6_6I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA5_5_6I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA5_5_6I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_1_6I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_1_6I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_2_5I0_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_2_5I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_2_5I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_3_4I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_3_4I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_4_3I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_4_3I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_5_2I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_5_2I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB2_1_5I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB2_1_5I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB2_2_4I0_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB2_2_4I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB2_2_4I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB2_3_3I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB2_3_3I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB2_4_2I0_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB2_4_2I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB2_4_2I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB2_5_1I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB2_5_1I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_1_4I0_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_1_4I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_1_4I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I0_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I0_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_4_1I0_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_4_1I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_4_1I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_1_3I0_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_1_3I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_1_3I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_2_2I0_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_2_2I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_2_2I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_3_1I0_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_3_1I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_3_1I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB5_1_2I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB5_1_2I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB5_2_1I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB5_2_1I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z0_5_3Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z0_5_3H2H_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z2_0_6Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z2_6_0Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z3_5_0Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z4_0_4Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z4_4_0Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z5_3_0Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.capacityABalls_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.capacityBBalls_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.fourRateBalls_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.halfTable_sound` and `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.nativeTBall_sound`.
-- source:
--   OpenAI, Staggered extraction for exact matrix multiplication over every field, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 107; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/LinearAlgebra at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ254M000

section
-- module Solutions.OAIQ254_MF.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- `norm_num` cannot decide equalities of `Fin` literals here (oaiq-091). -/
@[simp] theorem fin3_lit_0_1 : ((0 : Fin 3) = 1) ↔ False := by decide
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
end OAICompat434

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
open scoped BigOperators
def w50Trace : List Ball := [
  ⟨(47252585897334525427131536434317 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(24306677159329606395297438236621 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(24535616147583738291934726489499 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16433821705634918062580870706137 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(824002073875140207989546114123 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(103193358675069121855540162681 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(17221927415604884686783592779 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19701977356701113977243402277 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1232336053690703169237423847 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(17126483580120343107891663 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13708199793715603422120737 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2493463295410495917117529 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(103931816499206727234119 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(15994459590025507527571 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1785574973627510971 / 156250000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76201522169584958937 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w50S0 : Ball := ⟨(22328068739849776775696389866217 / 25000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w50S1 : Ball := ⟨(39883412292116543891426534049807 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w50S2 : Ball := ⟨(63627463042518121176310826622107 / 100000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
def w50S3 : Ball := ⟨(8096908106454018731516515646317 / 20000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
def w50S4 : Ball := ⟨(1024373763818137548924843116057 / 6250000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩

def w52Trace : List Ball := [
  ⟨(94576963914621259217505189236641 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(97263285916444179486511570691339 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49083539218577657455234692230219 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8218457853804215175566037617137 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4120631481820178285566038469107 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(412825332106161919969763009167 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8611892300201203221395936553 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4925959357334995388651066207 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(616219759802083691231947149 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(274044451525979487543910047 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13709142148901862855403159 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1246810233670350335173201 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(25984466323217592554217 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3998831041095165826097 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(114282564628990104257 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2381410987037007519 / 3125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w52S0 : Ball := ⟨(11181002629134464775733552852623 / 12500000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def w52S1 : Ball := ⟨(16001896933467112148862410300581 / 20000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
def w52S2 : Ball := ⟨(64015176367326041853428769853831 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w52S3 : Ball := ⟨(40979428053398585721896388350199 / 100000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
def w52S4 : Ball := ⟨(262392738059948593849370483877 / 1562500000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
def w52S5 : Ball := ⟨(2820093910491004738042527563213 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
abbrev w52 : Ball := w52S5

def w53Trace : List Ball := [
  ⟨(9472085981072132827787397524319 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19467314229715939628133190310611 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1964327694285953374980600969197 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16443112887117801282313517122753 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1030468863697918858474372015391 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(412929267379136138000551802967 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4306875961545940671389316009 / 3125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19707562341275789773722941567 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1232646711362290880639135941 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(137042965599593419509774749 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2742205831091363555804109 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2493935189601084972786341 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(51974988646074868342001 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1599705535433063038869 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1142941107839874819213 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19053104471079033951 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w53S0 : Ball := ⟨(89720412832823229054714993821997 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w53S1 : Ball := ⟨(80497524788922311615133304296963 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w53S2 : Ball := ⟨(64798514971431620491477576158537 / 100000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
def w53S3 : Ball := ⟨(20994237712514239322993932447441 / 50000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
def w53S4 : Ball := ⟨(2203790085647775600599247863759 / 12500000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
def w53S5 : Ball := ⟨(97133814831988602344613964599 / 3125000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
abbrev w53 : Ball := w53S5

def w54Trace : List Ball := [
  ⟨(94726336018724247935001405650513 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(97339359405216626913511575926391 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(6138641275384145091973061253063 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8221674309759144158417349949779 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(824384554276761515212889951833 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(412933220583575849129301793867 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(17227645304681629058613936897 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2463463001524730737676400099 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2465309182848158152945843913 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(137043754380314986761860231 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27422201843067345018911793 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2493947158904920272628963 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1663207006776495846063 / 800000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(15997121192714015743917 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(571472749450067305539 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1524253883956988289 / 2000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w54S0 : Ball := ⟨(8973078735532254802827096084977 / 10000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def w54S1 : Ball := ⟨(1610322839881222574619643253979 / 2000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
def w54S2 : Ball := ⟨(12965698243215627990406698829243 / 20000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w54S3 : Ball := ⟨(8405466546706241098088100358087 / 20000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
def w54S4 : Ball := ⟨(17662966966949435490819610182453 / 100000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩

def w55Trace : List Ball := [
  ⟨(94782596481407390293967837834647 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(24342000436659985798248846633711 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(12279690923707035899012601458711 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1027860623049928738496056645659 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(257650548629855777371855527057 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(825947649645521268410394518077 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(17229098239486942142506129949 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19709159115756258215941667633 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2465471054082147153897049431 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(68525927924805527885271123 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3427959504605575283113549 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2494070093031567274022077 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(207910337903625888762043 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3199559479998044318173 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1142990598124789335097 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3810776600625775973 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w55S0 : Ball := ⟨(350927367021769554806563478539 / 390625000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def w55S1 : Ball := ⟨(20176898772964434591503637741663 / 25000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
def w55S2 : Ball := ⟨(3256857952755629649879186192383 / 5000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
def w55S3 : Ball := ⟨(10607123724427591172522982947679 / 25000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
def w55S4 : Ball := ⟨(3600354358570068899733307293759 / 20000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
def w55S5 : Ball := ⟨(324063787681862306483878361403 / 10000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
abbrev w55 : Ball := w55S5

def w56Trace : List Ball := [
  ⟨(14828258162679588668233433511 / 15625000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3044630856729539361897555248149 / 3125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4913900328931913865351291252413 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16450856664549536116304513510777 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4123429703694875574151481364019 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(826118232085810222406215479293 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(17232150101559854136894803059 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9856107727824750835734076111 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1232905523003005477650992301 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(274137743543715374791958499 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27426772317048612058556363 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(311791036391876269407587 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(103965105413534485259281 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(15999217609018758510417 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(285771329366401189279 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76221491423314339981 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w56S0 : Ball := ⟨(281442867378014528867241064857 / 312500000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def w56S1 : Ball := ⟨(81111129700309682879484067206857 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
def w56S2 : Ball := ⟨(16447538403151148866018747980209 / 25000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w56S3 : Ball := ⟨(43283443123701095034535898275941 / 100000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
def w56S4 : Ball := ⟨(18734564486426676072317960817043 / 100000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
def w56S5 : Ball := ⟨(701967812992159249958260250633 / 20000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
abbrev w56 : Ball := w56S5

def w57Trace : List Ball := [
  ⟨(47452576266722153038239866652237 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(48715187775953089775793627829451 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9827947809962321612239856445469 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(658041662677348840149949950099 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(515433351619077091864625844423 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(413062216168045482412261977783 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(34464522053329517477201435527 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4928081635382049087557996979 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1232911701596389705529931453 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(274138980434711163504028661 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8776603152187461404139 / 32000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1247168837601924423442259 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(207930933092501257873229 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(15999269225058368783519 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(285772189981753086317 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9527713499172620473 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w57S0 : Ball := ⟨(90069879773963301880084931137781 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w57S1 : Ball := ⟨(811258324249620350057863717173 / 1000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w57S2 : Ball := ⟨(65814006866430214971078196359137 / 100000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
def w57S3 : Ball := ⟨(10828708749536308710192444745319 / 25000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
def w57S4 : Ball := ⟨(1172609331822842066457392908073 / 6250000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w57S5 : Ball := ⟨(176001618569985552871883666203 / 5000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
abbrev w57 : Ball := w57S5

def w58Trace : List Ball := [
  ⟨(18993342510008965157996807914409 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19492339150256029858466747391331 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(24575134926490143605627622348733 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8226843974534312368338427230153 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(257749870020624385803960070629 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(826213168808936101721999982621 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(137870788321863373812578496193 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9856958170403147295755950101 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1233000125509347000647412697 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(274156681883793439386824853 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13714247668551055439896789 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1247235985804475592532897 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(41588253894113779264351 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(320000158048977260693 / 2000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1143138024886875270331 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(7622480718571368373 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w58S0 : Ball := ⟨(90186764925628414183244839196039 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def w58S1 : Ball := ⟨(81336525677505595400650712769709 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
def w58S2 : Ball := ⟨(66156304092875270549036552301127 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w58S3 : Ball := ⟨(43766565712289852736744340018473 / 100000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
def w58S4 : Ball := ⟨(19155122742481857846431324033341 / 100000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
def w58S5 : Ball := ⟨(1834593636397728454747038920243 / 50000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
abbrev w58 : Ball := w58S5

def w59Trace : List Ball := [
  ⟨(47490850333497063225222791199187 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(48734660148762694177943420003049 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49152833285294875792310473008321 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8227166055829557417397002741567 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(64439487423007444955437219973 / 1562500000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(6609878139123358026635461521 / 800000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(137873879501826688188413451901 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19714303290334388889693170837 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2466043294549164617000496577 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(137080495130981559087490183 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13714443656540082916746213 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2494504657815055209296589 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(207943785215461371537067 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(500005865205680103811 / 3125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1143150015280410839187 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(38112780723490100557 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w59S0 : Ball := ⟨(90215234615944724854377390667683 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w59S1 : Ball := ⟨(16277577113619902693988897045447 / 20000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w59S2 : Ball := ⟨(16559969793115152661081606612261 / 25000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
def w59S3 : Ball := ⟨(43877215927821809924352512727881 / 100000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
def w59S4 : Ball := ⟨(19252100775766999323332088448043 / 100000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w59S5 : Ball := ⟨(3706433842802882971598806391479 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
abbrev w59 : Ball := w59S5

def w60Trace : List Ball := [
  ⟨(23745721986418235040063525564537 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9746992425611869888708904941217 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49153036338039423011353197225847 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8227191568083800393618580206081 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(412413743494527404410296581619 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(826236478210584295321268381899 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(17234265544119328566469238221 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9857166970189822247008305211 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(493209340799113235150302207 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(137080665762452556026083311 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13714459180560793840576223 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(623626811713823131614597 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(51985996121200138648321 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(400005048176758740281 / 2500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(285787741256181832387 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19056405297611713989 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w60S0 : Ball := ⟨(45108745012501309613478321617419 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w60S1 : Ball := ⟨(81391955064114471007886683511533 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w60S2 : Ball := ⟨(6624650349158829282356100571561 / 10000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
def w60S3 : Ball := ⟨(1755439689944407948904349965131 / 4000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w60S4 : Ball := ⟨(962990157822537223162333237821 / 5000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
def w60S5 : Ball := ⟨(741880035250460119215556900671 / 20000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
abbrev w60 : Ball := w60S5

def w61Trace : List Ball := [
  ⟨(47501388534953300269537814793721 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(97480041307561207442823525984863 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4915643765920409755228575603303 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16455237834416701714075898042023 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2062154479563192563901550180923 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1291039273988281839238206127 / 156250000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(68939112861304702693835589537 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19714847341243848967641021711 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(308262976685646748636650017 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(137083523897039662404424099 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13714719212699751572800091 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1247275307008564790950161 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(207947322298974951602579 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16000440458772423459837 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(114316687346405953597 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(15245324378702664913 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w61S0 : Ball := ⟨(45127638254971856842853482232953 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def w61S1 : Ball := ⟨(40730074689431987531897548967777 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
def w61S2 : Ball := ⟨(16589389842067082155989944919349 / 25000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
def w61S3 : Ball := ⟨(11008314213283139561532904136561 / 25000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
def w61S4 : Ball := ⟨(2423659636367431757761013627173 / 12500000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
def w61S5 : Ball := ⟨(3759440661092295383471873933991 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
abbrev w61 : Ball := w61S5

def w62Trace : List Ball := [
  ⟨(47528858214889330796866284093103 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(975079837523245654924984235281 / 1000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(24582915603321281247896188877831 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16457598191952896288198718714391 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2062391316267656867034845239623 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(165268854428717758636608773077 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13788955151011146139477972461 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9858132532099534452817058763 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1233130758119768073808956527 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(34272854081060479329808381 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27430874517711581976877601 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1247335183198581220676033 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(103978269584235628996157 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16001099125565780445249 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(228642160385547388341 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(38114692514423055511 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w62S0 : Ball := ⟨(90359694528442120979839736544901 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def w62S1 : Ball := ⟨(81648743952733729761496727521473 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
def w62S2 : Ball := ⟨(33332586945295364025786775133681 / 50000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w62S3 : Ball := ⟨(11110613524656749271650130482569 / 25000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
def w62S4 : Ball := ⟨(19751317263085675720860399788449 / 100000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
def w62S5 : Ball := ⟨(780229067254132455715814614877 / 20000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
abbrev w62 : Ball := w62S5

def w63Trace : List Ball := [
  ⟨(47545421936966955357703772543871 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19504965983873212950950901066831 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49171494027989773930876477096503 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16459021048129646270146966049099 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2062534080327990032477781152897 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(103298996798327791683894613541 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(68948189190076979013423640479 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2464639952160245497992569979 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2466356572890534609400745163 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(274192347021515755240398659 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3428967515130745679599039 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(498948509321778855783489 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(12997630910451450940857 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16001496130276130884313 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(71452329954660684231 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(297777540538980917 / 390625000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w63S0 : Ball := ⟨(90422685886568743561901534002337 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w63S1 : Ball := ⟨(81762621229410782458913378811489 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w63S2 : Ball := ⟨(66851262303040947716324724355973 / 100000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
def w63S3 : Ball := ⟨(44690912715099836768584676428061 / 100000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w63S4 : Ball := ⟨(19972776793086722638461408240463 / 100000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
def w63S5 : Ball := ⟨(797823625652927097301574016557 / 20000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
abbrev w63 : Ball := w63S5

def w64Trace : List Ball := [
  ⟨(23773899633748285834342891427259 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4876362381314299440843583684777 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(24586153355346867344054947098783 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3291845048197923189222394441697 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4125109136008962874565139610877 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(82639881993942415314992902391 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(68948679034642606844686148877 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4929310562285235891208506761 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(616592553462081556088703937 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(68548428090499300896559693 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27431864337294614751865181 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2494752904623930413962481 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(25995361472138860409469 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8000776550535486118313 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1143241078809691529031 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76231289351845734121 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w64S0 : Ball := ⟨(18086345721457180138703585993191 / 20000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w64S1 : Ball := ⟨(81778975389018111482986147927459 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w64S2 : Ball := ⟨(6687800815677629978363765295201 / 10000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
def w64S3 : Ball := ⟨(8945335950035674573719685240601 / 20000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w64S4 : Ball := ⟨(20004758814750161148398130971519 / 100000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
def w64S5 : Ball := ⟨(2000951876181621361436192434079 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
abbrev w64 : Ball := w64S5

def w65Trace : List Ball := [
  ⟨(9510243377677640497502654733287 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(48765361610291567863323942170687 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49173474977496830386002676629551 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2057439846918089772847901849397 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4125168039269619443817574141333 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(41320433029607042478404406331 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13789876639377651408790006523 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(788696741392644063268214751 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2466389822963264683769266371 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(548391350121221231873241 / 200000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27432042899959735420054851 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(623691948602428190938919 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(207964037776272101552759 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8000817498626057520363 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(57162327034164723297 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9528954109597374933 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w65S0 : Ball := ⟨(2826397784458169257380700346193 / 3125000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w65S1 : Ball := ⟨(81802490224538089510148027126831 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w65S2 : Ball := ⟨(66916474069356496939633314159919 / 100000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
def w65S3 : Ball := ⟨(8955629003749720906388856281539 / 20000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w65S4 : Ball := ⟨(5012705678300201162274066253711 / 25000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
def w65S5 : Ball := ⟨(4020354914762092772069910934733 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
abbrev w65 : Ball := w65S5

def w66Trace : List Ball := [
  ⟨(47551959881956705690865568533283 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(97531478806505749367905636124189 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4917372895406873769112278637073 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(164595825882721575473548531727 / 1000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(257823802782008365677058632927 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(6611286399128735591032436627 / 800000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(137899072554609252077266035017 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19717456858160095849060834097 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(154149630365718900374048487 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(137098050868802318181104959 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27432081718212553055045309 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1247385515670693202310859 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(207964286908077149073553 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3200330560174664217323 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1143247728053655633021 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76231707556112318017 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w66S0 : Ball := ⟨(2826486110769024994277303864871 / 3125000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w66S1 : Ball := ⟨(81807603039950940464400969384321 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w66S2 : Ball := ⟨(13384967830284380711145555832811 / 20000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
def w66S3 : Ball := ⟨(1119733523860923514002452793301 / 2500000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w66S4 : Ball := ⟨(20060850631328021895619230251689 / 100000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
def w66S5 : Ball := ⟨(4024377280524538946645373010247 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
abbrev w66 : Ball := w66S5

def w67Trace : List Ball := [
  ⟨(2977179782453473397812534840737 / 3125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9761577581507318907552595562203 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49202059728280366029193834904747 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1029168763705070739117357360143 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4126609045456495602003266333541 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(82664939136844166590062919423 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(137933216958393807659067133979 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9860865371245155049268421987 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(308358685143729845689035869 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(34280460475004400007407933 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2743641058546971071609409 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2495131997883312138021689 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(12999504286408589280007 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4000909534162119431151 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(285845033621445844197 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(15248006860355467333 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w67S0 : Ball := ⟨(11345407305023630319987560487103 / 12500000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def w67S1 : Ball := ⟨(10297461353350684338801061672883 / 12500000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
def w67S2 : Ball := ⟨(67864134607200580774998759276317 / 100000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
def w67S3 : Ball := ⟨(2878462978740149703673265370137 / 6250000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
def w67S4 : Ball := ⟨(21211005747142695743872387933351 / 100000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
def w67S5 : Ball := ⟨(1124766912013301171239299207633 / 25000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
abbrev w67 : Ball := w67S5

def w68Trace : List Ball := [
  ⟨(19082821330318199585320912915309 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(24422278516357353606153297422207 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1969068031054686151308159498269 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16472889865697696014826522024229 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4127850906009227039598341471179 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(826856837330627124341902713097 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(137962902467446869741565602167 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19725446336136741255721724877 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(308410345181999771320849327 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(68571261897121492016318007 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13720086820641070007201857 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2495445777206777007665663 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(104008109038954811232033 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4001340970690280005509 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1143495226957679720021 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1906181768229397611 / 2500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w68S0 : Ball := ⟨(9103851748121181514200484868169 / 10000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w68S1 : Ball := ⟨(2072002916294227314594335673461 / 2500000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w68S2 : Ball := ⟨(68691137362108524219187127322263 / 100000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
def w68S3 : Ball := ⟨(47184723521000616231385852952577 / 100000000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩
def w68S4 : Ball := ⟨(278299766719158598857016608607 / 1250000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩
def w68S5 : Ball := ⟨(123921216249500953719648431323 / 2500000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
abbrev w68 : Ball := w68S5

def w69Trace : List Ball := [
  ⟨(47805475967628620661785892524933 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4889453022515866932835609343927 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(12315067987788540119270673609527 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3296264238547170023791648804949 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4129542326047783830579303423151 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(827139355825413928491295939083 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(6900166414392374410624773403 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3946101198722342439629516661 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2467845517883467567761858427 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(137170685050793006435373261 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13722648711830320958904593 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2495873009857587127547621 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2600613733426562216213 / 1250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16007713521874603893429 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(22873038514246720151 / 2000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76257120933240621567 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w69S0 : Ball := ⟨(91414541299660704198725016189483 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w69S1 : Ball := ⟨(83566183610273725499229779212341 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w69S2 : Ball := ⟨(34916535215929905113774121060627 / 50000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
def w69S3 : Ball := ⟨(48766577259410929021170803306349 / 100000000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩
def w69S4 : Ball := ⟨(2972723821997618945998689143511 / 12500000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩
def w69S5 : Ball := ⟨(1413933907499541000335628042367 / 25000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
abbrev w69 : Ball := w69S5

def w70Trace : List Ball := [
  ⟨(23988643056420943153627345028999 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(97963365074818779625184332580213 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(12329697984373047030553815398463 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4124003556746373318913244730551 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(516561170475382015251996653563 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(165526306956076647443670213961 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138073747545804287471665543849 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9869659456925061618353717987 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2468825666828844875161893181 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13721973080946273948484527 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13727110321945469669016939 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(249661702148279697661669 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13006647336448448126711 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16011805105139227720451 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(285981197517193258563 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2383570853380330041 / 3125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w70S0 : Ball := ⟨(9207279931013963668074302339549 / 10000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w70S1 : Ball := ⟨(42387001864026249781323766839769 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w70S2 : Ball := ⟨(8983289635104823867779004419503 / 12500000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
def w70S3 : Ball := ⟨(1291191882690908152877607516607 / 2500000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩
def w70S4 : Ball := ⟨(1667176477926891920883717605763 / 6250000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
def w70S5 : Ball := ⟨(711546216589495384139900600903 / 10000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
abbrev w70 : Ball := w70S5

def w71Trace : List Ball := [
  ⟨(95959969822177445516881420373721 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19593220276637251310543636273393 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(6164963791349959299153013702223 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16496244772788557130169736089797 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4132535599666203287160821778373 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(206909813968633377067221692379 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138074852181710606647436852309 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19739457151293927728159110799 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1234420520300546862360887113 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(274441000147285938141404273 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13727180298690936344259997 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2496628690431989428404801 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208107255400930831063619 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3202373854886534961759 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1143929069409368619791 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76274536153770508103 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w71S0 : Ball := ⟨(9208315808273206044574012068141 / 10000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w71S1 : Ball := ⟨(84793080024894227942258697448883 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w71S2 : Ball := ⟨(7189866420108116523512076811799 / 10000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
def w71S3 : Ball := ⟨(10338835827799660624740986449977 / 20000000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩
def w71S4 : Ball := ⟨(13361440784274236720333260465431 / 50000000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩
def w71S5 : Ball := ⟨(892640499158334650275688313439 / 12500000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
abbrev w71 : Ball := w71S5

def w72Trace : List Ball := [
  ⟨(23991266957747227188395351906009 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(48984342884159080346521095652661 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49320577725876442826093461989991 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8248231257617447386095533335971 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4132579267663189516460563626239 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(413823274066265338819870743841 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(69037947731585030613808968791 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2467448463807663906129826797 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(308606945054152345089435761 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(274442453216256107188834579 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27454492776880442183417903 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2496639711198718473736729 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(41621620707084323470757 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1601192987920628098647 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1143933111036591383211 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(38137395031751895591 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w72S0 : Ball := ⟨(92092942438063023001312190166579 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def w72S1 : Ball := ⟨(21202775117250973327770577567139 / 25000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
def w72S2 : Ball := ⟨(71929227627634724119557177897881 / 100000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
def w72S3 : Ball := ⟨(6467267233885113103101692122031 / 12500000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w72S4 : Ball := ⟨(3346043637958720178252837876849 / 12500000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
def w72S5 : Ball := ⟨(7165445137359377199444462265751 / 100000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
abbrev w72 : Ball := w72S5

def w73Trace : List Ball := [
  ⟨(95967916836229853535076487075841 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(97970130023268554956379964747981 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49321062456648626724252944620047 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8248292098422150654482069915909 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2066301835351439425391366254809 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(827650623265915040460055448399 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27615295695882364760044391481 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19739660670665210962294462777 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2468863674524046956338516371 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(54888653046296503649590813 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(5490913328480550475901607 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2496645869901613316307581 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(104054288747864069219497 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16011963746766319893253 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(228787073920946180177 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76274931954237096433 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w73S0 : Ball := ⟨(92098410618855293807734146738343 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w73S1 : Ball := ⟨(84821172385192775425321959084731 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w73S2 : Ball := ⟨(17986578211996473658476720834171 / 25000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
def w73S3 : Ball := ⟨(3235169957762662633087786445653 / 6250000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩
def w73S4 : Ball := ⟨(83730597244880546602927167977 / 312500000000000000000000000000), (19 / 100000000000000000000000000000000)⟩
def w73S5 : Ball := ⟨(448692026559001458013779811137 / 6250000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
abbrev w73 : Ball := w73S5

def w74Trace : List Ball := [
  ⟨(47984033393108529270609571842997 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19594041207495216474579505987047 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49321087968993024843220351624949 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16496590601179395585974219219891 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4132604955080052076508841107719 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(827650837747573472835276879389 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(69038254582298316541177161709 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19739664510689233311140206579 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2468864101582789535239777061 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(68610826992311771838758763 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(5490914106014383759022057 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(499329238808929638681057 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(41621720488212595952411 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3202393105854636996311 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1143935488476971616837 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(595897964235706471 / 781250000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w74S0 : Ball := ⟨(92098698426838177469564281446487 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w74S1 : Ball := ⟨(84821702519176849854704396425933 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w74S2 : Ball := ⟨(1438944243650346471378712129703 / 2000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
def w74S3 : Ball := ⟨(51764013408361691782861867910389 / 100000000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩
def w74S4 : Ball := ⟨(6698782710352622527648452827991 / 25000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
def w74S5 : Ball := ⟨(224368449002596137414301240859 / 3125000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
abbrev w74 : Ball := w74S5

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
open scoped BigOperators

def w204Trace : List Ball := [
  ⟨(103525730532585083765635802348327 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(50876342461545220283344911231277 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(12645634365731894420561489628819 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16812047992137884047502410253269 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4195709248808582419501979411331 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(419084879392723706137269042773 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(139579378127390445633614782483 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3985507870138855669413527241 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2489740531729785778538711783 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(55306213974347011881980101 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3455547012540234070444851 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(39257249430006272998507 / 1562500000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(20932539613938223374423 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(643955279308795327133 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(287432510088517885517 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3831862310388269383 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]

def w205Trace : List Ball := [
  ⟨(5177200545407457936725894863887 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(101761720185538229175443234678713 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(10117106364076151216148505490391 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2101599247631588965830777341127 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4195858100725417846781520925281 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(838194526340381141976164274447 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(34895727988139861943243329813 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4981995162963319191238227741 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1244894763636742717740821001 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138267983163070956995587373 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(5528964199570413908071197 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2512501021775516541394697 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(52332061421111141025519 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16099085454201065924189 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1149743601007171603473 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76638090084231887307 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]

def w206Trace : List Ball := [
  ⟨(103545628795959314165950669719991 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(20352503963531647752889623936447 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(50585796820542302760069805669789 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8406430000158611741438531518567 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4195871273884764445699523615369 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8381967182197667420524887739 / 1000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(139583224687985182306806671269 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3985603941177880510044223719 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1244896931622925230797416981 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138268199824139957697478547 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(5528972073989377787395821 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(157031518832231551947237 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2616606223250532723649 / 1250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8049551730378985243373 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(35929525033728765733 / 3125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3831908238178260293 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w206S4 : Ball := ⟨(152470785229281034202046247661839 / 50000000000000000000000000000000), (161 / 100000000000000000000000000000000)⟩

def w207Trace : List Ball := [
  ⟨(25895388104022644530724097899391 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(25445068450534723132339712073629 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(50591680359171050077246254983811 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16814325734624219592274019343683 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1049040933937590164609761037369 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(838245380469968240056906398379 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(139590167729956054486335492629 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9964443370254117986897260201 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1244945062665348131301459951 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(276546019717521712116120507 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1105829378276622846144099 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(314072138642797392816147 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(6541690509486492628183 / 3125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8049751607999990192331 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(574885721641004008983 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(38319911322382438867 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w207S0 : Ball := ⟨(10729138000927319882225079156397 / 10000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w207S1 : Ball := ⟨(14389300280367835746741645602973 / 12500000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w207S2 : Ball := ⟨(66256628018750040456736781907719 / 50000000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩
def w207S3 : Ball := ⟨(4389940756415012911405482122683 / 2500000000000000000000000000000), (23 / 50000000000000000000000000000000)⟩
def w207S4 : Ball := ⟨(77086319379334462897050088564097 / 25000000000000000000000000000000), (81 / 50000000000000000000000000000000)⟩

def w209Trace : List Ball := [
  ⟨(12959554713508152279185215440391 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(50913578854064562025107176500673 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1581475490655752845643617086897 / 3125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(525568616422807859605960774401 / 3125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4196935892692184102800449779973 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(838373854517296019631332172769 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(139608497759818203605801585627 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19931175721416082521492444377 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(311268031838806428012894919 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(276571416155347290376093749 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3456005246854663437124877 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1256384657136512321865361 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(209348875512432180046181 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8050279257384380547259 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(287460443655318268061 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(38322099426848672467 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w209S0 : Ball := ⟨(107488037358343274815059916710221 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w209S1 : Ball := ⟨(115536781751485994924545595743119 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w209S2 : Ball := ⟨(133487479374905072050598726075087 / 100000000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩
def w209S3 : Ball := ⟨(35637814299731414010498763636029 / 20000000000000000000000000000000), (23 / 50000000000000000000000000000000)⟩
def w209S4 : Ball := ⟨(79378363003883803422826157257159 / 25000000000000000000000000000000), (33 / 20000000000000000000000000000000)⟩

def w210Trace : List Ball := [
  ⟨(51893245148916510458043424523677 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(25470379536419883400903718472069 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1582038296207461198700810466893 / 3125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16822681675305026040216865465753 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4197830889117548098550711822711 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(83852275996653983039556461231 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(69814871042885691579669102517 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19933828554813601828283962531 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(622609693391141400438528143 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(276600848387063126853210251 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27650716144400109715282851 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(125649602844320609064871 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(104683001325018801543213 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(503180670441951815627 / 3125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1149923277782722628013 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19162317395107418669 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w210S0 : Ball := ⟨(107716355683421877826589855435717 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w210S1 : Ball := ⟨(116028132817174526805366257070471 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w210S2 : Ball := ⟨(134625276050398923941953560270113 / 100000000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩
def w210S3 : Ball := ⟨(45309912379115285235292658989 / 25000000000000000000000000000), (23 / 50000000000000000000000000000000)⟩
def w210S4 : Ball := ⟨(164239052784248365396833507609001 / 50000000000000000000000000000000), (21 / 12500000000000000000000000000000)⟩

def w211Trace : List Ball := [
  ⟨(103804167939780837402223169024839 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(101890248230162625546048469382577 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(12657029371250055968518732003029 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8411700991842295028415022551883 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4197974592654152320760083688793 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(419273334002737363879198454921 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(69816576484002771124517450627 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4983563618274305822279220691 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(622621514642440807034863683 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(276605573679061076457394481 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27651145473504446803332271 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2513027817195059070766647 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(104684376157518386426437 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16101977788981006858953 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(287484090625769471841 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(38325041792581423451 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w211S0 : Ball := ⟨(107753052816702238613884623658711 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w211S1 : Ball := ⟨(14513400489148777798448977633907 / 12500000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w211S2 : Ball := ⟨(67404414002695674453294593824097 / 50000000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩
def w211S3 : Ball := ⟨(45433550270467967137254515929207 / 25000000000000000000000000000000), (23 / 50000000000000000000000000000000)⟩
def w211S4 : Ball := ⟨(330273198428662382369686571479973 / 100000000000000000000000000000000), (21 / 12500000000000000000000000000000)⟩

def w212Trace : List Ball := [
  ⟨(104599190331904000628813745749773 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(102282361957695475795426967817593 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(50757928032702220761458732478273 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3371144213839886630993041810373 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4204420655395460160923869849437 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(41980945142865793878327258623 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(139786103806686646370685142859 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19953351427846437846605133823 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2492605997950580621616267583 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(276817408672746412089431721 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27670391168531640866962909 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1257315388652445222384767 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(20949200107234286778673 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16110777814427754415279 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1150522818400496287701 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76686549503622296281 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w212S0 : Ball := ⟨(2735247654522469839306770641499 / 2500000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w212S1 : Ball := ⟨(119705275705130760332354839999003 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w212S2 : Ball := ⟨(143293530316413686502966442062081 / 100000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
def w212S3 : Ball := ⟨(205330358305409682587644549156297 / 100000000000000000000000000000000), (13 / 25000000000000000000000000000000)⟩
def w212S4 : Ball := ⟨(421605560418279230180499175283079 / 100000000000000000000000000000000), (107 / 50000000000000000000000000000000)⟩

def w213Trace : List Ball := [
  ⟨(26157275859831324365744712686873 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(102297096135084782165894288125237 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(50762802612280673532417540836009 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8428467108518888518131731208281 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2102331277191924252303948066939 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(839659132591981502102374193413 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(139791841633052312150345307513 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9977033877707794746937397177 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(155792844371048270478953783 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(55365070667083236885364113 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27671112915875068429899469 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2514690888058899122923109 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(41899324535930645125891 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4027776946775240287859 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1150544807802969279649 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76687916135422025799 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w213S0 : Ball := ⟨(13684061608146290988157528392871 / 12500000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w213S1 : Ball := ⟨(11984226694114768349011650235349 / 10000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w213S2 : Ball := ⟨(143621689455932989459716626308857 / 100000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
def w213S3 : Ball := ⟨(103135948410882266209611447706969 / 50000000000000000000000000000000), (13 / 25000000000000000000000000000000)⟩
def w213S4 : Ball := ⟨(212740477092243365053150468547347 / 50000000000000000000000000000000), (43 / 20000000000000000000000000000000)⟩

def w215Trace : List Ball := [
  ⟨(4187139477920639001521954579241 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(25580354429913406215624451251207 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2030833941261415319001599566811 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4214734136816501247527535360147 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2102530902224251221744589674839 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(52482845616424531760260647249 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(139801311514672859643088353773 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9977624995758146510741508493 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2492816736415580119971232367 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138419232552779537202049137 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(5534460814325991472207583 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2514790093025414121162599 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(20950425000837357552979 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16111652359746262246549 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(5752905490170948669 / 500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4793135715705515381 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w215S0 : Ball := ⟨(54787928148629754201638919915641 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w215S1 : Ball := ⟨(120068682832776662632199403468457 / 100000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
def w215S2 : Ball := ⟨(72082442985989586293653180480559 / 50000000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩
def w215S3 : Ball := ⟨(25979392934142196527039824898701 / 12500000000000000000000000000000), (29 / 50000000000000000000000000000000)⟩
def w215S4 : Ball := ⟨(215977234312498395921809841175079 / 50000000000000000000000000000000), (121 / 50000000000000000000000000000000)⟩

def w220Trace : List Ball := [
  ⟨(107084875445820695299160640798929 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(51751013322893069819703829251007 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(639508164219432470845289050563 / 1250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8477915588519967441379618215731 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4224366834186848782196458478141 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(421467132471827180933903528311 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(28051752975897456057263041407 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(5003085176464713268693896309 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2499152076901265839392861109 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(277471339570016106830320771 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13864894100534230352649571 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(629894230254313233324011 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(52468058976305529150023 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3227584546491913337963 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(115233155763175004841 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(38399400004766706569 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w220S0 : Ball := ⟨(22934341098493864111607004013547 / 20000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w220S1 : Ball := ⟨(65748000202758092698444430463227 / 50000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
def w220S2 : Ball := ⟨(172911981226475127943419719316139 / 100000000000000000000000000000000), (11 / 50000000000000000000000000000000)⟩
def w220S3 : Ball := ⟨(59797106503329774182282605479647 / 20000000000000000000000000000000), (77 / 100000000000000000000000000000000)⟩
def w220S4 : Ball := ⟨(893923486542640993202223535508217 / 100000000000000000000000000000000), (461 / 100000000000000000000000000000000)⟩

def w221Trace : List Ball := [
  ⟨(1339268057276728021287355743117 / 1250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(103529674328232375697388589204029 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(51169763971928340460930461652633 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16958093234741610868133632130949 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4224817169183960154458012937249 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(421504537239991756930953554861 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(140269425642877557666143042301 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(20013670748924004291178521387 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2499299633013892986065666731 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(55497215336508526036764087 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3466390817375991407338651 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1259844175301900332267297 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(209880800918803626493431 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16138534117346308669933 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(72023268194617138687 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(38400662085499790113 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w221S0 : Ball := ⟨(28698222867868499965608344436317 / 25000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w221S1 : Ball := ⟨(65887039661908040866861959994153 / 50000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
def w221S2 : Ball := ⟨(21705509977049216220696550478549 / 12500000000000000000000000000000), (11 / 50000000000000000000000000000000)⟩
def w221S3 : Ball := ⟨(301522664552821162795341339417369 / 100000000000000000000000000000000), (77 / 100000000000000000000000000000000)⟩
def w221S4 : Ball := ⟨(909159172390331157488692529352999 / 100000000000000000000000000000000), (93 / 20000000000000000000000000000000)⟩

def w222Trace : List Ball := [
  ⟨(107293056450183004216559407785969 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(25900937406314496019033677655931 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(5119417029577177059234251085819 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8482076148605313627577099232459 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1056505835191194489878475710739 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(168641886809869605887557279701 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1402979769654933300819045039 / 1000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(5004308182915532959302548207 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(156230924613593684958645997 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138762771260011013819957181 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3466838817656256972993287 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(251998674973509908747547 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2623796713296139566769 / 1250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(403504283054310769571 / 2500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(576240684370531357171 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76808082650664909263 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w222S0 : Ball := ⟨(28779499906055391914939566548151 / 25000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w222S1 : Ball := ⟨(1325215383748227699292153438721 / 1000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w222S2 : Ball := ⟨(87809790666148120186858229318343 / 50000000000000000000000000000000), (19 / 100000000000000000000000000000000)⟩
def w222S3 : Ball := ⟨(1927639834208188382189720445229 / 625000000000000000000000000000), (67 / 100000000000000000000000000000000)⟩
def w222S4 : Ball := ⟨(190248720917820006042275069622991 / 20000000000000000000000000000000), (207 / 50000000000000000000000000000000)⟩

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
open scoped BigOperators
def w25Trace : List Ball := [
  ⟨(45785468331137255202533763683031 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(47861811840303724011256853624459 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(48564143026673881496047046644407 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16306133560378945321348040094747 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(127948437180680440527584133693 / 3125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(82125546891779481619958138679 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13716078546995263974734271041 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9812497232940587076704824921 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(245610476699458716935617857 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(273165881628424891747947021 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3417290952422478213679 / 12500000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(621737822715778105260329 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(41472462615792647231503 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(15958626442958377566447 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(142547226720472755973 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(38025387233674064031 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w25S0 : Ball := ⟨(83852364412062900520750723805037 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w25S1 : Ball := ⟨(7031219017493392820519392477101 / 10000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w25S2 : Ball := ⟨(49438040871960752254217876879899 / 100000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
def w25S3 : Ball := ⟨(12220599426288309285318903017743 / 50000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
def w25S4 : Ball := ⟨(2986861006755963080988808702703 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w25S5 : Ball := ⟨(1393959167762382083395885227 / 390625000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
abbrev w25 : Ball := w25S5

def w27Trace : List Ball := [
  ⟨(18345749238798680348872437662081 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(95804872694180021059257238957191 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(24295810943323438321889519920711 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2039132896591194637450262654039 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(102393598707672803290857620257 / 2500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(164297751294903183192932957207 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(137194215615939970245554534893 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19629183311385744592861811947 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2456571092153000203910179393 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(68303146938082179954332607 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1708911201020875743470347 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2487305985036420974053119 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(103694811642239278688771 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(997536174179196014449 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1140508053188296877213 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4753687758117489537 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w27S0 : Ball := ⟨(84141628783220589862025521274081 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w27S1 : Ball := ⟨(17699534235733239104141844647297 / 25000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w27S2 : Ball := ⟨(25061880972951441318234900707649 / 50000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
def w27S3 : Ball := ⟨(25123915116095419316951877996989 / 100000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
def w27S4 : Ball := ⟨(6312111107607679070950604701523 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w27S5 : Ball := ⟨(39842746634784241075846779823 / 10000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
abbrev w27 : Ball := w27S5

def w28Trace : List Ball := [
  ⟨(45866093043236628690910415303721 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(47903321606528293279328882955251 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(6074027574786765803139212876333 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16313214142526871047025711989409 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2047887157789871415627475950069 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(102686729801808923283309457221 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(68597471918084791986138985711 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19629274556225876274325315563 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(614145312457620845239049149 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(273213605107331844565195833 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27342671823598038287914353 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2487313710813425916558001 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(103695109068236601540959 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3192124262223369525681 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(142563861241741040721 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(38029591680139898559 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w28S0 : Ball := ⟨(42073969821016789339138735730677 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w28S1 : Ball := ⟨(17702189364998315603374756844111 / 25000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w28S2 : Ball := ⟨(50138801330281514913431737642841 / 100000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
def w28S3 : Ball := ⟨(25138993988374394095320513350287 / 100000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
def w28S4 : Ball := ⟨(1263938037495047851933900678061 / 20000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w28S5 : Ball := ⟨(399384840656708247408468632317 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
abbrev w28 : Ball := w28S5

def w29Trace : List Ball := [
  ⟨(91739926316210653627319546008753 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19162125408239748000998588351451 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(48593567740191503494354742557579 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8156776916389714401306408249503 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4095842643320143413702771264727 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(205376318244231558543991306191 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(137196582356469179728787688201 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19629479859877734204450638683 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1228302052440812326464440527 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(273215894181302082659448183 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(6835720048011668453313061 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(248733109397380703848137 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(51847889141263851018821 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(15960716991452349912337 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1140517272660747421257 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9507448328584964663 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w29S0 : Ball := ⟨(42081070402518800141765154629049 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w29S1 : Ball := ⟨(35416329724434875443692865171559 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w29S2 : Ball := ⟨(25086328222997786007631674697119 / 50000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
def w29S3 : Ball := ⟨(12586477274239505117010599071759 / 50000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
def w29S4 : Ball := ⟨(6336776406997900900023143790749 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w29S5 : Ball := ⟨(200773676161426132972907255303 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
abbrev w29 : Ball := w29S5

def w30Trace : List Ball := [
  ⟨(9174609029957902154437624677593 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(95813799507906811013353201592599 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(48594640504591459769175466249557 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16313824334998381146095833716349 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4095897053809927505583463410353 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(821514378472295414601964051309 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(68598943564328695954114055969 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2453705418143757068413874741 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(614155576137078620877577969 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(273217716987394702640922623 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27343046117154707456085543 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2487344936280580518780713 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(103696311181129900274599 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(15960793182115268812837 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(285130588812785914949 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(38029953874906493541 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w30S0 : Ball := ⟨(5260840678286567396995096506637 / 6250000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def w30S1 : Ball := ⟨(70851698284325556537044168218429 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
def w30S2 : Ball := ⟨(25099815748865505058650902693233 / 50000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w30S3 : Ball := ⟨(3150003753134984172534741405573 / 12500000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
def w30S4 : Ball := ⟨(6350415132649271237874106001737 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
def w30S5 : Ball := ⟨(403277723569808612119577416691 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
abbrev w30 : Ball := w30S5

def w31Trace : List Ball := [
  ⟨(9174981756020691082646111016973 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(23953929453007680834852602624769 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(24297644585082993655772744665753 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16313987897976085081947607887131 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2047964976881087831130324812663 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(821519884204805974192950196127 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(68599338035617161611457780427 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19629742197886330706134065403 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2456633309115843010372744673 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(136609409579978722746157443 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13671573222430317938604133 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1243676653058259896414193 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(41478653360543430755323 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(7980419625608861396111 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1140525428466270284883 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76060101916079615319 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w31S0 : Ball := ⟨(84180290223312524147580341691057 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w31S1 : Ball := ⟨(35431606310405630683095576824341 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w31S2 : Ball := ⟨(12553987257355761094415622365359 / 25000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
def w31S3 : Ball := ⟨(25216415369256131926525881604669 / 100000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
def w31S4 : Ball := ⟨(6358676040748568642581432429083 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w31S5 : Ball := ⟨(10108190247797473146079027821 / 2500000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
abbrev w31 : Ball := w31S5

def w32Trace : List Ball := [
  ⟨(91777059830869566146310164777577 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(95829737754128551566208906938669 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(24300014907567119449590286789627 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8157591622940866257483410503829 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(102404259747599949509214460807 / 2500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(821560120329004847875456962459 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(137204441662330984814190093407 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4907616152544105685886105889 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2456713729806578233151512699 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(34153359217949888855758371 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13671939814686428928054917 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(248741447188194893614711 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(207397976288265609359303 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(498786747424433393229 / 3125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(570273943527846115787 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4753845051463291739 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w32S0 : Ball := ⟨(16846057422398024154745714396681 / 20000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def w32S1 : Ball := ⟨(7094741266968289040413426507439 / 10000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
def w32S2 : Ball := ⟨(12583838411305700795452735287839 / 25000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w32S3 : Ball := ⟨(12668239132948222699622097750127 / 50000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w32S4 : Ball := ⟨(641937130918242948973223227793 / 10000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
def w32S5 : Ball := ⟨(412083280051545387456384844737 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
abbrev w32 : Ball := w32S5

def w33Trace : List Ball := [
  ⟨(92020591576467497480895303966263 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(47977503157219909549116001781171 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9728475446754160113983268710099 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16325859536398933414508185259267 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4098317644752058048165725949081 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(821919430776376164307360990109 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(34313981494394074597538094283 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1963691518836658310049355563 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2457431800569046586545481959 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(273298790654017891399882257 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2735042586456943087206551 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(621990144992269308706891 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(51860005862632096887009 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3192836339105486316309 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(285187099210260665067 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(15214837287668698879 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w33S0 : Ball := ⟨(2646184148150950297900240566277 / 3125000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w33S1 : Ball := ⟨(35851727595137896831497085625209 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w33S2 : Ball := ⟨(12853463715559721633031132752789 / 25000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
def w33S3 : Ball := ⟨(264338447179536519402633134261 / 1000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
def w33S4 : Ball := ⟨(349374073286443092347940913209 / 5000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w33S5 : Ball := ⟨(97649794467808727035744116141 / 20000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
abbrev w33 : Ball := w33S5

def w34Trace : List Ball := [
  ⟨(46025539223268144597868685783973 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(95970680341390611306157109104387 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(24323837287158867023141826606731 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16327194861941372415598519937827 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2049293091967291598441905209091 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(41098218178548379200728177319 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(137262363898848866494607776981 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4909430444007688941217112287 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1228760793006986768120557299 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(10932311307622659090334279 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13675622173094707795076111 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(497605771811368031614489 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(207445280459776649945677 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3991139373025229214431 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(14259668316051650349 / 1250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19018942410052461929 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w34S0 : Ball := ⟨(2647937825990743053927941776291 / 3125000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w34S1 : Ball := ⟨(71798525238400846240616401987417 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w34S2 : Ball := ⟨(12887570566023208236227672488123 / 25000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
def w34S3 : Ball := ⟨(6643579003769110236807743691499 / 25000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
def w34S4 : Ball := ⟨(3530971358345741060007047842373 / 50000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w34S5 : Ball := ⟨(498710349338318708978337091987 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
abbrev w34 : Ball := w34S5

def w35Trace : List Ball := [
  ⟨(18458259894357045168789359147261 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(96094122398423393776398019687287 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(24344692010372100106204275336829 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16337707226655341034621989615683 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(820140011325250402246131990531 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(25697438709964611299354011029 / 3125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(17164129431784767346183331693 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19644070005470872722195333573 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(614557054358796432156557193 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(273378550146441153590993037 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13678842833090141194477119 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(99542647782933163519193 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(207486650850964829205643 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(7983757403813158833417 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1140970738493407546359 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76088226153007382339 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w35S0 : Ball := ⟨(5323552473869214941796088409629 / 6250000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w35S1 : Ball := ⟨(72550940011619938395365810290319 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w35S2 : Ball := ⟨(52636388965696749067867853291607 / 100000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
def w35S3 : Ball := ⟨(27705894433481224811200724774167 / 100000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
def w35S4 : Ball := ⟨(119940091618625924863213570383 / 1562500000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w35S5 : Ball := ⟨(294617611826880119373906560639 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
abbrev w35 : Ball := w35S5

def w36Trace : List Ball := [
  ⟨(92586525998389445044635539543647 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(96245681502540827462791948639183 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(48740569170007716976959102398173 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8175302058898727455485876069223 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4103292924037883109413256345447 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(411375897949383092705262040091 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(137375174110452454928249630137 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9825927117261879372062454119 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(614773659236326837629426871 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(273465315467281929041702281 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13682791391456534775720459 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1244612474254067232432973 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(103768683926648113365213 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3194228031102291658609 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(114121256949713037431 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76103490608737694551 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w36S0 : Ball := ⟨(85722647964504446235040329722281 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w36S1 : Ball := ⟨(9185465467557947849178136547819 / 12500000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w36S2 : Ball := ⟨(13499644136911927918613872157633 / 25000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
def w36S3 : Ball := ⟨(14579231345860847300381800125667 / 50000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
def w36S4 : Ball := ⟨(1700431893089051943325687998351 / 20000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
def w36S5 : Ball := ⟨(361433577879302122267148370717 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
abbrev w36 : Ball := w36S5

def w37Trace : List Ball := [
  ⟨(92855706800378760617807057200151 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(96383727476498096599917439067083 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(48787166994270920045802799322649 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3272468322125724280386215702291 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4105652224211070415286503074173 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(205786605807361036717177318219 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(17178962632246356735384911921 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4914733720080220934874996591 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(614970672902742571609969779 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27354422881102717733887631 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27372764907614129292059377 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(311228004589913548764421 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(20758348970072370685511 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1996804617225966714291 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(35669764967170844691 / 3125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76117366028868281679 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w37S0 : Ball := ⟨(86221822853979064097491013843017 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def w37S1 : Ball := ⟨(7434202736262946441961163601171 / 10000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
def w37S2 : Ball := ⟨(27633685161929740006283718065239 / 50000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w37S3 : Ball := ⟨(7636205556286558811523252697899 / 25000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
def w37S4 : Ball := ⟨(4664930823828937049074508328179 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w37S5 : Ball := ⟨(870463183644373012431832467149 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
abbrev w37 : Ball := w37S5

def w38Trace : List Ball := [
  ⟨(3717526112806951492682521512867 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(96425981845678055025061462186169 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(48801425588659187641839606597939 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16365932522415137488482255068569 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2053186963377980777431924033867 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(205816781927264574864009213143 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(137448989770562217180554024599 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(614409386753716246009201549 / 3125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1230061847374599373066128043 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(5471367225832648786097029 / 2000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27374961209808602787692069 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(498001446836910812714729 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(207597593184600305438383 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(399386125862280507339 / 2500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1141499722460633563029 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19030401953750193871 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w38S0 : Ball := ⟨(86375002496259768968627950073201 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def w38S1 : Ball := ⟨(74606410562288813206433125464533 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
def w38S2 : Ball := ⟨(27830582484943998945769191245379 / 50000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w38S3 : Ball := ⟨(3872706607256358456534840867853 / 12500000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
def w38S4 : Ball := ⟨(1919725627633542992106409058239 / 20000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w38S5 : Ball := ⟨(184267324269650028245362054147 / 20000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
abbrev w38 : Ball := w38S5

def w39Trace : List Ball := [
  ⟨(92969524740464356854824235453609 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(48221028465360750325929582142219 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(48806849519627898034725856991957 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16367298412563396372852888761067 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4106648432667302283588422668181 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(411656518696744241454036641633 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(137455565352067394109236567211 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19661923985976994083752778351 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(15376345968736228579015453 / 625000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(273577539449094311351820811 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1368789825409217566393231 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2490076907362237012181489 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(5190073923715739903109 / 2500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(15975828426382851727671 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(228305059182545227313 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(38061610444300228113 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w39S0 : Ball := ⟨(21608331326169535349514390800001 / 25000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def w39S1 : Ball := ⟨(74707197232243147245372973033227 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
def w39S2 : Ball := ⟨(55811653182972781602570515121739 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w39S3 : Ball := ⟨(6229881262032871647947875606787 / 20000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
def w39S4 : Ball := ⟨(1212856891844633924100129454253 / 12500000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w39S5 : Ball := ⟨(47072698883040833028730637789 / 5000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
abbrev w39 : Ball := w39S5

def w40Trace : List Ball := [
  ⟨(93326543252452916137773690035279 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(96624865807658786295299723483579 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(48868510092266792701872697400777 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1638282297066315259041386506273 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4109768006928397104243994084417 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(823834718621160127381350451101 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(68765139765065515239910463651 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4917820401820219570401200261 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2461256724875261582537894903 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(5473636207148947451721121 / 2000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(5477057168197736397859693 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(124543420114716013399469 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(12978993031855218782707 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(15980183615184677888437 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1141815796743122370283 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76141539729063497251 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w40S0 : Ball := ⟨(87098436754519649305471352811581 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w40S1 : Ball := ⟨(75861376850810593408499833334373 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w40S2 : Ball := ⟨(1438737124425175346642330190289 / 2500000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
def w40S3 : Ball := ⟨(33119432211187559792456839434591 / 100000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
def w40S4 : Ball := ⟨(5484483949957240480923011121351 / 50000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
def w40S5 : Ball := ⟨(1203182567893542988313075989517 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
abbrev w40 : Ball := w40S5

def w41Trace : List Ball := [
  ⟨(93505493257699602905292027424193 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(48358203591216657443841940251731 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(6112421477227634237371778660719 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16390590948308653775514083607563 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4111328642710541938236531036543 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(206023916441268534736171370527 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(137567648075341688587458692853 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4918990370615042075317185539 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2461777495304139517089019891 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(136866975834628753843178251 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13695015417731934767063961 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2491264162651096328062507 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(103847177163630301137033 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3196472230589389480371 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1141961040575833172559 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19037673853832087959 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w41S0 : Ball := ⟨(43716386346828529487681060020413 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w41S1 : Ball := ⟨(76444897409007034483268951842813 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w41S2 : Ball := ⟨(3652388962421006508740400469151 / 6250000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
def w41S3 : Ball := ⟨(34150259540005879027416158398401 / 100000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
def w41S4 : Ball := ⟨(11662402266497625522242092043533 / 100000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
def w41S5 : Ball := ⟨(272023253251217905585357692917 / 20000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
abbrev w41 : Ball := w41S5

def w42Trace : List Ball := [
  ⟨(93649953839738500117011901122889 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(96790262517084879611136117017981 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9784852763006940310912094448377 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8198427626676562411656875359551 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4112587037264617980038730266771 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(824306059286252249258819089577 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(137597775319898394962587310759 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2459966788588156475757984433 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(307774664312831216113926603 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(68443996022026978446207131 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27393855795004176290287403 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(311447897459682504086723 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(207718911943783478120247 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(15984116374545286033777 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(285519528537024161627 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(38079036866730112431 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w42S0 : Ball := ⟨(10962892317731439802072583324959 / 12500000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def w42S1 : Ball := ⟨(76918405100912012840008993922001 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
def w42S2 : Ball := ⟨(29582205216340035780846291658461 / 50000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w42S3 : Ball := ⟨(7000854923693244985245369826549 / 20000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
def w42S4 : Ball := ⟨(1531624051956248470783775251121 / 12500000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w42S5 : Ball := ⟨(1501358231379761225653256402091 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
abbrev w42 : Ball := w42S5

def w43Trace : List Ball := [
  ⟨(18768602587146882807725460765333 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(48444451944061654970230213313679 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(24478749835272702705991233814737 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8202608935959436148650365344681 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1028566686984192257156374634097 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(41229343480617762904287685491 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(68818991657560464205199889949 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19684769294602771237596010681 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1231378778791797647368648421 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(273832073963273001117079139 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1712434990495112277840229 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2492008868478492563381839 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(103875840202050172595989 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(15986458414841714877769 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(228446865341213778407 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(38083958234795805067 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w43S0 : Ball := ⟨(88065110768564165664786346892799 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w43S1 : Ball := ⟨(38777318673397380866730711376171 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w43S2 : Ball := ⟨(60147217739928528397467895558911 / 100000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
def w43S3 : Ball := ⟨(4522109752317966339400693332341 / 12500000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
def w43S4 : Ball := ⟨(13087665031685925678415575616303 / 100000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩

def w45Trace : List Ball := [
  ⟨(47000459601997266693962241397303 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(757574480477530258634580644213 / 781250000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(48984658263391453570115513109833 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16412050094192799796082022773821 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4115638894359620073096229009981 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(824816241766677271432037689513 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(137670823929380199445098046299 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4922220374839377456345274901 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1231607551950953736102805371 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(273877880597224816277989409 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3425391003958357827112761 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2492356495534119887340207 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(207778439319929123240953 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(15988370904712698710273 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1142361886894634768819 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3047038078634267457 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w45S0 : Ball := ⟨(88361728111959082604959394227423 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w45S1 : Ball := ⟨(9759743743664725026340928831601 / 12500000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w45S2 : Ball := ⟨(30480831341440877402475084818783 / 50000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
def w45S3 : Ball := ⟨(232270269816341119443749211379 / 625000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
def w45S4 : Ball := ⟨(215797912962223617937337370743 / 1562500000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
def w45S5 : Ball := ⟨(381491111844670997969310464477 / 20000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
abbrev w45 : Ball := w45S5

def w47Trace : List Ball := [
  ⟨(23551067237312741282554264861991 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(97073300161717367162887177862469 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49019598976757609477695066028629 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4105209591970440019072765314159 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2058701829608492552411445165259 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(412555609219808426631295374831 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(68856527334779870263474569491 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(492354230699703587737457761 / 2500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1231901710244256452585564589 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(273936777078303166045874577 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2740848717373724600264619 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(498560687546165114459831 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(207812842389407116586209 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1599082968609245640707 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(571262940863380218867 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76186280117654642291 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w47S0 : Ball := ⟨(22186110720657023844621600833661 / 25000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w47S1 : Ball := ⟨(78755761425480404148054640884943 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w47S2 : Ball := ⟨(62024699577071872195687741389427 / 100000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
def w47S3 : Ball := ⟨(38470633576260196816199481947743 / 100000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
def w47S4 : Ball := ⟨(2959979295517756841046743768497 / 20000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
def w47S5 : Ball := ⟨(2190369357473449020988501877573 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
abbrev w47 : Ball := w47S5

def w48Trace : List Ball := [
  ⟨(94419270218361035809552428430393 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(6073933153721119057953386558127 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(12264125121733108718963060818321 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4107529443045559965815223015743 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2059633386890960412762512875007 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(825422601388695535770847481979 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(17219703841179359082468113527 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19699750273470025757840325167 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2464424341311545703107438829 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(273998935083751948153589919 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(6853535725324154862791787 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2493275101249825013324713 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(51962286871340288117099 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(15993424350367215040567 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(28567473423769942893 / 2500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(38098587916192909579 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w48S0 : Ball := ⟨(17829997177135758485690281196141 / 20000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w48S1 : Ball := ⟨(39738599917083639520280180951687 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w48S2 : Ball := ⟨(1263325058696031873405067866189 / 2000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
def w48S3 : Ball := ⟨(9974938774558327363519202549313 / 25000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
def w48S4 : Ball := ⟨(15919904568989949697634800424041 / 100000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
def w48S5 : Ball := ⟨(316804201857183845064891195671 / 12500000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
abbrev w48 : Ball := w48S5

def w49Trace : List Ball := [
  ⟨(18888044363634577489035029389757 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(97193609297168861925373011548139 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2453004711570511291670680974039 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4107755339370769370494970857013 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(823889636042049047798641205753 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(825452918112802887490161383703 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27552394106197680085386767351 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2462536701230239742048734519 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(77015149646502777083525643 / 3125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(274004986102442690977777081 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27414693470264352651994297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2493321015618255131393993 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(41570536315688159034031 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(7996838461536800847379 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(571357891269164968123 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76198236278918942609 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w49S0 : Ball := ⟨(89189554970656982824678062734767 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def w49S1 : Ball := ⟨(79547767158638437124123715241031 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
def w49S2 : Ball := ⟨(63278472599249558923540404915203 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w49S3 : Ball := ⟨(10010412736234943074528092941621 / 25000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
def w49S4 : Ball := ⟨(16033338103963961597925957726953 / 100000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitB2_3_3
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
open scoped BigOperators
def w75Trace : List Ball := [
  ⟨(47984258318792228626159664919199 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19594086816114424047050644770849 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(24660582253072658137870913071147 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16496609814208595972252098607689 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1033152202053892432652296834613 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(827651481193121167860980029509 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(69038300610111366614256425569 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19739676030769274857254866359 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(123443269137990780785423429 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(54888687236522687833244959 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(857955693533921141667981 / 3125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(249664716647421917817563 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208108677277100834254701 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8005985438398001669499 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(285983961273458447111 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(38137480912985211927 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w75S0 : Ball := ⟨(46049780928091623904274937075729 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w75S1 : Ball := ⟨(42411646470504621252465323699529 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w75S2 : Ball := ⟨(71949910253562683888874819678621 / 100000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
def w75S3 : Ball := ⟨(10353579170991449269240042430431 / 20000000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩
def w75S4 : Ball := ⟨(13399575206248498238151727716091 / 50000000000000000000000000000000), (19 / 100000000000000000000000000000000)⟩
def w75S5 : Ball := ⟨(3590972314158189681948137986311 / 50000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
abbrev w75 : Ball := w75S5

def w76Trace : List Ball := [
  ⟨(95970316064140983210748773189317 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(24492836565014537542934063581113 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49321470656540947047895351479673 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8248343333342081168268026382941 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(826524844163522042877928099851 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(827654054983897943218992065923 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138076969443802221287737849221 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(123373263195056617710232437 / 625000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2468870507479895121205407599 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27444394903716851602494773 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(6863657211307646258170261 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2496651056199498431880271 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208108976621752210908723 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(400299806673015580233 / 2500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1143937271563382831119 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(38137525720585203059 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w76S0 : Ball := ⟨(92103015654511168586865744464237 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w76S1 : Ball := ⟨(42414827463275646922160593678481 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w76S2 : Ball := ⟨(71960703549577681986294925013061 / 100000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
def w76S3 : Ball := ⟨(25891714276751009998620334379867 / 50000000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩
def w76S4 : Ball := ⟨(26815234727556483071278308798089 / 100000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
def w76S5 : Ball := ⟨(7190568134939512128851691181373 / 100000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
abbrev w76 : Ball := w76S5

def w77Trace : List Ball := [
  ⟨(599998196714862947566973881793 / 625000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(97986246800292183448479581460381 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49326471517644006160941054246641 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16497942005045776829367930272113 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(516609496695927242188415170097 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(827696095511297713639811534369 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13808298400577145605687198933 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1974047478548518878179790713 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2468954213953520833885185813 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(274452325908372929454327427 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27455390850850632486117941 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3994743343941532548757 / 160000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(52028466507740566638613 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8006170823254418097359 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1143960571041724548049 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(38138257578051724877 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w77S0 : Ball := ⟨(46079723015819183918833007400189 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def w77S1 : Ball := ⟨(84933634928584649055280220334927 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
def w77S2 : Ball := ⟨(144274446843641886080573649277 / 200000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
def w77S3 : Ball := ⟨(13009447507524280115669613233039 / 25000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def w77S4 : Ball := ⟨(13539657956082376346944825012809 / 50000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
def w77S5 : Ball := ⟨(3666446751354095861172044368359 / 50000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
abbrev w77 : Ball := w77S5

def w78Trace : List Ball := [
  ⟨(96020413644037189957217964757881 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(97996739815936838298595712002941 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(6166249123703460412171721422267 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3299765191521990686269998599407 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1033263310853178824573597042751 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(827725697673292641718285387623 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8630451188981441500650936069 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19741004760251170535717719993 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1234506576605411116565446387 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(274458224188575312948449869 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(137279636941419755551929 / 500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2496759324711092996913137 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(20811730870221175755781 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16012587646799100805929 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(285994244078576643097 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9534693216362905723 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w78S0 : Ball := ⟨(2304979959093000837221736165533 / 2500000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w78S1 : Ball := ⟨(85006921789125949007060725715233 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w78S2 : Ball := ⟨(18065441880156440088265606256123 / 25000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
def w78S3 : Ball := ⟨(2610881522602482024356425865177 / 5000000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩
def w78S4 : Ball := ⟨(13633404650134109707643354112759 / 50000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
def w78S5 : Ball := ⟨(3717394447085967326472161488373 / 50000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
abbrev w78 : Ball := w78S5

def w79Trace : List Ball := [
  ⟨(96033917464170982234492905488421 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(98003583896933257526044034262951 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49332289805510238738680234429009 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8249701244661142997000964583671 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4133168861019445193259922763239 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(827745004410105906575911127179 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138089981114500120646726329691 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3948270081921325675552416113 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2469051593222249070682669387 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(274462071017293295381976047 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(219650218514900735722679 / 800000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(249678850034406022480171 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(104059776989796481278781 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(640509923422914949969 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1143987675644561548541 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1906955446122577819 / 2500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w79S0 : Ball := ⟨(92225133035152043788862331940617 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w79S1 : Ball := ⟨(21263687908378732071337427865903 / 25000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w79S2 : Ball := ⟨(14468621550877820723055435346621 / 20000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
def w79S3 : Ball := ⟨(52335252395631528540510869155833 / 100000000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩
def w79S4 : Ball := ⟨(13694893216572278235749817336601 / 50000000000000000000000000000000), (19 / 100000000000000000000000000000000)⟩
def w79S5 : Ball := ⟨(1500400801706539210505573972893 / 20000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
abbrev w79 : Ball := w79S5

def w80Trace : List Ball := [
  ⟨(96160345234366537310172583727337 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49033822531834466467586128472029 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(6169223198439036043827098909543 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16504797828722781371428429369449 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(258390674345734368645921138507 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(827925667106182924911573483711 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4316119584284786033809441793 / 3125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19744584673017436206860921403 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(493882254621591829415140877 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(10979922599558540121080343 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27459551463526947046107233 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2497061485103516167613351 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13008785123562470894501 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16014249224843623084609 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(572043891490034509171 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(38142252922384267457 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w80S0 : Ball := ⟨(92468119955925592233308091322847 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w80S1 : Ball := ⟨(42751766040917223746718772954043 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w80S2 : Ball := ⟨(9138567498086615758264738487079 / 12500000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
def w80S3 : Ball := ⟨(26724293093467221731389769703859 / 50000000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩
def w80S4 : Ball := ⟨(28567513653821593905095061748867 / 100000000000000000000000000000000), (19 / 100000000000000000000000000000000)⟩
def w80S5 : Ball := ⟨(4080514181806415973058622710461 / 50000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
abbrev w80 : Ball := w80S5

def w81Trace : List Ball := [
  ⟨(24053124077025220365733558709167 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(24523515466952327543625204408287 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(771291381243450214681389812979 / 1562500000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16507022146747570177260056670303 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4134696804994607794918473460099 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(828000140428055437612547132979 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138126480489573601282957720321 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4936479458154102098214842413 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1234779764845555446327872631 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(5490258022157201479199239 / 2000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3432612624333560165468793 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2497174001988667817428023 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(41629844162701618302781 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16014867941833794587233 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(572064521715122977261 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(762870972176346887 / 1000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w81S0 : Ball := ⟨(9256844445836325745624221593209 / 10000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w81S1 : Ball := ⟨(17137833818882166538176711635577 / 20000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w81S2 : Ball := ⟨(36713168500452663023365486407191 / 50000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
def w81S3 : Ball := ⟨(26957134826852592754025559658321 / 50000000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩
def w81S4 : Ball := ⟨(14533742361462179318412044926463 / 50000000000000000000000000000000), (11 / 50000000000000000000000000000000)⟩
def w81S5 : Ball := ⟨(2112296670293602445979800989231 / 25000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
abbrev w81 : Ball := w81S5

def w82Trace : List Ball := [
  ⟨(96229334968294592402883395225639 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(98102590361049671212432499515887 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4936550952998944770288224358031 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16507740184834890449016793715247 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4134840781021048794500536156301 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(828024180381130866552442238883 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(69064959742460643517425514209 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19746348166155745623164791301 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(246960738538238196158161981 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(54903538004494867068294717 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(686533415104400136005273 / 2500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2497210320676715960067309 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(104076007869665172573223 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16015067652522971389869 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1144142361524112935289 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19071983406541964123 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w82S0 : Ball := ⟨(92600849084402444230562752811101 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w82S1 : Ball := ⟨(42874586255761384969871489541317 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w82S2 : Ball := ⟨(9191150733013615280768056081407 / 12500000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
def w82S3 : Ball := ⟨(54065441150065099190158607543737 / 100000000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩
def w82S4 : Ball := ⟨(29230719267511525553688699485483 / 100000000000000000000000000000000), (19 / 100000000000000000000000000000000)⟩
def w82S5 : Ball := ⟨(854434948896069537004803880333 / 10000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
abbrev w82 : Ball := w82S5

def w84Trace : List Ball := [
  ⟨(24210167749691597416637228086919 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49205941808369283885152732830901 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(12367303675743656027992090631347 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16533757913766210860520197787981 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4140056549026171319660278514497 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(207223733207400735959413236017 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(69127234556299262076205809641 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4940483023773890676353700819 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(308917535965262589025470907 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(274691091182850470986593179 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3434638594406446175333449 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2498525259902930007272721 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3253956313268699616709 / 1562500000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16022297813194644531479 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(572312253510679535303 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3815910057998093299 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w84S0 : Ball := ⟨(93781155594913136951136476465931 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w84S1 : Ball := ⟨(87949051447173075698231551682523 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w84S2 : Ball := ⟨(7735035650457496480785014326887 / 10000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
def w84S3 : Ball := ⟨(29915388256924212838726277319197 / 50000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
def w84S4 : Ball := ⟨(7159443636500152746721657331183 / 20000000000000000000000000000000), (11 / 50000000000000000000000000000000)⟩
def w84S5 : Ball := ⟨(12814408296055632823834682914069 / 100000000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩
abbrev w84 : Ball := w84S5

def w85Trace : List Ball := [
  ⟨(48440010256844336590814135237133 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(98431769261522683809420629817117 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9895175713551043694871309445383 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16535429194353750192832977165253 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4140391515343909260256397560133 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(207237711310321651663366708339 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27652493137236567831160011689 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9881466275556340066470755307 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2471451528176236203088134939 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(68675555417481657434871667 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27478121106016816676297721 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1249304828458230918025801 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208259698399606947170941 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(320455236722258974211 / 2000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(228931089949188295959 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19080035705657037089 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w85S0 : Ball := ⟨(93857383747327381270952739073263 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def w85S1 : Ball := ⟨(44046042419465370295839454047483 / 50000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
def w85S2 : Ball := ⟨(77602154112693712445735636555629 / 100000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
def w85S3 : Ball := ⟨(60220943229302656687912598473581 / 100000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
def w85S4 : Ball := ⟨(7253124006853786977764830254907 / 20000000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩
def w85S5 : Ball := ⟨(13151951964699683421400377323041 / 100000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
abbrev w85 : Ball := w85S5

def w86Trace : List Ball := [
  ⟨(48440237319924594227230822566221 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19686399748523585161411498449313 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(24737977733188568838022111181733 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8267724239970218590240538563861 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(414039538060379979089766331039 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(414475745211132487604450722699 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138262557959066666648740732559 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19762944095361743020993938333 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(61786320294314055196830061 / 2500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(137351175051705579757728777 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13739066393693193474190419 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2498610630758880376322443 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208259773336614936497137 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16022767190369970358269 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1144655806786585530693 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(38160082613214071961 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w86S0 : Ball := ⟨(93858263664424617413741271563347 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w86S1 : Ball := ⟨(17618747316201300822493376772181 / 20000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w86S2 : Ball := ⟨(19401266062009408781754254430401 / 25000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
def w86S3 : Ball := ⟨(60225459969420491584042760181517 / 100000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
def w86S4 : Ball := ⟨(36271060285282700790853141181647 / 100000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
def w86S5 : Ball := ⟨(6577949071093059980401914202497 / 50000000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩
abbrev w86 : Ball := w86S5

def w87Trace : List Ball := [
  ⟨(19391935301940079203102230297813 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(98472015880149116906521409261053 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49489364205696618412262048225019 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8269405575763264578752255465279 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1035267329069939345442556567683 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(165812796028562169369654386621 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(69139322923441076681156279 / 50000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3952991365225817176202953127 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2471676603749162391141836633 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(274724742010292067637962653 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13740084689341520447134237 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2498780414667198649031423 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208272838120590395912151 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(801185033345091303563 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(572359027041109767321 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(38162035477780352119 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w87S0 : Ball := ⟨(47005894344328733846328990719511 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w87S1 : Ball := ⟨(22095541031101960472317826059927 / 25000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w87S2 : Ball := ⟨(15622813870627529169929207254323 / 20000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
def w87S3 : Ball := ⟨(61018078309067979934998251220249 / 100000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
def w87S4 : Ball := ⟨(1861602940265776154737666333371 / 5000000000000000000000000000000), (23 / 100000000000000000000000000000000)⟩
def w87S5 : Ball := ⟨(433195688400772867769213264289 / 3125000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
abbrev w87 : Ball := w87S5

def w88Trace : List Ball := [
  ⟨(96960434010132110258392349835097 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49236199279054655394302609606119 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49489492422679883335492771661221 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1653884330472663453731339594121 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4141075760142777159508644104883 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(207266263924187352330225759829 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138278799666601435988630127619 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19764976070056687226808768043 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2471678743427921414366041553 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(274724956098081315769931321 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27480188850299067760607327 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2498782037943135957883823 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(41654592606054047660727 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(250370462369400905323 / 1562500000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1144718649211453383 / 100000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(38162054147613681757 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w88S0 : Ball := ⟨(94013257634331836160818084228699 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w88S1 : Ball := ⟨(22096231527548133187286615332089 / 25000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w88S2 : Ball := ⟨(78118951635041937177141673690089 / 100000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
def w88S3 : Ball := ⟨(61025706045580213498506794278049 / 100000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
def w88S4 : Ball := ⟨(37241367983615654188317699957989 / 100000000000000000000000000000000), (23 / 100000000000000000000000000000000)⟩
def w88S5 : Ball := ⟨(13869194892910730966442083177749 / 100000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
abbrev w88 : Ball := w88S5

def w89Trace : List Ball := [
  ⟨(9697300938183443281718467403369 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3077460978208181357071295207717 / 3125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49491620897541978811502345768401 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16539377062481372541607295049991 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4141182730713106955977929782043 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(414541455120938766795231958089 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138281353117716136408927764313 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(988264776206185408639486907 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(308964282822826746854541281 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27472850999971318076709173 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27480512082821496819242353 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(624702246152044191256333 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208275036551284667909853 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2002982217959828719999 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1144728528441963054903 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76324728133693907503 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w89S0 : Ball := ⟨(94037645485693489259790235842833 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w89S1 : Ball := ⟨(2763462115154052837357843579581 / 3125000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w89S2 : Ball := ⟨(39100021052885563312727281342639 / 50000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
def w89S3 : Ball := ⟨(61152465853443771001832613697787 / 100000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
def w89S4 : Ball := ⟨(18698120399783031998407189759267 / 50000000000000000000000000000000), (23 / 100000000000000000000000000000000)⟩
def w89S5 : Ball := ⟨(6992394129695647447331751196051 / 50000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
abbrev w89 : Ball := w89S5

def w90Trace : List Ball := [
  ⟨(3033651761574679389787877273637 / 3125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(98531201503690214206787456465689 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49509192481079839240323793224789 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8271891612916808505629439514799 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(517758217024488988919945803207 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(414615144606389724457369627821 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(69151214966937536943703842699 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(988396616655716018717991873 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2472007437695969511145348087 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(137378921792985054360320521 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27483179990984915740062999 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2499031396251326907692907 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(41658430161908470847153 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3205016108376539274821 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1144810067989027449513 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76329843668026228377 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w90S0 : Ball := ⟨(47119580213786395683896601683397 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w90S1 : Ball := ⟨(88810193580938015775306569960381 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w90S2 : Ball := ⟨(19718126209709209853932550994123 / 25000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
def w90S3 : Ball := ⟨(62208720195523406479763195130849 / 100000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
def w90S4 : Ball := ⟨(19349624341824608662604755129257 / 50000000000000000000000000000000), (23 / 100000000000000000000000000000000)⟩
def w90S5 : Ball := ⟨(14976318486789256799246113282771 / 100000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
abbrev w90 : Ball := w90S5

def w91Trace : List Ball := [
  ⟨(9713754836989542857582642394109 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49280923313792589214803052609417 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49519457596464507723252416201987 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16546357037860604568701438141087 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2071290752565764854407549802839 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(829316370715427612040830636059 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4322335630177781559695160353 / 3125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19769472364982113645666587387 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1236089331902557687410468901 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(274774975322185489960800229 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27484738113250476217501279 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2499161288570788101138749 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208302145745177644296317 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4006448666300924265639 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1144857687387271941409 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76332830841358970493 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w91S0 : Ball := ⟨(94357033033137740333524498717863 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w91S1 : Ball := ⟨(44516248414083233587448570490359 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w91S2 : Ball := ⟨(19816963728643680095065048406261 / 25000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
def w91S3 : Ball := ⟨(31416964113790338254167490895973 / 50000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
def w91S4 : Ball := ⟨(39481025365087597356249876115843 / 100000000000000000000000000000000), (23 / 100000000000000000000000000000000)⟩
def w91S5 : Ball := ⟨(7793756819393451250565121368561 / 50000000000000000000000000000000), (19 / 100000000000000000000000000000000)⟩
abbrev w91 : Ball := w91S5

def w92Trace : List Ball := [
  ⟨(48569305408820487411955351992481 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(98562383030666098638167354662233 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49519637264461618491544295811141 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16546402085283324295567851499991 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2071295266020966563596386078371 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(103664734659778426152398320449 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(34578738902957365891468415427 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19769499317439838898264014857 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1236090830226090360856921151 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13738763757243379145431953 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(5496953076366492086521471 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2499163561797381096231273 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(104151160332241658108731 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16025807162890801279287 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(114485852075998519199 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1908322077922307337 / 2500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w92S0 : Ball := ⟨(94359097115811162154161248094363 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w92S1 : Ball := ⟨(22259098021277705950466714011629 / 25000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w92S2 : Ball := ⟨(19818697788833963375439369454407 / 25000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
def w92S3 : Ball := ⟨(62844925127221156664461117564787 / 100000000000000000000000000000000), (11 / 50000000000000000000000000000000)⟩
def w92S4 : Ball := ⟨(19747423071230165570839204502969 / 50000000000000000000000000000000), (7 / 25000000000000000000000000000000)⟩
def w92S5 : Ball := ⟨(15598428718166136993941318394257 / 100000000000000000000000000000000), (23 / 100000000000000000000000000000000)⟩
abbrev w92 : Ball := w92S5

def w93Trace : List Ball := [
  ⟨(48569988419480206395539855162043 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2464076817437585231959756330549 / 2500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49519868267611763600788214848167 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8273230001843500497968404964011 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(82852042762356393589045622457 / 2000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(829319814294441431113389049751 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(69157616307436794485066541717 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19769533970695813257429082497 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(618046378323433416937697223 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(68693915158011876404026391 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27484800441510773897974389 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(499833296904579429573803 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208302545561134401333541 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3205164646274477556173 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(143107449030108528467 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76332950328292280177 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w93S0 : Ball := ⟨(47180875501368827154028631902581 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def w93S1 : Ball := ⟨(5565087532689162942680905245599 / 6250000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
def w93S2 : Ball := ⟨(39641855035510214686892567596899 / 50000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
def w93S3 : Ball := ⟨(31429533413128131290686129552343 / 50000000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩
def w93S4 : Ball := ⟨(39512622822677505677310298661987 / 100000000000000000000000000000000), (11 / 50000000000000000000000000000000)⟩
def w93S5 : Ball := ⟨(15612473623271752962591099629173 / 100000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
abbrev w93 : Ball := w93S5

def w94Trace : List Ball := [
  ⟨(48572416979614677817617190289831 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19713104979699146593127961907507 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49520689625261929013998699820783 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4136666484604960233033498499099 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2071321702302402235851731726993 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(414663350763034812461569019783 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(69158108761226964305652624489 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19769657183147665874833030001 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(61804980309337414107116751 / 2500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(68694257815274562343070847 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13742462549404514216124779 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(124958843824348187596329 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(20830334519732457901309 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8012940181997489038433 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1144863401965983840387 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(38166594651079449773 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w94S0 : Ball := ⟨(5898199228103900652428663966829 / 6250000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w94S1 : Ball := ⟨(8905921058407795066853805981189 / 10000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w94S2 : Ball := ⟨(15863085979718284142129990761437 / 20000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
def w94S3 : Ball := ⟨(3931835887498981166397445803049 / 6250000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
def w94S4 : Ball := ⟨(39575893622335746261007805520769 / 100000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩
def w94S5 : Ball := ⟨(313250271201287039100674208231 / 2000000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩
abbrev w94 : Ball := w94S5

def w95Trace : List Ball := [
  ⟨(24311456493171441392247102581529 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(12327062894994895069985855091793 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2476888154934925706815547527189 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16550946449197211187254764013699 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(517937641129933890173000572753 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(414734924510606159250971639573 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138336687913027273810542390043 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9886109000543629018176101081 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1236241963658198205018555289 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(10992220698430343881729479 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27487515867975722764640197 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(624848213137902096158637 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(52079990981881999513601 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16027067737379137972801 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(572471289112259175847 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(38169077738912291657 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w95S0 : Ball := ⟨(23641876672774713557858358239331 / 25000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w95S1 : Ball := ⟨(89430133217710265658660394395847 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w95S2 : Ball := ⟨(39988743636687025370182115592353 / 50000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
def w95S3 : Ball := ⟨(63963984705627082531830129678749 / 100000000000000000000000000000000), (11 / 50000000000000000000000000000000)⟩
def w95S4 : Ball := ⟨(40913913394216953319749034133611 / 100000000000000000000000000000000), (29 / 100000000000000000000000000000000)⟩
def w95S5 : Ball := ⟨(2092435386536856772381940766823 / 12500000000000000000000000000000), (1 / 4000000000000000000000000000000)⟩
abbrev w95 : Ball := w95S5

def w97Trace : List Ball := [
  ⟨(97327607614174323681650812201511 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(24664442877948097077519038287853 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9910316479613191988362505573333 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16554410777444949079371375480773 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1036048816074920048872092163297 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(829585689598023855220969579261 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138353252803303299025888475217 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19774290192361416262128792671 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2472714311340101807567223623 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(274828567369759156915001631 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(5497922437284722551520529 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(39055743863796662987237 / 1562500000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(104166705328757661689753 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4007007117357327296681 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(572503320577857178929 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3817108661297856073 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w97S0 : Ball := ⟨(94726632038986837867671065921721 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w97S1 : Ball := ⟨(89731348174496076885890570441493 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w97S2 : Ball := ⟨(80517148452126404298140869809749 / 100000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
def w97S3 : Ball := ⟨(12966022389723522847161549084413 / 20000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
def w97S4 : Ball := ⟨(21014717076351461774002853295901 / 50000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩
def w97S5 : Ball := ⟨(17664733351963909170540862137551 / 100000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
abbrev w97 : Ball := w97S5

def w98Trace : List Ball := [
  ⟨(97338253403438111493986638144823 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49331571348303273596911606258353 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19821352349630714605656063693 / 40000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16554861611887908661548597891817 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2072142796779946810945326534917 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(414800381916331190103344780863 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138355408341793698659331276997 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(123590998979541348212119053 / 625000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(618186072449675022839998719 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(274831566687086940629263661 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1718117810197998138096909 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2499590346546338672786751 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(52083790087646979900011 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8014076739822915641043 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(572507488488976111313 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(7634269598129035133 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w98S0 : Ball := ⟨(94747355756319310956500685305549 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w98S1 : Ball := ⟨(44885307114072670345604100512461 / 50000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w98S2 : Ball := ⟨(10073453973623113352785232118491 / 12500000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
def w98S3 : Ball := ⟨(1014744749587032920878757644499 / 1562500000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
def w98S4 : Ball := ⟨(42176794903119878113210827611889 / 100000000000000000000000000000000), (7 / 25000000000000000000000000000000)⟩
def w98S5 : Ball := ⟨(17788820282998389285975177527331 / 100000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩
abbrev w98 : Ball := w98S5

def w99Trace : List Ball := [
  ⟨(6085161938053930672363297564401 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(98675421157941652928787147231029 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(12389373011185287699874689760043 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16555892164484010775213037196897 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(259030754548476304112310229789 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(829635220990840205577570070561 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138360335507751769185577468387 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1235948511953980365512499713 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(154550800902970704176954129 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(68709605623279709097557969 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27490508471509697569182873 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2499642323439937645249957 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(104169579875771911708247 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8014219612059700701161 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(572517015357665325767 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4771493178163965511 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w99S0 : Ball := ⟨(5924671329974443134962349153847 / 6250000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w99S1 : Ball := ⟨(44930214871323055166533317729081 / 50000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w99S2 : Ball := ⟨(3229958733413215076377858675419 / 4000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
def w99S3 : Ball := ⟨(815049485902523482678015622841 / 1250000000000000000000000000000), (11 / 50000000000000000000000000000000)⟩
def w99S4 : Ball := ⟨(21257781263038970410521431847113 / 50000000000000000000000000000000), (29 / 100000000000000000000000000000000)⟩
def w99S5 : Ball := ⟨(723029222763537158550702948243 / 4000000000000000000000000000000), (1 / 4000000000000000000000000000000)⟩
abbrev w99 : Ball := w99S5

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
open scoped BigOperators

def w2Trace : List Ball := [
  ⟨(84597619125205089736172006311063 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(287763190217468827617782392903 / 312500000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(47325044077594224176574894987021 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(15992412730055362749694693162069 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(503884342020049821649505183307 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(202661481013394753386767106967 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(6781913861429235519813141411 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9717005589004447660794023429 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(608706163735778491349902169 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(54206593500162287796340059 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27144053965850958234814469 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2470735506229453309749967 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8244528274498550519241 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(495915518354627658563 / 3125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(28360432994016500911 / 2500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(7567220252295638787 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w2S0 : Ball := ⟨(71567571616532659723992943125807 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def w2S1 : Ball := ⟨(1600599158464853492919978508641 / 3125000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
def w2S2 : Ball := ⟨(3279254612580348394160949624957 / 12500000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
def w2S3 : Ball := ⟨(688224692104287413796798727327 / 10000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
def w2S4 : Ball := ⟨(236826613411020605245216287039 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩

def w3Trace : List Ball := [
  ⟨(17193461196655432197407653245491 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(92806904729798666614606898981387 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(11893099547713272105641171468203 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16055235691371534665274372650617 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4043772080075276231177722127437 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(162555617274960997649942141381 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(135944590818002902278789717 / 100000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2434058547802820386565399929 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2439112676059295582138731649 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(271463001174311553358616637 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27183241520619055769889379 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(494801550387050376991799 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(103182677636193010383271 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(15887334380787229268963 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1135621079487512777459 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9468620676209316049 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w3S0 : Ball := ⟨(18475944245056002907619036694059 / 25000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def w3S1 : Ball := ⟨(1365442062985672132889830206583 / 2500000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
def w3S2 : Ball := ⟨(298309124379290915863936816923 / 1000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
def w3S3 : Ball := ⟨(444941668439696289244594944761 / 5000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
def w3S4 : Ball := ⟨(49493272078475156223283474047 / 6250000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def w3S5 : Ball := ⟨(3135467495723479693518430173 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
abbrev w3 : Ball := w3S5

def w4Trace : List Ball := [
  ⟨(43004612630968991983903177598447 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9282896008998414087586237195451 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(23789968392513580208215399184691 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8028574392909957357006619687303 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4044158532645516698440704419737 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(50802684700553595648245763723 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(67976953698316956060133492347 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(97368189006779382317589971 / 500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2439243044070346431057003157 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(271476073488622879500088817 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(5436886522198381256733501 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(77315850006009738723551 / 3125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(206373017740265737886027 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(15887882483420361399649 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(567828827970733624147 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(37875647702437033621 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w4S0 : Ball := ⟨(73975868301587910668784065662379 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w4S1 : Ball := ⟨(27362145454869395155073956927247 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
def w4S2 : Ball := ⟨(748687003893429899497028839077 / 2500000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w4S3 : Ball := ⟨(1121064459597841434976520886363 / 12500000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
def w4S4 : Ball := ⟨(804342734446976160702008647501 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def w4S5 : Ball := ⟨(6469672344576388104635416779 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
abbrev w4 : Ball := w4S5

def w5Trace : List Ball := [
  ⟨(1102320926751695236176977521 / 1280000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(92886606049739533380917829323629 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(47599637486974463747609226319519 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3212429573175963116025417762947 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1011292077056304944913192353953 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(406506223155515864668058512107 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(135978249263124604604816221119 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4869173281079488153358079977 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2439583648037062201120081527 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(135755113065605914026376263 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27187544405070211333868931 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2474367011762855242522383 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(206393035977987373765041 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3972328598130323853597 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1135753210921910421071 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(75757381770539529303 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w5S0 : Ball := ⟨(37082257859946174749445643608123 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def w5S1 : Ball := ⟨(5500375391966159423836525575271 / 10000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
def w5S2 : Ball := ⟨(15127064726273440959619896097297 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
def w5S3 : Ball := ⟨(286035109041082716582367764001 / 3125000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
def w5S4 : Ball := ⟨(167559339221287075088374028923 / 20000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def w5S5 : Ball := ⟨(1754758260017147069441912959 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
abbrev w5 : Ball := w5S5

def w6Trace : List Ball := [
  ⟨(86476687893016333469851031210019 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(93074662040343982398943316151241 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2978992336580033165667631160141 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8039222238224200623533197045651 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4048459513917666267452864835983 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(406782403076494292318624631071 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(68028785100499194342845957921 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1948664853100818516218114777 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2440693399944723665191346563 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(271621496488446545987587637 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13598841158114996097983393 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2475213422703491942250599 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(20645824923415843339483 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(15893978992079021112747 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(568032243788296634297 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(75777201665602273241 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w6S0 : Ball := ⟨(74782175489461577081980349690883 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w6S1 : Ball := ⟨(5592373770936627865813923153869 / 10000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
def w6S2 : Ball := ⟨(7818661098464989779733749713001 / 25000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w6S3 : Ball := ⟨(2445258454905990424310397234107 / 25000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
def w6S4 : Ball := ⟨(478343112903138528431752845003 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def w6S5 : Ball := ⟨(9152485346474589333197978901 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
abbrev w6 : Ball := w6S5

def w7Trace : List Ball := [
  ⟨(87752485434793811143629090557047 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(93742935822473699627791117052839 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(47891803884625337713041583981333 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4034053033629281069572169955353 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(50751486045689091884614126029 / 1250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(815520727221885311117769493659 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(6816917761748190668030554793 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3904376048871145087298573331 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2444619953418414338678937513 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(136007565022257252396560341 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27233541487519339704956071 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2478206938128977784931097 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(206688866553341695936579 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(15910473213465701152101 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1137165123275265574373 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(7584719860472175287 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w7S0 : Ball := ⟨(19251246749959249924984868595359 / 25000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def w7S1 : Ball := ⟨(14824420057112663320064282050391 / 25000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
def w7S2 : Ball := ⟨(35162148804755875201969759958069 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
def w7S3 : Ball := ⟨(2472753417135590046148799708857 / 20000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
def w7S4 : Ball := ⟨(95539210343058396701088265651 / 6250000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def w7S5 : Ball := ⟨(2920877028152050088661190921 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
abbrev w7 : Ball := w7S5

def w8Trace : List Ball := [
  ⟨(44255620504028353535093839376707 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(11767351027519824781514681327003 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(12006640780152923970773153169233 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16170327539606619655605560222823 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2033499611543479931625663355311 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(816674312997879217804234909849 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(34125973083663975682479550323 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9771322271714792344642153367 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(611733383535721364416486533 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(136123508118074211207180389 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(6813665539058170406805959 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(99198793107855363845763 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(206824660622540906858971 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(15920184415149323703729 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1137813098484958559199 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(15177669383476055103 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w8S0 : Ball := ⟨(19585599461965748205941204068907 / 25000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w8S1 : Ball := ⟨(61375313005528480896867231426661 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
def w8S2 : Ball := ⟨(7533858093053186981900116395073 / 20000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w8S3 : Ball := ⟨(3547438610391437687316481356023 / 25000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w8S4 : Ball := ⟨(2013491311119349508951105594633 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w8S5 : Ball := ⟨(20270736299765585597522899913 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
abbrev w8 : Ball := w8S5

def w9Trace : List Ball := [
  ⟨(88699527378614997584418606311283 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(47118432737122465965471112245453 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(48059913174409657365816802515053 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(404469147700798506071080704651 / 2500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2034350230150267839672430013299 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(408479738841919004807783139473 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(68272402572622724176966322727 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9773887863418301555598961499 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1223752594514843910638612953 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(272304306707673311571639007 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1362993993562388118284913 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2480405307799782445857741 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(51714550844373766236613 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(7961291538054047775879 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1137973143312383583331 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(75898503306711598709 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w9S0 : Ball := ⟨(78676061571896715450374622954693 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w9S1 : Ball := ⟨(7737403330581103835015607199747 / 12500000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
def w9S2 : Ball := ⟨(19157571296028018686908397173011 / 50000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w9S3 : Ball := ⟨(3670125379623966596001366263729 / 25000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w9S4 : Ball := ⟨(134698203021599649206550427993 / 6250000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w9S5 : Ball := ⟨(46447631096955076780984273421 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
abbrev w9 : Ball := w9S5

def w20Trace : List Ball := [
  ⟨(22731197607144101774011092514723 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(95390456669805207241683142200581 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(48451381739007150264794195763177 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(254338828832093308239029732759 / 1562500000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2044312817830481878169826672397 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(820297264545556802806604355509 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(17127931661774445574469817139 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19607784466622775384368432819 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2454188670577489270506761501 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(272973954342303384295332849 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13660427789018642650060929 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1242746792529787688532183 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(6476564671067041269493 / 3125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(638024082842483423813 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(569921249557372245787 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(7601692979348815989 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w20S0 : Ball := ⟨(20668293786201349530006062689821 / 25000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w20S1 : Ball := ⟨(68348538885236690604114750992311 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w20S2 : Ball := ⟨(23357613838733559785715792104211 / 50000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
def w20S3 : Ball := ⟨(4364624993915180021185672885889 / 20000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
def w20S4 : Ball := ⟨(4762487834377271309240017303431 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩

def w21Trace : List Ball := [
  ⟨(4546381593633731645311586412483 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(95391923531054658277119240326901 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(48451878493215132789703722658597 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8138905207517209490944482310063 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2044325434092121625958872558539 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(820301488939196054401488331089 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(137024058819870186573910781299 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2450982544547154255080643477 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2454197120511083437693337979 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(272974800790134413214912279 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27320932638228226963642379 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2485500014538094908746171 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(103625282282063317389969 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1595063746656350147507 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1139844860438857849223 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19004269788038699249 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w21S0 : Ball := ⟨(8267834237972635769477607291581 / 10000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w21S1 : Ball := ⟨(2136158843331017337499425708763 / 3125000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w21S2 : Ball := ⟨(46726907944359013114685439468713 / 100000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
def w21S3 : Ball := ⟨(54585098151015036316432984489 / 250000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
def w21S4 : Ball := ⟨(1191813176062378054567059252473 / 25000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
def w21S5 : Ball := ⟨(1818135867693942976840227081 / 800000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
abbrev w21 : Ball := w21S5

def w22Trace : List Ball := [
  ⟨(45633983581107315219871538302979 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(95567505449709056869614223920287 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9702264179715798017842559266091 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16292809564605679889594376395993 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4091669294235879701870235703463 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(410403392408157544587750880261 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(68548241623986150631976731017 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9808468373776151991027867257 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2455207688137624436663006131 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(273076028070996496451214379 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3416268507430148707161877 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(310783610027465150759859 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(207309768415760550521693 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(15954870056074715410523 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1140127224002864047001 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76034934980751262993 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w22S0 : Ball := ⟨(16659683659846176204193839074009 / 20000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def w22S1 : Ball := ⟨(1084160389242756578300787149797 / 1562500000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
def w22S2 : Ball := ⟨(48144537583739103387021781687031 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w22S3 : Ball := ⟨(4635792998304134126955863599117 / 20000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w22S4 : Ball := ⟨(537264418078140842912054215571 / 10000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
def w22S5 : Ball := ⟨(288653054932843312984454457957 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
abbrev w22 : Ball := w22S5

def w23Trace : List Ball := [
  ⟨(91442398411354295784312056220971 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(11957176265682583831194402276173 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2427087171168606046882071736961 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(127347530925498127880409157347 / 781250000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1023303350143481052761979289147 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(821065239705792884394370560659 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(34283381021857860976928541227 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19621578428657144143774750641 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2455724462005521975068942239 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(136563895014000851831093829 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1708428756864695040353181 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1243331002152587585539351 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(5183500966272767493217 / 2500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(15957034071661612795207 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(5701357934014597387 / 500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76044060795282790157 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w23S0 : Ball := ⟨(83617122272208506374499270625201 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def w23S1 : Ball := ⟨(69918231370854678480060373441927 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
def w23S2 : Ball := ⟨(12221397695070918230830931797667 / 25000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w23S3 : Ball := ⟨(23898009859373560452900205601421 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def w23S4 : Ball := ⟨(5711148752387159026538227846237 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
def w23S5 : Ball := ⟨(65234440143786806173257123601 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
abbrev w23 : Ball := w23S5

def w24Trace : List Ball := [
  ⟨(18306948936083586976691286324209 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(47852491693304259698880776577323 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(48557837668401624925941210426369 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16304543309773358430596289055167 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1023507518290895754584260768429 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(102650240778792981087280952429 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(137153112507079619255857847633 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19624033004609383051102587991 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(613999432345975286583212847 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(273155160767555829183993693 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27337351698033342730146787 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2486869872451918782220861 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(103678022037502702591321 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(15958178281763927115007 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(28508697926531112547 / 2500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(38024442540107584337 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def w24S0 : Ball := ⟨(83786094837092994281002747182393 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def w24S1 : Ball := ⟨(70201096880503413118637982536993 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def w24S2 : Ball := ⟨(3080121252016141275390368322639 / 6250000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
def w24S3 : Ball := ⟨(12143548066715496543652834142857 / 50000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
def w24S4 : Ball := ⟨(737328798243148368471610262829 / 12500000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
def w24S5 : Ball := ⟨(69587680859991730250340878531 / 20000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
abbrev w24 : Ball := w24S5

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Parameters_StageCCapacity
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldStageCCapacity

open AllFieldHistory AllFieldParameters MatrixMultiplication.Foundation
open scoped BigOperators

def symbolicMarginal (u : Shape) (d : ℝ) (i : Fin 3) (k : Fin 17) : ℝ :=
  ∑ b : Fin 4, if stageCAtom u b i = k.val then
    (if b.val < 2 then d / 2 else (1 - d) / 2) else 0

end MatrixMultiplication.AllFieldStageCCapacity

end

end MatrixAllFields

end OAI
end


