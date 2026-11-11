-- Prove2me | Definitions.Def_OAIQ254M011
-- name    : OAIQ254M011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T05:54:36.742288+00:00
-- url     : https://prove2.me/theorems/0c0d4e73-a1b1-4356-a12d-1952b000db55
-- title:
--   Definitions bundle OAIQ254M011 of the split of OpenAI, Staggered extraction for exact matrix multiplication over every field
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant`, carved from OpenAI's openai/math development (OpenAI, *Staggered extraction for exact matrix multiplication over every field*, OpenAI Math Release, September 24, 2026, result family 107, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 745 declarations of OpenAI's Lean: 745 definitions. The definitions and types are `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_2_2I2R10Raw`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_2_2I2R11Certificates`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_2_2I2R11P`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_2_2I2R11Raw`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_2_2I2R11Terms`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_2_2I2R12Certificates`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_2_2I2R12P`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_2_2I2R12Raw`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_2_2I2R12Terms`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_2_2I2R13Certificates`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_2_2I2R13P`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_2_2I2R13Raw`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_2_2I2R13Terms`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_2_2I2R14Certificates`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_2_2I2R14P`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_2_2I2R14Raw`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_2_2I2R14Terms`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_2_2I2R15Certificates`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_2_2I2R15P`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_2_2I2R15Raw`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_2_2I2R15Terms`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_2_2I2R16Certificates`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_2_2I2R16P`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_2_2I2R16Raw`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_2_2I2R16Terms`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_2_2I2R1Certificates`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_2_2I2R1P`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_2_2I2R1Raw`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_2_2I2R1Terms`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_2_2I2R2Certificates`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_2_2I2R2P`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_2_2I2R2Raw`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_2_2I2R2Terms`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_2_2I2R3Certificates`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_2_2I2R3P`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_2_2I2R3Raw`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_2_2I2R3Terms`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_2_2I2R4Certificates`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_2_2I2R4P`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_2_2I2R4Raw` and 705 more.
--
--   **Sources.** They come from these modules of lean/OAI/LinearAlgebra, in whole or in part: `MatrixFields_CapacityB_CapB4_2_2I2`, `MatrixFields_CapacityB_CapB4_3_1I0`, `MatrixFields_CapacityB_CapB4_3_1I1`, `MatrixFields_CapacityB_CapB4_3_1I2`, `MatrixFields_CapacityB_CapB5_1_2I0`, `MatrixFields_CapacityB_CapB5_1_2I1`, `MatrixFields_CapacityB_CapB5_1_2I2`, `MatrixFields_CapacityB_CapB5_2_1I0`, `MatrixFields_CapacityB_CapB5_2_1I1`, `MatrixFields_CapacityB_CapB5_2_1I2`, `MatrixFields_CapacityB_CapB6_1_1I0`, `MatrixFields_CapacityB_CapB6_1_1I1`, `MatrixFields_CapacityB_CapB6_1_1I2`, `MatrixFields_Certificates_Four0_1_7`, `MatrixFields_Certificates_Four0_3_5`, `MatrixFields_Certificates_Four0_4_4`, `MatrixFields_Certificates_Four0_5_3`, `MatrixFields_Certificates_Four0_7_1`, `MatrixFields_Certificates_Four0_8_0`, `MatrixFields_Certificates_Four1_0_7`, `MatrixFields_Certificates_Four1_7_0`, `MatrixFields_Certificates_Four2_0_6`, `MatrixFields_Certificates_Four2_6_0`, `MatrixFields_Certificates_Four3_0_5`, `MatrixFields_Certificates_Four3_5_0`, `MatrixFields_Certificates_Four4_0_4`, `MatrixFields_Certificates_Four4_4_0`, `MatrixFields_Certificates_Four5_0_3`, `MatrixFields_Certificates_Four5_3_0`, `MatrixFields_Certificates_Four6_0_2`, `MatrixFields_Certificates_Four6_2_0`, `MatrixFields_Certificates_Four7_0_1`, `MatrixFields_Certificates_Four7_1_0`, `MatrixFields_Certificates_Four8_0_0`, `MatrixFields_Certificates_NativeInterior`, `MatrixFields_Certificates_NativeSharp`, `MatrixFields_Certificates_SparseContraction`, `MatrixFields_Certificates_SplitA1_3_12`, `MatrixFields_Certificates_SplitB1_1_6`, `MatrixFields_Certificates_Zero0_1_7`, `MatrixFields_Histories_HistoryChildLaws`.
--
--   **Imports.** It imports the bundles `OAIQ254M002`, `OAIQ254M003`, `OAIQ254M004` and `OAIQ254M005` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z0_5_3H2H_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.capacityABalls_sound` and `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.capacityBBalls_sound`; the proofs of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_1_14I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_1_14I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_2_13I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_2_13I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_3_12I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_3_12I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_3_12I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_4_11I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_4_11I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_4_11I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I1PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I2PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I1PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I2PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I2Singles_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_2_12I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_2_12I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_2_12I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_3_11I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_3_11I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_3_11I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_4_10I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_4_10I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_4_10I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_5_9I1Group_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_5_9I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_5_9I2PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_5_9I2Singles_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_5_9I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_6_8I1Group_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_6_8I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_6_8I2PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_6_8I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_6_8I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_7_7I1Group_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_7_7I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_7_7I2PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_7_7I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_7_7I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_3_10I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_3_10I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_3_10I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_4_9I1Group_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_4_9I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_4_9I2PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_4_9I2Singles_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_4_9I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_5_8I1Group_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_5_8I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_5_8I2PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_5_8I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_5_8I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_6_7I1Group_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_6_7I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_6_7I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_6_7I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_4_8I1Group_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_4_8I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_4_8I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_5_7I1ResidualEntropies_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_5_7I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_5_7I2PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_5_7I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_5_7I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_6_6I1Group_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_6_6I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_6_6I2PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_6_6I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_6_6I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA5_5_6I1ResidualEntropies_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA5_5_6I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA5_5_6I2PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA5_5_6I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA5_5_6I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_1_6I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_1_6I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_2_5I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_2_5I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_3_4I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_3_4I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_4_3I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_4_3I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_5_2I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_5_2I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_6_1I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_6_1I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB2_1_5I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB2_1_5I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB2_2_4I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB2_2_4I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB2_3_3I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB2_3_3I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB2_4_2I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB2_4_2I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB2_5_1I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB2_5_1I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_1_4I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_1_4I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_4_1I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_4_1I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_1_3I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_1_3I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_2_2I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_2_2I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_3_1I0_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_3_1I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_3_1I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB5_1_2I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB5_1_2I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB5_2_1I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB5_2_1I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB6_1_1I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB6_1_1I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z0_5_3Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z0_5_3H2H_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z0_7_1Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z0_8_0Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z1_0_7Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z1_7_0Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z2_0_6Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z2_6_0Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z3_0_5Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z3_5_0Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z4_0_4Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z4_4_0Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z5_0_3Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z5_3_0Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z6_0_2Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z6_2_0Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z7_0_1Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z8_0_0Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.capacityABalls_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.capacityBBalls_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.fourRateBalls_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.halfTable_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.nativeLBBall_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.nativeTBall_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.native_sharp_rate_bound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.native_stageC_balanced_positive` and `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.native_stageC_feasible`.
-- source:
--   OpenAI, Staggered extraction for exact matrix multiplication over every field, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 107; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/LinearAlgebra at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ254M002
import Definitions.Def_OAIQ254M003
import Definitions.Def_OAIQ254M004
import Definitions.Def_OAIQ254M005

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_HistoryChildLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators

noncomputable section

namespace MatrixMultiplication.Staggering

def thirdCapacity (a b : Capacity) (high base : ℝ) (i : Fin 3) : ℝ :=
  high - 3 * balanceFraction a b high base i * (high - base)

end MatrixMultiplication.Staggering

end
end

end MatrixAllFields

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

def pairSumBall (bs : PairSlot → Ball) : Ball :=
  finSumBall 6 (fun i => finSumBall 6 (fun j => bs (i,j)))

def doublePairSumBall (bs : PairSlot × PairSlot → Ball) : Ball :=
  pairSumBall fun i => pairSumBall fun j => bs (i,j)

def singletonBall (support : List Shape) (p : Shape → Ball)
    (priority : Placement) (position : Fin 3) (e : Shape → Ball) : Ball :=
  listSumBall support fun u =>
    if designated priority position u then .mul (p u) (e u) else .exact 0

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
def multLogs (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 0, 0 => logN1
  | 0, 1 => logN10
  | 0, 2 => logN25
  | 0, 3 => logN2
  | 0, 4 => logN10
  | 0, 5 => logN1
  | 1, 0 => logN10
  | 1, 1 => logN100
  | 1, 2 => logN250
  | 1, 3 => logN20
  | 1, 4 => logN100
  | 1, 5 => logN10
  | 2, 0 => logN25
  | 2, 1 => logN250
  | 2, 2 => logN625
  | 2, 3 => logN50
  | 2, 4 => logN250
  | 2, 5 => logN25
  | 3, 0 => logN2
  | 3, 1 => logN20
  | 3, 2 => logN50
  | 3, 3 => logN4
  | 3, 4 => logN20
  | 3, 5 => logN2
  | 4, 0 => logN10
  | 4, 1 => logN100
  | 4, 2 => logN250
  | 4, 3 => logN20
  | 4, 4 => logN100
  | 4, 5 => logN10
  | 5, 0 => logN1
  | 5, 1 => logN10
  | 5, 2 => logN25
  | 5, 3 => logN2
  | 5, 4 => logN10
  | 5, 5 => logN1
  | _, _ => (.exact 0)

end MatrixMultiplication.NativeNumerics

end
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
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def Z0_0_8Raw (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 0, 0 => w195
  | 0, 1 => w195
  | 0, 2 => w195
  | 0, 3 => w195
  | 0, 4 => w195
  | 0, 5 => w195
  | 1, 0 => w195
  | 1, 1 => w195
  | 1, 2 => w195
  | 1, 3 => w195
  | 1, 4 => w195
  | 1, 5 => w195
  | 2, 0 => w195
  | 2, 1 => w195
  | 2, 2 => w195
  | 2, 3 => w195
  | 2, 4 => w195
  | 2, 5 => w195
  | 3, 0 => w195
  | 3, 1 => w195
  | 3, 2 => w195
  | 3, 3 => w195
  | 3, 4 => w195
  | 3, 5 => w195
  | 4, 0 => w195
  | 4, 1 => w195
  | 4, 2 => w195
  | 4, 3 => w195
  | 4, 4 => w195
  | 4, 5 => w195
  | 5, 0 => w195
  | 5, 1 => w195
  | 5, 2 => w195
  | 5, 3 => w195
  | 5, 4 => w195
  | 5, 5 => w195
  | _, _ => (.exact 0)

def Z0_0_8Value (a : PairSlot) : ℝ := (zeroPairLaw (shape 0 0 8) a.1 a.2 : ℝ)
def Z0_0_8H2Value (a : PairSlot) : ℝ := (halfLaw (shape 0 0 8) 2 a : ℝ)

def Z0_1_7Raw (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 0, 0 => w195
  | 0, 1 => w195
  | 0, 2 => w195
  | 0, 3 => w195
  | 0, 4 => w195
  | 0, 5 => w195
  | 1, 0 => w195
  | 1, 1 => w195
  | 1, 2 => w195
  | 1, 3 => w195
  | 1, 4 => w195
  | 1, 5 => w195
  | 2, 0 => w195
  | 2, 1 => w195
  | 2, 2 => w195
  | 2, 3 => w195
  | 2, 4 => w195
  | 2, 5 => w195
  | 3, 0 => w195
  | 3, 1 => w195
  | 3, 2 => w195
  | 3, 3 => w195
  | 3, 4 => w195
  | 3, 5 => w195
  | 4, 0 => w195
  | 4, 1 => w195
  | 4, 2 => w195
  | 4, 3 => w195
  | 4, 4 => w195
  | 4, 5 => w195
  | 5, 0 => w195
  | 5, 1 => w195
  | 5, 2 => w195
  | 5, 3 => w195
  | 5, 4 => w195
  | 5, 5 => w195
  | _, _ => (.exact 0)

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
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def Z0_3_5Raw (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 0, 0 => w195
  | 0, 1 => w195
  | 0, 2 => w195
  | 0, 3 => w195
  | 0, 4 => w195
  | 0, 5 => w195
  | 1, 0 => w195
  | 1, 1 => w195
  | 1, 2 => w195
  | 1, 3 => w195
  | 1, 4 => w195
  | 1, 5 => w172
  | 2, 0 => w195
  | 2, 1 => w195
  | 2, 2 => w195
  | 2, 3 => w195
  | 2, 4 => w209
  | 2, 5 => w195
  | 3, 0 => w195
  | 3, 1 => w195
  | 3, 2 => w195
  | 3, 3 => w195
  | 3, 4 => w195
  | 3, 5 => w195
  | 4, 0 => w195
  | 4, 1 => w195
  | 4, 2 => w209
  | 4, 3 => w195
  | 4, 4 => w195
  | 4, 5 => w195
  | 5, 0 => w195
  | 5, 1 => w172
  | 5, 2 => w195
  | 5, 3 => w195
  | 5, 4 => w195
  | 5, 5 => w195
  | _, _ => (.exact 0)

def Z0_3_5Value (a : PairSlot) : ℝ := (zeroPairLaw (shape 0 3 5) a.1 a.2 : ℝ)
def Z0_3_5H2Value (a : PairSlot) : ℝ := (halfLaw (shape 0 3 5) 2 a : ℝ)

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
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def Z0_4_4Raw (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 0, 0 => w195
  | 0, 1 => w195
  | 0, 2 => w195
  | 0, 3 => w195
  | 0, 4 => w195
  | 0, 5 => w121
  | 1, 0 => w195
  | 1, 1 => w195
  | 1, 2 => w195
  | 1, 3 => w195
  | 1, 4 => w215
  | 1, 5 => w195
  | 2, 0 => w195
  | 2, 1 => w195
  | 2, 2 => w222
  | 2, 3 => w205
  | 2, 4 => w195
  | 2, 5 => w195
  | 3, 0 => w195
  | 3, 1 => w195
  | 3, 2 => w205
  | 3, 3 => w195
  | 3, 4 => w195
  | 3, 5 => w195
  | 4, 0 => w195
  | 4, 1 => w215
  | 4, 2 => w195
  | 4, 3 => w195
  | 4, 4 => w195
  | 4, 5 => w195
  | 5, 0 => w121
  | 5, 1 => w195
  | 5, 2 => w195
  | 5, 3 => w195
  | 5, 4 => w195
  | 5, 5 => w195
  | _, _ => (.exact 0)

def Z0_4_4Value (a : PairSlot) : ℝ := (zeroPairLaw (shape 0 4 4) a.1 a.2 : ℝ)
def Z0_4_4H2Value (a : PairSlot) : ℝ := (halfLaw (shape 0 4 4) 2 a : ℝ)
def Z0_4_4H2Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 5, 0 => ⟨(588303889087378458388880598603 / 50000000000000000000000000000000), (109107079 / 25000000000000000000000000000000)⟩
  | 4, 1 => ⟨(26113887307747879276296106837317 / 100000000000000000000000000000000), (427326087 / 4000000000000000000000000000000)⟩
  | 2, 2 => ⟨(15034073848980370592136607206397 / 50000000000000000000000000000000), (25904605089 / 100000000000000000000000000000000)⟩
  | 2, 3 => ⟨(543150828368552529862213075723 / 3125000000000000000000000000000), (6648634459 / 100000000000000000000000000000000)⟩
  | 3, 2 => ⟨(543150828368552529862213075723 / 3125000000000000000000000000000), (6648634459 / 100000000000000000000000000000000)⟩
  | 3, 3 => ⟨(1688822355885139167546274512777 / 50000000000000000000000000000000), (644133659 / 50000000000000000000000000000000)⟩
  | 1, 4 => ⟨(26113887307747879276296106837317 / 100000000000000000000000000000000), (427326087 / 4000000000000000000000000000000)⟩
  | 0, 5 => ⟨(588303889087378458388880598603 / 50000000000000000000000000000000), (109107079 / 25000000000000000000000000000000)⟩
  | _, _ => (.exact 0)

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
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def Z0_6_2Raw (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 0, 0 => w195
  | 0, 1 => w195
  | 0, 2 => w195
  | 0, 3 => w195
  | 0, 4 => w195
  | 0, 5 => w195
  | 1, 0 => w195
  | 1, 1 => w195
  | 1, 2 => w195
  | 1, 3 => w195
  | 1, 4 => w195
  | 1, 5 => w195
  | 2, 0 => w195
  | 2, 1 => w195
  | 2, 2 => w195
  | 2, 3 => w195
  | 2, 4 => w195
  | 2, 5 => w116
  | 3, 0 => w195
  | 3, 1 => w195
  | 3, 2 => w195
  | 3, 3 => w195
  | 3, 4 => w195
  | 3, 5 => w43
  | 4, 0 => w195
  | 4, 1 => w195
  | 4, 2 => w195
  | 4, 3 => w195
  | 4, 4 => w195
  | 4, 5 => w195
  | 5, 0 => w195
  | 5, 1 => w195
  | 5, 2 => w116
  | 5, 3 => w43
  | 5, 4 => w195
  | 5, 5 => w195
  | _, _ => (.exact 0)

def Z0_6_2Value (a : PairSlot) : ℝ := (zeroPairLaw (shape 0 6 2) a.1 a.2 : ℝ)
def Z0_6_2H2Value (a : PairSlot) : ℝ := (halfLaw (shape 0 6 2) 2 a : ℝ)
def Z0_6_2H2Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 2, 0 => ⟨(29145119833177663734886171853233 / 100000000000000000000000000000000), (2674938617 / 20000000000000000000000000000000)⟩
  | 3, 0 => ⟨(1015323830087268728146699904139 / 20000000000000000000000000000000), (191958983 / 10000000000000000000000000000000)⟩
  | 1, 1 => ⟨(6833509022528220411360048899287 / 25000000000000000000000000000000), (5603431897 / 20000000000000000000000000000000)⟩
  | 0, 2 => ⟨(29145119833177663734886171853233 / 100000000000000000000000000000000), (2674938617 / 20000000000000000000000000000000)⟩
  | 0, 3 => ⟨(1015323830087268728146699904139 / 20000000000000000000000000000000), (191958983 / 10000000000000000000000000000000)⟩
  | _, _ => (.exact 0)

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
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def Z0_2_6Raw (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 0, 0 => w195
  | 0, 1 => w195
  | 0, 2 => w195
  | 0, 3 => w195
  | 0, 4 => w195
  | 0, 5 => w195
  | 1, 0 => w195
  | 1, 1 => w195
  | 1, 2 => w195
  | 1, 3 => w195
  | 1, 4 => w195
  | 1, 5 => w195
  | 2, 0 => w195
  | 2, 1 => w195
  | 2, 2 => w195
  | 2, 3 => w195
  | 2, 4 => w195
  | 2, 5 => w125
  | 3, 0 => w195
  | 3, 1 => w195
  | 3, 2 => w195
  | 3, 3 => w195
  | 3, 4 => w195
  | 3, 5 => w50
  | 4, 0 => w195
  | 4, 1 => w195
  | 4, 2 => w195
  | 4, 3 => w195
  | 4, 4 => w195
  | 4, 5 => w195
  | 5, 0 => w195
  | 5, 1 => w195
  | 5, 2 => w125
  | 5, 3 => w50
  | 5, 4 => w195
  | 5, 5 => w195
  | _, _ => (.exact 0)

def Z0_2_6Value (a : PairSlot) : ℝ := (zeroPairLaw (shape 0 2 6) a.1 a.2 : ℝ)
def Z0_2_6H2Value (a : PairSlot) : ℝ := (halfLaw (shape 0 2 6) 2 a : ℝ)

end MatrixMultiplication.NativeNumerics

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
def CB4_2_2I2R1Raw (a : Fin 6) : Ball := residualBall (below (shape 4 2 2)) B4_2_2Law (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) 1 a
def CB4_2_2I2R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(3924290670247618121826431431639 / 50000000000000000000000000000000), (3 / 10000000000000000000000000000000)⟩ ⟨(19973363265378585772023469851697 / 100000000000000000000000000000000), (8310008839 / 100000000000000000000000000000000)⟩ ⟨(-254483739148179485664331227253563 / 100000000000000000000000000000000), (26469779699 / 25000000000000000000000000000000)⟩ ⟨-4, 3924290670247618121826431431639, 3125000000000000000000000000000⟩]
def CB4_2_2I2R1P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R1Certificates (CB4_2_2I2R1CertificateIndex a)).input
def CB4_2_2I2R1Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R1Certificates (CB4_2_2I2R1CertificateIndex a)).output
def CB4_2_2I2R2Raw (a : Fin 6) : Ball := residualBall (below (shape 4 2 2)) B4_2_2Law (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) 2 a
def CB4_2_2I2R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(54606597188412179771489877547937 / 100000000000000000000000000000000), (63 / 100000000000000000000000000000000)⟩ ⟨(6607567353600587271775121013497 / 20000000000000000000000000000000), (23126793581 / 100000000000000000000000000000000)⟩ ⟨(-30250774145485251926939796014479 / 50000000000000000000000000000000), (1058791187 / 2500000000000000000000000000000)⟩ ⟨-1, 54606597188412179771489877547937, 50000000000000000000000000000000⟩,
   .log ⟨(81925921763941401533420105921 / 12500000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(3295170994711641414745310598131 / 100000000000000000000000000000000), (1249091203 / 100000000000000000000000000000000)⟩ ⟨(-62845855968178721135666464092211 / 12500000000000000000000000000000), (47645603363 / 25000000000000000000000000000000)⟩ ⟨-8, 81925921763941401533420105921, 48828125000000000000000000000⟩]
def CB4_2_2I2R2P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R2Certificates (CB4_2_2I2R2CertificateIndex a)).input
def CB4_2_2I2R2Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R2Certificates (CB4_2_2I2R2CertificateIndex a)).output
def CB4_2_2I2R3Raw (a : Fin 6) : Ball := residualBall (below (shape 4 2 2)) B4_2_2Law (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) 3 a
def CB4_2_2I2R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB4_2_2I2R3P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R3Certificates (CB4_2_2I2R3CertificateIndex a)).input
def CB4_2_2I2R3Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R3Certificates (CB4_2_2I2R3CertificateIndex a)).output
def CB4_2_2I2R4Raw (a : Fin 6) : Ball := residualBall (below (shape 4 2 2)) B4_2_2Law (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) 4 a
def CB4_2_2I2R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB4_2_2I2R4P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R4Certificates (CB4_2_2I2R4CertificateIndex a)).input
def CB4_2_2I2R4Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R4Certificates (CB4_2_2I2R4CertificateIndex a)).output
def CB4_2_2I2R5Raw (a : Fin 6) : Ball := residualBall (below (shape 4 2 2)) B4_2_2Law (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) 5 a
def CB4_2_2I2R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB4_2_2I2R5P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R5Certificates (CB4_2_2I2R5CertificateIndex a)).input
def CB4_2_2I2R5Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R5Certificates (CB4_2_2I2R5CertificateIndex a)).output
def CB4_2_2I2R6Raw (a : Fin 6) : Ball := residualBall (below (shape 4 2 2)) B4_2_2Law (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) 6 a
def CB4_2_2I2R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB4_2_2I2R6P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R6Certificates (CB4_2_2I2R6CertificateIndex a)).input
def CB4_2_2I2R6Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R6Certificates (CB4_2_2I2R6CertificateIndex a)).output
def CB4_2_2I2R7Raw (a : Fin 6) : Ball := residualBall (below (shape 4 2 2)) B4_2_2Law (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) 7 a
def CB4_2_2I2R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB4_2_2I2R7P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R7Certificates (CB4_2_2I2R7CertificateIndex a)).input
def CB4_2_2I2R7Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R7Certificates (CB4_2_2I2R7CertificateIndex a)).output
def CB4_2_2I2R8Raw (a : Fin 6) : Ball := residualBall (below (shape 4 2 2)) B4_2_2Law (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) 8 a
def CB4_2_2I2R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB4_2_2I2R8P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R8Certificates (CB4_2_2I2R8CertificateIndex a)).input
def CB4_2_2I2R8Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R8Certificates (CB4_2_2I2R8CertificateIndex a)).output
def CB4_2_2I2R9Raw (a : Fin 6) : Ball := residualBall (below (shape 4 2 2)) B4_2_2Law (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) 9 a
def CB4_2_2I2R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB4_2_2I2R9P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R9Certificates (CB4_2_2I2R9CertificateIndex a)).input
def CB4_2_2I2R9Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R9Certificates (CB4_2_2I2R9CertificateIndex a)).output
def CB4_2_2I2R10Raw (a : Fin 6) : Ball := residualBall (below (shape 4 2 2)) B4_2_2Law (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) 10 a
def CB4_2_2I2R11Raw (a : Fin 6) : Ball := residualBall (below (shape 4 2 2)) B4_2_2Law (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) 11 a
def CB4_2_2I2R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB4_2_2I2R11P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R11Certificates (CB4_2_2I2R11CertificateIndex a)).input
def CB4_2_2I2R11Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R11Certificates (CB4_2_2I2R11CertificateIndex a)).output
def CB4_2_2I2R12Raw (a : Fin 6) : Ball := residualBall (below (shape 4 2 2)) B4_2_2Law (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) 12 a
def CB4_2_2I2R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB4_2_2I2R12P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R12Certificates (CB4_2_2I2R12CertificateIndex a)).input
def CB4_2_2I2R12Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R12Certificates (CB4_2_2I2R12CertificateIndex a)).output
def CB4_2_2I2R13Raw (a : Fin 6) : Ball := residualBall (below (shape 4 2 2)) B4_2_2Law (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) 13 a
def CB4_2_2I2R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB4_2_2I2R13P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R13Certificates (CB4_2_2I2R13CertificateIndex a)).input
def CB4_2_2I2R13Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R13Certificates (CB4_2_2I2R13CertificateIndex a)).output
def CB4_2_2I2R14Raw (a : Fin 6) : Ball := residualBall (below (shape 4 2 2)) B4_2_2Law (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) 14 a
def CB4_2_2I2R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB4_2_2I2R14P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R14Certificates (CB4_2_2I2R14CertificateIndex a)).input
def CB4_2_2I2R14Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R14Certificates (CB4_2_2I2R14CertificateIndex a)).output
def CB4_2_2I2R15Raw (a : Fin 6) : Ball := residualBall (below (shape 4 2 2)) B4_2_2Law (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) 15 a
def CB4_2_2I2R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB4_2_2I2R15P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R15Certificates (CB4_2_2I2R15CertificateIndex a)).input
def CB4_2_2I2R15Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R15Certificates (CB4_2_2I2R15CertificateIndex a)).output
def CB4_2_2I2R16Raw (a : Fin 6) : Ball := residualBall (below (shape 4 2 2)) B4_2_2Law (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) 16 a
def CB4_2_2I2R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB4_2_2I2R16P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R16Certificates (CB4_2_2I2R16CertificateIndex a)).input
def CB4_2_2I2R16Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R16Certificates (CB4_2_2I2R16CertificateIndex a)).output

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
def CB4_3_1I0Raw (a : Fin 17) : Ball := marginalBall (below (shape 4 3 1)) B4_3_1Law ((stageBPriority (shape 4 3 1)) 0) a
def CB4_3_1I0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(50000000000000000000000000000001 / 100000000000000000000000000000000), (31 / 100000000000000000000000000000000)⟩ ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (2646977967 / 12500000000000000000000000000000)⟩ ⟨(-8664339756999316367715399131291 / 12500000000000000000000000000000), (42351647427 / 100000000000000000000000000000000)⟩ ⟨-1, 50000000000000000000000000000001, 50000000000000000000000000000000⟩]
def CB4_3_1I0P (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I0Certificates (CB4_3_1I0CertificateIndex a)).input
def CB4_3_1I0Terms (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I0Certificates (CB4_3_1I0CertificateIndex a)).output

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
def CB4_3_1I1PairValue (a : PairSlot) : ℝ := pairLaw (below (shape 4 3 1)) (shape 4 3 1) (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 1) a : ℝ)) a
def CB4_3_1I1PairCertificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(663549549127581616184973285819 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩ ⟨(1147190843975657773974584037547 / 20000000000000000000000000000000), (1124096677 / 50000000000000000000000000000000)⟩ ⟨(-216108737750623834291693366203169 / 50000000000000000000000000000000), (42351647479 / 25000000000000000000000000000000)⟩ ⟨-7, 663549549127581616184973285819, 390625000000000000000000000000⟩,
   .log ⟨(22175975409536958176216013675929 / 50000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩ ⟨(90146835953294368688057748091 / 250000000000000000000000000000), (704391819 / 2500000000000000000000000000000)⟩ ⟨(-2540667160308030643941501584461 / 3125000000000000000000000000000), (63527471103 / 100000000000000000000000000000000)⟩ ⟨-2, 22175975409536958176216013675929, 12500000000000000000000000000000⟩,
   .log ⟨(864190016534184083039605215301 / 20000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(13575106757374623747264395272099 / 100000000000000000000000000000000), (1097996127 / 20000000000000000000000000000000)⟩ ⟨(-314169488136817510983487125336409 / 100000000000000000000000000000000), (1985233471 / 1562500000000000000000000000000)⟩ ⟨-5, 864190016534184083039605215301, 625000000000000000000000000000⟩]
def CB4_3_1I1PairCertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 4, 0 => 1
  | 2, 1 => 2
  | 3, 1 => 3
  | 1, 2 => 2
  | 1, 3 => 3
  | 0, 4 => 1
  | _, _ => 0
def CB4_3_1I1PairP (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I1PairCertificates (CB4_3_1I1PairCertificateIndex a)).input
def CB4_3_1I1PairTerms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I1PairCertificates (CB4_3_1I1PairCertificateIndex a)).output

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
def CB4_3_1I1R0Raw (a : Fin 6) : Ball := residualBall (below (shape 4 3 1)) B4_3_1Law (stageBPriority (shape 4 3 1)) 1 (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 1)) 0 a
def CB4_3_1I1R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(663549549127581616184973285819 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩ ⟨(1147190843975657773974584037547 / 20000000000000000000000000000000), (1124096677 / 50000000000000000000000000000000)⟩ ⟨(-216108737750623834291693366203169 / 50000000000000000000000000000000), (42351647479 / 25000000000000000000000000000000)⟩ ⟨-7, 663549549127581616184973285819, 390625000000000000000000000000⟩]
def CB4_3_1I1R0P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I1R0Certificates (CB4_3_1I1R0CertificateIndex a)).input
def CB4_3_1I1R0Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I1R0Certificates (CB4_3_1I1R0CertificateIndex a)).output
def CB4_3_1I1R1Raw (a : Fin 6) : Ball := residualBall (below (shape 4 3 1)) B4_3_1Law (stageBPriority (shape 4 3 1)) 1 (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 1)) 1 a
def CB4_3_1I1R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(48672900901744836767630053428363 / 100000000000000000000000000000000), (1 / 4000000000000000000000000000000)⟩ ⟨(273803228812459785691571806703 / 781250000000000000000000000000), (966270721 / 3125000000000000000000000000000)⟩ ⟨(-3600238802156385008240902157601 / 5000000000000000000000000000000), (635274711 / 1000000000000000000000000000000)⟩ ⟨-2, 48672900901744836767630053428363, 25000000000000000000000000000000⟩]
def CB4_3_1I1R1P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I1R1Certificates (CB4_3_1I1R1CertificateIndex a)).input
def CB4_3_1I1R1Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I1R1Certificates (CB4_3_1I1R1CertificateIndex a)).output
def CB4_3_1I1R2Raw (a : Fin 6) : Ball := residualBall (below (shape 4 3 1)) B4_3_1Law (stageBPriority (shape 4 3 1)) 1 (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 1)) 2 a
def CB4_3_1I1R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(22175975409536958176216013675929 / 50000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩ ⟨(90146835953294368688057748091 / 250000000000000000000000000000), (704391819 / 2500000000000000000000000000000)⟩ ⟨(-2540667160308030643941501584461 / 3125000000000000000000000000000), (63527471103 / 100000000000000000000000000000000)⟩ ⟨-2, 22175975409536958176216013675929, 12500000000000000000000000000000⟩,
   .log ⟨(864190016534184083039605215301 / 20000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(13575106757374623747264395272099 / 100000000000000000000000000000000), (1097996127 / 20000000000000000000000000000000)⟩ ⟨(-314169488136817510983487125336409 / 100000000000000000000000000000000), (1985233471 / 1562500000000000000000000000000)⟩ ⟨-5, 864190016534184083039605215301, 625000000000000000000000000000⟩]
def CB4_3_1I1R2P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I1R2Certificates (CB4_3_1I1R2CertificateIndex a)).input
def CB4_3_1I1R2Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I1R2Certificates (CB4_3_1I1R2CertificateIndex a)).output
def CB4_3_1I1R3Raw (a : Fin 6) : Ball := residualBall (below (shape 4 3 1)) B4_3_1Law (stageBPriority (shape 4 3 1)) 1 (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 1)) 3 a
def CB4_3_1I1R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1293653321378517322144444232489 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩ ⟨(5624416465391076871446041112211 / 100000000000000000000000000000000), (2191533999 / 100000000000000000000000000000000)⟩ ⟨(-434769993818567805721764350077799 / 100000000000000000000000000000000), (3388131797 / 2000000000000000000000000000000)⟩ ⟨-7, 1293653321378517322144444232489, 781250000000000000000000000000⟩]
def CB4_3_1I1R3P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I1R3Certificates (CB4_3_1I1R3CertificateIndex a)).input
def CB4_3_1I1R3Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I1R3Certificates (CB4_3_1I1R3CertificateIndex a)).output
def CB4_3_1I1R4Raw (a : Fin 6) : Ball := residualBall (below (shape 4 3 1)) B4_3_1Law (stageBPriority (shape 4 3 1)) 1 (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 1)) 4 a
def CB4_3_1I1R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB4_3_1I1R4P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I1R4Certificates (CB4_3_1I1R4CertificateIndex a)).input
def CB4_3_1I1R4Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I1R4Certificates (CB4_3_1I1R4CertificateIndex a)).output
def CB4_3_1I1R5Raw (a : Fin 6) : Ball := residualBall (below (shape 4 3 1)) B4_3_1Law (stageBPriority (shape 4 3 1)) 1 (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 1)) 5 a
def CB4_3_1I1R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB4_3_1I1R5P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I1R5Certificates (CB4_3_1I1R5CertificateIndex a)).input
def CB4_3_1I1R5Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I1R5Certificates (CB4_3_1I1R5CertificateIndex a)).output
def CB4_3_1I1R6Raw (a : Fin 6) : Ball := residualBall (below (shape 4 3 1)) B4_3_1Law (stageBPriority (shape 4 3 1)) 1 (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 1)) 6 a
def CB4_3_1I1R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB4_3_1I1R6P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I1R6Certificates (CB4_3_1I1R6CertificateIndex a)).input
def CB4_3_1I1R6Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I1R6Certificates (CB4_3_1I1R6CertificateIndex a)).output
def CB4_3_1I1R7Raw (a : Fin 6) : Ball := residualBall (below (shape 4 3 1)) B4_3_1Law (stageBPriority (shape 4 3 1)) 1 (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 1)) 7 a
def CB4_3_1I1R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB4_3_1I1R7P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I1R7Certificates (CB4_3_1I1R7CertificateIndex a)).input
def CB4_3_1I1R7Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I1R7Certificates (CB4_3_1I1R7CertificateIndex a)).output
def CB4_3_1I1R8Raw (a : Fin 6) : Ball := residualBall (below (shape 4 3 1)) B4_3_1Law (stageBPriority (shape 4 3 1)) 1 (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 1)) 8 a
def CB4_3_1I1R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB4_3_1I1R8P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I1R8Certificates (CB4_3_1I1R8CertificateIndex a)).input
def CB4_3_1I1R8Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I1R8Certificates (CB4_3_1I1R8CertificateIndex a)).output
def CB4_3_1I1R9Raw (a : Fin 6) : Ball := residualBall (below (shape 4 3 1)) B4_3_1Law (stageBPriority (shape 4 3 1)) 1 (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 1)) 9 a
def CB4_3_1I1R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB4_3_1I1R9P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I1R9Certificates (CB4_3_1I1R9CertificateIndex a)).input
def CB4_3_1I1R9Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I1R9Certificates (CB4_3_1I1R9CertificateIndex a)).output
def CB4_3_1I1R10Raw (a : Fin 6) : Ball := residualBall (below (shape 4 3 1)) B4_3_1Law (stageBPriority (shape 4 3 1)) 1 (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 1)) 10 a
def CB4_3_1I1R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB4_3_1I1R10P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I1R10Certificates (CB4_3_1I1R10CertificateIndex a)).input
def CB4_3_1I1R10Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I1R10Certificates (CB4_3_1I1R10CertificateIndex a)).output
def CB4_3_1I1R11Raw (a : Fin 6) : Ball := residualBall (below (shape 4 3 1)) B4_3_1Law (stageBPriority (shape 4 3 1)) 1 (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 1)) 11 a
def CB4_3_1I1R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB4_3_1I1R11P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I1R11Certificates (CB4_3_1I1R11CertificateIndex a)).input
def CB4_3_1I1R11Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I1R11Certificates (CB4_3_1I1R11CertificateIndex a)).output
def CB4_3_1I1R12Raw (a : Fin 6) : Ball := residualBall (below (shape 4 3 1)) B4_3_1Law (stageBPriority (shape 4 3 1)) 1 (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 1)) 12 a
def CB4_3_1I1R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB4_3_1I1R12P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I1R12Certificates (CB4_3_1I1R12CertificateIndex a)).input
def CB4_3_1I1R12Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I1R12Certificates (CB4_3_1I1R12CertificateIndex a)).output
def CB4_3_1I1R13Raw (a : Fin 6) : Ball := residualBall (below (shape 4 3 1)) B4_3_1Law (stageBPriority (shape 4 3 1)) 1 (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 1)) 13 a
def CB4_3_1I1R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB4_3_1I1R13P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I1R13Certificates (CB4_3_1I1R13CertificateIndex a)).input
def CB4_3_1I1R13Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I1R13Certificates (CB4_3_1I1R13CertificateIndex a)).output
def CB4_3_1I1R14Raw (a : Fin 6) : Ball := residualBall (below (shape 4 3 1)) B4_3_1Law (stageBPriority (shape 4 3 1)) 1 (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 1)) 14 a
def CB4_3_1I1R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB4_3_1I1R14P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I1R14Certificates (CB4_3_1I1R14CertificateIndex a)).input
def CB4_3_1I1R14Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I1R14Certificates (CB4_3_1I1R14CertificateIndex a)).output
def CB4_3_1I1R15Raw (a : Fin 6) : Ball := residualBall (below (shape 4 3 1)) B4_3_1Law (stageBPriority (shape 4 3 1)) 1 (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 1)) 15 a
def CB4_3_1I1R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB4_3_1I1R15P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I1R15Certificates (CB4_3_1I1R15CertificateIndex a)).input
def CB4_3_1I1R15Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I1R15Certificates (CB4_3_1I1R15CertificateIndex a)).output
def CB4_3_1I1R16Raw (a : Fin 6) : Ball := residualBall (below (shape 4 3 1)) B4_3_1Law (stageBPriority (shape 4 3 1)) 1 (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 1)) 16 a
def CB4_3_1I1R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB4_3_1I1R16P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I1R16Certificates (CB4_3_1I1R16CertificateIndex a)).input
def CB4_3_1I1R16Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I1R16Certificates (CB4_3_1I1R16CertificateIndex a)).output

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
def CB4_3_1I2PairValue (a : PairSlot) : ℝ := pairLaw (below (shape 4 3 1)) (shape 4 3 1) (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 2) a : ℝ)) a
def CB4_3_1I2PairCertificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(33445776876645910225502339149 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(66916637569092300013809787887 / 25000000000000000000000000000000), (46035727 / 50000000000000000000000000000000)⟩ ⟨(-160059998763713561144352850920053 / 20000000000000000000000000000000), (68821427717 / 25000000000000000000000000000000)⟩ ⟨-12, 33445776876645910225502339149, 24414062500000000000000000000⟩,
   .log ⟨(7861396357689534306132328191817 / 100000000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩ ⟨(999657496337087923571046141681 / 5000000000000000000000000000000), (416178861 / 5000000000000000000000000000000)⟩ ⟨(-254320594167544918853353365611073 / 100000000000000000000000000000000), (10587911863 / 10000000000000000000000000000000)⟩ ⟨-4, 7861396357689534306132328191817, 6250000000000000000000000000000⟩,
   .log ⟨(1517934657342094088384406991891 / 2000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩ ⟨(261650711370711363939136650333 / 1250000000000000000000000000000), (32143516697 / 100000000000000000000000000000000)⟩ ⟨(-13789827387108331031511443051951 / 50000000000000000000000000000000), (42351647397 / 100000000000000000000000000000000)⟩ ⟨-1, 1517934657342094088384406991891, 1000000000000000000000000000000⟩,
   .log ⟨(4144793288664198085105361786561 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(13194192050951886106583167249909 / 100000000000000000000000000000000), (2633082361 / 50000000000000000000000000000000)⟩ ⟨(-318331726868921065296730018238409 / 100000000000000000000000000000000), (63527471073 / 50000000000000000000000000000000)⟩ ⟨-5, 4144793288664198085105361786561, 3125000000000000000000000000000⟩,
   .log ⟨(23996286434538977853265770399 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(100004840208826547166857491469 / 50000000000000000000000000000000), (71139769 / 100000000000000000000000000000000)⟩ ⟨(-833502637848870660423137584477063 / 100000000000000000000000000000000), (296461535729 / 100000000000000000000000000000000)⟩ ⟨-13, 23996286434538977853265770399, 12207031250000000000000000000⟩]
def CB4_3_1I2PairCertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 0, 5 => 1
  | 1, 4 => 2
  | 2, 2 => 3
  | 2, 3 => 4
  | 3, 2 => 4
  | 3, 3 => 5
  | 4, 1 => 2
  | 5, 0 => 1
  | _, _ => 0
def CB4_3_1I2PairP (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I2PairCertificates (CB4_3_1I2PairCertificateIndex a)).input
def CB4_3_1I2PairTerms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I2PairCertificates (CB4_3_1I2PairCertificateIndex a)).output

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
def CB4_3_1I2R0Raw (a : Fin 6) : Ball := residualBall (below (shape 4 3 1)) B4_3_1Law (stageBPriority (shape 4 3 1)) 2 (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 2)) 0 a
def CB4_3_1I2R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(33445776876645910225502339149 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(66916637569092300013809787887 / 25000000000000000000000000000000), (46035727 / 50000000000000000000000000000000)⟩ ⟨(-160059998763713561144352850920053 / 20000000000000000000000000000000), (68821427717 / 25000000000000000000000000000000)⟩ ⟨-12, 33445776876645910225502339149, 24414062500000000000000000000⟩]
def CB4_3_1I2R0P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I2R0Certificates (CB4_3_1I2R0CertificateIndex a)).input
def CB4_3_1I2R0Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I2R0Certificates (CB4_3_1I2R0CertificateIndex a)).output
def CB4_3_1I2R1Raw (a : Fin 6) : Ball := residualBall (below (shape 4 3 1)) B4_3_1Law (stageBPriority (shape 4 3 1)) 2 (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 2)) 1 a
def CB4_3_1I2R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(205241969884719280749621373729 / 3125000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩ ⟨(17883963881894316763402895444343 / 100000000000000000000000000000000), (869233559 / 12500000000000000000000000000000)⟩ ⟨(-13614999690928390286088220368213 / 5000000000000000000000000000000), (105879118597 / 100000000000000000000000000000000)⟩ ⟨-4, 205241969884719280749621373729, 195312500000000000000000000000⟩]
def CB4_3_1I2R1P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I2R1Certificates (CB4_3_1I2R1CertificateIndex a)).input
def CB4_3_1I2R1Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I2R1Certificates (CB4_3_1I2R1CertificateIndex a)).output
def CB4_3_1I2R2Raw (a : Fin 6) : Ball := residualBall (below (shape 4 3 1)) B4_3_1Law (stageBPriority (shape 4 3 1)) 2 (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 2)) 2 a
def CB4_3_1I2R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(2099011593102353882017205157611 / 5000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩ ⟨(36437638457790357055348919873311 / 100000000000000000000000000000000), (26668979669 / 100000000000000000000000000000000)⟩ ⟨(-347188539382341108541610836743 / 400000000000000000000000000000), (31763735541 / 50000000000000000000000000000000)⟩ ⟨-2, 2099011593102353882017205157611, 1250000000000000000000000000000⟩,
   .log ⟨(24985200677348428659613263363 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(83515580203663942172171693191 / 10000000000000000000000000000000), (290995221 / 100000000000000000000000000000000)⟩ ⟨(-668520387585913035565075107393799 / 100000000000000000000000000000000), (232934061313 / 100000000000000000000000000000000)⟩ ⟨-10, 24985200677348428659613263363, 19531250000000000000000000000⟩]
def CB4_3_1I2R2P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I2R2Certificates (CB4_3_1I2R2CertificateIndex a)).input
def CB4_3_1I2R2Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I2R2Certificates (CB4_3_1I2R2CertificateIndex a)).output
def CB4_3_1I2R3Raw (a : Fin 6) : Ball := residualBall (below (shape 4 3 1)) B4_3_1Law (stageBPriority (shape 4 3 1)) 2 (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 2)) 3 a
def CB4_3_1I2R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB4_3_1I2R3P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I2R3Certificates (CB4_3_1I2R3CertificateIndex a)).input
def CB4_3_1I2R3Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I2R3Certificates (CB4_3_1I2R3CertificateIndex a)).output
def CB4_3_1I2R4Raw (a : Fin 6) : Ball := residualBall (below (shape 4 3 1)) B4_3_1Law (stageBPriority (shape 4 3 1)) 2 (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 2)) 4 a
def CB4_3_1I2R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB4_3_1I2R4P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I2R4Certificates (CB4_3_1I2R4CertificateIndex a)).input
def CB4_3_1I2R4Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I2R4Certificates (CB4_3_1I2R4CertificateIndex a)).output
def CB4_3_1I2R5Raw (a : Fin 6) : Ball := residualBall (below (shape 4 3 1)) B4_3_1Law (stageBPriority (shape 4 3 1)) 2 (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 2)) 5 a
def CB4_3_1I2R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB4_3_1I2R5P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I2R5Certificates (CB4_3_1I2R5CertificateIndex a)).input
def CB4_3_1I2R5Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I2R5Certificates (CB4_3_1I2R5CertificateIndex a)).output
def CB4_3_1I2R6Raw (a : Fin 6) : Ball := residualBall (below (shape 4 3 1)) B4_3_1Law (stageBPriority (shape 4 3 1)) 2 (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 2)) 6 a
def CB4_3_1I2R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB4_3_1I2R6P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I2R6Certificates (CB4_3_1I2R6CertificateIndex a)).input
def CB4_3_1I2R6Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I2R6Certificates (CB4_3_1I2R6CertificateIndex a)).output
def CB4_3_1I2R7Raw (a : Fin 6) : Ball := residualBall (below (shape 4 3 1)) B4_3_1Law (stageBPriority (shape 4 3 1)) 2 (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 2)) 7 a
def CB4_3_1I2R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB4_3_1I2R7P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I2R7Certificates (CB4_3_1I2R7CertificateIndex a)).input
def CB4_3_1I2R7Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I2R7Certificates (CB4_3_1I2R7CertificateIndex a)).output
def CB4_3_1I2R8Raw (a : Fin 6) : Ball := residualBall (below (shape 4 3 1)) B4_3_1Law (stageBPriority (shape 4 3 1)) 2 (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 2)) 8 a
def CB4_3_1I2R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB4_3_1I2R8P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I2R8Certificates (CB4_3_1I2R8CertificateIndex a)).input
def CB4_3_1I2R8Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I2R8Certificates (CB4_3_1I2R8CertificateIndex a)).output
def CB4_3_1I2R9Raw (a : Fin 6) : Ball := residualBall (below (shape 4 3 1)) B4_3_1Law (stageBPriority (shape 4 3 1)) 2 (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 2)) 9 a
def CB4_3_1I2R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB4_3_1I2R9P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I2R9Certificates (CB4_3_1I2R9CertificateIndex a)).input
def CB4_3_1I2R9Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I2R9Certificates (CB4_3_1I2R9CertificateIndex a)).output
def CB4_3_1I2R10Raw (a : Fin 6) : Ball := residualBall (below (shape 4 3 1)) B4_3_1Law (stageBPriority (shape 4 3 1)) 2 (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 2)) 10 a
def CB4_3_1I2R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB4_3_1I2R10P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I2R10Certificates (CB4_3_1I2R10CertificateIndex a)).input
def CB4_3_1I2R10Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I2R10Certificates (CB4_3_1I2R10CertificateIndex a)).output
def CB4_3_1I2R11Raw (a : Fin 6) : Ball := residualBall (below (shape 4 3 1)) B4_3_1Law (stageBPriority (shape 4 3 1)) 2 (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 2)) 11 a
def CB4_3_1I2R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB4_3_1I2R11P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I2R11Certificates (CB4_3_1I2R11CertificateIndex a)).input
def CB4_3_1I2R11Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I2R11Certificates (CB4_3_1I2R11CertificateIndex a)).output
def CB4_3_1I2R12Raw (a : Fin 6) : Ball := residualBall (below (shape 4 3 1)) B4_3_1Law (stageBPriority (shape 4 3 1)) 2 (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 2)) 12 a
def CB4_3_1I2R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB4_3_1I2R12P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I2R12Certificates (CB4_3_1I2R12CertificateIndex a)).input
def CB4_3_1I2R12Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I2R12Certificates (CB4_3_1I2R12CertificateIndex a)).output
def CB4_3_1I2R13Raw (a : Fin 6) : Ball := residualBall (below (shape 4 3 1)) B4_3_1Law (stageBPriority (shape 4 3 1)) 2 (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 2)) 13 a
def CB4_3_1I2R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB4_3_1I2R13P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I2R13Certificates (CB4_3_1I2R13CertificateIndex a)).input
def CB4_3_1I2R13Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I2R13Certificates (CB4_3_1I2R13CertificateIndex a)).output
def CB4_3_1I2R14Raw (a : Fin 6) : Ball := residualBall (below (shape 4 3 1)) B4_3_1Law (stageBPriority (shape 4 3 1)) 2 (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 2)) 14 a
def CB4_3_1I2R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB4_3_1I2R14P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I2R14Certificates (CB4_3_1I2R14CertificateIndex a)).input
def CB4_3_1I2R14Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I2R14Certificates (CB4_3_1I2R14CertificateIndex a)).output
def CB4_3_1I2R15Raw (a : Fin 6) : Ball := residualBall (below (shape 4 3 1)) B4_3_1Law (stageBPriority (shape 4 3 1)) 2 (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 2)) 15 a
def CB4_3_1I2R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB4_3_1I2R15P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I2R15Certificates (CB4_3_1I2R15CertificateIndex a)).input
def CB4_3_1I2R15Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I2R15Certificates (CB4_3_1I2R15CertificateIndex a)).output
def CB4_3_1I2R16Raw (a : Fin 6) : Ball := residualBall (below (shape 4 3 1)) B4_3_1Law (stageBPriority (shape 4 3 1)) 2 (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 2)) 16 a
def CB4_3_1I2R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB4_3_1I2R16P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I2R16Certificates (CB4_3_1I2R16CertificateIndex a)).input
def CB4_3_1I2R16Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I2R16Certificates (CB4_3_1I2R16CertificateIndex a)).output

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
def CB5_1_2I0Raw (a : Fin 17) : Ball := marginalBall (below (shape 5 1 2)) B5_1_2Law ((stageBPriority (shape 5 1 2)) 0) a
def CB5_1_2I0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1 / 2), (53 / 100000000000000000000000000000000)⟩ ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823773 / 100000000000000000000000000000000)⟩ ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (42351647471 / 100000000000000000000000000000000)⟩ ⟨-1, 1, 1⟩]
def CB5_1_2I0P (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I0Certificates (CB5_1_2I0CertificateIndex a)).input
def CB5_1_2I0Terms (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I0Certificates (CB5_1_2I0CertificateIndex a)).output

end MatrixMultiplication.NativeNumerics

end
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
def Z0_1_7Value (a : PairSlot) : ℝ := (zeroPairLaw (shape 0 1 7) a.1 a.2 : ℝ)
def Z0_1_7Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 4, 5 => ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
  | 5, 4 => ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
  | _, _ => (.exact 0)
def Z0_1_7H2Value (a : PairSlot) : ℝ := (halfLaw (shape 0 1 7) 2 a : ℝ)
def Z0_1_7H2Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 4, 5 => ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
  | 5, 4 => ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
  | _, _ => (.exact 0)

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
def Z0_5_3Raw (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 0, 0 => w195
  | 0, 1 => w195
  | 0, 2 => w195
  | 0, 3 => w195
  | 0, 4 => w195
  | 0, 5 => w195
  | 1, 0 => w195
  | 1, 1 => w195
  | 1, 2 => w195
  | 1, 3 => w195
  | 1, 4 => w195
  | 1, 5 => w158
  | 2, 0 => w195
  | 2, 1 => w195
  | 2, 2 => w195
  | 2, 3 => w195
  | 2, 4 => w211
  | 2, 5 => w195
  | 3, 0 => w195
  | 3, 1 => w195
  | 3, 2 => w195
  | 3, 3 => w195
  | 3, 4 => w195
  | 3, 5 => w195
  | 4, 0 => w195
  | 4, 1 => w195
  | 4, 2 => w211
  | 4, 3 => w195
  | 4, 4 => w195
  | 4, 5 => w195
  | 5, 0 => w195
  | 5, 1 => w158
  | 5, 2 => w195
  | 5, 3 => w195
  | 5, 4 => w195
  | 5, 5 => w195
  | _, _ => (.exact 0)

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
def Z0_5_3Value (a : PairSlot) : ℝ := (zeroPairLaw (shape 0 5 3) a.1 a.2 : ℝ)
def Z0_5_3H2Value (a : PairSlot) : ℝ := (halfLaw (shape 0 5 3) 2 a : ℝ)
def Z0_5_3H2Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 4, 0 => ⟨(8277526209207412807813577207303 / 100000000000000000000000000000000), (6397079 / 200000000000000000000000000000)⟩
  | 2, 1 => ⟨(18077101393929149380776110958019 / 50000000000000000000000000000000), (5568125837 / 20000000000000000000000000000000)⟩
  | 3, 1 => ⟨(1614325147848684263111295424987 / 12500000000000000000000000000000), (5104607757 / 100000000000000000000000000000000)⟩
  | 1, 2 => ⟨(18077101393929149380776110958019 / 50000000000000000000000000000000), (5568125837 / 20000000000000000000000000000000)⟩
  | 1, 3 => ⟨(1614325147848684263111295424987 / 12500000000000000000000000000000), (5104607757 / 100000000000000000000000000000000)⟩
  | 0, 4 => ⟨(8277526209207412807813577207303 / 100000000000000000000000000000000), (6397079 / 200000000000000000000000000000)⟩
  | _, _ => (.exact 0)

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
def Z0_7_1Raw (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 0, 0 => w195
  | 0, 1 => w195
  | 0, 2 => w195
  | 0, 3 => w195
  | 0, 4 => w195
  | 0, 5 => w195
  | 1, 0 => w195
  | 1, 1 => w195
  | 1, 2 => w195
  | 1, 3 => w195
  | 1, 4 => w195
  | 1, 5 => w195
  | 2, 0 => w195
  | 2, 1 => w195
  | 2, 2 => w195
  | 2, 3 => w195
  | 2, 4 => w195
  | 2, 5 => w195
  | 3, 0 => w195
  | 3, 1 => w195
  | 3, 2 => w195
  | 3, 3 => w195
  | 3, 4 => w195
  | 3, 5 => w195
  | 4, 0 => w195
  | 4, 1 => w195
  | 4, 2 => w195
  | 4, 3 => w195
  | 4, 4 => w195
  | 4, 5 => w195
  | 5, 0 => w195
  | 5, 1 => w195
  | 5, 2 => w195
  | 5, 3 => w195
  | 5, 4 => w195
  | 5, 5 => w195
  | _, _ => (.exact 0)

def Z0_7_1Value (a : PairSlot) : ℝ := (zeroPairLaw (shape 0 7 1) a.1 a.2 : ℝ)
def Z0_7_1H2Value (a : PairSlot) : ℝ := (halfLaw (shape 0 7 1) 2 a : ℝ)
def Z0_7_1H2Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 1, 0 => ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
  | 0, 1 => ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
  | _, _ => (.exact 0)

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
def Z0_8_0Raw (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 0, 0 => w195
  | 0, 1 => w195
  | 0, 2 => w195
  | 0, 3 => w195
  | 0, 4 => w195
  | 0, 5 => w195
  | 1, 0 => w195
  | 1, 1 => w195
  | 1, 2 => w195
  | 1, 3 => w195
  | 1, 4 => w195
  | 1, 5 => w195
  | 2, 0 => w195
  | 2, 1 => w195
  | 2, 2 => w195
  | 2, 3 => w195
  | 2, 4 => w195
  | 2, 5 => w195
  | 3, 0 => w195
  | 3, 1 => w195
  | 3, 2 => w195
  | 3, 3 => w195
  | 3, 4 => w195
  | 3, 5 => w195
  | 4, 0 => w195
  | 4, 1 => w195
  | 4, 2 => w195
  | 4, 3 => w195
  | 4, 4 => w195
  | 4, 5 => w195
  | 5, 0 => w195
  | 5, 1 => w195
  | 5, 2 => w195
  | 5, 3 => w195
  | 5, 4 => w195
  | 5, 5 => w195
  | _, _ => (.exact 0)

def Z0_8_0Value (a : PairSlot) : ℝ := (zeroPairLaw (shape 0 8 0) a.1 a.2 : ℝ)

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
def Z1_0_7Raw (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 0, 0 => w195
  | 0, 1 => w195
  | 0, 2 => w195
  | 0, 3 => w195
  | 0, 4 => w195
  | 0, 5 => w195
  | 1, 0 => w195
  | 1, 1 => w195
  | 1, 2 => w195
  | 1, 3 => w195
  | 1, 4 => w195
  | 1, 5 => w195
  | 2, 0 => w195
  | 2, 1 => w195
  | 2, 2 => w195
  | 2, 3 => w195
  | 2, 4 => w195
  | 2, 5 => w195
  | 3, 0 => w195
  | 3, 1 => w195
  | 3, 2 => w195
  | 3, 3 => w195
  | 3, 4 => w195
  | 3, 5 => w195
  | 4, 0 => w195
  | 4, 1 => w195
  | 4, 2 => w195
  | 4, 3 => w195
  | 4, 4 => w195
  | 4, 5 => w195
  | 5, 0 => w195
  | 5, 1 => w195
  | 5, 2 => w195
  | 5, 3 => w195
  | 5, 4 => w195
  | 5, 5 => w195
  | _, _ => (.exact 0)

def Z1_0_7Value (a : PairSlot) : ℝ := (zeroPairLaw (shape 1 0 7) a.1 a.2 : ℝ)
def Z1_0_7H2Value (a : PairSlot) : ℝ := (halfLaw (shape 1 0 7) 2 a : ℝ)

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
def Z1_7_0Raw (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 0, 0 => w195
  | 0, 1 => w195
  | 0, 2 => w195
  | 0, 3 => w195
  | 0, 4 => w195
  | 0, 5 => w195
  | 1, 0 => w195
  | 1, 1 => w195
  | 1, 2 => w195
  | 1, 3 => w195
  | 1, 4 => w195
  | 1, 5 => w195
  | 2, 0 => w195
  | 2, 1 => w195
  | 2, 2 => w195
  | 2, 3 => w195
  | 2, 4 => w195
  | 2, 5 => w195
  | 3, 0 => w195
  | 3, 1 => w195
  | 3, 2 => w195
  | 3, 3 => w195
  | 3, 4 => w195
  | 3, 5 => w195
  | 4, 0 => w195
  | 4, 1 => w195
  | 4, 2 => w195
  | 4, 3 => w195
  | 4, 4 => w195
  | 4, 5 => w195
  | 5, 0 => w195
  | 5, 1 => w195
  | 5, 2 => w195
  | 5, 3 => w195
  | 5, 4 => w195
  | 5, 5 => w195
  | _, _ => (.exact 0)

def Z1_7_0Value (a : PairSlot) : ℝ := (zeroPairLaw (shape 1 7 0) a.1 a.2 : ℝ)
def Z1_7_0H1Value (a : PairSlot) : ℝ := (halfLaw (shape 1 7 0) 1 a : ℝ)

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
def Z2_0_6Raw (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 0, 0 => w195
  | 0, 1 => w195
  | 0, 2 => w195
  | 0, 3 => w195
  | 0, 4 => w195
  | 0, 5 => w195
  | 1, 0 => w195
  | 1, 1 => w195
  | 1, 2 => w195
  | 1, 3 => w195
  | 1, 4 => w195
  | 1, 5 => w195
  | 2, 0 => w195
  | 2, 1 => w195
  | 2, 2 => w195
  | 2, 3 => w195
  | 2, 4 => w195
  | 2, 5 => w136
  | 3, 0 => w195
  | 3, 1 => w195
  | 3, 2 => w195
  | 3, 3 => w195
  | 3, 4 => w195
  | 3, 5 => w54
  | 4, 0 => w195
  | 4, 1 => w195
  | 4, 2 => w195
  | 4, 3 => w195
  | 4, 4 => w195
  | 4, 5 => w195
  | 5, 0 => w195
  | 5, 1 => w195
  | 5, 2 => w136
  | 5, 3 => w54
  | 5, 4 => w195
  | 5, 5 => w195
  | _, _ => (.exact 0)

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
def Z2_0_6Value (a : PairSlot) : ℝ := (zeroPairLaw (shape 2 0 6) a.1 a.2 : ℝ)
def Z2_0_6H2Value (a : PairSlot) : ℝ := (halfLaw (shape 2 0 6) 2 a : ℝ)

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
def Z2_6_0Raw (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 0, 0 => w195
  | 0, 1 => w195
  | 0, 2 => w195
  | 0, 3 => w195
  | 0, 4 => w195
  | 0, 5 => w195
  | 1, 0 => w195
  | 1, 1 => w195
  | 1, 2 => w195
  | 1, 3 => w195
  | 1, 4 => w195
  | 1, 5 => w195
  | 2, 0 => w195
  | 2, 1 => w195
  | 2, 2 => w195
  | 2, 3 => w195
  | 2, 4 => w195
  | 2, 5 => w122
  | 3, 0 => w195
  | 3, 1 => w195
  | 3, 2 => w195
  | 3, 3 => w195
  | 3, 4 => w195
  | 3, 5 => w49
  | 4, 0 => w195
  | 4, 1 => w195
  | 4, 2 => w195
  | 4, 3 => w195
  | 4, 4 => w195
  | 4, 5 => w195
  | 5, 0 => w195
  | 5, 1 => w195
  | 5, 2 => w122
  | 5, 3 => w49
  | 5, 4 => w195
  | 5, 5 => w195
  | _, _ => (.exact 0)

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
def Z2_6_0Value (a : PairSlot) : ℝ := (zeroPairLaw (shape 2 6 0) a.1 a.2 : ℝ)
def Z2_6_0H1Value (a : PairSlot) : ℝ := (halfLaw (shape 2 6 0) 1 a : ℝ)

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
def Z3_0_5Raw (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 0, 0 => w195
  | 0, 1 => w195
  | 0, 2 => w195
  | 0, 3 => w195
  | 0, 4 => w195
  | 0, 5 => w195
  | 1, 0 => w195
  | 1, 1 => w195
  | 1, 2 => w195
  | 1, 3 => w195
  | 1, 4 => w195
  | 1, 5 => w189
  | 2, 0 => w195
  | 2, 1 => w195
  | 2, 2 => w195
  | 2, 3 => w195
  | 2, 4 => w202
  | 2, 5 => w195
  | 3, 0 => w195
  | 3, 1 => w195
  | 3, 2 => w195
  | 3, 3 => w195
  | 3, 4 => w195
  | 3, 5 => w195
  | 4, 0 => w195
  | 4, 1 => w195
  | 4, 2 => w202
  | 4, 3 => w195
  | 4, 4 => w195
  | 4, 5 => w195
  | 5, 0 => w195
  | 5, 1 => w189
  | 5, 2 => w195
  | 5, 3 => w195
  | 5, 4 => w195
  | 5, 5 => w195
  | _, _ => (.exact 0)

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
def Z3_0_5Value (a : PairSlot) : ℝ := (zeroPairLaw (shape 3 0 5) a.1 a.2 : ℝ)
def Z3_0_5H2Value (a : PairSlot) : ℝ := (halfLaw (shape 3 0 5) 2 a : ℝ)

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
def Z3_5_0Raw (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 0, 0 => w195
  | 0, 1 => w195
  | 0, 2 => w195
  | 0, 3 => w195
  | 0, 4 => w195
  | 0, 5 => w195
  | 1, 0 => w195
  | 1, 1 => w195
  | 1, 2 => w195
  | 1, 3 => w195
  | 1, 4 => w195
  | 1, 5 => w165
  | 2, 0 => w195
  | 2, 1 => w195
  | 2, 2 => w195
  | 2, 3 => w195
  | 2, 4 => w207
  | 2, 5 => w195
  | 3, 0 => w195
  | 3, 1 => w195
  | 3, 2 => w195
  | 3, 3 => w195
  | 3, 4 => w195
  | 3, 5 => w195
  | 4, 0 => w195
  | 4, 1 => w195
  | 4, 2 => w207
  | 4, 3 => w195
  | 4, 4 => w195
  | 4, 5 => w195
  | 5, 0 => w195
  | 5, 1 => w165
  | 5, 2 => w195
  | 5, 3 => w195
  | 5, 4 => w195
  | 5, 5 => w195
  | _, _ => (.exact 0)

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
def Z3_5_0Value (a : PairSlot) : ℝ := (zeroPairLaw (shape 3 5 0) a.1 a.2 : ℝ)
def Z3_5_0H1Value (a : PairSlot) : ℝ := (halfLaw (shape 3 5 0) 1 a : ℝ)

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
def Z4_0_4Raw (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 0, 0 => w195
  | 0, 1 => w195
  | 0, 2 => w195
  | 0, 3 => w195
  | 0, 4 => w195
  | 0, 5 => w132
  | 1, 0 => w195
  | 1, 1 => w195
  | 1, 2 => w195
  | 1, 3 => w195
  | 1, 4 => w213
  | 1, 5 => w195
  | 2, 0 => w195
  | 2, 1 => w195
  | 2, 2 => w220
  | 2, 3 => w206
  | 2, 4 => w195
  | 2, 5 => w195
  | 3, 0 => w195
  | 3, 1 => w195
  | 3, 2 => w206
  | 3, 3 => w195
  | 3, 4 => w195
  | 3, 5 => w195
  | 4, 0 => w195
  | 4, 1 => w213
  | 4, 2 => w195
  | 4, 3 => w195
  | 4, 4 => w195
  | 4, 5 => w195
  | 5, 0 => w132
  | 5, 1 => w195
  | 5, 2 => w195
  | 5, 3 => w195
  | 5, 4 => w195
  | 5, 5 => w195
  | _, _ => (.exact 0)

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
def Z4_0_4Value (a : PairSlot) : ℝ := (zeroPairLaw (shape 4 0 4) a.1 a.2 : ℝ)
def Z4_0_4H2Value (a : PairSlot) : ℝ := (halfLaw (shape 4 0 4) 2 a : ℝ)
def Z4_0_4H2Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 5, 0 => ⟨(1626115430860444246284949942957 / 100000000000000000000000000000000), (116871387 / 20000000000000000000000000000000)⟩
  | 4, 1 => ⟨(837392469762340720305966731003 / 3125000000000000000000000000000), (1123648383 / 10000000000000000000000000000000)⟩
  | 2, 2 => ⟨(31338440079614690320574653450617 / 100000000000000000000000000000000), (77498073 / 312500000000000000000000000000)⟩
  | 2, 3 => ⟨(18303731318867196612732623716901 / 100000000000000000000000000000000), (7214619983 / 100000000000000000000000000000000)⟩
  | 3, 2 => ⟨(18303731318867196612732623716901 / 100000000000000000000000000000000), (7214619983 / 100000000000000000000000000000000)⟩
  | 3, 3 => ⟨(3602380400946510922725768272093 / 100000000000000000000000000000000), (349134453 / 25000000000000000000000000000000)⟩
  | 1, 4 => ⟨(837392469762340720305966731003 / 3125000000000000000000000000000), (1123648383 / 10000000000000000000000000000000)⟩
  | 0, 5 => ⟨(1626115430860444246284949942957 / 100000000000000000000000000000000), (116871387 / 20000000000000000000000000000000)⟩
  | _, _ => (.exact 0)

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
def Z4_4_0Raw (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 0, 0 => w195
  | 0, 1 => w195
  | 0, 2 => w195
  | 0, 3 => w195
  | 0, 4 => w195
  | 0, 5 => w123
  | 1, 0 => w195
  | 1, 1 => w195
  | 1, 2 => w195
  | 1, 3 => w195
  | 1, 4 => w212
  | 1, 5 => w195
  | 2, 0 => w195
  | 2, 1 => w195
  | 2, 2 => w221
  | 2, 3 => w204
  | 2, 4 => w195
  | 2, 5 => w195
  | 3, 0 => w195
  | 3, 1 => w195
  | 3, 2 => w204
  | 3, 3 => w195
  | 3, 4 => w195
  | 3, 5 => w195
  | 4, 0 => w195
  | 4, 1 => w212
  | 4, 2 => w195
  | 4, 3 => w195
  | 4, 4 => w195
  | 4, 5 => w195
  | 5, 0 => w123
  | 5, 1 => w195
  | 5, 2 => w195
  | 5, 3 => w195
  | 5, 4 => w195
  | 5, 5 => w195
  | _, _ => (.exact 0)

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
def Z4_4_0Value (a : PairSlot) : ℝ := (zeroPairLaw (shape 4 4 0) a.1 a.2 : ℝ)
def Z4_4_0H1Value (a : PairSlot) : ℝ := (halfLaw (shape 4 4 0) 1 a : ℝ)
def Z4_4_0H1Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 5, 0 => ⟨(1312019371607181543741200578043 / 100000000000000000000000000000000), (18070111 / 4000000000000000000000000000000)⟩
  | 4, 1 => ⟨(26381660305887817562778739090541 / 100000000000000000000000000000000), (1089701667 / 10000000000000000000000000000000)⟩
  | 2, 2 => ⟨(480241208915683334342627678761 / 1562500000000000000000000000000), (1013455771 / 4000000000000000000000000000000)⟩
  | 2, 3 => ⟨(3604325882796094985265170692573 / 20000000000000000000000000000000), (1407752823 / 20000000000000000000000000000000)⟩
  | 3, 2 => ⟨(3604325882796094985265170692573 / 20000000000000000000000000000000), (1407752823 / 20000000000000000000000000000000)⟩
  | 3, 3 => ⟨(1783513370984199948259882031059 / 50000000000000000000000000000000), (172419939 / 12500000000000000000000000000000)⟩
  | 1, 4 => ⟨(26381660305887817562778739090541 / 100000000000000000000000000000000), (1089701667 / 10000000000000000000000000000000)⟩
  | 0, 5 => ⟨(1312019371607181543741200578043 / 100000000000000000000000000000000), (18070111 / 4000000000000000000000000000000)⟩
  | _, _ => (.exact 0)

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
def Z5_0_3Raw (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 0, 0 => w195
  | 0, 1 => w195
  | 0, 2 => w195
  | 0, 3 => w195
  | 0, 4 => w195
  | 0, 5 => w195
  | 1, 0 => w195
  | 1, 1 => w195
  | 1, 2 => w195
  | 1, 3 => w195
  | 1, 4 => w195
  | 1, 5 => w139
  | 2, 0 => w195
  | 2, 1 => w195
  | 2, 2 => w195
  | 2, 3 => w195
  | 2, 4 => w203
  | 2, 5 => w195
  | 3, 0 => w195
  | 3, 1 => w195
  | 3, 2 => w195
  | 3, 3 => w195
  | 3, 4 => w195
  | 3, 5 => w195
  | 4, 0 => w195
  | 4, 1 => w195
  | 4, 2 => w203
  | 4, 3 => w195
  | 4, 4 => w195
  | 4, 5 => w195
  | 5, 0 => w195
  | 5, 1 => w139
  | 5, 2 => w195
  | 5, 3 => w195
  | 5, 4 => w195
  | 5, 5 => w195
  | _, _ => (.exact 0)

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
def Z5_0_3Value (a : PairSlot) : ℝ := (zeroPairLaw (shape 5 0 3) a.1 a.2 : ℝ)
def Z5_0_3H2Value (a : PairSlot) : ℝ := (halfLaw (shape 5 0 3) 2 a : ℝ)
def Z5_0_3H2Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 4, 0 => ⟨(8420970324370679601710618565453 / 100000000000000000000000000000000), (327382217 / 10000000000000000000000000000000)⟩
  | 2, 1 => ⟨(36295678058602714916587164090917 / 100000000000000000000000000000000), (1706034339 / 6250000000000000000000000000000)⟩
  | 3, 1 => ⟨(7311426455825088170477182923379 / 50000000000000000000000000000000), (3064119637 / 50000000000000000000000000000000)⟩
  | 1, 2 => ⟨(36295678058602714916587164090917 / 100000000000000000000000000000000), (1706034339 / 6250000000000000000000000000000)⟩
  | 1, 3 => ⟨(7311426455825088170477182923379 / 50000000000000000000000000000000), (3064119637 / 50000000000000000000000000000000)⟩
  | 0, 4 => ⟨(8420970324370679601710618565453 / 100000000000000000000000000000000), (327382217 / 10000000000000000000000000000000)⟩
  | _, _ => (.exact 0)

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
def Z5_3_0Raw (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 0, 0 => w195
  | 0, 1 => w195
  | 0, 2 => w195
  | 0, 3 => w195
  | 0, 4 => w195
  | 0, 5 => w195
  | 1, 0 => w195
  | 1, 1 => w195
  | 1, 2 => w195
  | 1, 3 => w195
  | 1, 4 => w195
  | 1, 5 => w159
  | 2, 0 => w195
  | 2, 1 => w195
  | 2, 2 => w195
  | 2, 3 => w195
  | 2, 4 => w210
  | 2, 5 => w195
  | 3, 0 => w195
  | 3, 1 => w195
  | 3, 2 => w195
  | 3, 3 => w195
  | 3, 4 => w195
  | 3, 5 => w195
  | 4, 0 => w195
  | 4, 1 => w195
  | 4, 2 => w210
  | 4, 3 => w195
  | 4, 4 => w195
  | 4, 5 => w195
  | 5, 0 => w195
  | 5, 1 => w159
  | 5, 2 => w195
  | 5, 3 => w195
  | 5, 4 => w195
  | 5, 5 => w195
  | _, _ => (.exact 0)

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
def Z5_3_0Value (a : PairSlot) : ℝ := (zeroPairLaw (shape 5 3 0) a.1 a.2 : ℝ)
def Z5_3_0H1Value (a : PairSlot) : ℝ := (halfLaw (shape 5 3 0) 1 a : ℝ)
def Z5_3_0H1Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 4, 0 => ⟨(2108145010568870815331944029893 / 25000000000000000000000000000000), (1639971173 / 50000000000000000000000000000000)⟩
  | 2, 1 => ⟨(7233991706521058045956490938163 / 20000000000000000000000000000000), (13891550817 / 50000000000000000000000000000000)⟩
  | 3, 1 => ⟨(2598673100349966355117959463809 / 20000000000000000000000000000000), (514988899 / 10000000000000000000000000000000)⟩
  | 1, 2 => ⟨(7233991706521058045956490938163 / 20000000000000000000000000000000), (13891550817 / 50000000000000000000000000000000)⟩
  | 1, 3 => ⟨(2598673100349966355117959463809 / 20000000000000000000000000000000), (514988899 / 10000000000000000000000000000000)⟩
  | 0, 4 => ⟨(2108145010568870815331944029893 / 25000000000000000000000000000000), (1639971173 / 50000000000000000000000000000000)⟩
  | _, _ => (.exact 0)

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
def Z6_0_2Raw (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 0, 0 => w195
  | 0, 1 => w195
  | 0, 2 => w195
  | 0, 3 => w195
  | 0, 4 => w195
  | 0, 5 => w195
  | 1, 0 => w195
  | 1, 1 => w195
  | 1, 2 => w195
  | 1, 3 => w195
  | 1, 4 => w195
  | 1, 5 => w195
  | 2, 0 => w195
  | 2, 1 => w195
  | 2, 2 => w195
  | 2, 3 => w195
  | 2, 4 => w195
  | 2, 5 => w192
  | 3, 0 => w195
  | 3, 1 => w195
  | 3, 2 => w195
  | 3, 3 => w195
  | 3, 4 => w195
  | 3, 5 => w197
  | 4, 0 => w195
  | 4, 1 => w195
  | 4, 2 => w195
  | 4, 3 => w195
  | 4, 4 => w195
  | 4, 5 => w195
  | 5, 0 => w195
  | 5, 1 => w195
  | 5, 2 => w192
  | 5, 3 => w197
  | 5, 4 => w195
  | 5, 5 => w195
  | _, _ => (.exact 0)

def Z6_0_2Value (a : PairSlot) : ℝ := (zeroPairLaw (shape 6 0 2) a.1 a.2 : ℝ)

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
def Z6_2_0Raw (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 0, 0 => w195
  | 0, 1 => w195
  | 0, 2 => w195
  | 0, 3 => w195
  | 0, 4 => w195
  | 0, 5 => w195
  | 1, 0 => w195
  | 1, 1 => w195
  | 1, 2 => w195
  | 1, 3 => w195
  | 1, 4 => w195
  | 1, 5 => w195
  | 2, 0 => w195
  | 2, 1 => w195
  | 2, 2 => w195
  | 2, 3 => w195
  | 2, 4 => w195
  | 2, 5 => w194
  | 3, 0 => w195
  | 3, 1 => w195
  | 3, 2 => w195
  | 3, 3 => w195
  | 3, 4 => w195
  | 3, 5 => w196
  | 4, 0 => w195
  | 4, 1 => w195
  | 4, 2 => w195
  | 4, 3 => w195
  | 4, 4 => w195
  | 4, 5 => w195
  | 5, 0 => w195
  | 5, 1 => w195
  | 5, 2 => w194
  | 5, 3 => w196
  | 5, 4 => w195
  | 5, 5 => w195
  | _, _ => (.exact 0)

def Z6_2_0Value (a : PairSlot) : ℝ := (zeroPairLaw (shape 6 2 0) a.1 a.2 : ℝ)

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
def Z7_0_1Raw (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 0, 0 => w195
  | 0, 1 => w195
  | 0, 2 => w195
  | 0, 3 => w195
  | 0, 4 => w195
  | 0, 5 => w195
  | 1, 0 => w195
  | 1, 1 => w195
  | 1, 2 => w195
  | 1, 3 => w195
  | 1, 4 => w195
  | 1, 5 => w195
  | 2, 0 => w195
  | 2, 1 => w195
  | 2, 2 => w195
  | 2, 3 => w195
  | 2, 4 => w195
  | 2, 5 => w195
  | 3, 0 => w195
  | 3, 1 => w195
  | 3, 2 => w195
  | 3, 3 => w195
  | 3, 4 => w195
  | 3, 5 => w195
  | 4, 0 => w195
  | 4, 1 => w195
  | 4, 2 => w195
  | 4, 3 => w195
  | 4, 4 => w195
  | 4, 5 => w195
  | 5, 0 => w195
  | 5, 1 => w195
  | 5, 2 => w195
  | 5, 3 => w195
  | 5, 4 => w195
  | 5, 5 => w195
  | _, _ => (.exact 0)

def Z7_0_1Value (a : PairSlot) : ℝ := (zeroPairLaw (shape 7 0 1) a.1 a.2 : ℝ)

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
def Z7_1_0Raw (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 0, 0 => w195
  | 0, 1 => w195
  | 0, 2 => w195
  | 0, 3 => w195
  | 0, 4 => w195
  | 0, 5 => w195
  | 1, 0 => w195
  | 1, 1 => w195
  | 1, 2 => w195
  | 1, 3 => w195
  | 1, 4 => w195
  | 1, 5 => w195
  | 2, 0 => w195
  | 2, 1 => w195
  | 2, 2 => w195
  | 2, 3 => w195
  | 2, 4 => w195
  | 2, 5 => w195
  | 3, 0 => w195
  | 3, 1 => w195
  | 3, 2 => w195
  | 3, 3 => w195
  | 3, 4 => w195
  | 3, 5 => w195
  | 4, 0 => w195
  | 4, 1 => w195
  | 4, 2 => w195
  | 4, 3 => w195
  | 4, 4 => w195
  | 4, 5 => w195
  | 5, 0 => w195
  | 5, 1 => w195
  | 5, 2 => w195
  | 5, 3 => w195
  | 5, 4 => w195
  | 5, 5 => w195
  | _, _ => (.exact 0)

def Z7_1_0Value (a : PairSlot) : ℝ := (zeroPairLaw (shape 7 1 0) a.1 a.2 : ℝ)

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
def Z8_0_0Raw (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 0, 0 => w195
  | 0, 1 => w195
  | 0, 2 => w195
  | 0, 3 => w195
  | 0, 4 => w195
  | 0, 5 => w195
  | 1, 0 => w195
  | 1, 1 => w195
  | 1, 2 => w195
  | 1, 3 => w195
  | 1, 4 => w195
  | 1, 5 => w195
  | 2, 0 => w195
  | 2, 1 => w195
  | 2, 2 => w195
  | 2, 3 => w195
  | 2, 4 => w195
  | 2, 5 => w195
  | 3, 0 => w195
  | 3, 1 => w195
  | 3, 2 => w195
  | 3, 3 => w195
  | 3, 4 => w195
  | 3, 5 => w195
  | 4, 0 => w195
  | 4, 1 => w195
  | 4, 2 => w195
  | 4, 3 => w195
  | 4, 4 => w195
  | 4, 5 => w195
  | 5, 0 => w195
  | 5, 1 => w195
  | 5, 2 => w195
  | 5, 3 => w195
  | 5, 4 => w195
  | 5, 5 => w195
  | _, _ => (.exact 0)

def Z8_0_0Value (a : PairSlot) : ℝ := (zeroPairLaw (shape 8 0 0) a.1 a.2 : ℝ)

end MatrixMultiplication.NativeNumerics

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
def TParentBalls (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 1, 1, 6 => B1_1_6Ttotal
  | 1, 2, 5 => B1_2_5Ttotal
  | 1, 3, 4 => B1_3_4Ttotal
  | 1, 4, 3 => B1_4_3Ttotal
  | 1, 5, 2 => B1_5_2Ttotal
  | 1, 6, 1 => B1_6_1Ttotal
  | 2, 1, 5 => B2_1_5Ttotal
  | 2, 2, 4 => B2_2_4Ttotal
  | 2, 3, 3 => B2_3_3Ttotal
  | 2, 4, 2 => B2_4_2Ttotal
  | 2, 5, 1 => B2_5_1Ttotal
  | 3, 1, 4 => B3_1_4Ttotal
  | 3, 2, 3 => B3_2_3Ttotal
  | 3, 3, 2 => B3_3_2Ttotal
  | 3, 4, 1 => B3_4_1Ttotal
  | 4, 1, 3 => B4_1_3Ttotal
  | 4, 2, 2 => B4_2_2Ttotal
  | 4, 3, 1 => B4_3_1Ttotal
  | 5, 1, 2 => B5_1_2Ttotal
  | 5, 2, 1 => B5_2_1Ttotal
  | 6, 1, 1 => B6_1_1Ttotal
  | _, _, _ => (.exact 0)

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
def CB5_1_2I1PairValue (a : PairSlot) : ℝ := pairLaw (below (shape 5 1 2)) (shape 5 1 2) (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 1) a : ℝ)) a
def CB5_1_2I1PairCertificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(16505214817994806105572714739171 / 100000000000000000000000000000000), (33 / 100000000000000000000000000000000)⟩ ⟨(29734042252061927929320034727547 / 100000000000000000000000000000000), (6990230423 / 50000000000000000000000000000000)⟩ ⟨(-90074690271963004686404362733121 / 50000000000000000000000000000000), (84703294931 / 100000000000000000000000000000000)⟩ ⟨-3, 16505214817994806105572714739171, 12500000000000000000000000000000⟩,
   .log ⟨(49570105911377387117154514831 / 2500000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩ ⟨(7773897415469105343374013757949 / 100000000000000000000000000000000), (2939125929 / 100000000000000000000000000000000)⟩ ⟨(-7841316124447528729465058620191 / 2000000000000000000000000000000), (9264422877 / 6250000000000000000000000000000)⟩ ⟨-6, 49570105911377387117154514831, 39062500000000000000000000000⟩,
   .log ⟨(31511980945550098409741104667589 / 50000000000000000000000000000000), (17 / 50000000000000000000000000000000)⟩ ⟨(29095338750505488883321329985571 / 100000000000000000000000000000000), (13345843073 / 50000000000000000000000000000000)⟩ ⟨(-9233103688650880947564362099801 / 20000000000000000000000000000000), (42351647419 / 100000000000000000000000000000000)⟩ ⟨-1, 31511980945550098409741104667589, 25000000000000000000000000000000⟩]
def CB5_1_2I1PairCertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 2, 0 => 1
  | 3, 0 => 2
  | 1, 1 => 3
  | 0, 2 => 1
  | 0, 3 => 2
  | _, _ => 0
def CB5_1_2I1PairP (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I1PairCertificates (CB5_1_2I1PairCertificateIndex a)).input
def CB5_1_2I1PairTerms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I1PairCertificates (CB5_1_2I1PairCertificateIndex a)).output

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
def CB5_1_2I1R0Raw (a : Fin 6) : Ball := residualBall (below (shape 5 1 2)) B5_1_2Law (stageBPriority (shape 5 1 2)) 1 (fun u => B5_1_2Little u ((stageBPriority (shape 5 1 2)) 1)) 0 a
def CB5_1_2I1R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(18488019054449901590258895332411 / 100000000000000000000000000000000), (9 / 25000000000000000000000000000000)⟩ ⟨(31208650321412316625707562012269 / 100000000000000000000000000000000), (15659961367 / 100000000000000000000000000000000)⟩ ⟨(-168804728237775546533865029872577 / 100000000000000000000000000000000), (42351647463 / 50000000000000000000000000000000)⟩ ⟨-3, 18488019054449901590258895332411, 12500000000000000000000000000000⟩]
def CB5_1_2I1R0P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I1R0Certificates (CB5_1_2I1R0CertificateIndex a)).input
def CB5_1_2I1R0Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I1R0Certificates (CB5_1_2I1R0CertificateIndex a)).output
def CB5_1_2I1R1Raw (a : Fin 6) : Ball := residualBall (below (shape 5 1 2)) B5_1_2Law (stageBPriority (shape 5 1 2)) 1 (fun u => B5_1_2Little u ((stageBPriority (shape 5 1 2)) 1)) 1 a
def CB5_1_2I1R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(31511980945550098409741104667589 / 50000000000000000000000000000000), (17 / 50000000000000000000000000000000)⟩ ⟨(29095338750505488883321329985571 / 100000000000000000000000000000000), (13345843073 / 50000000000000000000000000000000)⟩ ⟨(-9233103688650880947564362099801 / 20000000000000000000000000000000), (42351647419 / 100000000000000000000000000000000)⟩ ⟨-1, 31511980945550098409741104667589, 25000000000000000000000000000000⟩]
def CB5_1_2I1R1P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I1R1Certificates (CB5_1_2I1R1CertificateIndex a)).input
def CB5_1_2I1R1Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I1R1Certificates (CB5_1_2I1R1CertificateIndex a)).output
def CB5_1_2I1R2Raw (a : Fin 6) : Ball := residualBall (below (shape 5 1 2)) B5_1_2Law (stageBPriority (shape 5 1 2)) 1 (fun u => B5_1_2Little u ((stageBPriority (shape 5 1 2)) 1)) 2 a
def CB5_1_2I1R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(16505214817994806105572714739171 / 100000000000000000000000000000000), (33 / 100000000000000000000000000000000)⟩ ⟨(29734042252061927929320034727547 / 100000000000000000000000000000000), (6990230423 / 50000000000000000000000000000000)⟩ ⟨(-90074690271963004686404362733121 / 50000000000000000000000000000000), (84703294931 / 100000000000000000000000000000000)⟩ ⟨-3, 16505214817994806105572714739171, 12500000000000000000000000000000⟩,
   .log ⟨(49570105911377387117154514831 / 2500000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩ ⟨(7773897415469105343374013757949 / 100000000000000000000000000000000), (2939125929 / 100000000000000000000000000000000)⟩ ⟨(-7841316124447528729465058620191 / 2000000000000000000000000000000), (9264422877 / 6250000000000000000000000000000)⟩ ⟨-6, 49570105911377387117154514831, 39062500000000000000000000000⟩]
def CB5_1_2I1R2P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I1R2Certificates (CB5_1_2I1R2CertificateIndex a)).input
def CB5_1_2I1R2Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I1R2Certificates (CB5_1_2I1R2CertificateIndex a)).output
def CB5_1_2I1R3Raw (a : Fin 6) : Ball := residualBall (below (shape 5 1 2)) B5_1_2Law (stageBPriority (shape 5 1 2)) 1 (fun u => B5_1_2Little u ((stageBPriority (shape 5 1 2)) 1)) 3 a
def CB5_1_2I1R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_1_2I1R3P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I1R3Certificates (CB5_1_2I1R3CertificateIndex a)).input
def CB5_1_2I1R3Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I1R3Certificates (CB5_1_2I1R3CertificateIndex a)).output
def CB5_1_2I1R4Raw (a : Fin 6) : Ball := residualBall (below (shape 5 1 2)) B5_1_2Law (stageBPriority (shape 5 1 2)) 1 (fun u => B5_1_2Little u ((stageBPriority (shape 5 1 2)) 1)) 4 a
def CB5_1_2I1R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_1_2I1R4P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I1R4Certificates (CB5_1_2I1R4CertificateIndex a)).input
def CB5_1_2I1R4Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I1R4Certificates (CB5_1_2I1R4CertificateIndex a)).output
def CB5_1_2I1R5Raw (a : Fin 6) : Ball := residualBall (below (shape 5 1 2)) B5_1_2Law (stageBPriority (shape 5 1 2)) 1 (fun u => B5_1_2Little u ((stageBPriority (shape 5 1 2)) 1)) 5 a
def CB5_1_2I1R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_1_2I1R5P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I1R5Certificates (CB5_1_2I1R5CertificateIndex a)).input
def CB5_1_2I1R5Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I1R5Certificates (CB5_1_2I1R5CertificateIndex a)).output
def CB5_1_2I1R6Raw (a : Fin 6) : Ball := residualBall (below (shape 5 1 2)) B5_1_2Law (stageBPriority (shape 5 1 2)) 1 (fun u => B5_1_2Little u ((stageBPriority (shape 5 1 2)) 1)) 6 a
def CB5_1_2I1R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_1_2I1R6P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I1R6Certificates (CB5_1_2I1R6CertificateIndex a)).input
def CB5_1_2I1R6Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I1R6Certificates (CB5_1_2I1R6CertificateIndex a)).output
def CB5_1_2I1R7Raw (a : Fin 6) : Ball := residualBall (below (shape 5 1 2)) B5_1_2Law (stageBPriority (shape 5 1 2)) 1 (fun u => B5_1_2Little u ((stageBPriority (shape 5 1 2)) 1)) 7 a
def CB5_1_2I1R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_1_2I1R7P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I1R7Certificates (CB5_1_2I1R7CertificateIndex a)).input
def CB5_1_2I1R7Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I1R7Certificates (CB5_1_2I1R7CertificateIndex a)).output
def CB5_1_2I1R8Raw (a : Fin 6) : Ball := residualBall (below (shape 5 1 2)) B5_1_2Law (stageBPriority (shape 5 1 2)) 1 (fun u => B5_1_2Little u ((stageBPriority (shape 5 1 2)) 1)) 8 a
def CB5_1_2I1R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_1_2I1R8P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I1R8Certificates (CB5_1_2I1R8CertificateIndex a)).input
def CB5_1_2I1R8Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I1R8Certificates (CB5_1_2I1R8CertificateIndex a)).output
def CB5_1_2I1R9Raw (a : Fin 6) : Ball := residualBall (below (shape 5 1 2)) B5_1_2Law (stageBPriority (shape 5 1 2)) 1 (fun u => B5_1_2Little u ((stageBPriority (shape 5 1 2)) 1)) 9 a
def CB5_1_2I1R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_1_2I1R9P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I1R9Certificates (CB5_1_2I1R9CertificateIndex a)).input
def CB5_1_2I1R9Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I1R9Certificates (CB5_1_2I1R9CertificateIndex a)).output
def CB5_1_2I1R10Raw (a : Fin 6) : Ball := residualBall (below (shape 5 1 2)) B5_1_2Law (stageBPriority (shape 5 1 2)) 1 (fun u => B5_1_2Little u ((stageBPriority (shape 5 1 2)) 1)) 10 a
def CB5_1_2I1R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_1_2I1R10P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I1R10Certificates (CB5_1_2I1R10CertificateIndex a)).input
def CB5_1_2I1R10Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I1R10Certificates (CB5_1_2I1R10CertificateIndex a)).output
def CB5_1_2I1R11Raw (a : Fin 6) : Ball := residualBall (below (shape 5 1 2)) B5_1_2Law (stageBPriority (shape 5 1 2)) 1 (fun u => B5_1_2Little u ((stageBPriority (shape 5 1 2)) 1)) 11 a
def CB5_1_2I1R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_1_2I1R11P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I1R11Certificates (CB5_1_2I1R11CertificateIndex a)).input
def CB5_1_2I1R11Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I1R11Certificates (CB5_1_2I1R11CertificateIndex a)).output
def CB5_1_2I1R12Raw (a : Fin 6) : Ball := residualBall (below (shape 5 1 2)) B5_1_2Law (stageBPriority (shape 5 1 2)) 1 (fun u => B5_1_2Little u ((stageBPriority (shape 5 1 2)) 1)) 12 a
def CB5_1_2I1R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_1_2I1R12P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I1R12Certificates (CB5_1_2I1R12CertificateIndex a)).input
def CB5_1_2I1R12Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I1R12Certificates (CB5_1_2I1R12CertificateIndex a)).output
def CB5_1_2I1R13Raw (a : Fin 6) : Ball := residualBall (below (shape 5 1 2)) B5_1_2Law (stageBPriority (shape 5 1 2)) 1 (fun u => B5_1_2Little u ((stageBPriority (shape 5 1 2)) 1)) 13 a
def CB5_1_2I1R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_1_2I1R13P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I1R13Certificates (CB5_1_2I1R13CertificateIndex a)).input
def CB5_1_2I1R13Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I1R13Certificates (CB5_1_2I1R13CertificateIndex a)).output
def CB5_1_2I1R14Raw (a : Fin 6) : Ball := residualBall (below (shape 5 1 2)) B5_1_2Law (stageBPriority (shape 5 1 2)) 1 (fun u => B5_1_2Little u ((stageBPriority (shape 5 1 2)) 1)) 14 a
def CB5_1_2I1R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_1_2I1R14P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I1R14Certificates (CB5_1_2I1R14CertificateIndex a)).input
def CB5_1_2I1R14Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I1R14Certificates (CB5_1_2I1R14CertificateIndex a)).output
def CB5_1_2I1R15Raw (a : Fin 6) : Ball := residualBall (below (shape 5 1 2)) B5_1_2Law (stageBPriority (shape 5 1 2)) 1 (fun u => B5_1_2Little u ((stageBPriority (shape 5 1 2)) 1)) 15 a
def CB5_1_2I1R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_1_2I1R15P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I1R15Certificates (CB5_1_2I1R15CertificateIndex a)).input
def CB5_1_2I1R15Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I1R15Certificates (CB5_1_2I1R15CertificateIndex a)).output
def CB5_1_2I1R16Raw (a : Fin 6) : Ball := residualBall (below (shape 5 1 2)) B5_1_2Law (stageBPriority (shape 5 1 2)) 1 (fun u => B5_1_2Little u ((stageBPriority (shape 5 1 2)) 1)) 16 a
def CB5_1_2I1R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_1_2I1R16P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I1R16Certificates (CB5_1_2I1R16CertificateIndex a)).input
def CB5_1_2I1R16Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I1R16Certificates (CB5_1_2I1R16CertificateIndex a)).output

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
def CB5_1_2I2PairValue (a : PairSlot) : ℝ := pairLaw (below (shape 5 1 2)) (shape 5 1 2) (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 2) a : ℝ)) a
def CB5_1_2I2PairCertificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(715243539925161855344559597823 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(3533519351837877097933777673677 / 100000000000000000000000000000000), (1363128417 / 100000000000000000000000000000000)⟩ ⟨(-247015118249624467839772444506523 / 50000000000000000000000000000000), (95291206783 / 50000000000000000000000000000000)⟩ ⟨-8, 715243539925161855344559597823, 390625000000000000000000000000⟩,
   .log ⟨(47206419312694013248239704463141 / 100000000000000000000000000000000), (47 / 100000000000000000000000000000000)⟩ ⟨(17717520383457034023941812023077 / 50000000000000000000000000000000), (5997808889 / 20000000000000000000000000000000)⟩ ⟨(-37532015012824145859083618599493 / 50000000000000000000000000000000), (63527471149 / 100000000000000000000000000000000)⟩ ⟨-2, 47206419312694013248239704463141, 25000000000000000000000000000000⟩,
   .log ⟨(519584286845206224103933984759 / 25000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩ ⟨(8050651056256028142810153266311 / 100000000000000000000000000000000), (1540367547 / 50000000000000000000000000000000)⟩ ⟨(-96840051509468401463964207778457 / 25000000000000000000000000000000), (148230766021 / 100000000000000000000000000000000)⟩ ⟨-6, 519584286845206224103933984759, 390625000000000000000000000000⟩]
def CB5_1_2I2PairCertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 5 => 1
  | 2, 4 => 2
  | 3, 4 => 3
  | 4, 2 => 2
  | 4, 3 => 3
  | 5, 1 => 1
  | _, _ => 0
def CB5_1_2I2PairP (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I2PairCertificates (CB5_1_2I2PairCertificateIndex a)).input
def CB5_1_2I2PairTerms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I2PairCertificates (CB5_1_2I2PairCertificateIndex a)).output

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
def CB5_1_2I2R0Raw (a : Fin 6) : Ball := residualBall (below (shape 5 1 2)) B5_1_2Law (stageBPriority (shape 5 1 2)) 2 (fun u => B5_1_2Little u ((stageBPriority (shape 5 1 2)) 2)) 0 a
def CB5_1_2I2R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_1_2I2R0P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I2R0Certificates (CB5_1_2I2R0CertificateIndex a)).input
def CB5_1_2I2R0Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I2R0Certificates (CB5_1_2I2R0CertificateIndex a)).output
def CB5_1_2I2R1Raw (a : Fin 6) : Ball := residualBall (below (shape 5 1 2)) B5_1_2Law (stageBPriority (shape 5 1 2)) 2 (fun u => B5_1_2Little u ((stageBPriority (shape 5 1 2)) 2)) 1 a
def CB5_1_2I2R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(715243539925161855344559597823 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(3533519351837877097933777673677 / 100000000000000000000000000000000), (1363128417 / 100000000000000000000000000000000)⟩ ⟨(-247015118249624467839772444506523 / 50000000000000000000000000000000), (95291206783 / 50000000000000000000000000000000)⟩ ⟨-8, 715243539925161855344559597823, 390625000000000000000000000000⟩]
def CB5_1_2I2R1P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I2R1Certificates (CB5_1_2I2R1CertificateIndex a)).input
def CB5_1_2I2R1Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I2R1Certificates (CB5_1_2I2R1CertificateIndex a)).output
def CB5_1_2I2R2Raw (a : Fin 6) : Ball := residualBall (below (shape 5 1 2)) B5_1_2Law (stageBPriority (shape 5 1 2)) 2 (fun u => B5_1_2Little u ((stageBPriority (shape 5 1 2)) 2)) 2 a
def CB5_1_2I2R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(957836126388584464034420063 / 3051757812500000000000000000), (17 / 100000000000000000000000000000000)⟩ ⟨(2273150951942751179081618308153 / 6250000000000000000000000000000), (9969484907 / 50000000000000000000000000000000)⟩ ⟨(-28969908256597909506085221295941 / 25000000000000000000000000000000), (63527471103 / 100000000000000000000000000000000)⟩ ⟨-2, 957836126388584464034420063, 762939453125000000000000000⟩,
   .log ⟨(25121351209792538452245608641 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(839024168275589113007705883313 / 100000000000000000000000000000000), (146290463 / 50000000000000000000000000000000)⟩ ⟨(-166994235554600585818279647600737 / 25000000000000000000000000000000), (232934061309 / 100000000000000000000000000000000)⟩ ⟨-10, 25121351209792538452245608641, 19531250000000000000000000000⟩]
def CB5_1_2I2R2P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I2R2Certificates (CB5_1_2I2R2CertificateIndex a)).input
def CB5_1_2I2R2Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I2R2Certificates (CB5_1_2I2R2CertificateIndex a)).output
def CB5_1_2I2R3Raw (a : Fin 6) : Ball := residualBall (below (shape 5 1 2)) B5_1_2Law (stageBPriority (shape 5 1 2)) 2 (fun u => B5_1_2Little u ((stageBPriority (shape 5 1 2)) 2)) 3 a
def CB5_1_2I2R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_1_2I2R3P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I2R3Certificates (CB5_1_2I2R3CertificateIndex a)).input
def CB5_1_2I2R3Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I2R3Certificates (CB5_1_2I2R3CertificateIndex a)).output
def CB5_1_2I2R4Raw (a : Fin 6) : Ball := residualBall (below (shape 5 1 2)) B5_1_2Law (stageBPriority (shape 5 1 2)) 2 (fun u => B5_1_2Little u ((stageBPriority (shape 5 1 2)) 2)) 4 a
def CB5_1_2I2R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_1_2I2R4P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I2R4Certificates (CB5_1_2I2R4CertificateIndex a)).input
def CB5_1_2I2R4Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I2R4Certificates (CB5_1_2I2R4CertificateIndex a)).output
def CB5_1_2I2R5Raw (a : Fin 6) : Ball := residualBall (below (shape 5 1 2)) B5_1_2Law (stageBPriority (shape 5 1 2)) 2 (fun u => B5_1_2Little u ((stageBPriority (shape 5 1 2)) 2)) 5 a
def CB5_1_2I2R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_1_2I2R5P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I2R5Certificates (CB5_1_2I2R5CertificateIndex a)).input
def CB5_1_2I2R5Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I2R5Certificates (CB5_1_2I2R5CertificateIndex a)).output
def CB5_1_2I2R6Raw (a : Fin 6) : Ball := residualBall (below (shape 5 1 2)) B5_1_2Law (stageBPriority (shape 5 1 2)) 2 (fun u => B5_1_2Little u ((stageBPriority (shape 5 1 2)) 2)) 6 a
def CB5_1_2I2R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_1_2I2R6P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I2R6Certificates (CB5_1_2I2R6CertificateIndex a)).input
def CB5_1_2I2R6Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I2R6Certificates (CB5_1_2I2R6CertificateIndex a)).output
def CB5_1_2I2R7Raw (a : Fin 6) : Ball := residualBall (below (shape 5 1 2)) B5_1_2Law (stageBPriority (shape 5 1 2)) 2 (fun u => B5_1_2Little u ((stageBPriority (shape 5 1 2)) 2)) 7 a
def CB5_1_2I2R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_1_2I2R7P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I2R7Certificates (CB5_1_2I2R7CertificateIndex a)).input
def CB5_1_2I2R7Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I2R7Certificates (CB5_1_2I2R7CertificateIndex a)).output
def CB5_1_2I2R8Raw (a : Fin 6) : Ball := residualBall (below (shape 5 1 2)) B5_1_2Law (stageBPriority (shape 5 1 2)) 2 (fun u => B5_1_2Little u ((stageBPriority (shape 5 1 2)) 2)) 8 a
def CB5_1_2I2R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_1_2I2R8P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I2R8Certificates (CB5_1_2I2R8CertificateIndex a)).input
def CB5_1_2I2R8Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I2R8Certificates (CB5_1_2I2R8CertificateIndex a)).output
def CB5_1_2I2R9Raw (a : Fin 6) : Ball := residualBall (below (shape 5 1 2)) B5_1_2Law (stageBPriority (shape 5 1 2)) 2 (fun u => B5_1_2Little u ((stageBPriority (shape 5 1 2)) 2)) 9 a
def CB5_1_2I2R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_1_2I2R9P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I2R9Certificates (CB5_1_2I2R9CertificateIndex a)).input
def CB5_1_2I2R9Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I2R9Certificates (CB5_1_2I2R9CertificateIndex a)).output
def CB5_1_2I2R10Raw (a : Fin 6) : Ball := residualBall (below (shape 5 1 2)) B5_1_2Law (stageBPriority (shape 5 1 2)) 2 (fun u => B5_1_2Little u ((stageBPriority (shape 5 1 2)) 2)) 10 a
def CB5_1_2I2R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_1_2I2R10P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I2R10Certificates (CB5_1_2I2R10CertificateIndex a)).input
def CB5_1_2I2R10Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I2R10Certificates (CB5_1_2I2R10CertificateIndex a)).output
def CB5_1_2I2R11Raw (a : Fin 6) : Ball := residualBall (below (shape 5 1 2)) B5_1_2Law (stageBPriority (shape 5 1 2)) 2 (fun u => B5_1_2Little u ((stageBPriority (shape 5 1 2)) 2)) 11 a
def CB5_1_2I2R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_1_2I2R11P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I2R11Certificates (CB5_1_2I2R11CertificateIndex a)).input
def CB5_1_2I2R11Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I2R11Certificates (CB5_1_2I2R11CertificateIndex a)).output
def CB5_1_2I2R12Raw (a : Fin 6) : Ball := residualBall (below (shape 5 1 2)) B5_1_2Law (stageBPriority (shape 5 1 2)) 2 (fun u => B5_1_2Little u ((stageBPriority (shape 5 1 2)) 2)) 12 a
def CB5_1_2I2R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_1_2I2R12P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I2R12Certificates (CB5_1_2I2R12CertificateIndex a)).input
def CB5_1_2I2R12Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I2R12Certificates (CB5_1_2I2R12CertificateIndex a)).output
def CB5_1_2I2R13Raw (a : Fin 6) : Ball := residualBall (below (shape 5 1 2)) B5_1_2Law (stageBPriority (shape 5 1 2)) 2 (fun u => B5_1_2Little u ((stageBPriority (shape 5 1 2)) 2)) 13 a
def CB5_1_2I2R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_1_2I2R13P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I2R13Certificates (CB5_1_2I2R13CertificateIndex a)).input
def CB5_1_2I2R13Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I2R13Certificates (CB5_1_2I2R13CertificateIndex a)).output
def CB5_1_2I2R14Raw (a : Fin 6) : Ball := residualBall (below (shape 5 1 2)) B5_1_2Law (stageBPriority (shape 5 1 2)) 2 (fun u => B5_1_2Little u ((stageBPriority (shape 5 1 2)) 2)) 14 a
def CB5_1_2I2R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_1_2I2R14P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I2R14Certificates (CB5_1_2I2R14CertificateIndex a)).input
def CB5_1_2I2R14Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I2R14Certificates (CB5_1_2I2R14CertificateIndex a)).output
def CB5_1_2I2R15Raw (a : Fin 6) : Ball := residualBall (below (shape 5 1 2)) B5_1_2Law (stageBPriority (shape 5 1 2)) 2 (fun u => B5_1_2Little u ((stageBPriority (shape 5 1 2)) 2)) 15 a
def CB5_1_2I2R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_1_2I2R15P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I2R15Certificates (CB5_1_2I2R15CertificateIndex a)).input
def CB5_1_2I2R15Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I2R15Certificates (CB5_1_2I2R15CertificateIndex a)).output
def CB5_1_2I2R16Raw (a : Fin 6) : Ball := residualBall (below (shape 5 1 2)) B5_1_2Law (stageBPriority (shape 5 1 2)) 2 (fun u => B5_1_2Little u ((stageBPriority (shape 5 1 2)) 2)) 16 a
def CB5_1_2I2R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_1_2I2R16P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I2R16Certificates (CB5_1_2I2R16CertificateIndex a)).input
def CB5_1_2I2R16Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I2R16Certificates (CB5_1_2I2R16CertificateIndex a)).output

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
def CB5_2_1I0Raw (a : Fin 17) : Ball := marginalBall (below (shape 5 2 1)) B5_2_1Law ((stageBPriority (shape 5 2 1)) 0) a
def CB5_2_1I0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1 / 2), (53 / 100000000000000000000000000000000)⟩ ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823773 / 100000000000000000000000000000000)⟩ ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (42351647471 / 100000000000000000000000000000000)⟩ ⟨-1, 1, 1⟩]
def CB5_2_1I0P (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I0Certificates (CB5_2_1I0CertificateIndex a)).input
def CB5_2_1I0Terms (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I0Certificates (CB5_2_1I0CertificateIndex a)).output

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
def CB5_2_1I1PairValue (a : PairSlot) : ℝ := pairLaw (below (shape 5 2 1)) (shape 5 2 1) (fun u => (stageBLaw (shape 5 2 1) u : ℝ)) (fun u a => (littleLaw (shape 5 2 1) u ((stageBPriority (shape 5 2 1)) 1) a : ℝ)) a
def CB5_2_1I1PairCertificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(8251288847660790062385380988161 / 50000000000000000000000000000000), (33 / 100000000000000000000000000000000)⟩ ⟨(29731928403890637480496172123267 / 100000000000000000000000000000000), (13978227117 / 100000000000000000000000000000000)⟩ ⟨(-90082679666218234075586429991739 / 50000000000000000000000000000000), (84703294931 / 100000000000000000000000000000000)⟩ ⟨-3, 8251288847660790062385380988161, 6250000000000000000000000000000⟩,
   .log ⟨(496830304206321792542832136267 / 25000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(62296678635940329152577077383 / 800000000000000000000000000000), (2945821479 / 100000000000000000000000000000000)⟩ ⟨(-391838257628642468839827015994241 / 100000000000000000000000000000000), (74115382991 / 50000000000000000000000000000000)⟩ ⟨-6, 496830304206321792542832136267, 390625000000000000000000000000⟩,
   .log ⟨(3151010108785313270505790947861 / 5000000000000000000000000000000), (17 / 50000000000000000000000000000000)⟩ ⟨(363717033270625690470714504197 / 1250000000000000000000000000000), (5338018769 / 20000000000000000000000000000000)⟩ ⟨(-1442858879826140153114781181427 / 3125000000000000000000000000000), (42351647419 / 100000000000000000000000000000000)⟩ ⟨-1, 3151010108785313270505790947861, 2500000000000000000000000000000⟩]
def CB5_2_1I1PairCertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 2, 0 => 1
  | 3, 0 => 2
  | 1, 1 => 3
  | 0, 2 => 1
  | 0, 3 => 2
  | _, _ => 0
def CB5_2_1I1PairP (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I1PairCertificates (CB5_2_1I1PairCertificateIndex a)).input
def CB5_2_1I1PairTerms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I1PairCertificates (CB5_2_1I1PairCertificateIndex a)).output

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
def CB5_2_1I1R0Raw (a : Fin 6) : Ball := residualBall (below (shape 5 2 1)) B5_2_1Law (stageBPriority (shape 5 2 1)) 1 (fun u => B5_2_1Little u ((stageBPriority (shape 5 2 1)) 1)) 0 a
def CB5_2_1I1R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1848989891214686729494209052139 / 10000000000000000000000000000000), (9 / 25000000000000000000000000000000)⟩ ⟨(15604971828411725998343746085051 / 50000000000000000000000000000000), (15661553669 / 100000000000000000000000000000000)⟩ ⟨(-4219864019418759598795757864871 / 2500000000000000000000000000000), (42351647463 / 50000000000000000000000000000000)⟩ ⟨-3, 1848989891214686729494209052139, 1250000000000000000000000000000⟩]
def CB5_2_1I1R0P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I1R0Certificates (CB5_2_1I1R0CertificateIndex a)).input
def CB5_2_1I1R0Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I1R0Certificates (CB5_2_1I1R0CertificateIndex a)).output
def CB5_2_1I1R1Raw (a : Fin 6) : Ball := residualBall (below (shape 5 2 1)) B5_2_1Law (stageBPriority (shape 5 2 1)) 1 (fun u => B5_2_1Little u ((stageBPriority (shape 5 2 1)) 1)) 1 a
def CB5_2_1I1R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(3151010108785313270505790947861 / 5000000000000000000000000000000), (17 / 50000000000000000000000000000000)⟩ ⟨(363717033270625690470714504197 / 1250000000000000000000000000000), (5338018769 / 20000000000000000000000000000000)⟩ ⟨(-1442858879826140153114781181427 / 3125000000000000000000000000000), (42351647419 / 100000000000000000000000000000000)⟩ ⟨-1, 3151010108785313270505790947861, 2500000000000000000000000000000⟩]
def CB5_2_1I1R1P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I1R1Certificates (CB5_2_1I1R1CertificateIndex a)).input
def CB5_2_1I1R1Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I1R1Certificates (CB5_2_1I1R1CertificateIndex a)).output
def CB5_2_1I1R2Raw (a : Fin 6) : Ball := residualBall (below (shape 5 2 1)) B5_2_1Law (stageBPriority (shape 5 2 1)) 1 (fun u => B5_2_1Little u ((stageBPriority (shape 5 2 1)) 1)) 2 a
def CB5_2_1I1R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(8251288847660790062385380988161 / 50000000000000000000000000000000), (33 / 100000000000000000000000000000000)⟩ ⟨(29731928403890637480496172123267 / 100000000000000000000000000000000), (13978227117 / 100000000000000000000000000000000)⟩ ⟨(-90082679666218234075586429991739 / 50000000000000000000000000000000), (84703294931 / 100000000000000000000000000000000)⟩ ⟨-3, 8251288847660790062385380988161, 6250000000000000000000000000000⟩,
   .log ⟨(496830304206321792542832136267 / 25000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(62296678635940329152577077383 / 800000000000000000000000000000), (2945821479 / 100000000000000000000000000000000)⟩ ⟨(-391838257628642468839827015994241 / 100000000000000000000000000000000), (74115382991 / 50000000000000000000000000000000)⟩ ⟨-6, 496830304206321792542832136267, 390625000000000000000000000000⟩]
def CB5_2_1I1R2P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I1R2Certificates (CB5_2_1I1R2CertificateIndex a)).input
def CB5_2_1I1R2Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I1R2Certificates (CB5_2_1I1R2CertificateIndex a)).output
def CB5_2_1I1R3Raw (a : Fin 6) : Ball := residualBall (below (shape 5 2 1)) B5_2_1Law (stageBPriority (shape 5 2 1)) 1 (fun u => B5_2_1Little u ((stageBPriority (shape 5 2 1)) 1)) 3 a
def CB5_2_1I1R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_2_1I1R3P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I1R3Certificates (CB5_2_1I1R3CertificateIndex a)).input
def CB5_2_1I1R3Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I1R3Certificates (CB5_2_1I1R3CertificateIndex a)).output
def CB5_2_1I1R4Raw (a : Fin 6) : Ball := residualBall (below (shape 5 2 1)) B5_2_1Law (stageBPriority (shape 5 2 1)) 1 (fun u => B5_2_1Little u ((stageBPriority (shape 5 2 1)) 1)) 4 a
def CB5_2_1I1R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_2_1I1R4P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I1R4Certificates (CB5_2_1I1R4CertificateIndex a)).input
def CB5_2_1I1R4Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I1R4Certificates (CB5_2_1I1R4CertificateIndex a)).output
def CB5_2_1I1R5Raw (a : Fin 6) : Ball := residualBall (below (shape 5 2 1)) B5_2_1Law (stageBPriority (shape 5 2 1)) 1 (fun u => B5_2_1Little u ((stageBPriority (shape 5 2 1)) 1)) 5 a
def CB5_2_1I1R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_2_1I1R5P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I1R5Certificates (CB5_2_1I1R5CertificateIndex a)).input
def CB5_2_1I1R5Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I1R5Certificates (CB5_2_1I1R5CertificateIndex a)).output
def CB5_2_1I1R6Raw (a : Fin 6) : Ball := residualBall (below (shape 5 2 1)) B5_2_1Law (stageBPriority (shape 5 2 1)) 1 (fun u => B5_2_1Little u ((stageBPriority (shape 5 2 1)) 1)) 6 a
def CB5_2_1I1R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_2_1I1R6P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I1R6Certificates (CB5_2_1I1R6CertificateIndex a)).input
def CB5_2_1I1R6Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I1R6Certificates (CB5_2_1I1R6CertificateIndex a)).output
def CB5_2_1I1R7Raw (a : Fin 6) : Ball := residualBall (below (shape 5 2 1)) B5_2_1Law (stageBPriority (shape 5 2 1)) 1 (fun u => B5_2_1Little u ((stageBPriority (shape 5 2 1)) 1)) 7 a
def CB5_2_1I1R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_2_1I1R7P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I1R7Certificates (CB5_2_1I1R7CertificateIndex a)).input
def CB5_2_1I1R7Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I1R7Certificates (CB5_2_1I1R7CertificateIndex a)).output
def CB5_2_1I1R8Raw (a : Fin 6) : Ball := residualBall (below (shape 5 2 1)) B5_2_1Law (stageBPriority (shape 5 2 1)) 1 (fun u => B5_2_1Little u ((stageBPriority (shape 5 2 1)) 1)) 8 a
def CB5_2_1I1R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_2_1I1R8P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I1R8Certificates (CB5_2_1I1R8CertificateIndex a)).input
def CB5_2_1I1R8Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I1R8Certificates (CB5_2_1I1R8CertificateIndex a)).output
def CB5_2_1I1R9Raw (a : Fin 6) : Ball := residualBall (below (shape 5 2 1)) B5_2_1Law (stageBPriority (shape 5 2 1)) 1 (fun u => B5_2_1Little u ((stageBPriority (shape 5 2 1)) 1)) 9 a
def CB5_2_1I1R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_2_1I1R9P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I1R9Certificates (CB5_2_1I1R9CertificateIndex a)).input
def CB5_2_1I1R9Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I1R9Certificates (CB5_2_1I1R9CertificateIndex a)).output
def CB5_2_1I1R10Raw (a : Fin 6) : Ball := residualBall (below (shape 5 2 1)) B5_2_1Law (stageBPriority (shape 5 2 1)) 1 (fun u => B5_2_1Little u ((stageBPriority (shape 5 2 1)) 1)) 10 a
def CB5_2_1I1R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_2_1I1R10P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I1R10Certificates (CB5_2_1I1R10CertificateIndex a)).input
def CB5_2_1I1R10Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I1R10Certificates (CB5_2_1I1R10CertificateIndex a)).output
def CB5_2_1I1R11Raw (a : Fin 6) : Ball := residualBall (below (shape 5 2 1)) B5_2_1Law (stageBPriority (shape 5 2 1)) 1 (fun u => B5_2_1Little u ((stageBPriority (shape 5 2 1)) 1)) 11 a
def CB5_2_1I1R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_2_1I1R11P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I1R11Certificates (CB5_2_1I1R11CertificateIndex a)).input
def CB5_2_1I1R11Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I1R11Certificates (CB5_2_1I1R11CertificateIndex a)).output
def CB5_2_1I1R12Raw (a : Fin 6) : Ball := residualBall (below (shape 5 2 1)) B5_2_1Law (stageBPriority (shape 5 2 1)) 1 (fun u => B5_2_1Little u ((stageBPriority (shape 5 2 1)) 1)) 12 a
def CB5_2_1I1R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_2_1I1R12P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I1R12Certificates (CB5_2_1I1R12CertificateIndex a)).input
def CB5_2_1I1R12Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I1R12Certificates (CB5_2_1I1R12CertificateIndex a)).output
def CB5_2_1I1R13Raw (a : Fin 6) : Ball := residualBall (below (shape 5 2 1)) B5_2_1Law (stageBPriority (shape 5 2 1)) 1 (fun u => B5_2_1Little u ((stageBPriority (shape 5 2 1)) 1)) 13 a
def CB5_2_1I1R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_2_1I1R13P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I1R13Certificates (CB5_2_1I1R13CertificateIndex a)).input
def CB5_2_1I1R13Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I1R13Certificates (CB5_2_1I1R13CertificateIndex a)).output
def CB5_2_1I1R14Raw (a : Fin 6) : Ball := residualBall (below (shape 5 2 1)) B5_2_1Law (stageBPriority (shape 5 2 1)) 1 (fun u => B5_2_1Little u ((stageBPriority (shape 5 2 1)) 1)) 14 a
def CB5_2_1I1R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_2_1I1R14P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I1R14Certificates (CB5_2_1I1R14CertificateIndex a)).input
def CB5_2_1I1R14Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I1R14Certificates (CB5_2_1I1R14CertificateIndex a)).output
def CB5_2_1I1R15Raw (a : Fin 6) : Ball := residualBall (below (shape 5 2 1)) B5_2_1Law (stageBPriority (shape 5 2 1)) 1 (fun u => B5_2_1Little u ((stageBPriority (shape 5 2 1)) 1)) 15 a
def CB5_2_1I1R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_2_1I1R15P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I1R15Certificates (CB5_2_1I1R15CertificateIndex a)).input
def CB5_2_1I1R15Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I1R15Certificates (CB5_2_1I1R15CertificateIndex a)).output
def CB5_2_1I1R16Raw (a : Fin 6) : Ball := residualBall (below (shape 5 2 1)) B5_2_1Law (stageBPriority (shape 5 2 1)) 1 (fun u => B5_2_1Little u ((stageBPriority (shape 5 2 1)) 1)) 16 a
def CB5_2_1I1R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_2_1I1R16P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I1R16Certificates (CB5_2_1I1R16CertificateIndex a)).input
def CB5_2_1I1R16Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I1R16Certificates (CB5_2_1I1R16CertificateIndex a)).output

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
def CB5_2_1I2PairValue (a : PairSlot) : ℝ := pairLaw (below (shape 5 2 1)) (shape 5 2 1) (fun u => (stageBLaw (shape 5 2 1) u : ℝ)) (fun u a => (littleLaw (shape 5 2 1) u ((stageBPriority (shape 5 2 1)) 2) a : ℝ)) a
def CB5_2_1I2PairCertificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(357314469969927548416673592027 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(1765548688963737013294197353 / 50000000000000000000000000000), (1361957097 / 100000000000000000000000000000000)⟩ ⟨(-386028282976899231126090684623 / 78125000000000000000000000000), (190582413567 / 100000000000000000000000000000000)⟩ ⟨-8, 357314469969927548416673592027, 195312500000000000000000000000⟩,
   .log ⟨(2950462341058093169205656218569 / 6250000000000000000000000000000), (47 / 100000000000000000000000000000000)⟩ ⟨(35434796847027417166598529257081 / 100000000000000000000000000000000), (5997933167 / 20000000000000000000000000000000)⟩ ⟨(-37530978994718978903390200891973 / 50000000000000000000000000000000), (15881867787 / 25000000000000000000000000000000)⟩ ⟨-2, 2950462341058093169205656218569, 1562500000000000000000000000000⟩,
   .log ⟨(1038986801565327097938076659421 / 50000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(8049606342952131962626332520331 / 100000000000000000000000000000000), (616039241 / 20000000000000000000000000000000)⟩ ⟨(-387377699640874925212272146653461 / 100000000000000000000000000000000), (148230765973 / 100000000000000000000000000000000)⟩ ⟨-6, 1038986801565327097938076659421, 781250000000000000000000000000⟩]
def CB5_2_1I2PairCertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 5 => 1
  | 2, 4 => 2
  | 3, 4 => 3
  | 4, 2 => 2
  | 4, 3 => 3
  | 5, 1 => 1
  | _, _ => 0
def CB5_2_1I2PairP (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I2PairCertificates (CB5_2_1I2PairCertificateIndex a)).input
def CB5_2_1I2PairTerms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I2PairCertificates (CB5_2_1I2PairCertificateIndex a)).output

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
def CB5_2_1I2R0Raw (a : Fin 6) : Ball := residualBall (below (shape 5 2 1)) B5_2_1Law (stageBPriority (shape 5 2 1)) 2 (fun u => B5_2_1Little u ((stageBPriority (shape 5 2 1)) 2)) 0 a
def CB5_2_1I2R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_2_1I2R0P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I2R0Certificates (CB5_2_1I2R0CertificateIndex a)).input
def CB5_2_1I2R0Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I2R0Certificates (CB5_2_1I2R0CertificateIndex a)).output
def CB5_2_1I2R1Raw (a : Fin 6) : Ball := residualBall (below (shape 5 2 1)) B5_2_1Law (stageBPriority (shape 5 2 1)) 2 (fun u => B5_2_1Little u ((stageBPriority (shape 5 2 1)) 2)) 1 a
def CB5_2_1I2R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(357314469969927548416673592027 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(1765548688963737013294197353 / 50000000000000000000000000000), (1361957097 / 100000000000000000000000000000000)⟩ ⟨(-386028282976899231126090684623 / 78125000000000000000000000000), (190582413567 / 100000000000000000000000000000000)⟩ ⟨-8, 357314469969927548416673592027, 195312500000000000000000000000⟩]
def CB5_2_1I2R1P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I2R1Certificates (CB5_2_1I2R1CertificateIndex a)).input
def CB5_2_1I2R1Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I2R1Certificates (CB5_2_1I2R1CertificateIndex a)).output
def CB5_2_1I2R2Raw (a : Fin 6) : Ball := residualBall (below (shape 5 2 1)) B5_2_1Law (stageBPriority (shape 5 2 1)) 2 (fun u => B5_2_1Little u ((stageBPriority (shape 5 2 1)) 2)) 2 a
def CB5_2_1I2R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(31389291360282303794266717453669 / 100000000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩ ⟨(909271958288411609593400969681 / 2500000000000000000000000000000), (19940823019 / 100000000000000000000000000000000)⟩ ⟨(-115870339072252818198395155685549 / 100000000000000000000000000000000), (63527471103 / 100000000000000000000000000000000)⟩ ⟨-2, 31389291360282303794266717453669, 25000000000000000000000000000000⟩,
   .log ⟨(120809727570828910791192024941 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(162337072483012858063204652021 / 20000000000000000000000000000000), (70351753 / 25000000000000000000000000000000)⟩ ⟨(-26874834625851977830357946977153 / 4000000000000000000000000000000), (11646703067 / 5000000000000000000000000000000)⟩ ⟨-10, 120809727570828910791192024941, 97656250000000000000000000000⟩]
def CB5_2_1I2R2P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I2R2Certificates (CB5_2_1I2R2CertificateIndex a)).input
def CB5_2_1I2R2Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I2R2Certificates (CB5_2_1I2R2CertificateIndex a)).output
def CB5_2_1I2R3Raw (a : Fin 6) : Ball := residualBall (below (shape 5 2 1)) B5_2_1Law (stageBPriority (shape 5 2 1)) 2 (fun u => B5_2_1Little u ((stageBPriority (shape 5 2 1)) 2)) 3 a
def CB5_2_1I2R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_2_1I2R3P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I2R3Certificates (CB5_2_1I2R3CertificateIndex a)).input
def CB5_2_1I2R3Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I2R3Certificates (CB5_2_1I2R3CertificateIndex a)).output
def CB5_2_1I2R4Raw (a : Fin 6) : Ball := residualBall (below (shape 5 2 1)) B5_2_1Law (stageBPriority (shape 5 2 1)) 2 (fun u => B5_2_1Little u ((stageBPriority (shape 5 2 1)) 2)) 4 a
def CB5_2_1I2R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_2_1I2R4P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I2R4Certificates (CB5_2_1I2R4CertificateIndex a)).input
def CB5_2_1I2R4Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I2R4Certificates (CB5_2_1I2R4CertificateIndex a)).output
def CB5_2_1I2R5Raw (a : Fin 6) : Ball := residualBall (below (shape 5 2 1)) B5_2_1Law (stageBPriority (shape 5 2 1)) 2 (fun u => B5_2_1Little u ((stageBPriority (shape 5 2 1)) 2)) 5 a
def CB5_2_1I2R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_2_1I2R5P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I2R5Certificates (CB5_2_1I2R5CertificateIndex a)).input
def CB5_2_1I2R5Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I2R5Certificates (CB5_2_1I2R5CertificateIndex a)).output
def CB5_2_1I2R6Raw (a : Fin 6) : Ball := residualBall (below (shape 5 2 1)) B5_2_1Law (stageBPriority (shape 5 2 1)) 2 (fun u => B5_2_1Little u ((stageBPriority (shape 5 2 1)) 2)) 6 a
def CB5_2_1I2R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_2_1I2R6P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I2R6Certificates (CB5_2_1I2R6CertificateIndex a)).input
def CB5_2_1I2R6Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I2R6Certificates (CB5_2_1I2R6CertificateIndex a)).output
def CB5_2_1I2R7Raw (a : Fin 6) : Ball := residualBall (below (shape 5 2 1)) B5_2_1Law (stageBPriority (shape 5 2 1)) 2 (fun u => B5_2_1Little u ((stageBPriority (shape 5 2 1)) 2)) 7 a
def CB5_2_1I2R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_2_1I2R7P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I2R7Certificates (CB5_2_1I2R7CertificateIndex a)).input
def CB5_2_1I2R7Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I2R7Certificates (CB5_2_1I2R7CertificateIndex a)).output
def CB5_2_1I2R8Raw (a : Fin 6) : Ball := residualBall (below (shape 5 2 1)) B5_2_1Law (stageBPriority (shape 5 2 1)) 2 (fun u => B5_2_1Little u ((stageBPriority (shape 5 2 1)) 2)) 8 a
def CB5_2_1I2R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_2_1I2R8P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I2R8Certificates (CB5_2_1I2R8CertificateIndex a)).input
def CB5_2_1I2R8Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I2R8Certificates (CB5_2_1I2R8CertificateIndex a)).output
def CB5_2_1I2R9Raw (a : Fin 6) : Ball := residualBall (below (shape 5 2 1)) B5_2_1Law (stageBPriority (shape 5 2 1)) 2 (fun u => B5_2_1Little u ((stageBPriority (shape 5 2 1)) 2)) 9 a
def CB5_2_1I2R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_2_1I2R9P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I2R9Certificates (CB5_2_1I2R9CertificateIndex a)).input
def CB5_2_1I2R9Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I2R9Certificates (CB5_2_1I2R9CertificateIndex a)).output
def CB5_2_1I2R10Raw (a : Fin 6) : Ball := residualBall (below (shape 5 2 1)) B5_2_1Law (stageBPriority (shape 5 2 1)) 2 (fun u => B5_2_1Little u ((stageBPriority (shape 5 2 1)) 2)) 10 a
def CB5_2_1I2R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_2_1I2R10P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I2R10Certificates (CB5_2_1I2R10CertificateIndex a)).input
def CB5_2_1I2R10Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I2R10Certificates (CB5_2_1I2R10CertificateIndex a)).output
def CB5_2_1I2R11Raw (a : Fin 6) : Ball := residualBall (below (shape 5 2 1)) B5_2_1Law (stageBPriority (shape 5 2 1)) 2 (fun u => B5_2_1Little u ((stageBPriority (shape 5 2 1)) 2)) 11 a
def CB5_2_1I2R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_2_1I2R11P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I2R11Certificates (CB5_2_1I2R11CertificateIndex a)).input
def CB5_2_1I2R11Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I2R11Certificates (CB5_2_1I2R11CertificateIndex a)).output
def CB5_2_1I2R12Raw (a : Fin 6) : Ball := residualBall (below (shape 5 2 1)) B5_2_1Law (stageBPriority (shape 5 2 1)) 2 (fun u => B5_2_1Little u ((stageBPriority (shape 5 2 1)) 2)) 12 a
def CB5_2_1I2R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_2_1I2R12P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I2R12Certificates (CB5_2_1I2R12CertificateIndex a)).input
def CB5_2_1I2R12Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I2R12Certificates (CB5_2_1I2R12CertificateIndex a)).output
def CB5_2_1I2R13Raw (a : Fin 6) : Ball := residualBall (below (shape 5 2 1)) B5_2_1Law (stageBPriority (shape 5 2 1)) 2 (fun u => B5_2_1Little u ((stageBPriority (shape 5 2 1)) 2)) 13 a
def CB5_2_1I2R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_2_1I2R13P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I2R13Certificates (CB5_2_1I2R13CertificateIndex a)).input
def CB5_2_1I2R13Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I2R13Certificates (CB5_2_1I2R13CertificateIndex a)).output
def CB5_2_1I2R14Raw (a : Fin 6) : Ball := residualBall (below (shape 5 2 1)) B5_2_1Law (stageBPriority (shape 5 2 1)) 2 (fun u => B5_2_1Little u ((stageBPriority (shape 5 2 1)) 2)) 14 a
def CB5_2_1I2R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_2_1I2R14P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I2R14Certificates (CB5_2_1I2R14CertificateIndex a)).input
def CB5_2_1I2R14Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I2R14Certificates (CB5_2_1I2R14CertificateIndex a)).output
def CB5_2_1I2R15Raw (a : Fin 6) : Ball := residualBall (below (shape 5 2 1)) B5_2_1Law (stageBPriority (shape 5 2 1)) 2 (fun u => B5_2_1Little u ((stageBPriority (shape 5 2 1)) 2)) 15 a
def CB5_2_1I2R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_2_1I2R15P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I2R15Certificates (CB5_2_1I2R15CertificateIndex a)).input
def CB5_2_1I2R15Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I2R15Certificates (CB5_2_1I2R15CertificateIndex a)).output
def CB5_2_1I2R16Raw (a : Fin 6) : Ball := residualBall (below (shape 5 2 1)) B5_2_1Law (stageBPriority (shape 5 2 1)) 2 (fun u => B5_2_1Little u ((stageBPriority (shape 5 2 1)) 2)) 16 a
def CB5_2_1I2R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB5_2_1I2R16P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I2R16Certificates (CB5_2_1I2R16CertificateIndex a)).input
def CB5_2_1I2R16Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I2R16Certificates (CB5_2_1I2R16CertificateIndex a)).output

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
def CB6_1_1I0Raw (a : Fin 17) : Ball := marginalBall (below (shape 6 1 1)) B6_1_1Law ((stageBPriority (shape 6 1 1)) 0) a
def CB6_1_1I0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1 / 2), (13 / 20000000000000000000000000000000)⟩ ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823793 / 100000000000000000000000000000000)⟩ ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (8470329499 / 20000000000000000000000000000000)⟩ ⟨-1, 1, 1⟩]
def CB6_1_1I0P (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I0Certificates (CB6_1_1I0CertificateIndex a)).input
def CB6_1_1I0Terms (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I0Certificates (CB6_1_1I0CertificateIndex a)).output

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
def CB6_1_1I1PairValue (a : PairSlot) : ℝ := pairLaw (below (shape 6 1 1)) (shape 6 1 1) (fun u => (stageBLaw (shape 6 1 1) u : ℝ)) (fun u a => (littleLaw (shape 6 1 1) u ((stageBPriority (shape 6 1 1)) 1) a : ℝ)) a
def CB6_1_1I1PairCertificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1 / 2), (13 / 20000000000000000000000000000000)⟩ ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823793 / 100000000000000000000000000000000)⟩ ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (8470329499 / 20000000000000000000000000000000)⟩ ⟨-1, 1, 1⟩]
def CB6_1_1I1PairCertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 0 => 1
  | 0, 1 => 1
  | _, _ => 0
def CB6_1_1I1PairP (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I1PairCertificates (CB6_1_1I1PairCertificateIndex a)).input
def CB6_1_1I1PairTerms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I1PairCertificates (CB6_1_1I1PairCertificateIndex a)).output

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
def CB6_1_1I1R0Raw (a : Fin 6) : Ball := residualBall (below (shape 6 1 1)) B6_1_1Law (stageBPriority (shape 6 1 1)) 1 (fun u => B6_1_1Little u ((stageBPriority (shape 6 1 1)) 1)) 0 a
def CB6_1_1I1R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1 / 2), (13 / 20000000000000000000000000000000)⟩ ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823793 / 100000000000000000000000000000000)⟩ ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (8470329499 / 20000000000000000000000000000000)⟩ ⟨-1, 1, 1⟩]
def CB6_1_1I1R0P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I1R0Certificates (CB6_1_1I1R0CertificateIndex a)).input
def CB6_1_1I1R0Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I1R0Certificates (CB6_1_1I1R0CertificateIndex a)).output
def CB6_1_1I1R1Raw (a : Fin 6) : Ball := residualBall (below (shape 6 1 1)) B6_1_1Law (stageBPriority (shape 6 1 1)) 1 (fun u => B6_1_1Little u ((stageBPriority (shape 6 1 1)) 1)) 1 a
def CB6_1_1I1R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1 / 2), (13 / 20000000000000000000000000000000)⟩ ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823793 / 100000000000000000000000000000000)⟩ ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (8470329499 / 20000000000000000000000000000000)⟩ ⟨-1, 1, 1⟩]
def CB6_1_1I1R1P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I1R1Certificates (CB6_1_1I1R1CertificateIndex a)).input
def CB6_1_1I1R1Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I1R1Certificates (CB6_1_1I1R1CertificateIndex a)).output
def CB6_1_1I1R2Raw (a : Fin 6) : Ball := residualBall (below (shape 6 1 1)) B6_1_1Law (stageBPriority (shape 6 1 1)) 1 (fun u => B6_1_1Little u ((stageBPriority (shape 6 1 1)) 1)) 2 a
def CB6_1_1I1R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB6_1_1I1R2P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I1R2Certificates (CB6_1_1I1R2CertificateIndex a)).input
def CB6_1_1I1R2Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I1R2Certificates (CB6_1_1I1R2CertificateIndex a)).output
def CB6_1_1I1R3Raw (a : Fin 6) : Ball := residualBall (below (shape 6 1 1)) B6_1_1Law (stageBPriority (shape 6 1 1)) 1 (fun u => B6_1_1Little u ((stageBPriority (shape 6 1 1)) 1)) 3 a
def CB6_1_1I1R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB6_1_1I1R3P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I1R3Certificates (CB6_1_1I1R3CertificateIndex a)).input
def CB6_1_1I1R3Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I1R3Certificates (CB6_1_1I1R3CertificateIndex a)).output
def CB6_1_1I1R4Raw (a : Fin 6) : Ball := residualBall (below (shape 6 1 1)) B6_1_1Law (stageBPriority (shape 6 1 1)) 1 (fun u => B6_1_1Little u ((stageBPriority (shape 6 1 1)) 1)) 4 a
def CB6_1_1I1R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB6_1_1I1R4P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I1R4Certificates (CB6_1_1I1R4CertificateIndex a)).input
def CB6_1_1I1R4Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I1R4Certificates (CB6_1_1I1R4CertificateIndex a)).output
def CB6_1_1I1R5Raw (a : Fin 6) : Ball := residualBall (below (shape 6 1 1)) B6_1_1Law (stageBPriority (shape 6 1 1)) 1 (fun u => B6_1_1Little u ((stageBPriority (shape 6 1 1)) 1)) 5 a
def CB6_1_1I1R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB6_1_1I1R5P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I1R5Certificates (CB6_1_1I1R5CertificateIndex a)).input
def CB6_1_1I1R5Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I1R5Certificates (CB6_1_1I1R5CertificateIndex a)).output
def CB6_1_1I1R6Raw (a : Fin 6) : Ball := residualBall (below (shape 6 1 1)) B6_1_1Law (stageBPriority (shape 6 1 1)) 1 (fun u => B6_1_1Little u ((stageBPriority (shape 6 1 1)) 1)) 6 a
def CB6_1_1I1R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB6_1_1I1R6P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I1R6Certificates (CB6_1_1I1R6CertificateIndex a)).input
def CB6_1_1I1R6Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I1R6Certificates (CB6_1_1I1R6CertificateIndex a)).output
def CB6_1_1I1R7Raw (a : Fin 6) : Ball := residualBall (below (shape 6 1 1)) B6_1_1Law (stageBPriority (shape 6 1 1)) 1 (fun u => B6_1_1Little u ((stageBPriority (shape 6 1 1)) 1)) 7 a
def CB6_1_1I1R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB6_1_1I1R7P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I1R7Certificates (CB6_1_1I1R7CertificateIndex a)).input
def CB6_1_1I1R7Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I1R7Certificates (CB6_1_1I1R7CertificateIndex a)).output
def CB6_1_1I1R8Raw (a : Fin 6) : Ball := residualBall (below (shape 6 1 1)) B6_1_1Law (stageBPriority (shape 6 1 1)) 1 (fun u => B6_1_1Little u ((stageBPriority (shape 6 1 1)) 1)) 8 a
def CB6_1_1I1R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB6_1_1I1R8P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I1R8Certificates (CB6_1_1I1R8CertificateIndex a)).input
def CB6_1_1I1R8Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I1R8Certificates (CB6_1_1I1R8CertificateIndex a)).output
def CB6_1_1I1R9Raw (a : Fin 6) : Ball := residualBall (below (shape 6 1 1)) B6_1_1Law (stageBPriority (shape 6 1 1)) 1 (fun u => B6_1_1Little u ((stageBPriority (shape 6 1 1)) 1)) 9 a
def CB6_1_1I1R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB6_1_1I1R9P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I1R9Certificates (CB6_1_1I1R9CertificateIndex a)).input
def CB6_1_1I1R9Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I1R9Certificates (CB6_1_1I1R9CertificateIndex a)).output
def CB6_1_1I1R10Raw (a : Fin 6) : Ball := residualBall (below (shape 6 1 1)) B6_1_1Law (stageBPriority (shape 6 1 1)) 1 (fun u => B6_1_1Little u ((stageBPriority (shape 6 1 1)) 1)) 10 a
def CB6_1_1I1R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB6_1_1I1R10P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I1R10Certificates (CB6_1_1I1R10CertificateIndex a)).input
def CB6_1_1I1R10Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I1R10Certificates (CB6_1_1I1R10CertificateIndex a)).output
def CB6_1_1I1R11Raw (a : Fin 6) : Ball := residualBall (below (shape 6 1 1)) B6_1_1Law (stageBPriority (shape 6 1 1)) 1 (fun u => B6_1_1Little u ((stageBPriority (shape 6 1 1)) 1)) 11 a
def CB6_1_1I1R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB6_1_1I1R11P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I1R11Certificates (CB6_1_1I1R11CertificateIndex a)).input
def CB6_1_1I1R11Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I1R11Certificates (CB6_1_1I1R11CertificateIndex a)).output
def CB6_1_1I1R12Raw (a : Fin 6) : Ball := residualBall (below (shape 6 1 1)) B6_1_1Law (stageBPriority (shape 6 1 1)) 1 (fun u => B6_1_1Little u ((stageBPriority (shape 6 1 1)) 1)) 12 a
def CB6_1_1I1R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB6_1_1I1R12P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I1R12Certificates (CB6_1_1I1R12CertificateIndex a)).input
def CB6_1_1I1R12Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I1R12Certificates (CB6_1_1I1R12CertificateIndex a)).output
def CB6_1_1I1R13Raw (a : Fin 6) : Ball := residualBall (below (shape 6 1 1)) B6_1_1Law (stageBPriority (shape 6 1 1)) 1 (fun u => B6_1_1Little u ((stageBPriority (shape 6 1 1)) 1)) 13 a
def CB6_1_1I1R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB6_1_1I1R13P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I1R13Certificates (CB6_1_1I1R13CertificateIndex a)).input
def CB6_1_1I1R13Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I1R13Certificates (CB6_1_1I1R13CertificateIndex a)).output
def CB6_1_1I1R14Raw (a : Fin 6) : Ball := residualBall (below (shape 6 1 1)) B6_1_1Law (stageBPriority (shape 6 1 1)) 1 (fun u => B6_1_1Little u ((stageBPriority (shape 6 1 1)) 1)) 14 a
def CB6_1_1I1R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB6_1_1I1R14P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I1R14Certificates (CB6_1_1I1R14CertificateIndex a)).input
def CB6_1_1I1R14Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I1R14Certificates (CB6_1_1I1R14CertificateIndex a)).output
def CB6_1_1I1R15Raw (a : Fin 6) : Ball := residualBall (below (shape 6 1 1)) B6_1_1Law (stageBPriority (shape 6 1 1)) 1 (fun u => B6_1_1Little u ((stageBPriority (shape 6 1 1)) 1)) 15 a
def CB6_1_1I1R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB6_1_1I1R15P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I1R15Certificates (CB6_1_1I1R15CertificateIndex a)).input
def CB6_1_1I1R15Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I1R15Certificates (CB6_1_1I1R15CertificateIndex a)).output
def CB6_1_1I1R16Raw (a : Fin 6) : Ball := residualBall (below (shape 6 1 1)) B6_1_1Law (stageBPriority (shape 6 1 1)) 1 (fun u => B6_1_1Little u ((stageBPriority (shape 6 1 1)) 1)) 16 a
def CB6_1_1I1R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB6_1_1I1R16P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I1R16Certificates (CB6_1_1I1R16CertificateIndex a)).input
def CB6_1_1I1R16Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I1R16Certificates (CB6_1_1I1R16CertificateIndex a)).output

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
def CB6_1_1I2PairValue (a : PairSlot) : ℝ := pairLaw (below (shape 6 1 1)) (shape 6 1 1) (fun u => (stageBLaw (shape 6 1 1) u : ℝ)) (fun u a => (littleLaw (shape 6 1 1) u ((stageBPriority (shape 6 1 1)) 2) a : ℝ)) a
def CB6_1_1I2PairCertificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(2335026597000525930807493756423 / 10000000000000000000000000000000), (23 / 50000000000000000000000000000000)⟩ ⟨(6792881033012198704545432958047 / 20000000000000000000000000000000), (19778444719 / 100000000000000000000000000000000)⟩ ⟨(-72728090567983674950078491652741 / 50000000000000000000000000000000), (84703294929 / 100000000000000000000000000000000)⟩ ⟨-3, 2335026597000525930807493756423, 1250000000000000000000000000000⟩,
   .log ⟨(149723592147492123923952773557 / 10000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(1572677708112943242842492197897 / 25000000000000000000000000000000), (2536416327 / 100000000000000000000000000000000)⟩ ⟨(-105038737419798517471371269498513 / 25000000000000000000000000000000), (5293955927 / 3125000000000000000000000000000)⟩ ⟨-7, 149723592147492123923952773557, 78125000000000000000000000000⟩,
   .log ⟨(125762490542599097263427673501 / 250000000000000000000000000000), (17 / 50000000000000000000000000000000)⟩ ⟨(8640710434411545663323659384189 / 25000000000000000000000000000000), (21304994663 / 100000000000000000000000000000000)⟩ ⟨(-17176644636114111149204353480011 / 25000000000000000000000000000000), (42351647433 / 100000000000000000000000000000000)⟩ ⟨-1, 125762490542599097263427673501, 125000000000000000000000000000⟩]
def CB6_1_1I2PairCertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 2, 5 => 1
  | 3, 5 => 2
  | 4, 4 => 3
  | 5, 2 => 1
  | 5, 3 => 2
  | _, _ => 0
def CB6_1_1I2PairP (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I2PairCertificates (CB6_1_1I2PairCertificateIndex a)).input
def CB6_1_1I2PairTerms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I2PairCertificates (CB6_1_1I2PairCertificateIndex a)).output

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
def CB6_1_1I2R0Raw (a : Fin 6) : Ball := residualBall (below (shape 6 1 1)) B6_1_1Law (stageBPriority (shape 6 1 1)) 2 (fun u => B6_1_1Little u ((stageBPriority (shape 6 1 1)) 2)) 0 a
def CB6_1_1I2R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB6_1_1I2R0P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I2R0Certificates (CB6_1_1I2R0CertificateIndex a)).input
def CB6_1_1I2R0Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I2R0Certificates (CB6_1_1I2R0CertificateIndex a)).output
def CB6_1_1I2R1Raw (a : Fin 6) : Ball := residualBall (below (shape 6 1 1)) B6_1_1Law (stageBPriority (shape 6 1 1)) 2 (fun u => B6_1_1Little u ((stageBPriority (shape 6 1 1)) 2)) 1 a
def CB6_1_1I2R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB6_1_1I2R1P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I2R1Certificates (CB6_1_1I2R1CertificateIndex a)).input
def CB6_1_1I2R1Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I2R1Certificates (CB6_1_1I2R1CertificateIndex a)).output
def CB6_1_1I2R2Raw (a : Fin 6) : Ball := residualBall (below (shape 6 1 1)) B6_1_1Law (stageBPriority (shape 6 1 1)) 2 (fun u => B6_1_1Little u ((stageBPriority (shape 6 1 1)) 2)) 2 a
def CB6_1_1I2R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(2335026597000525930807493756423 / 10000000000000000000000000000000), (23 / 50000000000000000000000000000000)⟩ ⟨(6792881033012198704545432958047 / 20000000000000000000000000000000), (19778444719 / 100000000000000000000000000000000)⟩ ⟨(-72728090567983674950078491652741 / 50000000000000000000000000000000), (84703294929 / 100000000000000000000000000000000)⟩ ⟨-3, 2335026597000525930807493756423, 1250000000000000000000000000000⟩,
   .log ⟨(149723592147492123923952773557 / 10000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(1572677708112943242842492197897 / 25000000000000000000000000000000), (2536416327 / 100000000000000000000000000000000)⟩ ⟨(-105038737419798517471371269498513 / 25000000000000000000000000000000), (5293955927 / 3125000000000000000000000000000)⟩ ⟨-7, 149723592147492123923952773557, 78125000000000000000000000000⟩]
def CB6_1_1I2R2P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I2R2Certificates (CB6_1_1I2R2CertificateIndex a)).input
def CB6_1_1I2R2Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I2R2Certificates (CB6_1_1I2R2CertificateIndex a)).output
def CB6_1_1I2R3Raw (a : Fin 6) : Ball := residualBall (below (shape 6 1 1)) B6_1_1Law (stageBPriority (shape 6 1 1)) 2 (fun u => B6_1_1Little u ((stageBPriority (shape 6 1 1)) 2)) 3 a
def CB6_1_1I2R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB6_1_1I2R3P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I2R3Certificates (CB6_1_1I2R3CertificateIndex a)).input
def CB6_1_1I2R3Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I2R3Certificates (CB6_1_1I2R3CertificateIndex a)).output
def CB6_1_1I2R4Raw (a : Fin 6) : Ball := residualBall (below (shape 6 1 1)) B6_1_1Law (stageBPriority (shape 6 1 1)) 2 (fun u => B6_1_1Little u ((stageBPriority (shape 6 1 1)) 2)) 4 a
def CB6_1_1I2R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB6_1_1I2R4P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I2R4Certificates (CB6_1_1I2R4CertificateIndex a)).input
def CB6_1_1I2R4Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I2R4Certificates (CB6_1_1I2R4CertificateIndex a)).output
def CB6_1_1I2R5Raw (a : Fin 6) : Ball := residualBall (below (shape 6 1 1)) B6_1_1Law (stageBPriority (shape 6 1 1)) 2 (fun u => B6_1_1Little u ((stageBPriority (shape 6 1 1)) 2)) 5 a
def CB6_1_1I2R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB6_1_1I2R5P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I2R5Certificates (CB6_1_1I2R5CertificateIndex a)).input
def CB6_1_1I2R5Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I2R5Certificates (CB6_1_1I2R5CertificateIndex a)).output
def CB6_1_1I2R6Raw (a : Fin 6) : Ball := residualBall (below (shape 6 1 1)) B6_1_1Law (stageBPriority (shape 6 1 1)) 2 (fun u => B6_1_1Little u ((stageBPriority (shape 6 1 1)) 2)) 6 a
def CB6_1_1I2R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB6_1_1I2R6P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I2R6Certificates (CB6_1_1I2R6CertificateIndex a)).input
def CB6_1_1I2R6Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I2R6Certificates (CB6_1_1I2R6CertificateIndex a)).output
def CB6_1_1I2R7Raw (a : Fin 6) : Ball := residualBall (below (shape 6 1 1)) B6_1_1Law (stageBPriority (shape 6 1 1)) 2 (fun u => B6_1_1Little u ((stageBPriority (shape 6 1 1)) 2)) 7 a
def CB6_1_1I2R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB6_1_1I2R7P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I2R7Certificates (CB6_1_1I2R7CertificateIndex a)).input
def CB6_1_1I2R7Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I2R7Certificates (CB6_1_1I2R7CertificateIndex a)).output
def CB6_1_1I2R8Raw (a : Fin 6) : Ball := residualBall (below (shape 6 1 1)) B6_1_1Law (stageBPriority (shape 6 1 1)) 2 (fun u => B6_1_1Little u ((stageBPriority (shape 6 1 1)) 2)) 8 a
def CB6_1_1I2R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB6_1_1I2R8P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I2R8Certificates (CB6_1_1I2R8CertificateIndex a)).input
def CB6_1_1I2R8Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I2R8Certificates (CB6_1_1I2R8CertificateIndex a)).output
def CB6_1_1I2R9Raw (a : Fin 6) : Ball := residualBall (below (shape 6 1 1)) B6_1_1Law (stageBPriority (shape 6 1 1)) 2 (fun u => B6_1_1Little u ((stageBPriority (shape 6 1 1)) 2)) 9 a
def CB6_1_1I2R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB6_1_1I2R9P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I2R9Certificates (CB6_1_1I2R9CertificateIndex a)).input
def CB6_1_1I2R9Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I2R9Certificates (CB6_1_1I2R9CertificateIndex a)).output
def CB6_1_1I2R10Raw (a : Fin 6) : Ball := residualBall (below (shape 6 1 1)) B6_1_1Law (stageBPriority (shape 6 1 1)) 2 (fun u => B6_1_1Little u ((stageBPriority (shape 6 1 1)) 2)) 10 a
def CB6_1_1I2R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB6_1_1I2R10P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I2R10Certificates (CB6_1_1I2R10CertificateIndex a)).input
def CB6_1_1I2R10Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I2R10Certificates (CB6_1_1I2R10CertificateIndex a)).output
def CB6_1_1I2R11Raw (a : Fin 6) : Ball := residualBall (below (shape 6 1 1)) B6_1_1Law (stageBPriority (shape 6 1 1)) 2 (fun u => B6_1_1Little u ((stageBPriority (shape 6 1 1)) 2)) 11 a
def CB6_1_1I2R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB6_1_1I2R11P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I2R11Certificates (CB6_1_1I2R11CertificateIndex a)).input
def CB6_1_1I2R11Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I2R11Certificates (CB6_1_1I2R11CertificateIndex a)).output
def CB6_1_1I2R12Raw (a : Fin 6) : Ball := residualBall (below (shape 6 1 1)) B6_1_1Law (stageBPriority (shape 6 1 1)) 2 (fun u => B6_1_1Little u ((stageBPriority (shape 6 1 1)) 2)) 12 a
def CB6_1_1I2R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB6_1_1I2R12P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I2R12Certificates (CB6_1_1I2R12CertificateIndex a)).input
def CB6_1_1I2R12Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I2R12Certificates (CB6_1_1I2R12CertificateIndex a)).output
def CB6_1_1I2R13Raw (a : Fin 6) : Ball := residualBall (below (shape 6 1 1)) B6_1_1Law (stageBPriority (shape 6 1 1)) 2 (fun u => B6_1_1Little u ((stageBPriority (shape 6 1 1)) 2)) 13 a
def CB6_1_1I2R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB6_1_1I2R13P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I2R13Certificates (CB6_1_1I2R13CertificateIndex a)).input
def CB6_1_1I2R13Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I2R13Certificates (CB6_1_1I2R13CertificateIndex a)).output
def CB6_1_1I2R14Raw (a : Fin 6) : Ball := residualBall (below (shape 6 1 1)) B6_1_1Law (stageBPriority (shape 6 1 1)) 2 (fun u => B6_1_1Little u ((stageBPriority (shape 6 1 1)) 2)) 14 a
def CB6_1_1I2R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB6_1_1I2R14P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I2R14Certificates (CB6_1_1I2R14CertificateIndex a)).input
def CB6_1_1I2R14Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I2R14Certificates (CB6_1_1I2R14CertificateIndex a)).output
def CB6_1_1I2R15Raw (a : Fin 6) : Ball := residualBall (below (shape 6 1 1)) B6_1_1Law (stageBPriority (shape 6 1 1)) 2 (fun u => B6_1_1Little u ((stageBPriority (shape 6 1 1)) 2)) 15 a
def CB6_1_1I2R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB6_1_1I2R15P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I2R15Certificates (CB6_1_1I2R15CertificateIndex a)).input
def CB6_1_1I2R15Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I2R15Certificates (CB6_1_1I2R15CertificateIndex a)).output
def CB6_1_1I2R16Raw (a : Fin 6) : Ball := residualBall (below (shape 6 1 1)) B6_1_1Law (stageBPriority (shape 6 1 1)) 2 (fun u => B6_1_1Little u ((stageBPriority (shape 6 1 1)) 2)) 16 a
def CB6_1_1I2R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CB6_1_1I2R16P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I2R16Certificates (CB6_1_1I2R16CertificateIndex a)).input
def CB6_1_1I2R16Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I2R16Certificates (CB6_1_1I2R16CertificateIndex a)).output

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
def capacityABalls (s : Shape) (i : Fin 3) : Ball :=
  match s 0, s 1, s 2 with
  | 1, 1, 14 => ((Matrix.vecCons (CA1_1_14I0H) (Matrix.vecCons (CA1_1_14I1H) (Matrix.vecCons (CA1_1_14I2H) Matrix.vecEmpty))) i)
  | 1, 2, 13 => ((Matrix.vecCons (CA1_2_13I0H) (Matrix.vecCons (CA1_2_13I1H) (Matrix.vecCons (CA1_2_13I2H) Matrix.vecEmpty))) i)
  | 1, 3, 12 => ((Matrix.vecCons (CA1_3_12I0H) (Matrix.vecCons (CA1_3_12I1H) (Matrix.vecCons (CA1_3_12I2H) Matrix.vecEmpty))) i)
  | 1, 4, 11 => ((Matrix.vecCons (CA1_4_11I0H) (Matrix.vecCons (CA1_4_11I1H) (Matrix.vecCons (CA1_4_11I2H) Matrix.vecEmpty))) i)
  | 1, 5, 10 => ((Matrix.vecCons (CA1_5_10I0H) (Matrix.vecCons (CA1_5_10I1H) (Matrix.vecCons (CA1_5_10I2H) Matrix.vecEmpty))) i)
  | 1, 6, 9 => ((Matrix.vecCons (CA1_6_9I0H) (Matrix.vecCons (CA1_6_9I1H) (Matrix.vecCons (CA1_6_9I2H) Matrix.vecEmpty))) i)
  | 1, 7, 8 => ((Matrix.vecCons (CA1_7_8I0H) (Matrix.vecCons (CA1_7_8I1H) (Matrix.vecCons (CA1_7_8I2H) Matrix.vecEmpty))) i)
  | 2, 2, 12 => ((Matrix.vecCons (CA2_2_12I0H) (Matrix.vecCons (CA2_2_12I1H) (Matrix.vecCons (CA2_2_12I2H) Matrix.vecEmpty))) i)
  | 2, 3, 11 => ((Matrix.vecCons (CA2_3_11I0H) (Matrix.vecCons (CA2_3_11I1H) (Matrix.vecCons (CA2_3_11I2H) Matrix.vecEmpty))) i)
  | 2, 4, 10 => ((Matrix.vecCons (CA2_4_10I0H) (Matrix.vecCons (CA2_4_10I1H) (Matrix.vecCons (CA2_4_10I2H) Matrix.vecEmpty))) i)
  | 2, 5, 9 => ((Matrix.vecCons (CA2_5_9I0H) (Matrix.vecCons (CA2_5_9I1H) (Matrix.vecCons (CA2_5_9I2H) Matrix.vecEmpty))) i)
  | 2, 6, 8 => ((Matrix.vecCons (CA2_6_8I0H) (Matrix.vecCons (CA2_6_8I1H) (Matrix.vecCons (CA2_6_8I2H) Matrix.vecEmpty))) i)
  | 2, 7, 7 => ((Matrix.vecCons (CA2_7_7I0H) (Matrix.vecCons (CA2_7_7I1H) (Matrix.vecCons (CA2_7_7I2H) Matrix.vecEmpty))) i)
  | 3, 3, 10 => ((Matrix.vecCons (CA3_3_10I0H) (Matrix.vecCons (CA3_3_10I1H) (Matrix.vecCons (CA3_3_10I2H) Matrix.vecEmpty))) i)
  | 3, 4, 9 => ((Matrix.vecCons (CA3_4_9I0H) (Matrix.vecCons (CA3_4_9I1H) (Matrix.vecCons (CA3_4_9I2H) Matrix.vecEmpty))) i)
  | 3, 5, 8 => ((Matrix.vecCons (CA3_5_8I0H) (Matrix.vecCons (CA3_5_8I1H) (Matrix.vecCons (CA3_5_8I2H) Matrix.vecEmpty))) i)
  | 3, 6, 7 => ((Matrix.vecCons (CA3_6_7I0H) (Matrix.vecCons (CA3_6_7I1H) (Matrix.vecCons (CA3_6_7I2H) Matrix.vecEmpty))) i)
  | 4, 4, 8 => ((Matrix.vecCons (CA4_4_8I0H) (Matrix.vecCons (CA4_4_8I1H) (Matrix.vecCons (CA4_4_8I2H) Matrix.vecEmpty))) i)
  | 4, 5, 7 => ((Matrix.vecCons (CA4_5_7I0H) (Matrix.vecCons (CA4_5_7I1H) (Matrix.vecCons (CA4_5_7I2H) Matrix.vecEmpty))) i)
  | 4, 6, 6 => ((Matrix.vecCons (CA4_6_6I0H) (Matrix.vecCons (CA4_6_6I1H) (Matrix.vecCons (CA4_6_6I2H) Matrix.vecEmpty))) i)
  | 5, 5, 6 => ((Matrix.vecCons (CA5_5_6I0H) (Matrix.vecCons (CA5_5_6I1H) (Matrix.vecCons (CA5_5_6I2H) Matrix.vecEmpty))) i)
  | _, _, _ => (.exact 0)
def capacityBBalls (s : Shape) (i : Fin 3) : Ball :=
  match s 0, s 1, s 2 with
  | 1, 1, 6 => ((Matrix.vecCons (CB1_1_6I0H) (Matrix.vecCons (CB1_1_6I1H) (Matrix.vecCons (CB1_1_6I2H) Matrix.vecEmpty))) i)
  | 1, 2, 5 => ((Matrix.vecCons (CB1_2_5I0H) (Matrix.vecCons (CB1_2_5I1H) (Matrix.vecCons (CB1_2_5I2H) Matrix.vecEmpty))) i)
  | 1, 3, 4 => ((Matrix.vecCons (CB1_3_4I0H) (Matrix.vecCons (CB1_3_4I1H) (Matrix.vecCons (CB1_3_4I2H) Matrix.vecEmpty))) i)
  | 1, 4, 3 => ((Matrix.vecCons (CB1_4_3I0H) (Matrix.vecCons (CB1_4_3I1H) (Matrix.vecCons (CB1_4_3I2H) Matrix.vecEmpty))) i)
  | 1, 5, 2 => ((Matrix.vecCons (CB1_5_2I0H) (Matrix.vecCons (CB1_5_2I1H) (Matrix.vecCons (CB1_5_2I2H) Matrix.vecEmpty))) i)
  | 1, 6, 1 => ((Matrix.vecCons (CB1_6_1I0H) (Matrix.vecCons (CB1_6_1I1H) (Matrix.vecCons (CB1_6_1I2H) Matrix.vecEmpty))) i)
  | 2, 1, 5 => ((Matrix.vecCons (CB2_1_5I0H) (Matrix.vecCons (CB2_1_5I1H) (Matrix.vecCons (CB2_1_5I2H) Matrix.vecEmpty))) i)
  | 2, 2, 4 => ((Matrix.vecCons (CB2_2_4I0H) (Matrix.vecCons (CB2_2_4I1H) (Matrix.vecCons (CB2_2_4I2H) Matrix.vecEmpty))) i)
  | 2, 3, 3 => ((Matrix.vecCons (CB2_3_3I0H) (Matrix.vecCons (CB2_3_3I1H) (Matrix.vecCons (CB2_3_3I2H) Matrix.vecEmpty))) i)
  | 2, 4, 2 => ((Matrix.vecCons (CB2_4_2I0H) (Matrix.vecCons (CB2_4_2I1H) (Matrix.vecCons (CB2_4_2I2H) Matrix.vecEmpty))) i)
  | 2, 5, 1 => ((Matrix.vecCons (CB2_5_1I0H) (Matrix.vecCons (CB2_5_1I1H) (Matrix.vecCons (CB2_5_1I2H) Matrix.vecEmpty))) i)
  | 3, 1, 4 => ((Matrix.vecCons (CB3_1_4I0H) (Matrix.vecCons (CB3_1_4I1H) (Matrix.vecCons (CB3_1_4I2H) Matrix.vecEmpty))) i)
  | 3, 2, 3 => ((Matrix.vecCons (CB3_2_3I0H) (Matrix.vecCons (CB3_2_3I1H) (Matrix.vecCons (CB3_2_3I2H) Matrix.vecEmpty))) i)
  | 3, 3, 2 => ((Matrix.vecCons (CB3_3_2I0H) (Matrix.vecCons (CB3_3_2I1H) (Matrix.vecCons (CB3_3_2I2H) Matrix.vecEmpty))) i)
  | 3, 4, 1 => ((Matrix.vecCons (CB3_4_1I0H) (Matrix.vecCons (CB3_4_1I1H) (Matrix.vecCons (CB3_4_1I2H) Matrix.vecEmpty))) i)
  | 4, 1, 3 => ((Matrix.vecCons (CB4_1_3I0H) (Matrix.vecCons (CB4_1_3I1H) (Matrix.vecCons (CB4_1_3I2H) Matrix.vecEmpty))) i)
  | 4, 2, 2 => ((Matrix.vecCons (CB4_2_2I0H) (Matrix.vecCons (CB4_2_2I1H) (Matrix.vecCons (CB4_2_2I2H) Matrix.vecEmpty))) i)
  | 4, 3, 1 => ((Matrix.vecCons (CB4_3_1I0H) (Matrix.vecCons (CB4_3_1I1H) (Matrix.vecCons (CB4_3_1I2H) Matrix.vecEmpty))) i)
  | 5, 1, 2 => ((Matrix.vecCons (CB5_1_2I0H) (Matrix.vecCons (CB5_1_2I1H) (Matrix.vecCons (CB5_1_2I2H) Matrix.vecEmpty))) i)
  | 5, 2, 1 => ((Matrix.vecCons (CB5_2_1I0H) (Matrix.vecCons (CB5_2_1I1H) (Matrix.vecCons (CB5_2_1I2H) Matrix.vecEmpty))) i)
  | 6, 1, 1 => ((Matrix.vecCons (CB6_1_1I0H) (Matrix.vecCons (CB6_1_1I1H) (Matrix.vecCons (CB6_1_1I2H) Matrix.vecEmpty))) i)
  | _, _, _ => (.exact 0)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end


