-- Prove2me | Definitions.Def_OAIQ254M012
-- name    : OAIQ254M012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T05:57:21.636938+00:00
-- url     : https://prove2.me/theorems/41ce0532-8ab2-4b95-92f7-97751ff661a1
-- title:
--   Definitions bundle OAIQ254M012 of the split of OpenAI, Staggered extraction for exact matrix multiplication over every field
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant`, carved from OpenAI's openai/math development (OpenAI, *Staggered extraction for exact matrix multiplication over every field*, OpenAI Math Release, September 24, 2026, result family 107, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 600 declarations of OpenAI's Lean: 600 definitions. The definitions and types are `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I2PairP`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I2PairTerms`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I1R5P`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I1R5Raw`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I1R5Terms`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I1R6Raw`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I1R7Raw`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I1R8P`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I1R8Raw`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I1R8Terms`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I1R9CertificateIndex`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I1R9P`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I1R9Raw`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I1R9Terms`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I2PairRaw`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I2R0Raw`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I2R10Raw`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I2R11Raw`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I2R12Raw`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I2R13Raw`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I2R14Raw`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I2R15Raw`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I2R16Raw`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I2R1Raw`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I2R2Raw`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I2R3Raw`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I2R4Raw`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I2R5Raw`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I2R6Raw`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I2R7Raw`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I2R8Raw`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I2R9Raw`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_2_12I1PairRaw`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_2_12I1R0Raw`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_2_12I1R10Raw`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_2_12I1R11Raw`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_2_12I1R12Raw`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_2_12I1R13Raw`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_2_12I1R14Raw`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_2_12I1R15Raw` and 560 more.
--
--   **Sources.** They come from these modules of lean/OAI/LinearAlgebra, in whole or in part: `MatrixFields_CapacityA_CapA1_6_9I2Pair`, `MatrixFields_CapacityA_CapA1_7_8I1`, `MatrixFields_CapacityA_CapA1_7_8I2`, `MatrixFields_CapacityA_CapA1_7_8I2Pair`, `MatrixFields_CapacityA_CapA2_2_12I1`, `MatrixFields_CapacityA_CapA2_2_12I2`, `MatrixFields_CapacityA_CapA2_3_11I1`, `MatrixFields_CapacityA_CapA2_3_11I2`, `MatrixFields_CapacityA_CapA2_4_10I1`, `MatrixFields_CapacityA_CapA2_4_10I2`, `MatrixFields_CapacityA_CapA2_4_10I2Pair`, `MatrixFields_CapacityA_CapA2_5_9I1`, `MatrixFields_CapacityA_CapA2_5_9I2`, `MatrixFields_CapacityA_CapA2_5_9I2Pair`, `MatrixFields_CapacityA_CapA2_6_8I1`, `MatrixFields_CapacityA_CapA2_6_8I1Pair`, `MatrixFields_CapacityA_CapA2_6_8I2`, `MatrixFields_CapacityA_CapA2_6_8I2Pair`, `MatrixFields_CapacityA_CapA2_7_7I1`, `MatrixFields_CapacityA_CapA2_7_7I1Pair`, `MatrixFields_CapacityA_CapA2_7_7I2`, `MatrixFields_CapacityA_CapA2_7_7I2Pair`, `MatrixFields_CapacityA_CapA3_3_10I1`, `MatrixFields_CapacityA_CapA3_3_10I2`, `MatrixFields_CapacityA_CapA3_3_10I2Pair`, `MatrixFields_CapacityA_CapA3_4_9I1`, `MatrixFields_CapacityA_CapA3_4_9I2`, `MatrixFields_CapacityA_CapA3_4_9I2Pair`, `MatrixFields_CapacityA_CapA3_5_8I1`, `MatrixFields_CapacityA_CapA3_5_8I2`, `MatrixFields_CapacityA_CapA3_5_8I2Pair`, `MatrixFields_CapacityA_CapA3_6_7I1`, `MatrixFields_CapacityA_CapA3_6_7I1Pair`, `MatrixFields_CapacityA_CapA3_6_7I2`, `MatrixFields_CapacityA_CapA3_6_7I2Pair`, `MatrixFields_CapacityA_CapA4_4_8I1`, `MatrixFields_CapacityA_CapA4_4_8I2`, `MatrixFields_CapacityA_CapA4_4_8I2Pair`, `MatrixFields_CapacityA_CapA4_5_7I1`, `MatrixFields_CapacityA_CapA4_5_7I2`, `MatrixFields_CapacityA_CapA4_5_7I2Pair`, `MatrixFields_CapacityA_CapA4_6_6I1`, `MatrixFields_CapacityA_CapA4_6_6I1Pair`, `MatrixFields_CapacityA_CapA4_6_6I2`, `MatrixFields_CapacityA_CapA4_6_6I2Pair`, `MatrixFields_CapacityA_CapA5_5_6I1`, `MatrixFields_CapacityA_CapA5_5_6I2`, `MatrixFields_CapacityA_CapA5_5_6I2Pair`, `MatrixFields_CapacityB_CapB1_2_5I2`, `MatrixFields_CapacityB_CapB4_2_2I2`, `MatrixFields_CapacityB_CapB4_3_1I1`, `MatrixFields_CapacityB_CapB4_3_1I2`, `MatrixFields_CapacityB_CapB5_1_2I1`, `MatrixFields_CapacityB_CapB5_1_2I2`, `MatrixFields_CapacityB_CapB5_2_1I1`, `MatrixFields_CapacityB_CapB5_2_1I2`, `MatrixFields_CapacityB_CapB6_1_1I1`, `MatrixFields_CapacityB_CapB6_1_1I2`, `MatrixFields_Certificates_Four0_3_5`, `MatrixFields_Certificates_Four0_4_4`, `MatrixFields_Certificates_Four0_5_3`, `MatrixFields_Certificates_Four0_7_1`, `MatrixFields_Certificates_Four0_8_0`, `MatrixFields_Certificates_Four1_0_7`, `MatrixFields_Certificates_Four1_7_0`, `MatrixFields_Certificates_Four2_0_6`, `MatrixFields_Certificates_Four2_6_0`, `MatrixFields_Certificates_Four3_0_5`, `MatrixFields_Certificates_Four3_5_0`, `MatrixFields_Certificates_Four4_0_4`, `MatrixFields_Certificates_Four4_4_0`, `MatrixFields_Certificates_Four5_0_3`, `MatrixFields_Certificates_Four5_3_0`, `MatrixFields_Certificates_Four6_0_2`, `MatrixFields_Certificates_Four6_2_0`, `MatrixFields_Certificates_Four7_0_1`, `MatrixFields_Certificates_Four7_1_0`, `MatrixFields_Certificates_Four8_0_0`, `MatrixFields_Certificates_SplitA1_3_12`, `MatrixFields_Certificates_SplitB1_1_6`, `MatrixFields_Certificates_Zero0_1_7`.
--
--   **Imports.** It imports the bundles `OAIQ254M007`, `OAIQ254M008`, `OAIQ254M009` and `OAIQ254M010` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_1_14I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_2_13I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_3_12I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_4_11I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I2PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I2PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I2Singles_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_2_12I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_2_12I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_2_12I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_3_11I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_3_11I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_3_11I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_4_10I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_4_10I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_4_10I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_5_9I1Group_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_5_9I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_5_9I2PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_5_9I2Singles_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_5_9I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_6_8I1Group_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_6_8I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_6_8I2PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_6_8I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_6_8I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_7_7I1Group_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_7_7I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_7_7I2PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_7_7I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_7_7I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_3_10I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_3_10I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_3_10I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_4_9I1Group_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_4_9I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_4_9I2PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_4_9I2Singles_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_4_9I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_5_8I1Group_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_5_8I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_5_8I2PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_5_8I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_5_8I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_6_7I1Group_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_6_7I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_6_7I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_6_7I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_4_8I1Group_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_4_8I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_4_8I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_5_7I1ResidualEntropies_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_5_7I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_5_7I2PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_5_7I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_5_7I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_6_6I1Group_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_6_6I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_6_6I2PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_6_6I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_6_6I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA5_5_6I1ResidualEntropies_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA5_5_6I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA5_5_6I2PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA5_5_6I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA5_5_6I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_2_5I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_2_2I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_3_1I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_3_1I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB5_1_2I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB5_1_2I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB5_2_1I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB5_2_1I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB6_1_1I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB6_1_1I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z0_5_3Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z0_7_1Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z0_8_0Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z1_0_7Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z1_7_0Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z2_0_6Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z2_6_0Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z3_0_5Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z3_5_0Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z4_0_4Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z4_4_0Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z5_0_3Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z5_3_0Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z6_0_2Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z6_2_0Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z7_0_1Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z8_0_0Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.capacityABalls_sound` and `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.fourRateBalls_sound`.
-- source:
--   OpenAI, Staggered extraction for exact matrix multiplication over every field, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 107; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/LinearAlgebra at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ254M007
import Definitions.Def_OAIQ254M008
import Definitions.Def_OAIQ254M009
import Definitions.Def_OAIQ254M010

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
def Z0_0_8Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 5, 5 => ⟨0, 0⟩
  | _, _ => (.exact 0)
def Z0_0_8H2Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 5, 5 => ⟨0, 0⟩
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
def Z0_3_5Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 1, 5 => ⟨(9620008942863245806376100207999 / 100000000000000000000000000000000), (3927490439 / 100000000000000000000000000000000)⟩
  | 2, 4 => ⟨(4534819094630300182044972074441 / 12500000000000000000000000000000), (27366039047 / 100000000000000000000000000000000)⟩
  | 3, 4 => ⟨(2694400333776053497620803489567 / 20000000000000000000000000000000), (108579459 / 2000000000000000000000000000000)⟩
  | 4, 2 => ⟨(4534819094630300182044972074441 / 12500000000000000000000000000000), (27366039047 / 100000000000000000000000000000000)⟩
  | 4, 3 => ⟨(2694400333776053497620803489567 / 20000000000000000000000000000000), (108579459 / 2000000000000000000000000000000)⟩
  | 5, 1 => ⟨(9620008942863245806376100207999 / 100000000000000000000000000000000), (3927490439 / 100000000000000000000000000000000)⟩
  | _, _ => (.exact 0)
def Z0_3_5H2Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 1, 5 => ⟨(9620008942863245806376100207999 / 100000000000000000000000000000000), (3927490439 / 100000000000000000000000000000000)⟩
  | 2, 4 => ⟨(4534819094630300182044972074441 / 12500000000000000000000000000000), (27366039047 / 100000000000000000000000000000000)⟩
  | 3, 4 => ⟨(2694400333776053497620803489567 / 20000000000000000000000000000000), (108579459 / 2000000000000000000000000000000)⟩
  | 4, 2 => ⟨(4534819094630300182044972074441 / 12500000000000000000000000000000), (27366039047 / 100000000000000000000000000000000)⟩
  | 4, 3 => ⟨(2694400333776053497620803489567 / 20000000000000000000000000000000), (108579459 / 2000000000000000000000000000000)⟩
  | 5, 1 => ⟨(9620008942863245806376100207999 / 100000000000000000000000000000000), (3927490439 / 100000000000000000000000000000000)⟩
  | _, _ => (.exact 0)

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
def Z0_4_4Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 0, 5 => ⟨(588303889087378458388880598603 / 50000000000000000000000000000000), (109107079 / 25000000000000000000000000000000)⟩
  | 1, 4 => ⟨(26113887307747879276296106837317 / 100000000000000000000000000000000), (427326087 / 4000000000000000000000000000000)⟩
  | 2, 2 => ⟨(15034073848980370592136607206397 / 50000000000000000000000000000000), (25904605089 / 100000000000000000000000000000000)⟩
  | 2, 3 => ⟨(543150828368552529862213075723 / 3125000000000000000000000000000), (6648634459 / 100000000000000000000000000000000)⟩
  | 3, 2 => ⟨(543150828368552529862213075723 / 3125000000000000000000000000000), (6648634459 / 100000000000000000000000000000000)⟩
  | 3, 3 => ⟨(1688822355885139167546274512777 / 50000000000000000000000000000000), (644133659 / 50000000000000000000000000000000)⟩
  | 4, 1 => ⟨(26113887307747879276296106837317 / 100000000000000000000000000000000), (427326087 / 4000000000000000000000000000000)⟩
  | 5, 0 => ⟨(588303889087378458388880598603 / 50000000000000000000000000000000), (109107079 / 25000000000000000000000000000000)⟩
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
def Z0_6_2Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 2, 5 => ⟨(29145119833177663734886171853233 / 100000000000000000000000000000000), (2674938617 / 20000000000000000000000000000000)⟩
  | 3, 5 => ⟨(1015323830087268728146699904139 / 20000000000000000000000000000000), (191958983 / 10000000000000000000000000000000)⟩
  | 4, 4 => ⟨(6833509022528220411360048899287 / 25000000000000000000000000000000), (5603431897 / 20000000000000000000000000000000)⟩
  | 5, 2 => ⟨(29145119833177663734886171853233 / 100000000000000000000000000000000), (2674938617 / 20000000000000000000000000000000)⟩
  | 5, 3 => ⟨(1015323830087268728146699904139 / 20000000000000000000000000000000), (191958983 / 10000000000000000000000000000000)⟩
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
def Z0_2_6Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 2, 5 => ⟨(1984967199516249315866366927071 / 6250000000000000000000000000000), (4090126411 / 25000000000000000000000000000000)⟩
  | 3, 5 => ⟨(101635442150174547299056890093 / 1562500000000000000000000000000), (463823177 / 20000000000000000000000000000000)⟩
  | 4, 4 => ⟨(6296810649006533489546320818881 / 20000000000000000000000000000000), (1541620801 / 6250000000000000000000000000000)⟩
  | 5, 2 => ⟨(1984967199516249315866366927071 / 6250000000000000000000000000000), (4090126411 / 25000000000000000000000000000000)⟩
  | 5, 3 => ⟨(101635442150174547299056890093 / 1562500000000000000000000000000), (463823177 / 20000000000000000000000000000000)⟩
  | _, _ => (.exact 0)
def Z0_2_6H2Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 2, 5 => ⟨(1984967199516249315866366927071 / 6250000000000000000000000000000), (4090126411 / 25000000000000000000000000000000)⟩
  | 3, 5 => ⟨(101635442150174547299056890093 / 1562500000000000000000000000000), (463823177 / 20000000000000000000000000000000)⟩
  | 4, 4 => ⟨(6296810649006533489546320818881 / 20000000000000000000000000000000), (1541620801 / 6250000000000000000000000000000)⟩
  | 5, 2 => ⟨(1984967199516249315866366927071 / 6250000000000000000000000000000), (4090126411 / 25000000000000000000000000000000)⟩
  | 5, 3 => ⟨(101635442150174547299056890093 / 1562500000000000000000000000000), (463823177 / 20000000000000000000000000000000)⟩
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
def Z0_5_3Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 1, 5 => ⟨(8277526209207412807813577207303 / 100000000000000000000000000000000), (6397079 / 200000000000000000000000000000)⟩
  | 2, 4 => ⟨(18077101393929149380776110958019 / 50000000000000000000000000000000), (5568125837 / 20000000000000000000000000000000)⟩
  | 3, 4 => ⟨(1614325147848684263111295424987 / 12500000000000000000000000000000), (5104607757 / 100000000000000000000000000000000)⟩
  | 4, 2 => ⟨(18077101393929149380776110958019 / 50000000000000000000000000000000), (5568125837 / 20000000000000000000000000000000)⟩
  | 4, 3 => ⟨(1614325147848684263111295424987 / 12500000000000000000000000000000), (5104607757 / 100000000000000000000000000000000)⟩
  | 5, 1 => ⟨(8277526209207412807813577207303 / 100000000000000000000000000000000), (6397079 / 200000000000000000000000000000)⟩
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
def Z0_7_1Terms (a : PairSlot) : Ball :=
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
def Z0_8_0Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 5, 5 => ⟨0, 0⟩
  | _, _ => (.exact 0)

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
def Z1_0_7Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 4, 5 => ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
  | 5, 4 => ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
  | _, _ => (.exact 0)
def Z1_0_7H2Terms (a : PairSlot) : Ball :=
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
def Z1_7_0Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 4, 5 => ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
  | 5, 4 => ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
  | _, _ => (.exact 0)
def Z1_7_0H1Terms (a : PairSlot) : Ball :=
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
def Z2_0_6Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 2, 5 => ⟨(32726299880370363099063710099363 / 100000000000000000000000000000000), (17716480919 / 100000000000000000000000000000000)⟩
  | 3, 5 => ⟨(1737939955340792184583902537331 / 25000000000000000000000000000000), (1266002049 / 50000000000000000000000000000000)⟩
  | 4, 4 => ⟨(32980274307046266973832495616429 / 100000000000000000000000000000000), (5797076779 / 25000000000000000000000000000000)⟩
  | 5, 2 => ⟨(32726299880370363099063710099363 / 100000000000000000000000000000000), (17716480919 / 100000000000000000000000000000000)⟩
  | 5, 3 => ⟨(1737939955340792184583902537331 / 25000000000000000000000000000000), (1266002049 / 50000000000000000000000000000000)⟩
  | _, _ => (.exact 0)
def Z2_0_6H2Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 2, 5 => ⟨(32726299880370363099063710099363 / 100000000000000000000000000000000), (17716480919 / 100000000000000000000000000000000)⟩
  | 3, 5 => ⟨(1737939955340792184583902537331 / 25000000000000000000000000000000), (1266002049 / 50000000000000000000000000000000)⟩
  | 4, 4 => ⟨(32980274307046266973832495616429 / 100000000000000000000000000000000), (5797076779 / 25000000000000000000000000000000)⟩
  | 5, 2 => ⟨(32726299880370363099063710099363 / 100000000000000000000000000000000), (17716480919 / 100000000000000000000000000000000)⟩
  | 5, 3 => ⟨(1737939955340792184583902537331 / 25000000000000000000000000000000), (1266002049 / 50000000000000000000000000000000)⟩
  | _, _ => (.exact 0)

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
def Z2_6_0Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 2, 5 => ⟨(30427836027795558418888937514137 / 100000000000000000000000000000000), (460590303 / 3125000000000000000000000000000)⟩
  | 3, 5 => ⟨(1649434431835907568086056539411 / 25000000000000000000000000000000), (94517481 / 4000000000000000000000000000000)⟩
  | 4, 4 => ⟨(14816344574932932322026713712577 / 50000000000000000000000000000000), (26262508073 / 100000000000000000000000000000000)⟩
  | 5, 2 => ⟨(30427836027795558418888937514137 / 100000000000000000000000000000000), (460590303 / 3125000000000000000000000000000)⟩
  | 5, 3 => ⟨(1649434431835907568086056539411 / 25000000000000000000000000000000), (94517481 / 4000000000000000000000000000000)⟩
  | _, _ => (.exact 0)
def Z2_6_0H1Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 2, 5 => ⟨(30427836027795558418888937514137 / 100000000000000000000000000000000), (460590303 / 3125000000000000000000000000000)⟩
  | 3, 5 => ⟨(1649434431835907568086056539411 / 25000000000000000000000000000000), (94517481 / 4000000000000000000000000000000)⟩
  | 4, 4 => ⟨(14816344574932932322026713712577 / 50000000000000000000000000000000), (26262508073 / 100000000000000000000000000000000)⟩
  | 5, 2 => ⟨(30427836027795558418888937514137 / 100000000000000000000000000000000), (460590303 / 3125000000000000000000000000000)⟩
  | 5, 3 => ⟨(1649434431835907568086056539411 / 25000000000000000000000000000000), (94517481 / 4000000000000000000000000000000)⟩
  | _, _ => (.exact 0)

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
def Z3_0_5Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 1, 5 => ⟨(6271937325482765530304899555359 / 50000000000000000000000000000000), (2446947971 / 50000000000000000000000000000000)⟩
  | 2, 4 => ⟨(36514800988917506010651666724087 / 100000000000000000000000000000000), (26275620159 / 100000000000000000000000000000000)⟩
  | 3, 4 => ⟨(1454931286001010573435377377673 / 10000000000000000000000000000000), (3041167587 / 50000000000000000000000000000000)⟩
  | 4, 2 => ⟨(36514800988917506010651666724087 / 100000000000000000000000000000000), (26275620159 / 100000000000000000000000000000000)⟩
  | 4, 3 => ⟨(1454931286001010573435377377673 / 10000000000000000000000000000000), (3041167587 / 50000000000000000000000000000000)⟩
  | 5, 1 => ⟨(6271937325482765530304899555359 / 50000000000000000000000000000000), (2446947971 / 50000000000000000000000000000000)⟩
  | _, _ => (.exact 0)
def Z3_0_5H2Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 1, 5 => ⟨(6271937325482765530304899555359 / 50000000000000000000000000000000), (2446947971 / 50000000000000000000000000000000)⟩
  | 2, 4 => ⟨(36514800988917506010651666724087 / 100000000000000000000000000000000), (26275620159 / 100000000000000000000000000000000)⟩
  | 3, 4 => ⟨(1454931286001010573435377377673 / 10000000000000000000000000000000), (3041167587 / 50000000000000000000000000000000)⟩
  | 4, 2 => ⟨(36514800988917506010651666724087 / 100000000000000000000000000000000), (26275620159 / 100000000000000000000000000000000)⟩
  | 4, 3 => ⟨(1454931286001010573435377377673 / 10000000000000000000000000000000), (3041167587 / 50000000000000000000000000000000)⟩
  | 5, 1 => ⟨(6271937325482765530304899555359 / 50000000000000000000000000000000), (2446947971 / 50000000000000000000000000000000)⟩
  | _, _ => (.exact 0)

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
def Z3_5_0Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 1, 5 => ⟨(1887791376702802768234330198239 / 20000000000000000000000000000000), (191298981 / 5000000000000000000000000000000)⟩
  | 2, 4 => ⟨(4538157350748923372425986557083 / 12500000000000000000000000000000), (27257172089 / 100000000000000000000000000000000)⟩
  | 3, 4 => ⟨(13981761458054113306784224791891 / 100000000000000000000000000000000), (716714517 / 12500000000000000000000000000000)⟩
  | 4, 2 => ⟨(4538157350748923372425986557083 / 12500000000000000000000000000000), (27257172089 / 100000000000000000000000000000000)⟩
  | 4, 3 => ⟨(13981761458054113306784224791891 / 100000000000000000000000000000000), (716714517 / 12500000000000000000000000000000)⟩
  | 5, 1 => ⟨(1887791376702802768234330198239 / 20000000000000000000000000000000), (191298981 / 5000000000000000000000000000000)⟩
  | _, _ => (.exact 0)
def Z3_5_0H1Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 1, 5 => ⟨(1887791376702802768234330198239 / 20000000000000000000000000000000), (191298981 / 5000000000000000000000000000000)⟩
  | 2, 4 => ⟨(4538157350748923372425986557083 / 12500000000000000000000000000000), (27257172089 / 100000000000000000000000000000000)⟩
  | 3, 4 => ⟨(13981761458054113306784224791891 / 100000000000000000000000000000000), (716714517 / 12500000000000000000000000000000)⟩
  | 4, 2 => ⟨(4538157350748923372425986557083 / 12500000000000000000000000000000), (27257172089 / 100000000000000000000000000000000)⟩
  | 4, 3 => ⟨(13981761458054113306784224791891 / 100000000000000000000000000000000), (716714517 / 12500000000000000000000000000000)⟩
  | 5, 1 => ⟨(1887791376702802768234330198239 / 20000000000000000000000000000000), (191298981 / 5000000000000000000000000000000)⟩
  | _, _ => (.exact 0)

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
def Z4_0_4Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 0, 5 => ⟨(1626115430860444246284949942957 / 100000000000000000000000000000000), (116871387 / 20000000000000000000000000000000)⟩
  | 1, 4 => ⟨(837392469762340720305966731003 / 3125000000000000000000000000000), (1123648383 / 10000000000000000000000000000000)⟩
  | 2, 2 => ⟨(31338440079614690320574653450617 / 100000000000000000000000000000000), (77498073 / 312500000000000000000000000000)⟩
  | 2, 3 => ⟨(18303731318867196612732623716901 / 100000000000000000000000000000000), (7214619983 / 100000000000000000000000000000000)⟩
  | 3, 2 => ⟨(18303731318867196612732623716901 / 100000000000000000000000000000000), (7214619983 / 100000000000000000000000000000000)⟩
  | 3, 3 => ⟨(3602380400946510922725768272093 / 100000000000000000000000000000000), (349134453 / 25000000000000000000000000000000)⟩
  | 4, 1 => ⟨(837392469762340720305966731003 / 3125000000000000000000000000000), (1123648383 / 10000000000000000000000000000000)⟩
  | 5, 0 => ⟨(1626115430860444246284949942957 / 100000000000000000000000000000000), (116871387 / 20000000000000000000000000000000)⟩
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
def Z4_4_0Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 0, 5 => ⟨(1312019371607181543741200578043 / 100000000000000000000000000000000), (18070111 / 4000000000000000000000000000000)⟩
  | 1, 4 => ⟨(26381660305887817562778739090541 / 100000000000000000000000000000000), (1089701667 / 10000000000000000000000000000000)⟩
  | 2, 2 => ⟨(480241208915683334342627678761 / 1562500000000000000000000000000), (1013455771 / 4000000000000000000000000000000)⟩
  | 2, 3 => ⟨(3604325882796094985265170692573 / 20000000000000000000000000000000), (1407752823 / 20000000000000000000000000000000)⟩
  | 3, 2 => ⟨(3604325882796094985265170692573 / 20000000000000000000000000000000), (1407752823 / 20000000000000000000000000000000)⟩
  | 3, 3 => ⟨(1783513370984199948259882031059 / 50000000000000000000000000000000), (172419939 / 12500000000000000000000000000000)⟩
  | 4, 1 => ⟨(26381660305887817562778739090541 / 100000000000000000000000000000000), (1089701667 / 10000000000000000000000000000000)⟩
  | 5, 0 => ⟨(1312019371607181543741200578043 / 100000000000000000000000000000000), (18070111 / 4000000000000000000000000000000)⟩
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
def Z5_0_3Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 1, 5 => ⟨(8420970324370679601710618565453 / 100000000000000000000000000000000), (327382217 / 10000000000000000000000000000000)⟩
  | 2, 4 => ⟨(36295678058602714916587164090917 / 100000000000000000000000000000000), (1706034339 / 6250000000000000000000000000000)⟩
  | 3, 4 => ⟨(7311426455825088170477182923379 / 50000000000000000000000000000000), (3064119637 / 50000000000000000000000000000000)⟩
  | 4, 2 => ⟨(36295678058602714916587164090917 / 100000000000000000000000000000000), (1706034339 / 6250000000000000000000000000000)⟩
  | 4, 3 => ⟨(7311426455825088170477182923379 / 50000000000000000000000000000000), (3064119637 / 50000000000000000000000000000000)⟩
  | 5, 1 => ⟨(8420970324370679601710618565453 / 100000000000000000000000000000000), (327382217 / 10000000000000000000000000000000)⟩
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
def Z5_3_0Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 1, 5 => ⟨(2108145010568870815331944029893 / 25000000000000000000000000000000), (1639971173 / 50000000000000000000000000000000)⟩
  | 2, 4 => ⟨(7233991706521058045956490938163 / 20000000000000000000000000000000), (13891550817 / 50000000000000000000000000000000)⟩
  | 3, 4 => ⟨(2598673100349966355117959463809 / 20000000000000000000000000000000), (514988899 / 10000000000000000000000000000000)⟩
  | 4, 2 => ⟨(7233991706521058045956490938163 / 20000000000000000000000000000000), (13891550817 / 50000000000000000000000000000000)⟩
  | 4, 3 => ⟨(2598673100349966355117959463809 / 20000000000000000000000000000000), (514988899 / 10000000000000000000000000000000)⟩
  | 5, 1 => ⟨(2108145010568870815331944029893 / 25000000000000000000000000000000), (1639971173 / 50000000000000000000000000000000)⟩
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
def Z6_0_2Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 2, 5 => ⟨(4002495251518592288865068392969 / 12500000000000000000000000000000), (4177168589 / 25000000000000000000000000000000)⟩
  | 3, 5 => ⟨(6467401863598941893694372777521 / 20000000000000000000000000000000), (3429759337 / 20000000000000000000000000000000)⟩
  | 4, 4 => ⟨(32222994902771441455963269141339 / 100000000000000000000000000000000), (3397670639 / 20000000000000000000000000000000)⟩
  | 5, 2 => ⟨(4002495251518592288865068392969 / 12500000000000000000000000000000), (4177168589 / 25000000000000000000000000000000)⟩
  | 5, 3 => ⟨(6467401863598941893694372777521 / 20000000000000000000000000000000), (3429759337 / 20000000000000000000000000000000)⟩
  | _, _ => (.exact 0)

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
def Z6_2_0Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 2, 5 => ⟨(32142323678894247471214709989819 / 100000000000000000000000000000000), (8438161133 / 50000000000000000000000000000000)⟩
  | 3, 5 => ⟨(32226444852149744429123998456101 / 100000000000000000000000000000000), (4248292889 / 25000000000000000000000000000000)⟩
  | 4, 4 => ⟨(8051438474921156001297838292377 / 25000000000000000000000000000000), (16964307637 / 100000000000000000000000000000000)⟩
  | 5, 2 => ⟨(32142323678894247471214709989819 / 100000000000000000000000000000000), (8438161133 / 50000000000000000000000000000000)⟩
  | 5, 3 => ⟨(32226444852149744429123998456101 / 100000000000000000000000000000000), (4248292889 / 25000000000000000000000000000000)⟩
  | _, _ => (.exact 0)

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
def Z7_0_1Terms (a : PairSlot) : Ball :=
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
def Z7_1_0Terms (a : PairSlot) : Ball :=
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
def Z8_0_0Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 5, 5 => ⟨0, 0⟩
  | _, _ => (.exact 0)

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_6_9I2Pair
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
def CA1_6_9I2PairP (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2PairCertificates (CA1_6_9I2PairCertificateIndex a)).input
def CA1_6_9I2PairTerms (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2PairCertificates (CA1_6_9I2PairCertificateIndex a)).output

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_7_8I1
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
def CA1_7_8I1R5Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 5 a
def CA1_7_8I1R5P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R5Certificates (CA1_7_8I1R5CertificateIndex a)).input
def CA1_7_8I1R5Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R5Certificates (CA1_7_8I1R5CertificateIndex a)).output
def CA1_7_8I1R6Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 6 a
def CA1_7_8I1R7Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 7 a
def CA1_7_8I1R8Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 8 a
def CA1_7_8I1R8P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R8Certificates (CA1_7_8I1R8CertificateIndex a)).input
def CA1_7_8I1R8Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R8Certificates (CA1_7_8I1R8CertificateIndex a)).output
def CA1_7_8I1R9Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 9 a
def CA1_7_8I1R9CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_7_8I1R9P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R9Certificates (CA1_7_8I1R9CertificateIndex a)).input
def CA1_7_8I1R9Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R9Certificates (CA1_7_8I1R9CertificateIndex a)).output

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_7_8I2Pair
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
def CA1_7_8I2PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 1 7 8) A1_7_8Law 2 a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_7_8I2
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
def CA1_7_8I2R0Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 0 a
def CA1_7_8I2R1Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 1 a
def CA1_7_8I2R2Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 2 a
def CA1_7_8I2R3Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 3 a
def CA1_7_8I2R4Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 4 a
def CA1_7_8I2R5Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 5 a
def CA1_7_8I2R6Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 6 a
def CA1_7_8I2R7Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 7 a
def CA1_7_8I2R8Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 8 a
def CA1_7_8I2R9Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 9 a
def CA1_7_8I2R10Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 10 a
def CA1_7_8I2R11Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 11 a
def CA1_7_8I2R12Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 12 a
def CA1_7_8I2R13Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 13 a
def CA1_7_8I2R14Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 14 a
def CA1_7_8I2R15Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 15 a
def CA1_7_8I2R16Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 16 a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA2_2_12I1
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
def CA2_2_12I1PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 2 2 12) A2_2_12Law 1 a

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
def CA2_2_12I1R0Raw (a : PairSlot) : Ball := residualBall (below (shape 2 2 12)) A2_2_12Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 0 a
def CA2_2_12I1R1Raw (a : PairSlot) : Ball := residualBall (below (shape 2 2 12)) A2_2_12Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 1 a
def CA2_2_12I1R2Raw (a : PairSlot) : Ball := residualBall (below (shape 2 2 12)) A2_2_12Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 2 a
def CA2_2_12I1R3Raw (a : PairSlot) : Ball := residualBall (below (shape 2 2 12)) A2_2_12Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 3 a
def CA2_2_12I1R4Raw (a : PairSlot) : Ball := residualBall (below (shape 2 2 12)) A2_2_12Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 4 a
def CA2_2_12I1R5Raw (a : PairSlot) : Ball := residualBall (below (shape 2 2 12)) A2_2_12Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 5 a
def CA2_2_12I1R6Raw (a : PairSlot) : Ball := residualBall (below (shape 2 2 12)) A2_2_12Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 6 a
def CA2_2_12I1R7Raw (a : PairSlot) : Ball := residualBall (below (shape 2 2 12)) A2_2_12Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 7 a
def CA2_2_12I1R8Raw (a : PairSlot) : Ball := residualBall (below (shape 2 2 12)) A2_2_12Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 8 a
def CA2_2_12I1R9Raw (a : PairSlot) : Ball := residualBall (below (shape 2 2 12)) A2_2_12Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 9 a
def CA2_2_12I1R10Raw (a : PairSlot) : Ball := residualBall (below (shape 2 2 12)) A2_2_12Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 10 a
def CA2_2_12I1R11Raw (a : PairSlot) : Ball := residualBall (below (shape 2 2 12)) A2_2_12Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 11 a
def CA2_2_12I1R12Raw (a : PairSlot) : Ball := residualBall (below (shape 2 2 12)) A2_2_12Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 12 a
def CA2_2_12I1R13Raw (a : PairSlot) : Ball := residualBall (below (shape 2 2 12)) A2_2_12Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 13 a
def CA2_2_12I1R14Raw (a : PairSlot) : Ball := residualBall (below (shape 2 2 12)) A2_2_12Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 14 a
def CA2_2_12I1R15Raw (a : PairSlot) : Ball := residualBall (below (shape 2 2 12)) A2_2_12Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 15 a
def CA2_2_12I1R16Raw (a : PairSlot) : Ball := residualBall (below (shape 2 2 12)) A2_2_12Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 16 a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA2_2_12I2
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
def CA2_2_12I2PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 2 2 12) A2_2_12Law 2 a

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
def CA2_2_12I2R0Raw (a : PairSlot) : Ball := residualBall (below (shape 2 2 12)) A2_2_12Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 0 a
def CA2_2_12I2R1Raw (a : PairSlot) : Ball := residualBall (below (shape 2 2 12)) A2_2_12Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 1 a
def CA2_2_12I2R2Raw (a : PairSlot) : Ball := residualBall (below (shape 2 2 12)) A2_2_12Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 2 a
def CA2_2_12I2R3Raw (a : PairSlot) : Ball := residualBall (below (shape 2 2 12)) A2_2_12Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 3 a
def CA2_2_12I2R4Raw (a : PairSlot) : Ball := residualBall (below (shape 2 2 12)) A2_2_12Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 4 a
def CA2_2_12I2R5Raw (a : PairSlot) : Ball := residualBall (below (shape 2 2 12)) A2_2_12Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 5 a
def CA2_2_12I2R6Raw (a : PairSlot) : Ball := residualBall (below (shape 2 2 12)) A2_2_12Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 6 a
def CA2_2_12I2R7Raw (a : PairSlot) : Ball := residualBall (below (shape 2 2 12)) A2_2_12Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 7 a
def CA2_2_12I2R8Raw (a : PairSlot) : Ball := residualBall (below (shape 2 2 12)) A2_2_12Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 8 a
def CA2_2_12I2R9Raw (a : PairSlot) : Ball := residualBall (below (shape 2 2 12)) A2_2_12Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 9 a
def CA2_2_12I2R10Raw (a : PairSlot) : Ball := residualBall (below (shape 2 2 12)) A2_2_12Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 10 a
def CA2_2_12I2R11Raw (a : PairSlot) : Ball := residualBall (below (shape 2 2 12)) A2_2_12Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 11 a
def CA2_2_12I2R12Raw (a : PairSlot) : Ball := residualBall (below (shape 2 2 12)) A2_2_12Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 12 a
def CA2_2_12I2R13Raw (a : PairSlot) : Ball := residualBall (below (shape 2 2 12)) A2_2_12Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 13 a
def CA2_2_12I2R14Raw (a : PairSlot) : Ball := residualBall (below (shape 2 2 12)) A2_2_12Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 14 a
def CA2_2_12I2R15Raw (a : PairSlot) : Ball := residualBall (below (shape 2 2 12)) A2_2_12Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 15 a
def CA2_2_12I2R16Raw (a : PairSlot) : Ball := residualBall (below (shape 2 2 12)) A2_2_12Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 16 a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA2_3_11I1
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
def CA2_3_11I1PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 2 3 11) A2_3_11Law 1 a

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
def CA2_3_11I1R0Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 0 a
def CA2_3_11I1R1Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 1 a
def CA2_3_11I1R2Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 2 a
def CA2_3_11I1R3Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 3 a
def CA2_3_11I1R4Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 4 a
def CA2_3_11I1R5Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 5 a
def CA2_3_11I1R6Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 6 a
def CA2_3_11I1R7Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 7 a
def CA2_3_11I1R8Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 8 a
def CA2_3_11I1R9Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 9 a
def CA2_3_11I1R10Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 10 a
def CA2_3_11I1R11Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 11 a
def CA2_3_11I1R12Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 12 a
def CA2_3_11I1R13Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 13 a
def CA2_3_11I1R14Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 14 a
def CA2_3_11I1R15Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 15 a
def CA2_3_11I1R16Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 16 a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA2_3_11I2
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
def CA2_3_11I2PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 2 3 11) A2_3_11Law 2 a

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
def CA2_3_11I2R0Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 0 a
def CA2_3_11I2R1Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 1 a
def CA2_3_11I2R2Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 2 a
def CA2_3_11I2R3Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 3 a
def CA2_3_11I2R4Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 4 a
def CA2_3_11I2R5Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 5 a
def CA2_3_11I2R6Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 6 a
def CA2_3_11I2R7Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 7 a
def CA2_3_11I2R8Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 8 a
def CA2_3_11I2R9Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 9 a
def CA2_3_11I2R10Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 10 a
def CA2_3_11I2R11Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 11 a
def CA2_3_11I2R12Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 12 a
def CA2_3_11I2R13Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 13 a
def CA2_3_11I2R14Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 14 a
def CA2_3_11I2R15Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 15 a
def CA2_3_11I2R16Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 16 a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA2_4_10I1
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
def CA2_4_10I1PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 2 4 10) A2_4_10Law 1 a

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
def CA2_4_10I1R0Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 0 a
def CA2_4_10I1R1Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 1 a
def CA2_4_10I1R2Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 2 a
def CA2_4_10I1R3Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 3 a
def CA2_4_10I1R4Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 4 a
def CA2_4_10I1R5Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 5 a
def CA2_4_10I1R6Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 6 a
def CA2_4_10I1R7Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 7 a
def CA2_4_10I1R8Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 8 a
def CA2_4_10I1R9Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 9 a
def CA2_4_10I1R10Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 10 a
def CA2_4_10I1R11Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 11 a
def CA2_4_10I1R12Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 12 a
def CA2_4_10I1R13Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 13 a
def CA2_4_10I1R14Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 14 a
def CA2_4_10I1R15Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 15 a
def CA2_4_10I1R16Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 16 a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA2_4_10I2Pair
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
def CA2_4_10I2PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 2 4 10) A2_4_10Law 2 a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA2_4_10I2
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
def CA2_4_10I2R0Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 0 a
def CA2_4_10I2R1Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 1 a
def CA2_4_10I2R2Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 2 a
def CA2_4_10I2R3Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 3 a
def CA2_4_10I2R4Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 4 a
def CA2_4_10I2R5Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 5 a
def CA2_4_10I2R6Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 6 a
def CA2_4_10I2R7Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 7 a
def CA2_4_10I2R8Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 8 a
def CA2_4_10I2R9Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 9 a
def CA2_4_10I2R10Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 10 a
def CA2_4_10I2R11Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 11 a
def CA2_4_10I2R12Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 12 a
def CA2_4_10I2R13Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 13 a
def CA2_4_10I2R14Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 14 a
def CA2_4_10I2R15Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 15 a
def CA2_4_10I2R16Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 16 a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA2_5_9I1
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
def CA2_5_9I1PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 2 5 9) A2_5_9Law 1 a

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
def CA2_5_9I1R0Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 0 a
def CA2_5_9I1R1Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 1 a
def CA2_5_9I1R2Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 2 a
def CA2_5_9I1R3Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 3 a
def CA2_5_9I1R4Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 4 a
def CA2_5_9I1R5Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 5 a
def CA2_5_9I1R6Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 6 a
def CA2_5_9I1R7Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 7 a
def CA2_5_9I1R8Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 8 a
def CA2_5_9I1R9Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 9 a
def CA2_5_9I1R10Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 10 a
def CA2_5_9I1R11Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 11 a
def CA2_5_9I1R12Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 12 a
def CA2_5_9I1R13Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 13 a
def CA2_5_9I1R14Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 14 a
def CA2_5_9I1R15Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 15 a
def CA2_5_9I1R16Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 16 a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA2_5_9I2Pair
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
def CA2_5_9I2PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 2 5 9) A2_5_9Law 2 a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA2_5_9I2
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
def CA2_5_9I2R0Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 0 a
def CA2_5_9I2R1Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 1 a
def CA2_5_9I2R2Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 2 a
def CA2_5_9I2R3Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 3 a
def CA2_5_9I2R4Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 4 a
def CA2_5_9I2R5Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 5 a
def CA2_5_9I2R6Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 6 a
def CA2_5_9I2R7Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 7 a
def CA2_5_9I2R8Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 8 a
def CA2_5_9I2R9Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 9 a
def CA2_5_9I2R10Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 10 a
def CA2_5_9I2R11Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 11 a
def CA2_5_9I2R12Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 12 a
def CA2_5_9I2R13Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 13 a
def CA2_5_9I2R14Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 14 a
def CA2_5_9I2R15Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 15 a
def CA2_5_9I2R16Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 16 a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA2_6_8I1Pair
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
def CA2_6_8I1PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 2 6 8) A2_6_8Law 1 a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA2_6_8I1
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
def CA2_6_8I1R0Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 0 a
def CA2_6_8I1R1Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 1 a
def CA2_6_8I1R2Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 2 a
def CA2_6_8I1R3Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 3 a
def CA2_6_8I1R4Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 4 a
def CA2_6_8I1R5Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 5 a
def CA2_6_8I1R6Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 6 a
def CA2_6_8I1R7Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 7 a
def CA2_6_8I1R8Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 8 a
def CA2_6_8I1R9Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 9 a
def CA2_6_8I1R10Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 10 a
def CA2_6_8I1R11Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 11 a
def CA2_6_8I1R12Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 12 a
def CA2_6_8I1R13Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 13 a
def CA2_6_8I1R14Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 14 a
def CA2_6_8I1R15Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 15 a
def CA2_6_8I1R16Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 16 a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA2_6_8I2Pair
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
def CA2_6_8I2PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 2 6 8) A2_6_8Law 2 a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA2_6_8I2
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
def CA2_6_8I2R0Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 0 a
def CA2_6_8I2R1Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 1 a
def CA2_6_8I2R2Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 2 a
def CA2_6_8I2R3Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 3 a
def CA2_6_8I2R4Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 4 a
def CA2_6_8I2R5Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 5 a
def CA2_6_8I2R6Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 6 a
def CA2_6_8I2R7Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 7 a
def CA2_6_8I2R8Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 8 a
def CA2_6_8I2R9Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 9 a
def CA2_6_8I2R10Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 10 a
def CA2_6_8I2R11Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 11 a
def CA2_6_8I2R12Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 12 a
def CA2_6_8I2R13Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 13 a
def CA2_6_8I2R14Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 14 a
def CA2_6_8I2R15Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 15 a
def CA2_6_8I2R16Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 16 a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA2_7_7I1Pair
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
def CA2_7_7I1PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 2 7 7) A2_7_7Law 1 a
def CA2_7_7I1PairP (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I1PairCertificates (CA2_7_7I1PairCertificateIndex a)).input
def CA2_7_7I1PairTerms (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I1PairCertificates (CA2_7_7I1PairCertificateIndex a)).output

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA2_7_7I1
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
def CA2_7_7I1R0Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 0 a
def CA2_7_7I1R1Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 1 a
def CA2_7_7I1R2Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 2 a
def CA2_7_7I1R3Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 3 a
def CA2_7_7I1R4Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 4 a
def CA2_7_7I1R5Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 5 a
def CA2_7_7I1R6Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 6 a
def CA2_7_7I1R7Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 7 a
def CA2_7_7I1R8Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 8 a
def CA2_7_7I1R9Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 9 a
def CA2_7_7I1R10Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 10 a
def CA2_7_7I1R11Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 11 a
def CA2_7_7I1R12Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 12 a
def CA2_7_7I1R13Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 13 a
def CA2_7_7I1R14Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 14 a
def CA2_7_7I1R15Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 15 a
def CA2_7_7I1R16Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 16 a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA2_7_7I2Pair
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
def CA2_7_7I2PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 2 7 7) A2_7_7Law 2 a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA2_7_7I2
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
def CA2_7_7I2R0Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 0 a
def CA2_7_7I2R1Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 1 a
def CA2_7_7I2R2Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 2 a
def CA2_7_7I2R3Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 3 a
def CA2_7_7I2R4Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 4 a
def CA2_7_7I2R5Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 5 a
def CA2_7_7I2R6Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 6 a
def CA2_7_7I2R7Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 7 a
def CA2_7_7I2R8Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 8 a
def CA2_7_7I2R9Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 9 a
def CA2_7_7I2R10Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 10 a
def CA2_7_7I2R11Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 11 a
def CA2_7_7I2R12Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 12 a
def CA2_7_7I2R13Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 13 a
def CA2_7_7I2R14Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 14 a
def CA2_7_7I2R15Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 15 a
def CA2_7_7I2R16Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 16 a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA3_3_10I1
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
def CA3_3_10I1PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 3 3 10) A3_3_10Law 1 a

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
def CA3_3_10I1R0Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 0 a
def CA3_3_10I1R1Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 1 a
def CA3_3_10I1R2Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 2 a
def CA3_3_10I1R3Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 3 a
def CA3_3_10I1R4Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 4 a
def CA3_3_10I1R5Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 5 a
def CA3_3_10I1R6Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 6 a
def CA3_3_10I1R7Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 7 a
def CA3_3_10I1R8Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 8 a
def CA3_3_10I1R9Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 9 a
def CA3_3_10I1R10Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 10 a
def CA3_3_10I1R11Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 11 a
def CA3_3_10I1R12Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 12 a
def CA3_3_10I1R13Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 13 a
def CA3_3_10I1R14Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 14 a
def CA3_3_10I1R15Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 15 a
def CA3_3_10I1R16Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 16 a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA3_3_10I2Pair
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
def CA3_3_10I2PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 3 3 10) A3_3_10Law 2 a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA3_3_10I2
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
def CA3_3_10I2R0Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 0 a
def CA3_3_10I2R1Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 1 a
def CA3_3_10I2R2Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 2 a
def CA3_3_10I2R3Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 3 a
def CA3_3_10I2R4Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 4 a
def CA3_3_10I2R5Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 5 a
def CA3_3_10I2R6Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 6 a
def CA3_3_10I2R7Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 7 a
def CA3_3_10I2R8Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 8 a
def CA3_3_10I2R9Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 9 a
def CA3_3_10I2R10Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 10 a
def CA3_3_10I2R11Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 11 a
def CA3_3_10I2R12Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 12 a
def CA3_3_10I2R13Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 13 a
def CA3_3_10I2R14Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 14 a
def CA3_3_10I2R15Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 15 a
def CA3_3_10I2R16Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 16 a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA3_4_9I1
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
def CA3_4_9I1PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 3 4 9) A3_4_9Law 1 a

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
def CA3_4_9I1R0Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 0 a
def CA3_4_9I1R1Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 1 a
def CA3_4_9I1R2Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 2 a
def CA3_4_9I1R3Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 3 a
def CA3_4_9I1R4Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 4 a
def CA3_4_9I1R5Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 5 a
def CA3_4_9I1R6Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 6 a
def CA3_4_9I1R7Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 7 a
def CA3_4_9I1R8Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 8 a
def CA3_4_9I1R9Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 9 a
def CA3_4_9I1R10Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 10 a
def CA3_4_9I1R11Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 11 a
def CA3_4_9I1R12Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 12 a
def CA3_4_9I1R13Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 13 a
def CA3_4_9I1R14Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 14 a
def CA3_4_9I1R15Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 15 a
def CA3_4_9I1R16Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 16 a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA3_4_9I2Pair
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
def CA3_4_9I2PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 3 4 9) A3_4_9Law 2 a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA3_4_9I2
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
def CA3_4_9I2R0Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 0 a
def CA3_4_9I2R1Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 1 a
def CA3_4_9I2R2Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 2 a
def CA3_4_9I2R3Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 3 a
def CA3_4_9I2R4Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 4 a
def CA3_4_9I2R5Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 5 a
def CA3_4_9I2R6Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 6 a
def CA3_4_9I2R7Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 7 a
def CA3_4_9I2R8Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 8 a
def CA3_4_9I2R9Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 9 a
def CA3_4_9I2R10Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 10 a
def CA3_4_9I2R11Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 11 a
def CA3_4_9I2R12Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 12 a
def CA3_4_9I2R13Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 13 a
def CA3_4_9I2R14Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 14 a
def CA3_4_9I2R15Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 15 a
def CA3_4_9I2R16Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 16 a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA3_5_8I1
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
def CA3_5_8I1PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 3 5 8) A3_5_8Law 1 a

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
def CA3_5_8I1R0Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 0 a
def CA3_5_8I1R1Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 1 a
def CA3_5_8I1R2Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 2 a
def CA3_5_8I1R3Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 3 a
def CA3_5_8I1R4Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 4 a
def CA3_5_8I1R5Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 5 a
def CA3_5_8I1R6Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 6 a
def CA3_5_8I1R7Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 7 a
def CA3_5_8I1R8Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 8 a
def CA3_5_8I1R9Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 9 a
def CA3_5_8I1R10Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 10 a
def CA3_5_8I1R11Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 11 a
def CA3_5_8I1R12Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 12 a
def CA3_5_8I1R13Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 13 a
def CA3_5_8I1R14Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 14 a
def CA3_5_8I1R15Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 15 a
def CA3_5_8I1R16Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 16 a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA3_5_8I2Pair
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
def CA3_5_8I2PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 3 5 8) A3_5_8Law 2 a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA3_5_8I2
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
def CA3_5_8I2R0Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 0 a
def CA3_5_8I2R1Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 1 a
def CA3_5_8I2R2Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 2 a
def CA3_5_8I2R3Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 3 a
def CA3_5_8I2R4Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 4 a
def CA3_5_8I2R5Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 5 a
def CA3_5_8I2R6Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 6 a
def CA3_5_8I2R7Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 7 a
def CA3_5_8I2R8Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 8 a
def CA3_5_8I2R9Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 9 a
def CA3_5_8I2R10Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 10 a
def CA3_5_8I2R11Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 11 a
def CA3_5_8I2R12Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 12 a
def CA3_5_8I2R13Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 13 a
def CA3_5_8I2R14Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 14 a
def CA3_5_8I2R15Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 15 a
def CA3_5_8I2R16Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 16 a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA3_6_7I1Pair
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
def CA3_6_7I1PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 3 6 7) A3_6_7Law 1 a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA3_6_7I1
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
def CA3_6_7I1R0Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 0 a
def CA3_6_7I1R1Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 1 a
def CA3_6_7I1R2Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 2 a
def CA3_6_7I1R3Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 3 a
def CA3_6_7I1R4Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 4 a
def CA3_6_7I1R5Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 5 a
def CA3_6_7I1R6Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 6 a
def CA3_6_7I1R7Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 7 a
def CA3_6_7I1R8Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 8 a
def CA3_6_7I1R9Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 9 a
def CA3_6_7I1R10Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 10 a
def CA3_6_7I1R11Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 11 a
def CA3_6_7I1R12Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 12 a
def CA3_6_7I1R13Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 13 a
def CA3_6_7I1R14Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 14 a
def CA3_6_7I1R15Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 15 a
def CA3_6_7I1R16Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 16 a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA3_6_7I2Pair
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
def CA3_6_7I2PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 3 6 7) A3_6_7Law 2 a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA3_6_7I2
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
def CA3_6_7I2R0Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 0 a
def CA3_6_7I2R1Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 1 a
def CA3_6_7I2R2Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 2 a
def CA3_6_7I2R3Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 3 a
def CA3_6_7I2R4Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 4 a
def CA3_6_7I2R5Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 5 a
def CA3_6_7I2R6Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 6 a
def CA3_6_7I2R7Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 7 a
def CA3_6_7I2R8Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 8 a
def CA3_6_7I2R9Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 9 a
def CA3_6_7I2R10Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 10 a
def CA3_6_7I2R11Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 11 a
def CA3_6_7I2R12Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 12 a
def CA3_6_7I2R13Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 13 a
def CA3_6_7I2R14Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 14 a
def CA3_6_7I2R15Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 15 a
def CA3_6_7I2R16Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 16 a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA4_4_8I1
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
def CA4_4_8I1PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 4 4 8) A4_4_8Law 1 a

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
def CA4_4_8I1R0Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 0 a
def CA4_4_8I1R1Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 1 a
def CA4_4_8I1R2Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 2 a
def CA4_4_8I1R3Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 3 a
def CA4_4_8I1R4Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 4 a
def CA4_4_8I1R5Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 5 a
def CA4_4_8I1R6Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 6 a
def CA4_4_8I1R7Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 7 a
def CA4_4_8I1R8Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 8 a
def CA4_4_8I1R9Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 9 a
def CA4_4_8I1R10Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 10 a
def CA4_4_8I1R11Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 11 a
def CA4_4_8I1R12Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 12 a
def CA4_4_8I1R13Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 13 a
def CA4_4_8I1R14Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 14 a
def CA4_4_8I1R15Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 15 a
def CA4_4_8I1R16Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 16 a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA4_4_8I2Pair
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
def CA4_4_8I2PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 4 4 8) A4_4_8Law 2 a
def CA4_4_8I2PairP (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I2PairCertificates (CA4_4_8I2PairCertificateIndex a)).input
def CA4_4_8I2PairTerms (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I2PairCertificates (CA4_4_8I2PairCertificateIndex a)).output

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA4_4_8I2
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
def CA4_4_8I2R0Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 0 a
def CA4_4_8I2R1Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 1 a
def CA4_4_8I2R2Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 2 a
def CA4_4_8I2R3Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 3 a
def CA4_4_8I2R4Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 4 a
def CA4_4_8I2R5Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 5 a
def CA4_4_8I2R6Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 6 a
def CA4_4_8I2R7Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 7 a
def CA4_4_8I2R8Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 8 a
def CA4_4_8I2R9Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 9 a
def CA4_4_8I2R10Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 10 a
def CA4_4_8I2R11Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 11 a
def CA4_4_8I2R12Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 12 a
def CA4_4_8I2R13Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 13 a
def CA4_4_8I2R14Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 14 a
def CA4_4_8I2R15Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 15 a
def CA4_4_8I2R16Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 16 a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA4_5_7I1
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
def CA4_5_7I1PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 4 5 7) A4_5_7Law 1 a

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
def CA4_5_7I1R0Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 0 a
def CA4_5_7I1R1Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 1 a
def CA4_5_7I1R2Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 2 a
def CA4_5_7I1R3Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 3 a
def CA4_5_7I1R4Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 4 a
def CA4_5_7I1R5Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 5 a
def CA4_5_7I1R6Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 6 a
def CA4_5_7I1R7Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 7 a
def CA4_5_7I1R8Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 8 a
def CA4_5_7I1R9Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 9 a
def CA4_5_7I1R10Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 10 a
def CA4_5_7I1R11Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 11 a
def CA4_5_7I1R12Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 12 a
def CA4_5_7I1R13Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 13 a
def CA4_5_7I1R14Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 14 a
def CA4_5_7I1R15Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 15 a
def CA4_5_7I1R16Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 16 a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA4_5_7I2Pair
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
def CA4_5_7I2PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 4 5 7) A4_5_7Law 2 a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA4_5_7I2
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
def CA4_5_7I2R0Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 0 a
def CA4_5_7I2R1Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 1 a
def CA4_5_7I2R2Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 2 a
def CA4_5_7I2R2P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I2R2Certificates (CA4_5_7I2R2CertificateIndex a)).input
def CA4_5_7I2R2Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I2R2Certificates (CA4_5_7I2R2CertificateIndex a)).output
def CA4_5_7I2R3Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 3 a
def CA4_5_7I2R3P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I2R3Certificates (CA4_5_7I2R3CertificateIndex a)).input
def CA4_5_7I2R3Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I2R3Certificates (CA4_5_7I2R3CertificateIndex a)).output
def CA4_5_7I2R4Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 4 a
def CA4_5_7I2R4P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I2R4Certificates (CA4_5_7I2R4CertificateIndex a)).input
def CA4_5_7I2R4Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I2R4Certificates (CA4_5_7I2R4CertificateIndex a)).output
def CA4_5_7I2R5Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 5 a
def CA4_5_7I2R5P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I2R5Certificates (CA4_5_7I2R5CertificateIndex a)).input
def CA4_5_7I2R5Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I2R5Certificates (CA4_5_7I2R5CertificateIndex a)).output
def CA4_5_7I2R6Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 6 a
def CA4_5_7I2R7Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 7 a
def CA4_5_7I2R7P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I2R7Certificates (CA4_5_7I2R7CertificateIndex a)).input
def CA4_5_7I2R7Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I2R7Certificates (CA4_5_7I2R7CertificateIndex a)).output
def CA4_5_7I2R8Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 8 a
def CA4_5_7I2R8CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_5_7I2R8P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I2R8Certificates (CA4_5_7I2R8CertificateIndex a)).input
def CA4_5_7I2R8Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I2R8Certificates (CA4_5_7I2R8CertificateIndex a)).output
def CA4_5_7I2R9Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 9 a
def CA4_5_7I2R9CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_5_7I2R9P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I2R9Certificates (CA4_5_7I2R9CertificateIndex a)).input
def CA4_5_7I2R9Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I2R9Certificates (CA4_5_7I2R9CertificateIndex a)).output
def CA4_5_7I2R10Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 10 a
def CA4_5_7I2R11Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 11 a
def CA4_5_7I2R12Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 12 a
def CA4_5_7I2R13Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 13 a
def CA4_5_7I2R14Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 14 a
def CA4_5_7I2R15Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 15 a
def CA4_5_7I2R16Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 16 a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA4_6_6I1Pair
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
def CA4_6_6I1PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 4 6 6) A4_6_6Law 1 a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA4_6_6I1
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
def CA4_6_6I1R0Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 0 a
def CA4_6_6I1R1Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 1 a
def CA4_6_6I1R2Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 2 a
def CA4_6_6I1R3Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 3 a
def CA4_6_6I1R4Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 4 a
def CA4_6_6I1R5Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 5 a
def CA4_6_6I1R6Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 6 a
def CA4_6_6I1R7Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 7 a
def CA4_6_6I1R8Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 8 a
def CA4_6_6I1R9Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 9 a
def CA4_6_6I1R10Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 10 a
def CA4_6_6I1R11Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 11 a
def CA4_6_6I1R12Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 12 a
def CA4_6_6I1R13Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 13 a
def CA4_6_6I1R14Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 14 a
def CA4_6_6I1R15Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 15 a
def CA4_6_6I1R16Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 16 a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA4_6_6I2Pair
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
def CA4_6_6I2PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 4 6 6) A4_6_6Law 2 a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA4_6_6I2
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
def CA4_6_6I2R0Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 0 a
def CA4_6_6I2R1Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 1 a
def CA4_6_6I2R2Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 2 a
def CA4_6_6I2R3Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 3 a
def CA4_6_6I2R4Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 4 a
def CA4_6_6I2R5Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 5 a
def CA4_6_6I2R6Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 6 a
def CA4_6_6I2R7Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 7 a
def CA4_6_6I2R8Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 8 a
def CA4_6_6I2R9Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 9 a
def CA4_6_6I2R10Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 10 a
def CA4_6_6I2R11Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 11 a
def CA4_6_6I2R12Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 12 a
def CA4_6_6I2R13Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 13 a
def CA4_6_6I2R14Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 14 a
def CA4_6_6I2R15Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 15 a
def CA4_6_6I2R16Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 16 a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA5_5_6I1
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
def CA5_5_6I1PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 5 5 6) A5_5_6Law 1 a

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
def CA5_5_6I1R0Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 0 a
def CA5_5_6I1R1Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 1 a
def CA5_5_6I1R2Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 2 a
def CA5_5_6I1R3Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 3 a
def CA5_5_6I1R4Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 4 a
def CA5_5_6I1R5Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 5 a
def CA5_5_6I1R6Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 6 a
def CA5_5_6I1R7Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 7 a
def CA5_5_6I1R8Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 8 a
def CA5_5_6I1R9Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 9 a
def CA5_5_6I1R10Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 10 a
def CA5_5_6I1R11Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 11 a
def CA5_5_6I1R12Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 12 a
def CA5_5_6I1R13Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 13 a
def CA5_5_6I1R14Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 14 a
def CA5_5_6I1R15Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 15 a
def CA5_5_6I1R16Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 16 a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA5_5_6I2Pair
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
def CA5_5_6I2PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 5 5 6) A5_5_6Law 2 a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA5_5_6I2
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
def CA5_5_6I2R0Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 0 a
def CA5_5_6I2R1Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 1 a
def CA5_5_6I2R2Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 2 a
def CA5_5_6I2R3Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 3 a
def CA5_5_6I2R4Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 4 a
def CA5_5_6I2R5Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 5 a
def CA5_5_6I2R6Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 6 a
def CA5_5_6I2R7Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 7 a
def CA5_5_6I2R8Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 8 a
def CA5_5_6I2R9Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 9 a
def CA5_5_6I2R10Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 10 a
def CA5_5_6I2R11Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 11 a
def CA5_5_6I2R12Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 12 a
def CA5_5_6I2R13Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 13 a
def CA5_5_6I2R14Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 14 a
def CA5_5_6I2R15Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 15 a
def CA5_5_6I2R16Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 16 a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB1_2_5I2
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
def CB1_2_5I2R0P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_2_5I2R0Certificates (CB1_2_5I2R0CertificateIndex a)).input
def CB1_2_5I2R0Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_2_5I2R0Certificates (CB1_2_5I2R0CertificateIndex a)).output

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
def CB4_2_2I2R10P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R10Certificates (CB4_2_2I2R10CertificateIndex a)).input
def CB4_2_2I2R10Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R10Certificates (CB4_2_2I2R10CertificateIndex a)).output

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB4_3_1I1
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype
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
def CB4_3_1I1PairRaw (a : PairSlot) : Ball := pairLawBall (below (shape 4 3 1)) (shape 4 3 1) B4_3_1Law (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 1)) a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB4_3_1I2
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype
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
def CB4_3_1I2PairRaw (a : PairSlot) : Ball := pairLawBall (below (shape 4 3 1)) (shape 4 3 1) B4_3_1Law (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 2)) a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB5_1_2I1
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype
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
def CB5_1_2I1PairRaw (a : PairSlot) : Ball := pairLawBall (below (shape 5 1 2)) (shape 5 1 2) B5_1_2Law (fun u => B5_1_2Little u ((stageBPriority (shape 5 1 2)) 1)) a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB5_1_2I2
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype
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
def CB5_1_2I2PairRaw (a : PairSlot) : Ball := pairLawBall (below (shape 5 1 2)) (shape 5 1 2) B5_1_2Law (fun u => B5_1_2Little u ((stageBPriority (shape 5 1 2)) 2)) a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB5_2_1I1
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype
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
def CB5_2_1I1PairRaw (a : PairSlot) : Ball := pairLawBall (below (shape 5 2 1)) (shape 5 2 1) B5_2_1Law (fun u => B5_2_1Little u ((stageBPriority (shape 5 2 1)) 1)) a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB5_2_1I2
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype
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
def CB5_2_1I2PairRaw (a : PairSlot) : Ball := pairLawBall (below (shape 5 2 1)) (shape 5 2 1) B5_2_1Law (fun u => B5_2_1Little u ((stageBPriority (shape 5 2 1)) 2)) a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB6_1_1I1
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype
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
def CB6_1_1I1PairRaw (a : PairSlot) : Ball := pairLawBall (below (shape 6 1 1)) (shape 6 1 1) B6_1_1Law (fun u => B6_1_1Little u ((stageBPriority (shape 6 1 1)) 1)) a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB6_1_1I2
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype
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
def CB6_1_1I2PairRaw (a : PairSlot) : Ball := pairLawBall (below (shape 6 1 1)) (shape 6 1 1) B6_1_1Law (fun u => B6_1_1Little u ((stageBPriority (shape 6 1 1)) 2)) a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end


