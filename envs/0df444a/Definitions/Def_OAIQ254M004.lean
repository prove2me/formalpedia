-- Prove2me | Definitions.Def_OAIQ254M004
-- name    : OAIQ254M004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T05:49:53.887595+00:00
-- url     : https://prove2.me/theorems/7ba70da0-bcfa-416a-a92a-08adc9a1c081
-- title:
--   Definitions bundle OAIQ254M004 of the split of OpenAI, Staggered extraction for exact matrix multiplication over every field
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant`, carved from OpenAI's openai/math development (OpenAI, *Staggered extraction for exact matrix multiplication over every field*, OpenAI Math Release, September 24, 2026, result family 107, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 6425 declarations of OpenAI's Lean: 6425 definitions. The definitions and types are `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I2R5Mass`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I2R5MassTerm`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I2R5MassTermLog`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I2R5MassTermLogWitness`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I2R6Entropy`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I2R6H`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I2R6Mass`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I2R6MassTerm`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I2R6MassTermLog`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I2R6MassTermLogWitness`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I2R7H`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I2R7Mass`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I2R7MassTerm`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I2R8Entropy`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I2R8H`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I2R8Mass`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I2R8MassTerm`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I2R9Entropy`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I2R9H`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I2R9Mass`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I2R9MassTerm`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I2Singleton`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I0Entropy`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I0H`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I0Mass`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I0MassTerm`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I0MassTermLog`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I0MassTermLogWitness`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I0Value`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I1Group`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I1H`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I1PairEntropy`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I1PairH`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I1PairMass`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I1PairMassTerm`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I1PairMassTermLog`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I1PairMassTermLogWitness`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I1R0Entropy`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I1R0H`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I1R0Mass` and 6385 more.
--
--   **Sources.** They come from these modules of lean/OAI/LinearAlgebra, in whole or in part: `MatrixFields_CapacityA_CapA1_5_10I2`, `MatrixFields_CapacityA_CapA1_6_9I0`, `MatrixFields_CapacityA_CapA1_6_9I1`, `MatrixFields_CapacityA_CapA1_6_9I1Pair`, `MatrixFields_CapacityA_CapA1_6_9I2`, `MatrixFields_CapacityA_CapA1_6_9I2Pair`, `MatrixFields_CapacityA_CapA1_7_8I0`, `MatrixFields_CapacityA_CapA1_7_8I1`, `MatrixFields_CapacityA_CapA1_7_8I1Pair`, `MatrixFields_CapacityA_CapA1_7_8I2`, `MatrixFields_CapacityA_CapA1_7_8I2Pair`, `MatrixFields_CapacityA_CapA2_2_12I0`, `MatrixFields_CapacityA_CapA2_2_12I1`, `MatrixFields_CapacityA_CapA2_2_12I2`, `MatrixFields_CapacityA_CapA2_3_11I0`, `MatrixFields_CapacityA_CapA2_3_11I1`, `MatrixFields_CapacityA_CapA2_3_11I2`, `MatrixFields_CapacityA_CapA2_4_10I0`, `MatrixFields_CapacityA_CapA2_4_10I1`, `MatrixFields_CapacityA_CapA2_4_10I2`, `MatrixFields_CapacityA_CapA2_4_10I2Pair`, `MatrixFields_CapacityA_CapA2_5_9I0`, `MatrixFields_CapacityA_CapA2_5_9I1`, `MatrixFields_CapacityA_CapA2_5_9I2`, `MatrixFields_CapacityA_CapA2_5_9I2Pair`, `MatrixFields_CapacityA_CapA2_6_8I0`, `MatrixFields_CapacityA_CapA2_6_8I1`, `MatrixFields_CapacityA_CapA2_6_8I1Pair`, `MatrixFields_CapacityA_CapA2_6_8I2`, `MatrixFields_CapacityA_CapA2_6_8I2Pair`, `MatrixFields_CapacityA_CapA2_7_7I0`, `MatrixFields_CapacityA_CapA2_7_7I1`, `MatrixFields_CapacityA_CapA2_7_7I1Pair`, `MatrixFields_CapacityA_CapA2_7_7I2`, `MatrixFields_CapacityA_CapA2_7_7I2Pair`, `MatrixFields_CapacityA_CapA3_3_10I0`, `MatrixFields_CapacityA_CapA3_3_10I1`, `MatrixFields_CapacityA_CapA3_3_10I2`, `MatrixFields_CapacityA_CapA3_3_10I2Pair`, `MatrixFields_CapacityA_CapA3_4_9I0`, `MatrixFields_CapacityA_CapA3_4_9I1`, `MatrixFields_CapacityA_CapA3_4_9I2`, `MatrixFields_CapacityA_CapA3_4_9I2Pair`, `MatrixFields_CapacityA_CapA3_5_8I0`, `MatrixFields_CapacityA_CapA3_5_8I1`, `MatrixFields_CapacityA_CapA3_5_8I2`, `MatrixFields_CapacityA_CapA3_5_8I2Pair`, `MatrixFields_CapacityA_CapA3_6_7I0`, `MatrixFields_CapacityA_CapA3_6_7I1`, `MatrixFields_CapacityA_CapA3_6_7I1Pair`, `MatrixFields_CapacityA_CapA3_6_7I2`, `MatrixFields_CapacityA_CapA3_6_7I2Pair`, `MatrixFields_CapacityA_CapA4_4_8I0`, `MatrixFields_CapacityA_CapA4_4_8I1`, `MatrixFields_CapacityA_CapA4_4_8I2`, `MatrixFields_CapacityA_CapA4_4_8I2Pair`, `MatrixFields_CapacityA_CapA4_5_7I0`, `MatrixFields_CapacityA_CapA4_5_7I1`, `MatrixFields_CapacityA_CapA4_5_7I2`, `MatrixFields_CapacityA_CapA4_5_7I2Pair`, `MatrixFields_CapacityA_CapA4_6_6I0`, `MatrixFields_CapacityA_CapA4_6_6I1`, `MatrixFields_CapacityA_CapA4_6_6I1Pair`, `MatrixFields_CapacityA_CapA4_6_6I2`, `MatrixFields_CapacityA_CapA4_6_6I2Pair`, `MatrixFields_CapacityA_CapA5_5_6I0`, `MatrixFields_CapacityA_CapA5_5_6I1`, `MatrixFields_CapacityA_CapA5_5_6I2`, `MatrixFields_CapacityA_CapA5_5_6I2Pair`, `MatrixFields_CapacityB_CapB1_1_6I0`, `MatrixFields_CapacityB_CapB1_1_6I1`, `MatrixFields_CapacityB_CapB1_1_6I2`, `MatrixFields_CapacityB_CapB1_2_5I0`, `MatrixFields_CapacityB_CapB1_2_5I1`, `MatrixFields_CapacityB_CapB1_2_5I2`, `MatrixFields_CapacityB_CapB1_3_4I0`, `MatrixFields_CapacityB_CapB1_3_4I1`, `MatrixFields_CapacityB_CapB1_3_4I2`, `MatrixFields_CapacityB_CapB1_4_3I0`, `MatrixFields_CapacityB_CapB1_4_3I1`, `MatrixFields_CapacityB_CapB1_4_3I2`, `MatrixFields_CapacityB_CapB1_5_2I0`, `MatrixFields_CapacityB_CapB1_5_2I1`, `MatrixFields_CapacityB_CapB1_5_2I2`, `MatrixFields_CapacityB_CapB1_6_1I0`, `MatrixFields_CapacityB_CapB1_6_1I1`, `MatrixFields_CapacityB_CapB1_6_1I2`, `MatrixFields_CapacityB_CapB2_1_5I0`, `MatrixFields_CapacityB_CapB2_1_5I1`, `MatrixFields_CapacityB_CapB2_1_5I2`, `MatrixFields_CapacityB_CapB2_2_4I0`, `MatrixFields_CapacityB_CapB2_2_4I1`, `MatrixFields_CapacityB_CapB2_2_4I2`, `MatrixFields_CapacityB_CapB2_3_3I0`, `MatrixFields_CapacityB_CapB2_3_3I1`, `MatrixFields_CapacityB_CapB2_3_3I2`, `MatrixFields_CapacityB_CapB2_4_2I0`, `MatrixFields_CapacityB_CapB2_4_2I1`, `MatrixFields_CapacityB_CapB2_4_2I2`, `MatrixFields_CapacityB_CapB2_5_1I0`, `MatrixFields_CapacityB_CapB2_5_1I1`, `MatrixFields_CapacityB_CapB2_5_1I2`, `MatrixFields_CapacityB_CapB3_1_4I0`, `MatrixFields_CapacityB_CapB3_1_4I1`, `MatrixFields_CapacityB_CapB3_1_4I2`, `MatrixFields_CapacityB_CapB3_2_3I0`, `MatrixFields_CapacityB_CapB3_2_3I1`, `MatrixFields_CapacityB_CapB3_2_3I2`, `MatrixFields_Certificates_Four0_5_3`, `MatrixFields_Certificates_Four0_7_1`, `MatrixFields_Certificates_Four1_7_0`, `MatrixFields_Certificates_Four2_0_6`, `MatrixFields_Certificates_Four2_6_0`, `MatrixFields_Certificates_Four3_0_5`, `MatrixFields_Certificates_Four3_5_0`, `MatrixFields_Certificates_Four4_0_4`, `MatrixFields_Certificates_Four4_4_0`, `MatrixFields_Certificates_Four5_0_3`, `MatrixFields_Certificates_Four5_3_0`, `MatrixFields_Certificates_SplitB1_1_6`.
--
--   **Imports.** It imports the bundles `OAIQ254M000` and `OAIQ254M001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ254M007`, `OAIQ254M008`, `OAIQ254M009`, `OAIQ254M010` and `OAIQ254M011`; the statements `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I0_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I0_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_2_12I0_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_2_12I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_2_12I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_2_12I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_3_11I0_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_3_11I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_3_11I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_3_11I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_4_10I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_4_10I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_4_10I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_5_9I0_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_5_9I1Group_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_5_9I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_5_9I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_6_8I1Group_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_6_8I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_6_8I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_6_8I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_7_7I1Group_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_7_7I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_7_7I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_7_7I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_3_10I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_3_10I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_3_10I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_4_9I0_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_4_9I1Group_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_4_9I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_4_9I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_5_8I1Group_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_5_8I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_5_8I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_5_8I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_6_7I1Group_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_6_7I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_6_7I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_6_7I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_4_8I1Group_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_4_8I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_4_8I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_5_7I1ResidualEntropies_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_5_7I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_5_7I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_5_7I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_6_6I1Group_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_6_6I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_6_6I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_6_6I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA5_5_6I1ResidualEntropies_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA5_5_6I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA5_5_6I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA5_5_6I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_1_6I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_1_6I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_2_5I0_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_2_5I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_2_5I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_3_4I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_3_4I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_4_3I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_4_3I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_5_2I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_5_2I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_6_1I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_6_1I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB2_1_5I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB2_1_5I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB2_2_4I0_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB2_2_4I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB2_2_4I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB2_3_3I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB2_3_3I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB2_4_2I0_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB2_4_2I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB2_4_2I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB2_5_1I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB2_5_1I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_1_4I0_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_1_4I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_1_4I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I0_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I1_sound` and `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I2_sound`.
-- source:
--   OpenAI, Staggered extraction for exact matrix multiplication over every field, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 107; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/LinearAlgebra at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ254M000
import Definitions.Def_OAIQ254M001

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
def Z0_6_2H2H : Ball := ⟨(23944378514335224099169884586251 / 25000000000000000000000000000000), (79781549081 / 100000000000000000000000000000000)⟩

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
def Z0_5_3H2H : Ball := ⟨(57346330179855185674256162523237 / 50000000000000000000000000000000), (93463376761 / 100000000000000000000000000000000)⟩

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
def Z0_7_1H2H : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩

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
def Z1_7_0H1H : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩

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
def Z2_0_6H2H : Ball := ⟨(112336393710513330648631136113803 / 100000000000000000000000000000000), (84861100943 / 100000000000000000000000000000000)⟩

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
def Z2_6_0H1H : Ball := ⟨(103683836660144242026519754768717 / 100000000000000000000000000000000), (8164198529 / 10000000000000000000000000000000)⟩

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
def Z3_0_5H2H : Ball := ⟨(12721597699978628561123047922307 / 10000000000000000000000000000000), (95679526433 / 100000000000000000000000000000000)⟩

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
def Z3_5_0H1H : Ball := ⟨(238903908590238056509455072959 / 200000000000000000000000000000), (94809559569 / 100000000000000000000000000000000)⟩

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
def Z4_0_4H2H : Ball := ⟨(128393632044806289060917439826619 / 100000000000000000000000000000000), (85442666561 / 100000000000000000000000000000000)⟩

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
def Z4_4_0H1H : Ball := ⟨(3143327057388077034003488044143 / 2500000000000000000000000000000), (105842468483 / 100000000000000000000000000000000)⟩

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
def Z5_0_3H2H : Ball := ⟨(7417437661827946357406518562891 / 6250000000000000000000000000000), (94573045611 / 100000000000000000000000000000000)⟩

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
def Z5_3_0H1H : Ball := ⟨(7199488009578825658337503516179 / 6250000000000000000000000000000), (93601689817 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_5_10I2
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
def CA1_5_10I2R5Mass : Ball := ⟨(13882800147632490517692935191451 / 50000000000000000000000000000000), (7 / 12500000000000000000000000000000)⟩
def CA1_5_10I2R5MassTermLogWitness : LogWitness := ⟨-2, 13882800147632490517692935191451, 12500000000000000000000000000000⟩
def CA1_5_10I2R5MassTermLog : Ball := ⟨(-32034308273830957315809443556301 / 25000000000000000000000000000000), (50821977 / 80000000000000000000000000000)⟩
def CA1_5_10I2R5MassTerm : Ball := ⟨(35578071970659610136089639018193 / 100000000000000000000000000000000), (17638783817 / 100000000000000000000000000000000)⟩
def CA1_5_10I2R6Entropy : Ball := ⟨(20436338874106306910887822878337 / 100000000000000000000000000000000), (2071766607 / 25000000000000000000000000000000)⟩
def CA1_5_10I2R6Mass : Ball := ⟨(3813512477230879852792119856759 / 50000000000000000000000000000000), (31 / 100000000000000000000000000000000)⟩
def CA1_5_10I2R6MassTermLogWitness : LogWitness := ⟨-4, 3813512477230879852792119856759, 3125000000000000000000000000000⟩
def CA1_5_10I2R6MassTermLog : Ball := ⟨(-257347233095323829263237736034197 / 100000000000000000000000000000000), (105879118821 / 100000000000000000000000000000000)⟩
def CA1_5_10I2R6MassTerm : Ball := ⟨(1226746105487326305680353180991 / 6250000000000000000000000000000), (4037713447 / 50000000000000000000000000000000)⟩
def CA1_5_10I2R6H : Ball := ⟨(808401186309086020002171982481 / 100000000000000000000000000000000), (8181246661 / 50000000000000000000000000000000)⟩
def CA1_5_10I2R7Mass : Ball := ⟨0, 0⟩
def CA1_5_10I2R7MassTerm : Ball := .exact 0
def CA1_5_10I2R7H : Ball := ⟨0, 0⟩
def CA1_5_10I2R8Entropy : Ball := ⟨0, 0⟩
def CA1_5_10I2R8Mass : Ball := ⟨0, 0⟩
def CA1_5_10I2R8MassTerm : Ball := .exact 0
def CA1_5_10I2R8H : Ball := ⟨0, 0⟩
def CA1_5_10I2R9Entropy : Ball := ⟨0, 0⟩
def CA1_5_10I2R9Mass : Ball := ⟨0, 0⟩
def CA1_5_10I2R9MassTerm : Ball := .exact 0
def CA1_5_10I2R9H : Ball := ⟨0, 0⟩
def CA1_5_10I2Singleton : Ball := ⟨(58076349994733647690213708595139 / 100000000000000000000000000000000), (4925097331 / 10000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_6_9I0
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
def CA1_6_9I0Value (a : Fin 17) : ℝ := marginal (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) ((Equiv.refl (Fin 3)) 0) a
def CA1_6_9I0Entropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (330872247 / 781250000000000000000000000000)⟩
def CA1_6_9I0Mass : Ball := ⟨1, (37 / 25000000000000000000000000000000)⟩
def CA1_6_9I0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CA1_6_9I0MassTermLog : Ball := ⟨0, (2117582383 / 10000000000000000000000000000000)⟩
def CA1_6_9I0MassTerm : Ball := ⟨0, (21175823831 / 100000000000000000000000000000000)⟩
def CA1_6_9I0H : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (63527471447 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_6_9I1Pair
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
def CA1_6_9I1PairEntropy : Ball := ⟨(10540962222544916736398105749029 / 3125000000000000000000000000000), (4223288391 / 3125000000000000000000000000000)⟩
def CA1_6_9I1PairMass : Ball := ⟨(50000000000000000000000000000003 / 50000000000000000000000000000000), (33 / 6250000000000000000000000000000)⟩
def CA1_6_9I1PairMassTermLogWitness : LogWitness := ⟨0, 50000000000000000000000000000003, 50000000000000000000000000000000⟩
def CA1_6_9I1PairMassTermLog : Ball := ⟨(3 / 50000000000000000000000000000000), (2117582421 / 10000000000000000000000000000000)⟩
def CA1_6_9I1PairMassTerm : Ball := ⟨(-3 / 50000000000000000000000000000000), (21175824211 / 100000000000000000000000000000000)⟩
def CA1_6_9I1PairH : Ball := ⟨(168655395560718667782369691984467 / 50000000000000000000000000000000), (156321052723 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_6_9I1
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
def CA1_6_9I1R0Entropy : Ball := ⟨(1450945636735909530787380563 / 1000000000000000000000000000000), (24724901 / 50000000000000000000000000000000)⟩
def CA1_6_9I1R0Mass : Ball := ⟨(8339999762212914871827795077 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def CA1_6_9I1R0MassTermLogWitness : LogWitness := ⟨-13, 8339999762212914871827795077, 6103515625000000000000000000⟩
def CA1_6_9I1R0MassTermLog : Ball := ⟨(-54366969353445431436392639182027 / 6250000000000000000000000000000), (2316105809 / 781250000000000000000000000000)⟩
def CA1_6_9I1R0MassTerm : Ball := ⟨(1450945636735909530787380563 / 1000000000000000000000000000000), (24724901 / 50000000000000000000000000000000)⟩
def CA1_6_9I1R0H : Ball := ⟨0, (24724901 / 25000000000000000000000000000000)⟩
def CA1_6_9I1R1Entropy : Ball := ⟨(3496646491070427809635638237251 / 50000000000000000000000000000000), (1345323603 / 50000000000000000000000000000000)⟩
def CA1_6_9I1R1Mass : Ball := ⟨(352950608149296318805341356721 / 25000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
def CA1_6_9I1R1MassTermLogWitness : LogWitness := ⟨-7, 352950608149296318805341356721, 195312500000000000000000000000⟩
def CA1_6_9I1R1MassTermLog : Ball := ⟨(-26626893606023402032010273739139 / 6250000000000000000000000000000), (42351647543 / 25000000000000000000000000000000)⟩
def CA1_6_9I1R1MassTerm : Ball := ⟨(6014706106478444419857431517203 / 100000000000000000000000000000000), (478337281 / 20000000000000000000000000000000)⟩
def CA1_6_9I1R1H : Ball := ⟨(978586875662411199413844957299 / 100000000000000000000000000000000), (5082333611 / 100000000000000000000000000000000)⟩
def CA1_6_9I1R2Entropy : Ball := ⟨(1407306729499306941139487517623 / 2500000000000000000000000000000), (11446317991 / 50000000000000000000000000000000)⟩
def CA1_6_9I1R2Mass : Ball := ⟨(22119032006028451712913607951511 / 100000000000000000000000000000000), (37 / 50000000000000000000000000000000)⟩
def CA1_6_9I1R2MassTermLogWitness : LogWitness := ⟨-3, 22119032006028451712913607951511, 12500000000000000000000000000000⟩
def CA1_6_9I1R2MassTermLog : Ball := ⟨(-4714786785377982092429811765109 / 3125000000000000000000000000000), (42351647533 / 50000000000000000000000000000000)⟩
def CA1_6_9I1R2MassTerm : Ball := ⟨(1668584316918009319523460857527 / 5000000000000000000000000000000), (9367774529 / 50000000000000000000000000000000)⟩
def CA1_6_9I1R2H : Ball := ⟨(1146029142080604562755514177719 / 5000000000000000000000000000000), (520352313 / 1250000000000000000000000000000)⟩
def CA1_6_9I1R3Entropy : Ball := ⟨(47193991985842643597243398958631 / 50000000000000000000000000000000), (24724641189 / 50000000000000000000000000000000)⟩
def CA1_6_9I1R3Mass : Ball := ⟨(6613121390462484295530342757863 / 12500000000000000000000000000000), (11 / 10000000000000000000000000000000)⟩
def CA1_6_9I1R3MassTermLogWitness : LogWitness := ⟨-1, 6613121390462484295530342757863, 6250000000000000000000000000000⟩
def CA1_6_9I1R3MassTermLog : Ball := ⟨(-795841099307891183778313920487 / 1250000000000000000000000000000), (42351647573 / 100000000000000000000000000000000)⟩
def CA1_6_9I1R3MassTerm : Ball := ⟨(33683160302350037717787471431689 / 100000000000000000000000000000000), (2240612699 / 10000000000000000000000000000000)⟩
def CA1_6_9I1R3H : Ball := ⟨(60704823669335249476699326485573 / 100000000000000000000000000000000), (8981926171 / 12500000000000000000000000000000)⟩
def CA1_6_9I1R4Entropy : Ball := ⟨(14856550065251473183810446770099 / 25000000000000000000000000000000), (12301511301 / 50000000000000000000000000000000)⟩
def CA1_6_9I1R4Mass : Ball := ⟨(2764879000753556464114200993939 / 12500000000000000000000000000000), (89 / 100000000000000000000000000000000)⟩
def CA1_6_9I1R4MassTermLogWitness : LogWitness := ⟨-3, 2764879000753556464114200993939, 1562500000000000000000000000000⟩
def CA1_6_9I1R4MassTermLog : Ball := ⟨(-150873177132095426957753976483483 / 100000000000000000000000000000000), (42351647567 / 50000000000000000000000000000000)⟩
def CA1_6_9I1R4MassTerm : Ball := ⟨(1668584316918009319523460857527 / 5000000000000000000000000000000), (2341943637 / 12500000000000000000000000000000)⟩
def CA1_6_9I1R4H : Ball := ⟨(203550890020669580818535702577 / 781250000000000000000000000000), (21669285849 / 50000000000000000000000000000000)⟩
def CA1_6_9I1R5Entropy : Ball := ⟨(3811580354574422824556889786497 / 50000000000000000000000000000000), (351423879 / 12500000000000000000000000000000)⟩
def CA1_6_9I1R5Mass : Ball := ⟨(352950608149296318805341356721 / 25000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def CA1_6_9I1R5MassTermLogWitness : LogWitness := ⟨-7, 352950608149296318805341356721, 195312500000000000000000000000⟩
def CA1_6_9I1R5MassTermLog : Ball := ⟨(-26626893606023402032010273739139 / 6250000000000000000000000000000), (33881318091 / 20000000000000000000000000000000)⟩
def CA1_6_9I1R5MassTerm : Ball := ⟨(6014706106478444419857431517203 / 100000000000000000000000000000000), (1195843213 / 50000000000000000000000000000000)⟩
def CA1_6_9I1R5H : Ball := ⟨(1608454602670401229256348055791 / 100000000000000000000000000000000), (2601538729 / 50000000000000000000000000000000)⟩
def CA1_6_9I1R6Entropy : Ball := ⟨(161048236629498467833803288279 / 100000000000000000000000000000000), (13921639 / 25000000000000000000000000000000)⟩
def CA1_6_9I1R6Mass : Ball := ⟨(3335999904885165948731118031 / 20000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def CA1_6_9I1R6MassTermLogWitness : LogWitness := ⟨-13, 3335999904885165948731118031, 2441406250000000000000000000⟩
def CA1_6_9I1R6MassTermLog : Ball := ⟨(-869871509655126902982282226906437 / 100000000000000000000000000000000), (74115391883 / 25000000000000000000000000000000)⟩
def CA1_6_9I1R6MassTerm : Ball := ⟨(36273640918397738269684514077 / 25000000000000000000000000000000), (49449841 / 100000000000000000000000000000000)⟩
def CA1_6_9I1R6H : Ball := ⟨(15953672955907514755065231971 / 100000000000000000000000000000000), (105136397 / 100000000000000000000000000000000)⟩
def CA1_6_9I1R7Entropy : Ball := ⟨0, 0⟩
def CA1_6_9I1R7Mass : Ball := ⟨0, 0⟩
def CA1_6_9I1R7MassTerm : Ball := .exact 0
def CA1_6_9I1R7H : Ball := ⟨0, 0⟩
def CA1_6_9I1R8Entropy : Ball := ⟨0, 0⟩
def CA1_6_9I1R8Mass : Ball := ⟨0, 0⟩
def CA1_6_9I1R8MassTerm : Ball := .exact 0
def CA1_6_9I1R8H : Ball := ⟨0, 0⟩
def CA1_6_9I1R9Entropy : Ball := ⟨0, 0⟩
def CA1_6_9I1R9Mass : Ball := ⟨0, 0⟩
def CA1_6_9I1R9MassTerm : Ball := .exact 0
def CA1_6_9I1R9H : Ball := ⟨0, 0⟩
def CA1_6_9I1R10Entropy : Ball := ⟨0, 0⟩
def CA1_6_9I1R10Mass : Ball := ⟨0, 0⟩
def CA1_6_9I1R10MassTerm : Ball := .exact 0
def CA1_6_9I1R10H : Ball := ⟨0, 0⟩
def CA1_6_9I1R11Entropy : Ball := ⟨0, 0⟩
def CA1_6_9I1R11Mass : Ball := ⟨0, 0⟩
def CA1_6_9I1R11MassTerm : Ball := .exact 0
def CA1_6_9I1R11H : Ball := ⟨0, 0⟩
def CA1_6_9I1R12Entropy : Ball := ⟨0, 0⟩
def CA1_6_9I1R12Mass : Ball := ⟨0, 0⟩
def CA1_6_9I1R12MassTerm : Ball := .exact 0
def CA1_6_9I1R12H : Ball := ⟨0, 0⟩
def CA1_6_9I1R13Entropy : Ball := ⟨0, 0⟩
def CA1_6_9I1R13Mass : Ball := ⟨0, 0⟩
def CA1_6_9I1R13MassTerm : Ball := .exact 0
def CA1_6_9I1R13H : Ball := ⟨0, 0⟩
def CA1_6_9I1R14Entropy : Ball := ⟨0, 0⟩
def CA1_6_9I1R14Mass : Ball := ⟨0, 0⟩
def CA1_6_9I1R14MassTerm : Ball := .exact 0
def CA1_6_9I1R14H : Ball := ⟨0, 0⟩
def CA1_6_9I1R15Entropy : Ball := ⟨0, 0⟩
def CA1_6_9I1R15Mass : Ball := ⟨0, 0⟩
def CA1_6_9I1R15MassTerm : Ball := .exact 0
def CA1_6_9I1R15H : Ball := ⟨0, 0⟩
def CA1_6_9I1R16Entropy : Ball := ⟨0, 0⟩
def CA1_6_9I1R16Mass : Ball := ⟨0, 0⟩
def CA1_6_9I1R16MassTerm : Ball := .exact 0
def CA1_6_9I1R16H : Ball := ⟨0, 0⟩
def CA1_6_9I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA1_6_9I1R0H
  | 1 => CA1_6_9I1R1H
  | 2 => CA1_6_9I1R2H
  | 3 => CA1_6_9I1R3H
  | 4 => CA1_6_9I1R4H
  | 5 => CA1_6_9I1R5H
  | 6 => CA1_6_9I1R6H
  | 7 => CA1_6_9I1R7H
  | 8 => CA1_6_9I1R8H
  | 9 => CA1_6_9I1R9H
  | 10 => CA1_6_9I1R10H
  | 11 => CA1_6_9I1R11H
  | 12 => CA1_6_9I1R12H
  | 13 => CA1_6_9I1R13H
  | 14 => CA1_6_9I1R14H
  | 15 => CA1_6_9I1R15H
  | 16 => CA1_6_9I1R16H
  | _ => (.exact 0)
def CA1_6_9I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | _, _, _ => (.exact 0)
def CA1_6_9I1Singleton : Ball := ⟨0, 0⟩
def CA1_6_9I1Group : Ball := ⟨(11228291558488176702000743821487 / 10000000000000000000000000000000), (20913951647 / 12500000000000000000000000000000)⟩

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
def CA1_6_9I1H : Ball := ⟨(56372479975836900762362253769597 / 50000000000000000000000000000000), (19637771163 / 4000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
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
def CA1_6_9I2PairEntropy : Ball := ⟨(3891016477355924693202053046363 / 1250000000000000000000000000000), (30716599161 / 25000000000000000000000000000000)⟩
def CA1_6_9I2PairMass : Ball := ⟨(25000000000000000000000000000001 / 25000000000000000000000000000000), (141 / 25000000000000000000000000000000)⟩
def CA1_6_9I2PairMassTermLogWitness : LogWitness := ⟨0, 25000000000000000000000000000001, 25000000000000000000000000000000⟩
def CA1_6_9I2PairMassTermLog : Ball := ⟨(1 / 25000000000000000000000000000000), (10587912123 / 50000000000000000000000000000000)⟩
def CA1_6_9I2PairMassTerm : Ball := ⟨(-1 / 25000000000000000000000000000000), (21175824247 / 100000000000000000000000000000000)⟩
def CA1_6_9I2PairH : Ball := ⟨(77820329547118493864041060927261 / 25000000000000000000000000000000), (144042220891 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_6_9I2
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
def CA1_6_9I2R0Entropy : Ball := ⟨0, 0⟩
def CA1_6_9I2R0Mass : Ball := ⟨0, 0⟩
def CA1_6_9I2R0MassTerm : Ball := .exact 0
def CA1_6_9I2R0H : Ball := ⟨0, 0⟩
def CA1_6_9I2R1Entropy : Ball := ⟨(175988165289010751885124581 / 10000000000000000000000000000000), (286661 / 50000000000000000000000000000000)⟩
def CA1_6_9I2R1Mass : Ball := ⟨(15382325296305947711052937 / 12500000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def CA1_6_9I2R1MassTermLogWitness : LogWitness := ⟨-20, 15382325296305947711052937, 11920928955078125000000000⟩
def CA1_6_9I2R1MassTermLog : Ball := ⟨(-340200501500156456410996990662069 / 25000000000000000000000000000000), (55586740323 / 12500000000000000000000000000000)⟩
def CA1_6_9I2R1MassTerm : Ball := ⟨(1674583929613384375085323043 / 100000000000000000000000000000000), (273631 / 50000000000000000000000000000000)⟩
def CA1_6_9I2R1H : Ball := ⟨(85297723276723143765922767 / 100000000000000000000000000000000), (140073 / 12500000000000000000000000000000)⟩
def CA1_6_9I2R2Entropy : Ball := ⟨(252231639391446614411570731061 / 50000000000000000000000000000000), (10928187 / 6250000000000000000000000000000)⟩
def CA1_6_9I2R2Mass : Ball := ⟨(59579133574804858063667759891 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
def CA1_6_9I2R2MassTermLogWitness : LogWitness := ⟨-11, 59579133574804858063667759891, 48828125000000000000000000000⟩
def CA1_6_9I2R2MassTermLog : Ball := ⟨(-742562006000625825643988134828249 / 100000000000000000000000000000000), (254109892587 / 100000000000000000000000000000000)⟩
def CA1_6_9I2R2MassTerm : Ball := ⟨(22120600471543166305970057429 / 5000000000000000000000000000000), (15139651 / 10000000000000000000000000000000)⟩
def CA1_6_9I2R2H : Ball := ⟨(31025634676014951351870156771 / 50000000000000000000000000000000), (163123751 / 50000000000000000000000000000000)⟩
def CA1_6_9I2R3Entropy : Ball := ⟨(4028149719231608323841773543143 / 25000000000000000000000000000000), (2897902561 / 50000000000000000000000000000000)⟩
def CA1_6_9I2R3Mass : Ball := ⟨(1824494469086848250146899505551 / 50000000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩
def CA1_6_9I2R3MassTermLogWitness : LogWitness := ⟨-5, 1824494469086848250146899505551, 1562500000000000000000000000000⟩
def CA1_6_9I2R3MassTermLog : Ball := ⟨(-165536003000312912821994124701353 / 50000000000000000000000000000000), (25410988529 / 20000000000000000000000000000000)⟩
def CA1_6_9I2R3MassTerm : Ball := ⟨(1208078087635259307639586179963 / 10000000000000000000000000000000), (463622087 / 10000000000000000000000000000000)⟩
def CA1_6_9I2R3H : Ball := ⟨(2015909000286920109485616186471 / 50000000000000000000000000000000), (1304003249 / 12500000000000000000000000000000)⟩
def CA1_6_9I2R4Entropy : Ball := ⟨(11490440467622214123101573439551 / 20000000000000000000000000000000), (2668242887 / 10000000000000000000000000000000)⟩
def CA1_6_9I2R4Mass : Ball := ⟨(26452485561849937182121371031453 / 100000000000000000000000000000000), (1 / 2500000000000000000000000000000)⟩
def CA1_6_9I2R4MassTermLogWitness : LogWitness := ⟨-2, 26452485561849937182121371031453, 25000000000000000000000000000000⟩
def CA1_6_9I2R4MassTermLog : Ball := ⟨(-132982006000625825643988306689287 / 100000000000000000000000000000000), (79409339 / 125000000000000000000000000000)⟩
def CA1_6_9I2R4MassTerm : Ball := ⟨(7035409187434792722528646753737 / 20000000000000000000000000000000), (16804595201 / 100000000000000000000000000000000)⟩
def CA1_6_9I2R4H : Ball := ⟨(2227515640093710700286463342907 / 10000000000000000000000000000000), (43487024071 / 100000000000000000000000000000000)⟩
def CA1_6_9I2R5Entropy : Ball := ⟨(23517334978803995253072225468431 / 50000000000000000000000000000000), (10150976213 / 50000000000000000000000000000000)⟩
def CA1_6_9I2R5Mass : Ball := ⟨(4617510766963688803154952235103 / 25000000000000000000000000000000), (29 / 50000000000000000000000000000000)⟩
def CA1_6_9I2R5MassTermLogWitness : LogWitness := ⟨-3, 4617510766963688803154952235103, 3125000000000000000000000000000⟩
def CA1_6_9I2R5MassTermLog : Ball := ⟨(-42225501500156456410997071898441 / 25000000000000000000000000000000), (16940659009 / 20000000000000000000000000000000)⟩
def CA1_6_9I2R5MassTerm : Ball := ⟨(31196273250786212986478738546041 / 100000000000000000000000000000000), (15644735173 / 100000000000000000000000000000000)⟩
def CA1_6_9I2R5H : Ball := ⟨(15838396706821777519665712390821 / 100000000000000000000000000000000), (35946687599 / 100000000000000000000000000000000)⟩
def CA1_6_9I2R6Entropy : Ball := ⟨(1490627322365452699908344106343 / 25000000000000000000000000000000), (2322918157 / 100000000000000000000000000000000)⟩
def CA1_6_9I2R6Mass : Ball := ⟨(1352223299022380417157697666993 / 100000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
def CA1_6_9I2R6MassTermLogWitness : LogWitness := ⟨-7, 1352223299022380417157697666993, 781250000000000000000000000000⟩
def CA1_6_9I2R6MassTermLog : Ball := ⟨(-430342006000625825643988211212169 / 100000000000000000000000000000000), (169406590277 / 100000000000000000000000000000000)⟩
def CA1_6_9I2R6MassTerm : Ball := ⟨(5819184870620752836316869770767 / 100000000000000000000000000000000), (286344429 / 12500000000000000000000000000000)⟩
def CA1_6_9I2R6H : Ball := ⟨(28664883768211592663301330921 / 20000000000000000000000000000000), (4613673589 / 100000000000000000000000000000000)⟩
def CA1_6_9I2R7Entropy : Ball := ⟨0, 0⟩
def CA1_6_9I2R7Mass : Ball := ⟨0, 0⟩
def CA1_6_9I2R7MassTerm : Ball := .exact 0
def CA1_6_9I2R7H : Ball := ⟨0, 0⟩
def CA1_6_9I2R8Entropy : Ball := ⟨0, 0⟩
def CA1_6_9I2R8Mass : Ball := ⟨0, 0⟩
def CA1_6_9I2R8MassTerm : Ball := .exact 0
def CA1_6_9I2R8H : Ball := ⟨0, 0⟩
def CA1_6_9I2R9Entropy : Ball := ⟨0, 0⟩
def CA1_6_9I2R9Mass : Ball := ⟨0, 0⟩
def CA1_6_9I2R9MassTerm : Ball := .exact 0
def CA1_6_9I2R9H : Ball := ⟨0, 0⟩
def CA1_6_9I2R10Entropy : Ball := ⟨0, 0⟩
def CA1_6_9I2R10Mass : Ball := ⟨0, 0⟩
def CA1_6_9I2R10MassTerm : Ball := .exact 0
def CA1_6_9I2R10H : Ball := ⟨0, 0⟩
def CA1_6_9I2R11Entropy : Ball := ⟨0, 0⟩
def CA1_6_9I2R11Mass : Ball := ⟨0, 0⟩
def CA1_6_9I2R11MassTerm : Ball := .exact 0
def CA1_6_9I2R11H : Ball := ⟨0, 0⟩
def CA1_6_9I2R12Entropy : Ball := ⟨0, 0⟩
def CA1_6_9I2R12Mass : Ball := ⟨0, 0⟩
def CA1_6_9I2R12MassTerm : Ball := .exact 0
def CA1_6_9I2R12H : Ball := ⟨0, 0⟩
def CA1_6_9I2R13Entropy : Ball := ⟨0, 0⟩
def CA1_6_9I2R13Mass : Ball := ⟨0, 0⟩
def CA1_6_9I2R13MassTerm : Ball := .exact 0
def CA1_6_9I2R13H : Ball := ⟨0, 0⟩
def CA1_6_9I2R14Entropy : Ball := ⟨0, 0⟩
def CA1_6_9I2R14Mass : Ball := ⟨0, 0⟩
def CA1_6_9I2R14MassTerm : Ball := .exact 0
def CA1_6_9I2R14H : Ball := ⟨0, 0⟩
def CA1_6_9I2R15Entropy : Ball := ⟨0, 0⟩
def CA1_6_9I2R15Mass : Ball := ⟨0, 0⟩
def CA1_6_9I2R15MassTerm : Ball := .exact 0
def CA1_6_9I2R15H : Ball := ⟨0, 0⟩
def CA1_6_9I2R16Entropy : Ball := ⟨0, 0⟩
def CA1_6_9I2R16Mass : Ball := ⟨0, 0⟩
def CA1_6_9I2R16MassTerm : Ball := .exact 0
def CA1_6_9I2R16H : Ball := ⟨0, 0⟩
def CA1_6_9I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA1_6_9I2R0H
  | 1 => CA1_6_9I2R1H
  | 2 => CA1_6_9I2R2H
  | 3 => CA1_6_9I2R3H
  | 4 => CA1_6_9I2R4H
  | 5 => CA1_6_9I2R5H
  | 6 => CA1_6_9I2R6H
  | 7 => CA1_6_9I2R7H
  | 8 => CA1_6_9I2R8H
  | 9 => CA1_6_9I2R9H
  | 10 => CA1_6_9I2R10H
  | 11 => CA1_6_9I2R11H
  | 12 => CA1_6_9I2R12H
  | 13 => CA1_6_9I2R13H
  | 14 => CA1_6_9I2R14H
  | 15 => CA1_6_9I2R15H
  | 16 => CA1_6_9I2R16H
  | _ => (.exact 0)
def CA1_6_9I2Singleton : Ball := ⟨(29824973448744012139609014923727 / 50000000000000000000000000000000), (4955604441 / 10000000000000000000000000000000)⟩
def CA1_6_9I2Group : Ball := ⟨(102000778991737113609883620931201 / 100000000000000000000000000000000), (144362823747 / 100000000000000000000000000000000)⟩

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
def CA1_6_9I2H : Ball := ⟨(53639880102499874118198500923321 / 50000000000000000000000000000000), (86553573677 / 20000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_7_8I0
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
def CA1_7_8I0Value (a : Fin 17) : ℝ := marginal (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) ((Equiv.refl (Fin 3)) 0) a
def CA1_7_8I0Entropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (105879119 / 250000000000000000000000000000)⟩
def CA1_7_8I0Mass : Ball := ⟨(50000000000000000000000000000001 / 50000000000000000000000000000000), (69 / 50000000000000000000000000000000)⟩
def CA1_7_8I0MassTermLogWitness : LogWitness := ⟨0, 50000000000000000000000000000001, 50000000000000000000000000000000⟩
def CA1_7_8I0MassTermLog : Ball := ⟨(1 / 50000000000000000000000000000000), (1058791191 / 5000000000000000000000000000000)⟩
def CA1_7_8I0MassTerm : Ball := ⟨(-1 / 50000000000000000000000000000000), (21175823821 / 100000000000000000000000000000000)⟩
def CA1_7_8I0H : Ball := ⟨(17328679513998632735430798262583 / 25000000000000000000000000000000), (63527471421 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_7_8I1Pair
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
def CA1_7_8I1PairEntropy : Ball := ⟨(20743720621129846018702258959579 / 6250000000000000000000000000000), (31761715599 / 25000000000000000000000000000000)⟩
def CA1_7_8I1PairMass : Ball := ⟨1, (133 / 25000000000000000000000000000000)⟩
def CA1_7_8I1PairMassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CA1_7_8I1PairMassTermLog : Ball := ⟨0, (10587912107 / 50000000000000000000000000000000)⟩
def CA1_7_8I1PairMassTerm : Ball := ⟨0, (4235164843 / 20000000000000000000000000000000)⟩
def CA1_7_8I1PairH : Ball := ⟨(20743720621129846018702258959579 / 6250000000000000000000000000000), (148222686611 / 100000000000000000000000000000000)⟩

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
def CA1_7_8I1R0Entropy : Ball := ⟨(7043538258496618443777008947 / 100000000000000000000000000000000), (1175919 / 50000000000000000000000000000000)⟩
def CA1_7_8I1R0Mass : Ball := ⟨(584532371534609447407610401 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def CA1_7_8I1R0MassTermLogWitness : LogWitness := ⟨-18, 584532371534609447407610401, 381469726562500000000000000⟩
def CA1_7_8I1R0MassTermLog : Ball := ⟨(-1204986858128109531200624689824771 / 100000000000000000000000000000000), (40234099213 / 10000000000000000000000000000000)⟩
def CA1_7_8I1R0MassTerm : Ball := ⟨(7043538258496618443777008947 / 100000000000000000000000000000000), (1175919 / 50000000000000000000000000000000)⟩
def CA1_7_8I1R0H : Ball := ⟨0, (1175919 / 25000000000000000000000000000000)⟩
def CA1_7_8I1R1Entropy : Ball := ⟨(533899727137404610567259234731 / 50000000000000000000000000000000), (94111543 / 25000000000000000000000000000000)⟩
def CA1_7_8I1R1Mass : Ball := ⟨(37035762938464593102856286141 / 25000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
def CA1_7_8I1R1MassTermLogWitness : LogWitness := ⟨-10, 37035762938464593102856286141, 24414062500000000000000000000⟩
def CA1_7_8I1R1MassTermLog : Ball := ⟨(-130294941842514042684847297564929 / 20000000000000000000000000000000), (232934063213 / 100000000000000000000000000000000)⟩
def CA1_7_8I1R1MassTerm : Ball := ⟨(965114515632076229225822100971 / 100000000000000000000000000000000), (345075657 / 100000000000000000000000000000000)⟩
def CA1_7_8I1R1H : Ball := ⟨(102684938642732991908696368491 / 100000000000000000000000000000000), (721521829 / 100000000000000000000000000000000)⟩
def CA1_7_8I1R2Entropy : Ball := ⟨(22173084254528448887803165273229 / 100000000000000000000000000000000), (824283473 / 10000000000000000000000000000000)⟩
def CA1_7_8I1R2Mass : Ball := ⟨(284199226740662785783306515621 / 5000000000000000000000000000000), (29 / 100000000000000000000000000000000)⟩
def CA1_7_8I1R2MassTermLogWitness : LogWitness := ⟨-5, 284199226740662785783306515621, 156250000000000000000000000000⟩
def CA1_7_8I1R2MassTermLog : Ball := ⟨(-286751769658500763880690399379981 / 100000000000000000000000000000000), (7940933913 / 6250000000000000000000000000000)⟩
def CA1_7_8I1R2MassTerm : Ball := ⟨(3259785248138502638354366883571 / 20000000000000000000000000000000), (7221783373 / 100000000000000000000000000000000)⟩
def CA1_7_8I1R2H : Ball := ⟨(2937079006917967848015665427687 / 50000000000000000000000000000000), (15464618103 / 100000000000000000000000000000000)⟩
def CA1_7_8I1R3Entropy : Ball := ⟨(21500742839450818718169888830119 / 25000000000000000000000000000000), (5174804739 / 12500000000000000000000000000000)⟩
def CA1_7_8I1R3Mass : Ball := ⟨(22083643940530675651237518466307 / 50000000000000000000000000000000), (47 / 50000000000000000000000000000000)⟩
def CA1_7_8I1R3MassTermLogWitness : LogWitness := ⟨-2, 22083643940530675651237518466307, 12500000000000000000000000000000⟩
def CA1_7_8I1R3MassTermLog : Ball := ⟨(-81718576409726083693032108385419 / 100000000000000000000000000000000), (31763735631 / 50000000000000000000000000000000)⟩
def CA1_7_8I1R3MassTerm : Ball := ⟨(9023219723797202219809978218521 / 25000000000000000000000000000000), (28058361193 / 100000000000000000000000000000000)⟩
def CA1_7_8I1R3H : Ball := ⟨(6238761557826808249179955305799 / 12500000000000000000000000000000), (13891359821 / 20000000000000000000000000000000)⟩
def CA1_7_8I1R4Entropy : Ball := ⟨(86255489647744146633277294971313 / 100000000000000000000000000000000), (39115762479 / 100000000000000000000000000000000)⟩
def CA1_7_8I1R4Mass : Ball := ⟨(5520910985132668912809379616577 / 12500000000000000000000000000000), (59 / 50000000000000000000000000000000)⟩
def CA1_7_8I1R4MassTermLogWitness : LogWitness := ⟨-2, 5520910985132668912809379616577, 3125000000000000000000000000000⟩
def CA1_7_8I1R4MassTermLog : Ball := ⟨(-16343715281945216738606421677083 / 20000000000000000000000000000000), (15881867829 / 25000000000000000000000000000000)⟩
def CA1_7_8I1R4MassTerm : Ball := ⟨(9023219723797202219809978218521 / 25000000000000000000000000000000), (28058361237 / 100000000000000000000000000000000)⟩
def CA1_7_8I1R4H : Ball := ⟨(50162610752555337754037382097229 / 100000000000000000000000000000000), (16793530929 / 25000000000000000000000000000000)⟩
def CA1_7_8I1R5Entropy : Ball := ⟨(5673982395440393240329963033421 / 25000000000000000000000000000000), (35561743 / 400000000000000000000000000000)⟩
def CA1_7_8I1R5Mass : Ball := ⟨(284199226740662785783306515621 / 5000000000000000000000000000000), (17 / 50000000000000000000000000000000)⟩
def CA1_7_8I1R5MassTermLogWitness : LogWitness := ⟨-5, 284199226740662785783306515621, 156250000000000000000000000000⟩
def CA1_7_8I1R5MassTermLog : Ball := ⟨(-286751769658500763880690399379981 / 100000000000000000000000000000000), (15881867837 / 12500000000000000000000000000000)⟩
def CA1_7_8I1R5MassTerm : Ball := ⟨(3259785248138502638354366883571 / 20000000000000000000000000000000), (225680731 / 3125000000000000000000000000000)⟩
def CA1_7_8I1R5H : Ball := ⟨(6397003341069059769548017715829 / 100000000000000000000000000000000), (8056109571 / 50000000000000000000000000000000)⟩
def CA1_7_8I1R6Entropy : Ball := ⟨(1106104567343285851154954668061 / 100000000000000000000000000000000), (189349699 / 50000000000000000000000000000000)⟩
def CA1_7_8I1R6Mass : Ball := ⟨(148143051753858372411425144563 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def CA1_7_8I1R6MassTermLogWitness : LogWitness := ⟨-10, 148143051753858372411425144563, 97656250000000000000000000000⟩
def CA1_7_8I1R6MassTermLog : Ball := ⟨(-16286867730314255335605912195633 / 2500000000000000000000000000000), (116467032619 / 50000000000000000000000000000000)⟩
def CA1_7_8I1R6MassTerm : Ball := ⟨(482557257816038114612911050483 / 50000000000000000000000000000000), (345075679 / 100000000000000000000000000000000)⟩
def CA1_7_8I1R6H : Ball := ⟨(28198010342241924385826513419 / 20000000000000000000000000000000), (723775077 / 100000000000000000000000000000000)⟩
def CA1_7_8I1R7Entropy : Ball := ⟨(72128460287202064852396239 / 1000000000000000000000000000000), (1195341 / 50000000000000000000000000000000)⟩
def CA1_7_8I1R7Mass : Ball := ⟨(35279809335985405792837309 / 6250000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def CA1_7_8I1R7MassTermLogWitness : LogWitness := ⟨-18, 35279809335985405792837309, 23841857910156250000000000⟩
def CA1_7_8I1R7MassTermLog : Ball := ⟨(-1208478119489740070137408744055067 / 100000000000000000000000000000000), (402341004287 / 100000000000000000000000000000000)⟩
def CA1_7_8I1R7MassTerm : Ball := ⟨(6821580422769314960419141647 / 100000000000000000000000000000000), (2271147 / 100000000000000000000000000000000)⟩
def CA1_7_8I1R7H : Ball := ⟨(391265605950891524820482253 / 100000000000000000000000000000000), (4661829 / 100000000000000000000000000000000)⟩
def CA1_7_8I1R8Entropy : Ball := ⟨0, 0⟩
def CA1_7_8I1R8Mass : Ball := ⟨0, 0⟩
def CA1_7_8I1R8MassTerm : Ball := .exact 0
def CA1_7_8I1R8H : Ball := ⟨0, 0⟩
def CA1_7_8I1R9Entropy : Ball := ⟨0, 0⟩
def CA1_7_8I1R9Mass : Ball := ⟨0, 0⟩
def CA1_7_8I1R9MassTerm : Ball := .exact 0
def CA1_7_8I1R9H : Ball := ⟨0, 0⟩
def CA1_7_8I1R10Entropy : Ball := ⟨0, 0⟩
def CA1_7_8I1R10Mass : Ball := ⟨0, 0⟩
def CA1_7_8I1R10MassTerm : Ball := .exact 0
def CA1_7_8I1R10H : Ball := ⟨0, 0⟩
def CA1_7_8I1R11Entropy : Ball := ⟨0, 0⟩
def CA1_7_8I1R11Mass : Ball := ⟨0, 0⟩
def CA1_7_8I1R11MassTerm : Ball := .exact 0
def CA1_7_8I1R11H : Ball := ⟨0, 0⟩
def CA1_7_8I1R12Entropy : Ball := ⟨0, 0⟩
def CA1_7_8I1R12Mass : Ball := ⟨0, 0⟩
def CA1_7_8I1R12MassTerm : Ball := .exact 0
def CA1_7_8I1R12H : Ball := ⟨0, 0⟩
def CA1_7_8I1R13Entropy : Ball := ⟨0, 0⟩
def CA1_7_8I1R13Mass : Ball := ⟨0, 0⟩
def CA1_7_8I1R13MassTerm : Ball := .exact 0
def CA1_7_8I1R13H : Ball := ⟨0, 0⟩
def CA1_7_8I1R14Entropy : Ball := ⟨0, 0⟩
def CA1_7_8I1R14Mass : Ball := ⟨0, 0⟩
def CA1_7_8I1R14MassTerm : Ball := .exact 0
def CA1_7_8I1R14H : Ball := ⟨0, 0⟩
def CA1_7_8I1R15Entropy : Ball := ⟨0, 0⟩
def CA1_7_8I1R15Mass : Ball := ⟨0, 0⟩
def CA1_7_8I1R15MassTerm : Ball := .exact 0
def CA1_7_8I1R15H : Ball := ⟨0, 0⟩
def CA1_7_8I1R16Entropy : Ball := ⟨0, 0⟩
def CA1_7_8I1R16Mass : Ball := ⟨0, 0⟩
def CA1_7_8I1R16MassTerm : Ball := .exact 0
def CA1_7_8I1R16H : Ball := ⟨0, 0⟩
def CA1_7_8I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA1_7_8I1R0H
  | 1 => CA1_7_8I1R1H
  | 2 => CA1_7_8I1R2H
  | 3 => CA1_7_8I1R3H
  | 4 => CA1_7_8I1R4H
  | 5 => CA1_7_8I1R5H
  | 6 => CA1_7_8I1R6H
  | 7 => CA1_7_8I1R7H
  | 8 => CA1_7_8I1R8H
  | 9 => CA1_7_8I1R9H
  | 10 => CA1_7_8I1R10H
  | 11 => CA1_7_8I1R11H
  | 12 => CA1_7_8I1R12H
  | 13 => CA1_7_8I1R13H
  | 14 => CA1_7_8I1R14H
  | 15 => CA1_7_8I1R15H
  | 16 => CA1_7_8I1R16H
  | _ => (.exact 0)
def CA1_7_8I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 1, 7, 0 => Z1_7_0H1H
  | _, _, _ => (.exact 0)
def CA1_7_8I1Singleton : Ball := ⟨(13901359324341445694796469 / 100000000000000000000000000000000), (1699 / 20000000000000000000000000000000)⟩
def CA1_7_8I1Group : Ball := ⟨(28146986181848504264966179332283 / 25000000000000000000000000000000), (42415607743 / 25000000000000000000000000000000)⟩

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
def CA1_7_8I1H : Ball := ⟨(21344728096657900435901341739 / 20000000000000000000000000000), (97509509711 / 20000000000000000000000000000000)⟩

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
def CA1_7_8I2PairEntropy : Ball := ⟨(314337290010813783318900239035769 / 100000000000000000000000000000000), (2495419539 / 2000000000000000000000000000000)⟩
def CA1_7_8I2PairMass : Ball := ⟨(25000000000000000000000000000001 / 25000000000000000000000000000000), (7 / 1250000000000000000000000000000)⟩
def CA1_7_8I2PairMassTermLogWitness : LogWitness := ⟨0, 25000000000000000000000000000001, 25000000000000000000000000000000⟩
def CA1_7_8I2PairMassTermLog : Ball := ⟨(1 / 25000000000000000000000000000000), (10587912121 / 50000000000000000000000000000000)⟩
def CA1_7_8I2PairMassTerm : Ball := ⟨(-1 / 25000000000000000000000000000000), (21175824243 / 100000000000000000000000000000000)⟩
def CA1_7_8I2PairH : Ball := ⟨(314337290010813783318900239035773 / 100000000000000000000000000000000), (145946801193 / 100000000000000000000000000000000)⟩

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
def CA1_7_8I2R0Entropy : Ball := ⟨(154649177236918223514006467 / 50000000000000000000000000000000), (101943 / 100000000000000000000000000000000)⟩
def CA1_7_8I2R0Mass : Ball := ⟨(20055422158842954722213457 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def CA1_7_8I2R0MassTermLogWitness : LogWitness := ⟨-23, 20055422158842954722213457, 11920928955078125000000000⟩
def CA1_7_8I2R0MassTermLog : Ball := ⟨(-1542218119489740070137408646605969 / 100000000000000000000000000000000), (254112377287 / 50000000000000000000000000000000)⟩
def CA1_7_8I2R0MassTerm : Ball := ⟨(154649177236918223514006467 / 50000000000000000000000000000000), (101943 / 100000000000000000000000000000000)⟩
def CA1_7_8I2R0H : Ball := ⟨0, (101943 / 50000000000000000000000000000000)⟩
def CA1_7_8I2R1Entropy : Ball := ⟨(26491739363016102819996227157 / 50000000000000000000000000000000), (4499897 / 25000000000000000000000000000000)⟩
def CA1_7_8I2R1Mass : Ball := ⟨(500003178829468586018862723 / 10000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def CA1_7_8I2R1MassTermLogWitness : LogWitness := ⟨-15, 500003178829468586018862723, 305175781250000000000000000⟩
def CA1_7_8I2R1MassTermLog : Ball := ⟨(-990348119489740070137408801335397 / 100000000000000000000000000000000), (338813218927 / 100000000000000000000000000000000)⟩
def CA1_7_8I2R1MassTerm : Ball := ⟨(49517720789265642780224169709 / 100000000000000000000000000000000), (16940789 / 100000000000000000000000000000000)⟩
def CA1_7_8I2R1H : Ball := ⟨(693151587353312571953656921 / 20000000000000000000000000000000), (34940377 / 100000000000000000000000000000000)⟩
def CA1_7_8I2R2Entropy : Ball := ⟨(2022525741344877452754004889909 / 50000000000000000000000000000000), (1396080699 / 100000000000000000000000000000000)⟩
def CA1_7_8I2R2Mass : Ball := ⟨(167176461285217244558128668051 / 25000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
def CA1_7_8I2R2MassTermLogWitness : LogWitness := ⟨-8, 167176461285217244558128668051, 97656250000000000000000000000⟩
def CA1_7_8I2R2MassTermLog : Ball := ⟨(-500758119489740070137408935000643 / 100000000000000000000000000000000), (47645603623 / 25000000000000000000000000000000)⟩
def CA1_7_8I2R2MassTerm : Ball := ⟨(3348598815045388870657504831627 / 100000000000000000000000000000000), (1274435791 / 100000000000000000000000000000000)⟩
def CA1_7_8I2R2H : Ball := ⟨(696452667644366034850504948191 / 100000000000000000000000000000000), (267051649 / 10000000000000000000000000000000)⟩
def CA1_7_8I2R3Entropy : Ball := ⟨(1030449053430587347357906794773 / 2500000000000000000000000000000), (2224534579 / 12500000000000000000000000000000)⟩
def CA1_7_8I2R3Mass : Ball := ⟨(82217687460943370040910113989 / 625000000000000000000000000000), (9 / 25000000000000000000000000000000)⟩
def CA1_7_8I2R3MassTermLogWitness : LogWitness := ⟨-3, 82217687460943370040910113989, 78125000000000000000000000000⟩
def CA1_7_8I2R3MassTermLog : Ball := ⟨(-4056762389794801402748180609559 / 2000000000000000000000000000000), (16940659001 / 20000000000000000000000000000000)⟩
def CA1_7_8I2R3MassTerm : Ball := ⟨(26683009781396696269243426562597 / 100000000000000000000000000000000), (11142574531 / 100000000000000000000000000000000)⟩
def CA1_7_8I2R3H : Ball := ⟨(14534952355826797625072845228323 / 100000000000000000000000000000000), (28938851163 / 100000000000000000000000000000000)⟩
def CA1_7_8I2R4Entropy : Ball := ⟨(62423828562684647399044494369899 / 100000000000000000000000000000000), (3128203961 / 10000000000000000000000000000000)⟩
def CA1_7_8I2R4Mass : Ball := ⟨(49619932619696659353487069911 / 160000000000000000000000000000), (11 / 25000000000000000000000000000000)⟩
def CA1_7_8I2R4MassTermLogWitness : LogWitness := ⟨-2, 49619932619696659353487069911, 40000000000000000000000000000⟩
def CA1_7_8I2R4MassTermLog : Ball := ⟨(-117078119489740070137409049573447 / 100000000000000000000000000000000), (6352747119 / 10000000000000000000000000000000)⟩
def CA1_7_8I2R4MassTerm : Ball := ⟨(36308802502010603181711095923221 / 100000000000000000000000000000000), (9850715151 / 50000000000000000000000000000000)⟩
def CA1_7_8I2R4H : Ball := ⟨(13057513030337022108666699223339 / 50000000000000000000000000000000), (6372933739 / 12500000000000000000000000000000)⟩
def CA1_7_8I2R5Entropy : Ball := ⟨(2413727825233280014842162938431 / 12500000000000000000000000000000), (763676097 / 10000000000000000000000000000000)⟩
def CA1_7_8I2R5Mass : Ball := ⟨(626909836209048342179201955027 / 12500000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
def CA1_7_8I2R5MassTermLogWitness : LogWitness := ⟨-5, 626909836209048342179201955027, 390625000000000000000000000000⟩
def CA1_7_8I2R5MassTermLog : Ball := ⟨(-29926811948974007013740899228697 / 10000000000000000000000000000000), (15881867827 / 12500000000000000000000000000000)⟩
def CA1_7_8I2R5MassTerm : Ball := ⟨(3752282555438057105977780971651 / 25000000000000000000000000000000), (318607977 / 5000000000000000000000000000000)⟩
def CA1_7_8I2R5H : Ball := ⟨(1075173095028502923706544905211 / 25000000000000000000000000000000), (1400892051 / 10000000000000000000000000000000)⟩
def CA1_7_8I2R6Entropy : Ball := ⟨(476313614682939715205785232963 / 50000000000000000000000000000000), (337400967 / 100000000000000000000000000000000)⟩
def CA1_7_8I2R6Mass : Ball := ⟨(28628603993112737310247303467 / 20000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def CA1_7_8I2R6MassTermLogWitness : LogWitness := ⟨-10, 28628603993112737310247303467, 19531250000000000000000000000⟩
def CA1_7_8I2R6MassTermLog : Ball := ⟨(-163727029872435017534352224202163 / 25000000000000000000000000000000), (232934065403 / 100000000000000000000000000000000)⟩
def CA1_7_8I2R6MassTerm : Ball := ⟨(234363815059324078428978966481 / 25000000000000000000000000000000), (166714451 / 50000000000000000000000000000000)⟩
def CA1_7_8I2R6H : Ball := ⟨(7585984564291558347827300001 / 50000000000000000000000000000000), (670829869 / 100000000000000000000000000000000)⟩
def CA1_7_8I2R7Entropy : Ball := ⟨0, 0⟩
def CA1_7_8I2R7Mass : Ball := ⟨0, 0⟩
def CA1_7_8I2R7MassTerm : Ball := .exact 0
def CA1_7_8I2R7H : Ball := ⟨0, 0⟩
def CA1_7_8I2R8Entropy : Ball := ⟨0, 0⟩
def CA1_7_8I2R8Mass : Ball := ⟨0, 0⟩
def CA1_7_8I2R8MassTerm : Ball := .exact 0
def CA1_7_8I2R8H : Ball := ⟨0, 0⟩
def CA1_7_8I2R9Entropy : Ball := ⟨0, 0⟩
def CA1_7_8I2R9Mass : Ball := ⟨0, 0⟩
def CA1_7_8I2R9MassTerm : Ball := .exact 0
def CA1_7_8I2R9H : Ball := ⟨0, 0⟩
def CA1_7_8I2R10Entropy : Ball := ⟨0, 0⟩
def CA1_7_8I2R10Mass : Ball := ⟨0, 0⟩
def CA1_7_8I2R10MassTerm : Ball := .exact 0
def CA1_7_8I2R10H : Ball := ⟨0, 0⟩
def CA1_7_8I2R11Entropy : Ball := ⟨0, 0⟩
def CA1_7_8I2R11Mass : Ball := ⟨0, 0⟩
def CA1_7_8I2R11MassTerm : Ball := .exact 0
def CA1_7_8I2R11H : Ball := ⟨0, 0⟩
def CA1_7_8I2R12Entropy : Ball := ⟨0, 0⟩
def CA1_7_8I2R12Mass : Ball := ⟨0, 0⟩
def CA1_7_8I2R12MassTerm : Ball := .exact 0
def CA1_7_8I2R12H : Ball := ⟨0, 0⟩
def CA1_7_8I2R13Entropy : Ball := ⟨0, 0⟩
def CA1_7_8I2R13Mass : Ball := ⟨0, 0⟩
def CA1_7_8I2R13MassTerm : Ball := .exact 0
def CA1_7_8I2R13H : Ball := ⟨0, 0⟩
def CA1_7_8I2R14Entropy : Ball := ⟨0, 0⟩
def CA1_7_8I2R14Mass : Ball := ⟨0, 0⟩
def CA1_7_8I2R14MassTerm : Ball := .exact 0
def CA1_7_8I2R14H : Ball := ⟨0, 0⟩
def CA1_7_8I2R15Entropy : Ball := ⟨0, 0⟩
def CA1_7_8I2R15Mass : Ball := ⟨0, 0⟩
def CA1_7_8I2R15MassTerm : Ball := .exact 0
def CA1_7_8I2R15H : Ball := ⟨0, 0⟩
def CA1_7_8I2R16Entropy : Ball := ⟨0, 0⟩
def CA1_7_8I2R16Mass : Ball := ⟨0, 0⟩
def CA1_7_8I2R16MassTerm : Ball := .exact 0
def CA1_7_8I2R16H : Ball := ⟨0, 0⟩
def CA1_7_8I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA1_7_8I2R0H
  | 1 => CA1_7_8I2R1H
  | 2 => CA1_7_8I2R2H
  | 3 => CA1_7_8I2R3H
  | 4 => CA1_7_8I2R4H
  | 5 => CA1_7_8I2R5H
  | 6 => CA1_7_8I2R6H
  | 7 => CA1_7_8I2R7H
  | 8 => CA1_7_8I2R8H
  | 9 => CA1_7_8I2R9H
  | 10 => CA1_7_8I2R10H
  | 11 => CA1_7_8I2R11H
  | 12 => CA1_7_8I2R12H
  | 13 => CA1_7_8I2R13H
  | 14 => CA1_7_8I2R14H
  | 15 => CA1_7_8I2R15H
  | 16 => CA1_7_8I2R16H
  | _ => (.exact 0)
def CA1_7_8I2Singleton : Ball := ⟨(30157846868231622175255511891177 / 50000000000000000000000000000000), (50537614749 / 100000000000000000000000000000000)⟩
def CA1_7_8I2Group : Ball := ⟨(105981454927787813602149374910997 / 100000000000000000000000000000000), (36961336739 / 25000000000000000000000000000000)⟩

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
def CA1_7_8I2H : Ball := ⟨(102374380155238156114601489213779 / 100000000000000000000000000000000), (88327499021 / 20000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA2_2_12I0
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
def CA2_2_12I0Value (a : Fin 17) : ℝ := marginal (below (shape 2 2 12)) (fun u => (stageALaw (shape 2 2 12) u : ℝ)) ((Equiv.refl (Fin 3)) 0) a
def CA2_2_12I0Entropy : Ball := ⟨(26498888992335123891271129780063 / 25000000000000000000000000000000), (3176373593 / 5000000000000000000000000000000)⟩
def CA2_2_12I0Mass : Ball := ⟨(50000000000000000000000000000001 / 50000000000000000000000000000000), (383 / 100000000000000000000000000000000)⟩
def CA2_2_12I0MassTermLogWitness : LogWitness := ⟨0, 50000000000000000000000000000001, 50000000000000000000000000000000⟩
def CA2_2_12I0MassTermLog : Ball := ⟨(1 / 50000000000000000000000000000000), (4235164813 / 20000000000000000000000000000000)⟩
def CA2_2_12I0MassTerm : Ball := ⟨(-1 / 50000000000000000000000000000000), (10587912033 / 50000000000000000000000000000000)⟩
def CA2_2_12I0H : Ball := ⟨(52997777984670247782542259560127 / 50000000000000000000000000000000), (42351647963 / 50000000000000000000000000000000)⟩

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
def CA2_2_12I1PairEntropy : Ball := ⟨(56819327619563437864369567455811 / 25000000000000000000000000000000), (52335587181 / 50000000000000000000000000000000)⟩
def CA2_2_12I1PairMass : Ball := ⟨(25000000000000000000000000000001 / 25000000000000000000000000000000), (243 / 50000000000000000000000000000000)⟩
def CA2_2_12I1PairMassTermLogWitness : LogWitness := ⟨0, 25000000000000000000000000000001, 25000000000000000000000000000000⟩
def CA2_2_12I1PairMassTermLog : Ball := ⟨(1 / 25000000000000000000000000000000), (2646978021 / 12500000000000000000000000000000)⟩
def CA2_2_12I1PairMassTerm : Ball := ⟨(-1 / 25000000000000000000000000000000), (21175824169 / 100000000000000000000000000000000)⟩
def CA2_2_12I1PairH : Ball := ⟨(14204831904890859466092391863953 / 6250000000000000000000000000000), (125846998531 / 100000000000000000000000000000000)⟩

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
def CA2_2_12I1R0Entropy : Ball := ⟨(17611682793149662795593791067173 / 50000000000000000000000000000000), (1689454137 / 10000000000000000000000000000000)⟩
def CA2_2_12I1R0Mass : Ball := ⟨(3324258940959977818741615350511 / 12500000000000000000000000000000), (3 / 2500000000000000000000000000000)⟩
def CA2_2_12I1R0MassTermLogWitness : LogWitness := ⟨-2, 3324258940959977818741615350511, 3125000000000000000000000000000⟩
def CA2_2_12I1R0MassTermLog : Ball := ⟨(-132448186993999404944990127695899 / 100000000000000000000000000000000), (63527471499 / 100000000000000000000000000000000)⟩
def CA2_2_12I1R0MassTerm : Ball := ⟨(17611682793149662795593791067173 / 50000000000000000000000000000000), (1689454137 / 10000000000000000000000000000000)⟩
def CA2_2_12I1R0H : Ball := ⟨0, (1689454137 / 5000000000000000000000000000000)⟩
def CA2_2_12I1R1Entropy : Ball := ⟨(16994820460645649627923063019079 / 25000000000000000000000000000000), (19825592773 / 50000000000000000000000000000000)⟩
def CA2_2_12I1R1Mass : Ball := ⟨(23405928472320177450067077195913 / 50000000000000000000000000000000), (79 / 50000000000000000000000000000000)⟩
def CA2_2_12I1R1MassTermLogWitness : LogWitness := ⟨-2, 23405928472320177450067077195913, 12500000000000000000000000000000⟩
def CA2_2_12I1R1MassTermLog : Ball := ⟨(-37951683081755841051312027298827 / 50000000000000000000000000000000), (31763735693 / 50000000000000000000000000000000)⟩
def CA2_2_12I1R1MassTerm : Ball := ⟨(7106355036925928135440648095211 / 20000000000000000000000000000000), (14869194573 / 50000000000000000000000000000000)⟩
def CA2_2_12I1R1H : Ball := ⟨(32447506657952957834489011600261 / 100000000000000000000000000000000), (17347393673 / 25000000000000000000000000000000)⟩
def CA2_2_12I1R2Entropy : Ball := ⟨(7928157623607387194456062884167 / 12500000000000000000000000000000), (5510719237 / 20000000000000000000000000000000)⟩
def CA2_2_12I1R2Mass : Ball := ⟨(2659407152767982254993292280409 / 10000000000000000000000000000000), (157 / 100000000000000000000000000000000)⟩
def CA2_2_12I1R2MassTermLogWitness : LogWitness := ⟨-2, 2659407152767982254993292280409, 2500000000000000000000000000000⟩
def CA2_2_12I1R2MassTermLog : Ball := ⟨(-33112046748499851236247531923973 / 25000000000000000000000000000000), (63527471639 / 100000000000000000000000000000000)⟩
def CA2_2_12I1R2MassTerm : Ball := ⟨(35223365586299325591187582134347 / 100000000000000000000000000000000), (1055908841 / 6250000000000000000000000000000)⟩
def CA2_2_12I1R2H : Ball := ⟨(28201895402559771964460920938989 / 100000000000000000000000000000000), (44448137641 / 100000000000000000000000000000000)⟩
def CA2_2_12I1R3Entropy : Ball := ⟨0, 0⟩
def CA2_2_12I1R3Mass : Ball := ⟨0, 0⟩
def CA2_2_12I1R3MassTerm : Ball := .exact 0
def CA2_2_12I1R3H : Ball := ⟨0, 0⟩
def CA2_2_12I1R4Entropy : Ball := ⟨0, 0⟩
def CA2_2_12I1R4Mass : Ball := ⟨0, 0⟩
def CA2_2_12I1R4MassTerm : Ball := .exact 0
def CA2_2_12I1R4H : Ball := ⟨0, 0⟩
def CA2_2_12I1R5Entropy : Ball := ⟨0, 0⟩
def CA2_2_12I1R5Mass : Ball := ⟨0, 0⟩
def CA2_2_12I1R5MassTerm : Ball := .exact 0
def CA2_2_12I1R5H : Ball := ⟨0, 0⟩
def CA2_2_12I1R6Entropy : Ball := ⟨0, 0⟩
def CA2_2_12I1R6Mass : Ball := ⟨0, 0⟩
def CA2_2_12I1R6MassTerm : Ball := .exact 0
def CA2_2_12I1R6H : Ball := ⟨0, 0⟩
def CA2_2_12I1R7Entropy : Ball := ⟨0, 0⟩
def CA2_2_12I1R7Mass : Ball := ⟨0, 0⟩
def CA2_2_12I1R7MassTerm : Ball := .exact 0
def CA2_2_12I1R7H : Ball := ⟨0, 0⟩
def CA2_2_12I1R8Entropy : Ball := ⟨0, 0⟩
def CA2_2_12I1R8Mass : Ball := ⟨0, 0⟩
def CA2_2_12I1R8MassTerm : Ball := .exact 0
def CA2_2_12I1R8H : Ball := ⟨0, 0⟩
def CA2_2_12I1R9Entropy : Ball := ⟨0, 0⟩
def CA2_2_12I1R9Mass : Ball := ⟨0, 0⟩
def CA2_2_12I1R9MassTerm : Ball := .exact 0
def CA2_2_12I1R9H : Ball := ⟨0, 0⟩
def CA2_2_12I1R10Entropy : Ball := ⟨0, 0⟩
def CA2_2_12I1R10Mass : Ball := ⟨0, 0⟩
def CA2_2_12I1R10MassTerm : Ball := .exact 0
def CA2_2_12I1R10H : Ball := ⟨0, 0⟩
def CA2_2_12I1R11Entropy : Ball := ⟨0, 0⟩
def CA2_2_12I1R11Mass : Ball := ⟨0, 0⟩
def CA2_2_12I1R11MassTerm : Ball := .exact 0
def CA2_2_12I1R11H : Ball := ⟨0, 0⟩
def CA2_2_12I1R12Entropy : Ball := ⟨0, 0⟩
def CA2_2_12I1R12Mass : Ball := ⟨0, 0⟩
def CA2_2_12I1R12MassTerm : Ball := .exact 0
def CA2_2_12I1R12H : Ball := ⟨0, 0⟩
def CA2_2_12I1R13Entropy : Ball := ⟨0, 0⟩
def CA2_2_12I1R13Mass : Ball := ⟨0, 0⟩
def CA2_2_12I1R13MassTerm : Ball := .exact 0
def CA2_2_12I1R13H : Ball := ⟨0, 0⟩
def CA2_2_12I1R14Entropy : Ball := ⟨0, 0⟩
def CA2_2_12I1R14Mass : Ball := ⟨0, 0⟩
def CA2_2_12I1R14MassTerm : Ball := .exact 0
def CA2_2_12I1R14H : Ball := ⟨0, 0⟩
def CA2_2_12I1R15Entropy : Ball := ⟨0, 0⟩
def CA2_2_12I1R15Mass : Ball := ⟨0, 0⟩
def CA2_2_12I1R15MassTerm : Ball := .exact 0
def CA2_2_12I1R15H : Ball := ⟨0, 0⟩
def CA2_2_12I1R16Entropy : Ball := ⟨0, 0⟩
def CA2_2_12I1R16Mass : Ball := ⟨0, 0⟩
def CA2_2_12I1R16MassTerm : Ball := .exact 0
def CA2_2_12I1R16H : Ball := ⟨0, 0⟩
def CA2_2_12I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA2_2_12I1R0H
  | 1 => CA2_2_12I1R1H
  | 2 => CA2_2_12I1R2H
  | 3 => CA2_2_12I1R3H
  | 4 => CA2_2_12I1R4H
  | 5 => CA2_2_12I1R5H
  | 6 => CA2_2_12I1R6H
  | 7 => CA2_2_12I1R7H
  | 8 => CA2_2_12I1R8H
  | 9 => CA2_2_12I1R9H
  | 10 => CA2_2_12I1R10H
  | 11 => CA2_2_12I1R11H
  | 12 => CA2_2_12I1R12H
  | 13 => CA2_2_12I1R13H
  | 14 => CA2_2_12I1R14H
  | 15 => CA2_2_12I1R15H
  | 16 => CA2_2_12I1R16H
  | _ => (.exact 0)
def CA2_2_12I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | _, _, _ => (.exact 0)
def CA2_2_12I1Singleton : Ball := ⟨0, 0⟩
def CA2_2_12I1Group : Ball := ⟨(242597608242050919195799730157 / 400000000000000000000000000000), (147626795073 / 100000000000000000000000000000000)⟩

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
def CA2_2_12I1H : Ball := ⟨(26494626589307072964894601186187 / 25000000000000000000000000000000), (421100588677 / 100000000000000000000000000000000)⟩

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
def CA2_2_12I2PairEntropy : Ball := ⟨(256092058421150692005924592852231 / 100000000000000000000000000000000), (111067525547 / 100000000000000000000000000000000)⟩
def CA2_2_12I2PairMass : Ball := ⟨(10000000000000000000000000000001 / 10000000000000000000000000000000), (139 / 25000000000000000000000000000000)⟩
def CA2_2_12I2PairMassTermLogWitness : LogWitness := ⟨0, 10000000000000000000000000000001, 10000000000000000000000000000000⟩
def CA2_2_12I2PairMassTermLog : Ball := ⟨(1 / 10000000000000000000000000000000), (10587912119 / 50000000000000000000000000000000)⟩
def CA2_2_12I2PairMassTerm : Ball := ⟨(-1 / 10000000000000000000000000000000), (21175824239 / 100000000000000000000000000000000)⟩
def CA2_2_12I2PairH : Ball := ⟨(256092058421150692005924592852241 / 100000000000000000000000000000000), (66121674893 / 50000000000000000000000000000000)⟩

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
def CA2_2_12I2R0Entropy : Ball := ⟨0, 0⟩
def CA2_2_12I2R0Mass : Ball := ⟨0, 0⟩
def CA2_2_12I2R0MassTerm : Ball := .exact 0
def CA2_2_12I2R0H : Ball := ⟨0, 0⟩
def CA2_2_12I2R1Entropy : Ball := ⟨0, 0⟩
def CA2_2_12I2R1Mass : Ball := ⟨0, 0⟩
def CA2_2_12I2R1MassTerm : Ball := .exact 0
def CA2_2_12I2R1H : Ball := ⟨0, 0⟩
def CA2_2_12I2R2Entropy : Ball := ⟨0, 0⟩
def CA2_2_12I2R2Mass : Ball := ⟨0, 0⟩
def CA2_2_12I2R2MassTerm : Ball := .exact 0
def CA2_2_12I2R2H : Ball := ⟨0, 0⟩
def CA2_2_12I2R3Entropy : Ball := ⟨0, 0⟩
def CA2_2_12I2R3Mass : Ball := ⟨0, 0⟩
def CA2_2_12I2R3MassTerm : Ball := .exact 0
def CA2_2_12I2R3H : Ball := ⟨0, 0⟩
def CA2_2_12I2R4Entropy : Ball := ⟨(3054368996686146513333569336029 / 100000000000000000000000000000000), (566749539 / 50000000000000000000000000000000)⟩
def CA2_2_12I2R4Mass : Ball := ⟨(124653160281836571338746140581 / 25000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
def CA2_2_12I2R4MassTermLogWitness : LogWitness := ⟨-8, 124653160281836571338746140581, 97656250000000000000000000000⟩
def CA2_2_12I2R4MassTermLog : Ball := ⟨(-530109594095838382374500639063209 / 100000000000000000000000000000000), (190582415353 / 100000000000000000000000000000000)⟩
def CA2_2_12I2R4MassTerm : Ball := ⟨(82599795249709834557519152781 / 3125000000000000000000000000000), (475134037 / 50000000000000000000000000000000)⟩
def CA2_2_12I2R4H : Ball := ⟨(411175548695431807492956447037 / 100000000000000000000000000000000), (130235447 / 6250000000000000000000000000000)⟩
def CA2_2_12I2R5Entropy : Ball := ⟨(24790632070256076154358483242849 / 50000000000000000000000000000000), (2767290111 / 12500000000000000000000000000000)⟩
def CA2_2_12I2R5Mass : Ball := ⟨(10061583182340158060849646345017 / 50000000000000000000000000000000), (29 / 25000000000000000000000000000000)⟩
def CA2_2_12I2R5MassTermLogWitness : LogWitness := ⟨-3, 10061583182340158060849646345017, 6250000000000000000000000000000⟩
def CA2_2_12I2R5MassTermLog : Ball := ⟨(-16032984791484648815113201465007 / 10000000000000000000000000000000), (21175823827 / 25000000000000000000000000000000)⟩
def CA2_2_12I2R5MassTerm : Ball := ⟨(8065860507035873417281125243751 / 25000000000000000000000000000000), (8522492609 / 50000000000000000000000000000000)⟩
def CA2_2_12I2R5H : Ball := ⟨(8658911056184329319796232755347 / 50000000000000000000000000000000), (19591653053 / 50000000000000000000000000000000)⟩
def CA2_2_12I2R6Entropy : Ball := ⟨(38076231241309777540719444269209 / 100000000000000000000000000000000), (8842609181 / 50000000000000000000000000000000)⟩
def CA2_2_12I2R6Mass : Ball := ⟨(13336799104008174087333670447257 / 50000000000000000000000000000000), (29 / 50000000000000000000000000000000)⟩
def CA2_2_12I2R6MassTermLogWitness : LogWitness := ⟨-2, 13336799104008174087333670447257, 12500000000000000000000000000000⟩
def CA2_2_12I2R6MassTermLog : Ball := ⟨(-66074797047919191187250376818187 / 50000000000000000000000000000000), (31763735633 / 50000000000000000000000000000000)⟩
def CA2_2_12I2R6MassTerm : Ball := ⟨(1101532867582763269065187204367 / 3125000000000000000000000000000), (3389012503 / 20000000000000000000000000000000)⟩
def CA2_2_12I2R6H : Ball := ⟨(565435895732270586126690745893 / 20000000000000000000000000000000), (34630280877 / 100000000000000000000000000000000)⟩
def CA2_2_12I2R7Entropy : Ball := ⟨0, 0⟩
def CA2_2_12I2R7Mass : Ball := ⟨0, 0⟩
def CA2_2_12I2R7MassTerm : Ball := .exact 0
def CA2_2_12I2R7H : Ball := ⟨0, 0⟩
def CA2_2_12I2R8Entropy : Ball := ⟨0, 0⟩
def CA2_2_12I2R8Mass : Ball := ⟨0, 0⟩
def CA2_2_12I2R8MassTerm : Ball := .exact 0
def CA2_2_12I2R8H : Ball := ⟨0, 0⟩
def CA2_2_12I2R9Entropy : Ball := ⟨0, 0⟩
def CA2_2_12I2R9Mass : Ball := ⟨0, 0⟩
def CA2_2_12I2R9MassTerm : Ball := .exact 0
def CA2_2_12I2R9H : Ball := ⟨0, 0⟩
def CA2_2_12I2R10Entropy : Ball := ⟨0, 0⟩
def CA2_2_12I2R10Mass : Ball := ⟨0, 0⟩
def CA2_2_12I2R10MassTerm : Ball := .exact 0
def CA2_2_12I2R10H : Ball := ⟨0, 0⟩
def CA2_2_12I2R11Entropy : Ball := ⟨0, 0⟩
def CA2_2_12I2R11Mass : Ball := ⟨0, 0⟩
def CA2_2_12I2R11MassTerm : Ball := .exact 0
def CA2_2_12I2R11H : Ball := ⟨0, 0⟩
def CA2_2_12I2R12Entropy : Ball := ⟨0, 0⟩
def CA2_2_12I2R12Mass : Ball := ⟨0, 0⟩
def CA2_2_12I2R12MassTerm : Ball := .exact 0
def CA2_2_12I2R12H : Ball := ⟨0, 0⟩
def CA2_2_12I2R13Entropy : Ball := ⟨0, 0⟩
def CA2_2_12I2R13Mass : Ball := ⟨0, 0⟩
def CA2_2_12I2R13MassTerm : Ball := .exact 0
def CA2_2_12I2R13H : Ball := ⟨0, 0⟩
def CA2_2_12I2R14Entropy : Ball := ⟨0, 0⟩
def CA2_2_12I2R14Mass : Ball := ⟨0, 0⟩
def CA2_2_12I2R14MassTerm : Ball := .exact 0
def CA2_2_12I2R14H : Ball := ⟨0, 0⟩
def CA2_2_12I2R15Entropy : Ball := ⟨0, 0⟩
def CA2_2_12I2R15Mass : Ball := ⟨0, 0⟩
def CA2_2_12I2R15MassTerm : Ball := .exact 0
def CA2_2_12I2R15H : Ball := ⟨0, 0⟩
def CA2_2_12I2R16Entropy : Ball := ⟨0, 0⟩
def CA2_2_12I2R16Mass : Ball := ⟨0, 0⟩
def CA2_2_12I2R16MassTerm : Ball := .exact 0
def CA2_2_12I2R16H : Ball := ⟨0, 0⟩
def CA2_2_12I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA2_2_12I2R0H
  | 1 => CA2_2_12I2R1H
  | 2 => CA2_2_12I2R2H
  | 3 => CA2_2_12I2R3H
  | 4 => CA2_2_12I2R4H
  | 5 => CA2_2_12I2R5H
  | 6 => CA2_2_12I2R6H
  | 7 => CA2_2_12I2R7H
  | 8 => CA2_2_12I2R8H
  | 9 => CA2_2_12I2R9H
  | 10 => CA2_2_12I2R10H
  | 11 => CA2_2_12I2R11H
  | 12 => CA2_2_12I2R12H
  | 13 => CA2_2_12I2R13H
  | 14 => CA2_2_12I2R14H
  | 15 => CA2_2_12I2R15H
  | 16 => CA2_2_12I2R16H
  | _ => (.exact 0)
def CA2_2_12I2Singleton : Ball := ⟨(49295386069855886010487108668437 / 100000000000000000000000000000000), (9719736623 / 25000000000000000000000000000000)⟩
def CA2_2_12I2Group : Ball := ⟨(69851563209581329388205984355633 / 100000000000000000000000000000000), (114776300627 / 100000000000000000000000000000000)⟩

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
def CA2_2_12I2H : Ball := ⟨(4655557280079521329180504965639 / 4000000000000000000000000000000), (1130612347 / 312500000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA2_3_11I0
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
def CA2_3_11I0Value (a : Fin 17) : ℝ := marginal (below (shape 2 3 11)) (fun u => (stageALaw (shape 2 3 11) u : ℝ)) ((Equiv.refl (Fin 3)) 0) a
def CA2_3_11I0Entropy : Ball := ⟨(2118188484701215442097066153019 / 2000000000000000000000000000000), (31763735773 / 50000000000000000000000000000000)⟩
def CA2_3_11I0Mass : Ball := ⟨1, (23 / 10000000000000000000000000000000)⟩
def CA2_3_11I0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CA2_3_11I0MassTermLog : Ball := ⟨0, (2646977989 / 12500000000000000000000000000000)⟩
def CA2_3_11I0MassTerm : Ball := ⟨0, (21175823913 / 100000000000000000000000000000000)⟩
def CA2_3_11I0H : Ball := ⟨(2118188484701215442097066153019 / 2000000000000000000000000000000), (84703295459 / 100000000000000000000000000000000)⟩

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
def CA2_3_11I1PairEntropy : Ball := ⟨(8837967053621728608536788985853 / 3125000000000000000000000000000), (30248726329 / 25000000000000000000000000000000)⟩
def CA2_3_11I1PairMass : Ball := ⟨(24999999999999999999999999999999 / 25000000000000000000000000000000), (103 / 25000000000000000000000000000000)⟩
def CA2_3_11I1PairMassTermLogWitness : LogWitness := ⟨-1, 24999999999999999999999999999999, 12500000000000000000000000000000⟩
def CA2_3_11I1PairMassTermLog : Ball := ⟨(-1 / 25000000000000000000000000000000), (21175823889 / 50000000000000000000000000000000)⟩
def CA2_3_11I1PairMassTerm : Ball := ⟨(1 / 25000000000000000000000000000000), (42351647779 / 100000000000000000000000000000000)⟩
def CA2_3_11I1PairH : Ball := ⟨(70703736428973828868294311886823 / 25000000000000000000000000000000), (32669310619 / 20000000000000000000000000000000)⟩

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
def CA2_3_11I1R0Entropy : Ball := ⟨(23624338930499515612716987850007 / 100000000000000000000000000000000), (5541570939 / 50000000000000000000000000000000)⟩
def CA2_3_11I1R0Mass : Ball := ⟨(2616932853915287520550304835637 / 25000000000000000000000000000000), (21 / 50000000000000000000000000000000)⟩
def CA2_3_11I1R0MassTermLogWitness : LogWitness := ⟨-4, 2616932853915287520550304835637, 1562500000000000000000000000000⟩
def CA2_3_11I1R0MassTermLog : Ball := ⟨(-225687285930495800137701698295113 / 100000000000000000000000000000000), (3308722463 / 3125000000000000000000000000000)⟩
def CA2_3_11I1R0MassTerm : Ball := ⟨(23624338930499515612716987850007 / 100000000000000000000000000000000), (5541570939 / 50000000000000000000000000000000)⟩
def CA2_3_11I1R0H : Ball := ⟨0, (5541570939 / 25000000000000000000000000000000)⟩
def CA2_3_11I1R1Entropy : Ball := ⟨(32044858929775539194174820947917 / 50000000000000000000000000000000), (4185641777 / 12500000000000000000000000000000)⟩
def CA2_3_11I1R1Mass : Ball := ⟨(9883067146084712479449695164363 / 25000000000000000000000000000000), (23 / 25000000000000000000000000000000)⟩
def CA2_3_11I1R1MassTermLogWitness : LogWitness := ⟨-2, 9883067146084712479449695164363, 6250000000000000000000000000000⟩
def CA2_3_11I1R1MassTermLog : Ball := ⟨(-9280529213977990659811937343419 / 10000000000000000000000000000000), (63527471281 / 100000000000000000000000000000000)⟩
def CA2_3_11I1R1MassTerm : Ball := ⟨(36688037349178104038961450659137 / 100000000000000000000000000000000), (12556925329 / 50000000000000000000000000000000)⟩
def CA2_3_11I1R1H : Ball := ⟨(27401680510372974349388191236697 / 100000000000000000000000000000000), (29299492437 / 50000000000000000000000000000000)⟩
def CA2_3_11I1R2Entropy : Ball := ⟨(78143527007801442452510568547531 / 100000000000000000000000000000000), (37844965177 / 100000000000000000000000000000000)⟩
def CA2_3_11I1R2Mass : Ball := ⟨(9883067146084712479449695164363 / 25000000000000000000000000000000), (63 / 50000000000000000000000000000000)⟩
def CA2_3_11I1R2MassTermLogWitness : LogWitness := ⟨-2, 9883067146084712479449695164363, 6250000000000000000000000000000⟩
def CA2_3_11I1R2MassTermLog : Ball := ⟨(-9280529213977990659811937343419 / 10000000000000000000000000000000), (63527471367 / 100000000000000000000000000000000)⟩
def CA2_3_11I1R2MassTerm : Ball := ⟨(36688037349178104038961450659137 / 100000000000000000000000000000000), (25113850723 / 100000000000000000000000000000000)⟩
def CA2_3_11I1R2H : Ball := ⟨(20727744829311669206774558944197 / 50000000000000000000000000000000), (629588159 / 1000000000000000000000000000000)⟩
def CA2_3_11I1R3Entropy : Ball := ⟨(3586226533977324093468986398943 / 10000000000000000000000000000000), (7140601921 / 50000000000000000000000000000000)⟩
def CA2_3_11I1R3Mass : Ball := ⟨(2616932853915287520550304835637 / 25000000000000000000000000000000), (1 / 1562500000000000000000000000000)⟩
def CA2_3_11I1R3MassTermLogWitness : LogWitness := ⟨-4, 2616932853915287520550304835637, 1562500000000000000000000000000⟩
def CA2_3_11I1R3MassTermLog : Ball := ⟨(-225687285930495800137701698295113 / 100000000000000000000000000000000), (52939559513 / 50000000000000000000000000000000)⟩
def CA2_3_11I1R3MassTerm : Ball := ⟨(23624338930499515612716987850007 / 100000000000000000000000000000000), (221662839 / 2000000000000000000000000000000)⟩
def CA2_3_11I1R3H : Ball := ⟨(12237926409273725321972876139423 / 100000000000000000000000000000000), (396317903 / 1562500000000000000000000000000)⟩
def CA2_3_11I1R4Entropy : Ball := ⟨0, 0⟩
def CA2_3_11I1R4Mass : Ball := ⟨0, 0⟩
def CA2_3_11I1R4MassTerm : Ball := .exact 0
def CA2_3_11I1R4H : Ball := ⟨0, 0⟩
def CA2_3_11I1R5Entropy : Ball := ⟨0, 0⟩
def CA2_3_11I1R5Mass : Ball := ⟨0, 0⟩
def CA2_3_11I1R5MassTerm : Ball := .exact 0
def CA2_3_11I1R5H : Ball := ⟨0, 0⟩
def CA2_3_11I1R6Entropy : Ball := ⟨0, 0⟩
def CA2_3_11I1R6Mass : Ball := ⟨0, 0⟩
def CA2_3_11I1R6MassTerm : Ball := .exact 0
def CA2_3_11I1R6H : Ball := ⟨0, 0⟩
def CA2_3_11I1R7Entropy : Ball := ⟨0, 0⟩
def CA2_3_11I1R7Mass : Ball := ⟨0, 0⟩
def CA2_3_11I1R7MassTerm : Ball := .exact 0
def CA2_3_11I1R7H : Ball := ⟨0, 0⟩
def CA2_3_11I1R8Entropy : Ball := ⟨0, 0⟩
def CA2_3_11I1R8Mass : Ball := ⟨0, 0⟩
def CA2_3_11I1R8MassTerm : Ball := .exact 0
def CA2_3_11I1R8H : Ball := ⟨0, 0⟩
def CA2_3_11I1R9Entropy : Ball := ⟨0, 0⟩
def CA2_3_11I1R9Mass : Ball := ⟨0, 0⟩
def CA2_3_11I1R9MassTerm : Ball := .exact 0
def CA2_3_11I1R9H : Ball := ⟨0, 0⟩
def CA2_3_11I1R10Entropy : Ball := ⟨0, 0⟩
def CA2_3_11I1R10Mass : Ball := ⟨0, 0⟩
def CA2_3_11I1R10MassTerm : Ball := .exact 0
def CA2_3_11I1R10H : Ball := ⟨0, 0⟩
def CA2_3_11I1R11Entropy : Ball := ⟨0, 0⟩
def CA2_3_11I1R11Mass : Ball := ⟨0, 0⟩
def CA2_3_11I1R11MassTerm : Ball := .exact 0
def CA2_3_11I1R11H : Ball := ⟨0, 0⟩
def CA2_3_11I1R12Entropy : Ball := ⟨0, 0⟩
def CA2_3_11I1R12Mass : Ball := ⟨0, 0⟩
def CA2_3_11I1R12MassTerm : Ball := .exact 0
def CA2_3_11I1R12H : Ball := ⟨0, 0⟩
def CA2_3_11I1R13Entropy : Ball := ⟨0, 0⟩
def CA2_3_11I1R13Mass : Ball := ⟨0, 0⟩
def CA2_3_11I1R13MassTerm : Ball := .exact 0
def CA2_3_11I1R13H : Ball := ⟨0, 0⟩
def CA2_3_11I1R14Entropy : Ball := ⟨0, 0⟩
def CA2_3_11I1R14Mass : Ball := ⟨0, 0⟩
def CA2_3_11I1R14MassTerm : Ball := .exact 0
def CA2_3_11I1R14H : Ball := ⟨0, 0⟩
def CA2_3_11I1R15Entropy : Ball := ⟨0, 0⟩
def CA2_3_11I1R15Mass : Ball := ⟨0, 0⟩
def CA2_3_11I1R15MassTerm : Ball := .exact 0
def CA2_3_11I1R15H : Ball := ⟨0, 0⟩
def CA2_3_11I1R16Entropy : Ball := ⟨0, 0⟩
def CA2_3_11I1R16Mass : Ball := ⟨0, 0⟩
def CA2_3_11I1R16MassTerm : Ball := .exact 0
def CA2_3_11I1R16H : Ball := ⟨0, 0⟩
def CA2_3_11I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA2_3_11I1R0H
  | 1 => CA2_3_11I1R1H
  | 2 => CA2_3_11I1R2H
  | 3 => CA2_3_11I1R3H
  | 4 => CA2_3_11I1R4H
  | 5 => CA2_3_11I1R5H
  | 6 => CA2_3_11I1R6H
  | 7 => CA2_3_11I1R7H
  | 8 => CA2_3_11I1R8H
  | 9 => CA2_3_11I1R9H
  | 10 => CA2_3_11I1R10H
  | 11 => CA2_3_11I1R11H
  | 12 => CA2_3_11I1R12H
  | 13 => CA2_3_11I1R13H
  | 14 => CA2_3_11I1R14H
  | 15 => CA2_3_11I1R15H
  | 16 => CA2_3_11I1R16H
  | _ => (.exact 0)
def CA2_3_11I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | _, _, _ => (.exact 0)
def CA2_3_11I1Singleton : Ball := ⟨0, 0⟩
def CA2_3_11I1Group : Ball := ⟨(40547548289135019042455092632257 / 50000000000000000000000000000000), (84544215161 / 50000000000000000000000000000000)⟩

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
def CA2_3_11I1H : Ball := ⟨(15078094069919404912919609627283 / 12500000000000000000000000000000), (501523413739 / 100000000000000000000000000000000)⟩

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
def CA2_3_11I2PairEntropy : Ball := ⟨(34186993952125239895041733853741 / 12500000000000000000000000000000), (3551715743 / 3125000000000000000000000000000)⟩
def CA2_3_11I2PairMass : Ball := ⟨(12500000000000000000000000000001 / 12500000000000000000000000000000), (31 / 6250000000000000000000000000000)⟩
def CA2_3_11I2PairMassTermLogWitness : LogWitness := ⟨0, 12500000000000000000000000000001, 12500000000000000000000000000000⟩
def CA2_3_11I2PairMassTermLog : Ball := ⟨(1 / 12500000000000000000000000000000), (10587912089 / 50000000000000000000000000000000)⟩
def CA2_3_11I2PairMassTerm : Ball := ⟨(-1 / 12500000000000000000000000000000), (21175824179 / 100000000000000000000000000000000)⟩
def CA2_3_11I2PairH : Ball := ⟨(17093496976062619947520866926871 / 6250000000000000000000000000000), (26966145591 / 20000000000000000000000000000000)⟩

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
def CA2_3_11I2R0Entropy : Ball := ⟨0, 0⟩
def CA2_3_11I2R0Mass : Ball := ⟨0, 0⟩
def CA2_3_11I2R0MassTerm : Ball := .exact 0
def CA2_3_11I2R0H : Ball := ⟨0, 0⟩
def CA2_3_11I2R1Entropy : Ball := ⟨0, 0⟩
def CA2_3_11I2R1Mass : Ball := ⟨0, 0⟩
def CA2_3_11I2R1MassTerm : Ball := .exact 0
def CA2_3_11I2R1H : Ball := ⟨0, 0⟩
def CA2_3_11I2R2Entropy : Ball := ⟨0, 0⟩
def CA2_3_11I2R2Mass : Ball := ⟨0, 0⟩
def CA2_3_11I2R2MassTerm : Ball := .exact 0
def CA2_3_11I2R2H : Ball := ⟨0, 0⟩
def CA2_3_11I2R3Entropy : Ball := ⟨(173058558568175476025596635617 / 50000000000000000000000000000000), (59337813 / 50000000000000000000000000000000)⟩
def CA2_3_11I2R3Mass : Ball := ⟨(3920521960453472358068863817 / 10000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def CA2_3_11I2R3MassTermLogWitness : LogWitness := ⟨-12, 3920521960453472358068863817, 2441406250000000000000000000⟩
def CA2_3_11I2R3MassTermLog : Ball := ⟨(-392205778693050138276878830221161 / 50000000000000000000000000000000), (275285723183 / 100000000000000000000000000000000)⟩
def CA2_3_11I2R3MassTerm : Ball := ⟨(153765136838285764580771240553 / 50000000000000000000000000000000), (5396321 / 5000000000000000000000000000000)⟩
def CA2_3_11I2R3H : Ball := ⟨(2411677716236213930603174383 / 6250000000000000000000000000000), (113301023 / 50000000000000000000000000000000)⟩
def CA2_3_11I2R4Entropy : Ball := ⟨(21001169407240103265116354711751 / 100000000000000000000000000000000), (1621509709 / 20000000000000000000000000000000)⟩
def CA2_3_11I2R4Mass : Ball := ⟨(5671267703747874110785818097211 / 100000000000000000000000000000000), (1 / 2500000000000000000000000000000)⟩
def CA2_3_11I2R4MassTermLogWitness : LogWitness := ⟨-5, 5671267703747874110785818097211, 3125000000000000000000000000000⟩
def CA2_3_11I2R4MassTermLog : Ball := ⟨(-286975751233100269100320826215251 / 100000000000000000000000000000000), (127054942803 / 100000000000000000000000000000000)⟩
def CA2_3_11I2R4MassTerm : Ball := ⟨(16275163097270657154798053737267 / 100000000000000000000000000000000), (7205626053 / 100000000000000000000000000000000)⟩
def CA2_3_11I2R4H : Ball := ⟨(1181501577492361527579575243621 / 25000000000000000000000000000000), (7656587299 / 50000000000000000000000000000000)⟩
def CA2_3_11I2R5Entropy : Ball := ⟨(33985462014153292895160479225641 / 50000000000000000000000000000000), (1610344993 / 5000000000000000000000000000000)⟩
def CA2_3_11I2R5Mass : Ball := ⟨(18129883648590987898761899411443 / 50000000000000000000000000000000), (51 / 50000000000000000000000000000000)⟩
def CA2_3_11I2R5MassTermLogWitness : LogWitness := ⟨-2, 18129883648590987898761899411443, 12500000000000000000000000000000⟩
def CA2_3_11I2R5MassTermLog : Ball := ⟨(-101446139829968549672529265203349 / 100000000000000000000000000000000), (6352747133 / 10000000000000000000000000000000)⟩
def CA2_3_11I2R5MassTerm : Ball := ⟨(36784134234320435001557660496367 / 100000000000000000000000000000000), (11517456689 / 50000000000000000000000000000000)⟩
def CA2_3_11I2R5H : Ball := ⟨(6237357958797230157752659590983 / 20000000000000000000000000000000), (27620906619 / 50000000000000000000000000000000)⟩
def CA2_3_11I2R6Entropy : Ball := ⟨(35044639855695036985622783937181 / 100000000000000000000000000000000), (9173190411 / 50000000000000000000000000000000)⟩
def CA2_3_11I2R6Mass : Ball := ⟨(21067985473744271817281816227921 / 100000000000000000000000000000000), (1 / 3125000000000000000000000000000)⟩
def CA2_3_11I2R6MassTermLogWitness : LogWitness := ⟨-3, 21067985473744271817281816227921, 12500000000000000000000000000000⟩
def CA2_3_11I2R6MassTermLog : Ball := ⟨(-7787077869305013827687891615047 / 5000000000000000000000000000000), (84703294883 / 100000000000000000000000000000000)⟩
def CA2_3_11I2R6MassTerm : Ball := ⟨(32811608686686705304979056360841 / 100000000000000000000000000000000), (2230659739 / 12500000000000000000000000000000)⟩
def CA2_3_11I2R6H : Ball := ⟨(111651558450416584032186378817 / 5000000000000000000000000000000), (18095829367 / 50000000000000000000000000000000)⟩
def CA2_3_11I2R7Entropy : Ball := ⟨0, 0⟩
def CA2_3_11I2R7Mass : Ball := ⟨0, 0⟩
def CA2_3_11I2R7MassTerm : Ball := .exact 0
def CA2_3_11I2R7H : Ball := ⟨0, 0⟩
def CA2_3_11I2R8Entropy : Ball := ⟨0, 0⟩
def CA2_3_11I2R8Mass : Ball := ⟨0, 0⟩
def CA2_3_11I2R8MassTerm : Ball := .exact 0
def CA2_3_11I2R8H : Ball := ⟨0, 0⟩
def CA2_3_11I2R9Entropy : Ball := ⟨0, 0⟩
def CA2_3_11I2R9Mass : Ball := ⟨0, 0⟩
def CA2_3_11I2R9MassTerm : Ball := .exact 0
def CA2_3_11I2R9H : Ball := ⟨0, 0⟩
def CA2_3_11I2R10Entropy : Ball := ⟨0, 0⟩
def CA2_3_11I2R10Mass : Ball := ⟨0, 0⟩
def CA2_3_11I2R10MassTerm : Ball := .exact 0
def CA2_3_11I2R10H : Ball := ⟨0, 0⟩
def CA2_3_11I2R11Entropy : Ball := ⟨0, 0⟩
def CA2_3_11I2R11Mass : Ball := ⟨0, 0⟩
def CA2_3_11I2R11MassTerm : Ball := .exact 0
def CA2_3_11I2R11H : Ball := ⟨0, 0⟩
def CA2_3_11I2R12Entropy : Ball := ⟨0, 0⟩
def CA2_3_11I2R12Mass : Ball := ⟨0, 0⟩
def CA2_3_11I2R12MassTerm : Ball := .exact 0
def CA2_3_11I2R12H : Ball := ⟨0, 0⟩
def CA2_3_11I2R13Entropy : Ball := ⟨0, 0⟩
def CA2_3_11I2R13Mass : Ball := ⟨0, 0⟩
def CA2_3_11I2R13MassTerm : Ball := .exact 0
def CA2_3_11I2R13H : Ball := ⟨0, 0⟩
def CA2_3_11I2R14Entropy : Ball := ⟨0, 0⟩
def CA2_3_11I2R14Mass : Ball := ⟨0, 0⟩
def CA2_3_11I2R14MassTerm : Ball := .exact 0
def CA2_3_11I2R14H : Ball := ⟨0, 0⟩
def CA2_3_11I2R15Entropy : Ball := ⟨0, 0⟩
def CA2_3_11I2R15Mass : Ball := ⟨0, 0⟩
def CA2_3_11I2R15MassTerm : Ball := .exact 0
def CA2_3_11I2R15H : Ball := ⟨0, 0⟩
def CA2_3_11I2R16Entropy : Ball := ⟨0, 0⟩
def CA2_3_11I2R16Mass : Ball := ⟨0, 0⟩
def CA2_3_11I2R16MassTerm : Ball := .exact 0
def CA2_3_11I2R16H : Ball := ⟨0, 0⟩
def CA2_3_11I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA2_3_11I2R0H
  | 1 => CA2_3_11I2R1H
  | 2 => CA2_3_11I2R2H
  | 3 => CA2_3_11I2R3H
  | 4 => CA2_3_11I2R4H
  | 5 => CA2_3_11I2R5H
  | 6 => CA2_3_11I2R6H
  | 7 => CA2_3_11I2R7H
  | 8 => CA2_3_11I2R8H
  | 9 => CA2_3_11I2R9H
  | 10 => CA2_3_11I2R10H
  | 11 => CA2_3_11I2R11H
  | 12 => CA2_3_11I2R12H
  | 13 => CA2_3_11I2R13H
  | 14 => CA2_3_11I2R14H
  | 15 => CA2_3_11I2R15H
  | 16 => CA2_3_11I2R16H
  | _ => (.exact 0)
def CA2_3_11I2Singleton : Ball := ⟨(38894992084717347555582283408189 / 100000000000000000000000000000000), (16335271253 / 50000000000000000000000000000000)⟩
def CA2_3_11I2Group : Ball := ⟨(9634925775142631944774657588007 / 12500000000000000000000000000000), (69821895561 / 50000000000000000000000000000000)⟩

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
def CA2_3_11I2H : Ball := ⟨(466160700057499250171638083679 / 390625000000000000000000000000), (414118310199 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA2_4_10I0
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
def CA2_4_10I0Value (a : Fin 17) : ℝ := marginal (below (shape 2 4 10)) (fun u => (stageALaw (shape 2 4 10) u : ℝ)) ((Equiv.refl (Fin 3)) 0) a
def CA2_4_10I0Entropy : Ball := ⟨(105385279083358165886590363081313 / 100000000000000000000000000000000), (63527471883 / 100000000000000000000000000000000)⟩
def CA2_4_10I0Mass : Ball := ⟨1, (49 / 12500000000000000000000000000000)⟩
def CA2_4_10I0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CA2_4_10I0MassTermLog : Ball := ⟨0, (10587912037 / 50000000000000000000000000000000)⟩
def CA2_4_10I0MassTerm : Ball := ⟨0, (847032963 / 4000000000000000000000000000000)⟩
def CA2_4_10I0H : Ball := ⟨(105385279083358165886590363081313 / 100000000000000000000000000000000), (42351647979 / 50000000000000000000000000000000)⟩

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
def CA2_4_10I1PairEntropy : Ball := ⟨(78464608316607251550725274170061 / 25000000000000000000000000000000), (130647428739 / 100000000000000000000000000000000)⟩
def CA2_4_10I1PairMass : Ball := ⟨(19999999999999999999999999999999 / 20000000000000000000000000000000), (677 / 100000000000000000000000000000000)⟩
def CA2_4_10I1PairMassTermLogWitness : LogWitness := ⟨-1, 19999999999999999999999999999999, 10000000000000000000000000000000⟩
def CA2_4_10I1PairMassTermLog : Ball := ⟨(-1 / 20000000000000000000000000000000), (42351648043 / 100000000000000000000000000000000)⟩
def CA2_4_10I1PairMassTerm : Ball := ⟨(1 / 20000000000000000000000000000000), (10587912011 / 25000000000000000000000000000000)⟩
def CA2_4_10I1PairH : Ball := ⟨(313858433266429006202901096680239 / 100000000000000000000000000000000), (172999076783 / 100000000000000000000000000000000)⟩

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
def CA2_4_10I1R0Entropy : Ball := ⟨(2308835273618154621376203064027 / 25000000000000000000000000000000), (3713016947 / 100000000000000000000000000000000)⟩
def CA2_4_10I1R0Mass : Ball := ⟨(2504889485643368923017551688527 / 100000000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩
def CA2_4_10I1R0MassTermLogWitness : LogWitness := ⟨-6, 2504889485643368923017551688527, 1562500000000000000000000000000⟩
def CA2_4_10I1R0MassTermLog : Ball := ⟨(-92173139248302656677203865689747 / 25000000000000000000000000000000), (148230766459 / 100000000000000000000000000000000)⟩
def CA2_4_10I1R0MassTerm : Ball := ⟨(2308835273618154621376203064027 / 25000000000000000000000000000000), (3713016947 / 100000000000000000000000000000000)⟩
def CA2_4_10I1R0H : Ball := ⟨0, (3713016947 / 50000000000000000000000000000000)⟩
def CA2_4_10I1R1Entropy : Ball := ⟨(24965343144609674399182126743019 / 50000000000000000000000000000000), (490436799 / 2000000000000000000000000000000)⟩
def CA2_4_10I1R1Mass : Ball := ⟨(11580111324399872760399582028853 / 50000000000000000000000000000000), (61 / 50000000000000000000000000000000)⟩
def CA2_4_10I1R1MassTermLogWitness : LogWitness := ⟨-3, 11580111324399872760399582028853, 6250000000000000000000000000000⟩
def CA2_4_10I1R1MassTermLog : Ball := ⟨(-14627339198234724098301207124197 / 10000000000000000000000000000000), (42351647629 / 50000000000000000000000000000000)⟩
def CA2_4_10I1R1MassTerm : Ball := ⟨(4234655407382902096081315647709 / 12500000000000000000000000000000), (1226091997 / 6250000000000000000000000000000)⟩
def CA2_4_10I1R1H : Ball := ⟨(8026721515078066014856864152183 / 50000000000000000000000000000000), (22069655951 / 50000000000000000000000000000000)⟩
def CA2_4_10I1R2Entropy : Ball := ⟨(17117059391645892364167391942107 / 20000000000000000000000000000000), (7948650027 / 20000000000000000000000000000000)⟩
def CA2_4_10I1R2Mass : Ball := ⟨(24334887865556885556183284253767 / 50000000000000000000000000000000), (107 / 50000000000000000000000000000000)⟩
def CA2_4_10I1R2MassTermLogWitness : LogWitness := ⟨-2, 24334887865556885556183284253767, 12500000000000000000000000000000⟩
def CA2_4_10I1R2MassTermLog : Ball := ⟨(-36005598505125881559196550427071 / 50000000000000000000000000000000), (496308371 / 781250000000000000000000000000)⟩
def CA2_4_10I1R2MassTerm : Ball := ⟨(1401907523447201525122493550069 / 4000000000000000000000000000000), (3864834757 / 12500000000000000000000000000000)⟩
def CA2_4_10I1R2H : Ball := ⟨(5053760887204942369277462095881 / 10000000000000000000000000000000), (70661928191 / 100000000000000000000000000000000)⟩
def CA2_4_10I1R3Entropy : Ball := ⟨(30290388825501837215966765588111 / 50000000000000000000000000000000), (2658746797 / 10000000000000000000000000000000)⟩
def CA2_4_10I1R3Mass : Ball := ⟨(11580111324399872760399582028853 / 50000000000000000000000000000000), (71 / 50000000000000000000000000000000)⟩
def CA2_4_10I1R3MassTermLogWitness : LogWitness := ⟨-3, 11580111324399872760399582028853, 6250000000000000000000000000000⟩
def CA2_4_10I1R3MassTermLog : Ball := ⟨(-14627339198234724098301207124197 / 10000000000000000000000000000000), (16940659069 / 20000000000000000000000000000000)⟩
def CA2_4_10I1R3MassTerm : Ball := ⟨(4234655407382902096081315647709 / 12500000000000000000000000000000), (19617472001 / 100000000000000000000000000000000)⟩
def CA2_4_10I1R3H : Ball := ⟨(534070687838809153265660119891 / 2000000000000000000000000000000), (46204939971 / 100000000000000000000000000000000)⟩
def CA2_4_10I1R4Entropy : Ball := ⟨(6116771990600472061821371236591 / 50000000000000000000000000000000), (274678377 / 6250000000000000000000000000000)⟩
def CA2_4_10I1R4Mass : Ball := ⟨(2504889485643368923017551688529 / 100000000000000000000000000000000), (27 / 100000000000000000000000000000000)⟩
def CA2_4_10I1R4MassTermLogWitness : LogWitness := ⟨-6, 2504889485643368923017551688529, 1562500000000000000000000000000⟩
def CA2_4_10I1R4MassTermLog : Ball := ⟨(-92173139248302656677203865689727 / 25000000000000000000000000000000), (148230766859 / 100000000000000000000000000000000)⟩
def CA2_4_10I1R4MassTerm : Ball := ⟨(9235341094472618485504812256113 / 100000000000000000000000000000000), (1856508497 / 50000000000000000000000000000000)⟩
def CA2_4_10I1R4H : Ball := ⟨(2998202886728325638137930217069 / 100000000000000000000000000000000), (4053935513 / 50000000000000000000000000000000)⟩
def CA2_4_10I1R5Entropy : Ball := ⟨0, 0⟩
def CA2_4_10I1R5Mass : Ball := ⟨0, 0⟩
def CA2_4_10I1R5MassTerm : Ball := .exact 0
def CA2_4_10I1R5H : Ball := ⟨0, 0⟩
def CA2_4_10I1R6Entropy : Ball := ⟨0, 0⟩
def CA2_4_10I1R6Mass : Ball := ⟨0, 0⟩
def CA2_4_10I1R6MassTerm : Ball := .exact 0
def CA2_4_10I1R6H : Ball := ⟨0, 0⟩
def CA2_4_10I1R7Entropy : Ball := ⟨0, 0⟩
def CA2_4_10I1R7Mass : Ball := ⟨0, 0⟩
def CA2_4_10I1R7MassTerm : Ball := .exact 0
def CA2_4_10I1R7H : Ball := ⟨0, 0⟩
def CA2_4_10I1R8Entropy : Ball := ⟨0, 0⟩
def CA2_4_10I1R8Mass : Ball := ⟨0, 0⟩
def CA2_4_10I1R8MassTerm : Ball := .exact 0
def CA2_4_10I1R8H : Ball := ⟨0, 0⟩
def CA2_4_10I1R9Entropy : Ball := ⟨0, 0⟩
def CA2_4_10I1R9Mass : Ball := ⟨0, 0⟩
def CA2_4_10I1R9MassTerm : Ball := .exact 0
def CA2_4_10I1R9H : Ball := ⟨0, 0⟩
def CA2_4_10I1R10Entropy : Ball := ⟨0, 0⟩
def CA2_4_10I1R10Mass : Ball := ⟨0, 0⟩
def CA2_4_10I1R10MassTerm : Ball := .exact 0
def CA2_4_10I1R10H : Ball := ⟨0, 0⟩
def CA2_4_10I1R11Entropy : Ball := ⟨0, 0⟩
def CA2_4_10I1R11Mass : Ball := ⟨0, 0⟩
def CA2_4_10I1R11MassTerm : Ball := .exact 0
def CA2_4_10I1R11H : Ball := ⟨0, 0⟩
def CA2_4_10I1R12Entropy : Ball := ⟨0, 0⟩
def CA2_4_10I1R12Mass : Ball := ⟨0, 0⟩
def CA2_4_10I1R12MassTerm : Ball := .exact 0
def CA2_4_10I1R12H : Ball := ⟨0, 0⟩
def CA2_4_10I1R13Entropy : Ball := ⟨0, 0⟩
def CA2_4_10I1R13Mass : Ball := ⟨0, 0⟩
def CA2_4_10I1R13MassTerm : Ball := .exact 0
def CA2_4_10I1R13H : Ball := ⟨0, 0⟩
def CA2_4_10I1R14Entropy : Ball := ⟨0, 0⟩
def CA2_4_10I1R14Mass : Ball := ⟨0, 0⟩
def CA2_4_10I1R14MassTerm : Ball := .exact 0
def CA2_4_10I1R14H : Ball := ⟨0, 0⟩
def CA2_4_10I1R15Entropy : Ball := ⟨0, 0⟩
def CA2_4_10I1R15Mass : Ball := ⟨0, 0⟩
def CA2_4_10I1R15MassTerm : Ball := .exact 0
def CA2_4_10I1R15H : Ball := ⟨0, 0⟩
def CA2_4_10I1R16Entropy : Ball := ⟨0, 0⟩
def CA2_4_10I1R16Mass : Ball := ⟨0, 0⟩
def CA2_4_10I1R16MassTerm : Ball := .exact 0
def CA2_4_10I1R16H : Ball := ⟨0, 0⟩
def CA2_4_10I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA2_4_10I1R0H
  | 1 => CA2_4_10I1R1H
  | 2 => CA2_4_10I1R2H
  | 3 => CA2_4_10I1R3H
  | 4 => CA2_4_10I1R4H
  | 5 => CA2_4_10I1R5H
  | 6 => CA2_4_10I1R6H
  | 7 => CA2_4_10I1R7H
  | 8 => CA2_4_10I1R8H
  | 9 => CA2_4_10I1R9H
  | 10 => CA2_4_10I1R10H
  | 11 => CA2_4_10I1R11H
  | 12 => CA2_4_10I1R12H
  | 13 => CA2_4_10I1R13H
  | 14 => CA2_4_10I1R14H
  | 15 => CA2_4_10I1R15H
  | 16 => CA2_4_10I1R16H
  | _ => (.exact 0)
def CA2_4_10I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | _, _, _ => (.exact 0)
def CA2_4_10I1Singleton : Ball := ⟨0, 0⟩
def CA2_4_10I1Group : Ball := ⟨(19258557836174867804781857094959 / 20000000000000000000000000000000), (22067510623 / 12500000000000000000000000000000)⟩

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
def CA2_4_10I1H : Ball := ⟨(121272854904680328155082525730649 / 100000000000000000000000000000000), (526079246751 / 100000000000000000000000000000000)⟩

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
def CA2_4_10I2PairEntropy : Ball := ⟨(35926908456638450987485173075227 / 12500000000000000000000000000000), (12716528731 / 10000000000000000000000000000000)⟩
def CA2_4_10I2PairMass : Ball := ⟨(24999999999999999999999999999997 / 25000000000000000000000000000000), (377 / 50000000000000000000000000000000)⟩
def CA2_4_10I2PairMassTermLogWitness : LogWitness := ⟨-1, 24999999999999999999999999999997, 12500000000000000000000000000000⟩
def CA2_4_10I2PairMassTermLog : Ball := ⟨(-11 / 100000000000000000000000000000000), (1058791203 / 2500000000000000000000000000000)⟩
def CA2_4_10I2PairMassTerm : Ball := ⟨(11 / 100000000000000000000000000000000), (42351648121 / 100000000000000000000000000000000)⟩
def CA2_4_10I2PairH : Ball := ⟨(57483053530621521579976276920361 / 20000000000000000000000000000000), (169516935431 / 100000000000000000000000000000000)⟩

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
def CA2_4_10I2R0Entropy : Ball := ⟨0, 0⟩
def CA2_4_10I2R0Mass : Ball := ⟨0, 0⟩
def CA2_4_10I2R0MassTerm : Ball := .exact 0
def CA2_4_10I2R0H : Ball := ⟨0, 0⟩
def CA2_4_10I2R1Entropy : Ball := ⟨0, 0⟩
def CA2_4_10I2R1Mass : Ball := ⟨0, 0⟩
def CA2_4_10I2R1MassTerm : Ball := .exact 0
def CA2_4_10I2R1H : Ball := ⟨0, 0⟩
def CA2_4_10I2R2Entropy : Ball := ⟨(2990972379172986392384533553 / 10000000000000000000000000000000), (4882699 / 50000000000000000000000000000000)⟩
def CA2_4_10I2R2Mass : Ball := ⟨(1290103932301626811496829007 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
def CA2_4_10I2R2MassTermLogWitness : LogWitness := ⟨-16, 1290103932301626811496829007, 762939453125000000000000000⟩
def CA2_4_10I2R2MassTermLog : Ball := ⟨(-1056505550160642353212106317084283 / 100000000000000000000000000000000), (179994598197 / 50000000000000000000000000000000)⟩
def CA2_4_10I2R2MassTerm : Ball := ⟨(1090401571808590665558663107 / 4000000000000000000000000000000), (9288523 / 100000000000000000000000000000000)⟩
def CA2_4_10I2R2H : Ball := ⟨(529936899303019456975751571 / 20000000000000000000000000000000), (19053921 / 100000000000000000000000000000000)⟩
def CA2_4_10I2R3Entropy : Ball := ⟨(2291779931671292420414679390167 / 50000000000000000000000000000000), (1067721 / 62500000000000000000000000000)⟩
def CA2_4_10I2R3Mass : Ball := ⟨(389590766700474046145817959981 / 50000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
def CA2_4_10I2R3MassTermLogWitness : LogWitness := ⟨-8, 389590766700474046145817959981, 195312500000000000000000000000⟩
def CA2_4_10I2R3MassTermLog : Ball := ⟨(-6068351765446050781817188320967 / 1250000000000000000000000000000), (190582414687 / 100000000000000000000000000000000)⟩
def CA2_4_10I2R3MassTerm : Ball := ⟨(3782678107053283472545872209083 / 100000000000000000000000000000000), (1160143 / 78125000000000000000000000000)⟩
def CA2_4_10I2R3H : Ball := ⟨(800881756289301368283486571251 / 100000000000000000000000000000000), (9979177 / 312500000000000000000000000000)⟩
def CA2_4_10I2R4Entropy : Ball := ⟨(47580084131454018982792986308027 / 100000000000000000000000000000000), (2012692307 / 10000000000000000000000000000000)⟩
def CA2_4_10I2R4Mass : Ball := ⟨(19115353448892195473084333322407 / 100000000000000000000000000000000), (3 / 2500000000000000000000000000000)⟩
def CA2_4_10I2R4MassTermLogWitness : LogWitness := ⟨-3, 19115353448892195473084333322407, 12500000000000000000000000000000⟩
def CA2_4_10I2R4MassTermLog : Ball := ⟨(-165467832835452117553219578152353 / 100000000000000000000000000000000), (84703295359 / 100000000000000000000000000000000)⟩
def CA2_4_10I2R4MassTerm : Ball := ⟨(15814880545359384516533513860097 / 50000000000000000000000000000000), (1619133449 / 10000000000000000000000000000000)⟩
def CA2_4_10I2R4H : Ball := ⟨(15950323040735249949725958587833 / 100000000000000000000000000000000), (907956439 / 2500000000000000000000000000000)⟩
def CA2_4_10I2R5Entropy : Ball := ⟨(9093216391080514831312704048851 / 12500000000000000000000000000000), (4694842291 / 12500000000000000000000000000000)⟩
def CA2_4_10I2R5Mass : Ball := ⟨(21147174126323547554821199212369 / 50000000000000000000000000000000), (81 / 50000000000000000000000000000000)⟩
def CA2_4_10I2R5MassTermLogWitness : LogWitness := ⟨-2, 21147174126323547554821199212369, 12500000000000000000000000000000⟩
def CA2_4_10I2R5MassTermLog : Ball := ⟨(-17210334398222848168988098648769 / 20000000000000000000000000000000), (63527471431 / 100000000000000000000000000000000)⟩
def CA2_4_10I2R5MassTerm : Ball := ⟨(909874845728685891983629432179 / 2500000000000000000000000000000), (26868530143 / 100000000000000000000000000000000)⟩
def CA2_4_10I2R5H : Ball := ⟨(1135960540609271342848639221989 / 3125000000000000000000000000000), (64427268471 / 100000000000000000000000000000000)⟩
def CA2_4_10I2R6Entropy : Ball := ⟨(22953632028807823408534549264129 / 100000000000000000000000000000000), (10016291023 / 100000000000000000000000000000000)⟩
def CA2_4_10I2R6Mass : Ball := ⟨(1843704332429729067184806144557 / 20000000000000000000000000000000), (3 / 6250000000000000000000000000000)⟩
def CA2_4_10I2R6MassTermLogWitness : LogWitness := ⟨-4, 1843704332429729067184806144557, 1250000000000000000000000000000⟩
def CA2_4_10I2R6MassTermLog : Ball := ⟨(-238395550160642353212106546222153 / 100000000000000000000000000000000), (21175823787 / 20000000000000000000000000000000)⟩
def CA2_4_10I2R6MassTerm : Ball := ⟨(2197654543315725499556882275933 / 10000000000000000000000000000000), (976048963 / 10000000000000000000000000000000)⟩
def CA2_4_10I2R6H : Ball := ⟨(977086595650568412965726504799 / 100000000000000000000000000000000), (19776780653 / 100000000000000000000000000000000)⟩
def CA2_4_10I2R7Entropy : Ball := ⟨0, 0⟩
def CA2_4_10I2R7Mass : Ball := ⟨0, 0⟩
def CA2_4_10I2R7MassTerm : Ball := .exact 0
def CA2_4_10I2R7H : Ball := ⟨0, 0⟩
def CA2_4_10I2R8Entropy : Ball := ⟨0, 0⟩
def CA2_4_10I2R8Mass : Ball := ⟨0, 0⟩
def CA2_4_10I2R8MassTerm : Ball := .exact 0
def CA2_4_10I2R8H : Ball := ⟨0, 0⟩
def CA2_4_10I2R9Entropy : Ball := ⟨0, 0⟩
def CA2_4_10I2R9Mass : Ball := ⟨0, 0⟩
def CA2_4_10I2R9MassTerm : Ball := .exact 0
def CA2_4_10I2R9H : Ball := ⟨0, 0⟩
def CA2_4_10I2R10Entropy : Ball := ⟨0, 0⟩
def CA2_4_10I2R10Mass : Ball := ⟨0, 0⟩
def CA2_4_10I2R10MassTerm : Ball := .exact 0
def CA2_4_10I2R10H : Ball := ⟨0, 0⟩
def CA2_4_10I2R11Entropy : Ball := ⟨0, 0⟩
def CA2_4_10I2R11Mass : Ball := ⟨0, 0⟩
def CA2_4_10I2R11MassTerm : Ball := .exact 0
def CA2_4_10I2R11H : Ball := ⟨0, 0⟩
def CA2_4_10I2R12Entropy : Ball := ⟨0, 0⟩
def CA2_4_10I2R12Mass : Ball := ⟨0, 0⟩
def CA2_4_10I2R12MassTerm : Ball := .exact 0
def CA2_4_10I2R12H : Ball := ⟨0, 0⟩
def CA2_4_10I2R13Entropy : Ball := ⟨0, 0⟩
def CA2_4_10I2R13Mass : Ball := ⟨0, 0⟩
def CA2_4_10I2R13MassTerm : Ball := .exact 0
def CA2_4_10I2R13H : Ball := ⟨0, 0⟩
def CA2_4_10I2R14Entropy : Ball := ⟨0, 0⟩
def CA2_4_10I2R14Mass : Ball := ⟨0, 0⟩
def CA2_4_10I2R14MassTerm : Ball := .exact 0
def CA2_4_10I2R14H : Ball := ⟨0, 0⟩
def CA2_4_10I2R15Entropy : Ball := ⟨0, 0⟩
def CA2_4_10I2R15Mass : Ball := ⟨0, 0⟩
def CA2_4_10I2R15MassTerm : Ball := .exact 0
def CA2_4_10I2R15H : Ball := ⟨0, 0⟩
def CA2_4_10I2R16Entropy : Ball := ⟨0, 0⟩
def CA2_4_10I2R16Mass : Ball := ⟨0, 0⟩
def CA2_4_10I2R16MassTerm : Ball := .exact 0
def CA2_4_10I2R16H : Ball := ⟨0, 0⟩
def CA2_4_10I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA2_4_10I2R0H
  | 1 => CA2_4_10I2R1H
  | 2 => CA2_4_10I2R2H
  | 3 => CA2_4_10I2R3H
  | 4 => CA2_4_10I2R4H
  | 5 => CA2_4_10I2R5H
  | 6 => CA2_4_10I2R6H
  | 7 => CA2_4_10I2R7H
  | 8 => CA2_4_10I2R8H
  | 9 => CA2_4_10I2R9H
  | 10 => CA2_4_10I2R10H
  | 11 => CA2_4_10I2R11H
  | 12 => CA2_4_10I2R12H
  | 13 => CA2_4_10I2R13H
  | 14 => CA2_4_10I2R14H
  | 15 => CA2_4_10I2R15H
  | 16 => CA2_4_10I2R16H
  | _ => (.exact 0)
def CA2_4_10I2Singleton : Ball := ⟨(16222574466090492566167298681711 / 50000000000000000000000000000000), (27623665329 / 100000000000000000000000000000000)⟩
def CA2_4_10I2Group : Ball := ⟨(10815853413606162866468887861101 / 12500000000000000000000000000000), (75679181287 / 50000000000000000000000000000000)⟩

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
def CA2_4_10I2H : Ball := ⟨(114361613035409002036379178824189 / 100000000000000000000000000000000), (472233660579 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA2_5_9I0
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
def CA2_5_9I0Value (a : Fin 17) : ℝ := marginal (below (shape 2 5 9)) (fun u => (stageALaw (shape 2 5 9) u : ℝ)) ((Equiv.refl (Fin 3)) 0) a
def CA2_5_9I0Entropy : Ball := ⟨(26206788452834352675294167181257 / 25000000000000000000000000000000), (7940933939 / 12500000000000000000000000000000)⟩
def CA2_5_9I0Mass : Ball := ⟨1, (53 / 25000000000000000000000000000000)⟩
def CA2_5_9I0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CA2_5_9I0MassTermLog : Ball := ⟨0, (10587911947 / 50000000000000000000000000000000)⟩
def CA2_5_9I0MassTerm : Ball := ⟨0, (4235164779 / 20000000000000000000000000000000)⟩
def CA2_5_9I0H : Ball := ⟨(26206788452834352675294167181257 / 25000000000000000000000000000000), (84703295407 / 100000000000000000000000000000000)⟩

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
def CA2_5_9I1PairEntropy : Ball := ⟨(16429681926455847443361379676879 / 5000000000000000000000000000000), (8661547441 / 6250000000000000000000000000000)⟩
def CA2_5_9I1PairMass : Ball := ⟨(12499999999999999999999999999999 / 12500000000000000000000000000000), (141 / 25000000000000000000000000000000)⟩
def CA2_5_9I1PairMassTermLogWitness : LogWitness := ⟨-1, 12499999999999999999999999999999, 6250000000000000000000000000000⟩
def CA2_5_9I1PairMassTermLog : Ball := ⟨(-7 / 100000000000000000000000000000000), (4235164793 / 10000000000000000000000000000000)⟩
def CA2_5_9I1PairMassTerm : Ball := ⟨(7 / 100000000000000000000000000000000), (42351647931 / 100000000000000000000000000000000)⟩
def CA2_5_9I1PairH : Ball := ⟨(328593638529116948867227593537573 / 100000000000000000000000000000000), (180936406987 / 100000000000000000000000000000000)⟩

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
def CA2_5_9I1R0Entropy : Ball := ⟨(158107504426140389340504222457 / 10000000000000000000000000000000), (22597199 / 4000000000000000000000000000000)⟩
def CA2_5_9I1R0Mass : Ball := ⟨(1667378902956342085611500253 / 625000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
def CA2_5_9I1R0MassTermLogWitness : LogWitness := ⟨-9, 1667378902956342085611500253, 1220703125000000000000000000⟩
def CA2_5_9I1R0MassTermLog : Ball := ⟨(-148162469387027396464920609740599 / 25000000000000000000000000000000), (211758238329 / 100000000000000000000000000000000)⟩
def CA2_5_9I1R0MassTerm : Ball := ⟨(158107504426140389340504222457 / 10000000000000000000000000000000), (22597199 / 4000000000000000000000000000000)⟩
def CA2_5_9I1R0H : Ball := ⟨0, (22597199 / 2000000000000000000000000000000)⟩
def CA2_5_9I1R1Entropy : Ball := ⟨(6670635961056939163159896733377 / 25000000000000000000000000000000), (5352074999 / 50000000000000000000000000000000)⟩
def CA2_5_9I1R1Mass : Ball := ⟨(1053102465437805853118592288551 / 12500000000000000000000000000000), (21 / 50000000000000000000000000000000)⟩
def CA2_5_9I1R1MassTermLogWitness : LogWitness := ⟨-4, 1053102465437805853118592288551, 781250000000000000000000000000⟩
def CA2_5_9I1R1MassTermLog : Ball := ⟨(-247398810778246609565454345786693 / 100000000000000000000000000000000), (105879118913 / 100000000000000000000000000000000)⟩
def CA2_5_9I1R1MassTerm : Ball := ⟨(10421451903078108812982719691723 / 50000000000000000000000000000000), (4460062499 / 50000000000000000000000000000000)⟩
def CA2_5_9I1R1H : Ball := ⟨(2919820019035769513337073775031 / 50000000000000000000000000000000), (4906068749 / 25000000000000000000000000000000)⟩
def CA2_5_9I1R2Entropy : Ball := ⟨(79090989020379437215757974737353 / 100000000000000000000000000000000), (16964072931 / 50000000000000000000000000000000)⟩
def CA2_5_9I1R2Mass : Ball := ⟨(5163549956503067305169177706389 / 12500000000000000000000000000000), (17 / 12500000000000000000000000000000)⟩
def CA2_5_9I1R2MassTermLogWitness : LogWitness := ⟨-2, 5163549956503067305169177706389, 3125000000000000000000000000000⟩
def CA2_5_9I1R2MassTermLog : Ball := ⟨(-22102608132383648426747574327047 / 25000000000000000000000000000000), (31763735689 / 50000000000000000000000000000000)⟩
def CA2_5_9I1R2MassTerm : Ball := ⟨(18260467401691828723107280068591 / 50000000000000000000000000000000), (26242181887 / 100000000000000000000000000000000)⟩
def CA2_5_9I1R2H : Ball := ⟨(42570054216995779769543414600171 / 100000000000000000000000000000000), (60170327749 / 100000000000000000000000000000000)⟩
def CA2_5_9I1R3Entropy : Ball := ⟨(521050911950431512271708031129 / 625000000000000000000000000000), (19390856207 / 50000000000000000000000000000000)⟩
def CA2_5_9I1R3Mass : Ball := ⟨(5163549956503067305169177706389 / 12500000000000000000000000000000), (3 / 2500000000000000000000000000000)⟩
def CA2_5_9I1R3MassTermLogWitness : LogWitness := ⟨-2, 5163549956503067305169177706389, 3125000000000000000000000000000⟩
def CA2_5_9I1R3MassTermLog : Ball := ⟨(-22102608132383648426747574327047 / 25000000000000000000000000000000), (63527471339 / 100000000000000000000000000000000)⟩
def CA2_5_9I1R3MassTerm : Ball := ⟨(18260467401691828723107280068591 / 50000000000000000000000000000000), (820068183 / 3125000000000000000000000000000)⟩
def CA2_5_9I1R3H : Ball := ⟨(23423605554342692258629362421729 / 50000000000000000000000000000000), (6502389427 / 10000000000000000000000000000000)⟩
def CA2_5_9I1R4Entropy : Ball := ⟨(6127051313947944535908853568479 / 20000000000000000000000000000000), (1533150331 / 12500000000000000000000000000000)⟩
def CA2_5_9I1R4Mass : Ball := ⟨(8424819723502446824948738308407 / 100000000000000000000000000000000), (53 / 100000000000000000000000000000000)⟩
def CA2_5_9I1R4MassTermLogWitness : LogWitness := ⟨-4, 8424819723502446824948738308407, 6250000000000000000000000000000⟩
def CA2_5_9I1R4MassTermLog : Ball := ⟨(-49479762155649321913090869157341 / 20000000000000000000000000000000), (26469779761 / 25000000000000000000000000000000)⟩
def CA2_5_9I1R4MassTerm : Ball := ⟨(4168580761231243525193087876689 / 20000000000000000000000000000000), (2230031259 / 25000000000000000000000000000000)⟩
def CA2_5_9I1R4H : Ball := ⟨(195847055271670101071576569179 / 2000000000000000000000000000000), (5296331921 / 25000000000000000000000000000000)⟩
def CA2_5_9I1R5Entropy : Ball := ⟨(37674616181117434643669330833 / 2000000000000000000000000000000), (162651839 / 25000000000000000000000000000000)⟩
def CA2_5_9I1R5Mass : Ball := ⟨(1667378902956342085611500253 / 625000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
def CA2_5_9I1R5MassTermLogWitness : LogWitness := ⟨-9, 1667378902956342085611500253, 1220703125000000000000000000⟩
def CA2_5_9I1R5MassTermLog : Ball := ⟨(-148162469387027396464920609740599 / 25000000000000000000000000000000), (105879120289 / 50000000000000000000000000000000)⟩
def CA2_5_9I1R5MassTerm : Ball := ⟨(158107504426140389340504222457 / 10000000000000000000000000000000), (564930017 / 100000000000000000000000000000000)⟩
def CA2_5_9I1R5H : Ball := ⟨(7566394119861695969460607927 / 2500000000000000000000000000000), (1215537373 / 100000000000000000000000000000000)⟩
def CA2_5_9I1R6Entropy : Ball := ⟨0, 0⟩
def CA2_5_9I1R6Mass : Ball := ⟨0, 0⟩
def CA2_5_9I1R6MassTerm : Ball := .exact 0
def CA2_5_9I1R6H : Ball := ⟨0, 0⟩
def CA2_5_9I1R7Entropy : Ball := ⟨0, 0⟩
def CA2_5_9I1R7Mass : Ball := ⟨0, 0⟩
def CA2_5_9I1R7MassTerm : Ball := .exact 0
def CA2_5_9I1R7H : Ball := ⟨0, 0⟩
def CA2_5_9I1R8Entropy : Ball := ⟨0, 0⟩
def CA2_5_9I1R8Mass : Ball := ⟨0, 0⟩
def CA2_5_9I1R8MassTerm : Ball := .exact 0
def CA2_5_9I1R8H : Ball := ⟨0, 0⟩
def CA2_5_9I1R9Entropy : Ball := ⟨0, 0⟩
def CA2_5_9I1R9Mass : Ball := ⟨0, 0⟩
def CA2_5_9I1R9MassTerm : Ball := .exact 0
def CA2_5_9I1R9H : Ball := ⟨0, 0⟩
def CA2_5_9I1R10Entropy : Ball := ⟨0, 0⟩
def CA2_5_9I1R10Mass : Ball := ⟨0, 0⟩
def CA2_5_9I1R10MassTerm : Ball := .exact 0
def CA2_5_9I1R10H : Ball := ⟨0, 0⟩
def CA2_5_9I1R11Entropy : Ball := ⟨0, 0⟩
def CA2_5_9I1R11Mass : Ball := ⟨0, 0⟩
def CA2_5_9I1R11MassTerm : Ball := .exact 0
def CA2_5_9I1R11H : Ball := ⟨0, 0⟩
def CA2_5_9I1R12Entropy : Ball := ⟨0, 0⟩
def CA2_5_9I1R12Mass : Ball := ⟨0, 0⟩
def CA2_5_9I1R12MassTerm : Ball := .exact 0
def CA2_5_9I1R12H : Ball := ⟨0, 0⟩
def CA2_5_9I1R13Entropy : Ball := ⟨0, 0⟩
def CA2_5_9I1R13Mass : Ball := ⟨0, 0⟩
def CA2_5_9I1R13MassTerm : Ball := .exact 0
def CA2_5_9I1R13H : Ball := ⟨0, 0⟩
def CA2_5_9I1R14Entropy : Ball := ⟨0, 0⟩
def CA2_5_9I1R14Mass : Ball := ⟨0, 0⟩
def CA2_5_9I1R14MassTerm : Ball := .exact 0
def CA2_5_9I1R14H : Ball := ⟨0, 0⟩
def CA2_5_9I1R15Entropy : Ball := ⟨0, 0⟩
def CA2_5_9I1R15Mass : Ball := ⟨0, 0⟩
def CA2_5_9I1R15MassTerm : Ball := .exact 0
def CA2_5_9I1R15H : Ball := ⟨0, 0⟩
def CA2_5_9I1R16Entropy : Ball := ⟨0, 0⟩
def CA2_5_9I1R16Mass : Ball := ⟨0, 0⟩
def CA2_5_9I1R16MassTerm : Ball := .exact 0
def CA2_5_9I1R16H : Ball := ⟨0, 0⟩
def CA2_5_9I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA2_5_9I1R0H
  | 1 => CA2_5_9I1R1H
  | 2 => CA2_5_9I1R2H
  | 3 => CA2_5_9I1R3H
  | 4 => CA2_5_9I1R4H
  | 5 => CA2_5_9I1R5H
  | 6 => CA2_5_9I1R6H
  | 7 => CA2_5_9I1R7H
  | 8 => CA2_5_9I1R8H
  | 9 => CA2_5_9I1R9H
  | 10 => CA2_5_9I1R10H
  | 11 => CA2_5_9I1R11H
  | 12 => CA2_5_9I1R12H
  | 13 => CA2_5_9I1R13H
  | 14 => CA2_5_9I1R14H
  | 15 => CA2_5_9I1R15H
  | 16 => CA2_5_9I1R16H
  | _ => (.exact 0)
def CA2_5_9I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | _, _, _ => (.exact 0)
def CA2_5_9I1Singleton : Ball := ⟨0, 0⟩
def CA2_5_9I1Group : Ball := ⟨(105351913892130676205833539769721 / 100000000000000000000000000000000), (84174611011 / 50000000000000000000000000000000)⟩

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
def CA2_5_9I1H : Ball := ⟨(117889810744855596455560513998131 / 100000000000000000000000000000000), (517634851031 / 100000000000000000000000000000000)⟩

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
def CA2_5_9I2PairEntropy : Ball := ⟨(73104883922187871874847302413713 / 25000000000000000000000000000000), (29147374527 / 25000000000000000000000000000000)⟩
def CA2_5_9I2PairMass : Ball := ⟨(24999999999999999999999999999999 / 25000000000000000000000000000000), (159 / 25000000000000000000000000000000)⟩
def CA2_5_9I2PairMassTermLogWitness : LogWitness := ⟨-1, 24999999999999999999999999999999, 12500000000000000000000000000000⟩
def CA2_5_9I2PairMassTermLog : Ball := ⟨(-1 / 25000000000000000000000000000000), (21175824001 / 50000000000000000000000000000000)⟩
def CA2_5_9I2PairMassTerm : Ball := ⟨(1 / 25000000000000000000000000000000), (42351648003 / 100000000000000000000000000000000)⟩
def CA2_5_9I2PairH : Ball := ⟨(4569055245136741992177956400857 / 1562500000000000000000000000000), (158941146111 / 100000000000000000000000000000000)⟩

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
def CA2_5_9I2R0Entropy : Ball := ⟨0, 0⟩
def CA2_5_9I2R0Mass : Ball := ⟨0, 0⟩
def CA2_5_9I2R0MassTerm : Ball := .exact 0
def CA2_5_9I2R0H : Ball := ⟨0, 0⟩
def CA2_5_9I2R1Entropy : Ball := ⟨(44167187154123555521479247 / 2500000000000000000000000000000), (287869 / 50000000000000000000000000000000)⟩
def CA2_5_9I2R1Mass : Ball := ⟨(15446294267654093658823153 / 12500000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
def CA2_5_9I2R1MassTermLogWitness : LogWitness := ⟨-20, 15446294267654093658823153, 11920928955078125000000000⟩
def CA2_5_9I2R1MassTermLog : Ball := ⟨(-1360387008092443278543485307817727 / 100000000000000000000000000000000), (88939106873 / 20000000000000000000000000000000)⟩
def CA2_5_9I2R1MassTerm : Ball := ⟨(67241401743646111151768287 / 4000000000000000000000000000000), (549567 / 100000000000000000000000000000000)⟩
def CA2_5_9I2R1H : Ball := ⟨(17130488514757888412992541 / 20000000000000000000000000000000), (225061 / 20000000000000000000000000000000)⟩
def CA2_5_9I2R2Entropy : Ball := ⟨(656499577510096381526505615357 / 100000000000000000000000000000000), (109772619 / 50000000000000000000000000000000)⟩
def CA2_5_9I2R2Mass : Ball := ⟨(80503335783270338034989132729 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def CA2_5_9I2R2MassTermLogWitness : LogWitness := ⟨-11, 80503335783270338034989132729, 48828125000000000000000000000⟩
def CA2_5_9I2R2MassTermLog : Ball := ⟨(-14249253686205517097888745662231 / 2000000000000000000000000000000), (254109891649 / 100000000000000000000000000000000)⟩
def CA2_5_9I2R2MassTerm : Ball := ⟨(57355622708080268666003791401 / 10000000000000000000000000000000), (204566983 / 100000000000000000000000000000000)⟩
def CA2_5_9I2R2H : Ball := ⟨(82943350429293694866467701347 / 100000000000000000000000000000000), (424112221 / 100000000000000000000000000000000)⟩
def CA2_5_9I2R3Entropy : Ball := ⟨(1907589960332171939248045725577 / 10000000000000000000000000000000), (3625098467 / 50000000000000000000000000000000)⟩
def CA2_5_9I2R3Mass : Ball := ⟨(2325282144135282199653223910747 / 50000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
def CA2_5_9I2R3MassTermLogWitness : LogWitness := ⟨-5, 2325282144135282199653223910747, 1562500000000000000000000000000⟩
def CA2_5_9I2R3MassTermLog : Ball := ⟨(-306818162143517270594524012514053 / 100000000000000000000000000000000), (127054942657 / 100000000000000000000000000000000)⟩
def CA2_5_9I2R3MassTerm : Ball := ⟨(2853755175714898042149589920809 / 20000000000000000000000000000000), (590877187 / 10000000000000000000000000000000)⟩
def CA2_5_9I2R3H : Ball := ⟨(192284948989889167269300306069 / 4000000000000000000000000000000), (3289742201 / 25000000000000000000000000000000)⟩
def CA2_5_9I2R4Entropy : Ball := ⟨(8608470373925618638701070759651 / 12500000000000000000000000000000), (16164273491 / 50000000000000000000000000000000)⟩
def CA2_5_9I2R4Mass : Ball := ⟨(38400299192288280458012912327183 / 100000000000000000000000000000000), (113 / 100000000000000000000000000000000)⟩
def CA2_5_9I2R4MassTermLogWitness : LogWitness := ⟨-2, 38400299192288280458012912327183, 25000000000000000000000000000000⟩
def CA2_5_9I2R4MassTermLog : Ball := ⟨(-5981905843493267938244762848697 / 6250000000000000000000000000000), (63527471343 / 100000000000000000000000000000000)⟩
def CA2_5_9I2R4MassTerm : Ball := ⟨(36753115860838253091643556582981 / 100000000000000000000000000000000), (12197369587 / 50000000000000000000000000000000)⟩
def CA2_5_9I2R4H : Ball := ⟨(32114647130566696017965009494227 / 100000000000000000000000000000000), (14180821539 / 25000000000000000000000000000000)⟩
def CA2_5_9I2R5Entropy : Ball := ⟨(30523059803915827962603849391909 / 50000000000000000000000000000000), (1297586929 / 5000000000000000000000000000000)⟩
def CA2_5_9I2R5Mass : Ball := ⟨(2921890586710961433291201015491 / 10000000000000000000000000000000), (21 / 25000000000000000000000000000000)⟩
def CA2_5_9I2R5MassTermLogWitness : LogWitness := ⟨-2, 2921890586710961433291201015491, 2500000000000000000000000000000⟩
def CA2_5_9I2R5MassTermLog : Ball := ⟨(-61517711251202312490872296417681 / 50000000000000000000000000000000), (7940933917 / 12500000000000000000000000000000)⟩
def CA2_5_9I2R5MassTerm : Ball := ⟨(4493700535522275955311475321987 / 12500000000000000000000000000000), (18562032153 / 100000000000000000000000000000000)⟩
def CA2_5_9I2R5H : Ball := ⟨(12548257661826724141357948103961 / 50000000000000000000000000000000), (44513770733 / 100000000000000000000000000000000)⟩
def CA2_5_9I2R6Entropy : Ball := ⟨(7241438794339083185892507716039 / 100000000000000000000000000000000), (1315609281 / 50000000000000000000000000000000)⟩
def CA2_5_9I2R6Mass : Ball := ⟨(1742463828534306415965938497567 / 100000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
def CA2_5_9I2R6MassTermLogWitness : LogWitness := ⟨-6, 1742463828534306415965938497567, 1562500000000000000000000000000⟩
def CA2_5_9I2R6MassTermLog : Ball := ⟨(-202493504046221639271742787434751 / 50000000000000000000000000000000), (148230766469 / 100000000000000000000000000000000)⟩
def CA2_5_9I2R6MassTerm : Ball := ⟨(7056752126274128498103940381303 / 100000000000000000000000000000000), (1291433769 / 50000000000000000000000000000000)⟩
def CA2_5_9I2R6H : Ball := ⟨(11542916754059667986785458421 / 6250000000000000000000000000000), (52140861 / 1000000000000000000000000000000)⟩
def CA2_5_9I2R7Entropy : Ball := ⟨0, 0⟩
def CA2_5_9I2R7Mass : Ball := ⟨0, 0⟩
def CA2_5_9I2R7MassTerm : Ball := .exact 0
def CA2_5_9I2R7H : Ball := ⟨0, 0⟩
def CA2_5_9I2R8Entropy : Ball := ⟨0, 0⟩
def CA2_5_9I2R8Mass : Ball := ⟨0, 0⟩
def CA2_5_9I2R8MassTerm : Ball := .exact 0
def CA2_5_9I2R8H : Ball := ⟨0, 0⟩
def CA2_5_9I2R9Entropy : Ball := ⟨0, 0⟩
def CA2_5_9I2R9Mass : Ball := ⟨0, 0⟩
def CA2_5_9I2R9MassTerm : Ball := .exact 0
def CA2_5_9I2R9H : Ball := ⟨0, 0⟩
def CA2_5_9I2R10Entropy : Ball := ⟨0, 0⟩
def CA2_5_9I2R10Mass : Ball := ⟨0, 0⟩
def CA2_5_9I2R10MassTerm : Ball := .exact 0
def CA2_5_9I2R10H : Ball := ⟨0, 0⟩
def CA2_5_9I2R11Entropy : Ball := ⟨0, 0⟩
def CA2_5_9I2R11Mass : Ball := ⟨0, 0⟩
def CA2_5_9I2R11MassTerm : Ball := .exact 0
def CA2_5_9I2R11H : Ball := ⟨0, 0⟩
def CA2_5_9I2R12Entropy : Ball := ⟨0, 0⟩
def CA2_5_9I2R12Mass : Ball := ⟨0, 0⟩
def CA2_5_9I2R12MassTerm : Ball := .exact 0
def CA2_5_9I2R12H : Ball := ⟨0, 0⟩
def CA2_5_9I2R13Entropy : Ball := ⟨0, 0⟩
def CA2_5_9I2R13Mass : Ball := ⟨0, 0⟩
def CA2_5_9I2R13MassTerm : Ball := .exact 0
def CA2_5_9I2R13H : Ball := ⟨0, 0⟩
def CA2_5_9I2R14Entropy : Ball := ⟨0, 0⟩
def CA2_5_9I2R14Mass : Ball := ⟨0, 0⟩
def CA2_5_9I2R14MassTerm : Ball := .exact 0
def CA2_5_9I2R14H : Ball := ⟨0, 0⟩
def CA2_5_9I2R15Entropy : Ball := ⟨0, 0⟩
def CA2_5_9I2R15Mass : Ball := ⟨0, 0⟩
def CA2_5_9I2R15MassTerm : Ball := .exact 0
def CA2_5_9I2R15H : Ball := ⟨0, 0⟩
def CA2_5_9I2R16Entropy : Ball := ⟨0, 0⟩
def CA2_5_9I2R16Mass : Ball := ⟨0, 0⟩
def CA2_5_9I2R16MassTerm : Ball := .exact 0
def CA2_5_9I2R16H : Ball := ⟨0, 0⟩
def CA2_5_9I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA2_5_9I2R0H
  | 1 => CA2_5_9I2R1H
  | 2 => CA2_5_9I2R2H
  | 3 => CA2_5_9I2R3H
  | 4 => CA2_5_9I2R4H
  | 5 => CA2_5_9I2R5H
  | 6 => CA2_5_9I2R6H
  | 7 => CA2_5_9I2R7H
  | 8 => CA2_5_9I2R8H
  | 9 => CA2_5_9I2R9H
  | 10 => CA2_5_9I2R10H
  | 11 => CA2_5_9I2R11H
  | 12 => CA2_5_9I2R12H
  | 13 => CA2_5_9I2R13H
  | 14 => CA2_5_9I2R14H
  | 15 => CA2_5_9I2R15H
  | 16 => CA2_5_9I2R16H
  | _ => (.exact 0)
def CA2_5_9I2Singleton : Ball := ⟨(30652448503721051159498519689651 / 100000000000000000000000000000000), (25420405831 / 100000000000000000000000000000000)⟩
def CA2_5_9I2Group : Ball := ⟨(92938450353625246814009033042313 / 100000000000000000000000000000000), (2909115103 / 2000000000000000000000000000000)⟩

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
def CA2_5_9I2H : Ball := ⟨(53271317490750496935685571785111 / 50000000000000000000000000000000), (449852656411 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA2_6_8I0
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
def CA2_6_8I0Value (a : Fin 17) : ℝ := marginal (below (shape 2 6 8)) (fun u => (stageALaw (shape 2 6 8) u : ℝ)) ((Equiv.refl (Fin 3)) 0) a
def CA2_6_8I0Entropy : Ball := ⟨(104189356219362736487019183045251 / 100000000000000000000000000000000), (12705494369 / 20000000000000000000000000000000)⟩
def CA2_6_8I0Mass : Ball := ⟨(99999999999999999999999999999997 / 100000000000000000000000000000000), (373 / 100000000000000000000000000000000)⟩
def CA2_6_8I0MassTermLogWitness : LogWitness := ⟨-1, 99999999999999999999999999999997, 50000000000000000000000000000000⟩
def CA2_6_8I0MassTermLog : Ball := ⟨(-1 / 50000000000000000000000000000000), (42351647739 / 100000000000000000000000000000000)⟩
def CA2_6_8I0MassTerm : Ball := ⟨(1 / 50000000000000000000000000000000), (2117582387 / 5000000000000000000000000000000)⟩
def CA2_6_8I0H : Ball := ⟨(104189356219362736487019183045249 / 100000000000000000000000000000000), (21175823917 / 20000000000000000000000000000000)⟩

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
def CA2_6_8I1PairEntropy : Ball := ⟨(82674041067498159813489851081439 / 25000000000000000000000000000000), (67959117417 / 50000000000000000000000000000000)⟩
def CA2_6_8I1PairMass : Ball := ⟨(50000000000000000000000000000003 / 50000000000000000000000000000000), (373 / 50000000000000000000000000000000)⟩
def CA2_6_8I1PairMassTermLogWitness : LogWitness := ⟨0, 50000000000000000000000000000003, 50000000000000000000000000000000⟩
def CA2_6_8I1PairMassTermLog : Ball := ⟨(3 / 50000000000000000000000000000000), (5293956107 / 25000000000000000000000000000000)⟩
def CA2_6_8I1PairMassTerm : Ball := ⟨(-3 / 50000000000000000000000000000000), (21175824429 / 100000000000000000000000000000000)⟩
def CA2_6_8I1PairH : Ball := ⟨(165348082134996319626979702162881 / 50000000000000000000000000000000), (157094059263 / 100000000000000000000000000000000)⟩

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
def CA2_6_8I1R0Entropy : Ball := ⟨(135529298691786926273657801109 / 100000000000000000000000000000000), (11446131 / 25000000000000000000000000000000)⟩
def CA2_6_8I1R0Mass : Ball := ⟨(482614198838945946544192483 / 3125000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def CA2_6_8I1R0MassTermLogWitness : LogWitness := ⟨-13, 482614198838945946544192483, 381469726562500000000000000⟩
def CA2_6_8I1R0MassTermLog : Ball := ⟨(-87757272668467590908988813682361 / 10000000000000000000000000000000), (296461550987 / 100000000000000000000000000000000)⟩
def CA2_6_8I1R0MassTerm : Ball := ⟨(135529298691786926273657801109 / 100000000000000000000000000000000), (11446131 / 25000000000000000000000000000000)⟩
def CA2_6_8I1R0H : Ball := ⟨0, (11446131 / 12500000000000000000000000000000)⟩
def CA2_6_8I1R1Entropy : Ball := ⟨(1729985614752913054347013600901 / 25000000000000000000000000000000), (1327673133 / 50000000000000000000000000000000)⟩
def CA2_6_8I1R1Mass : Ball := ⟨(139327975552563848910158761633 / 10000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def CA2_6_8I1R1MassTermLogWitness : LogWitness := ⟨-7, 139327975552563848910158761633, 78125000000000000000000000000⟩
def CA2_6_8I1R1MassTermLog : Ball := ⟨(-427350968183090038858467330187083 / 100000000000000000000000000000000), (42351647617 / 25000000000000000000000000000000)⟩
def CA2_6_8I1R1MassTerm : Ball := ⟨(5954194524737806017155259310491 / 100000000000000000000000000000000), (236030779 / 10000000000000000000000000000000)⟩
def CA2_6_8I1R1H : Ball := ⟨(965747934273846200232795093113 / 100000000000000000000000000000000), (626956757 / 12500000000000000000000000000000)⟩
def CA2_6_8I1R2Entropy : Ball := ⟨(7106507635133811281749043545967 / 12500000000000000000000000000000), (23334450821 / 100000000000000000000000000000000)⟩
def CA2_6_8I1R2Mass : Ball := ⟨(11302880088511327856722246324597 / 50000000000000000000000000000000), (73 / 50000000000000000000000000000000)⟩
def CA2_6_8I1R2MassTermLogWitness : LogWitness := ⟨-3, 11302880088511327856722246324597, 6250000000000000000000000000000⟩
def CA2_6_8I1R2MassTermLog : Ball := ⟨(-290422936932713047863097462883 / 195312500000000000000000000000), (42351647689 / 50000000000000000000000000000000)⟩
def CA2_6_8I1R2MassTerm : Ball := ⟨(33613984062502332850118446500137 / 100000000000000000000000000000000), (19147824033 / 100000000000000000000000000000000)⟩
def CA2_6_8I1R2H : Ball := ⟨(23238077018568157403873901867599 / 100000000000000000000000000000000), (21241137427 / 50000000000000000000000000000000)⟩
def CA2_6_8I1R3Entropy : Ball := ⟨(45866849567413292965853906750757 / 50000000000000000000000000000000), (24034877613 / 50000000000000000000000000000000)⟩
def CA2_6_8I1R3Mass : Ball := ⟨(12992758206544429763582252787509 / 25000000000000000000000000000000), (3 / 1562500000000000000000000000000)⟩
def CA2_6_8I1R3MassTermLogWitness : LogWitness := ⟨-1, 12992758206544429763582252787509, 12500000000000000000000000000000⟩
def CA2_6_8I1R3MassTermLog : Ball := ⟨(-65448368365785218025485415970023 / 100000000000000000000000000000000), (8470329547 / 20000000000000000000000000000000)⟩
def CA2_6_8I1R3MassTerm : Ball := ⟨(3401419300757994963401413575821 / 10000000000000000000000000000000), (22010588873 / 100000000000000000000000000000000)⟩
def CA2_6_8I1R3H : Ball := ⟨(7214938265905829537211709717913 / 12500000000000000000000000000000), (70080344099 / 100000000000000000000000000000000)⟩
def CA2_6_8I1R4Entropy : Ball := ⟨(11750646925601902058566610707749 / 20000000000000000000000000000000), (12311806081 / 50000000000000000000000000000000)⟩
def CA2_6_8I1R4Mass : Ball := ⟨(11302880088511327856722246324597 / 50000000000000000000000000000000), (141 / 100000000000000000000000000000000)⟩
def CA2_6_8I1R4MassTermLogWitness : LogWitness := ⟨-3, 11302880088511327856722246324597, 6250000000000000000000000000000⟩
def CA2_6_8I1R4MassTermLog : Ball := ⟨(-290422936932713047863097462883 / 195312500000000000000000000000), (21175823839 / 25000000000000000000000000000000)⟩
def CA2_6_8I1R4MassTerm : Ball := ⟨(33613984062502332850118446500137 / 100000000000000000000000000000000), (19147824021 / 100000000000000000000000000000000)⟩
def CA2_6_8I1R4H : Ball := ⟨(1571203160344198590169662939913 / 6250000000000000000000000000000), (43771436183 / 100000000000000000000000000000000)⟩
def CA2_6_8I1R5Entropy : Ball := ⟨(3757167752070174908295289419549 / 50000000000000000000000000000000), (691809971 / 25000000000000000000000000000000)⟩
def CA2_6_8I1R5Mass : Ball := ⟨(139327975552563848910158761633 / 10000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
def CA2_6_8I1R5MassTermLogWitness : LogWitness := ⟨-7, 139327975552563848910158761633, 78125000000000000000000000000⟩
def CA2_6_8I1R5MassTermLog : Ball := ⟨(-427350968183090038858467330187083 / 100000000000000000000000000000000), (42351647689 / 25000000000000000000000000000000)⟩
def CA2_6_8I1R5MassTerm : Ball := ⟨(5954194524737806017155259310491 / 100000000000000000000000000000000), (2360307811 / 100000000000000000000000000000000)⟩
def CA2_6_8I1R5H : Ball := ⟨(1560140979402543799435319528607 / 100000000000000000000000000000000), (1025509539 / 20000000000000000000000000000000)⟩
def CA2_6_8I1R6Entropy : Ball := ⟨(9381732985058963417343040983 / 6250000000000000000000000000000), (201157 / 390625000000000000000000000000)⟩
def CA2_6_8I1R6Mass : Ball := ⟨(15436371120660373983861206627 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def CA2_6_8I1R6MassTermLogWitness : LogWitness := ⟨-13, 15436371120660373983861206627, 12207031250000000000000000000⟩
def CA2_6_8I1R6MassTermLog : Ball := ⟨(-438809948952151772011195872757127 / 50000000000000000000000000000000), (29646157043 / 10000000000000000000000000000000)⟩
def CA2_6_8I1R6MassTerm : Ball := ⟨(135472664469268970989558269301 / 100000000000000000000000000000000), (22881481 / 50000000000000000000000000000000)⟩
def CA2_6_8I1R6H : Ball := ⟨(14635063291674443687930386427 / 100000000000000000000000000000000), (48629577 / 50000000000000000000000000000000)⟩
def CA2_6_8I1R7Entropy : Ball := ⟨0, 0⟩
def CA2_6_8I1R7Mass : Ball := ⟨0, 0⟩
def CA2_6_8I1R7MassTerm : Ball := .exact 0
def CA2_6_8I1R7H : Ball := ⟨0, 0⟩
def CA2_6_8I1R8Entropy : Ball := ⟨0, 0⟩
def CA2_6_8I1R8Mass : Ball := ⟨0, 0⟩
def CA2_6_8I1R8MassTerm : Ball := .exact 0
def CA2_6_8I1R8H : Ball := ⟨0, 0⟩
def CA2_6_8I1R9Entropy : Ball := ⟨0, 0⟩
def CA2_6_8I1R9Mass : Ball := ⟨0, 0⟩
def CA2_6_8I1R9MassTerm : Ball := .exact 0
def CA2_6_8I1R9H : Ball := ⟨0, 0⟩
def CA2_6_8I1R10Entropy : Ball := ⟨0, 0⟩
def CA2_6_8I1R10Mass : Ball := ⟨0, 0⟩
def CA2_6_8I1R10MassTerm : Ball := .exact 0
def CA2_6_8I1R10H : Ball := ⟨0, 0⟩
def CA2_6_8I1R11Entropy : Ball := ⟨0, 0⟩
def CA2_6_8I1R11Mass : Ball := ⟨0, 0⟩
def CA2_6_8I1R11MassTerm : Ball := .exact 0
def CA2_6_8I1R11H : Ball := ⟨0, 0⟩
def CA2_6_8I1R12Entropy : Ball := ⟨0, 0⟩
def CA2_6_8I1R12Mass : Ball := ⟨0, 0⟩
def CA2_6_8I1R12MassTerm : Ball := .exact 0
def CA2_6_8I1R12H : Ball := ⟨0, 0⟩
def CA2_6_8I1R13Entropy : Ball := ⟨0, 0⟩
def CA2_6_8I1R13Mass : Ball := ⟨0, 0⟩
def CA2_6_8I1R13MassTerm : Ball := .exact 0
def CA2_6_8I1R13H : Ball := ⟨0, 0⟩
def CA2_6_8I1R14Entropy : Ball := ⟨0, 0⟩
def CA2_6_8I1R14Mass : Ball := ⟨0, 0⟩
def CA2_6_8I1R14MassTerm : Ball := .exact 0
def CA2_6_8I1R14H : Ball := ⟨0, 0⟩
def CA2_6_8I1R15Entropy : Ball := ⟨0, 0⟩
def CA2_6_8I1R15Mass : Ball := ⟨0, 0⟩
def CA2_6_8I1R15MassTerm : Ball := .exact 0
def CA2_6_8I1R15H : Ball := ⟨0, 0⟩
def CA2_6_8I1R16Entropy : Ball := ⟨0, 0⟩
def CA2_6_8I1R16Mass : Ball := ⟨0, 0⟩
def CA2_6_8I1R16MassTerm : Ball := .exact 0
def CA2_6_8I1R16H : Ball := ⟨0, 0⟩
def CA2_6_8I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA2_6_8I1R0H
  | 1 => CA2_6_8I1R1H
  | 2 => CA2_6_8I1R2H
  | 3 => CA2_6_8I1R3H
  | 4 => CA2_6_8I1R4H
  | 5 => CA2_6_8I1R5H
  | 6 => CA2_6_8I1R6H
  | 7 => CA2_6_8I1R7H
  | 8 => CA2_6_8I1R8H
  | 9 => CA2_6_8I1R9H
  | 10 => CA2_6_8I1R10H
  | 11 => CA2_6_8I1R11H
  | 12 => CA2_6_8I1R12H
  | 13 => CA2_6_8I1R13H
  | 14 => CA2_6_8I1R14H
  | 15 => CA2_6_8I1R15H
  | 16 => CA2_6_8I1R16H
  | _ => (.exact 0)
def CA2_6_8I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 2, 6, 0 => Z2_6_0H1H
  | _, _, _ => (.exact 0)
def CA2_6_8I1Singleton : Ball := ⟨(37757724657937222513117 / 500000000000000000000000000000), (1487 / 25000000000000000000000000000000)⟩
def CA2_6_8I1Group : Ball := ⟨(54318682619917483587541367140529 / 50000000000000000000000000000000), (166666091037 / 100000000000000000000000000000000)⟩

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
def CA2_6_8I1H : Ball := ⟨(56710716895161352451896967881823 / 50000000000000000000000000000000), (490426241337 / 100000000000000000000000000000000)⟩

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
def CA2_6_8I2PairEntropy : Ball := ⟨(295145616783805131648839454279023 / 100000000000000000000000000000000), (23766934981 / 20000000000000000000000000000000)⟩
def CA2_6_8I2PairMass : Ball := ⟨(19999999999999999999999999999997 / 20000000000000000000000000000000), (807 / 100000000000000000000000000000000)⟩
def CA2_6_8I2PairMassTermLogWitness : LogWitness := ⟨-1, 19999999999999999999999999999997, 10000000000000000000000000000000⟩
def CA2_6_8I2PairMassTermLog : Ball := ⟨(-3 / 20000000000000000000000000000000), (42351648173 / 100000000000000000000000000000000)⟩
def CA2_6_8I2PairMassTerm : Ball := ⟨(3 / 20000000000000000000000000000000), (21175824087 / 50000000000000000000000000000000)⟩
def CA2_6_8I2PairH : Ball := ⟨(9223300524493910364026232946219 / 3125000000000000000000000000000), (161186323079 / 100000000000000000000000000000000)⟩

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
def CA2_6_8I2R0Entropy : Ball := ⟨(119700847339367931999913737 / 100000000000000000000000000000000), (1543 / 4000000000000000000000000000000)⟩
def CA2_6_8I2R0Mass : Ball := ⟨(7283242185896305552952829 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def CA2_6_8I2R0MassTermLogWitness : LogWitness := ⟨-24, 7283242185896305552952829, 5960464477539062500000000⟩
def CA2_6_8I2R0MassTermLog : Ball := ⟨(-821755231283971483508731748424759 / 50000000000000000000000000000000), (529409322223 / 100000000000000000000000000000000)⟩
def CA2_6_8I2R0MassTerm : Ball := ⟨(119700847339367931999913737 / 100000000000000000000000000000000), (1543 / 4000000000000000000000000000000)⟩
def CA2_6_8I2R0H : Ball := ⟨0, (1543 / 2000000000000000000000000000000)⟩
def CA2_6_8I2R1Entropy : Ball := ⟨(33502540808053205599377088871 / 50000000000000000000000000000000), (439241 / 2000000000000000000000000000000)⟩
def CA2_6_8I2R1Mass : Ball := ⟨(3241019566401678236465874989 / 50000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
def CA2_6_8I2R1MassTermLogWitness : LogWitness := ⟨-14, 3241019566401678236465874989, 3051757812500000000000000000⟩
def CA2_6_8I2R1MassTermLog : Ball := ⟨(-241097258077988760134087428289227 / 25000000000000000000000000000000), (317637416953 / 100000000000000000000000000000000)⟩
def CA2_6_8I2R1MassTerm : Ball := ⟨(12502414893384906351426921547 / 20000000000000000000000000000000), (20589421 / 100000000000000000000000000000000)⟩
def CA2_6_8I2R1H : Ball := ⟨(4493007149181879441619570007 / 100000000000000000000000000000000), (42551471 / 100000000000000000000000000000000)⟩
def CA2_6_8I2R2Entropy : Ball := ⟨(4897788760676158326718517941841 / 100000000000000000000000000000000), (351703941 / 20000000000000000000000000000000)⟩
def CA2_6_8I2R2Mass : Ball := ⟨(843614156404354023203443615967 / 100000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
def CA2_6_8I2R2MassTermLogWitness : LogWitness := ⟨-7, 843614156404354023203443615967, 781250000000000000000000000000⟩
def CA2_6_8I2R2MassTermLog : Ball := ⟨(-238761511778120627163225134528117 / 50000000000000000000000000000000), (84703295443 / 50000000000000000000000000000000)⟩
def CA2_6_8I2R2MassTerm : Ball := ⟨(4028451826810549400482286207711 / 100000000000000000000000000000000), (35728451 / 2500000000000000000000000000000)⟩
def CA2_6_8I2R2H : Ball := ⟨(86933693386560892623623173413 / 10000000000000000000000000000000), (637531549 / 20000000000000000000000000000000)⟩
def CA2_6_8I2R3Entropy : Ball := ⟨(23659782417700801331561596031563 / 50000000000000000000000000000000), (9506464617 / 50000000000000000000000000000000)⟩
def CA2_6_8I2R3Mass : Ball := ⟨(8348420043090712257433640806333 / 50000000000000000000000000000000), (23 / 25000000000000000000000000000000)⟩
def CA2_6_8I2R3MassTermLogWitness : LogWitness := ⟨-3, 8348420043090712257433640806333, 6250000000000000000000000000000⟩
def CA2_6_8I2R3MassTermLog : Ball := ⟨(-178995070086538463090810528272429 / 100000000000000000000000000000000), (42351647641 / 50000000000000000000000000000000)⟩
def CA2_6_8I2R3MassTerm : Ball := ⟨(466976884601526405198369062241 / 1562500000000000000000000000000), (7071386963 / 50000000000000000000000000000000)⟩
def CA2_6_8I2R3H : Ball := ⟨(8716522110451956365213786039851 / 50000000000000000000000000000000), (828892579 / 2500000000000000000000000000000)⟩
def CA2_6_8I2R4Entropy : Ball := ⟨(37794149076025064403696560009153 / 50000000000000000000000000000000), (38368461627 / 100000000000000000000000000000000)⟩
def CA2_6_8I2R4Mass : Ball := ⟨(48216067614404994882936565101297 / 100000000000000000000000000000000), (9 / 5000000000000000000000000000000)⟩
def CA2_6_8I2R4MassTermLogWitness : LogWitness := ⟨-2, 48216067614404994882936565101297, 25000000000000000000000000000000⟩
def CA2_6_8I2R4MassTermLog : Ball := ⟨(-72947786748534767477246031256031 / 100000000000000000000000000000000), (31763735711 / 50000000000000000000000000000000)⟩
def CA2_6_8I2R4MassTerm : Ball := ⟨(8793138545471372611168418006667 / 25000000000000000000000000000000), (30630448707 / 100000000000000000000000000000000)⟩
def CA2_6_8I2R4H : Ball := ⟨(20207871985082319181359723995819 / 50000000000000000000000000000000), (34499455167 / 50000000000000000000000000000000)⟩
def CA2_6_8I2R5Entropy : Ball := ⟨(14542026546320671912473665229847 / 50000000000000000000000000000000), (1162055613 / 10000000000000000000000000000000)⟩
def CA2_6_8I2R5Mass : Ball := ⟨(2215638108745201620908378579397 / 25000000000000000000000000000000), (7 / 12500000000000000000000000000000)⟩
def CA2_6_8I2R5MassTermLogWitness : LogWitness := ⟨-4, 2215638108745201620908378579397, 1562500000000000000000000000000⟩
def CA2_6_8I2R5MassTermLog : Ball := ⟨(-242333537764739794209388441775203 / 100000000000000000000000000000000), (52939559523 / 50000000000000000000000000000000)⟩
def CA2_6_8I2R5MassTerm : Ball := ⟨(21476936851944078875885785250807 / 100000000000000000000000000000000), (469179629 / 5000000000000000000000000000000)⟩
def CA2_6_8I2R5H : Ball := ⟨(7607116240697264949061545208887 / 100000000000000000000000000000000), (2100414871 / 10000000000000000000000000000000)⟩
def CA2_6_8I2R6Entropy : Ball := ⟨(1268493825755042281752827736733 / 100000000000000000000000000000000), (43083057 / 10000000000000000000000000000000)⟩
def CA2_6_8I2R6Mass : Ball := ⟨(10041119035149074821855904863 / 5000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def CA2_6_8I2R6MassTermLogWitness : LogWitness := ⟨-9, 10041119035149074821855904863, 9765625000000000000000000000⟩
def CA2_6_8I2R6MassTermLog : Ball := ⟨(-155262615641985741754365944816713 / 25000000000000000000000000000000), (42351648063 / 20000000000000000000000000000000)⟩
def CA2_6_8I2R6MassTerm : Ball := ⟨(1247208324295822018796855228129 / 100000000000000000000000000000000), (415291 / 97656250000000000000000000000)⟩
def CA2_6_8I2R6H : Ball := ⟨(5321375364805065738993127151 / 25000000000000000000000000000000), (428044277 / 50000000000000000000000000000000)⟩
def CA2_6_8I2R7Entropy : Ball := ⟨0, 0⟩
def CA2_6_8I2R7Mass : Ball := ⟨0, 0⟩
def CA2_6_8I2R7MassTerm : Ball := .exact 0
def CA2_6_8I2R7H : Ball := ⟨0, 0⟩
def CA2_6_8I2R8Entropy : Ball := ⟨0, 0⟩
def CA2_6_8I2R8Mass : Ball := ⟨0, 0⟩
def CA2_6_8I2R8MassTerm : Ball := .exact 0
def CA2_6_8I2R8H : Ball := ⟨0, 0⟩
def CA2_6_8I2R9Entropy : Ball := ⟨0, 0⟩
def CA2_6_8I2R9Mass : Ball := ⟨0, 0⟩
def CA2_6_8I2R9MassTerm : Ball := .exact 0
def CA2_6_8I2R9H : Ball := ⟨0, 0⟩
def CA2_6_8I2R10Entropy : Ball := ⟨0, 0⟩
def CA2_6_8I2R10Mass : Ball := ⟨0, 0⟩
def CA2_6_8I2R10MassTerm : Ball := .exact 0
def CA2_6_8I2R10H : Ball := ⟨0, 0⟩
def CA2_6_8I2R11Entropy : Ball := ⟨0, 0⟩
def CA2_6_8I2R11Mass : Ball := ⟨0, 0⟩
def CA2_6_8I2R11MassTerm : Ball := .exact 0
def CA2_6_8I2R11H : Ball := ⟨0, 0⟩
def CA2_6_8I2R12Entropy : Ball := ⟨0, 0⟩
def CA2_6_8I2R12Mass : Ball := ⟨0, 0⟩
def CA2_6_8I2R12MassTerm : Ball := .exact 0
def CA2_6_8I2R12H : Ball := ⟨0, 0⟩
def CA2_6_8I2R13Entropy : Ball := ⟨0, 0⟩
def CA2_6_8I2R13Mass : Ball := ⟨0, 0⟩
def CA2_6_8I2R13MassTerm : Ball := .exact 0
def CA2_6_8I2R13H : Ball := ⟨0, 0⟩
def CA2_6_8I2R14Entropy : Ball := ⟨0, 0⟩
def CA2_6_8I2R14Mass : Ball := ⟨0, 0⟩
def CA2_6_8I2R14MassTerm : Ball := .exact 0
def CA2_6_8I2R14H : Ball := ⟨0, 0⟩
def CA2_6_8I2R15Entropy : Ball := ⟨0, 0⟩
def CA2_6_8I2R15Mass : Ball := ⟨0, 0⟩
def CA2_6_8I2R15MassTerm : Ball := .exact 0
def CA2_6_8I2R15H : Ball := ⟨0, 0⟩
def CA2_6_8I2R16Entropy : Ball := ⟨0, 0⟩
def CA2_6_8I2R16Mass : Ball := ⟨0, 0⟩
def CA2_6_8I2R16MassTerm : Ball := .exact 0
def CA2_6_8I2R16H : Ball := ⟨0, 0⟩
def CA2_6_8I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA2_6_8I2R0H
  | 1 => CA2_6_8I2R1H
  | 2 => CA2_6_8I2R2H
  | 3 => CA2_6_8I2R3H
  | 4 => CA2_6_8I2R4H
  | 5 => CA2_6_8I2R5H
  | 6 => CA2_6_8I2R6H
  | 7 => CA2_6_8I2R7H
  | 8 => CA2_6_8I2R8H
  | 9 => CA2_6_8I2R9H
  | 10 => CA2_6_8I2R10H
  | 11 => CA2_6_8I2R11H
  | 12 => CA2_6_8I2R12H
  | 13 => CA2_6_8I2R13H
  | 14 => CA2_6_8I2R14H
  | 15 => CA2_6_8I2R15H
  | 16 => CA2_6_8I2R16H
  | _ => (.exact 0)
def CA2_6_8I2Singleton : Ball := ⟨(15172583866467906805800478596961 / 50000000000000000000000000000000), (25355929183 / 100000000000000000000000000000000)⟩
def CA2_6_8I2Group : Ball := ⟨(9669618760717564072244334628689 / 10000000000000000000000000000000), (152601066307 / 100000000000000000000000000000000)⟩

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
def CA2_6_8I2H : Ball := ⟨(25438310392363462550988190426307 / 25000000000000000000000000000000), (466388455693 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA2_7_7I0
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
def CA2_7_7I0Value (a : Fin 17) : ℝ := marginal (below (shape 2 7 7)) (fun u => (stageALaw (shape 2 7 7) u : ℝ)) ((Equiv.refl (Fin 3)) 0) a
def CA2_7_7I0Entropy : Ball := ⟨(103666587669993364878826396100727 / 100000000000000000000000000000000), (12668626213 / 20000000000000000000000000000000)⟩
def CA2_7_7I0Mass : Ball := ⟨(49999999999999999999999999999999 / 50000000000000000000000000000000), (103 / 50000000000000000000000000000000)⟩
def CA2_7_7I0MassTermLogWitness : LogWitness := ⟨-1, 49999999999999999999999999999999, 25000000000000000000000000000000⟩
def CA2_7_7I0MassTermLog : Ball := ⟨(-1 / 100000000000000000000000000000000), (10587911893 / 25000000000000000000000000000000)⟩
def CA2_7_7I0MassTerm : Ball := ⟨(1 / 100000000000000000000000000000000), (42351647573 / 100000000000000000000000000000000)⟩
def CA2_7_7I0H : Ball := ⟨(51833293834996682439413198050363 / 50000000000000000000000000000000), (52847389319 / 50000000000000000000000000000000)⟩

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
def CA2_7_7I1PairEntropy : Ball := ⟨(39759893300640491853024698056221 / 12500000000000000000000000000000), (15381496327 / 12500000000000000000000000000000)⟩
def CA2_7_7I1PairMass : Ball := ⟨(6249999999999999999999999999999 / 6250000000000000000000000000000), (9 / 1562500000000000000000000000000)⟩
def CA2_7_7I1PairMassTermLogWitness : LogWitness := ⟨-1, 6249999999999999999999999999999, 3125000000000000000000000000000⟩
def CA2_7_7I1PairMassTermLog : Ball := ⟨(-3 / 20000000000000000000000000000000), (21175823971 / 50000000000000000000000000000000)⟩
def CA2_7_7I1PairMassTerm : Ball := ⟨(3 / 20000000000000000000000000000000), (42351647943 / 100000000000000000000000000000000)⟩
def CA2_7_7I1PairH : Ball := ⟨(318079146405123934824197584449753 / 100000000000000000000000000000000), (165403618559 / 100000000000000000000000000000000)⟩

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
def CA2_7_7I1R0Entropy : Ball := ⟨(394363156944662384672781891 / 6250000000000000000000000000000), (521523 / 25000000000000000000000000000000)⟩
def CA2_7_7I1R0Mass : Ball := ⟨(518482090007836349659861879 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def CA2_7_7I1R0MassTermLogWitness : LogWitness := ⟨-18, 518482090007836349659861879, 381469726562500000000000000⟩
def CA2_7_7I1R0MassTermLog : Ball := ⟨(-1216977525881218296384070257089797 / 100000000000000000000000000000000), (201170517859 / 50000000000000000000000000000000)⟩
def CA2_7_7I1R0MassTerm : Ball := ⟨(394363156944662384672781891 / 6250000000000000000000000000000), (521523 / 25000000000000000000000000000000)⟩
def CA2_7_7I1R0H : Ball := ⟨0, (521523 / 12500000000000000000000000000000)⟩
def CA2_7_7I1R1Entropy : Ball := ⟨(481381006845902733106782874549 / 50000000000000000000000000000000), (166927251 / 50000000000000000000000000000000)⟩
def CA2_7_7I1R1Mass : Ball := ⟨(16422740291403525891109820993 / 12500000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def CA2_7_7I1R1MassTermLogWitness : LogWitness := ⟨-10, 16422740291403525891109820993, 12207031250000000000000000000⟩
def CA2_7_7I1R1MassTermLog : Ball := ⟨(-82935211822153354913022866703397 / 12500000000000000000000000000000), (232934065079 / 100000000000000000000000000000000)⟩
def CA2_7_7I1R1MassTerm : Ball := ⟨(871695004651368917354137361287 / 100000000000000000000000000000000), (306033293 / 100000000000000000000000000000000)⟩
def CA2_7_7I1R1H : Ball := ⟨(91067009040436548859428387811 / 100000000000000000000000000000000), (127977559 / 20000000000000000000000000000000)⟩
def CA2_7_7I1R2Entropy : Ball := ⟨(22281894091388814179056082332861 / 100000000000000000000000000000000), (333821083 / 4000000000000000000000000000000)⟩
def CA2_7_7I1R2Mass : Ball := ⟨(573365682191614768638905503871 / 10000000000000000000000000000000), (37 / 100000000000000000000000000000000)⟩
def CA2_7_7I1R2MassTermLogWitness : LogWitness := ⟨-5, 573365682191614768638905503871, 312500000000000000000000000000⟩
def CA2_7_7I1R2MassTermLog : Ball := ⟨(-71470416750031097905684090412837 / 25000000000000000000000000000000), (127054942743 / 100000000000000000000000000000000)⟩
def CA2_7_7I1R2MassTerm : Ball := ⟨(3278294740512047307358775649571 / 20000000000000000000000000000000), (7284894499 / 100000000000000000000000000000000)⟩
def CA2_7_7I1R2H : Ball := ⟨(2945210194414288821131102042503 / 50000000000000000000000000000000), (7815210787 / 50000000000000000000000000000000)⟩
def CA2_7_7I1R3Entropy : Ball := ⟨(1687120322098738908755082860537 / 2000000000000000000000000000000), (20448386167 / 50000000000000000000000000000000)⟩
def CA2_7_7I1R3Mass : Ball := ⟨(11033610693415654067533101632867 / 25000000000000000000000000000000), (59 / 50000000000000000000000000000000)⟩
def CA2_7_7I1R3MassTermLogWitness : LogWitness := ⟨-2, 11033610693415654067533101632867, 6250000000000000000000000000000⟩
def CA2_7_7I1R3MassTermLog : Ball := ⟨(-81792969309321574946819002094641 / 100000000000000000000000000000000), (15881867829 / 25000000000000000000000000000000)⟩
def CA2_7_7I1R3MassTerm : Ball := ⟨(18049435616350978685957054139607 / 50000000000000000000000000000000), (28037495571 / 100000000000000000000000000000000)⟩
def CA2_7_7I1R3H : Ball := ⟨(12064286218058747016460008686909 / 25000000000000000000000000000000), (13786853581 / 20000000000000000000000000000000)⟩
def CA2_7_7I1R4Entropy : Ball := ⟨(81128931506303862789148186832001 / 100000000000000000000000000000000), (4681889383 / 12500000000000000000000000000000)⟩
def CA2_7_7I1R4Mass : Ball := ⟨(11033610693415654067533101632867 / 25000000000000000000000000000000), (137 / 100000000000000000000000000000000)⟩
def CA2_7_7I1R4MassTermLogWitness : LogWitness := ⟨-2, 11033610693415654067533101632867, 6250000000000000000000000000000⟩
def CA2_7_7I1R4MassTermLog : Ball := ⟨(-81792969309321574946819002094641 / 100000000000000000000000000000000), (63527471359 / 100000000000000000000000000000000)⟩
def CA2_7_7I1R4MassTerm : Ball := ⟨(18049435616350978685957054139607 / 50000000000000000000000000000000), (5607499121 / 20000000000000000000000000000000)⟩
def CA2_7_7I1R4H : Ball := ⟨(45030060273601905417234078552787 / 100000000000000000000000000000000), (65492610669 / 100000000000000000000000000000000)⟩
def CA2_7_7I1R5Entropy : Ball := ⟨(5667951668003326490917762934093 / 25000000000000000000000000000000), (4461609599 / 50000000000000000000000000000000)⟩
def CA2_7_7I1R5Mass : Ball := ⟨(573365682191614768638905503871 / 10000000000000000000000000000000), (19 / 50000000000000000000000000000000)⟩
def CA2_7_7I1R5MassTermLogWitness : LogWitness := ⟨-5, 573365682191614768638905503871, 312500000000000000000000000000⟩
def CA2_7_7I1R5MassTermLog : Ball := ⟨(-71470416750031097905684090412837 / 25000000000000000000000000000000), (127054942761 / 100000000000000000000000000000000)⟩
def CA2_7_7I1R5MassTerm : Ball := ⟨(3278294740512047307358775649571 / 20000000000000000000000000000000), (3642447251 / 50000000000000000000000000000000)⟩
def CA2_7_7I1R5H : Ball := ⟨(6280332969453069426877173488517 / 100000000000000000000000000000000), (162081137 / 1000000000000000000000000000000)⟩
def CA2_7_7I1R6Entropy : Ball := ⟨(991324911239852086792671313709 / 100000000000000000000000000000000), (353019067 / 100000000000000000000000000000000)⟩
def CA2_7_7I1R6Mass : Ball := ⟨(26181701868319459768431725097 / 20000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def CA2_7_7I1R6MassTermLogWitness : LogWitness := ⟨-10, 26181701868319459768431725097, 19531250000000000000000000000⟩
def CA2_7_7I1R6MassTermLog : Ball := ⟨(-331921339386894290060685881598867 / 50000000000000000000000000000000), (29116758137 / 12500000000000000000000000000000)⟩
def CA2_7_7I1R6MassTerm : Ball := ⟨(43451327757804738615092393321 / 5000000000000000000000000000000), (304930553 / 100000000000000000000000000000000)⟩
def CA2_7_7I1R6H : Ball := ⟨(122298356083757314490823447289 / 100000000000000000000000000000000), (32897481 / 5000000000000000000000000000000)⟩
def CA2_7_7I1R7Entropy : Ball := ⟨(395497734704434699516257969 / 6250000000000000000000000000000), (129647 / 6250000000000000000000000000000)⟩
def CA2_7_7I1R7Mass : Ball := ⟨(61223223962159475536795967 / 12500000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def CA2_7_7I1R7MassTermLogWitness : LogWitness := ⟨-18, 61223223962159475536795967, 47683715820312500000000000⟩
def CA2_7_7I1R7MassTermLog : Ball := ⟨(-1222671260823137462223876793737441 / 100000000000000000000000000000000), (201170529159 / 50000000000000000000000000000000)⟩
def CA2_7_7I1R7MassTerm : Ball := ⟨(1497117528669416949537789903 / 25000000000000000000000000000000), (985317 / 50000000000000000000000000000000)⟩
def CA2_7_7I1R7H : Ball := ⟨(84873410148321848527241973 / 25000000000000000000000000000000), (2022493 / 50000000000000000000000000000000)⟩
def CA2_7_7I1R8Entropy : Ball := ⟨0, 0⟩
def CA2_7_7I1R8Mass : Ball := ⟨0, 0⟩
def CA2_7_7I1R8MassTerm : Ball := .exact 0
def CA2_7_7I1R8H : Ball := ⟨0, 0⟩
def CA2_7_7I1R9Entropy : Ball := ⟨0, 0⟩
def CA2_7_7I1R9Mass : Ball := ⟨0, 0⟩
def CA2_7_7I1R9MassTerm : Ball := .exact 0
def CA2_7_7I1R9H : Ball := ⟨0, 0⟩
def CA2_7_7I1R10Entropy : Ball := ⟨0, 0⟩
def CA2_7_7I1R10Mass : Ball := ⟨0, 0⟩
def CA2_7_7I1R10MassTerm : Ball := .exact 0
def CA2_7_7I1R10H : Ball := ⟨0, 0⟩
def CA2_7_7I1R11Entropy : Ball := ⟨0, 0⟩
def CA2_7_7I1R11Mass : Ball := ⟨0, 0⟩
def CA2_7_7I1R11MassTerm : Ball := .exact 0
def CA2_7_7I1R11H : Ball := ⟨0, 0⟩
def CA2_7_7I1R12Entropy : Ball := ⟨0, 0⟩
def CA2_7_7I1R12Mass : Ball := ⟨0, 0⟩
def CA2_7_7I1R12MassTerm : Ball := .exact 0
def CA2_7_7I1R12H : Ball := ⟨0, 0⟩
def CA2_7_7I1R13Entropy : Ball := ⟨0, 0⟩
def CA2_7_7I1R13Mass : Ball := ⟨0, 0⟩
def CA2_7_7I1R13MassTerm : Ball := .exact 0
def CA2_7_7I1R13H : Ball := ⟨0, 0⟩
def CA2_7_7I1R14Entropy : Ball := ⟨0, 0⟩
def CA2_7_7I1R14Mass : Ball := ⟨0, 0⟩
def CA2_7_7I1R14MassTerm : Ball := .exact 0
def CA2_7_7I1R14H : Ball := ⟨0, 0⟩
def CA2_7_7I1R15Entropy : Ball := ⟨0, 0⟩
def CA2_7_7I1R15Mass : Ball := ⟨0, 0⟩
def CA2_7_7I1R15MassTerm : Ball := .exact 0
def CA2_7_7I1R15H : Ball := ⟨0, 0⟩
def CA2_7_7I1R16Entropy : Ball := ⟨0, 0⟩
def CA2_7_7I1R16Mass : Ball := ⟨0, 0⟩
def CA2_7_7I1R16MassTerm : Ball := .exact 0
def CA2_7_7I1R16H : Ball := ⟨0, 0⟩
def CA2_7_7I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA2_7_7I1R0H
  | 1 => CA2_7_7I1R1H
  | 2 => CA2_7_7I1R2H
  | 3 => CA2_7_7I1R3H
  | 4 => CA2_7_7I1R4H
  | 5 => CA2_7_7I1R5H
  | 6 => CA2_7_7I1R6H
  | 7 => CA2_7_7I1R7H
  | 8 => CA2_7_7I1R8H
  | 9 => CA2_7_7I1R9H
  | 10 => CA2_7_7I1R10H
  | 11 => CA2_7_7I1R11H
  | 12 => CA2_7_7I1R12H
  | 13 => CA2_7_7I1R13H
  | 14 => CA2_7_7I1R14H
  | 15 => CA2_7_7I1R15H
  | 16 => CA2_7_7I1R16H
  | _ => (.exact 0)
def CA2_7_7I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 1, 7, 0 => Z1_7_0H1H
  | 2, 6, 0 => Z2_6_0H1H
  | _, _, _ => (.exact 0)
def CA2_7_7I1Singleton : Ball := ⟨(510743509163288709243151337 / 100000000000000000000000000000000), (19933 / 5000000000000000000000000000000)⟩
def CA2_7_7I1Group : Ball := ⟨(4226886964255699639666683793131 / 4000000000000000000000000000000), (167571867093 / 100000000000000000000000000000000)⟩

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
def CA2_7_7I1H : Ball := ⟨(106734798192338952840863394793203 / 100000000000000000000000000000000), (100109470549 / 20000000000000000000000000000000)⟩

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
def CA2_7_7I2PairEntropy : Ball := ⟨(7844896252681756294796751218143 / 2500000000000000000000000000000), (15209999259 / 12500000000000000000000000000000)⟩
def CA2_7_7I2PairMass : Ball := ⟨(12499999999999999999999999999997 / 12500000000000000000000000000000), (143 / 25000000000000000000000000000000)⟩
def CA2_7_7I2PairMassTermLogWitness : LogWitness := ⟨-1, 12499999999999999999999999999997, 6250000000000000000000000000000⟩
def CA2_7_7I2PairMassTermLog : Ball := ⟨(-3 / 12500000000000000000000000000000), (21175823969 / 50000000000000000000000000000000)⟩
def CA2_7_7I2PairMassTerm : Ball := ⟨(3 / 12500000000000000000000000000000), (42351647939 / 100000000000000000000000000000000)⟩
def CA2_7_7I2PairH : Ball := ⟨(4903060157926097684247969511339 / 1562500000000000000000000000000), (164031642011 / 100000000000000000000000000000000)⟩

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
def CA2_7_7I2R0Entropy : Ball := ⟨(3063334356907513434862083549 / 50000000000000000000000000000000), (2020217 / 100000000000000000000000000000000)⟩
def CA2_7_7I2R0Mass : Ball := ⟨(502109287941468832085436601 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def CA2_7_7I2R0MassTermLogWitness : LogWitness := ⟨-18, 502109287941468832085436601, 381469726562500000000000000⟩
def CA2_7_7I2R0MassTermLog : Ball := ⟨(-244037258857845153364503487992193 / 20000000000000000000000000000000), (50292631037 / 12500000000000000000000000000000)⟩
def CA2_7_7I2R0MassTerm : Ball := ⟨(3063334356907513434862083549 / 50000000000000000000000000000000), (2020217 / 100000000000000000000000000000000)⟩
def CA2_7_7I2R0H : Ball := ⟨0, (2020217 / 50000000000000000000000000000000)⟩
def CA2_7_7I2R1Entropy : Ball := ⟨(112914904520571858587520645573 / 12500000000000000000000000000000), (77530211 / 25000000000000000000000000000000)⟩
def CA2_7_7I2R1Mass : Ball := ⟨(61021004836896843510631497413 / 50000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
def CA2_7_7I2R1MassTermLogWitness : LogWitness := ⟨-10, 61021004836896843510631497413, 48828125000000000000000000000⟩
def CA2_7_7I2R1MassTermLog : Ball := ⟨(-83857001724005720628294388031371 / 12500000000000000000000000000000), (23293406379 / 10000000000000000000000000000000)⟩
def CA2_7_7I2R1MassTerm : Ball := ⟨(818726161249315203770880901103 / 100000000000000000000000000000000), (888367 / 312500000000000000000000000000)⟩
def CA2_7_7I2R1H : Ball := ⟨(84593074915259664929284263481 / 100000000000000000000000000000000), (148599571 / 25000000000000000000000000000000)⟩
def CA2_7_7I2R2Entropy : Ball := ⟨(2711217470013740754074505930069 / 12500000000000000000000000000000), (2011517339 / 25000000000000000000000000000000)⟩
def CA2_7_7I2R2Mass : Ball := ⟨(5522956558663634175499807649677 / 100000000000000000000000000000000), (9 / 25000000000000000000000000000000)⟩
def CA2_7_7I2R2MassTermLogWitness : LogWitness := ⟨-5, 5522956558663634175499807649677, 3125000000000000000000000000000⟩
def CA2_7_7I2R2MassTermLog : Ball := ⟨(-1158502744253016410078641519441 / 400000000000000000000000000000), (127054942749 / 100000000000000000000000000000000)⟩
def CA2_7_7I2R2MassTerm : Ball := ⟨(15995900824005039517055163864603 / 100000000000000000000000000000000), (3508594699 / 50000000000000000000000000000000)⟩
def CA2_7_7I2R2H : Ball := ⟨(5693838936104886515540883575949 / 100000000000000000000000000000000), (7531629377 / 50000000000000000000000000000000)⟩
def CA2_7_7I2R3Entropy : Ball := ⟨(7913344641104300020839317102751 / 10000000000000000000000000000000), (2335393329 / 6250000000000000000000000000000)⟩
def CA2_7_7I2R3Mass : Ball := ⟨(801871652470860403217686781329 / 2000000000000000000000000000000), (23 / 25000000000000000000000000000000)⟩
def CA2_7_7I2R3MassTermLogWitness : LogWitness := ⟨-2, 801871652470860403217686781329, 500000000000000000000000000000⟩
def CA2_7_7I2R3MassTermLog : Ball := ⟨(-18279077976160747981294955766949 / 20000000000000000000000000000000), (31763735639 / 50000000000000000000000000000000)⟩
def CA2_7_7I2R3MassTerm : Ball := ⟨(36643686155969324069048097794141 / 100000000000000000000000000000000), (2547043927 / 10000000000000000000000000000000)⟩
def CA2_7_7I2R3H : Ball := ⟨(42489760255073676139345073233369 / 100000000000000000000000000000000), (31418366267 / 50000000000000000000000000000000)⟩
def CA2_7_7I2R4Entropy : Ball := ⟨(14755923876197796826328822509719 / 25000000000000000000000000000000), (5617996369 / 20000000000000000000000000000000)⟩
def CA2_7_7I2R4Mass : Ball := ⟨(27865024072176842818050159770311 / 100000000000000000000000000000000), (67 / 100000000000000000000000000000000)⟩
def CA2_7_7I2R4MassTermLogWitness : LogWitness := ⟨-2, 27865024072176842818050159770311, 25000000000000000000000000000000⟩
def CA2_7_7I2R4MassTermLog : Ball := ⟨(-25555958021623995984140828497229 / 20000000000000000000000000000000), (63527471289 / 100000000000000000000000000000000)⟩
def CA2_7_7I2R4MassTerm : Ball := ⟨(178029346365023383066357772421 / 500000000000000000000000000000), (8850972627 / 50000000000000000000000000000000)⟩
def CA2_7_7I2R4H : Ball := ⟨(5854456557946627673010933888669 / 25000000000000000000000000000000), (45791927099 / 100000000000000000000000000000000)⟩
def CA2_7_7I2R5Entropy : Ball := ⟨(3986616181004158664681267932159 / 50000000000000000000000000000000), (1547220847 / 50000000000000000000000000000000)⟩
def CA2_7_7I2R5Mass : Ball := ⟨(31921049191380369372800029819 / 2000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def CA2_7_7I2R5MassTermLogWitness : LogWitness := ⟨-6, 31921049191380369372800029819, 31250000000000000000000000000⟩
def CA2_7_7I2R5MassTermLog : Ball := ⟨(-413763681809651446200549432929053 / 100000000000000000000000000000000), (148230766657 / 100000000000000000000000000000000)⟩
def CA2_7_7I2R5MassTerm : Ball := ⟨(1650971355081567343108674590919 / 25000000000000000000000000000000), (295730107 / 12500000000000000000000000000000)⟩
def CA2_7_7I2R5H : Ball := ⟨(684673470841023978463918750321 / 50000000000000000000000000000000), (109205651 / 2000000000000000000000000000000)⟩
def CA2_7_7I2R6Entropy : Ball := ⟨(74493376303584881935607169779 / 50000000000000000000000000000000), (2029121 / 4000000000000000000000000000000)⟩
def CA2_7_7I2R6Mass : Ball := ⟨(8476229158308448226948659597 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def CA2_7_7I2R6MassTermLogWitness : LogWitness := ⟨-13, 8476229158308448226948659597, 6103515625000000000000000000⟩
def CA2_7_7I2R6MassTermLog : Ball := ⟨(-108531407602892182777984611149741 / 12500000000000000000000000000000), (148230783477 / 50000000000000000000000000000000)⟩
def CA2_7_7I2R6MassTerm : Ball := ⟨(18398741634317878500727459383 / 12500000000000000000000000000000), (6282197 / 12500000000000000000000000000000)⟩
def CA2_7_7I2R6H : Ball := ⟨(898409766313367932697332247 / 50000000000000000000000000000000), (100985601 / 100000000000000000000000000000000)⟩
def CA2_7_7I2R7Entropy : Ball := ⟨0, 0⟩
def CA2_7_7I2R7Mass : Ball := ⟨0, 0⟩
def CA2_7_7I2R7MassTerm : Ball := .exact 0
def CA2_7_7I2R7H : Ball := ⟨0, 0⟩
def CA2_7_7I2R8Entropy : Ball := ⟨0, 0⟩
def CA2_7_7I2R8Mass : Ball := ⟨0, 0⟩
def CA2_7_7I2R8MassTerm : Ball := .exact 0
def CA2_7_7I2R8H : Ball := ⟨0, 0⟩
def CA2_7_7I2R9Entropy : Ball := ⟨0, 0⟩
def CA2_7_7I2R9Mass : Ball := ⟨0, 0⟩
def CA2_7_7I2R9MassTerm : Ball := .exact 0
def CA2_7_7I2R9H : Ball := ⟨0, 0⟩
def CA2_7_7I2R10Entropy : Ball := ⟨0, 0⟩
def CA2_7_7I2R10Mass : Ball := ⟨0, 0⟩
def CA2_7_7I2R10MassTerm : Ball := .exact 0
def CA2_7_7I2R10H : Ball := ⟨0, 0⟩
def CA2_7_7I2R11Entropy : Ball := ⟨0, 0⟩
def CA2_7_7I2R11Mass : Ball := ⟨0, 0⟩
def CA2_7_7I2R11MassTerm : Ball := .exact 0
def CA2_7_7I2R11H : Ball := ⟨0, 0⟩
def CA2_7_7I2R12Entropy : Ball := ⟨0, 0⟩
def CA2_7_7I2R12Mass : Ball := ⟨0, 0⟩
def CA2_7_7I2R12MassTerm : Ball := .exact 0
def CA2_7_7I2R12H : Ball := ⟨0, 0⟩
def CA2_7_7I2R13Entropy : Ball := ⟨0, 0⟩
def CA2_7_7I2R13Mass : Ball := ⟨0, 0⟩
def CA2_7_7I2R13MassTerm : Ball := .exact 0
def CA2_7_7I2R13H : Ball := ⟨0, 0⟩
def CA2_7_7I2R14Entropy : Ball := ⟨0, 0⟩
def CA2_7_7I2R14Mass : Ball := ⟨0, 0⟩
def CA2_7_7I2R14MassTerm : Ball := .exact 0
def CA2_7_7I2R14H : Ball := ⟨0, 0⟩
def CA2_7_7I2R15Entropy : Ball := ⟨0, 0⟩
def CA2_7_7I2R15Mass : Ball := ⟨0, 0⟩
def CA2_7_7I2R15MassTerm : Ball := .exact 0
def CA2_7_7I2R15H : Ball := ⟨0, 0⟩
def CA2_7_7I2R16Entropy : Ball := ⟨0, 0⟩
def CA2_7_7I2R16Mass : Ball := ⟨0, 0⟩
def CA2_7_7I2R16MassTerm : Ball := .exact 0
def CA2_7_7I2R16H : Ball := ⟨0, 0⟩
def CA2_7_7I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA2_7_7I2R0H
  | 1 => CA2_7_7I2R1H
  | 2 => CA2_7_7I2R2H
  | 3 => CA2_7_7I2R3H
  | 4 => CA2_7_7I2R4H
  | 5 => CA2_7_7I2R5H
  | 6 => CA2_7_7I2R6H
  | 7 => CA2_7_7I2R7H
  | 8 => CA2_7_7I2R8H
  | 9 => CA2_7_7I2R9H
  | 10 => CA2_7_7I2R10H
  | 11 => CA2_7_7I2R11H
  | 12 => CA2_7_7I2R12H
  | 13 => CA2_7_7I2R13H
  | 14 => CA2_7_7I2R14H
  | 15 => CA2_7_7I2R15H
  | 16 => CA2_7_7I2R16H
  | _ => (.exact 0)
def CA2_7_7I2Singleton : Ball := ⟨(3735549344201020389155168425783 / 12500000000000000000000000000000), (3138425543 / 12500000000000000000000000000000)⟩
def CA2_7_7I2Group : Ball := ⟨(823532456101625366543148449591 / 800000000000000000000000000000), (193698787 / 125000000000000000000000000000)⟩

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
def CA2_7_7I2H : Ball := ⟨(53956368040931955078041468163973 / 50000000000000000000000000000000), (473949701211 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA3_3_10I0
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
def CA3_3_10I0Value (a : Fin 17) : ℝ := marginal (below (shape 3 3 10)) (fun u => (stageALaw (shape 3 3 10) u : ℝ)) ((Equiv.refl (Fin 3)) 0) a
def CA3_3_10I0Entropy : Ball := ⟨(60351581144543783428797794684703 / 50000000000000000000000000000000), (36209504517 / 50000000000000000000000000000000)⟩
def CA3_3_10I0Mass : Ball := ⟨1, (23 / 10000000000000000000000000000000)⟩
def CA3_3_10I0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CA3_3_10I0MassTermLog : Ball := ⟨0, (2646977989 / 12500000000000000000000000000000)⟩
def CA3_3_10I0MassTerm : Ball := ⟨0, (21175823913 / 100000000000000000000000000000000)⟩
def CA3_3_10I0H : Ball := ⟨(60351581144543783428797794684703 / 50000000000000000000000000000000), (93594832947 / 100000000000000000000000000000000)⟩

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
def CA3_3_10I1PairEntropy : Ball := ⟨(70300841641986598335129862988459 / 25000000000000000000000000000000), (30173761973 / 25000000000000000000000000000000)⟩
def CA3_3_10I1PairMass : Ball := ⟨(25000000000000000000000000000001 / 25000000000000000000000000000000), (111 / 25000000000000000000000000000000)⟩
def CA3_3_10I1PairMassTermLogWitness : LogWitness := ⟨0, 25000000000000000000000000000001, 25000000000000000000000000000000⟩
def CA3_3_10I1PairMassTermLog : Ball := ⟨(1 / 25000000000000000000000000000000), (10587912063 / 50000000000000000000000000000000)⟩
def CA3_3_10I1PairMassTerm : Ball := ⟨(-1 / 25000000000000000000000000000000), (21175824127 / 100000000000000000000000000000000)⟩
def CA3_3_10I1PairH : Ball := ⟨(3515042082099329916756493149423 / 1250000000000000000000000000000), (141870872019 / 100000000000000000000000000000000)⟩

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
def CA3_3_10I1R0Entropy : Ball := ⟨(23711191063531435570046086221241 / 100000000000000000000000000000000), (5578249471 / 50000000000000000000000000000000)⟩
def CA3_3_10I1R0Mass : Ball := ⟨(2634253801667664169393495189081 / 25000000000000000000000000000000), (41 / 100000000000000000000000000000000)⟩
def CA3_3_10I1R0MassTermLogWitness : LogWitness := ⟨-4, 2634253801667664169393495189081, 1562500000000000000000000000000⟩
def CA3_3_10I1R0MassTermLog : Ball := ⟨(-14064224188767788938283650303749 / 6250000000000000000000000000000), (26469779701 / 25000000000000000000000000000000)⟩
def CA3_3_10I1R0MassTerm : Ball := ⟨(23711191063531435570046086221241 / 100000000000000000000000000000000), (5578249471 / 50000000000000000000000000000000)⟩
def CA3_3_10I1R0H : Ball := ⟨0, (5578249471 / 25000000000000000000000000000000)⟩
def CA3_3_10I1R1Entropy : Ball := ⟨(32023309006516069604011097727319 / 50000000000000000000000000000000), (8356612147 / 25000000000000000000000000000000)⟩
def CA3_3_10I1R1Mass : Ball := ⟨(9865746198332335830606504810919 / 25000000000000000000000000000000), (51 / 50000000000000000000000000000000)⟩
def CA3_3_10I1R1MassTermLogWitness : LogWitness := ⟨-2, 9865746198332335830606504810919, 6250000000000000000000000000000⟩
def CA3_3_10I1R1MassTermLog : Ball := ⟨(-9298070472677052150123757388541 / 10000000000000000000000000000000), (63527471307 / 100000000000000000000000000000000)⟩
def CA3_3_10I1R1MassTerm : Ball := ⟨(17916485042507767989356665939 / 48828125000000000000000000000), (25069836437 / 100000000000000000000000000000000)⟩
def CA3_3_10I1R1H : Ball := ⟨(13676828322988115182909871805783 / 50000000000000000000000000000000), (2339851401 / 4000000000000000000000000000000)⟩
def CA3_3_10I1R2Entropy : Ball := ⟨(38743699888758130439276589321029 / 50000000000000000000000000000000), (147229503 / 390625000000000000000000000000)⟩
def CA3_3_10I1R2Mass : Ball := ⟨(39462984793329343322426019243677 / 100000000000000000000000000000000), (133 / 100000000000000000000000000000000)⟩
def CA3_3_10I1R2MassTermLogWitness : LogWitness := ⟨-2, 39462984793329343322426019243677, 25000000000000000000000000000000⟩
def CA3_3_10I1R2MassTermLog : Ball := ⟨(-92980704726770521501237573885407 / 100000000000000000000000000000000), (31763735693 / 50000000000000000000000000000000)⟩
def CA3_3_10I1R2MassTerm : Ball := ⟨(17916485042507767989356665939 / 48828125000000000000000000000), (25069836497 / 100000000000000000000000000000000)⟩
def CA3_3_10I1R2H : Ball := ⟨(20397219205230176018175363399493 / 50000000000000000000000000000000), (12552117853 / 20000000000000000000000000000000)⟩
def CA3_3_10I1R3Entropy : Ball := ⟨(8940156715120176356471700930823 / 25000000000000000000000000000000), (3575039723 / 25000000000000000000000000000000)⟩
def CA3_3_10I1R3Mass : Ball := ⟨(2634253801667664169393495189081 / 25000000000000000000000000000000), (29 / 50000000000000000000000000000000)⟩
def CA3_3_10I1R3MassTermLogWitness : LogWitness := ⟨-4, 2634253801667664169393495189081, 1562500000000000000000000000000⟩
def CA3_3_10I1R3MassTermLog : Ball := ⟨(-14064224188767788938283650303749 / 6250000000000000000000000000000), (21175823793 / 20000000000000000000000000000000)⟩
def CA3_3_10I1R3MassTerm : Ball := ⟨(23711191063531435570046086221241 / 100000000000000000000000000000000), (11156498997 / 100000000000000000000000000000000)⟩
def CA3_3_10I1R3H : Ball := ⟨(12049435796949269855840717502051 / 100000000000000000000000000000000), (25456657889 / 100000000000000000000000000000000)⟩
def CA3_3_10I1R4Entropy : Ball := ⟨0, 0⟩
def CA3_3_10I1R4Mass : Ball := ⟨0, 0⟩
def CA3_3_10I1R4MassTerm : Ball := .exact 0
def CA3_3_10I1R4H : Ball := ⟨0, 0⟩
def CA3_3_10I1R5Entropy : Ball := ⟨0, 0⟩
def CA3_3_10I1R5Mass : Ball := ⟨0, 0⟩
def CA3_3_10I1R5MassTerm : Ball := .exact 0
def CA3_3_10I1R5H : Ball := ⟨0, 0⟩
def CA3_3_10I1R6Entropy : Ball := ⟨0, 0⟩
def CA3_3_10I1R6Mass : Ball := ⟨0, 0⟩
def CA3_3_10I1R6MassTerm : Ball := .exact 0
def CA3_3_10I1R6H : Ball := ⟨0, 0⟩
def CA3_3_10I1R7Entropy : Ball := ⟨0, 0⟩
def CA3_3_10I1R7Mass : Ball := ⟨0, 0⟩
def CA3_3_10I1R7MassTerm : Ball := .exact 0
def CA3_3_10I1R7H : Ball := ⟨0, 0⟩
def CA3_3_10I1R8Entropy : Ball := ⟨0, 0⟩
def CA3_3_10I1R8Mass : Ball := ⟨0, 0⟩
def CA3_3_10I1R8MassTerm : Ball := .exact 0
def CA3_3_10I1R8H : Ball := ⟨0, 0⟩
def CA3_3_10I1R9Entropy : Ball := ⟨0, 0⟩
def CA3_3_10I1R9Mass : Ball := ⟨0, 0⟩
def CA3_3_10I1R9MassTerm : Ball := .exact 0
def CA3_3_10I1R9H : Ball := ⟨0, 0⟩
def CA3_3_10I1R10Entropy : Ball := ⟨0, 0⟩
def CA3_3_10I1R10Mass : Ball := ⟨0, 0⟩
def CA3_3_10I1R10MassTerm : Ball := .exact 0
def CA3_3_10I1R10H : Ball := ⟨0, 0⟩
def CA3_3_10I1R11Entropy : Ball := ⟨0, 0⟩
def CA3_3_10I1R11Mass : Ball := ⟨0, 0⟩
def CA3_3_10I1R11MassTerm : Ball := .exact 0
def CA3_3_10I1R11H : Ball := ⟨0, 0⟩
def CA3_3_10I1R12Entropy : Ball := ⟨0, 0⟩
def CA3_3_10I1R12Mass : Ball := ⟨0, 0⟩
def CA3_3_10I1R12MassTerm : Ball := .exact 0
def CA3_3_10I1R12H : Ball := ⟨0, 0⟩
def CA3_3_10I1R13Entropy : Ball := ⟨0, 0⟩
def CA3_3_10I1R13Mass : Ball := ⟨0, 0⟩
def CA3_3_10I1R13MassTerm : Ball := .exact 0
def CA3_3_10I1R13H : Ball := ⟨0, 0⟩
def CA3_3_10I1R14Entropy : Ball := ⟨0, 0⟩
def CA3_3_10I1R14Mass : Ball := ⟨0, 0⟩
def CA3_3_10I1R14MassTerm : Ball := .exact 0
def CA3_3_10I1R14H : Ball := ⟨0, 0⟩
def CA3_3_10I1R15Entropy : Ball := ⟨0, 0⟩
def CA3_3_10I1R15Mass : Ball := ⟨0, 0⟩
def CA3_3_10I1R15MassTerm : Ball := .exact 0
def CA3_3_10I1R15H : Ball := ⟨0, 0⟩
def CA3_3_10I1R16Entropy : Ball := ⟨0, 0⟩
def CA3_3_10I1R16Mass : Ball := ⟨0, 0⟩
def CA3_3_10I1R16MassTerm : Ball := .exact 0
def CA3_3_10I1R16H : Ball := ⟨0, 0⟩
def CA3_3_10I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA3_3_10I1R0H
  | 1 => CA3_3_10I1R1H
  | 2 => CA3_3_10I1R2H
  | 3 => CA3_3_10I1R3H
  | 4 => CA3_3_10I1R4H
  | 5 => CA3_3_10I1R5H
  | 6 => CA3_3_10I1R6H
  | 7 => CA3_3_10I1R7H
  | 8 => CA3_3_10I1R8H
  | 9 => CA3_3_10I1R9H
  | 10 => CA3_3_10I1R10H
  | 11 => CA3_3_10I1R11H
  | 12 => CA3_3_10I1R12H
  | 13 => CA3_3_10I1R13H
  | 14 => CA3_3_10I1R14H
  | 15 => CA3_3_10I1R15H
  | 16 => CA3_3_10I1R16H
  | _ => (.exact 0)
def CA3_3_10I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | _, _, _ => (.exact 0)
def CA3_3_10I1Singleton : Ball := ⟨0, 0⟩
def CA3_3_10I1Group : Ball := ⟨(80197530853385852258011187912603 / 100000000000000000000000000000000), (169026530063 / 100000000000000000000000000000000)⟩

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
def CA3_3_10I1H : Ball := ⟨(60404152430587344412248538064317 / 50000000000000000000000000000000), (95984786429 / 20000000000000000000000000000000)⟩

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
def CA3_3_10I2PairEntropy : Ball := ⟨(14067330277652996114649336562101 / 5000000000000000000000000000000), (2407132681 / 2000000000000000000000000000000)⟩
def CA3_3_10I2PairMass : Ball := ⟨(10000000000000000000000000000001 / 10000000000000000000000000000000), (291 / 50000000000000000000000000000000)⟩
def CA3_3_10I2PairMassTermLogWitness : LogWitness := ⟨0, 10000000000000000000000000000001, 10000000000000000000000000000000⟩
def CA3_3_10I2PairMassTermLog : Ball := ⟨(1 / 10000000000000000000000000000000), (2646978033 / 12500000000000000000000000000000)⟩
def CA3_3_10I2PairMassTerm : Ball := ⟨(-1 / 10000000000000000000000000000000), (4235164853 / 20000000000000000000000000000000)⟩
def CA3_3_10I2PairH : Ball := ⟨(28134660555305992229298673124203 / 10000000000000000000000000000000), (28306491663 / 20000000000000000000000000000000)⟩

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
def CA3_3_10I2R0Entropy : Ball := ⟨0, 0⟩
def CA3_3_10I2R0Mass : Ball := ⟨0, 0⟩
def CA3_3_10I2R0MassTerm : Ball := .exact 0
def CA3_3_10I2R0H : Ball := ⟨0, 0⟩
def CA3_3_10I2R1Entropy : Ball := ⟨0, 0⟩
def CA3_3_10I2R1Mass : Ball := ⟨0, 0⟩
def CA3_3_10I2R1MassTerm : Ball := .exact 0
def CA3_3_10I2R1H : Ball := ⟨0, 0⟩
def CA3_3_10I2R2Entropy : Ball := ⟨(27045461557809082964663176751 / 100000000000000000000000000000000), (4534111 / 50000000000000000000000000000000)⟩
def CA3_3_10I2R2Mass : Ball := ⟨(92807394604080247176410297 / 4000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
def CA3_3_10I2R2MassTermLogWitness : LogWitness := ⟨-16, 92807394604080247176410297, 61035156250000000000000000⟩
def CA3_3_10I2R2MassTermLog : Ball := ⟨(-106712785992329267025334324179899 / 10000000000000000000000000000000), (359989218111 / 100000000000000000000000000000000)⟩
def CA3_3_10I2R2MassTerm : Ball := ⟨(6189834774306793376050655379 / 25000000000000000000000000000000), (8352469 / 100000000000000000000000000000000)⟩
def CA3_3_10I2R2H : Ball := ⟨(457224492116381892092111047 / 20000000000000000000000000000000), (17420691 / 100000000000000000000000000000000)⟩
def CA3_3_10I2R3Entropy : Ball := ⟨(441507539289100052411255702259 / 10000000000000000000000000000000), (819107733 / 50000000000000000000000000000000)⟩
def CA3_3_10I2R3Mass : Ball := ⟨(37572344183526581445090500591 / 5000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
def CA3_3_10I2R3MassTermLogWitness : LogWitness := ⟨-8, 37572344183526581445090500591, 19531250000000000000000000000⟩
def CA3_3_10I2R3MassTermLog : Ball := ⟨(-4890924938686978144743451349959 / 1000000000000000000000000000000), (95291207239 / 50000000000000000000000000000000)⟩
def CA3_3_10I2R3MassTerm : Ball := ⟨(459408787930351963191356758269 / 12500000000000000000000000000000), (44753927 / 3125000000000000000000000000000)⟩
def CA3_3_10I2R3H : Ball := ⟨(369902544724092409290851478219 / 50000000000000000000000000000000), (307034113 / 10000000000000000000000000000000)⟩
def CA3_3_10I2R4Entropy : Ball := ⟨(25423457300403477301361022683899 / 50000000000000000000000000000000), (21805058183 / 100000000000000000000000000000000)⟩
def CA3_3_10I2R4Mass : Ball := ⟨(1065537248148362328083124989429 / 5000000000000000000000000000000), (103 / 100000000000000000000000000000000)⟩
def CA3_3_10I2R4MassTermLogWitness : LogWitness := ⟨-3, 1065537248148362328083124989429, 625000000000000000000000000000⟩
def CA3_3_10I2R4MassTermLog : Ball := ⟨(-154595878211378320822588544937459 / 100000000000000000000000000000000), (16940659043 / 20000000000000000000000000000000)⟩
def CA3_3_10I2R4MassTerm : Ball := ⟨(2059095833055392783245717986463 / 6250000000000000000000000000000), (18050903379 / 100000000000000000000000000000000)⟩
def CA3_3_10I2R4H : Ball := ⟨(1790138127192067007079055758439 / 10000000000000000000000000000000), (19927980781 / 50000000000000000000000000000000)⟩
def CA3_3_10I2R5Entropy : Ball := ⟨(1504621729947227692373911410219 / 2000000000000000000000000000000), (505106357 / 1250000000000000000000000000000)⟩
def CA3_3_10I2R5Mass : Ball := ⟨(22940217358767125771206291343619 / 50000000000000000000000000000000), (13 / 12500000000000000000000000000000)⟩
def CA3_3_10I2R5MassTermLogWitness : LogWitness := ⟨-2, 22940217358767125771206291343619, 12500000000000000000000000000000⟩
def CA3_3_10I2R5MassTermLog : Ball := ⟨(-77913141867298139311620297031129 / 100000000000000000000000000000000), (2541098851 / 4000000000000000000000000000000)⟩
def CA3_3_10I2R5MassTerm : Ball := ⟨(17873444095402784870395903805863 / 50000000000000000000000000000000), (7286670017 / 25000000000000000000000000000000)⟩
def CA3_3_10I2R5H : Ball := ⟨(4935524788319476859737970362403 / 12500000000000000000000000000000), (17388797157 / 25000000000000000000000000000000)⟩
def CA3_3_10I2R6Entropy : Ball := ⟨(25476223292161548136787815053549 / 100000000000000000000000000000000), (372916513 / 3125000000000000000000000000000)⟩
def CA3_3_10I2R6Mass : Ball := ⟨(11023083640349972174887924565559 / 100000000000000000000000000000000), (17 / 50000000000000000000000000000000)⟩
def CA3_3_10I2R6MassTermLogWitness : LogWitness := ⟨-4, 11023083640349972174887924565559, 6250000000000000000000000000000⟩
def CA3_3_10I2R6MassTermLog : Ball := ⟨(-1102589299616463351266717354721 / 500000000000000000000000000000), (105879118723 / 100000000000000000000000000000000)⟩
def CA3_3_10I2R6MassTerm : Ball := ⟨(2430786814125434203440530503883 / 10000000000000000000000000000000), (1167114389 / 10000000000000000000000000000000)⟩
def CA3_3_10I2R6H : Ball := ⟨(1168355150907206102382510014719 / 100000000000000000000000000000000), (11802236153 / 50000000000000000000000000000000)⟩
def CA3_3_10I2R7Entropy : Ball := ⟨0, 0⟩
def CA3_3_10I2R7Mass : Ball := ⟨0, 0⟩
def CA3_3_10I2R7MassTerm : Ball := .exact 0
def CA3_3_10I2R7H : Ball := ⟨0, 0⟩
def CA3_3_10I2R8Entropy : Ball := ⟨0, 0⟩
def CA3_3_10I2R8Mass : Ball := ⟨0, 0⟩
def CA3_3_10I2R8MassTerm : Ball := .exact 0
def CA3_3_10I2R8H : Ball := ⟨0, 0⟩
def CA3_3_10I2R9Entropy : Ball := ⟨0, 0⟩
def CA3_3_10I2R9Mass : Ball := ⟨0, 0⟩
def CA3_3_10I2R9MassTerm : Ball := .exact 0
def CA3_3_10I2R9H : Ball := ⟨0, 0⟩
def CA3_3_10I2R10Entropy : Ball := ⟨0, 0⟩
def CA3_3_10I2R10Mass : Ball := ⟨0, 0⟩
def CA3_3_10I2R10MassTerm : Ball := .exact 0
def CA3_3_10I2R10H : Ball := ⟨0, 0⟩
def CA3_3_10I2R11Entropy : Ball := ⟨0, 0⟩
def CA3_3_10I2R11Mass : Ball := ⟨0, 0⟩
def CA3_3_10I2R11MassTerm : Ball := .exact 0
def CA3_3_10I2R11H : Ball := ⟨0, 0⟩
def CA3_3_10I2R12Entropy : Ball := ⟨0, 0⟩
def CA3_3_10I2R12Mass : Ball := ⟨0, 0⟩
def CA3_3_10I2R12MassTerm : Ball := .exact 0
def CA3_3_10I2R12H : Ball := ⟨0, 0⟩
def CA3_3_10I2R13Entropy : Ball := ⟨0, 0⟩
def CA3_3_10I2R13Mass : Ball := ⟨0, 0⟩
def CA3_3_10I2R13MassTerm : Ball := .exact 0
def CA3_3_10I2R13H : Ball := ⟨0, 0⟩
def CA3_3_10I2R14Entropy : Ball := ⟨0, 0⟩
def CA3_3_10I2R14Mass : Ball := ⟨0, 0⟩
def CA3_3_10I2R14MassTerm : Ball := .exact 0
def CA3_3_10I2R14H : Ball := ⟨0, 0⟩
def CA3_3_10I2R15Entropy : Ball := ⟨0, 0⟩
def CA3_3_10I2R15Mass : Ball := ⟨0, 0⟩
def CA3_3_10I2R15MassTerm : Ball := .exact 0
def CA3_3_10I2R15H : Ball := ⟨0, 0⟩
def CA3_3_10I2R16Entropy : Ball := ⟨0, 0⟩
def CA3_3_10I2R16Mass : Ball := ⟨0, 0⟩
def CA3_3_10I2R16MassTerm : Ball := .exact 0
def CA3_3_10I2R16H : Ball := ⟨0, 0⟩
def CA3_3_10I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA3_3_10I2R0H
  | 1 => CA3_3_10I2R1H
  | 2 => CA3_3_10I2R2H
  | 3 => CA3_3_10I2R3H
  | 4 => CA3_3_10I2R4H
  | 5 => CA3_3_10I2R5H
  | 6 => CA3_3_10I2R6H
  | 7 => CA3_3_10I2R7H
  | 8 => CA3_3_10I2R8H
  | 9 => CA3_3_10I2R9H
  | 10 => CA3_3_10I2R10H
  | 11 => CA3_3_10I2R11H
  | 12 => CA3_3_10I2R12H
  | 13 => CA3_3_10I2R13H
  | 14 => CA3_3_10I2R14H
  | 15 => CA3_3_10I2R15H
  | 16 => CA3_3_10I2R16H
  | _ => (.exact 0)
def CA3_3_10I2Singleton : Ball := ⟨(24142252657962249439325503564723 / 100000000000000000000000000000000), (9777366223 / 50000000000000000000000000000000)⟩
def CA3_3_10I2Group : Ball := ⟨(83438278599254707218444497574729 / 100000000000000000000000000000000), (155658116763 / 100000000000000000000000000000000)⟩

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
def CA3_3_10I2H : Ball := ⟨(28617512088637626964024434023143 / 25000000000000000000000000000000), (452848691841 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA3_4_9I0
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
def CA3_4_9I0Value (a : Fin 17) : ℝ := marginal (below (shape 3 4 9)) (fun u => (stageALaw (shape 3 4 9) u : ℝ)) ((Equiv.refl (Fin 3)) 0) a
def CA3_4_9I0Entropy : Ball := ⟨(6021628344741324854798471858789 / 5000000000000000000000000000000), (36166466363 / 50000000000000000000000000000000)⟩
def CA3_4_9I0Mass : Ball := ⟨1, (117 / 50000000000000000000000000000000)⟩
def CA3_4_9I0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CA3_4_9I0MassTermLog : Ball := ⟨0, (5293955979 / 25000000000000000000000000000000)⟩
def CA3_4_9I0MassTerm : Ball := ⟨0, (21175823917 / 100000000000000000000000000000000)⟩
def CA3_4_9I0H : Ball := ⟨(6021628344741324854798471858789 / 5000000000000000000000000000000), (93508756643 / 100000000000000000000000000000000)⟩

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
def CA3_4_9I1PairEntropy : Ball := ⟨(15572244029986886191407704878953 / 5000000000000000000000000000000), (12991587121 / 10000000000000000000000000000000)⟩
def CA3_4_9I1PairMass : Ball := ⟨(49999999999999999999999999999999 / 50000000000000000000000000000000), (67 / 12500000000000000000000000000000)⟩
def CA3_4_9I1PairMassTermLogWitness : LogWitness := ⟨-1, 49999999999999999999999999999999, 25000000000000000000000000000000⟩
def CA3_4_9I1PairMassTermLog : Ball := ⟨(-1 / 100000000000000000000000000000000), (21175823951 / 50000000000000000000000000000000)⟩
def CA3_4_9I1PairMassTerm : Ball := ⟨(1 / 100000000000000000000000000000000), (42351647903 / 100000000000000000000000000000000)⟩
def CA3_4_9I1PairH : Ball := ⟨(311444880599737723828154097579059 / 100000000000000000000000000000000), (172267519113 / 100000000000000000000000000000000)⟩

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
def CA3_4_9I1R0Entropy : Ball := ⟨(9445175467426299895193937865993 / 100000000000000000000000000000000), (3829449579 / 100000000000000000000000000000000)⟩
def CA3_4_9I1R0Mass : Ball := ⟨(129171885906327642982780946153 / 5000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def CA3_4_9I1R0MassTermLogWitness : LogWitness := ⟨-6, 129171885906327642982780946153, 78125000000000000000000000000⟩
def CA3_4_9I1R0MassTermLog : Ball := ⟨(-45700615313631960038590227361989 / 12500000000000000000000000000000), (148230766323 / 100000000000000000000000000000000)⟩
def CA3_4_9I1R0MassTerm : Ball := ⟨(9445175467426299895193937865993 / 100000000000000000000000000000000), (3829449579 / 100000000000000000000000000000000)⟩
def CA3_4_9I1R0H : Ball := ⟨0, (3829449579 / 50000000000000000000000000000000)⟩
def CA3_4_9I1R1Entropy : Ball := ⟨(24936694229921582604765072396319 / 50000000000000000000000000000000), (12234701683 / 50000000000000000000000000000000)⟩
def CA3_4_9I1R1Mass : Ball := ⟨(11555348898300423334234614023867 / 50000000000000000000000000000000), (11 / 12500000000000000000000000000000)⟩
def CA3_4_9I1R1MassTermLogWitness : LogWitness := ⟨-3, 11555348898300423334234614023867, 6250000000000000000000000000000⟩
def CA3_4_9I1R1MassTermLog : Ball := ⟨(-146487456758383475525259968672667 / 100000000000000000000000000000000), (84703295113 / 100000000000000000000000000000000)⟩
def CA3_4_9I1R1MassTerm : Ball := ⟨(33854273441356347927102503160183 / 100000000000000000000000000000000), (19575522687 / 100000000000000000000000000000000)⟩
def CA3_4_9I1R1H : Ball := ⟨(3203823003697363456485528326491 / 20000000000000000000000000000000), (44044926053 / 100000000000000000000000000000000)⟩
def CA3_4_9I1R2Entropy : Ball := ⟨(16999623191906052622317255483903 / 20000000000000000000000000000000), (19761347611 / 50000000000000000000000000000000)⟩
def CA3_4_9I1R2Mass : Ball := ⟨(48611728970545200943750306058413 / 100000000000000000000000000000000), (149 / 100000000000000000000000000000000)⟩
def CA3_4_9I1R2MassTermLogWitness : LogWitness := ⟨-2, 48611728970545200943750306058413, 25000000000000000000000000000000⟩
def CA3_4_9I1R2MassTermLog : Ball := ⟨(-14426106947124012552068567061067 / 20000000000000000000000000000000), (12705494271 / 20000000000000000000000000000000)⟩
def CA3_4_9I1R2MassTerm : Ball := ⟨(35063900050684587314112502652597 / 100000000000000000000000000000000), (6176360461 / 20000000000000000000000000000000)⟩
def CA3_4_9I1R2H : Ball := ⟨(24967107954422837898736887383459 / 50000000000000000000000000000000), (70404497527 / 100000000000000000000000000000000)⟩
def CA3_4_9I1R3Entropy : Ball := ⟨(14958602496200283997491536551753 / 25000000000000000000000000000000), (2635092969 / 10000000000000000000000000000000)⟩
def CA3_4_9I1R3Mass : Ball := ⟨(11555348898300423334234614023867 / 50000000000000000000000000000000), (3 / 3125000000000000000000000000000)⟩
def CA3_4_9I1R3MassTermLogWitness : LogWitness := ⟨-3, 11555348898300423334234614023867, 6250000000000000000000000000000⟩
def CA3_4_9I1R3MassTermLog : Ball := ⟨(-146487456758383475525259968672667 / 100000000000000000000000000000000), (84703295147 / 100000000000000000000000000000000)⟩
def CA3_4_9I1R3MassTerm : Ball := ⟨(33854273441356347927102503160183 / 100000000000000000000000000000000), (9787761353 / 50000000000000000000000000000000)⟩
def CA3_4_9I1R3H : Ball := ⟨(25980136543444788062863643046829 / 100000000000000000000000000000000), (11481613099 / 25000000000000000000000000000000)⟩
def CA3_4_9I1R4Entropy : Ball := ⟨(12402753196542864637174879970159 / 100000000000000000000000000000000), (4484363821 / 100000000000000000000000000000000)⟩
def CA3_4_9I1R4Mass : Ball := ⟨(1291718859063276429827809461529 / 50000000000000000000000000000000), (1 / 4000000000000000000000000000000)⟩
def CA3_4_9I1R4MassTermLogWitness : LogWitness := ⟨-6, 1291718859063276429827809461529, 781250000000000000000000000000⟩
def CA3_4_9I1R4MassTermLog : Ball := ⟨(-36560492250905568030872181889599 / 10000000000000000000000000000000), (37057691687 / 25000000000000000000000000000000)⟩
def CA3_4_9I1R4MassTerm : Ball := ⟨(2361293866856574973798484466497 / 25000000000000000000000000000000), (382944963 / 10000000000000000000000000000000)⟩
def CA3_4_9I1R4H : Ball := ⟨(2957577729116564741980942104171 / 100000000000000000000000000000000), (8313813451 / 100000000000000000000000000000000)⟩
def CA3_4_9I1R5Entropy : Ball := ⟨0, 0⟩
def CA3_4_9I1R5Mass : Ball := ⟨0, 0⟩
def CA3_4_9I1R5MassTerm : Ball := .exact 0
def CA3_4_9I1R5H : Ball := ⟨0, 0⟩
def CA3_4_9I1R6Entropy : Ball := ⟨0, 0⟩
def CA3_4_9I1R6Mass : Ball := ⟨0, 0⟩
def CA3_4_9I1R6MassTerm : Ball := .exact 0
def CA3_4_9I1R6H : Ball := ⟨0, 0⟩
def CA3_4_9I1R7Entropy : Ball := ⟨0, 0⟩
def CA3_4_9I1R7Mass : Ball := ⟨0, 0⟩
def CA3_4_9I1R7MassTerm : Ball := .exact 0
def CA3_4_9I1R7H : Ball := ⟨0, 0⟩
def CA3_4_9I1R8Entropy : Ball := ⟨0, 0⟩
def CA3_4_9I1R8Mass : Ball := ⟨0, 0⟩
def CA3_4_9I1R8MassTerm : Ball := .exact 0
def CA3_4_9I1R8H : Ball := ⟨0, 0⟩
def CA3_4_9I1R9Entropy : Ball := ⟨0, 0⟩
def CA3_4_9I1R9Mass : Ball := ⟨0, 0⟩
def CA3_4_9I1R9MassTerm : Ball := .exact 0
def CA3_4_9I1R9H : Ball := ⟨0, 0⟩
def CA3_4_9I1R10Entropy : Ball := ⟨0, 0⟩
def CA3_4_9I1R10Mass : Ball := ⟨0, 0⟩
def CA3_4_9I1R10MassTerm : Ball := .exact 0
def CA3_4_9I1R10H : Ball := ⟨0, 0⟩
def CA3_4_9I1R11Entropy : Ball := ⟨0, 0⟩
def CA3_4_9I1R11Mass : Ball := ⟨0, 0⟩
def CA3_4_9I1R11MassTerm : Ball := .exact 0
def CA3_4_9I1R11H : Ball := ⟨0, 0⟩
def CA3_4_9I1R12Entropy : Ball := ⟨0, 0⟩
def CA3_4_9I1R12Mass : Ball := ⟨0, 0⟩
def CA3_4_9I1R12MassTerm : Ball := .exact 0
def CA3_4_9I1R12H : Ball := ⟨0, 0⟩
def CA3_4_9I1R13Entropy : Ball := ⟨0, 0⟩
def CA3_4_9I1R13Mass : Ball := ⟨0, 0⟩
def CA3_4_9I1R13MassTerm : Ball := .exact 0
def CA3_4_9I1R13H : Ball := ⟨0, 0⟩
def CA3_4_9I1R14Entropy : Ball := ⟨0, 0⟩
def CA3_4_9I1R14Mass : Ball := ⟨0, 0⟩
def CA3_4_9I1R14MassTerm : Ball := .exact 0
def CA3_4_9I1R14H : Ball := ⟨0, 0⟩
def CA3_4_9I1R15Entropy : Ball := ⟨0, 0⟩
def CA3_4_9I1R15Mass : Ball := ⟨0, 0⟩
def CA3_4_9I1R15MassTerm : Ball := .exact 0
def CA3_4_9I1R15H : Ball := ⟨0, 0⟩
def CA3_4_9I1R16Entropy : Ball := ⟨0, 0⟩
def CA3_4_9I1R16Mass : Ball := ⟨0, 0⟩
def CA3_4_9I1R16MassTerm : Ball := .exact 0
def CA3_4_9I1R16H : Ball := ⟨0, 0⟩
def CA3_4_9I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA3_4_9I1R0H
  | 1 => CA3_4_9I1R1H
  | 2 => CA3_4_9I1R2H
  | 3 => CA3_4_9I1R3H
  | 4 => CA3_4_9I1R4H
  | 5 => CA3_4_9I1R5H
  | 6 => CA3_4_9I1R6H
  | 7 => CA3_4_9I1R7H
  | 8 => CA3_4_9I1R8H
  | 9 => CA3_4_9I1R9H
  | 10 => CA3_4_9I1R10H
  | 11 => CA3_4_9I1R11H
  | 12 => CA3_4_9I1R12H
  | 13 => CA3_4_9I1R13H
  | 14 => CA3_4_9I1R14H
  | 15 => CA3_4_9I1R15H
  | 16 => CA3_4_9I1R16H
  | _ => (.exact 0)
def CA3_4_9I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | _, _, _ => (.exact 0)
def CA3_4_9I1Singleton : Ball := ⟨0, 0⟩
def CA3_4_9I1Group : Ball := ⟨(94891045199893845884746001550373 / 100000000000000000000000000000000), (35269717717 / 20000000000000000000000000000000)⟩

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
def CA3_4_9I1H : Ball := ⟨(121662790199950032058662094478313 / 100000000000000000000000000000000), (524964696283 / 100000000000000000000000000000000)⟩

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
def CA3_4_9I2PairEntropy : Ball := ⟨(70463611022735415351723642098673 / 25000000000000000000000000000000), (28377027811 / 25000000000000000000000000000000)⟩
def CA3_4_9I2PairMass : Ball := ⟨(12500000000000000000000000000001 / 12500000000000000000000000000000), (157 / 25000000000000000000000000000000)⟩
def CA3_4_9I2PairMassTermLogWitness : LogWitness := ⟨0, 12500000000000000000000000000001, 12500000000000000000000000000000⟩
def CA3_4_9I2PairMassTermLog : Ball := ⟨(1 / 12500000000000000000000000000000), (2117582431 / 10000000000000000000000000000000)⟩
def CA3_4_9I2PairMassTerm : Ball := ⟨(-1 / 12500000000000000000000000000000), (21175824311 / 100000000000000000000000000000000)⟩
def CA3_4_9I2PairH : Ball := ⟨(2818544440909416614068945683947 / 1000000000000000000000000000000), (26936787111 / 20000000000000000000000000000000)⟩

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
def CA3_4_9I2R0Entropy : Ball := ⟨0, 0⟩
def CA3_4_9I2R0Mass : Ball := ⟨0, 0⟩
def CA3_4_9I2R0MassTerm : Ball := .exact 0
def CA3_4_9I2R0H : Ball := ⟨0, 0⟩
def CA3_4_9I2R1Entropy : Ball := ⟨(849205210818614472015140153 / 50000000000000000000000000000000), (34489 / 6250000000000000000000000000000)⟩
def CA3_4_9I2R1Mass : Ball := ⟨(2961092486317753981806299 / 2500000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def CA3_4_9I2R1MassTermLogWitness : LogWitness := ⟨-20, 2961092486317753981806299, 2384185791015625000000000⟩
def CA3_4_9I2R1MassTermLog : Ball := ⟨(-682312150319072910306522185635499 / 50000000000000000000000000000000), (111173496477 / 25000000000000000000000000000000)⟩
def CA3_4_9I2R1MassTerm : Ball := ⟨(808155752653246679917399297 / 50000000000000000000000000000000), (26337 / 5000000000000000000000000000000)⟩
def CA3_4_9I2R1H : Ball := ⟨(5131182270670974012217607 / 6250000000000000000000000000000), (269641 / 25000000000000000000000000000000)⟩
def CA3_4_9I2R2Entropy : Ball := ⟨(628888122444175715804910422913 / 100000000000000000000000000000000), (21940483 / 10000000000000000000000000000000)⟩
def CA3_4_9I2R2Mass : Ball := ⟨(961965437014597225752130051 / 1250000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def CA3_4_9I2R2MassTermLogWitness : LogWitness := ⟨-11, 961965437014597225752130051, 610351562500000000000000000⟩
def CA3_4_9I2R2MassTermLog : Ball := ⟨(-716967558751746717927349993101709 / 100000000000000000000000000000000), (31763736499 / 12500000000000000000000000000000)⟩
def CA3_4_9I2R2MassTerm : Ball := ⟨(4310612568624455895852198643 / 781250000000000000000000000000), (19555599 / 10000000000000000000000000000000)⟩
def CA3_4_9I2R2H : Ball := ⟨(77129713660245361135828996609 / 100000000000000000000000000000000), (20748041 / 5000000000000000000000000000000)⟩
def CA3_4_9I2R3Entropy : Ball := ⟨(194113002424552503680560439183 / 1000000000000000000000000000000), (1862541631 / 25000000000000000000000000000000)⟩
def CA3_4_9I2R3Mass : Ball := ⟨(480637009241608974383676101453 / 10000000000000000000000000000000), (3 / 10000000000000000000000000000000)⟩
def CA3_4_9I2R3MassTermLogWitness : LogWitness := ⟨-5, 480637009241608974383676101453, 312500000000000000000000000000⟩
def CA3_4_9I2R3MassTermLog : Ball := ⟨(-303522804530987493211666450419657 / 100000000000000000000000000000000), (63527471361 / 50000000000000000000000000000000)⟩
def CA3_4_9I2R3MassTerm : Ball := ⟨(7294214650319965502922602621079 / 50000000000000000000000000000000), (305336543 / 5000000000000000000000000000000)⟩
def CA3_4_9I2R3H : Ball := ⟨(2411435470907659681105419338071 / 50000000000000000000000000000000), (1694612173 / 12500000000000000000000000000000)⟩
def CA3_4_9I2R4Entropy : Ball := ⟨(7247738719067702017284385813033 / 10000000000000000000000000000000), (8762614119 / 25000000000000000000000000000000)⟩
def CA3_4_9I2R4Mass : Ball := ⟨(10806945416916588426153135488431 / 25000000000000000000000000000000), (153 / 100000000000000000000000000000000)⟩
def CA3_4_9I2R4MassTermLogWitness : LogWitness := ⟨-2, 10806945416916588426153135488431, 6250000000000000000000000000000⟩
def CA3_4_9I2R4MassTermLog : Ball := ⟨(-41934340163775995053156294938029 / 50000000000000000000000000000000), (63527471403 / 100000000000000000000000000000000)⟩
def CA3_4_9I2R4MassTerm : Ball := ⟨(9063642504886804196860635101949 / 25000000000000000000000000000000), (13730758383 / 50000000000000000000000000000000)⟩
def CA3_4_9I2R4H : Ball := ⟨(18111408585564901692700658861267 / 50000000000000000000000000000000), (31255986621 / 50000000000000000000000000000000)⟩
def CA3_4_9I2R5Entropy : Ball := ⟨(1065994452400275992111573048859 / 1562500000000000000000000000000), (8117576377 / 25000000000000000000000000000000)⟩
def CA3_4_9I2R5Mass : Ball := ⟨(18279533360800236689103924593337 / 50000000000000000000000000000000), (1 / 1000000000000000000000000000000)⟩
def CA3_4_9I2R5MassTermLogWitness : LogWitness := ⟨-2, 18279533360800236689103924593337, 12500000000000000000000000000000⟩
def CA3_4_9I2R5MassTermLog : Ball := ⟨(-100624096703649036266445403338169 / 100000000000000000000000000000000), (31763735661 / 50000000000000000000000000000000)⟩
def CA3_4_9I2R5MassTerm : Ball := ⟨(36787230651894833723090796725369 / 100000000000000000000000000000000), (2903131341 / 12500000000000000000000000000000)⟩
def CA3_4_9I2R5H : Ball := ⟨(31436414301722829772049878401607 / 100000000000000000000000000000000), (13923839059 / 25000000000000000000000000000000)⟩
def CA3_4_9I2R6Entropy : Ball := ⟨(2266362036190387866030857495951 / 25000000000000000000000000000000), (3549739209 / 100000000000000000000000000000000)⟩
def CA3_4_9I2R6Mass : Ball := ⟨(1175366482595508974701704124553 / 50000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
def CA3_4_9I2R6MassTermLogWitness : LogWitness := ⟨-6, 1175366482595508974701704124553, 781250000000000000000000000000⟩
def CA3_4_9I2R6MassTermLog : Ball := ⟨(-375044300638145820613044638924319 / 100000000000000000000000000000000), (148230766419 / 100000000000000000000000000000000)⟩
def CA3_4_9I2R6MassTerm : Ball := ⟨(88162900091710011023539451221 / 1000000000000000000000000000000), (871127387 / 25000000000000000000000000000000)⟩
def CA3_4_9I2R6H : Ball := ⟨(31144766948818795221185607713 / 12500000000000000000000000000000), (7034248757 / 100000000000000000000000000000000)⟩
def CA3_4_9I2R7Entropy : Ball := ⟨0, 0⟩
def CA3_4_9I2R7Mass : Ball := ⟨0, 0⟩
def CA3_4_9I2R7MassTerm : Ball := .exact 0
def CA3_4_9I2R7H : Ball := ⟨0, 0⟩
def CA3_4_9I2R8Entropy : Ball := ⟨0, 0⟩
def CA3_4_9I2R8Mass : Ball := ⟨0, 0⟩
def CA3_4_9I2R8MassTerm : Ball := .exact 0
def CA3_4_9I2R8H : Ball := ⟨0, 0⟩
def CA3_4_9I2R9Entropy : Ball := ⟨0, 0⟩
def CA3_4_9I2R9Mass : Ball := ⟨0, 0⟩
def CA3_4_9I2R9MassTerm : Ball := .exact 0
def CA3_4_9I2R9H : Ball := ⟨0, 0⟩
def CA3_4_9I2R10Entropy : Ball := ⟨0, 0⟩
def CA3_4_9I2R10Mass : Ball := ⟨0, 0⟩
def CA3_4_9I2R10MassTerm : Ball := .exact 0
def CA3_4_9I2R10H : Ball := ⟨0, 0⟩
def CA3_4_9I2R11Entropy : Ball := ⟨0, 0⟩
def CA3_4_9I2R11Mass : Ball := ⟨0, 0⟩
def CA3_4_9I2R11MassTerm : Ball := .exact 0
def CA3_4_9I2R11H : Ball := ⟨0, 0⟩
def CA3_4_9I2R12Entropy : Ball := ⟨0, 0⟩
def CA3_4_9I2R12Mass : Ball := ⟨0, 0⟩
def CA3_4_9I2R12MassTerm : Ball := .exact 0
def CA3_4_9I2R12H : Ball := ⟨0, 0⟩
def CA3_4_9I2R13Entropy : Ball := ⟨0, 0⟩
def CA3_4_9I2R13Mass : Ball := ⟨0, 0⟩
def CA3_4_9I2R13MassTerm : Ball := .exact 0
def CA3_4_9I2R13H : Ball := ⟨0, 0⟩
def CA3_4_9I2R14Entropy : Ball := ⟨0, 0⟩
def CA3_4_9I2R14Mass : Ball := ⟨0, 0⟩
def CA3_4_9I2R14MassTerm : Ball := .exact 0
def CA3_4_9I2R14H : Ball := ⟨0, 0⟩
def CA3_4_9I2R15Entropy : Ball := ⟨0, 0⟩
def CA3_4_9I2R15Mass : Ball := ⟨0, 0⟩
def CA3_4_9I2R15MassTerm : Ball := .exact 0
def CA3_4_9I2R15H : Ball := ⟨0, 0⟩
def CA3_4_9I2R16Entropy : Ball := ⟨0, 0⟩
def CA3_4_9I2R16Mass : Ball := ⟨0, 0⟩
def CA3_4_9I2R16MassTerm : Ball := .exact 0
def CA3_4_9I2R16H : Ball := ⟨0, 0⟩
def CA3_4_9I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA3_4_9I2R0H
  | 1 => CA3_4_9I2R1H
  | 2 => CA3_4_9I2R2H
  | 3 => CA3_4_9I2R3H
  | 4 => CA3_4_9I2R4H
  | 5 => CA3_4_9I2R5H
  | 6 => CA3_4_9I2R6H
  | 7 => CA3_4_9I2R7H
  | 8 => CA3_4_9I2R8H
  | 9 => CA3_4_9I2R9H
  | 10 => CA3_4_9I2R10H
  | 11 => CA3_4_9I2R11H
  | 12 => CA3_4_9I2R12H
  | 13 => CA3_4_9I2R13H
  | 14 => CA3_4_9I2R14H
  | 15 => CA3_4_9I2R15H
  | 16 => CA3_4_9I2R16H
  | _ => (.exact 0)
def CA3_4_9I2Singleton : Ball := ⟨(15375045182343300175117354668423 / 100000000000000000000000000000000), (125676761 / 1000000000000000000000000000000)⟩
def CA3_4_9I2Group : Ball := ⟨(88183517545178379153268898808731 / 100000000000000000000000000000000), (151782191103 / 100000000000000000000000000000000)⟩

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
def CA3_4_9I2H : Ball := ⟨(52743704500292451550178385388619 / 50000000000000000000000000000000), (438248317761 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA3_5_8I0
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
def CA3_5_8I0Value (a : Fin 17) : ℝ := marginal (below (shape 3 5 8)) (fun u => (stageALaw (shape 3 5 8) u : ℝ)) ((Equiv.refl (Fin 3)) 0) a
def CA3_5_8I0Entropy : Ball := ⟨(29881246885032669561186853940741 / 25000000000000000000000000000000), (36024944473 / 50000000000000000000000000000000)⟩
def CA3_5_8I0Mass : Ball := ⟨1, (13 / 6250000000000000000000000000000)⟩
def CA3_5_8I0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CA3_5_8I0MassTermLog : Ball := ⟨0, (2117582389 / 10000000000000000000000000000000)⟩
def CA3_5_8I0MassTerm : Ball := ⟨0, (21175823891 / 100000000000000000000000000000000)⟩
def CA3_5_8I0H : Ball := ⟨(29881246885032669561186853940741 / 25000000000000000000000000000000), (93225712837 / 100000000000000000000000000000000)⟩

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
def CA3_5_8I1PairEntropy : Ball := ⟨(16214910566568980863325613590037 / 5000000000000000000000000000000), (3445353169 / 2500000000000000000000000000000)⟩
def CA3_5_8I1PairMass : Ball := ⟨(12499999999999999999999999999999 / 12500000000000000000000000000000), (67 / 12500000000000000000000000000000)⟩
def CA3_5_8I1PairMassTermLogWitness : LogWitness := ⟨-1, 12499999999999999999999999999999, 6250000000000000000000000000000⟩
def CA3_5_8I1PairMassTermLog : Ball := ⟨(-7 / 100000000000000000000000000000000), (21175823951 / 50000000000000000000000000000000)⟩
def CA3_5_8I1PairMassTerm : Ball := ⟨(7 / 100000000000000000000000000000000), (42351647903 / 100000000000000000000000000000000)⟩
def CA3_5_8I1PairH : Ball := ⟨(324298211331379617266512271800733 / 100000000000000000000000000000000), (180165774663 / 100000000000000000000000000000000)⟩

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
def CA3_5_8I1R0Entropy : Ball := ⟨(1628879118491678187756967641173 / 100000000000000000000000000000000), (585553351 / 100000000000000000000000000000000)⟩
def CA3_5_8I1R0Mass : Ball := ⟨(138259867691619025407984228733 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
def CA3_5_8I1R0MassTermLogWitness : LogWitness := ⟨-9, 138259867691619025407984228733, 97656250000000000000000000000⟩
def CA3_5_8I1R0MassTermLog : Ball := ⟨(-117812865416941003692582243865407 / 20000000000000000000000000000000), (211758238637 / 100000000000000000000000000000000)⟩
def CA3_5_8I1R0MassTerm : Ball := ⟨(1628879118491678187756967641173 / 100000000000000000000000000000000), (585553351 / 100000000000000000000000000000000)⟩
def CA3_5_8I1R0H : Ball := ⟨0, (585553351 / 50000000000000000000000000000000)⟩
def CA3_5_8I1R1Entropy : Ball := ⟨(13457657893666748061001354681387 / 50000000000000000000000000000000), (1355127719 / 12500000000000000000000000000000)⟩
def CA3_5_8I1R1Mass : Ball := ⟨(4266273080468078013491963850177 / 50000000000000000000000000000000), (1 / 2500000000000000000000000000000)⟩
def CA3_5_8I1R1MassTermLogWitness : LogWitness := ⟨-4, 4266273080468078013491963850177, 3125000000000000000000000000000⟩
def CA3_5_8I1R1MassTermLog : Ball := ⟨(-15383014838693581327010069379649 / 6250000000000000000000000000000), (105879118883 / 100000000000000000000000000000000)⟩
def CA3_5_8I1R1MassTerm : Ball := ⟨(21001005472883014211656585649313 / 100000000000000000000000000000000), (1129273099 / 12500000000000000000000000000000)⟩
def CA3_5_8I1R1H : Ball := ⟨(5914310314450481910346123713461 / 100000000000000000000000000000000), (1242200409 / 6250000000000000000000000000000)⟩
def CA3_5_8I1R2Entropy : Ball := ⟨(3933374504091891382016717491171 / 5000000000000000000000000000000), (33720223149 / 100000000000000000000000000000000)⟩
def CA3_5_8I1R2Mass : Ball := ⟨(2059546705184030296110005192109 / 5000000000000000000000000000000), (147 / 100000000000000000000000000000000)⟩
def CA3_5_8I1R2MassTermLogWitness : LogWitness := ⟨-2, 2059546705184030296110005192109, 1250000000000000000000000000000⟩
def CA3_5_8I1R2MassTermLog : Ball := ⟨(-44347599993672980298295301558257 / 50000000000000000000000000000000), (31763735703 / 50000000000000000000000000000000)⟩
def CA3_5_8I1R2MassTerm : Ball := ⟨(18267190689957701875897541677933 / 50000000000000000000000000000000), (3270944877 / 12500000000000000000000000000000)⟩
def CA3_5_8I1R2H : Ball := ⟨(21066554350961211944269633233777 / 50000000000000000000000000000000), (11977556433 / 20000000000000000000000000000000)⟩
def CA3_5_8I1R3Entropy : Ball := ⟨(20472503413953983158455688787947 / 25000000000000000000000000000000), (19127854653 / 50000000000000000000000000000000)⟩
def CA3_5_8I1R3Mass : Ball := ⟨(2059546705184030296110005192109 / 5000000000000000000000000000000), (13 / 12500000000000000000000000000000)⟩
def CA3_5_8I1R3MassTermLogWitness : LogWitness := ⟨-2, 2059546705184030296110005192109, 1250000000000000000000000000000⟩
def CA3_5_8I1R3MassTermLog : Ball := ⟨(-44347599993672980298295301558257 / 50000000000000000000000000000000), (63527471301 / 100000000000000000000000000000000)⟩
def CA3_5_8I1R3MassTerm : Ball := ⟨(18267190689957701875897541677933 / 50000000000000000000000000000000), (13083779467 / 50000000000000000000000000000000)⟩
def CA3_5_8I1R3H : Ball := ⟨(22677816137950264441013835897961 / 50000000000000000000000000000000), (805290853 / 1250000000000000000000000000000)⟩
def CA3_5_8I1R4Entropy : Ball := ⟨(30274529390913526655977682079287 / 100000000000000000000000000000000), (12264440129 / 100000000000000000000000000000000)⟩
def CA3_5_8I1R4Mass : Ball := ⟨(8532546160936156026983927700353 / 100000000000000000000000000000000), (51 / 100000000000000000000000000000000)⟩
def CA3_5_8I1R4MassTermLogWitness : LogWitness := ⟨-4, 8532546160936156026983927700353, 6250000000000000000000000000000⟩
def CA3_5_8I1R4MassTermLog : Ball := ⟨(-49225647483819460246432222014879 / 20000000000000000000000000000000), (26469779753 / 25000000000000000000000000000000)⟩
def CA3_5_8I1R4MassTerm : Ball := ⟨(656281421027594194114268301541 / 3125000000000000000000000000000), (9034184831 / 100000000000000000000000000000000)⟩
def CA3_5_8I1R4H : Ball := ⟨(370940956721220497772843857199 / 4000000000000000000000000000000), (66558203 / 312500000000000000000000000000)⟩
def CA3_5_8I1R5Entropy : Ball := ⟨(968580955798841484078453451653 / 50000000000000000000000000000000), (16812453 / 2500000000000000000000000000000)⟩
def CA3_5_8I1R5Mass : Ball := ⟨(69128529515490861959248981511 / 25000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
def CA3_5_8I1R5MassTermLogWitness : LogWitness := ⟨-9, 69128529515490861959248981511, 48828125000000000000000000000⟩
def CA3_5_8I1R5MassTermLog : Ball := ⟨(-147266589635318730006094524319141 / 25000000000000000000000000000000), (105879120223 / 50000000000000000000000000000000)⟩
def CA3_5_8I1R5MassTerm : Ball := ⟨(1628851646120129836860628761549 / 100000000000000000000000000000000), (585541491 / 100000000000000000000000000000000)⟩
def CA3_5_8I1R5H : Ball := ⟨(308310265477553131296278141757 / 100000000000000000000000000000000), (1258039611 / 100000000000000000000000000000000)⟩
def CA3_5_8I1R6Entropy : Ball := ⟨0, 0⟩
def CA3_5_8I1R6Mass : Ball := ⟨0, 0⟩
def CA3_5_8I1R6MassTerm : Ball := .exact 0
def CA3_5_8I1R6H : Ball := ⟨0, 0⟩
def CA3_5_8I1R7Entropy : Ball := ⟨0, 0⟩
def CA3_5_8I1R7Mass : Ball := ⟨0, 0⟩
def CA3_5_8I1R7MassTerm : Ball := .exact 0
def CA3_5_8I1R7H : Ball := ⟨0, 0⟩
def CA3_5_8I1R8Entropy : Ball := ⟨0, 0⟩
def CA3_5_8I1R8Mass : Ball := ⟨0, 0⟩
def CA3_5_8I1R8MassTerm : Ball := .exact 0
def CA3_5_8I1R8H : Ball := ⟨0, 0⟩
def CA3_5_8I1R9Entropy : Ball := ⟨0, 0⟩
def CA3_5_8I1R9Mass : Ball := ⟨0, 0⟩
def CA3_5_8I1R9MassTerm : Ball := .exact 0
def CA3_5_8I1R9H : Ball := ⟨0, 0⟩
def CA3_5_8I1R10Entropy : Ball := ⟨0, 0⟩
def CA3_5_8I1R10Mass : Ball := ⟨0, 0⟩
def CA3_5_8I1R10MassTerm : Ball := .exact 0
def CA3_5_8I1R10H : Ball := ⟨0, 0⟩
def CA3_5_8I1R11Entropy : Ball := ⟨0, 0⟩
def CA3_5_8I1R11Mass : Ball := ⟨0, 0⟩
def CA3_5_8I1R11MassTerm : Ball := .exact 0
def CA3_5_8I1R11H : Ball := ⟨0, 0⟩
def CA3_5_8I1R12Entropy : Ball := ⟨0, 0⟩
def CA3_5_8I1R12Mass : Ball := ⟨0, 0⟩
def CA3_5_8I1R12MassTerm : Ball := .exact 0
def CA3_5_8I1R12H : Ball := ⟨0, 0⟩
def CA3_5_8I1R13Entropy : Ball := ⟨0, 0⟩
def CA3_5_8I1R13Mass : Ball := ⟨0, 0⟩
def CA3_5_8I1R13MassTerm : Ball := .exact 0
def CA3_5_8I1R13H : Ball := ⟨0, 0⟩
def CA3_5_8I1R14Entropy : Ball := ⟨0, 0⟩
def CA3_5_8I1R14Mass : Ball := ⟨0, 0⟩
def CA3_5_8I1R14MassTerm : Ball := .exact 0
def CA3_5_8I1R14H : Ball := ⟨0, 0⟩
def CA3_5_8I1R15Entropy : Ball := ⟨0, 0⟩
def CA3_5_8I1R15Mass : Ball := ⟨0, 0⟩
def CA3_5_8I1R15MassTerm : Ball := .exact 0
def CA3_5_8I1R15H : Ball := ⟨0, 0⟩
def CA3_5_8I1R16Entropy : Ball := ⟨0, 0⟩
def CA3_5_8I1R16Mass : Ball := ⟨0, 0⟩
def CA3_5_8I1R16MassTerm : Ball := .exact 0
def CA3_5_8I1R16H : Ball := ⟨0, 0⟩
def CA3_5_8I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA3_5_8I1R0H
  | 1 => CA3_5_8I1R1H
  | 2 => CA3_5_8I1R2H
  | 3 => CA3_5_8I1R3H
  | 4 => CA3_5_8I1R4H
  | 5 => CA3_5_8I1R5H
  | 6 => CA3_5_8I1R6H
  | 7 => CA3_5_8I1R7H
  | 8 => CA3_5_8I1R8H
  | 9 => CA3_5_8I1R9H
  | 10 => CA3_5_8I1R10H
  | 11 => CA3_5_8I1R11H
  | 12 => CA3_5_8I1R12H
  | 13 => CA3_5_8I1R13H
  | 14 => CA3_5_8I1R14H
  | 15 => CA3_5_8I1R15H
  | 16 => CA3_5_8I1R16H
  | _ => (.exact 0)
def CA3_5_8I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 3, 5, 0 => Z3_5_0H1H
  | _, _, _ => (.exact 0)
def CA3_5_8I1Singleton : Ball := ⟨(1677500010387187021113073 / 25000000000000000000000000000000), (333 / 6250000000000000000000000000000)⟩
def CA3_5_8I1Group : Ball := ⟨(102984892185781541805278521000961 / 100000000000000000000000000000000), (3358280671 / 2000000000000000000000000000000)⟩

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
def CA3_5_8I1H : Ball := ⟨(118328426959816533655955229798811 / 100000000000000000000000000000000), (515993841763 / 100000000000000000000000000000000)⟩

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
def CA3_5_8I2PairEntropy : Ball := ⟨(70418030916704243189739288208691 / 25000000000000000000000000000000), (57800160329 / 50000000000000000000000000000000)⟩
def CA3_5_8I2PairMass : Ball := ⟨(50000000000000000000000000000001 / 50000000000000000000000000000000), (127 / 20000000000000000000000000000000)⟩
def CA3_5_8I2PairMassTermLogWitness : LogWitness := ⟨0, 50000000000000000000000000000001, 50000000000000000000000000000000⟩
def CA3_5_8I2PairMassTermLog : Ball := ⟨(1 / 50000000000000000000000000000000), (21175824317 / 100000000000000000000000000000000)⟩
def CA3_5_8I2PairMassTerm : Ball := ⟨(-1 / 50000000000000000000000000000000), (10587912159 / 50000000000000000000000000000000)⟩
def CA3_5_8I2PairH : Ball := ⟨(140836061833408486379478576417383 / 50000000000000000000000000000000), (8548509061 / 6250000000000000000000000000000)⟩

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
def CA3_5_8I2R0Entropy : Ball := ⟨(11722525042486881302899449 / 12500000000000000000000000000000), (15473 / 50000000000000000000000000000000)⟩
def CA3_5_8I2R0Mass : Ball := ⟨(5617321274602978972531421 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def CA3_5_8I2R0MassTermLogWitness : LogWitness := ⟨-25, 5617321274602978972531421, 2980232238769531250000000⟩
def CA3_5_8I2R0MassTermLog : Ball := ⟨(-834741291760308362723103481718601 / 50000000000000000000000000000000), (550589217837 / 100000000000000000000000000000000)⟩
def CA3_5_8I2R0MassTerm : Ball := ⟨(11722525042486881302899449 / 12500000000000000000000000000000), (15473 / 50000000000000000000000000000000)⟩
def CA3_5_8I2R0H : Ball := ⟨0, (15473 / 25000000000000000000000000000000)⟩
def CA3_5_8I2R1Entropy : Ball := ⟨(33852970621212845371812639747 / 50000000000000000000000000000000), (1388533 / 6250000000000000000000000000000)⟩
def CA3_5_8I2R1Mass : Ball := ⟨(819643483877255325795700097 / 12500000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
def CA3_5_8I2R1MassTermLogWitness : LogWitness := ⟨-14, 819643483877255325795700097, 762939453125000000000000000⟩
def CA3_5_8I2R1MassTermLog : Ball := ⟨(-30101155413487687883558056430797 / 3125000000000000000000000000000), (158818708123 / 50000000000000000000000000000000)⟩
def CA3_5_8I2R1MassTerm : Ball := ⟨(63160872683114886588371371791 / 100000000000000000000000000000000), (10413997 / 50000000000000000000000000000000)⟩
def CA3_5_8I2R1H : Ball := ⟨(4545068559310804155253907703 / 100000000000000000000000000000000), (21522261 / 50000000000000000000000000000000)⟩
def CA3_5_8I2R2Entropy : Ball := ⟨(4903014197467876565269785133691 / 100000000000000000000000000000000), (884401411 / 50000000000000000000000000000000)⟩
def CA3_5_8I2R2Mass : Ball := ⟨(84890000149335079434501906979 / 10000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
def CA3_5_8I2R2MassTermLogWitness : LogWitness := ⟨-7, 84890000149335079434501906979, 78125000000000000000000000000⟩
def CA3_5_8I2R2MassTermLog : Ball := ⟨(-238449203473357323046087830923007 / 50000000000000000000000000000000), (169406590759 / 100000000000000000000000000000000)⟩
def CA3_5_8I2R2MassTerm : Ball := ⟨(4048390583692426779033983965233 / 100000000000000000000000000000000), (287618521 / 20000000000000000000000000000000)⟩
def CA3_5_8I2R2H : Ball := ⟨(427311806887724893117900584229 / 50000000000000000000000000000000), (3206895427 / 100000000000000000000000000000000)⟩
def CA3_5_8I2R3Entropy : Ball := ⟨(12028235618652855051199838483633 / 25000000000000000000000000000000), (2462483841 / 12500000000000000000000000000000)⟩
def CA3_5_8I2R3Mass : Ball := ⟨(8726568794983339000134653367169 / 50000000000000000000000000000000), (7 / 10000000000000000000000000000000)⟩
def CA3_5_8I2R3MassTermLogWitness : LogWitness := ⟨-3, 8726568794983339000134653367169, 6250000000000000000000000000000⟩
def CA3_5_8I2R3MassTermLog : Ball := ⟨(-174565074891994409889667767275929 / 100000000000000000000000000000000), (21175823783 / 25000000000000000000000000000000)⟩
def CA3_5_8I2R3MassTerm : Ball := ⟨(7616770676232039919841721935443 / 25000000000000000000000000000000), (7391691383 / 50000000000000000000000000000000)⟩
def CA3_5_8I2R3H : Ball := ⟨(441146494242081513135811654819 / 2500000000000000000000000000000), (17241626747 / 50000000000000000000000000000000)⟩
def CA3_5_8I2R4Entropy : Ball := ⟨(5014139172952875597738593390687 / 6250000000000000000000000000000), (46263707783 / 100000000000000000000000000000000)⟩
def CA3_5_8I2R4Mass : Ball := ⟨(58167735407735864562128006602881 / 100000000000000000000000000000000), (31 / 20000000000000000000000000000000)⟩
def CA3_5_8I2R4MassTermLogWitness : LogWitness := ⟨-1, 58167735407735864562128006602881, 50000000000000000000000000000000⟩
def CA3_5_8I2R4MassTermLog : Ball := ⟨(-27091967970527579926082113059819 / 50000000000000000000000000000000), (2646977977 / 6250000000000000000000000000000)⟩
def CA3_5_8I2R4MassTerm : Ball := ⟨(3151756849169006124968414455831 / 10000000000000000000000000000000), (1231749721 / 5000000000000000000000000000000)⟩
def CA3_5_8I2R4H : Ball := ⟨(24354329137777974157066674846341 / 50000000000000000000000000000000), (70898702203 / 100000000000000000000000000000000)⟩
def CA3_5_8I2R5Entropy : Ball := ⟨(2337112958258862323045104949707 / 6250000000000000000000000000000), (8373088087 / 50000000000000000000000000000000)⟩
def CA3_5_8I2R5Mass : Ball := ⟨(1605440317199808814079441729437 / 12500000000000000000000000000000), (13 / 25000000000000000000000000000000)⟩
def CA3_5_8I2R5MassTermLogWitness : LogWitness := ⟨-3, 1605440317199808814079441729437, 1562500000000000000000000000000⟩
def CA3_5_8I2R5MassTermLog : Ball := ⟨(-25654132305205111739328766222689 / 12500000000000000000000000000000), (2646977973 / 3125000000000000000000000000000)⟩
def CA3_5_8I2R5MassTerm : Ball := ⟨(26359154115554788539487055265713 / 100000000000000000000000000000000), (2719721727 / 25000000000000000000000000000000)⟩
def CA3_5_8I2R5H : Ball := ⟨(11034653216587008629234623929599 / 100000000000000000000000000000000), (13812531541 / 50000000000000000000000000000000)⟩
def CA3_5_8I2R6Entropy : Ball := ⟨(1978800781676650283064511728233 / 100000000000000000000000000000000), (732632603 / 100000000000000000000000000000000)⟩
def CA3_5_8I2R6Mass : Ball := ⟨(342133027168868932426842786183 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def CA3_5_8I2R6MassTermLogWitness : LogWitness := ⟨-9, 342133027168868932426842786183, 195312500000000000000000000000⟩
def CA3_5_8I2R6MassTermLog : Ball := ⟨(-283886291760308362723103641132293 / 50000000000000000000000000000000), (52939559719 / 25000000000000000000000000000000)⟩
def CA3_5_8I2R6MassTerm : Ball := ⟨(1942537527433980672240958010263 / 100000000000000000000000000000000), (724494913 / 100000000000000000000000000000000)⟩
def CA3_5_8I2R6H : Ball := ⟨(3626325424266961082355371797 / 10000000000000000000000000000000), (364281879 / 25000000000000000000000000000000)⟩
def CA3_5_8I2R7Entropy : Ball := ⟨0, 0⟩
def CA3_5_8I2R7Mass : Ball := ⟨0, 0⟩
def CA3_5_8I2R7MassTerm : Ball := .exact 0
def CA3_5_8I2R7H : Ball := ⟨0, 0⟩
def CA3_5_8I2R8Entropy : Ball := ⟨0, 0⟩
def CA3_5_8I2R8Mass : Ball := ⟨0, 0⟩
def CA3_5_8I2R8MassTerm : Ball := .exact 0
def CA3_5_8I2R8H : Ball := ⟨0, 0⟩
def CA3_5_8I2R9Entropy : Ball := ⟨0, 0⟩
def CA3_5_8I2R9Mass : Ball := ⟨0, 0⟩
def CA3_5_8I2R9MassTerm : Ball := .exact 0
def CA3_5_8I2R9H : Ball := ⟨0, 0⟩
def CA3_5_8I2R10Entropy : Ball := ⟨0, 0⟩
def CA3_5_8I2R10Mass : Ball := ⟨0, 0⟩
def CA3_5_8I2R10MassTerm : Ball := .exact 0
def CA3_5_8I2R10H : Ball := ⟨0, 0⟩
def CA3_5_8I2R11Entropy : Ball := ⟨0, 0⟩
def CA3_5_8I2R11Mass : Ball := ⟨0, 0⟩
def CA3_5_8I2R11MassTerm : Ball := .exact 0
def CA3_5_8I2R11H : Ball := ⟨0, 0⟩
def CA3_5_8I2R12Entropy : Ball := ⟨0, 0⟩
def CA3_5_8I2R12Mass : Ball := ⟨0, 0⟩
def CA3_5_8I2R12MassTerm : Ball := .exact 0
def CA3_5_8I2R12H : Ball := ⟨0, 0⟩
def CA3_5_8I2R13Entropy : Ball := ⟨0, 0⟩
def CA3_5_8I2R13Mass : Ball := ⟨0, 0⟩
def CA3_5_8I2R13MassTerm : Ball := .exact 0
def CA3_5_8I2R13H : Ball := ⟨0, 0⟩
def CA3_5_8I2R14Entropy : Ball := ⟨0, 0⟩
def CA3_5_8I2R14Mass : Ball := ⟨0, 0⟩
def CA3_5_8I2R14MassTerm : Ball := .exact 0
def CA3_5_8I2R14H : Ball := ⟨0, 0⟩
def CA3_5_8I2R15Entropy : Ball := ⟨0, 0⟩
def CA3_5_8I2R15Mass : Ball := ⟨0, 0⟩
def CA3_5_8I2R15MassTerm : Ball := .exact 0
def CA3_5_8I2R15H : Ball := ⟨0, 0⟩
def CA3_5_8I2R16Entropy : Ball := ⟨0, 0⟩
def CA3_5_8I2R16Mass : Ball := ⟨0, 0⟩
def CA3_5_8I2R16MassTerm : Ball := .exact 0
def CA3_5_8I2R16H : Ball := ⟨0, 0⟩
def CA3_5_8I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA3_5_8I2R0H
  | 1 => CA3_5_8I2R1H
  | 2 => CA3_5_8I2R2H
  | 3 => CA3_5_8I2R3H
  | 4 => CA3_5_8I2R4H
  | 5 => CA3_5_8I2R5H
  | 6 => CA3_5_8I2R6H
  | 7 => CA3_5_8I2R7H
  | 8 => CA3_5_8I2R8H
  | 9 => CA3_5_8I2R9H
  | 10 => CA3_5_8I2R10H
  | 11 => CA3_5_8I2R11H
  | 12 => CA3_5_8I2R12H
  | 13 => CA3_5_8I2R13H
  | 14 => CA3_5_8I2R14H
  | 15 => CA3_5_8I2R15H
  | 16 => CA3_5_8I2R16H
  | _ => (.exact 0)
def CA3_5_8I2Singleton : Ball := ⟨(6211276669360813360008105642437 / 50000000000000000000000000000000), (10316298947 / 100000000000000000000000000000000)⟩
def CA3_5_8I2Group : Ball := ⟨(45353578268562637195015629947023 / 50000000000000000000000000000000), (148030447083 / 100000000000000000000000000000000)⟩

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
def CA3_5_8I2H : Ball := ⟨(50128905296283211989447316523337 / 50000000000000000000000000000000), (216418519571 / 50000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA3_6_7I0
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
def CA3_6_7I0Value (a : Fin 17) : ℝ := marginal (below (shape 3 6 7)) (fun u => (stageALaw (shape 3 6 7) u : ℝ)) ((Equiv.refl (Fin 3)) 0) a
def CA3_6_7I0Entropy : Ball := ⟨(59354541419091826381184777022127 / 50000000000000000000000000000000), (35901262661 / 50000000000000000000000000000000)⟩
def CA3_6_7I0Mass : Ball := ⟨1, (23 / 10000000000000000000000000000000)⟩
def CA3_6_7I0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CA3_6_7I0MassTermLog : Ball := ⟨0, (2646977989 / 12500000000000000000000000000000)⟩
def CA3_6_7I0MassTerm : Ball := ⟨0, (21175823913 / 100000000000000000000000000000000)⟩
def CA3_6_7I0H : Ball := ⟨(59354541419091826381184777022127 / 50000000000000000000000000000000), (18595669847 / 20000000000000000000000000000000)⟩

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
def CA3_6_7I1PairEntropy : Ball := ⟨(160708552106823370392863971663899 / 50000000000000000000000000000000), (67128393269 / 50000000000000000000000000000000)⟩
def CA3_6_7I1PairMass : Ball := ⟨(49999999999999999999999999999993 / 50000000000000000000000000000000), (293 / 50000000000000000000000000000000)⟩
def CA3_6_7I1PairMassTermLogWitness : LogWitness := ⟨-1, 49999999999999999999999999999993, 25000000000000000000000000000000⟩
def CA3_6_7I1PairMassTermLog : Ball := ⟨(-7 / 50000000000000000000000000000000), (2646977997 / 6250000000000000000000000000000)⟩
def CA3_6_7I1PairMassTerm : Ball := ⟨(7 / 50000000000000000000000000000000), (42351647953 / 100000000000000000000000000000000)⟩
def CA3_6_7I1PairH : Ball := ⟨(40177138026705842598215992915973 / 12500000000000000000000000000000), (176608434491 / 100000000000000000000000000000000)⟩

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
def CA3_6_7I1R0Entropy : Ball := ⟨(138931155109136038320014250681 / 100000000000000000000000000000000), (47083883 / 100000000000000000000000000000000)⟩
def CA3_6_7I1R0Mass : Ball := ⟨(15881943617078418930441913137 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def CA3_6_7I1R0MassTermLogWitness : LogWitness := ⟨-13, 15881943617078418930441913137, 12207031250000000000000000000⟩
def CA3_6_7I1R0MassTermLog : Ball := ⟨(-874774262261820556491951653914897 / 100000000000000000000000000000000), (296461550451 / 100000000000000000000000000000000)⟩
def CA3_6_7I1R0MassTerm : Ball := ⟨(138931155109136038320014250681 / 100000000000000000000000000000000), (47083883 / 100000000000000000000000000000000)⟩
def CA3_6_7I1R0H : Ball := ⟨0, (47083883 / 50000000000000000000000000000000)⟩
def CA3_6_7I1R1Entropy : Ball := ⟨(1721537416766707285586801572237 / 25000000000000000000000000000000), (1319561321 / 50000000000000000000000000000000)⟩
def CA3_6_7I1R1Mass : Ball := ⟨(138476711256890786760421812117 / 10000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
def CA3_6_7I1R1MassTermLogWitness : LogWitness := ⟨-7, 138476711256890786760421812117, 78125000000000000000000000000⟩
def CA3_6_7I1R1MassTermLog : Ball := ⟨(-213981910512864433214684788559053 / 50000000000000000000000000000000), (84703295093 / 50000000000000000000000000000000)⟩
def CA3_6_7I1R1MassTerm : Ball := ⟨(5926302247257554248919325186761 / 100000000000000000000000000000000), (2345886791 / 100000000000000000000000000000000)⟩
def CA3_6_7I1R1H : Ball := ⟨(959847419809274893427881102187 / 100000000000000000000000000000000), (4985009433 / 100000000000000000000000000000000)⟩
def CA3_6_7I1R2Entropy : Ball := ⟨(5689113477092737753443204030387 / 10000000000000000000000000000000), (2344924691 / 10000000000000000000000000000000)⟩
def CA3_6_7I1R2Mass : Ball := ⟨(11405305594576277347709633660001 / 50000000000000000000000000000000), (113 / 100000000000000000000000000000000)⟩
def CA3_6_7I1R2MassTermLogWitness : LogWitness := ⟨-3, 11405305594576277347709633660001, 6250000000000000000000000000000⟩
def CA3_6_7I1R2MassTermLog : Ball := ⟨(-147794435526109069104234588319341 / 100000000000000000000000000000000), (84703295227 / 100000000000000000000000000000000)⟩
def CA3_6_7I1R2MassTerm : Ball := ⟨(33712814047063493684397758180661 / 100000000000000000000000000000000), (19321339507 / 100000000000000000000000000000000)⟩
def CA3_6_7I1R2H : Ball := ⟨(23178320723863883850034282123209 / 100000000000000000000000000000000), (42770586417 / 100000000000000000000000000000000)⟩
def CA3_6_7I1R3Entropy : Ball := ⟨(8985215799638267253201323400311 / 10000000000000000000000000000000), (23802652869 / 50000000000000000000000000000000)⟩
def CA3_6_7I1R3Mass : Ball := ⟨(6447184938665364754511518161423 / 12500000000000000000000000000000), (29 / 25000000000000000000000000000000)⟩
def CA3_6_7I1R3MassTermLogWitness : LogWitness := ⟨-1, 6447184938665364754511518161423, 6250000000000000000000000000000⟩
def CA3_6_7I1R3MassTermLog : Ball := ⟨(-16552126309689593680616697644509 / 25000000000000000000000000000000), (4235164759 / 10000000000000000000000000000000)⟩
def CA3_6_7I1R3MassTerm : Ball := ⟨(34148678222949591453344708204229 / 100000000000000000000000000000000), (4368782487 / 20000000000000000000000000000000)⟩
def CA3_6_7I1R3H : Ball := ⟨(55703479773433081078668525798881 / 100000000000000000000000000000000), (69449218173 / 100000000000000000000000000000000)⟩
def CA3_6_7I1R4Entropy : Ball := ⟨(11241698439528684788496173281783 / 20000000000000000000000000000000), (4789130677 / 20000000000000000000000000000000)⟩
def CA3_6_7I1R4Mass : Ball := ⟨(11405305594576277347709633660001 / 50000000000000000000000000000000), (1 / 1000000000000000000000000000000)⟩
def CA3_6_7I1R4MassTermLogWitness : LogWitness := ⟨-3, 11405305594576277347709633660001, 6250000000000000000000000000000⟩
def CA3_6_7I1R4MassTermLog : Ball := ⟨(-147794435526109069104234588319341 / 100000000000000000000000000000000), (8470329517 / 10000000000000000000000000000000)⟩
def CA3_6_7I1R4MassTerm : Ball := ⟨(33712814047063493684397758180661 / 100000000000000000000000000000000), (9660669737 / 50000000000000000000000000000000)⟩
def CA3_6_7I1R4H : Ball := ⟨(11247839075289965129041554114127 / 50000000000000000000000000000000), (43266992859 / 100000000000000000000000000000000)⟩
def CA3_6_7I1R5Entropy : Ball := ⟨(742898524440287926217499497107 / 10000000000000000000000000000000), (1383702859 / 50000000000000000000000000000000)⟩
def CA3_6_7I1R5Mass : Ball := ⟨(692161258382387705480172684873 / 50000000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩
def CA3_6_7I1R5MassTermLogWitness : LogWitness := ⟨-7, 692161258382387705480172684873, 390625000000000000000000000000⟩
def CA3_6_7I1R5MassTermLog : Ball := ⟨(-427995932359594196573051346155393 / 100000000000000000000000000000000), (169406590619 / 100000000000000000000000000000000)⟩
def CA3_6_7I1R5MassTerm : Ball := ⟨(1184968812498240039997339696673 / 20000000000000000000000000000000), (146570853 / 6250000000000000000000000000000)⟩
def CA3_6_7I1R5H : Ball := ⟨(300828236382335812437659297541 / 20000000000000000000000000000000), (2556269683 / 50000000000000000000000000000000)⟩
def CA3_6_7I1R6Entropy : Ball := ⟨(19149361111943272243989991259 / 12500000000000000000000000000000), (10539689 / 20000000000000000000000000000000)⟩
def CA3_6_7I1R6Mass : Ball := ⟨(1581646225432173469121351409 / 10000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def CA3_6_7I1R6MassTermLogWitness : LogWitness := ⟨-13, 1581646225432173469121351409, 1220703125000000000000000000⟩
def CA3_6_7I1R6MassTermLog : Ball := ⟨(-218796853813083489409265359694123 / 25000000000000000000000000000000), (296461569497 / 100000000000000000000000000000000)⟩
def CA3_6_7I1R6MassTerm : Ball := ⟨(138423687187959420791691804753 / 100000000000000000000000000000000), (9377957 / 20000000000000000000000000000000)⟩
def CA3_6_7I1R6H : Ball := ⟨(14771201707586757160228125319 / 100000000000000000000000000000000), (9958823 / 10000000000000000000000000000000)⟩
def CA3_6_7I1R7Entropy : Ball := ⟨0, 0⟩
def CA3_6_7I1R7Mass : Ball := ⟨0, 0⟩
def CA3_6_7I1R7MassTerm : Ball := .exact 0
def CA3_6_7I1R7H : Ball := ⟨0, 0⟩
def CA3_6_7I1R8Entropy : Ball := ⟨0, 0⟩
def CA3_6_7I1R8Mass : Ball := ⟨0, 0⟩
def CA3_6_7I1R8MassTerm : Ball := .exact 0
def CA3_6_7I1R8H : Ball := ⟨0, 0⟩
def CA3_6_7I1R9Entropy : Ball := ⟨0, 0⟩
def CA3_6_7I1R9Mass : Ball := ⟨0, 0⟩
def CA3_6_7I1R9MassTerm : Ball := .exact 0
def CA3_6_7I1R9H : Ball := ⟨0, 0⟩
def CA3_6_7I1R10Entropy : Ball := ⟨0, 0⟩
def CA3_6_7I1R10Mass : Ball := ⟨0, 0⟩
def CA3_6_7I1R10MassTerm : Ball := .exact 0
def CA3_6_7I1R10H : Ball := ⟨0, 0⟩
def CA3_6_7I1R11Entropy : Ball := ⟨0, 0⟩
def CA3_6_7I1R11Mass : Ball := ⟨0, 0⟩
def CA3_6_7I1R11MassTerm : Ball := .exact 0
def CA3_6_7I1R11H : Ball := ⟨0, 0⟩
def CA3_6_7I1R12Entropy : Ball := ⟨0, 0⟩
def CA3_6_7I1R12Mass : Ball := ⟨0, 0⟩
def CA3_6_7I1R12MassTerm : Ball := .exact 0
def CA3_6_7I1R12H : Ball := ⟨0, 0⟩
def CA3_6_7I1R13Entropy : Ball := ⟨0, 0⟩
def CA3_6_7I1R13Mass : Ball := ⟨0, 0⟩
def CA3_6_7I1R13MassTerm : Ball := .exact 0
def CA3_6_7I1R13H : Ball := ⟨0, 0⟩
def CA3_6_7I1R14Entropy : Ball := ⟨0, 0⟩
def CA3_6_7I1R14Mass : Ball := ⟨0, 0⟩
def CA3_6_7I1R14MassTerm : Ball := .exact 0
def CA3_6_7I1R14H : Ball := ⟨0, 0⟩
def CA3_6_7I1R15Entropy : Ball := ⟨0, 0⟩
def CA3_6_7I1R15Mass : Ball := ⟨0, 0⟩
def CA3_6_7I1R15MassTerm : Ball := .exact 0
def CA3_6_7I1R15H : Ball := ⟨0, 0⟩
def CA3_6_7I1R16Entropy : Ball := ⟨0, 0⟩
def CA3_6_7I1R16Mass : Ball := ⟨0, 0⟩
def CA3_6_7I1R16MassTerm : Ball := .exact 0
def CA3_6_7I1R16H : Ball := ⟨0, 0⟩
def CA3_6_7I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA3_6_7I1R0H
  | 1 => CA3_6_7I1R1H
  | 2 => CA3_6_7I1R2H
  | 3 => CA3_6_7I1R3H
  | 4 => CA3_6_7I1R4H
  | 5 => CA3_6_7I1R5H
  | 6 => CA3_6_7I1R6H
  | 7 => CA3_6_7I1R7H
  | 8 => CA3_6_7I1R8H
  | 9 => CA3_6_7I1R9H
  | 10 => CA3_6_7I1R10H
  | 11 => CA3_6_7I1R11H
  | 12 => CA3_6_7I1R12H
  | 13 => CA3_6_7I1R13H
  | 14 => CA3_6_7I1R14H
  | 15 => CA3_6_7I1R15H
  | 16 => CA3_6_7I1R16H
  | _ => (.exact 0)
def CA3_6_7I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 2, 6, 0 => Z2_6_0H1H
  | 3, 5, 0 => Z3_5_0H1H
  | _, _, _ => (.exact 0)
def CA3_6_7I1Singleton : Ball := ⟨(149742991488449009400997643 / 25000000000000000000000000000000), (237491 / 50000000000000000000000000000000)⟩
def CA3_6_7I1Group : Ball := ⟨(103856837423271389695599925856127 / 100000000000000000000000000000000), (82889288613 / 50000000000000000000000000000000)⟩

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
def CA3_6_7I1H : Ball := ⟨(11370342936710396139452809161553 / 10000000000000000000000000000000), (508165588943 / 100000000000000000000000000000000)⟩

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
def CA3_6_7I2PairEntropy : Ball := ⟨(75080845296854901583388450035229 / 25000000000000000000000000000000), (29471329207 / 25000000000000000000000000000000)⟩
def CA3_6_7I2PairMass : Ball := ⟨(25000000000000000000000000000001 / 25000000000000000000000000000000), (151 / 25000000000000000000000000000000)⟩
def CA3_6_7I2PairMassTermLogWitness : LogWitness := ⟨0, 25000000000000000000000000000001, 25000000000000000000000000000000⟩
def CA3_6_7I2PairMassTermLog : Ball := ⟨(1 / 25000000000000000000000000000000), (10587912143 / 50000000000000000000000000000000)⟩
def CA3_6_7I2PairMassTerm : Ball := ⟨(-1 / 25000000000000000000000000000000), (21175824287 / 100000000000000000000000000000000)⟩
def CA3_6_7I2PairH : Ball := ⟨(7508084529685490158338845003523 / 2500000000000000000000000000000), (27812228223 / 20000000000000000000000000000000)⟩

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
def CA3_6_7I2R0Entropy : Ball := ⟨(6215860913120059024385980159 / 100000000000000000000000000000000), (82091 / 4000000000000000000000000000000)⟩
def CA3_6_7I2R0Mass : Ball := ⟨(510077166889140883101150469 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def CA3_6_7I2R0MassTermLogWitness : LogWitness := ⟨-18, 510077166889140883101150469, 381469726562500000000000000⟩
def CA3_6_7I2R0MassTermLog : Ball := ⟨(-243722374441081436775523471546581 / 20000000000000000000000000000000), (201170521037 / 50000000000000000000000000000000)⟩
def CA3_6_7I2R0MassTerm : Ball := ⟨(6215860913120059024385980159 / 100000000000000000000000000000000), (82091 / 4000000000000000000000000000000)⟩
def CA3_6_7I2R0H : Ball := ⟨0, (82091 / 2000000000000000000000000000000)⟩
def CA3_6_7I2R1Entropy : Ball := ⟨(234932304814444663213154937893 / 25000000000000000000000000000000), (20289103 / 6250000000000000000000000000000)⟩
def CA3_6_7I2R1Mass : Ball := ⟨(15968760802922606319500670023 / 12500000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def CA3_6_7I2R1MassTermLogWitness : LogWitness := ⟨-10, 15968760802922606319500670023, 12207031250000000000000000000⟩
def CA3_6_7I2R1MassTermLog : Ball := ⟨(-333142477969134187109337408414973 / 50000000000000000000000000000000), (232934065209 / 100000000000000000000000000000000)⟩
def CA3_6_7I2R1MassTerm : Ball := ⟨(34047184281484914742132203749 / 4000000000000000000000000000000), (29757351 / 10000000000000000000000000000000)⟩
def CA3_6_7I2R1H : Ball := ⟨(88549612220655784299314657847 / 100000000000000000000000000000000), (311099579 / 50000000000000000000000000000000)⟩
def CA3_6_7I2R2Entropy : Ball := ⟨(2719398481543709835980531521027 / 12500000000000000000000000000000), (8093643753 / 100000000000000000000000000000000)⟩
def CA3_6_7I2R2Mass : Ball := ⟨(1395313867154386269020145935309 / 25000000000000000000000000000000), (7 / 20000000000000000000000000000000)⟩
def CA3_6_7I2R2MassTermLogWitness : LogWitness := ⟨-5, 1395313867154386269020145935309, 781250000000000000000000000000⟩
def CA3_6_7I2R2MassTermLog : Ball := ⟨(-288575644052640630693851869710027 / 100000000000000000000000000000000), (5082197709 / 4000000000000000000000000000000)⟩
def CA3_6_7I2R2MassTerm : Ball := ⟨(1610614391478630667960520793111 / 10000000000000000000000000000000), (7091261041 / 100000000000000000000000000000000)⟩
def CA3_6_7I2R2H : Ball := ⟨(2824521968781686004119522118553 / 50000000000000000000000000000000), (7592452397 / 50000000000000000000000000000000)⟩
def CA3_6_7I2R3Entropy : Ball := ⟨(40346546045806459693540131485657 / 50000000000000000000000000000000), (6238889 / 15625000000000000000000000000)⟩
def CA3_6_7I2R3Mass : Ball := ⟨(10834577778206780039035944465507 / 25000000000000000000000000000000), (3 / 2500000000000000000000000000000)⟩
def CA3_6_7I2R3MassTermLogWitness : LogWitness := ⟨-2, 10834577778206780039035944465507, 6250000000000000000000000000000⟩
def CA3_6_7I2R3MassTermLog : Ball := ⟨(-41806657948170529576606332041273 / 50000000000000000000000000000000), (31763735663 / 50000000000000000000000000000000)⟩
def CA3_6_7I2R3MassTerm : Ball := ⟨(9059149743726805557353515876951 / 25000000000000000000000000000000), (13765866633 / 50000000000000000000000000000000)⟩
def CA3_6_7I2R3H : Ball := ⟨(4445649311670569715766619946351 / 10000000000000000000000000000000), (33730311433 / 50000000000000000000000000000000)⟩
def CA3_6_7I2R4Entropy : Ball := ⟨(8564389467046437772836728256693 / 12500000000000000000000000000000), (6385750057 / 20000000000000000000000000000000)⟩
def CA3_6_7I2R4Mass : Ball := ⟨(4735986048838671198084086130441 / 12500000000000000000000000000000), (113 / 100000000000000000000000000000000)⟩
def CA3_6_7I2R4MassTermLogWitness : LogWitness := ⟨-2, 4735986048838671198084086130441, 3125000000000000000000000000000⟩
def CA3_6_7I2R4MassTermLog : Ball := ⟨(-24263467312493783074333674577909 / 25000000000000000000000000000000), (63527471347 / 100000000000000000000000000000000)⟩
def CA3_6_7I2R4MassTerm : Ball := ⟨(36771661660295578856776336701901 / 100000000000000000000000000000000), (1504326097 / 6250000000000000000000000000000)⟩
def CA3_6_7I2R4H : Ball := ⟨(31743454076075923325917489351643 / 100000000000000000000000000000000), (55997967837 / 100000000000000000000000000000000)⟩
def CA3_6_7I2R5Entropy : Ball := ⟨(1740376091767025966062209505709 / 12500000000000000000000000000000), (2474681907 / 50000000000000000000000000000000)⟩
def CA3_6_7I2R5Mass : Ball := ⟨(162459422574586507568322112067 / 5000000000000000000000000000000), (11 / 50000000000000000000000000000000)⟩
def CA3_6_7I2R5MassTermLogWitness : LogWitness := ⟨-5, 162459422574586507568322112067, 156250000000000000000000000000⟩
def CA3_6_7I2R5MassTermLog : Ball := ⟨(-342676492806180126403811039545367 / 100000000000000000000000000000000), (63527471387 / 50000000000000000000000000000000)⟩
def CA3_6_7I2R5MassTerm : Ball := ⟨(11134205030235294118142875014453 / 100000000000000000000000000000000), (1032063651 / 25000000000000000000000000000000)⟩
def CA3_6_7I2R5H : Ball := ⟨(2788803703900913610354801031219 / 100000000000000000000000000000000), (4538809209 / 50000000000000000000000000000000)⟩
def CA3_6_7I2R6Entropy : Ball := ⟨(244765065010678833786572623483 / 100000000000000000000000000000000), (10342263 / 12500000000000000000000000000000)⟩
def CA3_6_7I2R6Mass : Ball := ⟨(1487769489664154864336262869 / 5000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def CA3_6_7I2R6MassTermLogWitness : LogWitness := ⟨-12, 1487769489664154864336262869, 1220703125000000000000000000⟩
def CA3_6_7I2R6MassTermLog : Ball := ⟨(-811991517986568473916712948623463 / 100000000000000000000000000000000), (275285728043 / 100000000000000000000000000000000)⟩
def CA3_6_7I2R6MassTerm : Ball := ⟨(241611241265299880754628677639 / 100000000000000000000000000000000), (81912391 / 100000000000000000000000000000000)⟩
def CA3_6_7I2R6H : Ball := ⟨(788455936344738257985986461 / 25000000000000000000000000000000), (32930099 / 20000000000000000000000000000000)⟩
def CA3_6_7I2R7Entropy : Ball := ⟨0, 0⟩
def CA3_6_7I2R7Mass : Ball := ⟨0, 0⟩
def CA3_6_7I2R7MassTerm : Ball := .exact 0
def CA3_6_7I2R7H : Ball := ⟨0, 0⟩
def CA3_6_7I2R8Entropy : Ball := ⟨0, 0⟩
def CA3_6_7I2R8Mass : Ball := ⟨0, 0⟩
def CA3_6_7I2R8MassTerm : Ball := .exact 0
def CA3_6_7I2R8H : Ball := ⟨0, 0⟩
def CA3_6_7I2R9Entropy : Ball := ⟨0, 0⟩
def CA3_6_7I2R9Mass : Ball := ⟨0, 0⟩
def CA3_6_7I2R9MassTerm : Ball := .exact 0
def CA3_6_7I2R9H : Ball := ⟨0, 0⟩
def CA3_6_7I2R10Entropy : Ball := ⟨0, 0⟩
def CA3_6_7I2R10Mass : Ball := ⟨0, 0⟩
def CA3_6_7I2R10MassTerm : Ball := .exact 0
def CA3_6_7I2R10H : Ball := ⟨0, 0⟩
def CA3_6_7I2R11Entropy : Ball := ⟨0, 0⟩
def CA3_6_7I2R11Mass : Ball := ⟨0, 0⟩
def CA3_6_7I2R11MassTerm : Ball := .exact 0
def CA3_6_7I2R11H : Ball := ⟨0, 0⟩
def CA3_6_7I2R12Entropy : Ball := ⟨0, 0⟩
def CA3_6_7I2R12Mass : Ball := ⟨0, 0⟩
def CA3_6_7I2R12MassTerm : Ball := .exact 0
def CA3_6_7I2R12H : Ball := ⟨0, 0⟩
def CA3_6_7I2R13Entropy : Ball := ⟨0, 0⟩
def CA3_6_7I2R13Mass : Ball := ⟨0, 0⟩
def CA3_6_7I2R13MassTerm : Ball := .exact 0
def CA3_6_7I2R13H : Ball := ⟨0, 0⟩
def CA3_6_7I2R14Entropy : Ball := ⟨0, 0⟩
def CA3_6_7I2R14Mass : Ball := ⟨0, 0⟩
def CA3_6_7I2R14MassTerm : Ball := .exact 0
def CA3_6_7I2R14H : Ball := ⟨0, 0⟩
def CA3_6_7I2R15Entropy : Ball := ⟨0, 0⟩
def CA3_6_7I2R15Mass : Ball := ⟨0, 0⟩
def CA3_6_7I2R15MassTerm : Ball := .exact 0
def CA3_6_7I2R15H : Ball := ⟨0, 0⟩
def CA3_6_7I2R16Entropy : Ball := ⟨0, 0⟩
def CA3_6_7I2R16Mass : Ball := ⟨0, 0⟩
def CA3_6_7I2R16MassTerm : Ball := .exact 0
def CA3_6_7I2R16H : Ball := ⟨0, 0⟩
def CA3_6_7I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA3_6_7I2R0H
  | 1 => CA3_6_7I2R1H
  | 2 => CA3_6_7I2R2H
  | 3 => CA3_6_7I2R3H
  | 4 => CA3_6_7I2R4H
  | 5 => CA3_6_7I2R5H
  | 6 => CA3_6_7I2R6H
  | 7 => CA3_6_7I2R7H
  | 8 => CA3_6_7I2R8H
  | 9 => CA3_6_7I2R9H
  | 10 => CA3_6_7I2R10H
  | 11 => CA3_6_7I2R11H
  | 12 => CA3_6_7I2R12H
  | 13 => CA3_6_7I2R13H
  | 14 => CA3_6_7I2R14H
  | 15 => CA3_6_7I2R15H
  | 16 => CA3_6_7I2R16H
  | _ => (.exact 0)
def CA3_6_7I2Singleton : Ball := ⟨(2956785446459103303223532671727 / 25000000000000000000000000000000), (992338599 / 10000000000000000000000000000000)⟩
def CA3_6_7I2Group : Ball := ⟨(96556640056048354052402923374077 / 100000000000000000000000000000000), (39608863527 / 25000000000000000000000000000000)⟩

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
def CA3_6_7I2H : Ball := ⟨(53605050537661449114373976696383 / 50000000000000000000000000000000), (455932049331 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA4_4_8I0
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
def CA4_4_8I0Value (a : Fin 17) : ℝ := marginal (below (shape 4 4 8)) (fun u => (stageALaw (shape 4 4 8) u : ℝ)) ((Equiv.refl (Fin 3)) 0) a
def CA4_4_8I0Entropy : Ball := ⟨(237828189850981917108409227793 / 195312500000000000000000000000), (77721914423 / 100000000000000000000000000000000)⟩
def CA4_4_8I0Mass : Ball := ⟨(49999999999999999999999999999999 / 50000000000000000000000000000000), (179 / 50000000000000000000000000000000)⟩
def CA4_4_8I0MassTermLogWitness : LogWitness := ⟨-1, 49999999999999999999999999999999, 25000000000000000000000000000000⟩
def CA4_4_8I0MassTermLog : Ball := ⟨(-1 / 100000000000000000000000000000000), (10587911931 / 25000000000000000000000000000000)⟩
def CA4_4_8I0MassTerm : Ball := ⟨(1 / 100000000000000000000000000000000), (1694065909 / 4000000000000000000000000000000)⟩
def CA4_4_8I0H : Ball := ⟨(24353606640740548311901104926003 / 20000000000000000000000000000000), (30018390537 / 25000000000000000000000000000000)⟩

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
def CA4_4_8I1PairEntropy : Ball := ⟨(308850256342829279281678118501801 / 100000000000000000000000000000000), (32371590663 / 25000000000000000000000000000000)⟩
def CA4_4_8I1PairMass : Ball := ⟨(100000000000000000000000000000001 / 100000000000000000000000000000000), (331 / 50000000000000000000000000000000)⟩
def CA4_4_8I1PairMassTermLogWitness : LogWitness := ⟨0, 100000000000000000000000000000001, 100000000000000000000000000000000⟩
def CA4_4_8I1PairMassTermLog : Ball := ⟨(1 / 100000000000000000000000000000000), (2646978043 / 12500000000000000000000000000000)⟩
def CA4_4_8I1PairMassTerm : Ball := ⟨(-1 / 100000000000000000000000000000000), (4235164869 / 20000000000000000000000000000000)⟩
def CA4_4_8I1PairH : Ball := ⟨(154425128171414639640839059250901 / 50000000000000000000000000000000), (150662186997 / 100000000000000000000000000000000)⟩

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
def CA4_4_8I1R0Entropy : Ball := ⟨(4760412769112588948014764417159 / 50000000000000000000000000000000), (483969577 / 12500000000000000000000000000000)⟩
def CA4_4_8I1R0Mass : Ball := ⟨(10203043120648639286547464097 / 390625000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
def CA4_4_8I1R0MassTermLogWitness : LogWitness := ⟨-6, 10203043120648639286547464097, 6103515625000000000000000000⟩
def CA4_4_8I1R0MassTermLog : Ball := ⟨(-91126549988371926878531538134997 / 25000000000000000000000000000000), (14823076647 / 10000000000000000000000000000000)⟩
def CA4_4_8I1R0MassTerm : Ball := ⟨(4760412769112588948014764417159 / 50000000000000000000000000000000), (483969577 / 12500000000000000000000000000000)⟩
def CA4_4_8I1R0H : Ball := ⟨0, (483969577 / 6250000000000000000000000000000)⟩
def CA4_4_8I1R1Entropy : Ball := ⟨(4991801634033016332264529747017 / 10000000000000000000000000000000), (6127559147 / 25000000000000000000000000000000)⟩
def CA4_4_8I1R1Mass : Ball := ⟨(11574631800747792340835551260257 / 50000000000000000000000000000000), (29 / 25000000000000000000000000000000)⟩
def CA4_4_8I1R1MassTermLogWitness : LogWitness := ⟨-3, 11574631800747792340835551260257, 6250000000000000000000000000000⟩
def CA4_4_8I1R1MassTermLog : Ball := ⟨(-146320721583239404426945632322161 / 100000000000000000000000000000000), (84703295233 / 100000000000000000000000000000000)⟩
def CA4_4_8I1R1MassTerm : Ball := ⟨(4234021192864316680996658137711 / 12500000000000000000000000000000), (19608189263 / 100000000000000000000000000000000)⟩
def CA4_4_8I1R1H : Ball := ⟨(8022923398707814937336016184241 / 50000000000000000000000000000000), (44118425851 / 100000000000000000000000000000000)⟩
def CA4_4_8I1R2Entropy : Ball := ⟨(42295276331446539552996156842209 / 50000000000000000000000000000000), (19825311793 / 50000000000000000000000000000000)⟩
def CA4_4_8I1R2Mass : Ball := ⟨(24238757359618363660972746670653 / 50000000000000000000000000000000), (221 / 100000000000000000000000000000000)⟩
def CA4_4_8I1R2MassTermLogWitness : LogWitness := ⟨-2, 24238757359618363660972746670653, 12500000000000000000000000000000⟩
def CA4_4_8I1R2MassTermLog : Ball := ⟨(-7240701095832249874519106100029 / 10000000000000000000000000000000), (3970466969 / 6250000000000000000000000000000)⟩
def CA4_4_8I1R2MassTerm : Ball := ⟨(35101119395080139462631003646157 / 100000000000000000000000000000000), (3079653951 / 10000000000000000000000000000000)⟩
def CA4_4_8I1R2H : Ball := ⟨(49489433267812939643361310038261 / 100000000000000000000000000000000), (8805895387 / 12500000000000000000000000000000)⟩
def CA4_4_8I1R3Entropy : Ball := ⟨(236468866107331943318081814259 / 400000000000000000000000000000), (3291546349 / 12500000000000000000000000000000)⟩
def CA4_4_8I1R3Mass : Ball := ⟨(11574631800747792340835551260257 / 50000000000000000000000000000000), (61 / 50000000000000000000000000000000)⟩
def CA4_4_8I1R3MassTermLogWitness : LogWitness := ⟨-3, 11574631800747792340835551260257, 6250000000000000000000000000000⟩
def CA4_4_8I1R3MassTermLog : Ball := ⟨(-146320721583239404426945632322161 / 100000000000000000000000000000000), (84703295259 / 100000000000000000000000000000000)⟩
def CA4_4_8I1R3MassTerm : Ball := ⟨(4234021192864316680996658137711 / 12500000000000000000000000000000), (9804094639 / 50000000000000000000000000000000)⟩
def CA4_4_8I1R3H : Ball := ⟨(12622523491959226190773594231531 / 50000000000000000000000000000000), (4594056007 / 10000000000000000000000000000000)⟩
def CA4_4_8I1R4Entropy : Ball := ⟨(12222052254233571303206328305513 / 100000000000000000000000000000000), (888135627 / 20000000000000000000000000000000)⟩
def CA4_4_8I1R4Mass : Ball := ⟨(130598648384254758648132819459 / 5000000000000000000000000000000), (7 / 25000000000000000000000000000000)⟩
def CA4_4_8I1R4MassTermLogWitness : LogWitness := ⟨-6, 130598648384254758648132819459, 78125000000000000000000000000⟩
def CA4_4_8I1R4MassTermLog : Ball := ⟨(-91126608097643880853565541221611 / 25000000000000000000000000000000), (148230766853 / 100000000000000000000000000000000)⟩
def CA4_4_8I1R4MassTerm : Ball := ⟨(148762648117424695324148511307 / 1562500000000000000000000000000), (3871747663 / 100000000000000000000000000000000)⟩
def CA4_4_8I1R4H : Ball := ⟨(540248554943678160492164716373 / 20000000000000000000000000000000), (4156212899 / 50000000000000000000000000000000)⟩
def CA4_4_8I1R5Entropy : Ball := ⟨0, 0⟩
def CA4_4_8I1R5Mass : Ball := ⟨0, 0⟩
def CA4_4_8I1R5MassTerm : Ball := .exact 0
def CA4_4_8I1R5H : Ball := ⟨0, 0⟩
def CA4_4_8I1R6Entropy : Ball := ⟨0, 0⟩
def CA4_4_8I1R6Mass : Ball := ⟨0, 0⟩
def CA4_4_8I1R6MassTerm : Ball := .exact 0
def CA4_4_8I1R6H : Ball := ⟨0, 0⟩
def CA4_4_8I1R7Entropy : Ball := ⟨0, 0⟩
def CA4_4_8I1R7Mass : Ball := ⟨0, 0⟩
def CA4_4_8I1R7MassTerm : Ball := .exact 0
def CA4_4_8I1R7H : Ball := ⟨0, 0⟩
def CA4_4_8I1R8Entropy : Ball := ⟨0, 0⟩
def CA4_4_8I1R8Mass : Ball := ⟨0, 0⟩
def CA4_4_8I1R8MassTerm : Ball := .exact 0
def CA4_4_8I1R8H : Ball := ⟨0, 0⟩
def CA4_4_8I1R9Entropy : Ball := ⟨0, 0⟩
def CA4_4_8I1R9Mass : Ball := ⟨0, 0⟩
def CA4_4_8I1R9MassTerm : Ball := .exact 0
def CA4_4_8I1R9H : Ball := ⟨0, 0⟩
def CA4_4_8I1R10Entropy : Ball := ⟨0, 0⟩
def CA4_4_8I1R10Mass : Ball := ⟨0, 0⟩
def CA4_4_8I1R10MassTerm : Ball := .exact 0
def CA4_4_8I1R10H : Ball := ⟨0, 0⟩
def CA4_4_8I1R11Entropy : Ball := ⟨0, 0⟩
def CA4_4_8I1R11Mass : Ball := ⟨0, 0⟩
def CA4_4_8I1R11MassTerm : Ball := .exact 0
def CA4_4_8I1R11H : Ball := ⟨0, 0⟩
def CA4_4_8I1R12Entropy : Ball := ⟨0, 0⟩
def CA4_4_8I1R12Mass : Ball := ⟨0, 0⟩
def CA4_4_8I1R12MassTerm : Ball := .exact 0
def CA4_4_8I1R12H : Ball := ⟨0, 0⟩
def CA4_4_8I1R13Entropy : Ball := ⟨0, 0⟩
def CA4_4_8I1R13Mass : Ball := ⟨0, 0⟩
def CA4_4_8I1R13MassTerm : Ball := .exact 0
def CA4_4_8I1R13H : Ball := ⟨0, 0⟩
def CA4_4_8I1R14Entropy : Ball := ⟨0, 0⟩
def CA4_4_8I1R14Mass : Ball := ⟨0, 0⟩
def CA4_4_8I1R14MassTerm : Ball := .exact 0
def CA4_4_8I1R14H : Ball := ⟨0, 0⟩
def CA4_4_8I1R15Entropy : Ball := ⟨0, 0⟩
def CA4_4_8I1R15Mass : Ball := ⟨0, 0⟩
def CA4_4_8I1R15MassTerm : Ball := .exact 0
def CA4_4_8I1R15H : Ball := ⟨0, 0⟩
def CA4_4_8I1R16Entropy : Ball := ⟨0, 0⟩
def CA4_4_8I1R16Mass : Ball := ⟨0, 0⟩
def CA4_4_8I1R16MassTerm : Ball := .exact 0
def CA4_4_8I1R16H : Ball := ⟨0, 0⟩
def CA4_4_8I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA4_4_8I1R0H
  | 1 => CA4_4_8I1R1H
  | 2 => CA4_4_8I1R2H
  | 3 => CA4_4_8I1R3H
  | 4 => CA4_4_8I1R4H
  | 5 => CA4_4_8I1R5H
  | 6 => CA4_4_8I1R6H
  | 7 => CA4_4_8I1R7H
  | 8 => CA4_4_8I1R8H
  | 9 => CA4_4_8I1R9H
  | 10 => CA4_4_8I1R10H
  | 11 => CA4_4_8I1R11H
  | 12 => CA4_4_8I1R12H
  | 13 => CA4_4_8I1R13H
  | 14 => CA4_4_8I1R14H
  | 15 => CA4_4_8I1R15H
  | 16 => CA4_4_8I1R16H
  | _ => (.exact 0)
def CA4_4_8I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 4, 4, 0 => Z4_4_0H1H
  | _, _, _ => (.exact 0)
def CA4_4_8I1Singleton : Ball := ⟨(119273563983486045807973 / 1562500000000000000000000000000), (1607 / 25000000000000000000000000000000)⟩
def CA4_4_8I1Group : Ball := ⟨(46740788728686753822574143080971 / 50000000000000000000000000000000), (7062483779 / 4000000000000000000000000000000)⟩

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
def CA4_4_8I1H : Ball := ⟨(60943550714041131995690773088959 / 50000000000000000000000000000000), (503786375947 / 100000000000000000000000000000000)⟩

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
def CA4_4_8I2PairEntropy : Ball := ⟨(277590657874130194496323896621127 / 100000000000000000000000000000000), (114789632413 / 100000000000000000000000000000000)⟩
def CA4_4_8I2PairMass : Ball := ⟨(99999999999999999999999999999987 / 100000000000000000000000000000000), (793 / 100000000000000000000000000000000)⟩
def CA4_4_8I2PairMassTermLogWitness : LogWitness := ⟨-1, 99999999999999999999999999999987, 50000000000000000000000000000000⟩
def CA4_4_8I2PairMassTermLog : Ball := ⟨(-3 / 25000000000000000000000000000000), (42351648159 / 100000000000000000000000000000000)⟩
def CA4_4_8I2PairMassTerm : Ball := ⟨(3 / 25000000000000000000000000000000), (264697801 / 625000000000000000000000000000)⟩
def CA4_4_8I2PairH : Ball := ⟨(55518131574826038899264779324223 / 20000000000000000000000000000000), (157141280573 / 100000000000000000000000000000000)⟩

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
def CA4_4_8I2R0Entropy : Ball := ⟨(100885900988501493060513433 / 100000000000000000000000000000000), (32159 / 100000000000000000000000000000000)⟩
def CA4_4_8I2R0Mass : Ball := ⟨(3035600478242196747209827 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def CA4_4_8I2R0MassTermLogWitness : LogWitness := ⟨-24, 3035600478242196747209827, 2980232238769531250000000⟩
def CA4_4_8I2R0MassTermLog : Ball := ⟨(-415428107682506870021708107576163 / 25000000000000000000000000000000), (6617650791 / 1250000000000000000000000000000)⟩
def CA4_4_8I2R0MassTerm : Ball := ⟨(100885900988501493060513433 / 100000000000000000000000000000000), (32159 / 100000000000000000000000000000000)⟩
def CA4_4_8I2R0H : Ball := ⟨0, (32159 / 50000000000000000000000000000000)⟩
def CA4_4_8I2R1Entropy : Ball := ⟨(8364595743039152683402561227 / 12500000000000000000000000000000), (10965003 / 50000000000000000000000000000000)⟩
def CA4_4_8I2R1Mass : Ball := ⟨(809072654081018314756371891 / 12500000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
def CA4_4_8I2R1MassTermLogWitness : LogWitness := ⟨-14, 809072654081018314756371891, 762939453125000000000000000⟩
def CA4_4_8I2R1MassTermLog : Ball := ⟨(-964535048197697813685602414151053 / 100000000000000000000000000000000), (317637417043 / 100000000000000000000000000000000)⟩
def CA4_4_8I2R1MassTerm : Ball := ⟨(12486062902391588654992660491 / 20000000000000000000000000000000), (20559379 / 100000000000000000000000000000000)⟩
def CA4_4_8I2R1H : Ball := ⟨(4486451432355278192257187361 / 100000000000000000000000000000000), (8497877 / 20000000000000000000000000000000)⟩
def CA4_4_8I2R2Entropy : Ball := ⟨(4842314309154171101349504406353 / 100000000000000000000000000000000), (34848783 / 2000000000000000000000000000000)⟩
def CA4_4_8I2R2Mass : Ball := ⟨(167271198048058184994176476867 / 20000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
def CA4_4_8I2R2MassTermLogWitness : LogWitness := ⟨-7, 167271198048058184994176476867, 156250000000000000000000000000⟩
def CA4_4_8I2R2MassTermLog : Ball := ⟨(-1913548446750902621982351257567 / 400000000000000000000000000000), (84703295449 / 50000000000000000000000000000000)⟩
def CA4_4_8I2R2MassTerm : Ball := ⟨(250063704071112776882502314991 / 6250000000000000000000000000000), (1416842229 / 100000000000000000000000000000000)⟩
def CA4_4_8I2R2H : Ball := ⟨(841295044016366671229467366497 / 100000000000000000000000000000000), (3159281379 / 100000000000000000000000000000000)⟩
def CA4_4_8I2R3Entropy : Ball := ⟨(965071419989512771136140668901 / 2000000000000000000000000000000), (9912913627 / 50000000000000000000000000000000)⟩
def CA4_4_8I2R3Mass : Ball := ⟨(2198754904646018241523616143957 / 12500000000000000000000000000000), (49 / 50000000000000000000000000000000)⟩
def CA4_4_8I2R3MassTermLogWitness : LogWitness := ⟨-3, 2198754904646018241523616143957, 1562500000000000000000000000000⟩
def CA4_4_8I2R3MassTermLog : Ball := ⟨(-173783739658914282888710670776333 / 100000000000000000000000000000000), (10587911911 / 12500000000000000000000000000000)⟩
def CA4_4_8I2R3MassTerm : Ball := ⟨(30568627993821162617363647220061 / 100000000000000000000000000000000), (14899343047 / 100000000000000000000000000000000)⟩
def CA4_4_8I2R3H : Ball := ⟨(17684943005654475939443386224989 / 100000000000000000000000000000000), (34725170301 / 100000000000000000000000000000000)⟩
def CA4_4_8I2R4Entropy : Ball := ⟨(40672593295687207125656793739673 / 50000000000000000000000000000000), (606516093 / 1250000000000000000000000000000)⟩
def CA4_4_8I2R4Mass : Ball := ⟨(60999836269589822775266016196717 / 100000000000000000000000000000000), (53 / 20000000000000000000000000000000)⟩
def CA4_4_8I2R4MassTermLogWitness : LogWitness := ⟨-1, 60999836269589822775266016196717, 50000000000000000000000000000000⟩
def CA4_4_8I2R4MassTermLog : Ball := ⟨(-24714950296173360416017773017097 / 50000000000000000000000000000000), (211758239 / 500000000000000000000000000000)⟩
def CA4_4_8I2R4MassTerm : Ball := ⟨(942254950923515926994287812149 / 3125000000000000000000000000000), (25834435947 / 100000000000000000000000000000000)⟩
def CA4_4_8I2R4H : Ball := ⟨(25596514080910952293748188745289 / 50000000000000000000000000000000), (74355723387 / 100000000000000000000000000000000)⟩
def CA4_4_8I2R5Entropy : Ball := ⟨(20608350620764726935840034913327 / 50000000000000000000000000000000), (1641418899 / 10000000000000000000000000000000)⟩
def CA4_4_8I2R5Mass : Ball := ⟨(932211631179929584578895179769 / 6250000000000000000000000000000), (1 / 1250000000000000000000000000000)⟩
def CA4_4_8I2R5MassTermLogWitness : LogWitness := ⟨-3, 932211631179929584578895179769, 781250000000000000000000000000⟩
def CA4_4_8I2R5MassTermLog : Ball := ⟨(-2973088877719296093409086138257 / 1562500000000000000000000000000), (21175823817 / 25000000000000000000000000000000)⟩
def CA4_4_8I2R5MassTerm : Ball := ⟨(28380651851178098873272106745451 / 100000000000000000000000000000000), (12633823681 / 100000000000000000000000000000000)⟩
def CA4_4_8I2R5H : Ball := ⟨(12836049390351354998407963081203 / 100000000000000000000000000000000), (29048012671 / 100000000000000000000000000000000)⟩
def CA4_4_8I2R6Entropy : Ball := ⟨(62052490728871733419264032607 / 2500000000000000000000000000000), (871286391 / 100000000000000000000000000000000)⟩
def CA4_4_8I2R6Mass : Ball := ⟨(90121904226141243243038230063 / 20000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
def CA4_4_8I2R6MassTermLogWitness : LogWitness := ⟨-8, 90121904226141243243038230063, 78125000000000000000000000000⟩
def CA4_4_8I2R6MassTermLog : Ball := ⟨(-270116215365013740043416369183291 / 50000000000000000000000000000000), (95291207461 / 50000000000000000000000000000000)⟩
def CA4_4_8I2R6MassTerm : Ball := ⟨(2434338769105351000162219863469 / 100000000000000000000000000000000), (858782551 / 100000000000000000000000000000000)⟩
def CA4_4_8I2R6H : Ball := ⟨(47760860049518336608341440811 / 100000000000000000000000000000000), (865034471 / 50000000000000000000000000000000)⟩
def CA4_4_8I2R7Entropy : Ball := ⟨0, 0⟩
def CA4_4_8I2R7Mass : Ball := ⟨0, 0⟩
def CA4_4_8I2R7MassTerm : Ball := .exact 0
def CA4_4_8I2R7H : Ball := ⟨0, 0⟩
def CA4_4_8I2R8Entropy : Ball := ⟨0, 0⟩
def CA4_4_8I2R8Mass : Ball := ⟨0, 0⟩
def CA4_4_8I2R8MassTerm : Ball := .exact 0
def CA4_4_8I2R8H : Ball := ⟨0, 0⟩
def CA4_4_8I2R9Entropy : Ball := ⟨0, 0⟩
def CA4_4_8I2R9Mass : Ball := ⟨0, 0⟩
def CA4_4_8I2R9MassTerm : Ball := .exact 0
def CA4_4_8I2R9H : Ball := ⟨0, 0⟩
def CA4_4_8I2R10Entropy : Ball := ⟨0, 0⟩
def CA4_4_8I2R10Mass : Ball := ⟨0, 0⟩
def CA4_4_8I2R10MassTerm : Ball := .exact 0
def CA4_4_8I2R10H : Ball := ⟨0, 0⟩
def CA4_4_8I2R11Entropy : Ball := ⟨0, 0⟩
def CA4_4_8I2R11Mass : Ball := ⟨0, 0⟩
def CA4_4_8I2R11MassTerm : Ball := .exact 0
def CA4_4_8I2R11H : Ball := ⟨0, 0⟩
def CA4_4_8I2R12Entropy : Ball := ⟨0, 0⟩
def CA4_4_8I2R12Mass : Ball := ⟨0, 0⟩
def CA4_4_8I2R12MassTerm : Ball := .exact 0
def CA4_4_8I2R12H : Ball := ⟨0, 0⟩
def CA4_4_8I2R13Entropy : Ball := ⟨0, 0⟩
def CA4_4_8I2R13Mass : Ball := ⟨0, 0⟩
def CA4_4_8I2R13MassTerm : Ball := .exact 0
def CA4_4_8I2R13H : Ball := ⟨0, 0⟩
def CA4_4_8I2R14Entropy : Ball := ⟨0, 0⟩
def CA4_4_8I2R14Mass : Ball := ⟨0, 0⟩
def CA4_4_8I2R14MassTerm : Ball := .exact 0
def CA4_4_8I2R14H : Ball := ⟨0, 0⟩
def CA4_4_8I2R15Entropy : Ball := ⟨0, 0⟩
def CA4_4_8I2R15Mass : Ball := ⟨0, 0⟩
def CA4_4_8I2R15MassTerm : Ball := .exact 0
def CA4_4_8I2R15H : Ball := ⟨0, 0⟩
def CA4_4_8I2R16Entropy : Ball := ⟨0, 0⟩
def CA4_4_8I2R16Mass : Ball := ⟨0, 0⟩
def CA4_4_8I2R16MassTerm : Ball := .exact 0
def CA4_4_8I2R16H : Ball := ⟨0, 0⟩
def CA4_4_8I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA4_4_8I2R0H
  | 1 => CA4_4_8I2R1H
  | 2 => CA4_4_8I2R2H
  | 3 => CA4_4_8I2R3H
  | 4 => CA4_4_8I2R4H
  | 5 => CA4_4_8I2R5H
  | 6 => CA4_4_8I2R6H
  | 7 => CA4_4_8I2R7H
  | 8 => CA4_4_8I2R8H
  | 9 => CA4_4_8I2R9H
  | 10 => CA4_4_8I2R10H
  | 11 => CA4_4_8I2R11H
  | 12 => CA4_4_8I2R12H
  | 13 => CA4_4_8I2R13H
  | 14 => CA4_4_8I2R14H
  | 15 => CA4_4_8I2R15H
  | 16 => CA4_4_8I2R16H
  | _ => (.exact 0)
def CA4_4_8I2Singleton : Ball := ⟨(6400259021839332148975225827439 / 100000000000000000000000000000000), (2472876643 / 50000000000000000000000000000000)⟩
def CA4_4_8I2Group : Ball := ⟨(44503910967582653980176509309439 / 50000000000000000000000000000000), (148006563669 / 100000000000000000000000000000000)⟩

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
def CA4_4_8I2H : Ball := ⟨(99575014003799578575617859383359 / 100000000000000000000000000000000), (453154407911 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA4_5_7I0
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
def CA4_5_7I0Value (a : Fin 17) : ℝ := marginal (below (shape 4 5 7)) (fun u => (stageALaw (shape 4 5 7) u : ℝ)) ((Equiv.refl (Fin 3)) 0) a
def CA4_5_7I0Entropy : Ball := ⟨(121770579021978154205728038513521 / 100000000000000000000000000000000), (38861318809 / 50000000000000000000000000000000)⟩
def CA4_5_7I0Mass : Ball := ⟨1, (61 / 25000000000000000000000000000000)⟩
def CA4_5_7I0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CA4_5_7I0MassTermLog : Ball := ⟨0, (10587911963 / 50000000000000000000000000000000)⟩
def CA4_5_7I0MassTerm : Ball := ⟨0, (21175823927 / 100000000000000000000000000000000)⟩
def CA4_5_7I0H : Ball := ⟨(121770579021978154205728038513521 / 100000000000000000000000000000000), (19779692309 / 20000000000000000000000000000000)⟩

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
def CA4_5_7I1PairEntropy : Ball := ⟨(79691337278687147638616213846057 / 25000000000000000000000000000000), (32389139629 / 25000000000000000000000000000000)⟩
def CA4_5_7I1PairMass : Ball := ⟨(12500000000000000000000000000001 / 12500000000000000000000000000000), (71 / 12500000000000000000000000000000)⟩
def CA4_5_7I1PairMassTermLogWitness : LogWitness := ⟨0, 12500000000000000000000000000001, 12500000000000000000000000000000⟩
def CA4_5_7I1PairMassTermLog : Ball := ⟨(1 / 12500000000000000000000000000000), (84703297 / 400000000000000000000000000000)⟩
def CA4_5_7I1PairMassTerm : Ball := ⟨(-1 / 12500000000000000000000000000000), (21175824251 / 100000000000000000000000000000000)⟩
def CA4_5_7I1PairH : Ball := ⟨(79691337278687147638616213846059 / 25000000000000000000000000000000), (150732382767 / 100000000000000000000000000000000)⟩

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
def CA4_5_7I1R0Entropy : Ball := ⟨(1617754235717366730301305147667 / 100000000000000000000000000000000), (580740483 / 100000000000000000000000000000000)⟩
def CA4_5_7I1R0Mass : Ball := ⟨(274246922597902442652317637103 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
def CA4_5_7I1R0MassTermLogWitness : LogWitness := ⟨-9, 274246922597902442652317637103, 195312500000000000000000000000⟩
def CA4_5_7I1R0MassTermLog : Ball := ⟨(-147472414675852045839935424960033 / 25000000000000000000000000000000), (211758238653 / 100000000000000000000000000000000)⟩
def CA4_5_7I1R0MassTerm : Ball := ⟨(1617754235717366730301305147667 / 100000000000000000000000000000000), (580740483 / 100000000000000000000000000000000)⟩
def CA4_5_7I1R0H : Ball := ⟨0, (580740483 / 50000000000000000000000000000000)⟩
def CA4_5_7I1R1Entropy : Ball := ⟨(13601674597694605000986940575089 / 50000000000000000000000000000000), (5505752523 / 50000000000000000000000000000000)⟩
def CA4_5_7I1R1Mass : Ball := ⟨(433336345409804315292274935367 / 5000000000000000000000000000000), (23 / 50000000000000000000000000000000)⟩
def CA4_5_7I1R1MassTermLogWitness : LogWitness := ⟨-4, 433336345409804315292274935367, 312500000000000000000000000000⟩
def CA4_5_7I1R1MassTermLog : Ball := ⟨(-122283949285658722951672162212549 / 50000000000000000000000000000000), (21175823789 / 20000000000000000000000000000000)⟩
def CA4_5_7I1R1MassTerm : Ball := ⟨(10598015937145040405897974413661 / 50000000000000000000000000000000), (1835250841 / 20000000000000000000000000000000)⟩
def CA4_5_7I1R1H : Ball := ⟨(750914665137391148772241540357 / 12500000000000000000000000000000), (20187759251 / 100000000000000000000000000000000)⟩
def CA4_5_7I1R2Entropy : Ball := ⟨(7813934809360427089096774128201 / 10000000000000000000000000000000), (33469182719 / 100000000000000000000000000000000)⟩
def CA4_5_7I1R2Mass : Ball := ⟨(41059026169206011251502183655559 / 100000000000000000000000000000000), (39 / 25000000000000000000000000000000)⟩
def CA4_5_7I1R2MassTermLogWitness : LogWitness := ⟨-2, 41059026169206011251502183655559, 25000000000000000000000000000000⟩
def CA4_5_7I1R2MassTermLog : Ball := ⟨(-44507974597047939457626321697919 / 50000000000000000000000000000000), (15881867857 / 25000000000000000000000000000000)⟩
def CA4_5_7I1R2MassTerm : Ball := ⟨(9137270468592738599433860267587 / 25000000000000000000000000000000), (13041880629 / 50000000000000000000000000000000)⟩
def CA4_5_7I1R2H : Ball := ⟨(20795133109616658246616150105831 / 50000000000000000000000000000000), (59552943977 / 100000000000000000000000000000000)⟩
def CA4_5_7I1R3Entropy : Ball := ⟨(20119932829788400800803494434161 / 25000000000000000000000000000000), (9599990053 / 25000000000000000000000000000000)⟩
def CA4_5_7I1R3Mass : Ball := ⟨(1026475654230150281287554591389 / 2500000000000000000000000000000), (59 / 50000000000000000000000000000000)⟩
def CA4_5_7I1R3MassTermLogWitness : LogWitness := ⟨-2, 1026475654230150281287554591389, 625000000000000000000000000000⟩
def CA4_5_7I1R3MassTermLog : Ball := ⟨(-22253987298523969728813160848959 / 25000000000000000000000000000000), (7940933917 / 12500000000000000000000000000000)⟩
def CA4_5_7I1R3MassTerm : Ball := ⟨(9137270468592738599433860267587 / 25000000000000000000000000000000), (13041880593 / 50000000000000000000000000000000)⟩
def CA4_5_7I1R3H : Ball := ⟨(5491331180597831100684817083287 / 12500000000000000000000000000000), (32241860699 / 50000000000000000000000000000000)⟩
def CA4_5_7I1R4Entropy : Ball := ⟨(29394647576223133249001703349923 / 100000000000000000000000000000000), (5656646089 / 50000000000000000000000000000000)⟩
def CA4_5_7I1R4Mass : Ball := ⟨(1733273090106455195757138116287 / 20000000000000000000000000000000), (27 / 50000000000000000000000000000000)⟩
def CA4_5_7I1R4MassTermLogWitness : LogWitness := ⟨-4, 1733273090106455195757138116287, 1250000000000000000000000000000⟩
def CA4_5_7I1R4MassTermLog : Ball := ⟨(-122286034647326346589745223372571 / 50000000000000000000000000000000), (52939559519 / 50000000000000000000000000000000)⟩
def CA4_5_7I1R4MassTerm : Ball := ⟨(4239101863000727614975279320073 / 20000000000000000000000000000000), (2293967881 / 25000000000000000000000000000000)⟩
def CA4_5_7I1R4H : Ball := ⟨(4099569130609747587062653374779 / 50000000000000000000000000000000), (10244581851 / 50000000000000000000000000000000)⟩
def CA4_5_7I1R5Entropy : Ball := ⟨(14914328921679276033228790387 / 781250000000000000000000000000), (41386421 / 6250000000000000000000000000000)⟩
def CA4_5_7I1R5Mass : Ball := ⟨(68529940688064192565889625353 / 25000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
def CA4_5_7I1R5MassTermLogWitness : LogWitness := ⟨-9, 68529940688064192565889625353, 48828125000000000000000000000⟩
def CA4_5_7I1R5MassTermLog : Ball := ⟨(-294968018187080496147774346415151 / 50000000000000000000000000000000), (211758240477 / 100000000000000000000000000000000)⟩
def CA4_5_7I1R5MassTerm : Ball := ⟨(80856563164945865771325579269 / 5000000000000000000000000000000), (290235623 / 50000000000000000000000000000000)⟩
def CA4_5_7I1R5H : Ball := ⟨(72975709669007504206693396039 / 25000000000000000000000000000000), (621326991 / 50000000000000000000000000000000)⟩
def CA4_5_7I1R6Entropy : Ball := ⟨0, 0⟩
def CA4_5_7I1R6Mass : Ball := ⟨0, 0⟩
def CA4_5_7I1R6MassTerm : Ball := .exact 0
def CA4_5_7I1R6H : Ball := ⟨0, 0⟩
def CA4_5_7I1R7Entropy : Ball := ⟨0, 0⟩
def CA4_5_7I1R7Mass : Ball := ⟨0, 0⟩
def CA4_5_7I1R7MassTerm : Ball := .exact 0
def CA4_5_7I1R7H : Ball := ⟨0, 0⟩
def CA4_5_7I1R8Entropy : Ball := ⟨0, 0⟩
def CA4_5_7I1R8Mass : Ball := ⟨0, 0⟩
def CA4_5_7I1R8MassTerm : Ball := .exact 0
def CA4_5_7I1R8H : Ball := ⟨0, 0⟩
def CA4_5_7I1R9Entropy : Ball := ⟨0, 0⟩
def CA4_5_7I1R9Mass : Ball := ⟨0, 0⟩
def CA4_5_7I1R9MassTerm : Ball := .exact 0
def CA4_5_7I1R9H : Ball := ⟨0, 0⟩
def CA4_5_7I1R10Entropy : Ball := ⟨0, 0⟩
def CA4_5_7I1R10Mass : Ball := ⟨0, 0⟩
def CA4_5_7I1R10MassTerm : Ball := .exact 0
def CA4_5_7I1R10H : Ball := ⟨0, 0⟩
def CA4_5_7I1R11Entropy : Ball := ⟨0, 0⟩
def CA4_5_7I1R11Mass : Ball := ⟨0, 0⟩
def CA4_5_7I1R11MassTerm : Ball := .exact 0
def CA4_5_7I1R11H : Ball := ⟨0, 0⟩
def CA4_5_7I1R12Entropy : Ball := ⟨0, 0⟩
def CA4_5_7I1R12Mass : Ball := ⟨0, 0⟩
def CA4_5_7I1R12MassTerm : Ball := .exact 0
def CA4_5_7I1R12H : Ball := ⟨0, 0⟩
def CA4_5_7I1R13Entropy : Ball := ⟨0, 0⟩
def CA4_5_7I1R13Mass : Ball := ⟨0, 0⟩
def CA4_5_7I1R13MassTerm : Ball := .exact 0
def CA4_5_7I1R13H : Ball := ⟨0, 0⟩
def CA4_5_7I1R14Entropy : Ball := ⟨0, 0⟩
def CA4_5_7I1R14Mass : Ball := ⟨0, 0⟩
def CA4_5_7I1R14MassTerm : Ball := .exact 0
def CA4_5_7I1R14H : Ball := ⟨0, 0⟩
def CA4_5_7I1R15Entropy : Ball := ⟨0, 0⟩
def CA4_5_7I1R15Mass : Ball := ⟨0, 0⟩
def CA4_5_7I1R15MassTerm : Ball := .exact 0
def CA4_5_7I1R15H : Ball := ⟨0, 0⟩
def CA4_5_7I1R16Entropy : Ball := ⟨0, 0⟩
def CA4_5_7I1R16Mass : Ball := ⟨0, 0⟩
def CA4_5_7I1R16MassTerm : Ball := .exact 0
def CA4_5_7I1R16H : Ball := ⟨0, 0⟩
def CA4_5_7I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA4_5_7I1R0H
  | 1 => CA4_5_7I1R1H
  | 2 => CA4_5_7I1R2H
  | 3 => CA4_5_7I1R3H
  | 4 => CA4_5_7I1R4H
  | 5 => CA4_5_7I1R5H
  | 6 => CA4_5_7I1R6H
  | 7 => CA4_5_7I1R7H
  | 8 => CA4_5_7I1R8H
  | 9 => CA4_5_7I1R9H
  | 10 => CA4_5_7I1R10H
  | 11 => CA4_5_7I1R11H
  | 12 => CA4_5_7I1R12H
  | 13 => CA4_5_7I1R13H
  | 14 => CA4_5_7I1R14H
  | 15 => CA4_5_7I1R15H
  | 16 => CA4_5_7I1R16H
  | _ => (.exact 0)
def CA4_5_7I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 3, 5, 0 => Z3_5_0H1H
  | 4, 4, 0 => Z4_4_0H1H
  | _, _, _ => (.exact 0)
def CA4_5_7I1Singleton : Ball := ⟨(303183391302263079046188083 / 50000000000000000000000000000000), (251569 / 50000000000000000000000000000000)⟩
def CA4_5_7I1Group : Ball := ⟨(50009940225896612102999470955347 / 50000000000000000000000000000000), (83559113207 / 50000000000000000000000000000000)⟩

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
def CA4_5_7I1H : Ball := ⟨(3710174631598816941952092861339 / 3125000000000000000000000000000), (96993767119 / 20000000000000000000000000000000)⟩

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
def CA4_5_7I2PairEntropy : Ball := ⟨(2926908964202703077957468825237 / 1000000000000000000000000000000), (29293837857 / 25000000000000000000000000000000)⟩
def CA4_5_7I2PairMass : Ball := ⟨(5000000000000000000000000000001 / 5000000000000000000000000000000), (1 / 156250000000000000000000000000)⟩
def CA4_5_7I2PairMassTermLogWitness : LogWitness := ⟨0, 5000000000000000000000000000001, 5000000000000000000000000000000⟩
def CA4_5_7I2PairMassTermLog : Ball := ⟨(1 / 5000000000000000000000000000000), (10587912161 / 50000000000000000000000000000000)⟩
def CA4_5_7I2PairMassTerm : Ball := ⟨(-1 / 5000000000000000000000000000000), (21175824323 / 100000000000000000000000000000000)⟩
def CA4_5_7I2PairH : Ball := ⟨(7317272410506757694893672063093 / 2500000000000000000000000000000), (138351175751 / 100000000000000000000000000000000)⟩

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
def CA4_5_7I2R0Entropy : Ball := ⟨(373459546953319618009331341 / 6250000000000000000000000000000), (982967 / 50000000000000000000000000000000)⟩
def CA4_5_7I2R0Mass : Ball := ⟨(244308754727999724283630797 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def CA4_5_7I2R0MassTermLogWitness : LogWitness := ⟨-18, 244308754727999724283630797, 190734863281250000000000000⟩
def CA4_5_7I2R0MassTermLog : Ball := ⟨(-1222910074979865424709459157630799 / 100000000000000000000000000000000), (201170529647 / 50000000000000000000000000000000)⟩
def CA4_5_7I2R0MassTerm : Ball := ⟨(373459546953319618009331341 / 6250000000000000000000000000000), (982967 / 50000000000000000000000000000000)⟩
def CA4_5_7I2R0H : Ball := ⟨0, (982967 / 25000000000000000000000000000000)⟩
def CA4_5_7I2R1Entropy : Ball := ⟨(463082674732548310216718970043 / 50000000000000000000000000000000), (159605011 / 50000000000000000000000000000000)⟩
def CA4_5_7I2R1Mass : Ball := ⟨(2512377436904649203704730017 / 2000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def CA4_5_7I2R1MassTermLogWitness : LogWitness := ⟨-10, 2512377436904649203704730017, 1953125000000000000000000000⟩
def CA4_5_7I2R1MassTermLog : Ball := ⟨(-333983648433910948618079631291197 / 50000000000000000000000000000000), (232934065289 / 100000000000000000000000000000000)⟩
def CA4_5_7I2R1MassTerm : Ball := ⟨(419546491310226323073778343693 / 50000000000000000000000000000000), (146304593 / 50000000000000000000000000000000)⟩
def CA4_5_7I2R1H : Ball := ⟨(870723668446439742858812527 / 1000000000000000000000000000000), (76477401 / 12500000000000000000000000000000)⟩
def CA4_5_7I2R2Entropy : Ball := ⟨(10763902528042878560003338099253 / 50000000000000000000000000000000), (7985231791 / 100000000000000000000000000000000)⟩
def CA4_5_7I2R2Mass : Ball := ⟨(1102674149440720740080837894287 / 20000000000000000000000000000000), (39 / 100000000000000000000000000000000)⟩
def CA4_5_7I2R2MassTermLogWitness : LogWitness := ⟨-5, 1102674149440720740080837894287, 625000000000000000000000000000⟩
def CA4_5_7I2R2MassTermLog : Ball := ⟨(-144899699950644721659372497607277 / 50000000000000000000000000000000), (25410988561 / 20000000000000000000000000000000)⟩
def CA4_5_7I2R2MassTerm : Ball := ⟨(639108613589171253827319714027 / 4000000000000000000000000000000), (7005010163 / 100000000000000000000000000000000)⟩
def CA4_5_7I2R2H : Ball := ⟨(5550089716356475774323683347831 / 100000000000000000000000000000000), (7495120977 / 50000000000000000000000000000000)⟩
def CA4_5_7I2R3Entropy : Ball := ⟨(40277065983904835146155203584921 / 50000000000000000000000000000000), (4046970777 / 10000000000000000000000000000000)⟩
def CA4_5_7I2R3Mass : Ball := ⟨(22102336221707881009322431087423 / 50000000000000000000000000000000), (67 / 50000000000000000000000000000000)⟩
def CA4_5_7I2R3MassTermLogWitness : LogWitness := ⟨-2, 22102336221707881009322431087423, 12500000000000000000000000000000⟩
def CA4_5_7I2R3MassTermLog : Ball := ⟨(-81633969110199724265404696715543 / 100000000000000000000000000000000), (7940933919 / 12500000000000000000000000000000)⟩
def CA4_5_7I2R3MassTerm : Ball := ⟨(36086028647722992852483823757497 / 100000000000000000000000000000000), (28082110733 / 100000000000000000000000000000000)⟩
def CA4_5_7I2R3H : Ball := ⟨(8893620664017335487965316682469 / 20000000000000000000000000000000), (68551818503 / 100000000000000000000000000000000)⟩
def CA4_5_7I2R4Entropy : Ball := ⟨(72053839721292129411492716637041 / 100000000000000000000000000000000), (17288775127 / 50000000000000000000000000000000)⟩
def CA4_5_7I2R4Mass : Ball := ⟨(10664450289966456164136767792449 / 25000000000000000000000000000000), (19 / 12500000000000000000000000000000)⟩
def CA4_5_7I2R4MassTermLogWitness : LogWitness := ⟨-2, 10664450289966456164136767792449, 6250000000000000000000000000000⟩
def CA4_5_7I2R4MassTermLog : Ball := ⟨(-21299000441064703795460550474203 / 25000000000000000000000000000000), (12705494281 / 20000000000000000000000000000000)⟩
def CA4_5_7I2R4MassTerm : Ball := ⟨(18171370514376652650033390669629 / 50000000000000000000000000000000), (6774855641 / 25000000000000000000000000000000)⟩
def CA4_5_7I2R4H : Ball := ⟨(35711098692538824111425935297783 / 100000000000000000000000000000000), (30838486409 / 50000000000000000000000000000000)⟩
def CA4_5_7I2R5Entropy : Ball := ⟨(9015065231855951410268254976127 / 50000000000000000000000000000000), (696172159 / 10000000000000000000000000000000)⟩
def CA4_5_7I2R5Mass : Ball := ⟨(1142470438971876058233718386119 / 25000000000000000000000000000000), (7 / 25000000000000000000000000000000)⟩
def CA4_5_7I2R5MassTermLogWitness : LogWitness := ⟨-5, 1142470438971876058233718386119, 781250000000000000000000000000⟩
def CA4_5_7I2R5MassTermLog : Ball := ⟨(-308568285540194419975053007221709 / 100000000000000000000000000000000), (12705494271 / 10000000000000000000000000000000)⟩
def CA4_5_7I2R5MassTerm : Ball := ⟨(14101205785356204585631815735069 / 100000000000000000000000000000000), (2903130367 / 50000000000000000000000000000000)⟩
def CA4_5_7I2R5H : Ball := ⟨(785784935671139646980938843437 / 20000000000000000000000000000000), (3191995581 / 25000000000000000000000000000000)⟩
def CA4_5_7I2R6Entropy : Ball := ⟨(48381166404908176803070457653 / 10000000000000000000000000000000), (83471091 / 50000000000000000000000000000000)⟩
def CA4_5_7I2R6Mass : Ball := ⟨(16246788883517155613847561503 / 25000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def CA4_5_7I2R6MassTermLogWitness : LogWitness := ⟨-11, 16246788883517155613847561503, 12207031250000000000000000000⟩
def CA4_5_7I2R6MassTermLog : Ball := ⟨(-733873582176963528087673936985231 / 100000000000000000000000000000000), (63527473357 / 25000000000000000000000000000000)⟩
def CA4_5_7I2R6MassTerm : Ball := ⟨(119230891568196048297085156129 / 25000000000000000000000000000000), (165138837 / 100000000000000000000000000000000)⟩
def CA4_5_7I2R6H : Ball := ⟨(3444048888148787421181976007 / 50000000000000000000000000000000), (332081019 / 100000000000000000000000000000000)⟩
def CA4_5_7I2R7Entropy : Ball := ⟨0, 0⟩
def CA4_5_7I2R7Mass : Ball := ⟨0, 0⟩
def CA4_5_7I2R7MassTerm : Ball := .exact 0
def CA4_5_7I2R7H : Ball := ⟨0, 0⟩
def CA4_5_7I2R8Entropy : Ball := ⟨0, 0⟩
def CA4_5_7I2R8Mass : Ball := ⟨0, 0⟩
def CA4_5_7I2R8MassTerm : Ball := .exact 0
def CA4_5_7I2R8H : Ball := ⟨0, 0⟩
def CA4_5_7I2R9Entropy : Ball := ⟨0, 0⟩
def CA4_5_7I2R9Mass : Ball := ⟨0, 0⟩
def CA4_5_7I2R9MassTerm : Ball := .exact 0
def CA4_5_7I2R9H : Ball := ⟨0, 0⟩
def CA4_5_7I2R10Entropy : Ball := ⟨0, 0⟩
def CA4_5_7I2R10Mass : Ball := ⟨0, 0⟩
def CA4_5_7I2R10MassTerm : Ball := .exact 0
def CA4_5_7I2R10H : Ball := ⟨0, 0⟩
def CA4_5_7I2R11Entropy : Ball := ⟨0, 0⟩
def CA4_5_7I2R11Mass : Ball := ⟨0, 0⟩
def CA4_5_7I2R11MassTerm : Ball := .exact 0
def CA4_5_7I2R11H : Ball := ⟨0, 0⟩
def CA4_5_7I2R12Entropy : Ball := ⟨0, 0⟩
def CA4_5_7I2R12Mass : Ball := ⟨0, 0⟩
def CA4_5_7I2R12MassTerm : Ball := .exact 0
def CA4_5_7I2R12H : Ball := ⟨0, 0⟩
def CA4_5_7I2R13Entropy : Ball := ⟨0, 0⟩
def CA4_5_7I2R13Mass : Ball := ⟨0, 0⟩
def CA4_5_7I2R13MassTerm : Ball := .exact 0
def CA4_5_7I2R13H : Ball := ⟨0, 0⟩
def CA4_5_7I2R14Entropy : Ball := ⟨0, 0⟩
def CA4_5_7I2R14Mass : Ball := ⟨0, 0⟩
def CA4_5_7I2R14MassTerm : Ball := .exact 0
def CA4_5_7I2R14H : Ball := ⟨0, 0⟩
def CA4_5_7I2R15Entropy : Ball := ⟨0, 0⟩
def CA4_5_7I2R15Mass : Ball := ⟨0, 0⟩
def CA4_5_7I2R15MassTerm : Ball := .exact 0
def CA4_5_7I2R15H : Ball := ⟨0, 0⟩
def CA4_5_7I2R16Entropy : Ball := ⟨0, 0⟩
def CA4_5_7I2R16Mass : Ball := ⟨0, 0⟩
def CA4_5_7I2R16MassTerm : Ball := .exact 0
def CA4_5_7I2R16H : Ball := ⟨0, 0⟩
def CA4_5_7I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA4_5_7I2R0H
  | 1 => CA4_5_7I2R1H
  | 2 => CA4_5_7I2R2H
  | 3 => CA4_5_7I2R3H
  | 4 => CA4_5_7I2R4H
  | 5 => CA4_5_7I2R5H
  | 6 => CA4_5_7I2R6H
  | 7 => CA4_5_7I2R7H
  | 8 => CA4_5_7I2R8H
  | 9 => CA4_5_7I2R9H
  | 10 => CA4_5_7I2R10H
  | 11 => CA4_5_7I2R11H
  | 12 => CA4_5_7I2R12H
  | 13 => CA4_5_7I2R13H
  | 14 => CA4_5_7I2R14H
  | 15 => CA4_5_7I2R15H
  | 16 => CA4_5_7I2R16H
  | _ => (.exact 0)
def CA4_5_7I2Singleton : Ball := ⟨(1736985044719429942832526678359 / 50000000000000000000000000000000), (714924641 / 25000000000000000000000000000000)⟩
def CA4_5_7I2Group : Ball := ⟨(2913317092543671156102318588643 / 3125000000000000000000000000000), (80897273129 / 50000000000000000000000000000000)⟩

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
def CA4_5_7I2H : Ball := ⟨(13279825312184419225649811606321 / 12500000000000000000000000000000), (461940268267 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA4_6_6I0
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
def CA4_6_6I0Value (a : Fin 17) : ℝ := marginal (below (shape 4 6 6)) (fun u => (stageALaw (shape 4 6 6) u : ℝ)) ((Equiv.refl (Fin 3)) 0) a
def CA4_6_6I0Entropy : Ball := ⟨(121498391389477694074765237267123 / 100000000000000000000000000000000), (77644200987 / 100000000000000000000000000000000)⟩
def CA4_6_6I0Mass : Ball := ⟨(50000000000000000000000000000001 / 50000000000000000000000000000000), (13 / 3125000000000000000000000000000)⟩
def CA4_6_6I0MassTermLogWitness : LogWitness := ⟨0, 50000000000000000000000000000001, 50000000000000000000000000000000⟩
def CA4_6_6I0MassTermLog : Ball := ⟨(1 / 50000000000000000000000000000000), (10587912049 / 50000000000000000000000000000000)⟩
def CA4_6_6I0MassTerm : Ball := ⟨(-1 / 50000000000000000000000000000000), (21175824099 / 100000000000000000000000000000000)⟩
def CA4_6_6I0H : Ball := ⟨(971987131115821552598121898137 / 800000000000000000000000000000), (49410012543 / 50000000000000000000000000000000)⟩

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
def CA4_6_6I1PairEntropy : Ball := ⟨(156995264750201302767556569042031 / 50000000000000000000000000000000), (33376481437 / 25000000000000000000000000000000)⟩
def CA4_6_6I1PairMass : Ball := ⟨(9999999999999999999999999999999 / 10000000000000000000000000000000), (3 / 390625000000000000000000000000)⟩
def CA4_6_6I1PairMassTermLogWitness : LogWitness := ⟨-1, 9999999999999999999999999999999, 5000000000000000000000000000000⟩
def CA4_6_6I1PairMassTermLog : Ball := ⟨(-9 / 100000000000000000000000000000000), (21175824067 / 50000000000000000000000000000000)⟩
def CA4_6_6I1PairMassTerm : Ball := ⟨(9 / 100000000000000000000000000000000), (8470329627 / 20000000000000000000000000000000)⟩
def CA4_6_6I1PairH : Ball := ⟨(313990529500402605535113138084053 / 100000000000000000000000000000000), (175857573883 / 100000000000000000000000000000000)⟩

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
def CA4_6_6I1R0Entropy : Ball := ⟨(69047100494242373905364798197 / 50000000000000000000000000000000), (4676377 / 10000000000000000000000000000000)⟩
def CA4_6_6I1R0Mass : Ball := ⟨(15773965556059223716466861929 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def CA4_6_6I1R0MassTermLogWitness : LogWitness := ⟨-13, 15773965556059223716466861929, 12207031250000000000000000000⟩
def CA4_6_6I1R0MassTermLog : Ball := ⟨(-437728231679315675174532705087319 / 50000000000000000000000000000000), (14823077529 / 5000000000000000000000000000000)⟩
def CA4_6_6I1R0MassTerm : Ball := ⟨(69047100494242373905364798197 / 50000000000000000000000000000000), (4676377 / 10000000000000000000000000000000)⟩
def CA4_6_6I1R0H : Ball := ⟨0, (4676377 / 5000000000000000000000000000000)⟩
def CA4_6_6I1R1Entropy : Ball := ⟨(848589911628194458485256767603 / 12500000000000000000000000000000), (648121927 / 25000000000000000000000000000000)⟩
def CA4_6_6I1R1Mass : Ball := ⟨(85018587892439093136197242101 / 6250000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def CA4_6_6I1R1MassTermLogWitness : LogWitness := ⟨-7, 85018587892439093136197242101, 48828125000000000000000000000⟩
def CA4_6_6I1R1MassTermLog : Ball := ⟨(-85949336581196713914057177179397 / 20000000000000000000000000000000), (169406590493 / 100000000000000000000000000000000)⟩
def CA4_6_6I1R1MassTerm : Ball := ⟨(116916659622804854083157751421 / 2000000000000000000000000000000), (2304433517 / 100000000000000000000000000000000)⟩
def CA4_6_6I1R1H : Ball := ⟨(471443155942656481862083284887 / 50000000000000000000000000000000), (195876849 / 4000000000000000000000000000000)⟩
def CA4_6_6I1R2Entropy : Ball := ⟨(56841281440862299997228627084157 / 100000000000000000000000000000000), (4695386197 / 20000000000000000000000000000000)⟩
def CA4_6_6I1R2Mass : Ball := ⟨(143097168407686324514841093003 / 625000000000000000000000000000), (39 / 25000000000000000000000000000000)⟩
def CA4_6_6I1R2MassTermLogWitness : LogWitness := ⟨-3, 143097168407686324514841093003, 78125000000000000000000000000⟩
def CA4_6_6I1R2MassTermLog : Ball := ⟨(-73711387543860233702273399980243 / 50000000000000000000000000000000), (84703295413 / 100000000000000000000000000000000)⟩
def CA4_6_6I1R2MassTerm : Ball := ⟨(33753250678169599658428471925163 / 100000000000000000000000000000000), (4848320749 / 25000000000000000000000000000000)⟩
def CA4_6_6I1R2H : Ball := ⟨(11544015381346350169400077579497 / 50000000000000000000000000000000), (42870213981 / 100000000000000000000000000000000)⟩
def CA4_6_6I1R3Entropy : Ball := ⟨(44167472494111664479493619967087 / 50000000000000000000000000000000), (23565865991 / 50000000000000000000000000000000)⟩
def CA4_6_6I1R3Mass : Ball := ⟨(3216047710366887920466225297997 / 6250000000000000000000000000000), (107 / 50000000000000000000000000000000)⟩
def CA4_6_6I1R3MassTermLogWitness : LogWitness := ⟨-1, 3216047710366887920466225297997, 3125000000000000000000000000000⟩
def CA4_6_6I1R3MassTermLog : Ball := ⟨(-16610706930713633064934840352097 / 25000000000000000000000000000000), (42351647781 / 100000000000000000000000000000000)⟩
def CA4_6_6I1R3MassTerm : Ball := ⟨(34189328634942064644830345826001 / 100000000000000000000000000000000), (21792787323 / 100000000000000000000000000000000)⟩
def CA4_6_6I1R3H : Ball := ⟨(54145616353281264314156894108173 / 100000000000000000000000000000000), (13784903861 / 20000000000000000000000000000000)⟩
def CA4_6_6I1R4Entropy : Ball := ⟨(6792120916943168034646391707517 / 12500000000000000000000000000000), (23448249421 / 100000000000000000000000000000000)⟩
def CA4_6_6I1R4Mass : Ball := ⟨(1430298472873864012349266424117 / 6250000000000000000000000000000), (149 / 100000000000000000000000000000000)⟩
def CA4_6_6I1R4MassTermLogWitness : LogWitness := ⟨-3, 1430298472873864012349266424117, 781250000000000000000000000000⟩
def CA4_6_6I1R4MassTermLog : Ball := ⟨(-29493966379330907074674043622459 / 20000000000000000000000000000000), (84703295383 / 100000000000000000000000000000000)⟩
def CA4_6_6I1R4MassTerm : Ball := ⟨(33748140057080067657293397594779 / 100000000000000000000000000000000), (9692079633 / 50000000000000000000000000000000)⟩
def CA4_6_6I1R4H : Ball := ⟨(20588827278465276619877736065357 / 100000000000000000000000000000000), (42832408687 / 100000000000000000000000000000000)⟩
def CA4_6_6I1R5Entropy : Ball := ⟨(1798273317126225663650556231 / 25000000000000000000000000000), (334484669 / 12500000000000000000000000000000)⟩
def CA4_6_6I1R5Mass : Ball := ⟨(5421238472678391887231668409 / 400000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
def CA4_6_6I1R5MassTermLogWitness : LogWitness := ⟨-7, 5421238472678391887231668409, 3125000000000000000000000000⟩
def CA4_6_6I1R5MassTermLog : Ball := ⟨(-430114025726452064064942892187163 / 100000000000000000000000000000000), (21175823849 / 12500000000000000000000000000000)⟩
def CA4_6_6I1R5MassTerm : Ball := ⟨(2914688379883531929262569133991 / 50000000000000000000000000000000), (2295983897 / 100000000000000000000000000000000)⟩
def CA4_6_6I1R5H : Ball := ⟨(681858254368919398038543328009 / 50000000000000000000000000000000), (4971861249 / 100000000000000000000000000000000)⟩
def CA4_6_6I1R6Entropy : Ball := ⟨(149134423420517275608068340133 / 100000000000000000000000000000000), (2559891 / 5000000000000000000000000000000)⟩
def CA4_6_6I1R6Mass : Ball := ⟨(15412579127215443834383332517 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def CA4_6_6I1R6MassTermLogWitness : LogWitness := ⟨-13, 15412579127215443834383332517, 12207031250000000000000000000⟩
def CA4_6_6I1R6MassTermLog : Ball := ⟨(-438887073126462491403995506839213 / 50000000000000000000000000000000), (29646157049 / 10000000000000000000000000000000)⟩
def CA4_6_6I1R6MassTerm : Ball := ⟨(135287634849471878805145624111 / 100000000000000000000000000000000), (11423107 / 25000000000000000000000000000000)⟩
def CA4_6_6I1R6H : Ball := ⟨(6923394285522698401461358011 / 50000000000000000000000000000000), (12111281 / 12500000000000000000000000000000)⟩
def CA4_6_6I1R7Entropy : Ball := ⟨0, 0⟩
def CA4_6_6I1R7Mass : Ball := ⟨0, 0⟩
def CA4_6_6I1R7MassTerm : Ball := .exact 0
def CA4_6_6I1R7H : Ball := ⟨0, 0⟩
def CA4_6_6I1R8Entropy : Ball := ⟨0, 0⟩
def CA4_6_6I1R8Mass : Ball := ⟨0, 0⟩
def CA4_6_6I1R8MassTerm : Ball := .exact 0
def CA4_6_6I1R8H : Ball := ⟨0, 0⟩
def CA4_6_6I1R9Entropy : Ball := ⟨0, 0⟩
def CA4_6_6I1R9Mass : Ball := ⟨0, 0⟩
def CA4_6_6I1R9MassTerm : Ball := .exact 0
def CA4_6_6I1R9H : Ball := ⟨0, 0⟩
def CA4_6_6I1R10Entropy : Ball := ⟨0, 0⟩
def CA4_6_6I1R10Mass : Ball := ⟨0, 0⟩
def CA4_6_6I1R10MassTerm : Ball := .exact 0
def CA4_6_6I1R10H : Ball := ⟨0, 0⟩
def CA4_6_6I1R11Entropy : Ball := ⟨0, 0⟩
def CA4_6_6I1R11Mass : Ball := ⟨0, 0⟩
def CA4_6_6I1R11MassTerm : Ball := .exact 0
def CA4_6_6I1R11H : Ball := ⟨0, 0⟩
def CA4_6_6I1R12Entropy : Ball := ⟨0, 0⟩
def CA4_6_6I1R12Mass : Ball := ⟨0, 0⟩
def CA4_6_6I1R12MassTerm : Ball := .exact 0
def CA4_6_6I1R12H : Ball := ⟨0, 0⟩
def CA4_6_6I1R13Entropy : Ball := ⟨0, 0⟩
def CA4_6_6I1R13Mass : Ball := ⟨0, 0⟩
def CA4_6_6I1R13MassTerm : Ball := .exact 0
def CA4_6_6I1R13H : Ball := ⟨0, 0⟩
def CA4_6_6I1R14Entropy : Ball := ⟨0, 0⟩
def CA4_6_6I1R14Mass : Ball := ⟨0, 0⟩
def CA4_6_6I1R14MassTerm : Ball := .exact 0
def CA4_6_6I1R14H : Ball := ⟨0, 0⟩
def CA4_6_6I1R15Entropy : Ball := ⟨0, 0⟩
def CA4_6_6I1R15Mass : Ball := ⟨0, 0⟩
def CA4_6_6I1R15MassTerm : Ball := .exact 0
def CA4_6_6I1R15H : Ball := ⟨0, 0⟩
def CA4_6_6I1R16Entropy : Ball := ⟨0, 0⟩
def CA4_6_6I1R16Mass : Ball := ⟨0, 0⟩
def CA4_6_6I1R16MassTerm : Ball := .exact 0
def CA4_6_6I1R16H : Ball := ⟨0, 0⟩
def CA4_6_6I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA4_6_6I1R0H
  | 1 => CA4_6_6I1R1H
  | 2 => CA4_6_6I1R2H
  | 3 => CA4_6_6I1R3H
  | 4 => CA4_6_6I1R4H
  | 5 => CA4_6_6I1R5H
  | 6 => CA4_6_6I1R6H
  | 7 => CA4_6_6I1R7H
  | 8 => CA4_6_6I1R8H
  | 9 => CA4_6_6I1R9H
  | 10 => CA4_6_6I1R10H
  | 11 => CA4_6_6I1R11H
  | 12 => CA4_6_6I1R12H
  | 13 => CA4_6_6I1R13H
  | 14 => CA4_6_6I1R14H
  | 15 => CA4_6_6I1R15H
  | 16 => CA4_6_6I1R16H
  | _ => (.exact 0)
def CA4_6_6I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 2, 6, 0 => Z2_6_0H1H
  | 3, 5, 0 => Z3_5_0H1H
  | 4, 4, 0 => Z4_4_0H1H
  | _, _, _ => (.exact 0)
def CA4_6_6I1Singleton : Ball := ⟨(1242243551352522190804190177 / 6250000000000000000000000000000), (16424641 / 100000000000000000000000000000000)⟩
def CA4_6_6I1Group : Ball := ⟨(10016279990045507878449182831717 / 10000000000000000000000000000000), (41175691719 / 25000000000000000000000000000000)⟩

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
def CA4_6_6I1H : Ball := ⟨(113664929699492447966129481449713 / 100000000000000000000000000000000), (101052621527 / 20000000000000000000000000000000)⟩

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
def CA4_6_6I2PairEntropy : Ball := ⟨(154442923167174487264206344281983 / 50000000000000000000000000000000), (66037078417 / 50000000000000000000000000000000)⟩
def CA4_6_6I2PairMass : Ball := ⟨(50000000000000000000000000000007 / 50000000000000000000000000000000), (383 / 50000000000000000000000000000000)⟩
def CA4_6_6I2PairMassTermLogWitness : LogWitness := ⟨0, 50000000000000000000000000000007, 50000000000000000000000000000000⟩
def CA4_6_6I2PairMassTermLog : Ball := ⟨(7 / 50000000000000000000000000000000), (330872257 / 1562500000000000000000000000000)⟩
def CA4_6_6I2PairMassTerm : Ball := ⟨(-7 / 50000000000000000000000000000000), (21175824449 / 100000000000000000000000000000000)⟩
def CA4_6_6I2PairH : Ball := ⟨(15444292316717448726420634428199 / 5000000000000000000000000000000), (153249981283 / 100000000000000000000000000000000)⟩

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
def CA4_6_6I2R0Entropy : Ball := ⟨(35194515439582966269226210913 / 25000000000000000000000000000000), (47791271 / 100000000000000000000000000000000)⟩
def CA4_6_6I2R0Mass : Ball := ⟨(16120553786259023039634395387 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def CA4_6_6I2R0MassTermLogWitness : LogWitness := ⟨-13, 16120553786259023039634395387, 12207031250000000000000000000⟩
def CA4_6_6I2R0MassTermLog : Ball := ⟨(-106601933282416248877794389871 / 12207031250000000000000000000), (296461550171 / 100000000000000000000000000000000)⟩
def CA4_6_6I2R0MassTerm : Ball := ⟨(35194515439582966269226210913 / 25000000000000000000000000000000), (47791271 / 100000000000000000000000000000000)⟩
def CA4_6_6I2R0H : Ball := ⟨0, (47791271 / 50000000000000000000000000000000)⟩
def CA4_6_6I2R1Entropy : Ball := ⟨(1707607198642413904839239804119 / 25000000000000000000000000000000), (1306213179 / 50000000000000000000000000000000)⟩
def CA4_6_6I2R1Mass : Ball := ⟨(342689840677687947278184466827 / 25000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def CA4_6_6I2R1MassTermLogWitness : LogWitness := ⟨-7, 342689840677687947278184466827, 195312500000000000000000000000⟩
def CA4_6_6I2R1MassTermLog : Ball := ⟨(-214490266017660209100125380398921 / 50000000000000000000000000000000), (33881318097 / 20000000000000000000000000000000)⟩
def CA4_6_6I2R1MassTerm : Ball := ⟨(183759087721267205798870959323 / 3125000000000000000000000000000), (2322156761 / 100000000000000000000000000000000)⟩
def CA4_6_6I2R1H : Ball := ⟨(47506899374455251689654425907 / 5000000000000000000000000000000), (4934583119 / 100000000000000000000000000000000)⟩
def CA4_6_6I2R2Entropy : Ball := ⟨(56840555858831280511348543567501 / 100000000000000000000000000000000), (23468845131 / 100000000000000000000000000000000)⟩
def CA4_6_6I2R2Mass : Ball := ⟨(4576201140301024826530043161077 / 20000000000000000000000000000000), (39 / 25000000000000000000000000000000)⟩
def CA4_6_6I2R2MassTermLogWitness : LogWitness := ⟨-3, 4576201140301024826530043161077, 2500000000000000000000000000000⟩
def CA4_6_6I2R2MassTermLog : Ball := ⟨(-147486306495714444044522497902991 / 100000000000000000000000000000000), (42351647707 / 50000000000000000000000000000000)⟩
def CA4_6_6I2R2MassTerm : Ball := ⟨(33746350198223744188971964201703 / 100000000000000000000000000000000), (4845241521 / 25000000000000000000000000000000)⟩
def CA4_6_6I2R2H : Ball := ⟨(11547102830303768161188289682899 / 50000000000000000000000000000000), (8569962243 / 20000000000000000000000000000000)⟩
def CA4_6_6I2R3Entropy : Ball := ⟨(43043982495920787653178568618309 / 50000000000000000000000000000000), (11714076041 / 25000000000000000000000000000000)⟩
def CA4_6_6I2R3Mass : Ball := ⟨(12762938573402547726709552123847 / 25000000000000000000000000000000), (21 / 10000000000000000000000000000000)⟩
def CA4_6_6I2R3MassTermLogWitness : LogWitness := ⟨-1, 12762938573402547726709552123847, 12500000000000000000000000000000⟩
def CA4_6_6I2R3MassTermLog : Ball := ⟨(-2689321110977372408220498540859 / 4000000000000000000000000000000), (42351647777 / 100000000000000000000000000000000)⟩
def CA4_6_6I2R3MassTerm : Ball := ⟨(8580910035889725034669812880701 / 25000000000000000000000000000000), (4324251861 / 20000000000000000000000000000000)⟩
def CA4_6_6I2R3H : Ball := ⟨(25882162424141337583838942856907 / 50000000000000000000000000000000), (68477563469 / 100000000000000000000000000000000)⟩
def CA4_6_6I2R4Entropy : Ball := ⟨(50548892671349424436784968979809 / 100000000000000000000000000000000), (4324531559 / 20000000000000000000000000000000)⟩
def CA4_6_6I2R4Mass : Ball := ⟨(2115011303459201040478593529703 / 10000000000000000000000000000000), (67 / 50000000000000000000000000000000)⟩
def CA4_6_6I2R4MassTermLogWitness : LogWitness := ⟨-3, 2115011303459201040478593529703, 1250000000000000000000000000000⟩
def CA4_6_6I2R4MassTermLog : Ball := ⟨(-3107049872169863249670890214253 / 2000000000000000000000000000000), (16940659073 / 20000000000000000000000000000000)⟩
def CA4_6_6I2R4MassTerm : Ball := ⟨(8214307000063408053921907574261 / 25000000000000000000000000000000), (17914842923 / 100000000000000000000000000000000)⟩
def CA4_6_6I2R4H : Ball := ⟨(3538332934219158444219467736553 / 20000000000000000000000000000000), (19768750359 / 50000000000000000000000000000000)⟩
def CA4_6_6I2R5Entropy : Ball := ⟨(1333292581102270880457583042099 / 25000000000000000000000000000000), (945052173 / 50000000000000000000000000000000)⟩
def CA4_6_6I2R5Mass : Ball := ⟨(97084953765188630096407201251 / 10000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def CA4_6_6I2R5MassTermLogWitness : LogWitness := ⟨-7, 97084953765188630096407201251, 78125000000000000000000000000⟩
def CA4_6_6I2R5MassTermLog : Ball := ⟨(-231737698238005191053161152691633 / 50000000000000000000000000000000), (84703295453 / 50000000000000000000000000000000)⟩
def CA4_6_6I2R5MassTerm : Ball := ⟨(899929748763518745743438399873 / 20000000000000000000000000000000), (164468317 / 10000000000000000000000000000000)⟩
def CA4_6_6I2R5H : Ball := ⟨(833521580591489793113140169031 / 100000000000000000000000000000000), (883696879 / 25000000000000000000000000000000)⟩
def CA4_6_6I2R6Entropy : Ball := ⟨(12484339615419062730215074583 / 25000000000000000000000000000000), (3407559 / 20000000000000000000000000000000)⟩
def CA4_6_6I2R6Mass : Ball := ⟨(623473513678439796404846421 / 12500000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def CA4_6_6I2R6MassTermLogWitness : LogWitness := ⟨-15, 623473513678439796404846421, 381469726562500000000000000⟩
def CA4_6_6I2R6MassTermLog : Ball := ⟨(-990593291812139828845765896723109 / 100000000000000000000000000000000), (338813299221 / 100000000000000000000000000000000)⟩
def CA4_6_6I2R6MassTerm : Ball := ⟨(49408694421792549308377853077 / 100000000000000000000000000000000), (337987 / 2000000000000000000000000000000)⟩
def CA4_6_6I2R6H : Ball := ⟨(105732807976740322496489051 / 20000000000000000000000000000000), (6787429 / 20000000000000000000000000000000)⟩
def CA4_6_6I2R7Entropy : Ball := ⟨0, 0⟩
def CA4_6_6I2R7Mass : Ball := ⟨0, 0⟩
def CA4_6_6I2R7MassTerm : Ball := .exact 0
def CA4_6_6I2R7H : Ball := ⟨0, 0⟩
def CA4_6_6I2R8Entropy : Ball := ⟨0, 0⟩
def CA4_6_6I2R8Mass : Ball := ⟨0, 0⟩
def CA4_6_6I2R8MassTerm : Ball := .exact 0
def CA4_6_6I2R8H : Ball := ⟨0, 0⟩
def CA4_6_6I2R9Entropy : Ball := ⟨0, 0⟩
def CA4_6_6I2R9Mass : Ball := ⟨0, 0⟩
def CA4_6_6I2R9MassTerm : Ball := .exact 0
def CA4_6_6I2R9H : Ball := ⟨0, 0⟩
def CA4_6_6I2R10Entropy : Ball := ⟨0, 0⟩
def CA4_6_6I2R10Mass : Ball := ⟨0, 0⟩
def CA4_6_6I2R10MassTerm : Ball := .exact 0
def CA4_6_6I2R10H : Ball := ⟨0, 0⟩
def CA4_6_6I2R11Entropy : Ball := ⟨0, 0⟩
def CA4_6_6I2R11Mass : Ball := ⟨0, 0⟩
def CA4_6_6I2R11MassTerm : Ball := .exact 0
def CA4_6_6I2R11H : Ball := ⟨0, 0⟩
def CA4_6_6I2R12Entropy : Ball := ⟨0, 0⟩
def CA4_6_6I2R12Mass : Ball := ⟨0, 0⟩
def CA4_6_6I2R12MassTerm : Ball := .exact 0
def CA4_6_6I2R12H : Ball := ⟨0, 0⟩
def CA4_6_6I2R13Entropy : Ball := ⟨0, 0⟩
def CA4_6_6I2R13Mass : Ball := ⟨0, 0⟩
def CA4_6_6I2R13MassTerm : Ball := .exact 0
def CA4_6_6I2R13H : Ball := ⟨0, 0⟩
def CA4_6_6I2R14Entropy : Ball := ⟨0, 0⟩
def CA4_6_6I2R14Mass : Ball := ⟨0, 0⟩
def CA4_6_6I2R14MassTerm : Ball := .exact 0
def CA4_6_6I2R14H : Ball := ⟨0, 0⟩
def CA4_6_6I2R15Entropy : Ball := ⟨0, 0⟩
def CA4_6_6I2R15Mass : Ball := ⟨0, 0⟩
def CA4_6_6I2R15MassTerm : Ball := .exact 0
def CA4_6_6I2R15H : Ball := ⟨0, 0⟩
def CA4_6_6I2R16Entropy : Ball := ⟨0, 0⟩
def CA4_6_6I2R16Mass : Ball := ⟨0, 0⟩
def CA4_6_6I2R16MassTerm : Ball := .exact 0
def CA4_6_6I2R16H : Ball := ⟨0, 0⟩
def CA4_6_6I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA4_6_6I2R0H
  | 1 => CA4_6_6I2R1H
  | 2 => CA4_6_6I2R2H
  | 3 => CA4_6_6I2R3H
  | 4 => CA4_6_6I2R4H
  | 5 => CA4_6_6I2R5H
  | 6 => CA4_6_6I2R6H
  | 7 => CA4_6_6I2R7H
  | 8 => CA4_6_6I2R8H
  | 9 => CA4_6_6I2R9H
  | 10 => CA4_6_6I2R10H
  | 11 => CA4_6_6I2R11H
  | 12 => CA4_6_6I2R12H
  | 13 => CA4_6_6I2R13H
  | 14 => CA4_6_6I2R14H
  | 15 => CA4_6_6I2R15H
  | 16 => CA4_6_6I2R16H
  | _ => (.exact 0)
def CA4_6_6I2Singleton : Ball := ⟨(385647486515267613255081256021 / 12500000000000000000000000000000), (648017637 / 25000000000000000000000000000000)⟩
def CA4_6_6I2Group : Ball := ⟨(97419563304228623145711164942971 / 100000000000000000000000000000000), (10128489767 / 6250000000000000000000000000000)⟩

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
def CA4_6_6I2H : Ball := ⟨(57023359862945864118495179339019 / 50000000000000000000000000000000), (477361653827 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA5_5_6I0
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
def CA5_5_6I0Value (a : Fin 17) : ℝ := marginal (below (shape 5 5 6)) (fun u => (stageALaw (shape 5 5 6) u : ℝ)) ((Equiv.refl (Fin 3)) 0) a
def CA5_5_6I0Entropy : Ball := ⟨(47535472245704849515622895199 / 40000000000000000000000000000), (8963936847 / 12500000000000000000000000000000)⟩
def CA5_5_6I0Mass : Ball := ⟨(49999999999999999999999999999999 / 50000000000000000000000000000000), (127 / 50000000000000000000000000000000)⟩
def CA5_5_6I0MassTermLogWitness : LogWitness := ⟨-1, 49999999999999999999999999999999, 25000000000000000000000000000000⟩
def CA5_5_6I0MassTermLog : Ball := ⟨(-1 / 100000000000000000000000000000000), (2117582381 / 5000000000000000000000000000000)⟩
def CA5_5_6I0MassTerm : Ball := ⟨(1 / 100000000000000000000000000000000), (42351647621 / 100000000000000000000000000000000)⟩
def CA5_5_6I0H : Ball := ⟨(118838680614262123789057237997499 / 100000000000000000000000000000000), (114063142397 / 100000000000000000000000000000000)⟩

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
def CA5_5_6I1PairEntropy : Ball := ⟨(78619182179922625235000698456083 / 25000000000000000000000000000000), (32217977861 / 25000000000000000000000000000000)⟩
def CA5_5_6I1PairMass : Ball := ⟨1, (73 / 12500000000000000000000000000000)⟩
def CA5_5_6I1PairMassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CA5_5_6I1PairMassTermLog : Ball := ⟨0, (10587912133 / 50000000000000000000000000000000)⟩
def CA5_5_6I1PairMassTerm : Ball := ⟨0, (21175824267 / 100000000000000000000000000000000)⟩
def CA5_5_6I1PairH : Ball := ⟨(78619182179922625235000698456083 / 25000000000000000000000000000000), (150047735711 / 100000000000000000000000000000000)⟩

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
def CA5_5_6I1R0Entropy : Ball := ⟨(402680401197399720458807296919 / 25000000000000000000000000000000), (144425551 / 25000000000000000000000000000000)⟩
def CA5_5_6I1R0Mass : Ball := ⟨(272812136002498323516874715041 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
def CA5_5_6I1R0MassTermLogWitness : LogWitness := ⟨-9, 272812136002498323516874715041, 195312500000000000000000000000⟩
def CA5_5_6I1R0MassTermLog : Ball := ⟨(-18450443916180478597926154971713 / 3125000000000000000000000000000), (105879119331 / 50000000000000000000000000000000)⟩
def CA5_5_6I1R0MassTerm : Ball := ⟨(402680401197399720458807296919 / 25000000000000000000000000000000), (144425551 / 25000000000000000000000000000000)⟩
def CA5_5_6I1R0H : Ball := ⟨0, (144425551 / 12500000000000000000000000000000)⟩
def CA5_5_6I1R1Entropy : Ball := ⟨(1365840203404610014013524827681 / 5000000000000000000000000000000), (692437397 / 6250000000000000000000000000000)⟩
def CA5_5_6I1R1Mass : Ball := ⟨(4359924130796579287577240988223 / 50000000000000000000000000000000), (23 / 50000000000000000000000000000000)⟩
def CA5_5_6I1R1MassTermLogWitness : LogWitness := ⟨-4, 4359924130796579287577240988223, 3125000000000000000000000000000⟩
def CA5_5_6I1R1MassTermLog : Ball := ⟨(-243956834941205074802058332777901 / 100000000000000000000000000000000), (52939559471 / 50000000000000000000000000000000)⟩
def CA5_5_6I1R1MassTerm : Ball := ⟨(4254533166131672394740051234551 / 20000000000000000000000000000000), (73859989 / 800000000000000000000000000000)⟩
def CA5_5_6I1R1H : Ball := ⟨(1208827647486767661314048076173 / 20000000000000000000000000000000), (20311496977 / 100000000000000000000000000000000)⟩
def CA5_5_6I1R2Entropy : Ball := ⟨(77773938708604008470389406430849 / 100000000000000000000000000000000), (833045701 / 2500000000000000000000000000000)⟩
def CA5_5_6I1R2Mass : Ball := ⟨(1281479362575135721916520103391 / 3125000000000000000000000000000), (39 / 25000000000000000000000000000000)⟩
def CA5_5_6I1R2MassTermLogWitness : LogWitness := ⟨-2, 1281479362575135721916520103391, 781250000000000000000000000000⟩
def CA5_5_6I1R2MassTermLog : Ball := ⟨(-17828382412244256628210000201737 / 20000000000000000000000000000000), (63527471429 / 100000000000000000000000000000000)⟩
def CA5_5_6I1R2MassTerm : Ball := ⟨(36554726607021648898164340666049 / 100000000000000000000000000000000), (2605092609 / 10000000000000000000000000000000)⟩
def CA5_5_6I1R2H : Ball := ⟨(25762007563488974732640666103 / 62500000000000000000000000000), (5937275413 / 10000000000000000000000000000000)⟩
def CA5_5_6I1R3Entropy : Ball := ⟨(495014840752811077285599252337 / 625000000000000000000000000000), (9489307673 / 25000000000000000000000000000000)⟩
def CA5_5_6I1R3Mass : Ball := ⟨(10251159363232810376536125401349 / 25000000000000000000000000000000), (63 / 50000000000000000000000000000000)⟩
def CA5_5_6I1R3MassTermLogWitness : LogWitness := ⟨-2, 10251159363232810376536125401349, 6250000000000000000000000000000⟩
def CA5_5_6I1R3MassTermLog : Ball := ⟨(-44574250853600040046678633920341 / 50000000000000000000000000000000), (15881867839 / 25000000000000000000000000000000)⟩
def CA5_5_6I1R3MassTerm : Ball := ⟨(9138754979939402818134539391403 / 25000000000000000000000000000000), (13024604713 / 50000000000000000000000000000000)⟩
def CA5_5_6I1R3H : Ball := ⟨(10661838650173040273289430702077 / 25000000000000000000000000000000), (32003220059 / 50000000000000000000000000000000)⟩
def CA5_5_6I1R4Entropy : Ball := ⟨(2886655913384854950397474803421 / 10000000000000000000000000000000), (11135344901 / 100000000000000000000000000000000)⟩
def CA5_5_6I1R4Mass : Ball := ⟨(8709704615006561778394818864849 / 100000000000000000000000000000000), (59 / 100000000000000000000000000000000)⟩
def CA5_5_6I1R4MassTermLogWitness : LogWitness := ⟨-4, 8709704615006561778394818864849, 6250000000000000000000000000000⟩
def CA5_5_6I1R4MassTermLog : Ball := ⟨(-244073230901602138310941379700737 / 100000000000000000000000000000000), (26469779773 / 25000000000000000000000000000000)⟩
def CA5_5_6I1R4MassTerm : Ball := ⟨(4251611491166492618787916417629 / 20000000000000000000000000000000), (4610879333 / 50000000000000000000000000000000)⟩
def CA5_5_6I1R4H : Ball := ⟨(1521700335603217282007033189213 / 20000000000000000000000000000000), (20357103567 / 100000000000000000000000000000000)⟩
def CA5_5_6I1R5Entropy : Ball := ⟨(92920399505332508934279156161 / 5000000000000000000000000000000), (161404543 / 25000000000000000000000000000000)⟩
def CA5_5_6I1R5Mass : Ball := ⟨(27008255653140599382478005553 / 10000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
def CA5_5_6I1R5MassTermLogWitness : LogWitness := ⟨-9, 27008255653140599382478005553, 19531250000000000000000000000⟩
def CA5_5_6I1R5MassTermLog : Ball := ⟨(-591419778777729021357025396717877 / 100000000000000000000000000000000), (52939560133 / 25000000000000000000000000000000)⟩
def CA5_5_6I1R5MassTerm : Ball := ⟨(319464331671055250544989325127 / 20000000000000000000000000000000), (57192213 / 10000000000000000000000000000000)⟩
def CA5_5_6I1R5H : Ball := ⟨(52217266350274785192127299517 / 20000000000000000000000000000000), (608770151 / 50000000000000000000000000000000)⟩
def CA5_5_6I1R6Entropy : Ball := ⟨0, 0⟩
def CA5_5_6I1R6Mass : Ball := ⟨0, 0⟩
def CA5_5_6I1R6MassTerm : Ball := .exact 0
def CA5_5_6I1R6H : Ball := ⟨0, 0⟩
def CA5_5_6I1R7Entropy : Ball := ⟨0, 0⟩
def CA5_5_6I1R7Mass : Ball := ⟨0, 0⟩
def CA5_5_6I1R7MassTerm : Ball := .exact 0
def CA5_5_6I1R7H : Ball := ⟨0, 0⟩
def CA5_5_6I1R8Entropy : Ball := ⟨0, 0⟩
def CA5_5_6I1R8Mass : Ball := ⟨0, 0⟩
def CA5_5_6I1R8MassTerm : Ball := .exact 0
def CA5_5_6I1R8H : Ball := ⟨0, 0⟩
def CA5_5_6I1R9Entropy : Ball := ⟨0, 0⟩
def CA5_5_6I1R9Mass : Ball := ⟨0, 0⟩
def CA5_5_6I1R9MassTerm : Ball := .exact 0
def CA5_5_6I1R9H : Ball := ⟨0, 0⟩
def CA5_5_6I1R10Entropy : Ball := ⟨0, 0⟩
def CA5_5_6I1R10Mass : Ball := ⟨0, 0⟩
def CA5_5_6I1R10MassTerm : Ball := .exact 0
def CA5_5_6I1R10H : Ball := ⟨0, 0⟩
def CA5_5_6I1R11Entropy : Ball := ⟨0, 0⟩
def CA5_5_6I1R11Mass : Ball := ⟨0, 0⟩
def CA5_5_6I1R11MassTerm : Ball := .exact 0
def CA5_5_6I1R11H : Ball := ⟨0, 0⟩
def CA5_5_6I1R12Entropy : Ball := ⟨0, 0⟩
def CA5_5_6I1R12Mass : Ball := ⟨0, 0⟩
def CA5_5_6I1R12MassTerm : Ball := .exact 0
def CA5_5_6I1R12H : Ball := ⟨0, 0⟩
def CA5_5_6I1R13Entropy : Ball := ⟨0, 0⟩
def CA5_5_6I1R13Mass : Ball := ⟨0, 0⟩
def CA5_5_6I1R13MassTerm : Ball := .exact 0
def CA5_5_6I1R13H : Ball := ⟨0, 0⟩
def CA5_5_6I1R14Entropy : Ball := ⟨0, 0⟩
def CA5_5_6I1R14Mass : Ball := ⟨0, 0⟩
def CA5_5_6I1R14MassTerm : Ball := .exact 0
def CA5_5_6I1R14H : Ball := ⟨0, 0⟩
def CA5_5_6I1R15Entropy : Ball := ⟨0, 0⟩
def CA5_5_6I1R15Mass : Ball := ⟨0, 0⟩
def CA5_5_6I1R15MassTerm : Ball := .exact 0
def CA5_5_6I1R15H : Ball := ⟨0, 0⟩
def CA5_5_6I1R16Entropy : Ball := ⟨0, 0⟩
def CA5_5_6I1R16Mass : Ball := ⟨0, 0⟩
def CA5_5_6I1R16MassTerm : Ball := .exact 0
def CA5_5_6I1R16H : Ball := ⟨0, 0⟩
def CA5_5_6I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA5_5_6I1R0H
  | 1 => CA5_5_6I1R1H
  | 2 => CA5_5_6I1R2H
  | 3 => CA5_5_6I1R3H
  | 4 => CA5_5_6I1R4H
  | 5 => CA5_5_6I1R5H
  | 6 => CA5_5_6I1R6H
  | 7 => CA5_5_6I1R7H
  | 8 => CA5_5_6I1R8H
  | 9 => CA5_5_6I1R9H
  | 10 => CA5_5_6I1R10H
  | 11 => CA5_5_6I1R11H
  | 12 => CA5_5_6I1R12H
  | 13 => CA5_5_6I1R13H
  | 14 => CA5_5_6I1R14H
  | 15 => CA5_5_6I1R15H
  | 16 => CA5_5_6I1R16H
  | _ => (.exact 0)
def CA5_5_6I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 3, 5, 0 => Z3_5_0H1H
  | 4, 4, 0 => Z4_4_0H1H
  | 5, 3, 0 => Z5_3_0H1H
  | _, _, _ => (.exact 0)
def CA5_5_6I1Singleton : Ball := ⟨(19127110369820477968402652613 / 100000000000000000000000000000000), (317069 / 2000000000000000000000000000000)⟩
def CA5_5_6I1Group : Ball := ⟨(24449855014961409946479308512559 / 25000000000000000000000000000000), (20804574119 / 12500000000000000000000000000000)⟩

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
def CA5_5_6I1H : Ball := ⟨(5943894429999961068408416286193 / 5000000000000000000000000000000), (96584184323 / 20000000000000000000000000000000)⟩

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
def CA5_5_6I2PairEntropy : Ball := ⟨(7645719045720304886034929598111 / 2500000000000000000000000000000), (65603713603 / 50000000000000000000000000000000)⟩
def CA5_5_6I2PairMass : Ball := ⟨(24999999999999999999999999999999 / 25000000000000000000000000000000), (157 / 25000000000000000000000000000000)⟩
def CA5_5_6I2PairMassTermLogWitness : LogWitness := ⟨-1, 24999999999999999999999999999999, 12500000000000000000000000000000⟩
def CA5_5_6I2PairMassTermLog : Ball := ⟨(-1 / 25000000000000000000000000000000), (21175823997 / 50000000000000000000000000000000)⟩
def CA5_5_6I2PairMassTerm : Ball := ⟨(1 / 25000000000000000000000000000000), (8470329599 / 20000000000000000000000000000000)⟩
def CA5_5_6I2PairH : Ball := ⟨(76457190457203048860349295981109 / 25000000000000000000000000000000), (173559075201 / 100000000000000000000000000000000)⟩

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
def CA5_5_6I2R0Entropy : Ball := ⟨(68276483212391443391781487719 / 50000000000000000000000000000000), (46175027 / 100000000000000000000000000000000)⟩
def CA5_5_6I2R0Mass : Ball := ⟨(15575375530790721635899474223 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def CA5_5_6I2R0MassTermLogWitness : LogWitness := ⟨-13, 15575375530790721635899474223, 12207031250000000000000000000⟩
def CA5_5_6I2R0MassTermLog : Ball := ⟨(-87672342894611700539772651333191 / 10000000000000000000000000000000), (296461550823 / 100000000000000000000000000000000)⟩
def CA5_5_6I2R0MassTerm : Ball := ⟨(68276483212391443391781487719 / 50000000000000000000000000000000), (46175027 / 100000000000000000000000000000000)⟩
def CA5_5_6I2R0H : Ball := ⟨0, (46175027 / 50000000000000000000000000000000)⟩
def CA5_5_6I2R1Entropy : Ball := ⟨(168793534463164199850227551857 / 2500000000000000000000000000000), (80463843 / 3125000000000000000000000000000)⟩
def CA5_5_6I2R1Mass : Ball := ⟨(135103909759799156335132177059 / 10000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
def CA5_5_6I2R1MassTermLogWitness : LogWitness := ⟨-7, 135103909759799156335132177059, 78125000000000000000000000000⟩
def CA5_5_6I2R1MassTermLog : Ball := ⟨(-430429618768192802067370993586397 / 100000000000000000000000000000000), (42351647551 / 25000000000000000000000000000000)⟩
def CA5_5_6I2R1MassTerm : Ball := ⟨(2907636218600133681334528422563 / 50000000000000000000000000000000), (2288749311 / 100000000000000000000000000000000)⟩
def CA5_5_6I2R1H : Ball := ⟨(468234470663150315670022614577 / 50000000000000000000000000000000), (4863592287 / 100000000000000000000000000000000)⟩
def CA5_5_6I2R2Entropy : Ball := ⟨(28396361696103269921360434316719 / 50000000000000000000000000000000), (23471452803 / 100000000000000000000000000000000)⟩
def CA5_5_6I2R2Mass : Ball := ⟨(5728601642561274622206123691819 / 25000000000000000000000000000000), (59 / 50000000000000000000000000000000)⟩
def CA5_5_6I2R2MassTermLogWitness : LogWitness := ⟨-3, 5728601642561274622206123691819, 3125000000000000000000000000000⟩
def CA5_5_6I2R2MassTermLog : Ball := ⟨(-147340436536233278409874066759607 / 100000000000000000000000000000000), (84703295247 / 100000000000000000000000000000000)⟩
def CA5_5_6I2R2MassTerm : Ball := ⟨(8440546667571611990464074052287 / 25000000000000000000000000000000), (9704628813 / 50000000000000000000000000000000)⟩
def CA5_5_6I2R2H : Ball := ⟨(2303053672192009188086457242429 / 10000000000000000000000000000000), (42880710429 / 100000000000000000000000000000000)⟩
def CA5_5_6I2R3Entropy : Ball := ⟨(42827910006253249849785614807063 / 50000000000000000000000000000000), (5870811981 / 12500000000000000000000000000000)⟩
def CA5_5_6I2R3Mass : Ball := ⟨(6422068319895982483134058275067 / 12500000000000000000000000000000), (17 / 12500000000000000000000000000000)⟩
def CA5_5_6I2R3MassTermLogWitness : LogWitness := ⟨-1, 6422068319895982483134058275067, 6250000000000000000000000000000⟩
def CA5_5_6I2R3MassTermLog : Ball := ⟨(-66598841028332232150207658845161 / 100000000000000000000000000000000), (4235164763 / 10000000000000000000000000000000)⟩
def CA5_5_6I2R3MassTerm : Ball := ⟨(34216184568787296356545389408101 / 100000000000000000000000000000000), (10879407027 / 50000000000000000000000000000000)⟩
def CA5_5_6I2R3H : Ball := ⟨(2057585417748768133721033608241 / 4000000000000000000000000000000), (34362654951 / 50000000000000000000000000000000)⟩
def CA5_5_6I2R4Entropy : Ball := ⟨(5250437566787745619822915728669 / 10000000000000000000000000000000), (11363891223 / 50000000000000000000000000000000)⟩
def CA5_5_6I2R4Mass : Ball := ⟨(11279980527551382227517252762299 / 50000000000000000000000000000000), (7 / 6250000000000000000000000000000)⟩
def CA5_5_6I2R4MassTermLogWitness : LogWitness := ⟨-3, 11279980527551382227517252762299, 6250000000000000000000000000000⟩
def CA5_5_6I2R4MassTermLog : Ball := ⟨(-74449674282031453783921025571407 / 50000000000000000000000000000000), (21175823807 / 25000000000000000000000000000000)⟩
def CA5_5_6I2R4MassTerm : Ball := ⟨(4198954380919288659638450314487 / 12500000000000000000000000000000), (19109030583 / 100000000000000000000000000000000)⟩
def CA5_5_6I2R4H : Ball := ⟨(9456370310261573460560777385397 / 50000000000000000000000000000000), (41836813029 / 100000000000000000000000000000000)⟩
def CA5_5_6I2R5Entropy : Ball := ⟨(323183958239563752696145772469 / 5000000000000000000000000000000), (598232569 / 25000000000000000000000000000000)⟩
def CA5_5_6I2R5Mass : Ball := ⟨(122892479786441668451354241211 / 10000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
def CA5_5_6I2R5MassTermLogWitness : LogWitness := ⟨-7, 122892479786441668451354241211, 78125000000000000000000000000⟩
def CA5_5_6I2R5MassTermLog : Ball := ⟨(-439903054697170788664264893857777 / 100000000000000000000000000000000), (4235164761 / 2500000000000000000000000000000)⟩
def CA5_5_6I2R5MassTerm : Ball := ⟨(540607772573660047982269508961 / 10000000000000000000000000000000), (2081879653 / 100000000000000000000000000000000)⟩
def CA5_5_6I2R5H : Ball := ⟨(105760143905467457410022035977 / 10000000000000000000000000000000), (4474809929 / 100000000000000000000000000000000)⟩
def CA5_5_6I2R6Entropy : Ball := ⟨(23589226604292424392367008741 / 25000000000000000000000000000000), (32501583 / 100000000000000000000000000000000)⟩
def CA5_5_6I2R6Mass : Ball := ⟨(10143646586596796759663111597 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def CA5_5_6I2R6MassTermLogWitness : LogWitness := ⟨-14, 10143646586596796759663111597, 6103515625000000000000000000⟩
def CA5_5_6I2R6MassTermLog : Ball := ⟨(-919607790753164239606091652322159 / 100000000000000000000000000000000), (63527482879 / 20000000000000000000000000000000)⟩
def CA5_5_6I2R6MassTerm : Ball := ⟨(46640882138405778787300293759 / 50000000000000000000000000000000), (32220073 / 100000000000000000000000000000000)⟩
def CA5_5_6I2R6H : Ball := ⟨(537571070179069997433723723 / 50000000000000000000000000000000), (8090207 / 12500000000000000000000000000000)⟩
def CA5_5_6I2R7Entropy : Ball := ⟨0, 0⟩
def CA5_5_6I2R7Mass : Ball := ⟨0, 0⟩
def CA5_5_6I2R7MassTerm : Ball := .exact 0
def CA5_5_6I2R7H : Ball := ⟨0, 0⟩
def CA5_5_6I2R8Entropy : Ball := ⟨0, 0⟩
def CA5_5_6I2R8Mass : Ball := ⟨0, 0⟩
def CA5_5_6I2R8MassTerm : Ball := .exact 0
def CA5_5_6I2R8H : Ball := ⟨0, 0⟩
def CA5_5_6I2R9Entropy : Ball := ⟨0, 0⟩
def CA5_5_6I2R9Mass : Ball := ⟨0, 0⟩
def CA5_5_6I2R9MassTerm : Ball := .exact 0
def CA5_5_6I2R9H : Ball := ⟨0, 0⟩
def CA5_5_6I2R10Entropy : Ball := ⟨0, 0⟩
def CA5_5_6I2R10Mass : Ball := ⟨0, 0⟩
def CA5_5_6I2R10MassTerm : Ball := .exact 0
def CA5_5_6I2R10H : Ball := ⟨0, 0⟩
def CA5_5_6I2R11Entropy : Ball := ⟨0, 0⟩
def CA5_5_6I2R11Mass : Ball := ⟨0, 0⟩
def CA5_5_6I2R11MassTerm : Ball := .exact 0
def CA5_5_6I2R11H : Ball := ⟨0, 0⟩
def CA5_5_6I2R12Entropy : Ball := ⟨0, 0⟩
def CA5_5_6I2R12Mass : Ball := ⟨0, 0⟩
def CA5_5_6I2R12MassTerm : Ball := .exact 0
def CA5_5_6I2R12H : Ball := ⟨0, 0⟩
def CA5_5_6I2R13Entropy : Ball := ⟨0, 0⟩
def CA5_5_6I2R13Mass : Ball := ⟨0, 0⟩
def CA5_5_6I2R13MassTerm : Ball := .exact 0
def CA5_5_6I2R13H : Ball := ⟨0, 0⟩
def CA5_5_6I2R14Entropy : Ball := ⟨0, 0⟩
def CA5_5_6I2R14Mass : Ball := ⟨0, 0⟩
def CA5_5_6I2R14MassTerm : Ball := .exact 0
def CA5_5_6I2R14H : Ball := ⟨0, 0⟩
def CA5_5_6I2R15Entropy : Ball := ⟨0, 0⟩
def CA5_5_6I2R15Mass : Ball := ⟨0, 0⟩
def CA5_5_6I2R15MassTerm : Ball := .exact 0
def CA5_5_6I2R15H : Ball := ⟨0, 0⟩
def CA5_5_6I2R16Entropy : Ball := ⟨0, 0⟩
def CA5_5_6I2R16Mass : Ball := ⟨0, 0⟩
def CA5_5_6I2R16MassTerm : Ball := .exact 0
def CA5_5_6I2R16H : Ball := ⟨0, 0⟩
def CA5_5_6I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA5_5_6I2R0H
  | 1 => CA5_5_6I2R1H
  | 2 => CA5_5_6I2R2H
  | 3 => CA5_5_6I2R3H
  | 4 => CA5_5_6I2R4H
  | 5 => CA5_5_6I2R5H
  | 6 => CA5_5_6I2R6H
  | 7 => CA5_5_6I2R7H
  | 8 => CA5_5_6I2R8H
  | 9 => CA5_5_6I2R9H
  | 10 => CA5_5_6I2R10H
  | 11 => CA5_5_6I2R11H
  | 12 => CA5_5_6I2R12H
  | 13 => CA5_5_6I2R13H
  | 14 => CA5_5_6I2R14H
  | 15 => CA5_5_6I2R15H
  | 16 => CA5_5_6I2R16H
  | _ => (.exact 0)
def CA5_5_6I2Singleton : Ball := ⟨(67303983500677611484406205059 / 10000000000000000000000000000000), (8071347 / 1562500000000000000000000000000)⟩
def CA5_5_6I2Group : Ball := ⟨(96051098143690551605291162488069 / 100000000000000000000000000000000), (81727436747 / 50000000000000000000000000000000)⟩

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
def CA5_5_6I2H : Ball := ⟨(56863282770715546115407429474149 / 50000000000000000000000000000000), (500468822189 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB1_1_6I0
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
def CB1_1_6I0Value (a : Fin 17) : ℝ := marginal (below (shape 1 1 6)) (fun u => (stageBLaw (shape 1 1 6) u : ℝ)) ((stageBPriority (shape 1 1 6)) 0) a
def CB1_1_6I0Entropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (21175823693 / 50000000000000000000000000000000)⟩
def CB1_1_6I0Mass : Ball := ⟨1, (3 / 25000000000000000000000000000000)⟩
def CB1_1_6I0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB1_1_6I0MassTermLog : Ball := ⟨0, (10587911847 / 50000000000000000000000000000000)⟩
def CB1_1_6I0MassTerm : Ball := ⟨0, (4235164739 / 20000000000000000000000000000000)⟩
def CB1_1_6I0H : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (63527471081 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB1_1_6I1
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
def CB1_1_6I1PairEntropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (21175823693 / 50000000000000000000000000000000)⟩
def CB1_1_6I1PairMass : Ball := ⟨1, (3 / 25000000000000000000000000000000)⟩
def CB1_1_6I1PairMassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB1_1_6I1PairMassTermLog : Ball := ⟨0, (10587911847 / 50000000000000000000000000000000)⟩
def CB1_1_6I1PairMassTerm : Ball := ⟨0, (4235164739 / 20000000000000000000000000000000)⟩
def CB1_1_6I1PairH : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (63527471081 / 100000000000000000000000000000000)⟩

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
def CB1_1_6I1R0Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 1 6)) (fun u => (stageBLaw (shape 1 1 6) u : ℝ)) (stageBPriority (shape 1 1 6)) 1 (fun u a => (littleLaw (shape 1 1 6) u ((stageBPriority (shape 1 1 6)) 1) a : ℝ)) 0 a
def CB1_1_6I1R0Entropy : Ball := ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823693 / 100000000000000000000000000000000)⟩
def CB1_1_6I1R0Mass : Ball := ⟨(1 / 2), (3 / 50000000000000000000000000000000)⟩
def CB1_1_6I1R0MassTermLogWitness : LogWitness := ⟨-1, 1, 1⟩
def CB1_1_6I1R0MassTermLog : Ball := ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (42351647377 / 100000000000000000000000000000000)⟩
def CB1_1_6I1R0MassTerm : Ball := ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823693 / 100000000000000000000000000000000)⟩
def CB1_1_6I1R0H : Ball := ⟨0, (21175823693 / 50000000000000000000000000000000)⟩
def CB1_1_6I1R1Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 1 6)) (fun u => (stageBLaw (shape 1 1 6) u : ℝ)) (stageBPriority (shape 1 1 6)) 1 (fun u a => (littleLaw (shape 1 1 6) u ((stageBPriority (shape 1 1 6)) 1) a : ℝ)) 1 a
def CB1_1_6I1R1Entropy : Ball := ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823693 / 100000000000000000000000000000000)⟩
def CB1_1_6I1R1Mass : Ball := ⟨(1 / 2), (3 / 50000000000000000000000000000000)⟩
def CB1_1_6I1R1MassTermLogWitness : LogWitness := ⟨-1, 1, 1⟩
def CB1_1_6I1R1MassTermLog : Ball := ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (42351647377 / 100000000000000000000000000000000)⟩
def CB1_1_6I1R1MassTerm : Ball := ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823693 / 100000000000000000000000000000000)⟩
def CB1_1_6I1R1H : Ball := ⟨0, (21175823693 / 50000000000000000000000000000000)⟩
def CB1_1_6I1R2Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 1 6)) (fun u => (stageBLaw (shape 1 1 6) u : ℝ)) (stageBPriority (shape 1 1 6)) 1 (fun u a => (littleLaw (shape 1 1 6) u ((stageBPriority (shape 1 1 6)) 1) a : ℝ)) 2 a
def CB1_1_6I1R2Entropy : Ball := ⟨0, 0⟩
def CB1_1_6I1R2Mass : Ball := ⟨0, 0⟩
def CB1_1_6I1R2MassTerm : Ball := .exact 0
def CB1_1_6I1R2H : Ball := ⟨0, 0⟩
def CB1_1_6I1R3Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 1 6)) (fun u => (stageBLaw (shape 1 1 6) u : ℝ)) (stageBPriority (shape 1 1 6)) 1 (fun u a => (littleLaw (shape 1 1 6) u ((stageBPriority (shape 1 1 6)) 1) a : ℝ)) 3 a
def CB1_1_6I1R3Entropy : Ball := ⟨0, 0⟩
def CB1_1_6I1R3Mass : Ball := ⟨0, 0⟩
def CB1_1_6I1R3MassTerm : Ball := .exact 0
def CB1_1_6I1R3H : Ball := ⟨0, 0⟩
def CB1_1_6I1R4Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 1 6)) (fun u => (stageBLaw (shape 1 1 6) u : ℝ)) (stageBPriority (shape 1 1 6)) 1 (fun u a => (littleLaw (shape 1 1 6) u ((stageBPriority (shape 1 1 6)) 1) a : ℝ)) 4 a
def CB1_1_6I1R4Entropy : Ball := ⟨0, 0⟩
def CB1_1_6I1R4Mass : Ball := ⟨0, 0⟩
def CB1_1_6I1R4MassTerm : Ball := .exact 0
def CB1_1_6I1R4H : Ball := ⟨0, 0⟩
def CB1_1_6I1R5Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 1 6)) (fun u => (stageBLaw (shape 1 1 6) u : ℝ)) (stageBPriority (shape 1 1 6)) 1 (fun u a => (littleLaw (shape 1 1 6) u ((stageBPriority (shape 1 1 6)) 1) a : ℝ)) 5 a
def CB1_1_6I1R5Entropy : Ball := ⟨0, 0⟩
def CB1_1_6I1R5Mass : Ball := ⟨0, 0⟩
def CB1_1_6I1R5MassTerm : Ball := .exact 0
def CB1_1_6I1R5H : Ball := ⟨0, 0⟩
def CB1_1_6I1R6Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 1 6)) (fun u => (stageBLaw (shape 1 1 6) u : ℝ)) (stageBPriority (shape 1 1 6)) 1 (fun u a => (littleLaw (shape 1 1 6) u ((stageBPriority (shape 1 1 6)) 1) a : ℝ)) 6 a
def CB1_1_6I1R6Entropy : Ball := ⟨0, 0⟩
def CB1_1_6I1R6Mass : Ball := ⟨0, 0⟩
def CB1_1_6I1R6MassTerm : Ball := .exact 0
def CB1_1_6I1R6H : Ball := ⟨0, 0⟩
def CB1_1_6I1R7Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 1 6)) (fun u => (stageBLaw (shape 1 1 6) u : ℝ)) (stageBPriority (shape 1 1 6)) 1 (fun u a => (littleLaw (shape 1 1 6) u ((stageBPriority (shape 1 1 6)) 1) a : ℝ)) 7 a
def CB1_1_6I1R7Entropy : Ball := ⟨0, 0⟩
def CB1_1_6I1R7Mass : Ball := ⟨0, 0⟩
def CB1_1_6I1R7MassTerm : Ball := .exact 0
def CB1_1_6I1R7H : Ball := ⟨0, 0⟩
def CB1_1_6I1R8Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 1 6)) (fun u => (stageBLaw (shape 1 1 6) u : ℝ)) (stageBPriority (shape 1 1 6)) 1 (fun u a => (littleLaw (shape 1 1 6) u ((stageBPriority (shape 1 1 6)) 1) a : ℝ)) 8 a
def CB1_1_6I1R8Entropy : Ball := ⟨0, 0⟩
def CB1_1_6I1R8Mass : Ball := ⟨0, 0⟩
def CB1_1_6I1R8MassTerm : Ball := .exact 0
def CB1_1_6I1R8H : Ball := ⟨0, 0⟩
def CB1_1_6I1R9Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 1 6)) (fun u => (stageBLaw (shape 1 1 6) u : ℝ)) (stageBPriority (shape 1 1 6)) 1 (fun u a => (littleLaw (shape 1 1 6) u ((stageBPriority (shape 1 1 6)) 1) a : ℝ)) 9 a
def CB1_1_6I1R9Entropy : Ball := ⟨0, 0⟩
def CB1_1_6I1R9Mass : Ball := ⟨0, 0⟩
def CB1_1_6I1R9MassTerm : Ball := .exact 0
def CB1_1_6I1R9H : Ball := ⟨0, 0⟩
def CB1_1_6I1R10Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 1 6)) (fun u => (stageBLaw (shape 1 1 6) u : ℝ)) (stageBPriority (shape 1 1 6)) 1 (fun u a => (littleLaw (shape 1 1 6) u ((stageBPriority (shape 1 1 6)) 1) a : ℝ)) 10 a
def CB1_1_6I1R10Entropy : Ball := ⟨0, 0⟩
def CB1_1_6I1R10Mass : Ball := ⟨0, 0⟩
def CB1_1_6I1R10MassTerm : Ball := .exact 0
def CB1_1_6I1R10H : Ball := ⟨0, 0⟩
def CB1_1_6I1R11Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 1 6)) (fun u => (stageBLaw (shape 1 1 6) u : ℝ)) (stageBPriority (shape 1 1 6)) 1 (fun u a => (littleLaw (shape 1 1 6) u ((stageBPriority (shape 1 1 6)) 1) a : ℝ)) 11 a
def CB1_1_6I1R11Entropy : Ball := ⟨0, 0⟩
def CB1_1_6I1R11Mass : Ball := ⟨0, 0⟩
def CB1_1_6I1R11MassTerm : Ball := .exact 0
def CB1_1_6I1R11H : Ball := ⟨0, 0⟩
def CB1_1_6I1R12Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 1 6)) (fun u => (stageBLaw (shape 1 1 6) u : ℝ)) (stageBPriority (shape 1 1 6)) 1 (fun u a => (littleLaw (shape 1 1 6) u ((stageBPriority (shape 1 1 6)) 1) a : ℝ)) 12 a
def CB1_1_6I1R12Entropy : Ball := ⟨0, 0⟩
def CB1_1_6I1R12Mass : Ball := ⟨0, 0⟩
def CB1_1_6I1R12MassTerm : Ball := .exact 0
def CB1_1_6I1R12H : Ball := ⟨0, 0⟩
def CB1_1_6I1R13Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 1 6)) (fun u => (stageBLaw (shape 1 1 6) u : ℝ)) (stageBPriority (shape 1 1 6)) 1 (fun u a => (littleLaw (shape 1 1 6) u ((stageBPriority (shape 1 1 6)) 1) a : ℝ)) 13 a
def CB1_1_6I1R13Entropy : Ball := ⟨0, 0⟩
def CB1_1_6I1R13Mass : Ball := ⟨0, 0⟩
def CB1_1_6I1R13MassTerm : Ball := .exact 0
def CB1_1_6I1R13H : Ball := ⟨0, 0⟩
def CB1_1_6I1R14Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 1 6)) (fun u => (stageBLaw (shape 1 1 6) u : ℝ)) (stageBPriority (shape 1 1 6)) 1 (fun u a => (littleLaw (shape 1 1 6) u ((stageBPriority (shape 1 1 6)) 1) a : ℝ)) 14 a
def CB1_1_6I1R14Entropy : Ball := ⟨0, 0⟩
def CB1_1_6I1R14Mass : Ball := ⟨0, 0⟩
def CB1_1_6I1R14MassTerm : Ball := .exact 0
def CB1_1_6I1R14H : Ball := ⟨0, 0⟩
def CB1_1_6I1R15Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 1 6)) (fun u => (stageBLaw (shape 1 1 6) u : ℝ)) (stageBPriority (shape 1 1 6)) 1 (fun u a => (littleLaw (shape 1 1 6) u ((stageBPriority (shape 1 1 6)) 1) a : ℝ)) 15 a
def CB1_1_6I1R15Entropy : Ball := ⟨0, 0⟩
def CB1_1_6I1R15Mass : Ball := ⟨0, 0⟩
def CB1_1_6I1R15MassTerm : Ball := .exact 0
def CB1_1_6I1R15H : Ball := ⟨0, 0⟩
def CB1_1_6I1R16Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 1 6)) (fun u => (stageBLaw (shape 1 1 6) u : ℝ)) (stageBPriority (shape 1 1 6)) 1 (fun u a => (littleLaw (shape 1 1 6) u ((stageBPriority (shape 1 1 6)) 1) a : ℝ)) 16 a
def CB1_1_6I1R16Entropy : Ball := ⟨0, 0⟩
def CB1_1_6I1R16Mass : Ball := ⟨0, 0⟩
def CB1_1_6I1R16MassTerm : Ball := .exact 0
def CB1_1_6I1R16H : Ball := ⟨0, 0⟩
def CB1_1_6I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CB1_1_6I1R0H
  | 1 => CB1_1_6I1R1H
  | 2 => CB1_1_6I1R2H
  | 3 => CB1_1_6I1R3H
  | 4 => CB1_1_6I1R4H
  | 5 => CB1_1_6I1R5H
  | 6 => CB1_1_6I1R6H
  | 7 => CB1_1_6I1R7H
  | 8 => CB1_1_6I1R8H
  | 9 => CB1_1_6I1R9H
  | 10 => CB1_1_6I1R10H
  | 11 => CB1_1_6I1R11H
  | 12 => CB1_1_6I1R12H
  | 13 => CB1_1_6I1R13H
  | 14 => CB1_1_6I1R14H
  | 15 => CB1_1_6I1R15H
  | 16 => CB1_1_6I1R16H
  | _ => (.exact 0)
def CB1_1_6I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | _, _, _ => (.exact 0)
def CB1_1_6I1Singleton : Ball := ⟨0, 0⟩
def CB1_1_6I1Group : Ball := ⟨0, (21175823693 / 25000000000000000000000000000000)⟩

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
def CB1_1_6I1H : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (372694497 / 160000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB1_1_6I2
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
def CB1_1_6I2PairEntropy : Ball := ⟨(2649791993391134161133427463893 / 25000000000000000000000000000000), (139781723 / 312500000000000000000000000000)⟩
def CB1_1_6I2PairMass : Ball := ⟨1, (1 / 6250000000000000000000000000000)⟩
def CB1_1_6I2PairMassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB1_1_6I2PairMassTermLog : Ball := ⟨0, (10587911849 / 50000000000000000000000000000000)⟩
def CB1_1_6I2PairMassTerm : Ball := ⟨0, (21175823699 / 100000000000000000000000000000000)⟩
def CB1_1_6I2PairH : Ball := ⟨(2649791993391134161133427463893 / 25000000000000000000000000000000), (65905975059 / 100000000000000000000000000000000)⟩

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
def CB1_1_6I2R0Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 1 6)) (fun u => (stageBLaw (shape 1 1 6) u : ℝ)) (stageBPriority (shape 1 1 6)) 2 (fun u a => (littleLaw (shape 1 1 6) u ((stageBPriority (shape 1 1 6)) 2) a : ℝ)) 0 a
def CB1_1_6I2R0Entropy : Ball := ⟨0, 0⟩
def CB1_1_6I2R0Mass : Ball := ⟨0, 0⟩
def CB1_1_6I2R0MassTerm : Ball := .exact 0
def CB1_1_6I2R0H : Ball := ⟨0, 0⟩
def CB1_1_6I2R1Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 1 6)) (fun u => (stageBLaw (shape 1 1 6) u : ℝ)) (stageBPriority (shape 1 1 6)) 2 (fun u a => (littleLaw (shape 1 1 6) u ((stageBPriority (shape 1 1 6)) 2) a : ℝ)) 1 a
def CB1_1_6I2R1Entropy : Ball := ⟨0, 0⟩
def CB1_1_6I2R1Mass : Ball := ⟨0, 0⟩
def CB1_1_6I2R1MassTerm : Ball := .exact 0
def CB1_1_6I2R1H : Ball := ⟨0, 0⟩
def CB1_1_6I2R2Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 1 6)) (fun u => (stageBLaw (shape 1 1 6) u : ℝ)) (stageBPriority (shape 1 1 6)) 2 (fun u a => (littleLaw (shape 1 1 6) u ((stageBPriority (shape 1 1 6)) 2) a : ℝ)) 2 a
def CB1_1_6I2R2Entropy : Ball := ⟨(4372521442184919741117703745571 / 100000000000000000000000000000000), (1585611047 / 100000000000000000000000000000000)⟩
def CB1_1_6I2R2Mass : Ball := ⟨(935876354068540274256216050051 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
def CB1_1_6I2R2MassTermLogWitness : LogWitness := ⟨-7, 935876354068540274256216050051, 781250000000000000000000000000⟩
def CB1_1_6I2R2MassTermLog : Ball := ⟨(-5839302621965975341803519774219 / 1250000000000000000000000000000), (169406589997 / 100000000000000000000000000000000)⟩
def CB1_1_6I2R2MassTerm : Ball := ⟨(136621631203709617952889282303 / 3125000000000000000000000000000), (792718121 / 50000000000000000000000000000000)⟩
def CB1_1_6I2R2H : Ball := ⟨(1006789865939146600394739 / 160000000000000000000000000000), (3171047289 / 100000000000000000000000000000000)⟩
def CB1_1_6I2R3Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 1 6)) (fun u => (stageBLaw (shape 1 1 6) u : ℝ)) (stageBPriority (shape 1 1 6)) 2 (fun u a => (littleLaw (shape 1 1 6) u ((stageBPriority (shape 1 1 6)) 2) a : ℝ)) 3 a
def CB1_1_6I2R3Entropy : Ball := ⟨0, 0⟩
def CB1_1_6I2R3Mass : Ball := ⟨0, 0⟩
def CB1_1_6I2R3MassTerm : Ball := .exact 0
def CB1_1_6I2R3H : Ball := ⟨0, 0⟩
def CB1_1_6I2R4Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 1 6)) (fun u => (stageBLaw (shape 1 1 6) u : ℝ)) (stageBPriority (shape 1 1 6)) 2 (fun u a => (littleLaw (shape 1 1 6) u ((stageBPriority (shape 1 1 6)) 2) a : ℝ)) 4 a
def CB1_1_6I2R4Entropy : Ball := ⟨0, 0⟩
def CB1_1_6I2R4Mass : Ball := ⟨0, 0⟩
def CB1_1_6I2R4MassTerm : Ball := .exact 0
def CB1_1_6I2R4H : Ball := ⟨0, 0⟩
def CB1_1_6I2R5Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 1 6)) (fun u => (stageBLaw (shape 1 1 6) u : ℝ)) (stageBPriority (shape 1 1 6)) 2 (fun u a => (littleLaw (shape 1 1 6) u ((stageBPriority (shape 1 1 6)) 2) a : ℝ)) 5 a
def CB1_1_6I2R5Entropy : Ball := ⟨0, 0⟩
def CB1_1_6I2R5Mass : Ball := ⟨0, 0⟩
def CB1_1_6I2R5MassTerm : Ball := .exact 0
def CB1_1_6I2R5H : Ball := ⟨0, 0⟩
def CB1_1_6I2R6Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 1 6)) (fun u => (stageBLaw (shape 1 1 6) u : ℝ)) (stageBPriority (shape 1 1 6)) 2 (fun u a => (littleLaw (shape 1 1 6) u ((stageBPriority (shape 1 1 6)) 2) a : ℝ)) 6 a
def CB1_1_6I2R6Entropy : Ball := ⟨0, 0⟩
def CB1_1_6I2R6Mass : Ball := ⟨0, 0⟩
def CB1_1_6I2R6MassTerm : Ball := .exact 0
def CB1_1_6I2R6H : Ball := ⟨0, 0⟩
def CB1_1_6I2R7Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 1 6)) (fun u => (stageBLaw (shape 1 1 6) u : ℝ)) (stageBPriority (shape 1 1 6)) 2 (fun u a => (littleLaw (shape 1 1 6) u ((stageBPriority (shape 1 1 6)) 2) a : ℝ)) 7 a
def CB1_1_6I2R7Entropy : Ball := ⟨0, 0⟩
def CB1_1_6I2R7Mass : Ball := ⟨0, 0⟩
def CB1_1_6I2R7MassTerm : Ball := .exact 0
def CB1_1_6I2R7H : Ball := ⟨0, 0⟩
def CB1_1_6I2R8Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 1 6)) (fun u => (stageBLaw (shape 1 1 6) u : ℝ)) (stageBPriority (shape 1 1 6)) 2 (fun u a => (littleLaw (shape 1 1 6) u ((stageBPriority (shape 1 1 6)) 2) a : ℝ)) 8 a
def CB1_1_6I2R8Entropy : Ball := ⟨0, 0⟩
def CB1_1_6I2R8Mass : Ball := ⟨0, 0⟩
def CB1_1_6I2R8MassTerm : Ball := .exact 0
def CB1_1_6I2R8H : Ball := ⟨0, 0⟩
def CB1_1_6I2R9Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 1 6)) (fun u => (stageBLaw (shape 1 1 6) u : ℝ)) (stageBPriority (shape 1 1 6)) 2 (fun u a => (littleLaw (shape 1 1 6) u ((stageBPriority (shape 1 1 6)) 2) a : ℝ)) 9 a
def CB1_1_6I2R9Entropy : Ball := ⟨0, 0⟩
def CB1_1_6I2R9Mass : Ball := ⟨0, 0⟩
def CB1_1_6I2R9MassTerm : Ball := .exact 0
def CB1_1_6I2R9H : Ball := ⟨0, 0⟩
def CB1_1_6I2R10Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 1 6)) (fun u => (stageBLaw (shape 1 1 6) u : ℝ)) (stageBPriority (shape 1 1 6)) 2 (fun u a => (littleLaw (shape 1 1 6) u ((stageBPriority (shape 1 1 6)) 2) a : ℝ)) 10 a
def CB1_1_6I2R10Entropy : Ball := ⟨0, 0⟩
def CB1_1_6I2R10Mass : Ball := ⟨0, 0⟩
def CB1_1_6I2R10MassTerm : Ball := .exact 0
def CB1_1_6I2R10H : Ball := ⟨0, 0⟩
def CB1_1_6I2R11Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 1 6)) (fun u => (stageBLaw (shape 1 1 6) u : ℝ)) (stageBPriority (shape 1 1 6)) 2 (fun u a => (littleLaw (shape 1 1 6) u ((stageBPriority (shape 1 1 6)) 2) a : ℝ)) 11 a
def CB1_1_6I2R11Entropy : Ball := ⟨0, 0⟩
def CB1_1_6I2R11Mass : Ball := ⟨0, 0⟩
def CB1_1_6I2R11MassTerm : Ball := .exact 0
def CB1_1_6I2R11H : Ball := ⟨0, 0⟩
def CB1_1_6I2R12Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 1 6)) (fun u => (stageBLaw (shape 1 1 6) u : ℝ)) (stageBPriority (shape 1 1 6)) 2 (fun u a => (littleLaw (shape 1 1 6) u ((stageBPriority (shape 1 1 6)) 2) a : ℝ)) 12 a
def CB1_1_6I2R12Entropy : Ball := ⟨0, 0⟩
def CB1_1_6I2R12Mass : Ball := ⟨0, 0⟩
def CB1_1_6I2R12MassTerm : Ball := .exact 0
def CB1_1_6I2R12H : Ball := ⟨0, 0⟩
def CB1_1_6I2R13Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 1 6)) (fun u => (stageBLaw (shape 1 1 6) u : ℝ)) (stageBPriority (shape 1 1 6)) 2 (fun u a => (littleLaw (shape 1 1 6) u ((stageBPriority (shape 1 1 6)) 2) a : ℝ)) 13 a
def CB1_1_6I2R13Entropy : Ball := ⟨0, 0⟩
def CB1_1_6I2R13Mass : Ball := ⟨0, 0⟩
def CB1_1_6I2R13MassTerm : Ball := .exact 0
def CB1_1_6I2R13H : Ball := ⟨0, 0⟩
def CB1_1_6I2R14Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 1 6)) (fun u => (stageBLaw (shape 1 1 6) u : ℝ)) (stageBPriority (shape 1 1 6)) 2 (fun u a => (littleLaw (shape 1 1 6) u ((stageBPriority (shape 1 1 6)) 2) a : ℝ)) 14 a
def CB1_1_6I2R14Entropy : Ball := ⟨0, 0⟩
def CB1_1_6I2R14Mass : Ball := ⟨0, 0⟩
def CB1_1_6I2R14MassTerm : Ball := .exact 0
def CB1_1_6I2R14H : Ball := ⟨0, 0⟩
def CB1_1_6I2R15Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 1 6)) (fun u => (stageBLaw (shape 1 1 6) u : ℝ)) (stageBPriority (shape 1 1 6)) 2 (fun u a => (littleLaw (shape 1 1 6) u ((stageBPriority (shape 1 1 6)) 2) a : ℝ)) 15 a
def CB1_1_6I2R15Entropy : Ball := ⟨0, 0⟩
def CB1_1_6I2R15Mass : Ball := ⟨0, 0⟩
def CB1_1_6I2R15MassTerm : Ball := .exact 0
def CB1_1_6I2R15H : Ball := ⟨0, 0⟩
def CB1_1_6I2R16Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 1 6)) (fun u => (stageBLaw (shape 1 1 6) u : ℝ)) (stageBPriority (shape 1 1 6)) 2 (fun u a => (littleLaw (shape 1 1 6) u ((stageBPriority (shape 1 1 6)) 2) a : ℝ)) 16 a
def CB1_1_6I2R16Entropy : Ball := ⟨0, 0⟩
def CB1_1_6I2R16Mass : Ball := ⟨0, 0⟩
def CB1_1_6I2R16MassTerm : Ball := .exact 0
def CB1_1_6I2R16H : Ball := ⟨0, 0⟩
def CB1_1_6I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CB1_1_6I2R0H
  | 1 => CB1_1_6I2R1H
  | 2 => CB1_1_6I2R2H
  | 3 => CB1_1_6I2R3H
  | 4 => CB1_1_6I2R4H
  | 5 => CB1_1_6I2R5H
  | 6 => CB1_1_6I2R6H
  | 7 => CB1_1_6I2R7H
  | 8 => CB1_1_6I2R8H
  | 9 => CB1_1_6I2R9H
  | 10 => CB1_1_6I2R10H
  | 11 => CB1_1_6I2R11H
  | 12 => CB1_1_6I2R12H
  | 13 => CB1_1_6I2R13H
  | 14 => CB1_1_6I2R14H
  | 15 => CB1_1_6I2R15H
  | 16 => CB1_1_6I2R16H
  | _ => (.exact 0)
def CB1_1_6I2S0_0_4Value (a : Fin 6) : ℝ := (littleLaw (shape 1 1 6) (shape 0 0 4) ((stageBPriority (shape 1 1 6)) 2) a : ℝ)
def CB1_1_6I2S0_0_4E_5Log : Ball := .exact 0
def CB1_1_6I2S0_0_4E_5 : Ball := ⟨0, 0⟩
def CB1_1_6I2S0_0_4Terms (a : Fin 6) : Ball :=
  match a.val with
  | 5 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB1_1_6I2S0_0_4Entropy : Ball := ⟨0, 0⟩
def CB1_1_6I2S0_0_4Mass : Ball := ⟨1, 0⟩
def CB1_1_6I2S0_0_4MassTermLog : Ball := .exact 0
def CB1_1_6I2S0_0_4MassTerm : Ball := ⟨0, 0⟩
def CB1_1_6I2S0_0_4H : Ball := ⟨0, 0⟩
def CB1_1_6I2S0_1_3Value (a : Fin 6) : ℝ := (littleLaw (shape 1 1 6) (shape 0 1 3) ((stageBPriority (shape 1 1 6)) 2) a : ℝ)
def CB1_1_6I2S0_1_3E_4Log : Ball := .exact 0
def CB1_1_6I2S0_1_3E_4 : Ball := ⟨0, 0⟩
def CB1_1_6I2S0_1_3Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB1_1_6I2S0_1_3Entropy : Ball := ⟨0, 0⟩
def CB1_1_6I2S0_1_3Mass : Ball := ⟨1, 0⟩
def CB1_1_6I2S0_1_3MassTermLog : Ball := .exact 0
def CB1_1_6I2S0_1_3MassTerm : Ball := ⟨0, 0⟩
def CB1_1_6I2S0_1_3H : Ball := ⟨0, 0⟩
def CB1_1_6I2S1_0_3Value (a : Fin 6) : ℝ := (littleLaw (shape 1 1 6) (shape 1 0 3) ((stageBPriority (shape 1 1 6)) 2) a : ℝ)
def CB1_1_6I2S1_0_3E_4Log : Ball := .exact 0
def CB1_1_6I2S1_0_3E_4 : Ball := ⟨0, 0⟩
def CB1_1_6I2S1_0_3Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB1_1_6I2S1_0_3Entropy : Ball := ⟨0, 0⟩
def CB1_1_6I2S1_0_3Mass : Ball := ⟨1, 0⟩
def CB1_1_6I2S1_0_3MassTermLog : Ball := .exact 0
def CB1_1_6I2S1_0_3MassTerm : Ball := ⟨0, 0⟩
def CB1_1_6I2S1_0_3H : Ball := ⟨0, 0⟩
def CB1_1_6I2Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => CB1_1_6I2S0_0_4H
  | 0, 1, 3 => CB1_1_6I2S0_1_3H
  | 1, 0, 3 => CB1_1_6I2S1_0_3H
  | _, _, _ => (.exact 0)
def CB1_1_6I2Singleton : Ball := ⟨0, 0⟩
def CB1_1_6I2Group : Ball := ⟨(1006789865939146600394739 / 160000000000000000000000000000), (3171047289 / 100000000000000000000000000000000)⟩

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
def CB1_1_6I2H : Ball := ⟨(5298954743116056355641608215911 / 50000000000000000000000000000000), (72248069637 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB1_2_5I0
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
def CB1_2_5I0Value (a : Fin 17) : ℝ := marginal (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) ((stageBPriority (shape 1 2 5)) 0) a
def CB1_2_5I0Entropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (2646977971 / 6250000000000000000000000000000)⟩
def CB1_2_5I0Mass : Ball := ⟨1, (1 / 1000000000000000000000000000000)⟩
def CB1_2_5I0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB1_2_5I0MassTermLog : Ball := ⟨0, (10587911891 / 50000000000000000000000000000000)⟩
def CB1_2_5I0MassTerm : Ball := ⟨0, (21175823783 / 100000000000000000000000000000000)⟩
def CB1_2_5I0H : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (63527471319 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB1_2_5I1
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
def CB1_2_5I1PairEntropy : Ball := ⟨(102640618134804607996736335335607 / 100000000000000000000000000000000), (60087317757 / 100000000000000000000000000000000)⟩
def CB1_2_5I1PairMass : Ball := ⟨1, (13 / 12500000000000000000000000000000)⟩
def CB1_2_5I1PairMassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB1_2_5I1PairMassTermLog : Ball := ⟨0, (10587911893 / 50000000000000000000000000000000)⟩
def CB1_2_5I1PairMassTerm : Ball := ⟨0, (21175823787 / 100000000000000000000000000000000)⟩
def CB1_2_5I1PairH : Ball := ⟨(102640618134804607996736335335607 / 100000000000000000000000000000000), (10157892693 / 12500000000000000000000000000000)⟩

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
def CB1_2_5I1R0Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 1 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 1) a : ℝ)) 0 a
def CB1_2_5I1R0Entropy : Ball := ⟨(31056367098208207478678397415287 / 100000000000000000000000000000000), (7737049887 / 50000000000000000000000000000000)⟩
def CB1_2_5I1R0Mass : Ball := ⟨(228357405259132776332554478709 / 1250000000000000000000000000000), (17 / 50000000000000000000000000000000)⟩
def CB1_2_5I1R0MassTermLogWitness : LogWitness := ⟨-3, 228357405259132776332554478709, 156250000000000000000000000000⟩
def CB1_2_5I1R0MassTermLog : Ball := ⟨(-169998686176645017605219863694851 / 100000000000000000000000000000000), (42351647459 / 50000000000000000000000000000000)⟩
def CB1_2_5I1R0MassTerm : Ball := ⟨(31056367098208207478678397415287 / 100000000000000000000000000000000), (7737049887 / 50000000000000000000000000000000)⟩
def CB1_2_5I1R0H : Ball := ⟨0, (7737049887 / 25000000000000000000000000000000)⟩
def CB1_2_5I1R1Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 1 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 1) a : ℝ)) 1 a
def CB1_2_5I1R1Entropy : Ball := ⟨(28857559975047847690218380534771 / 100000000000000000000000000000000), (26877547731 / 100000000000000000000000000000000)⟩
def CB1_2_5I1R1Mass : Ball := ⟨(396642594740867223667445521291 / 625000000000000000000000000000), (1 / 3125000000000000000000000000000)⟩
def CB1_2_5I1R1MassTermLogWitness : LogWitness := ⟨-1, 396642594740867223667445521291, 312500000000000000000000000000⟩
def CB1_2_5I1R1MassTermLog : Ball := ⟨(-45471603966760271388874596887337 / 100000000000000000000000000000000), (5293955927 / 12500000000000000000000000000000)⟩
def CB1_2_5I1R1MassTerm : Ball := ⟨(28857559975047847690218380534771 / 100000000000000000000000000000000), (26877547731 / 100000000000000000000000000000000)⟩
def CB1_2_5I1R1H : Ball := ⟨0, (26877547731 / 50000000000000000000000000000000)⟩
def CB1_2_5I1R2Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 1 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 1) a : ℝ)) 2 a
def CB1_2_5I1R2Entropy : Ball := ⟨(18445764539939190076629488700209 / 50000000000000000000000000000000), (16604885013 / 100000000000000000000000000000000)⟩
def CB1_2_5I1R2Mass : Ball := ⟨(228357405259132776332554478709 / 1250000000000000000000000000000), (9 / 25000000000000000000000000000000)⟩
def CB1_2_5I1R2MassTermLogWitness : LogWitness := ⟨-3, 228357405259132776332554478709, 156250000000000000000000000000⟩
def CB1_2_5I1R2MassTermLog : Ball := ⟨(-169998686176645017605219863694851 / 100000000000000000000000000000000), (84703294929 / 100000000000000000000000000000000)⟩
def CB1_2_5I1R2MassTerm : Ball := ⟨(31056367098208207478678397415287 / 100000000000000000000000000000000), (15474099779 / 100000000000000000000000000000000)⟩
def CB1_2_5I1R2H : Ball := ⟨(5835161981670172674580579985131 / 100000000000000000000000000000000), (4009873099 / 12500000000000000000000000000000)⟩
def CB1_2_5I1R3Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 1 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 1) a : ℝ)) 3 a
def CB1_2_5I1R3Entropy : Ball := ⟨0, 0⟩
def CB1_2_5I1R3Mass : Ball := ⟨0, 0⟩
def CB1_2_5I1R3MassTerm : Ball := .exact 0
def CB1_2_5I1R3H : Ball := ⟨0, 0⟩
def CB1_2_5I1R4Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 1 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 1) a : ℝ)) 4 a
def CB1_2_5I1R4Entropy : Ball := ⟨0, 0⟩
def CB1_2_5I1R4Mass : Ball := ⟨0, 0⟩
def CB1_2_5I1R4MassTerm : Ball := .exact 0
def CB1_2_5I1R4H : Ball := ⟨0, 0⟩
def CB1_2_5I1R5Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 1 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 1) a : ℝ)) 5 a
def CB1_2_5I1R5Entropy : Ball := ⟨0, 0⟩
def CB1_2_5I1R5Mass : Ball := ⟨0, 0⟩
def CB1_2_5I1R5MassTerm : Ball := .exact 0
def CB1_2_5I1R5H : Ball := ⟨0, 0⟩
def CB1_2_5I1R6Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 1 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 1) a : ℝ)) 6 a
def CB1_2_5I1R6Entropy : Ball := ⟨0, 0⟩
def CB1_2_5I1R6Mass : Ball := ⟨0, 0⟩
def CB1_2_5I1R6MassTerm : Ball := .exact 0
def CB1_2_5I1R6H : Ball := ⟨0, 0⟩
def CB1_2_5I1R7Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 1 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 1) a : ℝ)) 7 a
def CB1_2_5I1R7Entropy : Ball := ⟨0, 0⟩
def CB1_2_5I1R7Mass : Ball := ⟨0, 0⟩
def CB1_2_5I1R7MassTerm : Ball := .exact 0
def CB1_2_5I1R7H : Ball := ⟨0, 0⟩
def CB1_2_5I1R8Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 1 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 1) a : ℝ)) 8 a
def CB1_2_5I1R8Entropy : Ball := ⟨0, 0⟩
def CB1_2_5I1R8Mass : Ball := ⟨0, 0⟩
def CB1_2_5I1R8MassTerm : Ball := .exact 0
def CB1_2_5I1R8H : Ball := ⟨0, 0⟩
def CB1_2_5I1R9Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 1 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 1) a : ℝ)) 9 a
def CB1_2_5I1R9Entropy : Ball := ⟨0, 0⟩
def CB1_2_5I1R9Mass : Ball := ⟨0, 0⟩
def CB1_2_5I1R9MassTerm : Ball := .exact 0
def CB1_2_5I1R9H : Ball := ⟨0, 0⟩
def CB1_2_5I1R10Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 1 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 1) a : ℝ)) 10 a
def CB1_2_5I1R10Entropy : Ball := ⟨0, 0⟩
def CB1_2_5I1R10Mass : Ball := ⟨0, 0⟩
def CB1_2_5I1R10MassTerm : Ball := .exact 0
def CB1_2_5I1R10H : Ball := ⟨0, 0⟩
def CB1_2_5I1R11Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 1 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 1) a : ℝ)) 11 a
def CB1_2_5I1R11Entropy : Ball := ⟨0, 0⟩
def CB1_2_5I1R11Mass : Ball := ⟨0, 0⟩
def CB1_2_5I1R11MassTerm : Ball := .exact 0
def CB1_2_5I1R11H : Ball := ⟨0, 0⟩
def CB1_2_5I1R12Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 1 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 1) a : ℝ)) 12 a
def CB1_2_5I1R12Entropy : Ball := ⟨0, 0⟩
def CB1_2_5I1R12Mass : Ball := ⟨0, 0⟩
def CB1_2_5I1R12MassTerm : Ball := .exact 0
def CB1_2_5I1R12H : Ball := ⟨0, 0⟩
def CB1_2_5I1R13Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 1 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 1) a : ℝ)) 13 a
def CB1_2_5I1R13Entropy : Ball := ⟨0, 0⟩
def CB1_2_5I1R13Mass : Ball := ⟨0, 0⟩
def CB1_2_5I1R13MassTerm : Ball := .exact 0
def CB1_2_5I1R13H : Ball := ⟨0, 0⟩
def CB1_2_5I1R14Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 1 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 1) a : ℝ)) 14 a
def CB1_2_5I1R14Entropy : Ball := ⟨0, 0⟩
def CB1_2_5I1R14Mass : Ball := ⟨0, 0⟩
def CB1_2_5I1R14MassTerm : Ball := .exact 0
def CB1_2_5I1R14H : Ball := ⟨0, 0⟩
def CB1_2_5I1R15Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 1 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 1) a : ℝ)) 15 a
def CB1_2_5I1R15Entropy : Ball := ⟨0, 0⟩
def CB1_2_5I1R15Mass : Ball := ⟨0, 0⟩
def CB1_2_5I1R15MassTerm : Ball := .exact 0
def CB1_2_5I1R15H : Ball := ⟨0, 0⟩
def CB1_2_5I1R16Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 1 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 1) a : ℝ)) 16 a
def CB1_2_5I1R16Entropy : Ball := ⟨0, 0⟩
def CB1_2_5I1R16Mass : Ball := ⟨0, 0⟩
def CB1_2_5I1R16MassTerm : Ball := .exact 0
def CB1_2_5I1R16H : Ball := ⟨0, 0⟩
def CB1_2_5I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CB1_2_5I1R0H
  | 1 => CB1_2_5I1R1H
  | 2 => CB1_2_5I1R2H
  | 3 => CB1_2_5I1R3H
  | 4 => CB1_2_5I1R4H
  | 5 => CB1_2_5I1R5H
  | 6 => CB1_2_5I1R6H
  | 7 => CB1_2_5I1R7H
  | 8 => CB1_2_5I1R8H
  | 9 => CB1_2_5I1R9H
  | 10 => CB1_2_5I1R10H
  | 11 => CB1_2_5I1R11H
  | 12 => CB1_2_5I1R12H
  | 13 => CB1_2_5I1R13H
  | 14 => CB1_2_5I1R14H
  | 15 => CB1_2_5I1R15H
  | 16 => CB1_2_5I1R16H
  | _ => (.exact 0)
def CB1_2_5I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | _, _, _ => (.exact 0)
def CB1_2_5I1Singleton : Ball := ⟨0, 0⟩
def CB1_2_5I1Group : Ball := ⟨(5835161981670172674580579985131 / 100000000000000000000000000000000), (58391139901 / 50000000000000000000000000000000)⟩

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
def CB1_2_5I1H : Ball := ⟨(18194058834292852529515035073069 / 20000000000000000000000000000000), (78706925287 / 25000000000000000000000000000000)⟩

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
def CB1_2_5I2PairEntropy : Ball := ⟨(42875906267882254072548923946733 / 50000000000000000000000000000000), (33407030893 / 50000000000000000000000000000000)⟩
def CB1_2_5I2PairMass : Ball := ⟨1, (13 / 12500000000000000000000000000000)⟩
def CB1_2_5I2PairMassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB1_2_5I2PairMassTermLog : Ball := ⟨0, (10587911893 / 50000000000000000000000000000000)⟩
def CB1_2_5I2PairMassTerm : Ball := ⟨0, (21175823787 / 100000000000000000000000000000000)⟩
def CB1_2_5I2PairH : Ball := ⟨(42875906267882254072548923946733 / 50000000000000000000000000000000), (87989885573 / 100000000000000000000000000000000)⟩

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
def CB1_2_5I2R0Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) 0 a
def CB1_2_5I2R0Entropy : Ball := ⟨0, 0⟩
def CB1_2_5I2R0Mass : Ball := ⟨0, 0⟩
def CB1_2_5I2R0MassTerm : Ball := .exact 0
def CB1_2_5I2R0H : Ball := ⟨0, 0⟩
def CB1_2_5I2R1Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) 1 a
def CB1_2_5I2R1Entropy : Ball := ⟨(104823217663759354529068898563 / 20000000000000000000000000000000), (36845039 / 20000000000000000000000000000000)⟩
def CB1_2_5I2R1Mass : Ball := ⟨(36249118515191988245121850051 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def CB1_2_5I2R1MassTermLogWitness : LogWitness := ⟨-11, 36249118515191988245121850051, 24414062500000000000000000000⟩
def CB1_2_5I2R1MassTermLog : Ball := ⟨(-180734080505688700582649404519601 / 25000000000000000000000000000000), (10164395423 / 4000000000000000000000000000000)⟩
def CB1_2_5I2R1MassTerm : Ball := ⟨(104823217663759354529068898563 / 20000000000000000000000000000000), (36845039 / 20000000000000000000000000000000)⟩
def CB1_2_5I2R1H : Ball := ⟨0, (36845039 / 10000000000000000000000000000000)⟩
def CB1_2_5I2R2Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) 2 a
def CB1_2_5I2R2Entropy : Ball := ⟨(7284663137258594485497802035789 / 20000000000000000000000000000000), (10079080399 / 50000000000000000000000000000000)⟩
def CB1_2_5I2R2Mass : Ball := ⟨(396642594740867223667445521291 / 1250000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩
def CB1_2_5I2R2MassTermLogWitness : LogWitness := ⟨-2, 396642594740867223667445521291, 312500000000000000000000000000⟩
def CB1_2_5I2R2MassTermLog : Ball := ⟨(-114786322022754802330597789937667 / 100000000000000000000000000000000), (63527471099 / 100000000000000000000000000000000)⟩
def CB1_2_5I2R2MassTerm : Ball := ⟨(7284663137258594485497802035789 / 20000000000000000000000000000000), (10079080399 / 50000000000000000000000000000000)⟩
def CB1_2_5I2R2H : Ball := ⟨0, (10079080399 / 25000000000000000000000000000000)⟩
def CB1_2_5I2R3Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) 3 a
def CB1_2_5I2R3Entropy : Ball := ⟨0, 0⟩
def CB1_2_5I2R3Mass : Ball := ⟨0, 0⟩
def CB1_2_5I2R3MassTerm : Ball := .exact 0
def CB1_2_5I2R3H : Ball := ⟨0, 0⟩
def CB1_2_5I2R4Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) 4 a
def CB1_2_5I2R4Entropy : Ball := ⟨0, 0⟩
def CB1_2_5I2R4Mass : Ball := ⟨0, 0⟩
def CB1_2_5I2R4MassTerm : Ball := .exact 0
def CB1_2_5I2R4H : Ball := ⟨0, 0⟩
def CB1_2_5I2R5Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) 5 a
def CB1_2_5I2R5Entropy : Ball := ⟨0, 0⟩
def CB1_2_5I2R5Mass : Ball := ⟨0, 0⟩
def CB1_2_5I2R5MassTerm : Ball := .exact 0
def CB1_2_5I2R5H : Ball := ⟨0, 0⟩
def CB1_2_5I2R6Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) 6 a
def CB1_2_5I2R6Entropy : Ball := ⟨0, 0⟩
def CB1_2_5I2R6Mass : Ball := ⟨0, 0⟩
def CB1_2_5I2R6MassTerm : Ball := .exact 0
def CB1_2_5I2R6H : Ball := ⟨0, 0⟩
def CB1_2_5I2R7Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) 7 a
def CB1_2_5I2R7Entropy : Ball := ⟨0, 0⟩
def CB1_2_5I2R7Mass : Ball := ⟨0, 0⟩
def CB1_2_5I2R7MassTerm : Ball := .exact 0
def CB1_2_5I2R7H : Ball := ⟨0, 0⟩
def CB1_2_5I2R8Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) 8 a
def CB1_2_5I2R8Entropy : Ball := ⟨0, 0⟩
def CB1_2_5I2R8Mass : Ball := ⟨0, 0⟩
def CB1_2_5I2R8MassTerm : Ball := .exact 0
def CB1_2_5I2R8H : Ball := ⟨0, 0⟩
def CB1_2_5I2R9Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) 9 a
def CB1_2_5I2R9Entropy : Ball := ⟨0, 0⟩
def CB1_2_5I2R9Mass : Ball := ⟨0, 0⟩
def CB1_2_5I2R9MassTerm : Ball := .exact 0
def CB1_2_5I2R9H : Ball := ⟨0, 0⟩
def CB1_2_5I2R10Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) 10 a
def CB1_2_5I2R10Entropy : Ball := ⟨0, 0⟩
def CB1_2_5I2R10Mass : Ball := ⟨0, 0⟩
def CB1_2_5I2R10MassTerm : Ball := .exact 0
def CB1_2_5I2R10H : Ball := ⟨0, 0⟩
def CB1_2_5I2R11Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) 11 a
def CB1_2_5I2R11Entropy : Ball := ⟨0, 0⟩
def CB1_2_5I2R11Mass : Ball := ⟨0, 0⟩
def CB1_2_5I2R11MassTerm : Ball := .exact 0
def CB1_2_5I2R11H : Ball := ⟨0, 0⟩
def CB1_2_5I2R12Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) 12 a
def CB1_2_5I2R12Entropy : Ball := ⟨0, 0⟩
def CB1_2_5I2R12Mass : Ball := ⟨0, 0⟩
def CB1_2_5I2R12MassTerm : Ball := .exact 0
def CB1_2_5I2R12H : Ball := ⟨0, 0⟩
def CB1_2_5I2R13Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) 13 a
def CB1_2_5I2R13Entropy : Ball := ⟨0, 0⟩
def CB1_2_5I2R13Mass : Ball := ⟨0, 0⟩
def CB1_2_5I2R13MassTerm : Ball := .exact 0
def CB1_2_5I2R13H : Ball := ⟨0, 0⟩
def CB1_2_5I2R14Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) 14 a
def CB1_2_5I2R14Entropy : Ball := ⟨0, 0⟩
def CB1_2_5I2R14Mass : Ball := ⟨0, 0⟩
def CB1_2_5I2R14MassTerm : Ball := .exact 0
def CB1_2_5I2R14H : Ball := ⟨0, 0⟩
def CB1_2_5I2R15Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) 15 a
def CB1_2_5I2R15Entropy : Ball := ⟨0, 0⟩
def CB1_2_5I2R15Mass : Ball := ⟨0, 0⟩
def CB1_2_5I2R15MassTerm : Ball := .exact 0
def CB1_2_5I2R15H : Ball := ⟨0, 0⟩
def CB1_2_5I2R16Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) 16 a
def CB1_2_5I2R16Entropy : Ball := ⟨0, 0⟩
def CB1_2_5I2R16Mass : Ball := ⟨0, 0⟩
def CB1_2_5I2R16MassTerm : Ball := .exact 0
def CB1_2_5I2R16H : Ball := ⟨0, 0⟩
def CB1_2_5I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CB1_2_5I2R0H
  | 1 => CB1_2_5I2R1H
  | 2 => CB1_2_5I2R2H
  | 3 => CB1_2_5I2R3H
  | 4 => CB1_2_5I2R4H
  | 5 => CB1_2_5I2R5H
  | 6 => CB1_2_5I2R6H
  | 7 => CB1_2_5I2R7H
  | 8 => CB1_2_5I2R8H
  | 9 => CB1_2_5I2R9H
  | 10 => CB1_2_5I2R10H
  | 11 => CB1_2_5I2R11H
  | 12 => CB1_2_5I2R12H
  | 13 => CB1_2_5I2R13H
  | 14 => CB1_2_5I2R14H
  | 15 => CB1_2_5I2R15H
  | 16 => CB1_2_5I2R16H
  | _ => (.exact 0)
def CB1_2_5I2S0_0_4Value (a : Fin 6) : ℝ := (littleLaw (shape 1 2 5) (shape 0 0 4) ((stageBPriority (shape 1 2 5)) 2) a : ℝ)
def CB1_2_5I2S0_0_4E_5Log : Ball := .exact 0
def CB1_2_5I2S0_0_4E_5 : Ball := ⟨0, 0⟩
def CB1_2_5I2S0_0_4Terms (a : Fin 6) : Ball :=
  match a.val with
  | 5 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB1_2_5I2S0_0_4Entropy : Ball := ⟨0, 0⟩
def CB1_2_5I2S0_0_4Mass : Ball := ⟨1, 0⟩
def CB1_2_5I2S0_0_4MassTermLog : Ball := .exact 0
def CB1_2_5I2S0_0_4MassTerm : Ball := ⟨0, 0⟩
def CB1_2_5I2S0_0_4H : Ball := ⟨0, 0⟩
def CB1_2_5I2S0_1_3Value (a : Fin 6) : ℝ := (littleLaw (shape 1 2 5) (shape 0 1 3) ((stageBPriority (shape 1 2 5)) 2) a : ℝ)
def CB1_2_5I2S0_1_3E_4Log : Ball := .exact 0
def CB1_2_5I2S0_1_3E_4 : Ball := ⟨0, 0⟩
def CB1_2_5I2S0_1_3Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB1_2_5I2S0_1_3Entropy : Ball := ⟨0, 0⟩
def CB1_2_5I2S0_1_3Mass : Ball := ⟨1, 0⟩
def CB1_2_5I2S0_1_3MassTermLog : Ball := .exact 0
def CB1_2_5I2S0_1_3MassTerm : Ball := ⟨0, 0⟩
def CB1_2_5I2S0_1_3H : Ball := ⟨0, 0⟩
def CB1_2_5I2S0_2_2Value (a : Fin 6) : ℝ := (littleLaw (shape 1 2 5) (shape 0 2 2) ((stageBPriority (shape 1 2 5)) 2) a : ℝ)
def CB1_2_5I2S0_2_2E_2LogWitness : LogWitness := ⟨-1, 180469, 100000⟩
def CB1_2_5I2S0_2_2E_2Log : Ball := ⟨(-2568958716933578869052947578733 / 25000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def CB1_2_5I2S0_2_2E_2 : Ball := ⟨(9272348213725720898382327931727 / 100000000000000000000000000000000), (38215797243 / 100000000000000000000000000000000)⟩
def CB1_2_5I2S0_2_2E_3LogWitness : LogWitness := ⟨-4, 19531, 12500⟩
def CB1_2_5I2S0_2_2E_3Log : Ball := ⟨(-232631441969328242519371516318041 / 100000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
def CB1_2_5I2S0_2_2E_3 : Ball := ⟨(11358811732757374761614612713019 / 50000000000000000000000000000000), (1033962531 / 10000000000000000000000000000000)⟩
def CB1_2_5I2S0_2_2Terms (a : Fin 6) : Ball :=
  match a.val with
  | 2 => ⟨(9272348213725720898382327931727 / 100000000000000000000000000000000), (38215797243 / 100000000000000000000000000000000)⟩
  | 3 => ⟨(11358811732757374761614612713019 / 50000000000000000000000000000000), (1033962531 / 10000000000000000000000000000000)⟩
  | _ => (.exact 0)
def CB1_2_5I2S0_2_2Entropy : Ball := ⟨(6397994335848094084322310671553 / 20000000000000000000000000000000), (48555422553 / 100000000000000000000000000000000)⟩
def CB1_2_5I2S0_2_2Mass : Ball := ⟨1, 0⟩
def CB1_2_5I2S0_2_2MassTermLog : Ball := .exact 0
def CB1_2_5I2S0_2_2MassTerm : Ball := ⟨0, 0⟩
def CB1_2_5I2S0_2_2H : Ball := ⟨(6397994335848094084322310671553 / 20000000000000000000000000000000), (48555422553 / 100000000000000000000000000000000)⟩
def CB1_2_5I2S1_0_3Value (a : Fin 6) : ℝ := (littleLaw (shape 1 2 5) (shape 1 0 3) ((stageBPriority (shape 1 2 5)) 2) a : ℝ)
def CB1_2_5I2S1_0_3E_4Log : Ball := .exact 0
def CB1_2_5I2S1_0_3E_4 : Ball := ⟨0, 0⟩
def CB1_2_5I2S1_0_3Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB1_2_5I2S1_0_3Entropy : Ball := ⟨0, 0⟩
def CB1_2_5I2S1_0_3Mass : Ball := ⟨1, 0⟩
def CB1_2_5I2S1_0_3MassTermLog : Ball := .exact 0
def CB1_2_5I2S1_0_3MassTerm : Ball := ⟨0, 0⟩
def CB1_2_5I2S1_0_3H : Ball := ⟨0, 0⟩
def CB1_2_5I2Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => CB1_2_5I2S0_0_4H
  | 0, 1, 3 => CB1_2_5I2S0_1_3H
  | 0, 2, 2 => CB1_2_5I2S0_2_2H
  | 1, 0, 3 => CB1_2_5I2S1_0_3H
  | _, _, _ => (.exact 0)
def CB1_2_5I2Singleton : Ball := ⟨(1455231344023407159119860932703 / 25000000000000000000000000000000), (883519043 / 10000000000000000000000000000000)⟩
def CB1_2_5I2Group : Ball := ⟨(1455231344023407159119860932703 / 25000000000000000000000000000000), (3094997651 / 6250000000000000000000000000000)⟩

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
def CB1_2_5I2H : Ball := ⟨(37054980891788625436069480215921 / 50000000000000000000000000000000), (37405962081 / 20000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB1_3_4I0
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
def CB1_3_4I0Value (a : Fin 17) : ℝ := marginal (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) ((stageBPriority (shape 1 3 4)) 0) a
def CB1_3_4I0Entropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (21175823729 / 50000000000000000000000000000000)⟩
def CB1_3_4I0Mass : Ball := ⟨1, (27 / 50000000000000000000000000000000)⟩
def CB1_3_4I0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB1_3_4I0MassTermLog : Ball := ⟨0, (2646977967 / 12500000000000000000000000000000)⟩
def CB1_3_4I0MassTerm : Ball := ⟨0, (21175823737 / 100000000000000000000000000000000)⟩
def CB1_3_4I0H : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (12705494239 / 20000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB1_3_4I1
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
def CB1_3_4I1PairEntropy : Ball := ⟨(5513758257608105145450104572581 / 5000000000000000000000000000000), (35850866179 / 50000000000000000000000000000000)⟩
def CB1_3_4I1PairMass : Ball := ⟨1, (29 / 50000000000000000000000000000000)⟩
def CB1_3_4I1PairMassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB1_3_4I1PairMassTermLog : Ball := ⟨0, (1058791187 / 5000000000000000000000000000000)⟩
def CB1_3_4I1PairMassTerm : Ball := ⟨0, (21175823741 / 100000000000000000000000000000000)⟩
def CB1_3_4I1PairH : Ball := ⟨(5513758257608105145450104572581 / 5000000000000000000000000000000), (92877556099 / 100000000000000000000000000000000)⟩

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
def CB1_3_4I1R0Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 1 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 1) a : ℝ)) 0 a
def CB1_3_4I1R0Entropy : Ball := ⟨(717087504867112438922694885631 / 12500000000000000000000000000000), (2248573677 / 100000000000000000000000000000000)⟩
def CB1_3_4I1R0Mass : Ball := ⟨(132732360120937838226056869067 / 10000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def CB1_3_4I1R0MassTermLogWitness : LogWitness := ⟨-7, 132732360120937838226056869067, 78125000000000000000000000000⟩
def CB1_3_4I1R0MassTermLog : Ball := ⟨(-216100280056421786268538236371047 / 50000000000000000000000000000000), (42351647479 / 25000000000000000000000000000000)⟩
def CB1_3_4I1R0MassTerm : Ball := ⟨(717087504867112438922694885631 / 12500000000000000000000000000000), (2248573677 / 100000000000000000000000000000000)⟩
def CB1_3_4I1R0H : Ball := ⟨0, (2248573677 / 50000000000000000000000000000000)⟩
def CB1_3_4I1R1Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 1 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 1) a : ℝ)) 1 a
def CB1_3_4I1R1Entropy : Ball := ⟨(700937522751638320155014264963 / 2000000000000000000000000000000), (6184104089 / 20000000000000000000000000000000)⟩
def CB1_3_4I1R1Mass : Ball := ⟨(4867267639879062161773943130933 / 10000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
def CB1_3_4I1R1MassTermLogWitness : LogWitness := ⟨-2, 4867267639879062161773943130933, 2500000000000000000000000000000⟩
def CB1_3_4I1R1MassTermLog : Ball := ⟨(-14401047458509075034822692518743 / 20000000000000000000000000000000), (15881867773 / 25000000000000000000000000000000)⟩
def CB1_3_4I1R1MassTerm : Ball := ⟨(700937522751638320155014264963 / 2000000000000000000000000000000), (6184104089 / 20000000000000000000000000000000)⟩
def CB1_3_4I1R1H : Ball := ⟨0, (6184104089 / 10000000000000000000000000000000)⟩
def CB1_3_4I1R2Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 1 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 1) a : ℝ)) 2 a
def CB1_3_4I1R2Entropy : Ball := ⟨(24700441268572075971559743320381 / 50000000000000000000000000000000), (16801146251 / 50000000000000000000000000000000)⟩
def CB1_3_4I1R2Mass : Ball := ⟨(4867267639879062161773943130933 / 10000000000000000000000000000000), (23 / 100000000000000000000000000000000)⟩
def CB1_3_4I1R2MassTermLogWitness : LogWitness := ⟨-2, 4867267639879062161773943130933, 2500000000000000000000000000000⟩
def CB1_3_4I1R2MassTermLog : Ball := ⟨(-14401047458509075034822692518743 / 20000000000000000000000000000000), (7940933887 / 12500000000000000000000000000000)⟩
def CB1_3_4I1R2MassTerm : Ball := ⟨(700937522751638320155014264963 / 2000000000000000000000000000000), (120783283 / 390625000000000000000000000000)⟩
def CB1_3_4I1R2H : Ball := ⟨(3588501599890558983842193348153 / 25000000000000000000000000000000), (1290456259 / 2000000000000000000000000000000)⟩
def CB1_3_4I1R3Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 1 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 1) a : ℝ)) 3 a
def CB1_3_4I1R3Entropy : Ball := ⟨(2837762529623000514779049028849 / 50000000000000000000000000000000), (443488499 / 20000000000000000000000000000000)⟩
def CB1_3_4I1R3Mass : Ball := ⟨(1308946998292554555787053318931 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
def CB1_3_4I1R3MassTermLogWitness : LogWitness := ⟨-7, 1308946998292554555787053318931, 781250000000000000000000000000⟩
def CB1_3_4I1R3MassTermLog : Ball := ⟨(-433594719010731091912411543100809 / 100000000000000000000000000000000), (33881317969 / 20000000000000000000000000000000)⟩
def CB1_3_4I1R3MassTerm : Ball := ⟨(2837762529623000514779049028849 / 50000000000000000000000000000000), (443488499 / 20000000000000000000000000000000)⟩
def CB1_3_4I1R3H : Ball := ⟨0, (443488499 / 10000000000000000000000000000000)⟩
def CB1_3_4I1R4Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 1 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 1) a : ℝ)) 4 a
def CB1_3_4I1R4Entropy : Ball := ⟨0, 0⟩
def CB1_3_4I1R4Mass : Ball := ⟨0, 0⟩
def CB1_3_4I1R4MassTerm : Ball := .exact 0
def CB1_3_4I1R4H : Ball := ⟨0, 0⟩
def CB1_3_4I1R5Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 1 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 1) a : ℝ)) 5 a
def CB1_3_4I1R5Entropy : Ball := ⟨0, 0⟩
def CB1_3_4I1R5Mass : Ball := ⟨0, 0⟩
def CB1_3_4I1R5MassTerm : Ball := .exact 0
def CB1_3_4I1R5H : Ball := ⟨0, 0⟩
def CB1_3_4I1R6Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 1 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 1) a : ℝ)) 6 a
def CB1_3_4I1R6Entropy : Ball := ⟨0, 0⟩
def CB1_3_4I1R6Mass : Ball := ⟨0, 0⟩
def CB1_3_4I1R6MassTerm : Ball := .exact 0
def CB1_3_4I1R6H : Ball := ⟨0, 0⟩
def CB1_3_4I1R7Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 1 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 1) a : ℝ)) 7 a
def CB1_3_4I1R7Entropy : Ball := ⟨0, 0⟩
def CB1_3_4I1R7Mass : Ball := ⟨0, 0⟩
def CB1_3_4I1R7MassTerm : Ball := .exact 0
def CB1_3_4I1R7H : Ball := ⟨0, 0⟩
def CB1_3_4I1R8Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 1 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 1) a : ℝ)) 8 a
def CB1_3_4I1R8Entropy : Ball := ⟨0, 0⟩
def CB1_3_4I1R8Mass : Ball := ⟨0, 0⟩
def CB1_3_4I1R8MassTerm : Ball := .exact 0
def CB1_3_4I1R8H : Ball := ⟨0, 0⟩
def CB1_3_4I1R9Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 1 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 1) a : ℝ)) 9 a
def CB1_3_4I1R9Entropy : Ball := ⟨0, 0⟩
def CB1_3_4I1R9Mass : Ball := ⟨0, 0⟩
def CB1_3_4I1R9MassTerm : Ball := .exact 0
def CB1_3_4I1R9H : Ball := ⟨0, 0⟩
def CB1_3_4I1R10Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 1 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 1) a : ℝ)) 10 a
def CB1_3_4I1R10Entropy : Ball := ⟨0, 0⟩
def CB1_3_4I1R10Mass : Ball := ⟨0, 0⟩
def CB1_3_4I1R10MassTerm : Ball := .exact 0
def CB1_3_4I1R10H : Ball := ⟨0, 0⟩
def CB1_3_4I1R11Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 1 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 1) a : ℝ)) 11 a
def CB1_3_4I1R11Entropy : Ball := ⟨0, 0⟩
def CB1_3_4I1R11Mass : Ball := ⟨0, 0⟩
def CB1_3_4I1R11MassTerm : Ball := .exact 0
def CB1_3_4I1R11H : Ball := ⟨0, 0⟩
def CB1_3_4I1R12Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 1 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 1) a : ℝ)) 12 a
def CB1_3_4I1R12Entropy : Ball := ⟨0, 0⟩
def CB1_3_4I1R12Mass : Ball := ⟨0, 0⟩
def CB1_3_4I1R12MassTerm : Ball := .exact 0
def CB1_3_4I1R12H : Ball := ⟨0, 0⟩
def CB1_3_4I1R13Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 1 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 1) a : ℝ)) 13 a
def CB1_3_4I1R13Entropy : Ball := ⟨0, 0⟩
def CB1_3_4I1R13Mass : Ball := ⟨0, 0⟩
def CB1_3_4I1R13MassTerm : Ball := .exact 0
def CB1_3_4I1R13H : Ball := ⟨0, 0⟩
def CB1_3_4I1R14Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 1 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 1) a : ℝ)) 14 a
def CB1_3_4I1R14Entropy : Ball := ⟨0, 0⟩
def CB1_3_4I1R14Mass : Ball := ⟨0, 0⟩
def CB1_3_4I1R14MassTerm : Ball := .exact 0
def CB1_3_4I1R14H : Ball := ⟨0, 0⟩
def CB1_3_4I1R15Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 1 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 1) a : ℝ)) 15 a
def CB1_3_4I1R15Entropy : Ball := ⟨0, 0⟩
def CB1_3_4I1R15Mass : Ball := ⟨0, 0⟩
def CB1_3_4I1R15MassTerm : Ball := .exact 0
def CB1_3_4I1R15H : Ball := ⟨0, 0⟩
def CB1_3_4I1R16Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 1 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 1) a : ℝ)) 16 a
def CB1_3_4I1R16Entropy : Ball := ⟨0, 0⟩
def CB1_3_4I1R16Mass : Ball := ⟨0, 0⟩
def CB1_3_4I1R16MassTerm : Ball := .exact 0
def CB1_3_4I1R16H : Ball := ⟨0, 0⟩
def CB1_3_4I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CB1_3_4I1R0H
  | 1 => CB1_3_4I1R1H
  | 2 => CB1_3_4I1R2H
  | 3 => CB1_3_4I1R3H
  | 4 => CB1_3_4I1R4H
  | 5 => CB1_3_4I1R5H
  | 6 => CB1_3_4I1R6H
  | 7 => CB1_3_4I1R7H
  | 8 => CB1_3_4I1R8H
  | 9 => CB1_3_4I1R9H
  | 10 => CB1_3_4I1R10H
  | 11 => CB1_3_4I1R11H
  | 12 => CB1_3_4I1R12H
  | 13 => CB1_3_4I1R13H
  | 14 => CB1_3_4I1R14H
  | 15 => CB1_3_4I1R15H
  | 16 => CB1_3_4I1R16H
  | _ => (.exact 0)
def CB1_3_4I1S1_3_0Value (a : Fin 6) : ℝ := (littleLaw (shape 1 3 4) (shape 1 3 0) ((stageBPriority (shape 1 3 4)) 1) a : ℝ)
def CB1_3_4I1S1_3_0E_4Log : Ball := .exact 0
def CB1_3_4I1S1_3_0E_4 : Ball := ⟨0, 0⟩
def CB1_3_4I1S1_3_0Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB1_3_4I1S1_3_0Entropy : Ball := ⟨0, 0⟩
def CB1_3_4I1S1_3_0Mass : Ball := ⟨1, 0⟩
def CB1_3_4I1S1_3_0MassTermLog : Ball := .exact 0
def CB1_3_4I1S1_3_0MassTerm : Ball := ⟨0, 0⟩
def CB1_3_4I1S1_3_0H : Ball := ⟨0, 0⟩
def CB1_3_4I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 1, 3, 0 => CB1_3_4I1S1_3_0H
  | _, _, _ => (.exact 0)
def CB1_3_4I1Singleton : Ball := ⟨0, 0⟩
def CB1_3_4I1Group : Ball := ⟨(3588501599890558983842193348153 / 25000000000000000000000000000000), (16911985773 / 12500000000000000000000000000000)⟩

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
def CB1_3_4I1H : Ball := ⟨(20391788088259407759566136166599 / 25000000000000000000000000000000), (363469328467 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB1_3_4I2
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
def CB1_3_4I2PairEntropy : Ball := ⟨(42104089517135168957866229320237 / 50000000000000000000000000000000), (29258810673 / 50000000000000000000000000000000)⟩
def CB1_3_4I2PairMass : Ball := ⟨(99999999999999999999999999999999 / 100000000000000000000000000000000), (29 / 50000000000000000000000000000000)⟩
def CB1_3_4I2PairMassTermLogWitness : LogWitness := ⟨-1, 99999999999999999999999999999999, 50000000000000000000000000000000⟩
def CB1_3_4I2PairMassTermLog : Ball := ⟨0, (661744491 / 1562500000000000000000000000000)⟩
def CB1_3_4I2PairMassTerm : Ball := ⟨0, (1694065897 / 4000000000000000000000000000000)⟩
def CB1_3_4I2PairH : Ball := ⟨(42104089517135168957866229320237 / 50000000000000000000000000000000), (100869268771 / 100000000000000000000000000000000)⟩

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
def CB1_3_4I2R0Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) 0 a
def CB1_3_4I2R0Entropy : Ball := ⟨(39518182540949711406409763533 / 25000000000000000000000000000000), (54479569 / 100000000000000000000000000000000)⟩
def CB1_3_4I2R0Mass : Ball := ⟨(18376602916823826473515371739 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def CB1_3_4I2R0MassTermLogWitness : LogWitness := ⟨-13, 18376602916823826473515371739, 12207031250000000000000000000⟩
def CB1_3_4I2R0MassTermLog : Ball := ⟨(-860184719010731091912411428528721 / 100000000000000000000000000000000), (296461537003 / 100000000000000000000000000000000)⟩
def CB1_3_4I2R0MassTerm : Ball := ⟨(39518182540949711406409763533 / 25000000000000000000000000000000), (54479569 / 100000000000000000000000000000000)⟩
def CB1_3_4I2R0H : Ball := ⟨0, (54479569 / 50000000000000000000000000000000)⟩
def CB1_3_4I2R1Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) 1 a
def CB1_3_4I2R1Entropy : Ball := ⟨(4207246008919777995755135783277 / 25000000000000000000000000000000), (9484093 / 125000000000000000000000000000)⟩
def CB1_3_4I2R1Mass : Ball := ⟨(1492912089080617619303408645301 / 25000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
def CB1_3_4I2R1MassTermLogWitness : LogWitness := ⟨-5, 1492912089080617619303408645301, 781250000000000000000000000000⟩
def CB1_3_4I2R1MassTermLog : Ball := ⟨(-281814719010731091912411582144759 / 100000000000000000000000000000000), (25410988453 / 20000000000000000000000000000000)⟩
def CB1_3_4I2R1MassTerm : Ball := ⟨(4207246008919777995755135783277 / 25000000000000000000000000000000), (9484093 / 125000000000000000000000000000)⟩
def CB1_3_4I2R1H : Ball := ⟨0, (9484093 / 62500000000000000000000000000)⟩
def CB1_3_4I2R2Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) 2 a
def CB1_3_4I2R2Entropy : Ball := ⟨(36733298066748055801157160259867 / 100000000000000000000000000000000), (13612432781 / 50000000000000000000000000000000)⟩
def CB1_3_4I2R2Mass : Ball := ⟨(21350514021234075570262898364063 / 50000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
def CB1_3_4I2R2MassTermLogWitness : LogWitness := ⟨-2, 21350514021234075570262898364063, 12500000000000000000000000000000⟩
def CB1_3_4I2R2MassTermLog : Ball := ⟨(-85094719010731091912411638578429 / 100000000000000000000000000000000), (63527471079 / 100000000000000000000000000000000)⟩
def CB1_3_4I2R2MassTerm : Ball := ⟨(7267263965486352088861529489067 / 20000000000000000000000000000000), (6781720813 / 25000000000000000000000000000000)⟩
def CB1_3_4I2R2H : Ball := ⟨(99244559829073839212378203633 / 25000000000000000000000000000000), (27175874407 / 50000000000000000000000000000000)⟩
def CB1_3_4I2R3Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) 3 a
def CB1_3_4I2R3Entropy : Ball := ⟨0, 0⟩
def CB1_3_4I2R3Mass : Ball := ⟨0, 0⟩
def CB1_3_4I2R3MassTerm : Ball := .exact 0
def CB1_3_4I2R3H : Ball := ⟨0, 0⟩
def CB1_3_4I2R4Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) 4 a
def CB1_3_4I2R4Entropy : Ball := ⟨0, 0⟩
def CB1_3_4I2R4Mass : Ball := ⟨0, 0⟩
def CB1_3_4I2R4MassTerm : Ball := .exact 0
def CB1_3_4I2R4H : Ball := ⟨0, 0⟩
def CB1_3_4I2R5Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) 5 a
def CB1_3_4I2R5Entropy : Ball := ⟨0, 0⟩
def CB1_3_4I2R5Mass : Ball := ⟨0, 0⟩
def CB1_3_4I2R5MassTerm : Ball := .exact 0
def CB1_3_4I2R5H : Ball := ⟨0, 0⟩
def CB1_3_4I2R6Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) 6 a
def CB1_3_4I2R6Entropy : Ball := ⟨0, 0⟩
def CB1_3_4I2R6Mass : Ball := ⟨0, 0⟩
def CB1_3_4I2R6MassTerm : Ball := .exact 0
def CB1_3_4I2R6H : Ball := ⟨0, 0⟩
def CB1_3_4I2R7Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) 7 a
def CB1_3_4I2R7Entropy : Ball := ⟨0, 0⟩
def CB1_3_4I2R7Mass : Ball := ⟨0, 0⟩
def CB1_3_4I2R7MassTerm : Ball := .exact 0
def CB1_3_4I2R7H : Ball := ⟨0, 0⟩
def CB1_3_4I2R8Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) 8 a
def CB1_3_4I2R8Entropy : Ball := ⟨0, 0⟩
def CB1_3_4I2R8Mass : Ball := ⟨0, 0⟩
def CB1_3_4I2R8MassTerm : Ball := .exact 0
def CB1_3_4I2R8H : Ball := ⟨0, 0⟩
def CB1_3_4I2R9Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) 9 a
def CB1_3_4I2R9Entropy : Ball := ⟨0, 0⟩
def CB1_3_4I2R9Mass : Ball := ⟨0, 0⟩
def CB1_3_4I2R9MassTerm : Ball := .exact 0
def CB1_3_4I2R9H : Ball := ⟨0, 0⟩
def CB1_3_4I2R10Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) 10 a
def CB1_3_4I2R10Entropy : Ball := ⟨0, 0⟩
def CB1_3_4I2R10Mass : Ball := ⟨0, 0⟩
def CB1_3_4I2R10MassTerm : Ball := .exact 0
def CB1_3_4I2R10H : Ball := ⟨0, 0⟩
def CB1_3_4I2R11Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) 11 a
def CB1_3_4I2R11Entropy : Ball := ⟨0, 0⟩
def CB1_3_4I2R11Mass : Ball := ⟨0, 0⟩
def CB1_3_4I2R11MassTerm : Ball := .exact 0
def CB1_3_4I2R11H : Ball := ⟨0, 0⟩
def CB1_3_4I2R12Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) 12 a
def CB1_3_4I2R12Entropy : Ball := ⟨0, 0⟩
def CB1_3_4I2R12Mass : Ball := ⟨0, 0⟩
def CB1_3_4I2R12MassTerm : Ball := .exact 0
def CB1_3_4I2R12H : Ball := ⟨0, 0⟩
def CB1_3_4I2R13Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) 13 a
def CB1_3_4I2R13Entropy : Ball := ⟨0, 0⟩
def CB1_3_4I2R13Mass : Ball := ⟨0, 0⟩
def CB1_3_4I2R13MassTerm : Ball := .exact 0
def CB1_3_4I2R13H : Ball := ⟨0, 0⟩
def CB1_3_4I2R14Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) 14 a
def CB1_3_4I2R14Entropy : Ball := ⟨0, 0⟩
def CB1_3_4I2R14Mass : Ball := ⟨0, 0⟩
def CB1_3_4I2R14MassTerm : Ball := .exact 0
def CB1_3_4I2R14H : Ball := ⟨0, 0⟩
def CB1_3_4I2R15Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) 15 a
def CB1_3_4I2R15Entropy : Ball := ⟨0, 0⟩
def CB1_3_4I2R15Mass : Ball := ⟨0, 0⟩
def CB1_3_4I2R15MassTerm : Ball := .exact 0
def CB1_3_4I2R15H : Ball := ⟨0, 0⟩
def CB1_3_4I2R16Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) 16 a
def CB1_3_4I2R16Entropy : Ball := ⟨0, 0⟩
def CB1_3_4I2R16Mass : Ball := ⟨0, 0⟩
def CB1_3_4I2R16MassTerm : Ball := .exact 0
def CB1_3_4I2R16H : Ball := ⟨0, 0⟩
def CB1_3_4I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CB1_3_4I2R0H
  | 1 => CB1_3_4I2R1H
  | 2 => CB1_3_4I2R2H
  | 3 => CB1_3_4I2R3H
  | 4 => CB1_3_4I2R4H
  | 5 => CB1_3_4I2R5H
  | 6 => CB1_3_4I2R6H
  | 7 => CB1_3_4I2R7H
  | 8 => CB1_3_4I2R8H
  | 9 => CB1_3_4I2R9H
  | 10 => CB1_3_4I2R10H
  | 11 => CB1_3_4I2R11H
  | 12 => CB1_3_4I2R12H
  | 13 => CB1_3_4I2R13H
  | 14 => CB1_3_4I2R14H
  | 15 => CB1_3_4I2R15H
  | 16 => CB1_3_4I2R16H
  | _ => (.exact 0)
def CB1_3_4I2S0_0_4Value (a : Fin 6) : ℝ := (littleLaw (shape 1 3 4) (shape 0 0 4) ((stageBPriority (shape 1 3 4)) 2) a : ℝ)
def CB1_3_4I2S0_0_4E_5Log : Ball := .exact 0
def CB1_3_4I2S0_0_4E_5 : Ball := ⟨0, 0⟩
def CB1_3_4I2S0_0_4Terms (a : Fin 6) : Ball :=
  match a.val with
  | 5 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB1_3_4I2S0_0_4Entropy : Ball := ⟨0, 0⟩
def CB1_3_4I2S0_0_4Mass : Ball := ⟨1, 0⟩
def CB1_3_4I2S0_0_4MassTermLog : Ball := .exact 0
def CB1_3_4I2S0_0_4MassTerm : Ball := ⟨0, 0⟩
def CB1_3_4I2S0_0_4H : Ball := ⟨0, 0⟩
def CB1_3_4I2S0_1_3Value (a : Fin 6) : ℝ := (littleLaw (shape 1 3 4) (shape 0 1 3) ((stageBPriority (shape 1 3 4)) 2) a : ℝ)
def CB1_3_4I2S0_1_3E_4Log : Ball := .exact 0
def CB1_3_4I2S0_1_3E_4 : Ball := ⟨0, 0⟩
def CB1_3_4I2S0_1_3Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB1_3_4I2S0_1_3Entropy : Ball := ⟨0, 0⟩
def CB1_3_4I2S0_1_3Mass : Ball := ⟨1, 0⟩
def CB1_3_4I2S0_1_3MassTermLog : Ball := .exact 0
def CB1_3_4I2S0_1_3MassTerm : Ball := ⟨0, 0⟩
def CB1_3_4I2S0_1_3H : Ball := ⟨0, 0⟩
def CB1_3_4I2S0_2_2Value (a : Fin 6) : ℝ := (littleLaw (shape 1 3 4) (shape 0 2 2) ((stageBPriority (shape 1 3 4)) 2) a : ℝ)
def CB1_3_4I2S0_2_2E_2LogWitness : LogWitness := ⟨-1, 453517, 250000⟩
def CB1_3_4I2S0_2_2E_2Log : Ball := ⟨(-609845895945556733363202867553 / 6250000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def CB1_3_4I2S0_2_2E_2 : Ball := ⟨(8850415398129313697429749596289 / 100000000000000000000000000000000), (19207192059 / 50000000000000000000000000000000)⟩
def CB1_3_4I2S0_2_2E_3LogWitness : LogWitness := ⟨-4, 46483, 31250⟩
def CB1_3_4I2S0_2_2E_3Log : Ball := ⟨(-59388036101788952339754245697507 / 25000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
def CB1_3_4I2S0_2_2E_3 : Ball := ⟨(11042136328477823486435186411029 / 50000000000000000000000000000000), (9843158123 / 100000000000000000000000000000000)⟩
def CB1_3_4I2S0_2_2Terms (a : Fin 6) : Ball :=
  match a.val with
  | 2 => ⟨(8850415398129313697429749596289 / 100000000000000000000000000000000), (19207192059 / 50000000000000000000000000000000)⟩
  | 3 => ⟨(11042136328477823486435186411029 / 50000000000000000000000000000000), (9843158123 / 100000000000000000000000000000000)⟩
  | _ => (.exact 0)
def CB1_3_4I2S0_2_2Entropy : Ball := ⟨(30934688055084960670300122418347 / 100000000000000000000000000000000), (48257542241 / 100000000000000000000000000000000)⟩
def CB1_3_4I2S0_2_2Mass : Ball := ⟨1, 0⟩
def CB1_3_4I2S0_2_2MassTermLog : Ball := .exact 0
def CB1_3_4I2S0_2_2MassTerm : Ball := ⟨0, 0⟩
def CB1_3_4I2S0_2_2H : Ball := ⟨(30934688055084960670300122418347 / 100000000000000000000000000000000), (48257542241 / 100000000000000000000000000000000)⟩
def CB1_3_4I2S0_3_1Value (a : Fin 6) : ℝ := (littleLaw (shape 1 3 4) (shape 0 3 1) ((stageBPriority (shape 1 3 4)) 2) a : ℝ)
def CB1_3_4I2S0_3_1E_1Log : Ball := .exact 0
def CB1_3_4I2S0_3_1E_1 : Ball := ⟨0, 0⟩
def CB1_3_4I2S0_3_1Terms (a : Fin 6) : Ball :=
  match a.val with
  | 1 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB1_3_4I2S0_3_1Entropy : Ball := ⟨0, 0⟩
def CB1_3_4I2S0_3_1Mass : Ball := ⟨1, 0⟩
def CB1_3_4I2S0_3_1MassTermLog : Ball := .exact 0
def CB1_3_4I2S0_3_1MassTerm : Ball := ⟨0, 0⟩
def CB1_3_4I2S0_3_1H : Ball := ⟨0, 0⟩
def CB1_3_4I2S1_0_3Value (a : Fin 6) : ℝ := (littleLaw (shape 1 3 4) (shape 1 0 3) ((stageBPriority (shape 1 3 4)) 2) a : ℝ)
def CB1_3_4I2S1_0_3E_4Log : Ball := .exact 0
def CB1_3_4I2S1_0_3E_4 : Ball := ⟨0, 0⟩
def CB1_3_4I2S1_0_3Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB1_3_4I2S1_0_3Entropy : Ball := ⟨0, 0⟩
def CB1_3_4I2S1_0_3Mass : Ball := ⟨1, 0⟩
def CB1_3_4I2S1_0_3MassTermLog : Ball := .exact 0
def CB1_3_4I2S1_0_3MassTerm : Ball := ⟨0, 0⟩
def CB1_3_4I2S1_0_3H : Ball := ⟨0, 0⟩
def CB1_3_4I2Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => CB1_3_4I2S0_0_4H
  | 0, 1, 3 => CB1_3_4I2S0_1_3H
  | 0, 2, 2 => CB1_3_4I2S0_2_2H
  | 0, 3, 1 => CB1_3_4I2S0_3_1H
  | 1, 0, 3 => CB1_3_4I2S1_0_3H
  | _, _, _ => (.exact 0)
def CB1_3_4I2Singleton : Ball := ⟨(2641885964250374911539500817683 / 20000000000000000000000000000000), (20606466649 / 100000000000000000000000000000000)⟩
def CB1_3_4I2Group : Ball := ⟨(13606408060568169914547016902947 / 100000000000000000000000000000000), (90241723401 / 100000000000000000000000000000000)⟩

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
def CB1_3_4I2H : Ball := ⟨(2849768145656699904331921241729 / 5000000000000000000000000000000), (281352715573 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB1_4_3I0
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
def CB1_4_3I0Value (a : Fin 17) : ℝ := marginal (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) ((stageBPriority (shape 1 4 3)) 0) a
def CB1_4_3I0Entropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (21175823729 / 50000000000000000000000000000000)⟩
def CB1_4_3I0Mass : Ball := ⟨1, (27 / 50000000000000000000000000000000)⟩
def CB1_4_3I0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB1_4_3I0MassTermLog : Ball := ⟨0, (2646977967 / 12500000000000000000000000000000)⟩
def CB1_4_3I0MassTerm : Ball := ⟨0, (21175823737 / 100000000000000000000000000000000)⟩
def CB1_4_3I0H : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (12705494239 / 20000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB1_4_3I1
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
def CB1_4_3I1PairEntropy : Ball := ⟨(55245686803749918217598858537289 / 50000000000000000000000000000000), (17938935117 / 25000000000000000000000000000000)⟩
def CB1_4_3I1PairMass : Ball := ⟨1, (7 / 12500000000000000000000000000000)⟩
def CB1_4_3I1PairMassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB1_4_3I1PairMassTermLog : Ball := ⟨0, (10587911869 / 50000000000000000000000000000000)⟩
def CB1_4_3I1PairMassTerm : Ball := ⟨0, (21175823739 / 100000000000000000000000000000000)⟩
def CB1_4_3I1PairH : Ball := ⟨(55245686803749918217598858537289 / 50000000000000000000000000000000), (92931564207 / 100000000000000000000000000000000)⟩

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
def CB1_4_3I1R0Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 1 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 1) a : ℝ)) 0 a
def CB1_4_3I1R0Entropy : Ball := ⟨(2832103256882534265290777128763 / 50000000000000000000000000000000), (2211696927 / 100000000000000000000000000000000)⟩
def CB1_4_3I1R0Mass : Ball := ⟨(1305555413502823769500199931759 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
def CB1_4_3I1R0MassTermLogWitness : LogWitness := ⟨-7, 1305555413502823769500199931759, 781250000000000000000000000000⟩
def CB1_4_3I1R0MassTermLog : Ball := ⟨(-216927081577024822663609695696999 / 50000000000000000000000000000000), (84703294923 / 50000000000000000000000000000000)⟩
def CB1_4_3I1R0MassTerm : Ball := ⟨(2832103256882534265290777128763 / 50000000000000000000000000000000), (2211696927 / 100000000000000000000000000000000)⟩
def CB1_4_3I1R0H : Ball := ⟨0, (2211696927 / 50000000000000000000000000000000)⟩
def CB1_4_3I1R1Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 1 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 1) a : ℝ)) 1 a
def CB1_4_3I1R1Entropy : Ball := ⟨(35040777318051406005918583475043 / 100000000000000000000000000000000), (15467174613 / 50000000000000000000000000000000)⟩
def CB1_4_3I1R1Mass : Ball := ⟨(48694444586497176230499800068241 / 100000000000000000000000000000000), (11 / 50000000000000000000000000000000)⟩
def CB1_4_3I1R1MassTermLogWitness : LogWitness := ⟨-2, 48694444586497176230499800068241, 25000000000000000000000000000000⟩
def CB1_4_3I1R1MassTermLog : Ball := ⟨(-71960523660574021003240660753221 / 100000000000000000000000000000000), (31763735547 / 50000000000000000000000000000000)⟩
def CB1_4_3I1R1MassTerm : Ball := ⟨(35040777318051406005918583475043 / 100000000000000000000000000000000), (15467174613 / 50000000000000000000000000000000)⟩
def CB1_4_3I1R1H : Ball := ⟨0, (15467174613 / 25000000000000000000000000000000)⟩
def CB1_4_3I1R2Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 1 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 1) a : ℝ)) 2 a
def CB1_4_3I1R2Entropy : Ball := ⟨(49581480289984849687017304279763 / 100000000000000000000000000000000), (33666173307 / 100000000000000000000000000000000)⟩
def CB1_4_3I1R2Mass : Ball := ⟨(48694444586497176230499800068241 / 100000000000000000000000000000000), (23 / 100000000000000000000000000000000)⟩
def CB1_4_3I1R2MassTermLogWitness : LogWitness := ⟨-2, 48694444586497176230499800068241, 25000000000000000000000000000000⟩
def CB1_4_3I1R2MassTermLog : Ball := ⟨(-71960523660574021003240660753221 / 100000000000000000000000000000000), (7940933887 / 12500000000000000000000000000000)⟩
def CB1_4_3I1R2MassTerm : Ball := ⟨(35040777318051406005918583475043 / 100000000000000000000000000000000), (30934349227 / 100000000000000000000000000000000)⟩
def CB1_4_3I1R2H : Ball := ⟨(181758787149168046013734010059 / 1250000000000000000000000000000), (32300261267 / 50000000000000000000000000000000)⟩
def CB1_4_3I1R3Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 1 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 1) a : ℝ)) 3 a
def CB1_4_3I1R3Entropy : Ball := ⟨(2776018400687065419939160153901 / 50000000000000000000000000000000), (13468741 / 625000000000000000000000000000)⟩
def CB1_4_3I1R3Mass : Ball := ⟨(636043303940678115759208606101 / 50000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
def CB1_4_3I1R3MassTermLogWitness : LogWitness := ⟨-7, 636043303940678115759208606101, 390625000000000000000000000000⟩
def CB1_4_3I1R3MassTermLog : Ball := ⟨(-218225581771549981913164283923513 / 50000000000000000000000000000000), (84703294889 / 50000000000000000000000000000000)⟩
def CB1_4_3I1R3MassTerm : Ball := ⟨(2776018400687065419939160153901 / 50000000000000000000000000000000), (13468741 / 625000000000000000000000000000)⟩
def CB1_4_3I1R3H : Ball := ⟨0, (13468741 / 312500000000000000000000000000)⟩
def CB1_4_3I1R4Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 1 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 1) a : ℝ)) 4 a
def CB1_4_3I1R4Entropy : Ball := ⟨0, 0⟩
def CB1_4_3I1R4Mass : Ball := ⟨0, 0⟩
def CB1_4_3I1R4MassTerm : Ball := .exact 0
def CB1_4_3I1R4H : Ball := ⟨0, 0⟩
def CB1_4_3I1R5Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 1 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 1) a : ℝ)) 5 a
def CB1_4_3I1R5Entropy : Ball := ⟨0, 0⟩
def CB1_4_3I1R5Mass : Ball := ⟨0, 0⟩
def CB1_4_3I1R5MassTerm : Ball := .exact 0
def CB1_4_3I1R5H : Ball := ⟨0, 0⟩
def CB1_4_3I1R6Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 1 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 1) a : ℝ)) 6 a
def CB1_4_3I1R6Entropy : Ball := ⟨0, 0⟩
def CB1_4_3I1R6Mass : Ball := ⟨0, 0⟩
def CB1_4_3I1R6MassTerm : Ball := .exact 0
def CB1_4_3I1R6H : Ball := ⟨0, 0⟩
def CB1_4_3I1R7Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 1 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 1) a : ℝ)) 7 a
def CB1_4_3I1R7Entropy : Ball := ⟨0, 0⟩
def CB1_4_3I1R7Mass : Ball := ⟨0, 0⟩
def CB1_4_3I1R7MassTerm : Ball := .exact 0
def CB1_4_3I1R7H : Ball := ⟨0, 0⟩
def CB1_4_3I1R8Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 1 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 1) a : ℝ)) 8 a
def CB1_4_3I1R8Entropy : Ball := ⟨0, 0⟩
def CB1_4_3I1R8Mass : Ball := ⟨0, 0⟩
def CB1_4_3I1R8MassTerm : Ball := .exact 0
def CB1_4_3I1R8H : Ball := ⟨0, 0⟩
def CB1_4_3I1R9Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 1 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 1) a : ℝ)) 9 a
def CB1_4_3I1R9Entropy : Ball := ⟨0, 0⟩
def CB1_4_3I1R9Mass : Ball := ⟨0, 0⟩
def CB1_4_3I1R9MassTerm : Ball := .exact 0
def CB1_4_3I1R9H : Ball := ⟨0, 0⟩
def CB1_4_3I1R10Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 1 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 1) a : ℝ)) 10 a
def CB1_4_3I1R10Entropy : Ball := ⟨0, 0⟩
def CB1_4_3I1R10Mass : Ball := ⟨0, 0⟩
def CB1_4_3I1R10MassTerm : Ball := .exact 0
def CB1_4_3I1R10H : Ball := ⟨0, 0⟩
def CB1_4_3I1R11Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 1 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 1) a : ℝ)) 11 a
def CB1_4_3I1R11Entropy : Ball := ⟨0, 0⟩
def CB1_4_3I1R11Mass : Ball := ⟨0, 0⟩
def CB1_4_3I1R11MassTerm : Ball := .exact 0
def CB1_4_3I1R11H : Ball := ⟨0, 0⟩
def CB1_4_3I1R12Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 1 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 1) a : ℝ)) 12 a
def CB1_4_3I1R12Entropy : Ball := ⟨0, 0⟩
def CB1_4_3I1R12Mass : Ball := ⟨0, 0⟩
def CB1_4_3I1R12MassTerm : Ball := .exact 0
def CB1_4_3I1R12H : Ball := ⟨0, 0⟩
def CB1_4_3I1R13Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 1 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 1) a : ℝ)) 13 a
def CB1_4_3I1R13Entropy : Ball := ⟨0, 0⟩
def CB1_4_3I1R13Mass : Ball := ⟨0, 0⟩
def CB1_4_3I1R13MassTerm : Ball := .exact 0
def CB1_4_3I1R13H : Ball := ⟨0, 0⟩
def CB1_4_3I1R14Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 1 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 1) a : ℝ)) 14 a
def CB1_4_3I1R14Entropy : Ball := ⟨0, 0⟩
def CB1_4_3I1R14Mass : Ball := ⟨0, 0⟩
def CB1_4_3I1R14MassTerm : Ball := .exact 0
def CB1_4_3I1R14H : Ball := ⟨0, 0⟩
def CB1_4_3I1R15Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 1 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 1) a : ℝ)) 15 a
def CB1_4_3I1R15Entropy : Ball := ⟨0, 0⟩
def CB1_4_3I1R15Mass : Ball := ⟨0, 0⟩
def CB1_4_3I1R15MassTerm : Ball := .exact 0
def CB1_4_3I1R15H : Ball := ⟨0, 0⟩
def CB1_4_3I1R16Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 1 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 1) a : ℝ)) 16 a
def CB1_4_3I1R16Entropy : Ball := ⟨0, 0⟩
def CB1_4_3I1R16Mass : Ball := ⟨0, 0⟩
def CB1_4_3I1R16MassTerm : Ball := .exact 0
def CB1_4_3I1R16H : Ball := ⟨0, 0⟩
def CB1_4_3I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CB1_4_3I1R0H
  | 1 => CB1_4_3I1R1H
  | 2 => CB1_4_3I1R2H
  | 3 => CB1_4_3I1R3H
  | 4 => CB1_4_3I1R4H
  | 5 => CB1_4_3I1R5H
  | 6 => CB1_4_3I1R6H
  | 7 => CB1_4_3I1R7H
  | 8 => CB1_4_3I1R8H
  | 9 => CB1_4_3I1R9H
  | 10 => CB1_4_3I1R10H
  | 11 => CB1_4_3I1R11H
  | 12 => CB1_4_3I1R12H
  | 13 => CB1_4_3I1R13H
  | 14 => CB1_4_3I1R14H
  | 15 => CB1_4_3I1R15H
  | 16 => CB1_4_3I1R16H
  | _ => (.exact 0)
def CB1_4_3I1S1_0_3Value (a : Fin 6) : ℝ := (littleLaw (shape 1 4 3) (shape 1 0 3) ((stageBPriority (shape 1 4 3)) 1) a : ℝ)
def CB1_4_3I1S1_0_3E_4Log : Ball := .exact 0
def CB1_4_3I1S1_0_3E_4 : Ball := ⟨0, 0⟩
def CB1_4_3I1S1_0_3Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB1_4_3I1S1_0_3Entropy : Ball := ⟨0, 0⟩
def CB1_4_3I1S1_0_3Mass : Ball := ⟨1, 0⟩
def CB1_4_3I1S1_0_3MassTermLog : Ball := .exact 0
def CB1_4_3I1S1_0_3MassTerm : Ball := ⟨0, 0⟩
def CB1_4_3I1S1_0_3H : Ball := ⟨0, 0⟩
def CB1_4_3I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 1, 0, 3 => CB1_4_3I1S1_0_3H
  | _, _, _ => (.exact 0)
def CB1_4_3I1Singleton : Ball := ⟨0, 0⟩
def CB1_4_3I1Group : Ball := ⟨(181758787149168046013734010059 / 1250000000000000000000000000000), (3380065299 / 2500000000000000000000000000000)⟩

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
def CB1_4_3I1H : Ball := ⟨(40704983831816474536500137732569 / 50000000000000000000000000000000), (363336788127 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB1_4_3I2
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
def CB1_4_3I2PairEntropy : Ball := ⟨(43988529390247762599665303535651 / 50000000000000000000000000000000), (5955403551 / 10000000000000000000000000000000)⟩
def CB1_4_3I2PairMass : Ball := ⟨1, (57 / 100000000000000000000000000000000)⟩
def CB1_4_3I2PairMassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB1_4_3I2PairMassTermLog : Ball := ⟨0, (21175823739 / 100000000000000000000000000000000)⟩
def CB1_4_3I2PairMassTerm : Ball := ⟨0, (1058791187 / 5000000000000000000000000000000)⟩
def CB1_4_3I2PairH : Ball := ⟨(43988529390247762599665303535651 / 50000000000000000000000000000000), (322919437 / 400000000000000000000000000000)⟩

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
def CB1_4_3I2R0Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) 0 a
def CB1_4_3I2R0Entropy : Ball := ⟨(66956953162162032020595243473 / 25000000000000000000000000000000), (1439607 / 1562500000000000000000000000000)⟩
def CB1_4_3I2R0Mass : Ball := ⟨(33468805621467537981782719557 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def CB1_4_3I2R0MassTermLogWitness : LogWitness := ⟨-12, 33468805621467537981782719557, 24414062500000000000000000000⟩
def CB1_4_3I2R0MassTermLog : Ball := ⟨(-800231163543099963826328472368741 / 100000000000000000000000000000000), (137642855433 / 50000000000000000000000000000000)⟩
def CB1_4_3I2R0MassTerm : Ball := ⟨(66956953162162032020595243473 / 25000000000000000000000000000000), (1439607 / 1562500000000000000000000000000)⟩
def CB1_4_3I2R0H : Ball := ⟨0, (1439607 / 781250000000000000000000000000)⟩
def CB1_4_3I2R1Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) 1 a
def CB1_4_3I2R1Entropy : Ball := ⟨(17929134143311901936334016847311 / 100000000000000000000000000000000), (6981657981 / 100000000000000000000000000000000)⟩
def CB1_4_3I2R1Mass : Ball := ⟨(5275191590850223000844657229 / 80000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
def CB1_4_3I2R1MassTermLogWitness : LogWitness := ⟨-4, 5275191590850223000844657229, 5000000000000000000000000000⟩
def CB1_4_3I2R1MassTermLog : Ball := ⟨(-271901163543099963826328625133483 / 100000000000000000000000000000000), (105879118581 / 100000000000000000000000000000000)⟩
def CB1_4_3I2R1MassTerm : Ball := ⟨(17929134143311901936334016847311 / 100000000000000000000000000000000), (6981657981 / 100000000000000000000000000000000)⟩
def CB1_4_3I2R1H : Ball := ⟨0, (6981657981 / 50000000000000000000000000000000)⟩
def CB1_4_3I2R2Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) 2 a
def CB1_4_3I2R2Entropy : Ball := ⟨(37295318394695860831553311381161 / 100000000000000000000000000000000), (3370422823 / 12500000000000000000000000000000)⟩
def CB1_4_3I2R2Mass : Ball := ⟨(42100455097934397479443978531991 / 100000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
def CB1_4_3I2R2MassTermLogWitness : LogWitness := ⟨-2, 42100455097934397479443978531991, 25000000000000000000000000000000⟩
def CB1_4_3I2R2MassTermLog : Ball := ⟨(-86511163543099963826328663324499 / 100000000000000000000000000000000), (1588186777 / 2500000000000000000000000000000)⟩
def CB1_4_3I2R2MassTerm : Ball := ⟨(36421593562163392644111126100921 / 100000000000000000000000000000000), (26745354449 / 100000000000000000000000000000000)⟩
def CB1_4_3I2R2H : Ball := ⟨(10921560406655852343027316003 / 1250000000000000000000000000000), (53708737033 / 100000000000000000000000000000000)⟩
def CB1_4_3I2R3Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) 3 a
def CB1_4_3I2R3Entropy : Ball := ⟨0, 0⟩
def CB1_4_3I2R3Mass : Ball := ⟨0, 0⟩
def CB1_4_3I2R3MassTerm : Ball := .exact 0
def CB1_4_3I2R3H : Ball := ⟨0, 0⟩
def CB1_4_3I2R4Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) 4 a
def CB1_4_3I2R4Entropy : Ball := ⟨0, 0⟩
def CB1_4_3I2R4Mass : Ball := ⟨0, 0⟩
def CB1_4_3I2R4MassTerm : Ball := .exact 0
def CB1_4_3I2R4H : Ball := ⟨0, 0⟩
def CB1_4_3I2R5Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) 5 a
def CB1_4_3I2R5Entropy : Ball := ⟨0, 0⟩
def CB1_4_3I2R5Mass : Ball := ⟨0, 0⟩
def CB1_4_3I2R5MassTerm : Ball := .exact 0
def CB1_4_3I2R5H : Ball := ⟨0, 0⟩
def CB1_4_3I2R6Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) 6 a
def CB1_4_3I2R6Entropy : Ball := ⟨0, 0⟩
def CB1_4_3I2R6Mass : Ball := ⟨0, 0⟩
def CB1_4_3I2R6MassTerm : Ball := .exact 0
def CB1_4_3I2R6H : Ball := ⟨0, 0⟩
def CB1_4_3I2R7Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) 7 a
def CB1_4_3I2R7Entropy : Ball := ⟨0, 0⟩
def CB1_4_3I2R7Mass : Ball := ⟨0, 0⟩
def CB1_4_3I2R7MassTerm : Ball := .exact 0
def CB1_4_3I2R7H : Ball := ⟨0, 0⟩
def CB1_4_3I2R8Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) 8 a
def CB1_4_3I2R8Entropy : Ball := ⟨0, 0⟩
def CB1_4_3I2R8Mass : Ball := ⟨0, 0⟩
def CB1_4_3I2R8MassTerm : Ball := .exact 0
def CB1_4_3I2R8H : Ball := ⟨0, 0⟩
def CB1_4_3I2R9Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) 9 a
def CB1_4_3I2R9Entropy : Ball := ⟨0, 0⟩
def CB1_4_3I2R9Mass : Ball := ⟨0, 0⟩
def CB1_4_3I2R9MassTerm : Ball := .exact 0
def CB1_4_3I2R9H : Ball := ⟨0, 0⟩
def CB1_4_3I2R10Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) 10 a
def CB1_4_3I2R10Entropy : Ball := ⟨0, 0⟩
def CB1_4_3I2R10Mass : Ball := ⟨0, 0⟩
def CB1_4_3I2R10MassTerm : Ball := .exact 0
def CB1_4_3I2R10H : Ball := ⟨0, 0⟩
def CB1_4_3I2R11Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) 11 a
def CB1_4_3I2R11Entropy : Ball := ⟨0, 0⟩
def CB1_4_3I2R11Mass : Ball := ⟨0, 0⟩
def CB1_4_3I2R11MassTerm : Ball := .exact 0
def CB1_4_3I2R11H : Ball := ⟨0, 0⟩
def CB1_4_3I2R12Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) 12 a
def CB1_4_3I2R12Entropy : Ball := ⟨0, 0⟩
def CB1_4_3I2R12Mass : Ball := ⟨0, 0⟩
def CB1_4_3I2R12MassTerm : Ball := .exact 0
def CB1_4_3I2R12H : Ball := ⟨0, 0⟩
def CB1_4_3I2R13Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) 13 a
def CB1_4_3I2R13Entropy : Ball := ⟨0, 0⟩
def CB1_4_3I2R13Mass : Ball := ⟨0, 0⟩
def CB1_4_3I2R13MassTerm : Ball := .exact 0
def CB1_4_3I2R13H : Ball := ⟨0, 0⟩
def CB1_4_3I2R14Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) 14 a
def CB1_4_3I2R14Entropy : Ball := ⟨0, 0⟩
def CB1_4_3I2R14Mass : Ball := ⟨0, 0⟩
def CB1_4_3I2R14MassTerm : Ball := .exact 0
def CB1_4_3I2R14H : Ball := ⟨0, 0⟩
def CB1_4_3I2R15Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) 15 a
def CB1_4_3I2R15Entropy : Ball := ⟨0, 0⟩
def CB1_4_3I2R15Mass : Ball := ⟨0, 0⟩
def CB1_4_3I2R15MassTerm : Ball := .exact 0
def CB1_4_3I2R15H : Ball := ⟨0, 0⟩
def CB1_4_3I2R16Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) 16 a
def CB1_4_3I2R16Entropy : Ball := ⟨0, 0⟩
def CB1_4_3I2R16Mass : Ball := ⟨0, 0⟩
def CB1_4_3I2R16MassTerm : Ball := .exact 0
def CB1_4_3I2R16H : Ball := ⟨0, 0⟩
def CB1_4_3I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CB1_4_3I2R0H
  | 1 => CB1_4_3I2R1H
  | 2 => CB1_4_3I2R2H
  | 3 => CB1_4_3I2R3H
  | 4 => CB1_4_3I2R4H
  | 5 => CB1_4_3I2R5H
  | 6 => CB1_4_3I2R6H
  | 7 => CB1_4_3I2R7H
  | 8 => CB1_4_3I2R8H
  | 9 => CB1_4_3I2R9H
  | 10 => CB1_4_3I2R10H
  | 11 => CB1_4_3I2R11H
  | 12 => CB1_4_3I2R12H
  | 13 => CB1_4_3I2R13H
  | 14 => CB1_4_3I2R14H
  | 15 => CB1_4_3I2R15H
  | 16 => CB1_4_3I2R16H
  | _ => (.exact 0)
def CB1_4_3I2S0_1_3Value (a : Fin 6) : ℝ := (littleLaw (shape 1 4 3) (shape 0 1 3) ((stageBPriority (shape 1 4 3)) 2) a : ℝ)
def CB1_4_3I2S0_1_3E_1Log : Ball := .exact 0
def CB1_4_3I2S0_1_3E_1 : Ball := ⟨0, 0⟩
def CB1_4_3I2S0_1_3Terms (a : Fin 6) : Ball :=
  match a.val with
  | 1 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB1_4_3I2S0_1_3Entropy : Ball := ⟨0, 0⟩
def CB1_4_3I2S0_1_3Mass : Ball := ⟨1, 0⟩
def CB1_4_3I2S0_1_3MassTermLog : Ball := .exact 0
def CB1_4_3I2S0_1_3MassTerm : Ball := ⟨0, 0⟩
def CB1_4_3I2S0_1_3H : Ball := ⟨0, 0⟩
def CB1_4_3I2S0_2_2Value (a : Fin 6) : ℝ := (littleLaw (shape 1 4 3) (shape 0 2 2) ((stageBPriority (shape 1 4 3)) 2) a : ℝ)
def CB1_4_3I2S0_2_2E_2LogWitness : LogWitness := ⟨-1, 226099, 125000⟩
def CB1_4_3I2S0_2_2E_2Log : Ball := ⟨(-2512199035246581498367078978841 / 25000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def CB1_4_3I2S0_2_2E_2 : Ball := ⟨(568005689670216830199298190037 / 6250000000000000000000000000000), (4787832559 / 12500000000000000000000000000000)⟩
def CB1_4_3I2S0_2_2E_3LogWitness : LogWitness := ⟨-4, 23901, 15625⟩
def CB1_4_3I2S0_2_2E_3Log : Ball := ⟨(-234754061879590774959727984514419 / 100000000000000000000000000000000), (52939559207 / 50000000000000000000000000000000)⟩
def CB1_4_3I2S0_2_2E_3 : Ball := ⟨(22443427331936396449249834231517 / 100000000000000000000000000000000), (5061233619 / 50000000000000000000000000000000)⟩
def CB1_4_3I2S0_2_2Terms (a : Fin 6) : Ball :=
  match a.val with
  | 2 => ⟨(568005689670216830199298190037 / 6250000000000000000000000000000), (4787832559 / 12500000000000000000000000000000)⟩
  | 3 => ⟨(22443427331936396449249834231517 / 100000000000000000000000000000000), (5061233619 / 50000000000000000000000000000000)⟩
  | _ => (.exact 0)
def CB1_4_3I2S0_2_2Entropy : Ball := ⟨(31531518366659865732438605272109 / 100000000000000000000000000000000), (4842512771 / 10000000000000000000000000000000)⟩
def CB1_4_3I2S0_2_2Mass : Ball := ⟨1, 0⟩
def CB1_4_3I2S0_2_2MassTermLog : Ball := .exact 0
def CB1_4_3I2S0_2_2MassTerm : Ball := ⟨0, 0⟩
def CB1_4_3I2S0_2_2H : Ball := ⟨(31531518366659865732438605272109 / 100000000000000000000000000000000), (4842512771 / 10000000000000000000000000000000)⟩
def CB1_4_3I2S0_3_1Value (a : Fin 6) : ℝ := (littleLaw (shape 1 4 3) (shape 0 3 1) ((stageBPriority (shape 1 4 3)) 2) a : ℝ)
def CB1_4_3I2S0_3_1E_4Log : Ball := .exact 0
def CB1_4_3I2S0_3_1E_4 : Ball := ⟨0, 0⟩
def CB1_4_3I2S0_3_1Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB1_4_3I2S0_3_1Entropy : Ball := ⟨0, 0⟩
def CB1_4_3I2S0_3_1Mass : Ball := ⟨1, 0⟩
def CB1_4_3I2S0_3_1MassTermLog : Ball := .exact 0
def CB1_4_3I2S0_3_1MassTerm : Ball := ⟨0, 0⟩
def CB1_4_3I2S0_3_1H : Ball := ⟨0, 0⟩
def CB1_4_3I2S0_4_0Value (a : Fin 6) : ℝ := (littleLaw (shape 1 4 3) (shape 0 4 0) ((stageBPriority (shape 1 4 3)) 2) a : ℝ)
def CB1_4_3I2S0_4_0E_5Log : Ball := .exact 0
def CB1_4_3I2S0_4_0E_5 : Ball := ⟨0, 0⟩
def CB1_4_3I2S0_4_0Terms (a : Fin 6) : Ball :=
  match a.val with
  | 5 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB1_4_3I2S0_4_0Entropy : Ball := ⟨0, 0⟩
def CB1_4_3I2S0_4_0Mass : Ball := ⟨1, 0⟩
def CB1_4_3I2S0_4_0MassTermLog : Ball := .exact 0
def CB1_4_3I2S0_4_0MassTerm : Ball := ⟨0, 0⟩
def CB1_4_3I2S0_4_0H : Ball := ⟨0, 0⟩
def CB1_4_3I2S1_3_0Value (a : Fin 6) : ℝ := (littleLaw (shape 1 4 3) (shape 1 3 0) ((stageBPriority (shape 1 4 3)) 2) a : ℝ)
def CB1_4_3I2S1_3_0E_4Log : Ball := .exact 0
def CB1_4_3I2S1_3_0E_4 : Ball := ⟨0, 0⟩
def CB1_4_3I2S1_3_0Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB1_4_3I2S1_3_0Entropy : Ball := ⟨0, 0⟩
def CB1_4_3I2S1_3_0Mass : Ball := ⟨1, 0⟩
def CB1_4_3I2S1_3_0MassTermLog : Ball := .exact 0
def CB1_4_3I2S1_3_0MassTerm : Ball := ⟨0, 0⟩
def CB1_4_3I2S1_3_0H : Ball := ⟨0, 0⟩
def CB1_4_3I2Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 1, 3 => CB1_4_3I2S0_1_3H
  | 0, 2, 2 => CB1_4_3I2S0_2_2H
  | 0, 3, 1 => CB1_4_3I2S0_3_1H
  | 0, 4, 0 => CB1_4_3I2S0_4_0H
  | 1, 3, 0 => CB1_4_3I2S1_3_0H
  | _, _, _ => (.exact 0)
def CB1_4_3I2Singleton : Ball := ⟨(2654982546330514860850858021989 / 20000000000000000000000000000000), (1274199947 / 6250000000000000000000000000000)⟩
def CB1_4_3I2Group : Ball := ⟨(2829727512837008498339295078037 / 20000000000000000000000000000000), (88243521843 / 100000000000000000000000000000000)⟩

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
def CB1_4_3I2H : Ball := ⟨(14919945913031360053984414072733 / 25000000000000000000000000000000), (32152112867 / 12500000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB1_5_2I0
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
def CB1_5_2I0Value (a : Fin 17) : ℝ := marginal (below (shape 1 5 2)) (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) ((stageBPriority (shape 1 5 2)) 0) a
def CB1_5_2I0Entropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (21175823769 / 50000000000000000000000000000000)⟩
def CB1_5_2I0Mass : Ball := ⟨1, (51 / 50000000000000000000000000000000)⟩
def CB1_5_2I0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB1_5_2I0MassTermLog : Ball := ⟨0, (2646977973 / 12500000000000000000000000000000)⟩
def CB1_5_2I0MassTerm : Ball := ⟨0, (4235164757 / 20000000000000000000000000000000)⟩
def CB1_5_2I0H : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (63527471323 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB1_5_2I1
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
def CB1_5_2I1PairEntropy : Ball := ⟨(20829866306840848256149970053113 / 20000000000000000000000000000000), (60542738677 / 100000000000000000000000000000000)⟩
def CB1_5_2I1PairMass : Ball := ⟨1, (13 / 12500000000000000000000000000000)⟩
def CB1_5_2I1PairMassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB1_5_2I1PairMassTermLog : Ball := ⟨0, (10587911893 / 50000000000000000000000000000000)⟩
def CB1_5_2I1PairMassTerm : Ball := ⟨0, (21175823787 / 100000000000000000000000000000000)⟩
def CB1_5_2I1PairH : Ball := ⟨(20829866306840848256149970053113 / 20000000000000000000000000000000), (2553705077 / 3125000000000000000000000000000)⟩

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
def CB1_5_2I1R0Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 5 2)) (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 1 (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 1) a : ℝ)) 0 a
def CB1_5_2I1R0Entropy : Ball := ⟨(31215734820710901625169931976881 / 100000000000000000000000000000000), (3917171599 / 25000000000000000000000000000000)⟩
def CB1_5_2I1R0Mass : Ball := ⟨(18498319753969354799445690702431 / 100000000000000000000000000000000), (7 / 20000000000000000000000000000000)⟩
def CB1_5_2I1R0MassTermLogWitness : LogWitness := ⟨-3, 18498319753969354799445690702431, 12500000000000000000000000000000⟩
def CB1_5_2I1R0MassTermLog : Ball := ⟨(-5273407131682300154373846080691 / 3125000000000000000000000000000), (84703294921 / 100000000000000000000000000000000)⟩
def CB1_5_2I1R0MassTerm : Ball := ⟨(31215734820710901625169931976881 / 100000000000000000000000000000000), (3917171599 / 25000000000000000000000000000000)⟩
def CB1_5_2I1R0H : Ball := ⟨0, (3917171599 / 12500000000000000000000000000000)⟩
def CB1_5_2I1R1Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 5 2)) (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 1 (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 1) a : ℝ)) 1 a
def CB1_5_2I1R1Entropy : Ball := ⟨(29106426039391263700905778712527 / 100000000000000000000000000000000), (26682961111 / 100000000000000000000000000000000)⟩
def CB1_5_2I1R1Mass : Ball := ⟨(31501680246030645200554309297569 / 50000000000000000000000000000000), (1 / 3125000000000000000000000000000)⟩
def CB1_5_2I1R1MassTermLogWitness : LogWitness := ⟨-1, 31501680246030645200554309297569, 25000000000000000000000000000000⟩
def CB1_5_2I1R1MassTermLog : Ball := ⟨(-46198211987531689822285187163589 / 100000000000000000000000000000000), (5293955927 / 12500000000000000000000000000000)⟩
def CB1_5_2I1R1MassTerm : Ball := ⟨(29106426039391263700905778712527 / 100000000000000000000000000000000), (26682961111 / 100000000000000000000000000000000)⟩
def CB1_5_2I1R1H : Ball := ⟨0, (26682961111 / 50000000000000000000000000000000)⟩
def CB1_5_2I1R2Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 5 2)) (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 1 (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 1) a : ℝ)) 2 a
def CB1_5_2I1R2Entropy : Ball := ⟨(37521452747406488789922035776519 / 100000000000000000000000000000000), (16929888783 / 100000000000000000000000000000000)⟩
def CB1_5_2I1R2Mass : Ball := ⟨(18498319753969354799445690702431 / 100000000000000000000000000000000), (9 / 25000000000000000000000000000000)⟩
def CB1_5_2I1R2MassTermLogWitness : LogWitness := ⟨-3, 18498319753969354799445690702431, 12500000000000000000000000000000⟩
def CB1_5_2I1R2MassTermLog : Ball := ⟨(-5273407131682300154373846080691 / 3125000000000000000000000000000), (42351647463 / 50000000000000000000000000000000)⟩
def CB1_5_2I1R2MassTerm : Ball := ⟨(31215734820710901625169931976881 / 100000000000000000000000000000000), (15668686399 / 100000000000000000000000000000000)⟩
def CB1_5_2I1R2H : Ball := ⟨(3152858963347793582376051899819 / 50000000000000000000000000000000), (16299287591 / 50000000000000000000000000000000)⟩
def CB1_5_2I1R3Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 5 2)) (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 1 (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 1) a : ℝ)) 3 a
def CB1_5_2I1R3Entropy : Ball := ⟨0, 0⟩
def CB1_5_2I1R3Mass : Ball := ⟨0, 0⟩
def CB1_5_2I1R3MassTerm : Ball := .exact 0
def CB1_5_2I1R3H : Ball := ⟨0, 0⟩
def CB1_5_2I1R4Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 5 2)) (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 1 (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 1) a : ℝ)) 4 a
def CB1_5_2I1R4Entropy : Ball := ⟨0, 0⟩
def CB1_5_2I1R4Mass : Ball := ⟨0, 0⟩
def CB1_5_2I1R4MassTerm : Ball := .exact 0
def CB1_5_2I1R4H : Ball := ⟨0, 0⟩
def CB1_5_2I1R5Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 5 2)) (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 1 (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 1) a : ℝ)) 5 a
def CB1_5_2I1R5Entropy : Ball := ⟨0, 0⟩
def CB1_5_2I1R5Mass : Ball := ⟨0, 0⟩
def CB1_5_2I1R5MassTerm : Ball := .exact 0
def CB1_5_2I1R5H : Ball := ⟨0, 0⟩
def CB1_5_2I1R6Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 5 2)) (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 1 (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 1) a : ℝ)) 6 a
def CB1_5_2I1R6Entropy : Ball := ⟨0, 0⟩
def CB1_5_2I1R6Mass : Ball := ⟨0, 0⟩
def CB1_5_2I1R6MassTerm : Ball := .exact 0
def CB1_5_2I1R6H : Ball := ⟨0, 0⟩
def CB1_5_2I1R7Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 5 2)) (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 1 (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 1) a : ℝ)) 7 a
def CB1_5_2I1R7Entropy : Ball := ⟨0, 0⟩
def CB1_5_2I1R7Mass : Ball := ⟨0, 0⟩
def CB1_5_2I1R7MassTerm : Ball := .exact 0
def CB1_5_2I1R7H : Ball := ⟨0, 0⟩
def CB1_5_2I1R8Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 5 2)) (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 1 (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 1) a : ℝ)) 8 a
def CB1_5_2I1R8Entropy : Ball := ⟨0, 0⟩
def CB1_5_2I1R8Mass : Ball := ⟨0, 0⟩
def CB1_5_2I1R8MassTerm : Ball := .exact 0
def CB1_5_2I1R8H : Ball := ⟨0, 0⟩
def CB1_5_2I1R9Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 5 2)) (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 1 (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 1) a : ℝ)) 9 a
def CB1_5_2I1R9Entropy : Ball := ⟨0, 0⟩
def CB1_5_2I1R9Mass : Ball := ⟨0, 0⟩
def CB1_5_2I1R9MassTerm : Ball := .exact 0
def CB1_5_2I1R9H : Ball := ⟨0, 0⟩
def CB1_5_2I1R10Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 5 2)) (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 1 (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 1) a : ℝ)) 10 a
def CB1_5_2I1R10Entropy : Ball := ⟨0, 0⟩
def CB1_5_2I1R10Mass : Ball := ⟨0, 0⟩
def CB1_5_2I1R10MassTerm : Ball := .exact 0
def CB1_5_2I1R10H : Ball := ⟨0, 0⟩
def CB1_5_2I1R11Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 5 2)) (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 1 (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 1) a : ℝ)) 11 a
def CB1_5_2I1R11Entropy : Ball := ⟨0, 0⟩
def CB1_5_2I1R11Mass : Ball := ⟨0, 0⟩
def CB1_5_2I1R11MassTerm : Ball := .exact 0
def CB1_5_2I1R11H : Ball := ⟨0, 0⟩
def CB1_5_2I1R12Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 5 2)) (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 1 (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 1) a : ℝ)) 12 a
def CB1_5_2I1R12Entropy : Ball := ⟨0, 0⟩
def CB1_5_2I1R12Mass : Ball := ⟨0, 0⟩
def CB1_5_2I1R12MassTerm : Ball := .exact 0
def CB1_5_2I1R12H : Ball := ⟨0, 0⟩
def CB1_5_2I1R13Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 5 2)) (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 1 (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 1) a : ℝ)) 13 a
def CB1_5_2I1R13Entropy : Ball := ⟨0, 0⟩
def CB1_5_2I1R13Mass : Ball := ⟨0, 0⟩
def CB1_5_2I1R13MassTerm : Ball := .exact 0
def CB1_5_2I1R13H : Ball := ⟨0, 0⟩
def CB1_5_2I1R14Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 5 2)) (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 1 (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 1) a : ℝ)) 14 a
def CB1_5_2I1R14Entropy : Ball := ⟨0, 0⟩
def CB1_5_2I1R14Mass : Ball := ⟨0, 0⟩
def CB1_5_2I1R14MassTerm : Ball := .exact 0
def CB1_5_2I1R14H : Ball := ⟨0, 0⟩
def CB1_5_2I1R15Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 5 2)) (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 1 (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 1) a : ℝ)) 15 a
def CB1_5_2I1R15Entropy : Ball := ⟨0, 0⟩
def CB1_5_2I1R15Mass : Ball := ⟨0, 0⟩
def CB1_5_2I1R15MassTerm : Ball := .exact 0
def CB1_5_2I1R15H : Ball := ⟨0, 0⟩
def CB1_5_2I1R16Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 5 2)) (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 1 (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 1) a : ℝ)) 16 a
def CB1_5_2I1R16Entropy : Ball := ⟨0, 0⟩
def CB1_5_2I1R16Mass : Ball := ⟨0, 0⟩
def CB1_5_2I1R16MassTerm : Ball := .exact 0
def CB1_5_2I1R16H : Ball := ⟨0, 0⟩
def CB1_5_2I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CB1_5_2I1R0H
  | 1 => CB1_5_2I1R1H
  | 2 => CB1_5_2I1R2H
  | 3 => CB1_5_2I1R3H
  | 4 => CB1_5_2I1R4H
  | 5 => CB1_5_2I1R5H
  | 6 => CB1_5_2I1R6H
  | 7 => CB1_5_2I1R7H
  | 8 => CB1_5_2I1R8H
  | 9 => CB1_5_2I1R9H
  | 10 => CB1_5_2I1R10H
  | 11 => CB1_5_2I1R11H
  | 12 => CB1_5_2I1R12H
  | 13 => CB1_5_2I1R13H
  | 14 => CB1_5_2I1R14H
  | 15 => CB1_5_2I1R15H
  | 16 => CB1_5_2I1R16H
  | _ => (.exact 0)
def CB1_5_2I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | _, _, _ => (.exact 0)
def CB1_5_2I1Singleton : Ball := ⟨0, 0⟩
def CB1_5_2I1Group : Ball := ⟨(3152858963347793582376051899819 / 50000000000000000000000000000000), (29325467549 / 25000000000000000000000000000000)⟩

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
def CB1_5_2I1H : Ball := ⟨(91537895680813066951245642666289 / 100000000000000000000000000000000), (39540287857 / 12500000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB1_5_2I2
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
def CB1_5_2I2PairEntropy : Ball := ⟨(46989230332183785828872600023813 / 50000000000000000000000000000000), (17212159099 / 25000000000000000000000000000000)⟩
def CB1_5_2I2PairMass : Ball := ⟨1, (13 / 12500000000000000000000000000000)⟩
def CB1_5_2I2PairMassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB1_5_2I2PairMassTermLog : Ball := ⟨0, (10587911893 / 50000000000000000000000000000000)⟩
def CB1_5_2I2PairMassTerm : Ball := ⟨0, (21175823787 / 100000000000000000000000000000000)⟩
def CB1_5_2I2PairH : Ball := ⟨(46989230332183785828872600023813 / 50000000000000000000000000000000), (90024460183 / 100000000000000000000000000000000)⟩

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
def CB1_5_2I2R0Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 5 2)) (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 2 (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 2) a : ℝ)) 0 a
def CB1_5_2I2R0Entropy : Ball := ⟨0, 0⟩
def CB1_5_2I2R0Mass : Ball := ⟨0, 0⟩
def CB1_5_2I2R0MassTerm : Ball := .exact 0
def CB1_5_2I2R0H : Ball := ⟨0, 0⟩
def CB1_5_2I2R1Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 5 2)) (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 2 (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 2) a : ℝ)) 1 a
def CB1_5_2I2R1Entropy : Ball := ⟨(1759970095016132032706174310353 / 50000000000000000000000000000000), (678282269 / 50000000000000000000000000000000)⟩
def CB1_5_2I2R1Mass : Ball := ⟨(355899712240329557865752533361 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def CB1_5_2I2R1MassTermLogWitness : LogWitness := ⟨-8, 355899712240329557865752533361, 195312500000000000000000000000⟩
def CB1_5_2I2R1MassTermLog : Ball := ⟨(-494512930043526220764008265666271 / 100000000000000000000000000000000), (744462553 / 390625000000000000000000000000)⟩
def CB1_5_2I2R1MassTerm : Ball := ⟨(1759970095016132032706174310353 / 50000000000000000000000000000000), (678282269 / 50000000000000000000000000000000)⟩
def CB1_5_2I2R1H : Ball := ⟨0, (678282269 / 25000000000000000000000000000000)⟩
def CB1_5_2I2R2Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 5 2)) (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 2 (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 2) a : ℝ)) 2 a
def CB1_5_2I2R2Entropy : Ball := ⟨(1161430537036209655451354528793 / 3125000000000000000000000000000), (2526522869 / 12500000000000000000000000000000)⟩
def CB1_5_2I2R2Mass : Ball := ⟨(31501680246030645200554309297569 / 100000000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩
def CB1_5_2I2R2MassTermLogWitness : LogWitness := ⟨-2, 31501680246030645200554309297569, 25000000000000000000000000000000⟩
def CB1_5_2I2R2MassTermLog : Ball := ⟨(-115512930043526220764008380213919 / 100000000000000000000000000000000), (31763735551 / 50000000000000000000000000000000)⟩
def CB1_5_2I2R2MassTerm : Ball := ⟨(9097128466283174464330993949041 / 25000000000000000000000000000000), (4002444167 / 20000000000000000000000000000000)⟩
def CB1_5_2I2R2H : Ball := ⟨(194315830006502779279842281303 / 25000000000000000000000000000000), (40224403787 / 100000000000000000000000000000000)⟩
def CB1_5_2I2R3Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 5 2)) (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 2 (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 2) a : ℝ)) 3 a
def CB1_5_2I2R3Entropy : Ball := ⟨0, 0⟩
def CB1_5_2I2R3Mass : Ball := ⟨0, 0⟩
def CB1_5_2I2R3MassTerm : Ball := .exact 0
def CB1_5_2I2R3H : Ball := ⟨0, 0⟩
def CB1_5_2I2R4Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 5 2)) (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 2 (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 2) a : ℝ)) 4 a
def CB1_5_2I2R4Entropy : Ball := ⟨0, 0⟩
def CB1_5_2I2R4Mass : Ball := ⟨0, 0⟩
def CB1_5_2I2R4MassTerm : Ball := .exact 0
def CB1_5_2I2R4H : Ball := ⟨0, 0⟩
def CB1_5_2I2R5Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 5 2)) (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 2 (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 2) a : ℝ)) 5 a
def CB1_5_2I2R5Entropy : Ball := ⟨0, 0⟩
def CB1_5_2I2R5Mass : Ball := ⟨0, 0⟩
def CB1_5_2I2R5MassTerm : Ball := .exact 0
def CB1_5_2I2R5H : Ball := ⟨0, 0⟩
def CB1_5_2I2R6Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 5 2)) (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 2 (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 2) a : ℝ)) 6 a
def CB1_5_2I2R6Entropy : Ball := ⟨0, 0⟩
def CB1_5_2I2R6Mass : Ball := ⟨0, 0⟩
def CB1_5_2I2R6MassTerm : Ball := .exact 0
def CB1_5_2I2R6H : Ball := ⟨0, 0⟩
def CB1_5_2I2R7Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 5 2)) (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 2 (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 2) a : ℝ)) 7 a
def CB1_5_2I2R7Entropy : Ball := ⟨0, 0⟩
def CB1_5_2I2R7Mass : Ball := ⟨0, 0⟩
def CB1_5_2I2R7MassTerm : Ball := .exact 0
def CB1_5_2I2R7H : Ball := ⟨0, 0⟩
def CB1_5_2I2R8Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 5 2)) (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 2 (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 2) a : ℝ)) 8 a
def CB1_5_2I2R8Entropy : Ball := ⟨0, 0⟩
def CB1_5_2I2R8Mass : Ball := ⟨0, 0⟩
def CB1_5_2I2R8MassTerm : Ball := .exact 0
def CB1_5_2I2R8H : Ball := ⟨0, 0⟩
def CB1_5_2I2R9Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 5 2)) (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 2 (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 2) a : ℝ)) 9 a
def CB1_5_2I2R9Entropy : Ball := ⟨0, 0⟩
def CB1_5_2I2R9Mass : Ball := ⟨0, 0⟩
def CB1_5_2I2R9MassTerm : Ball := .exact 0
def CB1_5_2I2R9H : Ball := ⟨0, 0⟩
def CB1_5_2I2R10Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 5 2)) (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 2 (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 2) a : ℝ)) 10 a
def CB1_5_2I2R10Entropy : Ball := ⟨0, 0⟩
def CB1_5_2I2R10Mass : Ball := ⟨0, 0⟩
def CB1_5_2I2R10MassTerm : Ball := .exact 0
def CB1_5_2I2R10H : Ball := ⟨0, 0⟩
def CB1_5_2I2R11Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 5 2)) (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 2 (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 2) a : ℝ)) 11 a
def CB1_5_2I2R11Entropy : Ball := ⟨0, 0⟩
def CB1_5_2I2R11Mass : Ball := ⟨0, 0⟩
def CB1_5_2I2R11MassTerm : Ball := .exact 0
def CB1_5_2I2R11H : Ball := ⟨0, 0⟩
def CB1_5_2I2R12Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 5 2)) (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 2 (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 2) a : ℝ)) 12 a
def CB1_5_2I2R12Entropy : Ball := ⟨0, 0⟩
def CB1_5_2I2R12Mass : Ball := ⟨0, 0⟩
def CB1_5_2I2R12MassTerm : Ball := .exact 0
def CB1_5_2I2R12H : Ball := ⟨0, 0⟩
def CB1_5_2I2R13Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 5 2)) (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 2 (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 2) a : ℝ)) 13 a
def CB1_5_2I2R13Entropy : Ball := ⟨0, 0⟩
def CB1_5_2I2R13Mass : Ball := ⟨0, 0⟩
def CB1_5_2I2R13MassTerm : Ball := .exact 0
def CB1_5_2I2R13H : Ball := ⟨0, 0⟩
def CB1_5_2I2R14Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 5 2)) (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 2 (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 2) a : ℝ)) 14 a
def CB1_5_2I2R14Entropy : Ball := ⟨0, 0⟩
def CB1_5_2I2R14Mass : Ball := ⟨0, 0⟩
def CB1_5_2I2R14MassTerm : Ball := .exact 0
def CB1_5_2I2R14H : Ball := ⟨0, 0⟩
def CB1_5_2I2R15Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 5 2)) (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 2 (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 2) a : ℝ)) 15 a
def CB1_5_2I2R15Entropy : Ball := ⟨0, 0⟩
def CB1_5_2I2R15Mass : Ball := ⟨0, 0⟩
def CB1_5_2I2R15MassTerm : Ball := .exact 0
def CB1_5_2I2R15H : Ball := ⟨0, 0⟩
def CB1_5_2I2R16Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 5 2)) (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 2 (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 2) a : ℝ)) 16 a
def CB1_5_2I2R16Entropy : Ball := ⟨0, 0⟩
def CB1_5_2I2R16Mass : Ball := ⟨0, 0⟩
def CB1_5_2I2R16MassTerm : Ball := .exact 0
def CB1_5_2I2R16H : Ball := ⟨0, 0⟩
def CB1_5_2I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CB1_5_2I2R0H
  | 1 => CB1_5_2I2R1H
  | 2 => CB1_5_2I2R2H
  | 3 => CB1_5_2I2R3H
  | 4 => CB1_5_2I2R4H
  | 5 => CB1_5_2I2R5H
  | 6 => CB1_5_2I2R6H
  | 7 => CB1_5_2I2R7H
  | 8 => CB1_5_2I2R8H
  | 9 => CB1_5_2I2R9H
  | 10 => CB1_5_2I2R10H
  | 11 => CB1_5_2I2R11H
  | 12 => CB1_5_2I2R12H
  | 13 => CB1_5_2I2R13H
  | 14 => CB1_5_2I2R14H
  | 15 => CB1_5_2I2R15H
  | 16 => CB1_5_2I2R16H
  | _ => (.exact 0)
def CB1_5_2I2S0_2_2Value (a : Fin 6) : ℝ := (littleLaw (shape 1 5 2) (shape 0 2 2) ((stageBPriority (shape 1 5 2)) 2) a : ℝ)
def CB1_5_2I2S0_2_2E_2LogWitness : LogWitness := ⟨-1, 890067, 500000⟩
def CB1_5_2I2S0_2_2E_2Log : Ball := ⟨(-11645853819053979009096802094341 / 100000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
def CB1_5_2I2S0_2_2E_2 : Ball := ⟨(1295698771395489741836220418713 / 12500000000000000000000000000000), (9423950929 / 25000000000000000000000000000000)⟩
def CB1_5_2I2S0_2_2E_3LogWitness : LogWitness := ⟨-4, 109933, 62500⟩
def CB1_5_2I2S0_2_2E_3Log : Ball := ⟨(-220788418967003649163974598210309 / 100000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
def CB1_5_2I2S0_2_2E_3 : Ball := ⟨(12135966631149806081771609752527 / 50000000000000000000000000000000), (93116873 / 800000000000000000000000000000)⟩
def CB1_5_2I2S0_2_2Terms (a : Fin 6) : Ball :=
  match a.val with
  | 2 => ⟨(1295698771395489741836220418713 / 12500000000000000000000000000000), (9423950929 / 25000000000000000000000000000000)⟩
  | 3 => ⟨(12135966631149806081771609752527 / 50000000000000000000000000000000), (93116873 / 800000000000000000000000000000)⟩
  | _ => (.exact 0)
def CB1_5_2I2S0_2_2Entropy : Ball := ⟨(17318761716731765049116491427379 / 50000000000000000000000000000000), (49335412841 / 100000000000000000000000000000000)⟩
def CB1_5_2I2S0_2_2Mass : Ball := ⟨1, 0⟩
def CB1_5_2I2S0_2_2MassTermLog : Ball := .exact 0
def CB1_5_2I2S0_2_2MassTerm : Ball := ⟨0, 0⟩
def CB1_5_2I2S0_2_2H : Ball := ⟨(17318761716731765049116491427379 / 50000000000000000000000000000000), (49335412841 / 100000000000000000000000000000000)⟩
def CB1_5_2I2S0_3_1Value (a : Fin 6) : ℝ := (littleLaw (shape 1 5 2) (shape 0 3 1) ((stageBPriority (shape 1 5 2)) 2) a : ℝ)
def CB1_5_2I2S0_3_1E_4Log : Ball := .exact 0
def CB1_5_2I2S0_3_1E_4 : Ball := ⟨0, 0⟩
def CB1_5_2I2S0_3_1Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB1_5_2I2S0_3_1Entropy : Ball := ⟨0, 0⟩
def CB1_5_2I2S0_3_1Mass : Ball := ⟨1, 0⟩
def CB1_5_2I2S0_3_1MassTermLog : Ball := .exact 0
def CB1_5_2I2S0_3_1MassTerm : Ball := ⟨0, 0⟩
def CB1_5_2I2S0_3_1H : Ball := ⟨0, 0⟩
def CB1_5_2I2S0_4_0Value (a : Fin 6) : ℝ := (littleLaw (shape 1 5 2) (shape 0 4 0) ((stageBPriority (shape 1 5 2)) 2) a : ℝ)
def CB1_5_2I2S0_4_0E_5Log : Ball := .exact 0
def CB1_5_2I2S0_4_0E_5 : Ball := ⟨0, 0⟩
def CB1_5_2I2S0_4_0Terms (a : Fin 6) : Ball :=
  match a.val with
  | 5 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB1_5_2I2S0_4_0Entropy : Ball := ⟨0, 0⟩
def CB1_5_2I2S0_4_0Mass : Ball := ⟨1, 0⟩
def CB1_5_2I2S0_4_0MassTermLog : Ball := .exact 0
def CB1_5_2I2S0_4_0MassTerm : Ball := ⟨0, 0⟩
def CB1_5_2I2S0_4_0H : Ball := ⟨0, 0⟩
def CB1_5_2I2S1_3_0Value (a : Fin 6) : ℝ := (littleLaw (shape 1 5 2) (shape 1 3 0) ((stageBPriority (shape 1 5 2)) 2) a : ℝ)
def CB1_5_2I2S1_3_0E_4Log : Ball := .exact 0
def CB1_5_2I2S1_3_0E_4 : Ball := ⟨0, 0⟩
def CB1_5_2I2S1_3_0Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB1_5_2I2S1_3_0Entropy : Ball := ⟨0, 0⟩
def CB1_5_2I2S1_3_0Mass : Ball := ⟨1, 0⟩
def CB1_5_2I2S1_3_0MassTermLog : Ball := .exact 0
def CB1_5_2I2S1_3_0MassTerm : Ball := ⟨0, 0⟩
def CB1_5_2I2S1_3_0H : Ball := ⟨0, 0⟩
def CB1_5_2I2Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => CB1_5_2I2S0_2_2H
  | 0, 3, 1 => CB1_5_2I2S0_3_1H
  | 0, 4, 0 => CB1_5_2I2S0_4_0H
  | 1, 3, 0 => CB1_5_2I2S1_3_0H
  | _, _, _ => (.exact 0)
def CB1_5_2I2Singleton : Ball := ⟨(6160810147124401651688069031141 / 100000000000000000000000000000000), (4387526623 / 50000000000000000000000000000000)⟩
def CB1_5_2I2Group : Ball := ⟨(6938073467150412768807438156353 / 100000000000000000000000000000000), (51712586109 / 100000000000000000000000000000000)⟩

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
def CB1_5_2I2H : Ball := ⟨(2002557843251668653003258093373 / 2500000000000000000000000000000), (193449632401 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB1_6_1I0
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
def CB1_6_1I0Value (a : Fin 17) : ℝ := marginal (below (shape 1 6 1)) (fun u => (stageBLaw (shape 1 6 1) u : ℝ)) ((stageBPriority (shape 1 6 1)) 0) a
def CB1_6_1I0Entropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (21175823741 / 50000000000000000000000000000000)⟩
def CB1_6_1I0Mass : Ball := ⟨1, (17 / 25000000000000000000000000000000)⟩
def CB1_6_1I0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB1_6_1I0MassTermLog : Ball := ⟨0, (16940659 / 80000000000000000000000000000)⟩
def CB1_6_1I0MassTerm : Ball := ⟨0, (21175823751 / 100000000000000000000000000000000)⟩
def CB1_6_1I0H : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (63527471233 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB1_6_1I1
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
def CB1_6_1I1PairEntropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (21175823741 / 50000000000000000000000000000000)⟩
def CB1_6_1I1PairMass : Ball := ⟨1, (17 / 25000000000000000000000000000000)⟩
def CB1_6_1I1PairMassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB1_6_1I1PairMassTermLog : Ball := ⟨0, (16940659 / 80000000000000000000000000000)⟩
def CB1_6_1I1PairMassTerm : Ball := ⟨0, (21175823751 / 100000000000000000000000000000000)⟩
def CB1_6_1I1PairH : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (63527471233 / 100000000000000000000000000000000)⟩

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
def CB1_6_1I1R0Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 6 1)) (fun u => (stageBLaw (shape 1 6 1) u : ℝ)) (stageBPriority (shape 1 6 1)) 1 (fun u a => (littleLaw (shape 1 6 1) u ((stageBPriority (shape 1 6 1)) 1) a : ℝ)) 0 a
def CB1_6_1I1R0Entropy : Ball := ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823741 / 100000000000000000000000000000000)⟩
def CB1_6_1I1R0Mass : Ball := ⟨(1 / 2), (17 / 50000000000000000000000000000000)⟩
def CB1_6_1I1R0MassTermLogWitness : LogWitness := ⟨-1, 1, 1⟩
def CB1_6_1I1R0MassTermLog : Ball := ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (42351647433 / 100000000000000000000000000000000)⟩
def CB1_6_1I1R0MassTerm : Ball := ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823741 / 100000000000000000000000000000000)⟩
def CB1_6_1I1R0H : Ball := ⟨0, (21175823741 / 50000000000000000000000000000000)⟩
def CB1_6_1I1R1Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 6 1)) (fun u => (stageBLaw (shape 1 6 1) u : ℝ)) (stageBPriority (shape 1 6 1)) 1 (fun u a => (littleLaw (shape 1 6 1) u ((stageBPriority (shape 1 6 1)) 1) a : ℝ)) 1 a
def CB1_6_1I1R1Entropy : Ball := ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823741 / 100000000000000000000000000000000)⟩
def CB1_6_1I1R1Mass : Ball := ⟨(1 / 2), (17 / 50000000000000000000000000000000)⟩
def CB1_6_1I1R1MassTermLogWitness : LogWitness := ⟨-1, 1, 1⟩
def CB1_6_1I1R1MassTermLog : Ball := ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (42351647433 / 100000000000000000000000000000000)⟩
def CB1_6_1I1R1MassTerm : Ball := ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823741 / 100000000000000000000000000000000)⟩
def CB1_6_1I1R1H : Ball := ⟨0, (21175823741 / 50000000000000000000000000000000)⟩
def CB1_6_1I1R2Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 6 1)) (fun u => (stageBLaw (shape 1 6 1) u : ℝ)) (stageBPriority (shape 1 6 1)) 1 (fun u a => (littleLaw (shape 1 6 1) u ((stageBPriority (shape 1 6 1)) 1) a : ℝ)) 2 a
def CB1_6_1I1R2Entropy : Ball := ⟨0, 0⟩
def CB1_6_1I1R2Mass : Ball := ⟨0, 0⟩
def CB1_6_1I1R2MassTerm : Ball := .exact 0
def CB1_6_1I1R2H : Ball := ⟨0, 0⟩
def CB1_6_1I1R3Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 6 1)) (fun u => (stageBLaw (shape 1 6 1) u : ℝ)) (stageBPriority (shape 1 6 1)) 1 (fun u a => (littleLaw (shape 1 6 1) u ((stageBPriority (shape 1 6 1)) 1) a : ℝ)) 3 a
def CB1_6_1I1R3Entropy : Ball := ⟨0, 0⟩
def CB1_6_1I1R3Mass : Ball := ⟨0, 0⟩
def CB1_6_1I1R3MassTerm : Ball := .exact 0
def CB1_6_1I1R3H : Ball := ⟨0, 0⟩
def CB1_6_1I1R4Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 6 1)) (fun u => (stageBLaw (shape 1 6 1) u : ℝ)) (stageBPriority (shape 1 6 1)) 1 (fun u a => (littleLaw (shape 1 6 1) u ((stageBPriority (shape 1 6 1)) 1) a : ℝ)) 4 a
def CB1_6_1I1R4Entropy : Ball := ⟨0, 0⟩
def CB1_6_1I1R4Mass : Ball := ⟨0, 0⟩
def CB1_6_1I1R4MassTerm : Ball := .exact 0
def CB1_6_1I1R4H : Ball := ⟨0, 0⟩
def CB1_6_1I1R5Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 6 1)) (fun u => (stageBLaw (shape 1 6 1) u : ℝ)) (stageBPriority (shape 1 6 1)) 1 (fun u a => (littleLaw (shape 1 6 1) u ((stageBPriority (shape 1 6 1)) 1) a : ℝ)) 5 a
def CB1_6_1I1R5Entropy : Ball := ⟨0, 0⟩
def CB1_6_1I1R5Mass : Ball := ⟨0, 0⟩
def CB1_6_1I1R5MassTerm : Ball := .exact 0
def CB1_6_1I1R5H : Ball := ⟨0, 0⟩
def CB1_6_1I1R6Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 6 1)) (fun u => (stageBLaw (shape 1 6 1) u : ℝ)) (stageBPriority (shape 1 6 1)) 1 (fun u a => (littleLaw (shape 1 6 1) u ((stageBPriority (shape 1 6 1)) 1) a : ℝ)) 6 a
def CB1_6_1I1R6Entropy : Ball := ⟨0, 0⟩
def CB1_6_1I1R6Mass : Ball := ⟨0, 0⟩
def CB1_6_1I1R6MassTerm : Ball := .exact 0
def CB1_6_1I1R6H : Ball := ⟨0, 0⟩
def CB1_6_1I1R7Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 6 1)) (fun u => (stageBLaw (shape 1 6 1) u : ℝ)) (stageBPriority (shape 1 6 1)) 1 (fun u a => (littleLaw (shape 1 6 1) u ((stageBPriority (shape 1 6 1)) 1) a : ℝ)) 7 a
def CB1_6_1I1R7Entropy : Ball := ⟨0, 0⟩
def CB1_6_1I1R7Mass : Ball := ⟨0, 0⟩
def CB1_6_1I1R7MassTerm : Ball := .exact 0
def CB1_6_1I1R7H : Ball := ⟨0, 0⟩
def CB1_6_1I1R8Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 6 1)) (fun u => (stageBLaw (shape 1 6 1) u : ℝ)) (stageBPriority (shape 1 6 1)) 1 (fun u a => (littleLaw (shape 1 6 1) u ((stageBPriority (shape 1 6 1)) 1) a : ℝ)) 8 a
def CB1_6_1I1R8Entropy : Ball := ⟨0, 0⟩
def CB1_6_1I1R8Mass : Ball := ⟨0, 0⟩
def CB1_6_1I1R8MassTerm : Ball := .exact 0
def CB1_6_1I1R8H : Ball := ⟨0, 0⟩
def CB1_6_1I1R9Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 6 1)) (fun u => (stageBLaw (shape 1 6 1) u : ℝ)) (stageBPriority (shape 1 6 1)) 1 (fun u a => (littleLaw (shape 1 6 1) u ((stageBPriority (shape 1 6 1)) 1) a : ℝ)) 9 a
def CB1_6_1I1R9Entropy : Ball := ⟨0, 0⟩
def CB1_6_1I1R9Mass : Ball := ⟨0, 0⟩
def CB1_6_1I1R9MassTerm : Ball := .exact 0
def CB1_6_1I1R9H : Ball := ⟨0, 0⟩
def CB1_6_1I1R10Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 6 1)) (fun u => (stageBLaw (shape 1 6 1) u : ℝ)) (stageBPriority (shape 1 6 1)) 1 (fun u a => (littleLaw (shape 1 6 1) u ((stageBPriority (shape 1 6 1)) 1) a : ℝ)) 10 a
def CB1_6_1I1R10Entropy : Ball := ⟨0, 0⟩
def CB1_6_1I1R10Mass : Ball := ⟨0, 0⟩
def CB1_6_1I1R10MassTerm : Ball := .exact 0
def CB1_6_1I1R10H : Ball := ⟨0, 0⟩
def CB1_6_1I1R11Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 6 1)) (fun u => (stageBLaw (shape 1 6 1) u : ℝ)) (stageBPriority (shape 1 6 1)) 1 (fun u a => (littleLaw (shape 1 6 1) u ((stageBPriority (shape 1 6 1)) 1) a : ℝ)) 11 a
def CB1_6_1I1R11Entropy : Ball := ⟨0, 0⟩
def CB1_6_1I1R11Mass : Ball := ⟨0, 0⟩
def CB1_6_1I1R11MassTerm : Ball := .exact 0
def CB1_6_1I1R11H : Ball := ⟨0, 0⟩
def CB1_6_1I1R12Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 6 1)) (fun u => (stageBLaw (shape 1 6 1) u : ℝ)) (stageBPriority (shape 1 6 1)) 1 (fun u a => (littleLaw (shape 1 6 1) u ((stageBPriority (shape 1 6 1)) 1) a : ℝ)) 12 a
def CB1_6_1I1R12Entropy : Ball := ⟨0, 0⟩
def CB1_6_1I1R12Mass : Ball := ⟨0, 0⟩
def CB1_6_1I1R12MassTerm : Ball := .exact 0
def CB1_6_1I1R12H : Ball := ⟨0, 0⟩
def CB1_6_1I1R13Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 6 1)) (fun u => (stageBLaw (shape 1 6 1) u : ℝ)) (stageBPriority (shape 1 6 1)) 1 (fun u a => (littleLaw (shape 1 6 1) u ((stageBPriority (shape 1 6 1)) 1) a : ℝ)) 13 a
def CB1_6_1I1R13Entropy : Ball := ⟨0, 0⟩
def CB1_6_1I1R13Mass : Ball := ⟨0, 0⟩
def CB1_6_1I1R13MassTerm : Ball := .exact 0
def CB1_6_1I1R13H : Ball := ⟨0, 0⟩
def CB1_6_1I1R14Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 6 1)) (fun u => (stageBLaw (shape 1 6 1) u : ℝ)) (stageBPriority (shape 1 6 1)) 1 (fun u a => (littleLaw (shape 1 6 1) u ((stageBPriority (shape 1 6 1)) 1) a : ℝ)) 14 a
def CB1_6_1I1R14Entropy : Ball := ⟨0, 0⟩
def CB1_6_1I1R14Mass : Ball := ⟨0, 0⟩
def CB1_6_1I1R14MassTerm : Ball := .exact 0
def CB1_6_1I1R14H : Ball := ⟨0, 0⟩
def CB1_6_1I1R15Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 6 1)) (fun u => (stageBLaw (shape 1 6 1) u : ℝ)) (stageBPriority (shape 1 6 1)) 1 (fun u a => (littleLaw (shape 1 6 1) u ((stageBPriority (shape 1 6 1)) 1) a : ℝ)) 15 a
def CB1_6_1I1R15Entropy : Ball := ⟨0, 0⟩
def CB1_6_1I1R15Mass : Ball := ⟨0, 0⟩
def CB1_6_1I1R15MassTerm : Ball := .exact 0
def CB1_6_1I1R15H : Ball := ⟨0, 0⟩
def CB1_6_1I1R16Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 6 1)) (fun u => (stageBLaw (shape 1 6 1) u : ℝ)) (stageBPriority (shape 1 6 1)) 1 (fun u a => (littleLaw (shape 1 6 1) u ((stageBPriority (shape 1 6 1)) 1) a : ℝ)) 16 a
def CB1_6_1I1R16Entropy : Ball := ⟨0, 0⟩
def CB1_6_1I1R16Mass : Ball := ⟨0, 0⟩
def CB1_6_1I1R16MassTerm : Ball := .exact 0
def CB1_6_1I1R16H : Ball := ⟨0, 0⟩
def CB1_6_1I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CB1_6_1I1R0H
  | 1 => CB1_6_1I1R1H
  | 2 => CB1_6_1I1R2H
  | 3 => CB1_6_1I1R3H
  | 4 => CB1_6_1I1R4H
  | 5 => CB1_6_1I1R5H
  | 6 => CB1_6_1I1R6H
  | 7 => CB1_6_1I1R7H
  | 8 => CB1_6_1I1R8H
  | 9 => CB1_6_1I1R9H
  | 10 => CB1_6_1I1R10H
  | 11 => CB1_6_1I1R11H
  | 12 => CB1_6_1I1R12H
  | 13 => CB1_6_1I1R13H
  | 14 => CB1_6_1I1R14H
  | 15 => CB1_6_1I1R15H
  | 16 => CB1_6_1I1R16H
  | _ => (.exact 0)
def CB1_6_1I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | _, _, _ => (.exact 0)
def CB1_6_1I1Singleton : Ball := ⟨0, 0⟩
def CB1_6_1I1Group : Ball := ⟨0, (21175823741 / 25000000000000000000000000000000)⟩

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
def CB1_6_1I1H : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (232934061161 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB1_6_1I2
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
def CB1_6_1I2PairEntropy : Ball := ⟨(9416373772512423570761032525457 / 12500000000000000000000000000000), (29127720699 / 50000000000000000000000000000000)⟩
def CB1_6_1I2PairMass : Ball := ⟨1, (9 / 12500000000000000000000000000000)⟩
def CB1_6_1I2PairMassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB1_6_1I2PairMassTermLog : Ball := ⟨0, (10587911877 / 50000000000000000000000000000000)⟩
def CB1_6_1I2PairMassTerm : Ball := ⟨0, (4235164751 / 20000000000000000000000000000000)⟩
def CB1_6_1I2PairH : Ball := ⟨(9416373772512423570761032525457 / 12500000000000000000000000000000), (79431265153 / 100000000000000000000000000000000)⟩

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
def CB1_6_1I2R0Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 6 1)) (fun u => (stageBLaw (shape 1 6 1) u : ℝ)) (stageBPriority (shape 1 6 1)) 2 (fun u a => (littleLaw (shape 1 6 1) u ((stageBPriority (shape 1 6 1)) 2) a : ℝ)) 0 a
def CB1_6_1I2R0Entropy : Ball := ⟨0, 0⟩
def CB1_6_1I2R0Mass : Ball := ⟨0, 0⟩
def CB1_6_1I2R0MassTerm : Ball := .exact 0
def CB1_6_1I2R0H : Ball := ⟨0, 0⟩
def CB1_6_1I2R1Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 6 1)) (fun u => (stageBLaw (shape 1 6 1) u : ℝ)) (stageBPriority (shape 1 6 1)) 2 (fun u a => (littleLaw (shape 1 6 1) u ((stageBPriority (shape 1 6 1)) 2) a : ℝ)) 1 a
def CB1_6_1I2R1Entropy : Ball := ⟨0, 0⟩
def CB1_6_1I2R1Mass : Ball := ⟨0, 0⟩
def CB1_6_1I2R1MassTerm : Ball := .exact 0
def CB1_6_1I2R1H : Ball := ⟨0, 0⟩
def CB1_6_1I2R2Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 6 1)) (fun u => (stageBLaw (shape 1 6 1) u : ℝ)) (stageBPriority (shape 1 6 1)) 2 (fun u a => (littleLaw (shape 1 6 1) u ((stageBPriority (shape 1 6 1)) 2) a : ℝ)) 2 a
def CB1_6_1I2R2Entropy : Ball := ⟨(27343400567405714695954252025363 / 100000000000000000000000000000000), (12972090991 / 100000000000000000000000000000000)⟩
def CB1_6_1I2R2Mass : Ball := ⟨(148169974001711440219168429137 / 1250000000000000000000000000000), (23 / 100000000000000000000000000000000)⟩
def CB1_6_1I2R2MassTermLogWitness : LogWitness := ⟨-4, 148169974001711440219168429137, 78125000000000000000000000000⟩
def CB1_6_1I2R2MassTermLog : Ball := ⟨(-21325387425382860905843152201521 / 10000000000000000000000000000000), (105879118609 / 100000000000000000000000000000000)⟩
def CB1_6_1I2R2MassTerm : Ball := ⟨(12639128401581610264774180864021 / 50000000000000000000000000000000), (12550485051 / 100000000000000000000000000000000)⟩
def CB1_6_1I2R2H : Ball := ⟨(2065143764242494166405890297321 / 100000000000000000000000000000000), (12761288021 / 50000000000000000000000000000000)⟩
def CB1_6_1I2R3Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 6 1)) (fun u => (stageBLaw (shape 1 6 1) u : ℝ)) (stageBPriority (shape 1 6 1)) 2 (fun u a => (littleLaw (shape 1 6 1) u ((stageBPriority (shape 1 6 1)) 2) a : ℝ)) 3 a
def CB1_6_1I2R3Entropy : Ball := ⟨0, 0⟩
def CB1_6_1I2R3Mass : Ball := ⟨0, 0⟩
def CB1_6_1I2R3MassTerm : Ball := .exact 0
def CB1_6_1I2R3H : Ball := ⟨0, 0⟩
def CB1_6_1I2R4Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 6 1)) (fun u => (stageBLaw (shape 1 6 1) u : ℝ)) (stageBPriority (shape 1 6 1)) 2 (fun u a => (littleLaw (shape 1 6 1) u ((stageBPriority (shape 1 6 1)) 2) a : ℝ)) 4 a
def CB1_6_1I2R4Entropy : Ball := ⟨0, 0⟩
def CB1_6_1I2R4Mass : Ball := ⟨0, 0⟩
def CB1_6_1I2R4MassTerm : Ball := .exact 0
def CB1_6_1I2R4H : Ball := ⟨0, 0⟩
def CB1_6_1I2R5Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 6 1)) (fun u => (stageBLaw (shape 1 6 1) u : ℝ)) (stageBPriority (shape 1 6 1)) 2 (fun u a => (littleLaw (shape 1 6 1) u ((stageBPriority (shape 1 6 1)) 2) a : ℝ)) 5 a
def CB1_6_1I2R5Entropy : Ball := ⟨0, 0⟩
def CB1_6_1I2R5Mass : Ball := ⟨0, 0⟩
def CB1_6_1I2R5MassTerm : Ball := .exact 0
def CB1_6_1I2R5H : Ball := ⟨0, 0⟩
def CB1_6_1I2R6Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 6 1)) (fun u => (stageBLaw (shape 1 6 1) u : ℝ)) (stageBPriority (shape 1 6 1)) 2 (fun u a => (littleLaw (shape 1 6 1) u ((stageBPriority (shape 1 6 1)) 2) a : ℝ)) 6 a
def CB1_6_1I2R6Entropy : Ball := ⟨0, 0⟩
def CB1_6_1I2R6Mass : Ball := ⟨0, 0⟩
def CB1_6_1I2R6MassTerm : Ball := .exact 0
def CB1_6_1I2R6H : Ball := ⟨0, 0⟩
def CB1_6_1I2R7Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 6 1)) (fun u => (stageBLaw (shape 1 6 1) u : ℝ)) (stageBPriority (shape 1 6 1)) 2 (fun u a => (littleLaw (shape 1 6 1) u ((stageBPriority (shape 1 6 1)) 2) a : ℝ)) 7 a
def CB1_6_1I2R7Entropy : Ball := ⟨0, 0⟩
def CB1_6_1I2R7Mass : Ball := ⟨0, 0⟩
def CB1_6_1I2R7MassTerm : Ball := .exact 0
def CB1_6_1I2R7H : Ball := ⟨0, 0⟩
def CB1_6_1I2R8Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 6 1)) (fun u => (stageBLaw (shape 1 6 1) u : ℝ)) (stageBPriority (shape 1 6 1)) 2 (fun u a => (littleLaw (shape 1 6 1) u ((stageBPriority (shape 1 6 1)) 2) a : ℝ)) 8 a
def CB1_6_1I2R8Entropy : Ball := ⟨0, 0⟩
def CB1_6_1I2R8Mass : Ball := ⟨0, 0⟩
def CB1_6_1I2R8MassTerm : Ball := .exact 0
def CB1_6_1I2R8H : Ball := ⟨0, 0⟩
def CB1_6_1I2R9Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 6 1)) (fun u => (stageBLaw (shape 1 6 1) u : ℝ)) (stageBPriority (shape 1 6 1)) 2 (fun u a => (littleLaw (shape 1 6 1) u ((stageBPriority (shape 1 6 1)) 2) a : ℝ)) 9 a
def CB1_6_1I2R9Entropy : Ball := ⟨0, 0⟩
def CB1_6_1I2R9Mass : Ball := ⟨0, 0⟩
def CB1_6_1I2R9MassTerm : Ball := .exact 0
def CB1_6_1I2R9H : Ball := ⟨0, 0⟩
def CB1_6_1I2R10Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 6 1)) (fun u => (stageBLaw (shape 1 6 1) u : ℝ)) (stageBPriority (shape 1 6 1)) 2 (fun u a => (littleLaw (shape 1 6 1) u ((stageBPriority (shape 1 6 1)) 2) a : ℝ)) 10 a
def CB1_6_1I2R10Entropy : Ball := ⟨0, 0⟩
def CB1_6_1I2R10Mass : Ball := ⟨0, 0⟩
def CB1_6_1I2R10MassTerm : Ball := .exact 0
def CB1_6_1I2R10H : Ball := ⟨0, 0⟩
def CB1_6_1I2R11Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 6 1)) (fun u => (stageBLaw (shape 1 6 1) u : ℝ)) (stageBPriority (shape 1 6 1)) 2 (fun u a => (littleLaw (shape 1 6 1) u ((stageBPriority (shape 1 6 1)) 2) a : ℝ)) 11 a
def CB1_6_1I2R11Entropy : Ball := ⟨0, 0⟩
def CB1_6_1I2R11Mass : Ball := ⟨0, 0⟩
def CB1_6_1I2R11MassTerm : Ball := .exact 0
def CB1_6_1I2R11H : Ball := ⟨0, 0⟩
def CB1_6_1I2R12Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 6 1)) (fun u => (stageBLaw (shape 1 6 1) u : ℝ)) (stageBPriority (shape 1 6 1)) 2 (fun u a => (littleLaw (shape 1 6 1) u ((stageBPriority (shape 1 6 1)) 2) a : ℝ)) 12 a
def CB1_6_1I2R12Entropy : Ball := ⟨0, 0⟩
def CB1_6_1I2R12Mass : Ball := ⟨0, 0⟩
def CB1_6_1I2R12MassTerm : Ball := .exact 0
def CB1_6_1I2R12H : Ball := ⟨0, 0⟩
def CB1_6_1I2R13Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 6 1)) (fun u => (stageBLaw (shape 1 6 1) u : ℝ)) (stageBPriority (shape 1 6 1)) 2 (fun u a => (littleLaw (shape 1 6 1) u ((stageBPriority (shape 1 6 1)) 2) a : ℝ)) 13 a
def CB1_6_1I2R13Entropy : Ball := ⟨0, 0⟩
def CB1_6_1I2R13Mass : Ball := ⟨0, 0⟩
def CB1_6_1I2R13MassTerm : Ball := .exact 0
def CB1_6_1I2R13H : Ball := ⟨0, 0⟩
def CB1_6_1I2R14Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 6 1)) (fun u => (stageBLaw (shape 1 6 1) u : ℝ)) (stageBPriority (shape 1 6 1)) 2 (fun u a => (littleLaw (shape 1 6 1) u ((stageBPriority (shape 1 6 1)) 2) a : ℝ)) 14 a
def CB1_6_1I2R14Entropy : Ball := ⟨0, 0⟩
def CB1_6_1I2R14Mass : Ball := ⟨0, 0⟩
def CB1_6_1I2R14MassTerm : Ball := .exact 0
def CB1_6_1I2R14H : Ball := ⟨0, 0⟩
def CB1_6_1I2R15Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 6 1)) (fun u => (stageBLaw (shape 1 6 1) u : ℝ)) (stageBPriority (shape 1 6 1)) 2 (fun u a => (littleLaw (shape 1 6 1) u ((stageBPriority (shape 1 6 1)) 2) a : ℝ)) 15 a
def CB1_6_1I2R15Entropy : Ball := ⟨0, 0⟩
def CB1_6_1I2R15Mass : Ball := ⟨0, 0⟩
def CB1_6_1I2R15MassTerm : Ball := .exact 0
def CB1_6_1I2R15H : Ball := ⟨0, 0⟩
def CB1_6_1I2R16Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 6 1)) (fun u => (stageBLaw (shape 1 6 1) u : ℝ)) (stageBPriority (shape 1 6 1)) 2 (fun u a => (littleLaw (shape 1 6 1) u ((stageBPriority (shape 1 6 1)) 2) a : ℝ)) 16 a
def CB1_6_1I2R16Entropy : Ball := ⟨0, 0⟩
def CB1_6_1I2R16Mass : Ball := ⟨0, 0⟩
def CB1_6_1I2R16MassTerm : Ball := .exact 0
def CB1_6_1I2R16H : Ball := ⟨0, 0⟩
def CB1_6_1I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CB1_6_1I2R0H
  | 1 => CB1_6_1I2R1H
  | 2 => CB1_6_1I2R2H
  | 3 => CB1_6_1I2R3H
  | 4 => CB1_6_1I2R4H
  | 5 => CB1_6_1I2R5H
  | 6 => CB1_6_1I2R6H
  | 7 => CB1_6_1I2R7H
  | 8 => CB1_6_1I2R8H
  | 9 => CB1_6_1I2R9H
  | 10 => CB1_6_1I2R10H
  | 11 => CB1_6_1I2R11H
  | 12 => CB1_6_1I2R12H
  | 13 => CB1_6_1I2R13H
  | 14 => CB1_6_1I2R14H
  | 15 => CB1_6_1I2R15H
  | 16 => CB1_6_1I2R16H
  | _ => (.exact 0)
def CB1_6_1I2S0_3_1Value (a : Fin 6) : ℝ := (littleLaw (shape 1 6 1) (shape 0 3 1) ((stageBPriority (shape 1 6 1)) 2) a : ℝ)
def CB1_6_1I2S0_3_1E_4Log : Ball := .exact 0
def CB1_6_1I2S0_3_1E_4 : Ball := ⟨0, 0⟩
def CB1_6_1I2S0_3_1Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB1_6_1I2S0_3_1Entropy : Ball := ⟨0, 0⟩
def CB1_6_1I2S0_3_1Mass : Ball := ⟨1, 0⟩
def CB1_6_1I2S0_3_1MassTermLog : Ball := .exact 0
def CB1_6_1I2S0_3_1MassTerm : Ball := ⟨0, 0⟩
def CB1_6_1I2S0_3_1H : Ball := ⟨0, 0⟩
def CB1_6_1I2S0_4_0Value (a : Fin 6) : ℝ := (littleLaw (shape 1 6 1) (shape 0 4 0) ((stageBPriority (shape 1 6 1)) 2) a : ℝ)
def CB1_6_1I2S0_4_0E_5Log : Ball := .exact 0
def CB1_6_1I2S0_4_0E_5 : Ball := ⟨0, 0⟩
def CB1_6_1I2S0_4_0Terms (a : Fin 6) : Ball :=
  match a.val with
  | 5 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB1_6_1I2S0_4_0Entropy : Ball := ⟨0, 0⟩
def CB1_6_1I2S0_4_0Mass : Ball := ⟨1, 0⟩
def CB1_6_1I2S0_4_0MassTermLog : Ball := .exact 0
def CB1_6_1I2S0_4_0MassTerm : Ball := ⟨0, 0⟩
def CB1_6_1I2S0_4_0H : Ball := ⟨0, 0⟩
def CB1_6_1I2S1_3_0Value (a : Fin 6) : ℝ := (littleLaw (shape 1 6 1) (shape 1 3 0) ((stageBPriority (shape 1 6 1)) 2) a : ℝ)
def CB1_6_1I2S1_3_0E_4Log : Ball := .exact 0
def CB1_6_1I2S1_3_0E_4 : Ball := ⟨0, 0⟩
def CB1_6_1I2S1_3_0Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB1_6_1I2S1_3_0Entropy : Ball := ⟨0, 0⟩
def CB1_6_1I2S1_3_0Mass : Ball := ⟨1, 0⟩
def CB1_6_1I2S1_3_0MassTermLog : Ball := .exact 0
def CB1_6_1I2S1_3_0MassTerm : Ball := ⟨0, 0⟩
def CB1_6_1I2S1_3_0H : Ball := ⟨0, 0⟩
def CB1_6_1I2Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 3, 1 => CB1_6_1I2S0_3_1H
  | 0, 4, 0 => CB1_6_1I2S0_4_0H
  | 1, 3, 0 => CB1_6_1I2S1_3_0H
  | _, _, _ => (.exact 0)
def CB1_6_1I2Singleton : Ball := ⟨0, 0⟩
def CB1_6_1I2Group : Ball := ⟨(2065143764242494166405890297321 / 100000000000000000000000000000000), (12761288021 / 50000000000000000000000000000000)⟩

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
def CB1_6_1I2H : Ball := ⟨(35600351325807200116638239804507 / 50000000000000000000000000000000), (130476417237 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB2_1_5I0
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
def CB2_1_5I0Value (a : Fin 17) : ℝ := marginal (below (shape 2 1 5)) (fun u => (stageBLaw (shape 2 1 5) u : ℝ)) ((stageBPriority (shape 2 1 5)) 0) a
def CB2_1_5I0Entropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (10587911883 / 25000000000000000000000000000000)⟩
def CB2_1_5I0Mass : Ball := ⟨1, (49 / 50000000000000000000000000000000)⟩
def CB2_1_5I0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB2_1_5I0MassTermLog : Ball := ⟨0, (1058791189 / 5000000000000000000000000000000)⟩
def CB2_1_5I0MassTerm : Ball := ⟨0, (21175823781 / 100000000000000000000000000000000)⟩
def CB2_1_5I0H : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (63527471313 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB2_1_5I1
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
def CB2_1_5I1PairEntropy : Ball := ⟨(25758658807311872438505605593739 / 25000000000000000000000000000000), (15051072369 / 25000000000000000000000000000000)⟩
def CB2_1_5I1PairMass : Ball := ⟨1, (51 / 50000000000000000000000000000000)⟩
def CB2_1_5I1PairMassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB2_1_5I1PairMassTermLog : Ball := ⟨0, (2646977973 / 12500000000000000000000000000000)⟩
def CB2_1_5I1PairMassTerm : Ball := ⟨0, (4235164757 / 20000000000000000000000000000000)⟩
def CB2_1_5I1PairH : Ball := ⟨(25758658807311872438505605593739 / 25000000000000000000000000000000), (81380113261 / 100000000000000000000000000000000)⟩

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
def CB2_1_5I1R0Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 1 5)) (fun u => (stageBLaw (shape 2 1 5) u : ℝ)) (stageBPriority (shape 2 1 5)) 1 (fun u a => (littleLaw (shape 2 1 5) u ((stageBPriority (shape 2 1 5)) 1) a : ℝ)) 0 a
def CB2_1_5I1R0Entropy : Ball := ⟨(31092011736610680071881277157671 / 100000000000000000000000000000000), (3879329603 / 25000000000000000000000000000000)⟩
def CB2_1_5I1R0Mass : Ball := ⟨(4579903996636975901019875225137 / 25000000000000000000000000000000), (33 / 100000000000000000000000000000000)⟩
def CB2_1_5I1R0MassTermLogWitness : LogWitness := ⟨-3, 4579903996636975901019875225137, 3125000000000000000000000000000⟩
def CB2_1_5I1R0MassTermLog : Ball := ⟨(-169719778839477575972721710038793 / 100000000000000000000000000000000), (1323488983 / 1562500000000000000000000000000)⟩
def CB2_1_5I1R0MassTerm : Ball := ⟨(31092011736610680071881277157671 / 100000000000000000000000000000000), (3879329603 / 25000000000000000000000000000000)⟩
def CB2_1_5I1R0H : Ball := ⟨0, (3879329603 / 12500000000000000000000000000000)⟩
def CB2_1_5I1R1Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 1 5)) (fun u => (stageBLaw (shape 2 1 5) u : ℝ)) (stageBPriority (shape 2 1 5)) 1 (fun u a => (littleLaw (shape 2 1 5) u ((stageBPriority (shape 2 1 5)) 1) a : ℝ)) 1 a
def CB2_1_5I1R1Entropy : Ball := ⟨(7228280637521402636754794374159 / 25000000000000000000000000000000), (2683432909 / 10000000000000000000000000000000)⟩
def CB2_1_5I1R1Mass : Ball := ⟨(7920096003363024098980124774863 / 12500000000000000000000000000000), (1 / 3125000000000000000000000000000)⟩
def CB2_1_5I1R1MassTermLogWitness : LogWitness := ⟨-1, 7920096003363024098980124774863, 6250000000000000000000000000000⟩
def CB2_1_5I1R1MassTermLog : Ball := ⟨(-9126506338372838613585647245343 / 20000000000000000000000000000000), (5293955927 / 12500000000000000000000000000000)⟩
def CB2_1_5I1R1MassTerm : Ball := ⟨(7228280637521402636754794374159 / 25000000000000000000000000000000), (2683432909 / 10000000000000000000000000000000)⟩
def CB2_1_5I1R1H : Ball := ⟨0, (2683432909 / 5000000000000000000000000000000)⟩
def CB2_1_5I1R2Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 1 5)) (fun u => (stageBLaw (shape 2 1 5) u : ℝ)) (stageBPriority (shape 2 1 5)) 1 (fun u a => (littleLaw (shape 2 1 5) u ((stageBPriority (shape 2 1 5)) 1) a : ℝ)) 2 a
def CB2_1_5I1R2Entropy : Ball := ⟨(926518908489523490087540560979 / 2500000000000000000000000000000), (16684980193 / 100000000000000000000000000000000)⟩
def CB2_1_5I1R2Mass : Ball := ⟨(4579903996636975901019875225137 / 25000000000000000000000000000000), (7 / 20000000000000000000000000000000)⟩
def CB2_1_5I1R2MassTermLogWitness : LogWitness := ⟨-3, 4579903996636975901019875225137, 3125000000000000000000000000000⟩
def CB2_1_5I1R2MassTermLog : Ball := ⟨(-169719778839477575972721710038793 / 100000000000000000000000000000000), (42351647461 / 50000000000000000000000000000000)⟩
def CB2_1_5I1R2MassTerm : Ball := ⟨(31092011736610680071881277157671 / 100000000000000000000000000000000), (7758659209 / 50000000000000000000000000000000)⟩
def CB2_1_5I1R2H : Ball := ⟨(5968744602970259531620345281489 / 100000000000000000000000000000000), (32202298611 / 100000000000000000000000000000000)⟩
def CB2_1_5I1R3Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 1 5)) (fun u => (stageBLaw (shape 2 1 5) u : ℝ)) (stageBPriority (shape 2 1 5)) 1 (fun u a => (littleLaw (shape 2 1 5) u ((stageBPriority (shape 2 1 5)) 1) a : ℝ)) 3 a
def CB2_1_5I1R3Entropy : Ball := ⟨0, 0⟩
def CB2_1_5I1R3Mass : Ball := ⟨0, 0⟩
def CB2_1_5I1R3MassTerm : Ball := .exact 0
def CB2_1_5I1R3H : Ball := ⟨0, 0⟩
def CB2_1_5I1R4Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 1 5)) (fun u => (stageBLaw (shape 2 1 5) u : ℝ)) (stageBPriority (shape 2 1 5)) 1 (fun u a => (littleLaw (shape 2 1 5) u ((stageBPriority (shape 2 1 5)) 1) a : ℝ)) 4 a
def CB2_1_5I1R4Entropy : Ball := ⟨0, 0⟩
def CB2_1_5I1R4Mass : Ball := ⟨0, 0⟩
def CB2_1_5I1R4MassTerm : Ball := .exact 0
def CB2_1_5I1R4H : Ball := ⟨0, 0⟩
def CB2_1_5I1R5Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 1 5)) (fun u => (stageBLaw (shape 2 1 5) u : ℝ)) (stageBPriority (shape 2 1 5)) 1 (fun u a => (littleLaw (shape 2 1 5) u ((stageBPriority (shape 2 1 5)) 1) a : ℝ)) 5 a
def CB2_1_5I1R5Entropy : Ball := ⟨0, 0⟩
def CB2_1_5I1R5Mass : Ball := ⟨0, 0⟩
def CB2_1_5I1R5MassTerm : Ball := .exact 0
def CB2_1_5I1R5H : Ball := ⟨0, 0⟩
def CB2_1_5I1R6Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 1 5)) (fun u => (stageBLaw (shape 2 1 5) u : ℝ)) (stageBPriority (shape 2 1 5)) 1 (fun u a => (littleLaw (shape 2 1 5) u ((stageBPriority (shape 2 1 5)) 1) a : ℝ)) 6 a
def CB2_1_5I1R6Entropy : Ball := ⟨0, 0⟩
def CB2_1_5I1R6Mass : Ball := ⟨0, 0⟩
def CB2_1_5I1R6MassTerm : Ball := .exact 0
def CB2_1_5I1R6H : Ball := ⟨0, 0⟩
def CB2_1_5I1R7Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 1 5)) (fun u => (stageBLaw (shape 2 1 5) u : ℝ)) (stageBPriority (shape 2 1 5)) 1 (fun u a => (littleLaw (shape 2 1 5) u ((stageBPriority (shape 2 1 5)) 1) a : ℝ)) 7 a
def CB2_1_5I1R7Entropy : Ball := ⟨0, 0⟩
def CB2_1_5I1R7Mass : Ball := ⟨0, 0⟩
def CB2_1_5I1R7MassTerm : Ball := .exact 0
def CB2_1_5I1R7H : Ball := ⟨0, 0⟩
def CB2_1_5I1R8Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 1 5)) (fun u => (stageBLaw (shape 2 1 5) u : ℝ)) (stageBPriority (shape 2 1 5)) 1 (fun u a => (littleLaw (shape 2 1 5) u ((stageBPriority (shape 2 1 5)) 1) a : ℝ)) 8 a
def CB2_1_5I1R8Entropy : Ball := ⟨0, 0⟩
def CB2_1_5I1R8Mass : Ball := ⟨0, 0⟩
def CB2_1_5I1R8MassTerm : Ball := .exact 0
def CB2_1_5I1R8H : Ball := ⟨0, 0⟩
def CB2_1_5I1R9Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 1 5)) (fun u => (stageBLaw (shape 2 1 5) u : ℝ)) (stageBPriority (shape 2 1 5)) 1 (fun u a => (littleLaw (shape 2 1 5) u ((stageBPriority (shape 2 1 5)) 1) a : ℝ)) 9 a
def CB2_1_5I1R9Entropy : Ball := ⟨0, 0⟩
def CB2_1_5I1R9Mass : Ball := ⟨0, 0⟩
def CB2_1_5I1R9MassTerm : Ball := .exact 0
def CB2_1_5I1R9H : Ball := ⟨0, 0⟩
def CB2_1_5I1R10Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 1 5)) (fun u => (stageBLaw (shape 2 1 5) u : ℝ)) (stageBPriority (shape 2 1 5)) 1 (fun u a => (littleLaw (shape 2 1 5) u ((stageBPriority (shape 2 1 5)) 1) a : ℝ)) 10 a
def CB2_1_5I1R10Entropy : Ball := ⟨0, 0⟩
def CB2_1_5I1R10Mass : Ball := ⟨0, 0⟩
def CB2_1_5I1R10MassTerm : Ball := .exact 0
def CB2_1_5I1R10H : Ball := ⟨0, 0⟩
def CB2_1_5I1R11Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 1 5)) (fun u => (stageBLaw (shape 2 1 5) u : ℝ)) (stageBPriority (shape 2 1 5)) 1 (fun u a => (littleLaw (shape 2 1 5) u ((stageBPriority (shape 2 1 5)) 1) a : ℝ)) 11 a
def CB2_1_5I1R11Entropy : Ball := ⟨0, 0⟩
def CB2_1_5I1R11Mass : Ball := ⟨0, 0⟩
def CB2_1_5I1R11MassTerm : Ball := .exact 0
def CB2_1_5I1R11H : Ball := ⟨0, 0⟩
def CB2_1_5I1R12Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 1 5)) (fun u => (stageBLaw (shape 2 1 5) u : ℝ)) (stageBPriority (shape 2 1 5)) 1 (fun u a => (littleLaw (shape 2 1 5) u ((stageBPriority (shape 2 1 5)) 1) a : ℝ)) 12 a
def CB2_1_5I1R12Entropy : Ball := ⟨0, 0⟩
def CB2_1_5I1R12Mass : Ball := ⟨0, 0⟩
def CB2_1_5I1R12MassTerm : Ball := .exact 0
def CB2_1_5I1R12H : Ball := ⟨0, 0⟩
def CB2_1_5I1R13Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 1 5)) (fun u => (stageBLaw (shape 2 1 5) u : ℝ)) (stageBPriority (shape 2 1 5)) 1 (fun u a => (littleLaw (shape 2 1 5) u ((stageBPriority (shape 2 1 5)) 1) a : ℝ)) 13 a
def CB2_1_5I1R13Entropy : Ball := ⟨0, 0⟩
def CB2_1_5I1R13Mass : Ball := ⟨0, 0⟩
def CB2_1_5I1R13MassTerm : Ball := .exact 0
def CB2_1_5I1R13H : Ball := ⟨0, 0⟩
def CB2_1_5I1R14Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 1 5)) (fun u => (stageBLaw (shape 2 1 5) u : ℝ)) (stageBPriority (shape 2 1 5)) 1 (fun u a => (littleLaw (shape 2 1 5) u ((stageBPriority (shape 2 1 5)) 1) a : ℝ)) 14 a
def CB2_1_5I1R14Entropy : Ball := ⟨0, 0⟩
def CB2_1_5I1R14Mass : Ball := ⟨0, 0⟩
def CB2_1_5I1R14MassTerm : Ball := .exact 0
def CB2_1_5I1R14H : Ball := ⟨0, 0⟩
def CB2_1_5I1R15Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 1 5)) (fun u => (stageBLaw (shape 2 1 5) u : ℝ)) (stageBPriority (shape 2 1 5)) 1 (fun u a => (littleLaw (shape 2 1 5) u ((stageBPriority (shape 2 1 5)) 1) a : ℝ)) 15 a
def CB2_1_5I1R15Entropy : Ball := ⟨0, 0⟩
def CB2_1_5I1R15Mass : Ball := ⟨0, 0⟩
def CB2_1_5I1R15MassTerm : Ball := .exact 0
def CB2_1_5I1R15H : Ball := ⟨0, 0⟩
def CB2_1_5I1R16Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 1 5)) (fun u => (stageBLaw (shape 2 1 5) u : ℝ)) (stageBPriority (shape 2 1 5)) 1 (fun u a => (littleLaw (shape 2 1 5) u ((stageBPriority (shape 2 1 5)) 1) a : ℝ)) 16 a
def CB2_1_5I1R16Entropy : Ball := ⟨0, 0⟩
def CB2_1_5I1R16Mass : Ball := ⟨0, 0⟩
def CB2_1_5I1R16MassTerm : Ball := .exact 0
def CB2_1_5I1R16H : Ball := ⟨0, 0⟩
def CB2_1_5I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CB2_1_5I1R0H
  | 1 => CB2_1_5I1R1H
  | 2 => CB2_1_5I1R2H
  | 3 => CB2_1_5I1R3H
  | 4 => CB2_1_5I1R4H
  | 5 => CB2_1_5I1R5H
  | 6 => CB2_1_5I1R6H
  | 7 => CB2_1_5I1R7H
  | 8 => CB2_1_5I1R8H
  | 9 => CB2_1_5I1R9H
  | 10 => CB2_1_5I1R10H
  | 11 => CB2_1_5I1R11H
  | 12 => CB2_1_5I1R12H
  | 13 => CB2_1_5I1R13H
  | 14 => CB2_1_5I1R14H
  | 15 => CB2_1_5I1R15H
  | 16 => CB2_1_5I1R16H
  | _ => (.exact 0)
def CB2_1_5I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | _, _, _ => (.exact 0)
def CB2_1_5I1Singleton : Ball := ⟨0, 0⟩
def CB2_1_5I1Group : Ball := ⟨(5968744602970259531620345281489 / 100000000000000000000000000000000), (23381118723 / 20000000000000000000000000000000)⟩

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
def CB2_1_5I1H : Ball := ⟨(45548573011653485345390865905989 / 50000000000000000000000000000000), (315191300491 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB2_1_5I2
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
def CB2_1_5I2PairEntropy : Ball := ⟨(10795367978625769694970750708457 / 12500000000000000000000000000000), (8372663363 / 12500000000000000000000000000000)⟩
def CB2_1_5I2PairMass : Ball := ⟨1, (51 / 50000000000000000000000000000000)⟩
def CB2_1_5I2PairMassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB2_1_5I2PairMassTermLog : Ball := ⟨0, (2646977973 / 12500000000000000000000000000000)⟩
def CB2_1_5I2PairMassTerm : Ball := ⟨0, (4235164757 / 20000000000000000000000000000000)⟩
def CB2_1_5I2PairH : Ball := ⟨(10795367978625769694970750708457 / 12500000000000000000000000000000), (88157130689 / 100000000000000000000000000000000)⟩

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
def CB2_1_5I2R0Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 1 5)) (fun u => (stageBLaw (shape 2 1 5) u : ℝ)) (stageBPriority (shape 2 1 5)) 2 (fun u a => (littleLaw (shape 2 1 5) u ((stageBPriority (shape 2 1 5)) 2) a : ℝ)) 0 a
def CB2_1_5I2R0Entropy : Ball := ⟨0, 0⟩
def CB2_1_5I2R0Mass : Ball := ⟨0, 0⟩
def CB2_1_5I2R0MassTerm : Ball := .exact 0
def CB2_1_5I2R0H : Ball := ⟨0, 0⟩
def CB2_1_5I2R1Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 1 5)) (fun u => (stageBLaw (shape 2 1 5) u : ℝ)) (stageBPriority (shape 2 1 5)) 2 (fun u a => (littleLaw (shape 2 1 5) u ((stageBPriority (shape 2 1 5)) 2) a : ℝ)) 1 a
def CB2_1_5I2R1Entropy : Ball := ⟨(15915961829956415895565101573 / 2500000000000000000000000000000), (28875921 / 12500000000000000000000000000000)⟩
def CB2_1_5I2R1Mass : Ball := ⟨(45454225515120282149964459091 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def CB2_1_5I2R1MassTermLogWitness : LogWitness := ⟨-11, 45454225515120282149964459091, 24414062500000000000000000000⟩
def CB2_1_5I2R1MassTermLog : Ball := ⟨(-350153624873929362004825628773133 / 50000000000000000000000000000000), (15881867831 / 6250000000000000000000000000000)⟩
def CB2_1_5I2R1MassTerm : Ball := ⟨(15915961829956415895565101573 / 2500000000000000000000000000000), (28875921 / 12500000000000000000000000000000)⟩
def CB2_1_5I2R1H : Ball := ⟨0, (28875921 / 6250000000000000000000000000000)⟩
def CB2_1_5I2R2Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 1 5)) (fun u => (stageBLaw (shape 2 1 5) u : ℝ)) (stageBPriority (shape 2 1 5)) 2 (fun u a => (littleLaw (shape 2 1 5) u ((stageBPriority (shape 2 1 5)) 2) a : ℝ)) 2 a
def CB2_1_5I2R2Entropy : Ball := ⟨(36416199494071481849150495475937 / 100000000000000000000000000000000), (1257867563 / 6250000000000000000000000000000)⟩
def CB2_1_5I2R2Mass : Ball := ⟨(7920096003363024098980124774863 / 25000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
def CB2_1_5I2R2MassTermLogWitness : LogWitness := ⟨-2, 7920096003363024098980124774863, 6250000000000000000000000000000⟩
def CB2_1_5I2R2MassTermLog : Ball := ⟨(-22989449949571744801930285855409 / 20000000000000000000000000000000), (12705494221 / 20000000000000000000000000000000)⟩
def CB2_1_5I2R2MassTerm : Ball := ⟨(1456629205320939615371968330297 / 4000000000000000000000000000000), (10062873411 / 50000000000000000000000000000000)⟩
def CB2_1_5I2R2H : Ball := ⟨(29335065499466553205451157 / 6250000000000000000000000000000), (4025162783 / 10000000000000000000000000000000)⟩
def CB2_1_5I2R3Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 1 5)) (fun u => (stageBLaw (shape 2 1 5) u : ℝ)) (stageBPriority (shape 2 1 5)) 2 (fun u a => (littleLaw (shape 2 1 5) u ((stageBPriority (shape 2 1 5)) 2) a : ℝ)) 3 a
def CB2_1_5I2R3Entropy : Ball := ⟨0, 0⟩
def CB2_1_5I2R3Mass : Ball := ⟨0, 0⟩
def CB2_1_5I2R3MassTerm : Ball := .exact 0
def CB2_1_5I2R3H : Ball := ⟨0, 0⟩
def CB2_1_5I2R4Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 1 5)) (fun u => (stageBLaw (shape 2 1 5) u : ℝ)) (stageBPriority (shape 2 1 5)) 2 (fun u a => (littleLaw (shape 2 1 5) u ((stageBPriority (shape 2 1 5)) 2) a : ℝ)) 4 a
def CB2_1_5I2R4Entropy : Ball := ⟨0, 0⟩
def CB2_1_5I2R4Mass : Ball := ⟨0, 0⟩
def CB2_1_5I2R4MassTerm : Ball := .exact 0
def CB2_1_5I2R4H : Ball := ⟨0, 0⟩
def CB2_1_5I2R5Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 1 5)) (fun u => (stageBLaw (shape 2 1 5) u : ℝ)) (stageBPriority (shape 2 1 5)) 2 (fun u a => (littleLaw (shape 2 1 5) u ((stageBPriority (shape 2 1 5)) 2) a : ℝ)) 5 a
def CB2_1_5I2R5Entropy : Ball := ⟨0, 0⟩
def CB2_1_5I2R5Mass : Ball := ⟨0, 0⟩
def CB2_1_5I2R5MassTerm : Ball := .exact 0
def CB2_1_5I2R5H : Ball := ⟨0, 0⟩
def CB2_1_5I2R6Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 1 5)) (fun u => (stageBLaw (shape 2 1 5) u : ℝ)) (stageBPriority (shape 2 1 5)) 2 (fun u a => (littleLaw (shape 2 1 5) u ((stageBPriority (shape 2 1 5)) 2) a : ℝ)) 6 a
def CB2_1_5I2R6Entropy : Ball := ⟨0, 0⟩
def CB2_1_5I2R6Mass : Ball := ⟨0, 0⟩
def CB2_1_5I2R6MassTerm : Ball := .exact 0
def CB2_1_5I2R6H : Ball := ⟨0, 0⟩
def CB2_1_5I2R7Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 1 5)) (fun u => (stageBLaw (shape 2 1 5) u : ℝ)) (stageBPriority (shape 2 1 5)) 2 (fun u a => (littleLaw (shape 2 1 5) u ((stageBPriority (shape 2 1 5)) 2) a : ℝ)) 7 a
def CB2_1_5I2R7Entropy : Ball := ⟨0, 0⟩
def CB2_1_5I2R7Mass : Ball := ⟨0, 0⟩
def CB2_1_5I2R7MassTerm : Ball := .exact 0
def CB2_1_5I2R7H : Ball := ⟨0, 0⟩
def CB2_1_5I2R8Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 1 5)) (fun u => (stageBLaw (shape 2 1 5) u : ℝ)) (stageBPriority (shape 2 1 5)) 2 (fun u a => (littleLaw (shape 2 1 5) u ((stageBPriority (shape 2 1 5)) 2) a : ℝ)) 8 a
def CB2_1_5I2R8Entropy : Ball := ⟨0, 0⟩
def CB2_1_5I2R8Mass : Ball := ⟨0, 0⟩
def CB2_1_5I2R8MassTerm : Ball := .exact 0
def CB2_1_5I2R8H : Ball := ⟨0, 0⟩
def CB2_1_5I2R9Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 1 5)) (fun u => (stageBLaw (shape 2 1 5) u : ℝ)) (stageBPriority (shape 2 1 5)) 2 (fun u a => (littleLaw (shape 2 1 5) u ((stageBPriority (shape 2 1 5)) 2) a : ℝ)) 9 a
def CB2_1_5I2R9Entropy : Ball := ⟨0, 0⟩
def CB2_1_5I2R9Mass : Ball := ⟨0, 0⟩
def CB2_1_5I2R9MassTerm : Ball := .exact 0
def CB2_1_5I2R9H : Ball := ⟨0, 0⟩
def CB2_1_5I2R10Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 1 5)) (fun u => (stageBLaw (shape 2 1 5) u : ℝ)) (stageBPriority (shape 2 1 5)) 2 (fun u a => (littleLaw (shape 2 1 5) u ((stageBPriority (shape 2 1 5)) 2) a : ℝ)) 10 a
def CB2_1_5I2R10Entropy : Ball := ⟨0, 0⟩
def CB2_1_5I2R10Mass : Ball := ⟨0, 0⟩
def CB2_1_5I2R10MassTerm : Ball := .exact 0
def CB2_1_5I2R10H : Ball := ⟨0, 0⟩
def CB2_1_5I2R11Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 1 5)) (fun u => (stageBLaw (shape 2 1 5) u : ℝ)) (stageBPriority (shape 2 1 5)) 2 (fun u a => (littleLaw (shape 2 1 5) u ((stageBPriority (shape 2 1 5)) 2) a : ℝ)) 11 a
def CB2_1_5I2R11Entropy : Ball := ⟨0, 0⟩
def CB2_1_5I2R11Mass : Ball := ⟨0, 0⟩
def CB2_1_5I2R11MassTerm : Ball := .exact 0
def CB2_1_5I2R11H : Ball := ⟨0, 0⟩
def CB2_1_5I2R12Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 1 5)) (fun u => (stageBLaw (shape 2 1 5) u : ℝ)) (stageBPriority (shape 2 1 5)) 2 (fun u a => (littleLaw (shape 2 1 5) u ((stageBPriority (shape 2 1 5)) 2) a : ℝ)) 12 a
def CB2_1_5I2R12Entropy : Ball := ⟨0, 0⟩
def CB2_1_5I2R12Mass : Ball := ⟨0, 0⟩
def CB2_1_5I2R12MassTerm : Ball := .exact 0
def CB2_1_5I2R12H : Ball := ⟨0, 0⟩
def CB2_1_5I2R13Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 1 5)) (fun u => (stageBLaw (shape 2 1 5) u : ℝ)) (stageBPriority (shape 2 1 5)) 2 (fun u a => (littleLaw (shape 2 1 5) u ((stageBPriority (shape 2 1 5)) 2) a : ℝ)) 13 a
def CB2_1_5I2R13Entropy : Ball := ⟨0, 0⟩
def CB2_1_5I2R13Mass : Ball := ⟨0, 0⟩
def CB2_1_5I2R13MassTerm : Ball := .exact 0
def CB2_1_5I2R13H : Ball := ⟨0, 0⟩
def CB2_1_5I2R14Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 1 5)) (fun u => (stageBLaw (shape 2 1 5) u : ℝ)) (stageBPriority (shape 2 1 5)) 2 (fun u a => (littleLaw (shape 2 1 5) u ((stageBPriority (shape 2 1 5)) 2) a : ℝ)) 14 a
def CB2_1_5I2R14Entropy : Ball := ⟨0, 0⟩
def CB2_1_5I2R14Mass : Ball := ⟨0, 0⟩
def CB2_1_5I2R14MassTerm : Ball := .exact 0
def CB2_1_5I2R14H : Ball := ⟨0, 0⟩
def CB2_1_5I2R15Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 1 5)) (fun u => (stageBLaw (shape 2 1 5) u : ℝ)) (stageBPriority (shape 2 1 5)) 2 (fun u a => (littleLaw (shape 2 1 5) u ((stageBPriority (shape 2 1 5)) 2) a : ℝ)) 15 a
def CB2_1_5I2R15Entropy : Ball := ⟨0, 0⟩
def CB2_1_5I2R15Mass : Ball := ⟨0, 0⟩
def CB2_1_5I2R15MassTerm : Ball := .exact 0
def CB2_1_5I2R15H : Ball := ⟨0, 0⟩
def CB2_1_5I2R16Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 1 5)) (fun u => (stageBLaw (shape 2 1 5) u : ℝ)) (stageBPriority (shape 2 1 5)) 2 (fun u a => (littleLaw (shape 2 1 5) u ((stageBPriority (shape 2 1 5)) 2) a : ℝ)) 16 a
def CB2_1_5I2R16Entropy : Ball := ⟨0, 0⟩
def CB2_1_5I2R16Mass : Ball := ⟨0, 0⟩
def CB2_1_5I2R16MassTerm : Ball := .exact 0
def CB2_1_5I2R16H : Ball := ⟨0, 0⟩
def CB2_1_5I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CB2_1_5I2R0H
  | 1 => CB2_1_5I2R1H
  | 2 => CB2_1_5I2R2H
  | 3 => CB2_1_5I2R3H
  | 4 => CB2_1_5I2R4H
  | 5 => CB2_1_5I2R5H
  | 6 => CB2_1_5I2R6H
  | 7 => CB2_1_5I2R7H
  | 8 => CB2_1_5I2R8H
  | 9 => CB2_1_5I2R9H
  | 10 => CB2_1_5I2R10H
  | 11 => CB2_1_5I2R11H
  | 12 => CB2_1_5I2R12H
  | 13 => CB2_1_5I2R13H
  | 14 => CB2_1_5I2R14H
  | 15 => CB2_1_5I2R15H
  | 16 => CB2_1_5I2R16H
  | _ => (.exact 0)
def CB2_1_5I2S0_0_4Value (a : Fin 6) : ℝ := (littleLaw (shape 2 1 5) (shape 0 0 4) ((stageBPriority (shape 2 1 5)) 2) a : ℝ)
def CB2_1_5I2S0_0_4E_5Log : Ball := .exact 0
def CB2_1_5I2S0_0_4E_5 : Ball := ⟨0, 0⟩
def CB2_1_5I2S0_0_4Terms (a : Fin 6) : Ball :=
  match a.val with
  | 5 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB2_1_5I2S0_0_4Entropy : Ball := ⟨0, 0⟩
def CB2_1_5I2S0_0_4Mass : Ball := ⟨1, 0⟩
def CB2_1_5I2S0_0_4MassTermLog : Ball := .exact 0
def CB2_1_5I2S0_0_4MassTerm : Ball := ⟨0, 0⟩
def CB2_1_5I2S0_0_4H : Ball := ⟨0, 0⟩
def CB2_1_5I2S0_1_3Value (a : Fin 6) : ℝ := (littleLaw (shape 2 1 5) (shape 0 1 3) ((stageBPriority (shape 2 1 5)) 2) a : ℝ)
def CB2_1_5I2S0_1_3E_4Log : Ball := .exact 0
def CB2_1_5I2S0_1_3E_4 : Ball := ⟨0, 0⟩
def CB2_1_5I2S0_1_3Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB2_1_5I2S0_1_3Entropy : Ball := ⟨0, 0⟩
def CB2_1_5I2S0_1_3Mass : Ball := ⟨1, 0⟩
def CB2_1_5I2S0_1_3MassTermLog : Ball := .exact 0
def CB2_1_5I2S0_1_3MassTerm : Ball := ⟨0, 0⟩
def CB2_1_5I2S0_1_3H : Ball := ⟨0, 0⟩
def CB2_1_5I2S1_0_3Value (a : Fin 6) : ℝ := (littleLaw (shape 2 1 5) (shape 1 0 3) ((stageBPriority (shape 2 1 5)) 2) a : ℝ)
def CB2_1_5I2S1_0_3E_4Log : Ball := .exact 0
def CB2_1_5I2S1_0_3E_4 : Ball := ⟨0, 0⟩
def CB2_1_5I2S1_0_3Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB2_1_5I2S1_0_3Entropy : Ball := ⟨0, 0⟩
def CB2_1_5I2S1_0_3Mass : Ball := ⟨1, 0⟩
def CB2_1_5I2S1_0_3MassTermLog : Ball := .exact 0
def CB2_1_5I2S1_0_3MassTerm : Ball := ⟨0, 0⟩
def CB2_1_5I2S1_0_3H : Ball := ⟨0, 0⟩
def CB2_1_5I2S2_0_2Value (a : Fin 6) : ℝ := (littleLaw (shape 2 1 5) (shape 2 0 2) ((stageBPriority (shape 2 1 5)) 2) a : ℝ)
def CB2_1_5I2S2_0_2E_2LogWitness : LogWitness := ⟨-1, 449689, 250000⟩
def CB2_1_5I2S2_0_2E_2Log : Ball := ⟨(-2651296642407782012789413805853 / 25000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def CB2_1_5I2S2_0_2E_2 : Ball := ⟨(4769035743310852342197034819761 / 50000000000000000000000000000000), (7618027981 / 20000000000000000000000000000000)⟩
def CB2_1_5I2S2_0_2E_3LogWitness : LogWitness := ⟨-4, 50311, 31250⟩
def CB2_1_5I2S2_0_2E_3Log : Ball := ⟨(-229638435735244201494939716178541 / 100000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
def CB2_1_5I2S2_0_2E_3 : Ball := ⟨(23106678680551742042823824121317 / 100000000000000000000000000000000), (5326884327 / 50000000000000000000000000000000)⟩
def CB2_1_5I2S2_0_2Terms (a : Fin 6) : Ball :=
  match a.val with
  | 2 => ⟨(4769035743310852342197034819761 / 50000000000000000000000000000000), (7618027981 / 20000000000000000000000000000000)⟩
  | 3 => ⟨(23106678680551742042823824121317 / 100000000000000000000000000000000), (5326884327 / 50000000000000000000000000000000)⟩
  | _ => (.exact 0)
def CB2_1_5I2S2_0_2Entropy : Ball := ⟨(32644750167173446727217893760839 / 100000000000000000000000000000000), (48743908559 / 100000000000000000000000000000000)⟩
def CB2_1_5I2S2_0_2Mass : Ball := ⟨1, 0⟩
def CB2_1_5I2S2_0_2MassTermLog : Ball := .exact 0
def CB2_1_5I2S2_0_2MassTerm : Ball := ⟨0, 0⟩
def CB2_1_5I2S2_0_2H : Ball := ⟨(32644750167173446727217893760839 / 100000000000000000000000000000000), (48743908559 / 100000000000000000000000000000000)⟩
def CB2_1_5I2Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => CB2_1_5I2S0_0_4H
  | 0, 1, 3 => CB2_1_5I2S0_1_3H
  | 1, 0, 3 => CB2_1_5I2S1_0_3H
  | 2, 0, 2 => CB2_1_5I2S2_0_2H
  | _, _, _ => (.exact 0)
def CB2_1_5I2Singleton : Ball := ⟨(1487679008418615246531854016649 / 25000000000000000000000000000000), (277668267 / 3125000000000000000000000000000)⟩
def CB2_1_5I2Group : Ball := ⟨(1487796348680613112744675821277 / 25000000000000000000000000000000), (4959902711 / 10000000000000000000000000000000)⟩

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
def CB2_1_5I2H : Ball := ⟨(465378581497257829111303744359 / 625000000000000000000000000000), (187355184909 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB2_2_4I0
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
def CB2_2_4I0Value (a : Fin 17) : ℝ := marginal (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) ((stageBPriority (shape 2 2 4)) 0) a
def CB2_2_4I0Entropy : Ball := ⟨(91376960812637137857751538245273 / 100000000000000000000000000000000), (28982422453 / 50000000000000000000000000000000)⟩
def CB2_2_4I0Mass : Ball := ⟨(50000000000000000000000000000001 / 50000000000000000000000000000000), (7 / 3125000000000000000000000000000)⟩
def CB2_2_4I0MassTermLogWitness : LogWitness := ⟨0, 50000000000000000000000000000001, 50000000000000000000000000000000⟩
def CB2_2_4I0MassTermLog : Ball := ⟨(1 / 50000000000000000000000000000000), (10587911953 / 50000000000000000000000000000000)⟩
def CB2_2_4I0MassTerm : Ball := ⟨(-1 / 50000000000000000000000000000000), (21175823907 / 100000000000000000000000000000000)⟩
def CB2_2_4I0H : Ball := ⟨(3655078432505485514310061529811 / 4000000000000000000000000000000), (79140668813 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB2_2_4I1
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
def CB2_2_4I1PairEntropy : Ball := ⟨(102615661013236249480829850512361 / 100000000000000000000000000000000), (15024038279 / 25000000000000000000000000000000)⟩
def CB2_2_4I1PairMass : Ball := ⟨(50000000000000000000000000000001 / 50000000000000000000000000000000), (57 / 25000000000000000000000000000000)⟩
def CB2_2_4I1PairMassTermLogWitness : LogWitness := ⟨0, 50000000000000000000000000000001, 50000000000000000000000000000000⟩
def CB2_2_4I1PairMassTermLog : Ball := ⟨(1 / 50000000000000000000000000000000), (2117582391 / 10000000000000000000000000000000)⟩
def CB2_2_4I1PairMassTerm : Ball := ⟨(-1 / 50000000000000000000000000000000), (21175823911 / 100000000000000000000000000000000)⟩
def CB2_2_4I1PairH : Ball := ⟨(102615661013236249480829850512363 / 100000000000000000000000000000000), (81271977027 / 100000000000000000000000000000000)⟩

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
def CB2_2_4I1R0Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) 0 a
def CB2_2_4I1R0Entropy : Ball := ⟨(31170581090219803908545577364083 / 100000000000000000000000000000000), (15613197227 / 100000000000000000000000000000000)⟩
def CB2_2_4I1R0Mass : Ball := ⟨(18432809600162602238233930394191 / 100000000000000000000000000000000), (17 / 25000000000000000000000000000000)⟩
def CB2_2_4I1R0MassTermLogWitness : LogWitness := ⟨-3, 18432809600162602238233930394191, 12500000000000000000000000000000⟩
def CB2_2_4I1R0MassTermLog : Ball := ⟨(-42275949470482293361630256775271 / 25000000000000000000000000000000), (847032951 / 1000000000000000000000000000000)⟩
def CB2_2_4I1R0MassTerm : Ball := ⟨(31170581090219803908545577364083 / 100000000000000000000000000000000), (15613197227 / 100000000000000000000000000000000)⟩
def CB2_2_4I1R0H : Ball := ⟨0, (15613197227 / 50000000000000000000000000000000)⟩
def CB2_2_4I1R1Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) 1 a
def CB2_2_4I1R1Entropy : Ball := ⟨(29035798632197530040660383517107 / 100000000000000000000000000000000), (6684612613 / 25000000000000000000000000000000)⟩
def CB2_2_4I1R1Mass : Ball := ⟨(3156719039983739776176606960581 / 5000000000000000000000000000000), (11 / 12500000000000000000000000000000)⟩
def CB2_2_4I1R1MassTermLogWitness : LogWitness := ⟨-1, 3156719039983739776176606960581, 2500000000000000000000000000000⟩
def CB2_2_4I1R1MassTermLog : Ball := ⟨(-9198094054118637402943840466023 / 20000000000000000000000000000000), (8470329501 / 20000000000000000000000000000000)⟩
def CB2_2_4I1R1MassTerm : Ball := ⟨(29035798632197530040660383517107 / 100000000000000000000000000000000), (6684612613 / 25000000000000000000000000000000)⟩
def CB2_2_4I1R1H : Ball := ⟨0, (6684612613 / 12500000000000000000000000000000)⟩
def CB2_2_4I1R2Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) 2 a
def CB2_2_4I1R2Entropy : Ball := ⟨(36769237256975377708146829217607 / 100000000000000000000000000000000), (4164794117 / 25000000000000000000000000000000)⟩
def CB2_2_4I1R2Mass : Ball := ⟨(4602659717688795246539547045461 / 25000000000000000000000000000000), (17 / 25000000000000000000000000000000)⟩
def CB2_2_4I1R2MassTermLogWitness : LogWitness := ⟨-3, 4602659717688795246539547045461, 3125000000000000000000000000000⟩
def CB2_2_4I1R2MassTermLog : Ball := ⟨(-169224148896851114673947115933983 / 100000000000000000000000000000000), (84703295101 / 100000000000000000000000000000000)⟩
def CB2_2_4I1R2MassTerm : Ball := ⟨(31155246935508296120647022464513 / 100000000000000000000000000000000), (15594417889 / 100000000000000000000000000000000)⟩
def CB2_2_4I1R2H : Ball := ⟨(2806995160733540793749903376547 / 50000000000000000000000000000000), (32253594357 / 100000000000000000000000000000000)⟩
def CB2_2_4I1R3Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) 3 a
def CB2_2_4I1R3Entropy : Ball := ⟨0, 0⟩
def CB2_2_4I1R3Mass : Ball := ⟨0, 0⟩
def CB2_2_4I1R3MassTerm : Ball := .exact 0
def CB2_2_4I1R3H : Ball := ⟨0, 0⟩
def CB2_2_4I1R4Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) 4 a
def CB2_2_4I1R4Entropy : Ball := ⟨0, 0⟩
def CB2_2_4I1R4Mass : Ball := ⟨0, 0⟩
def CB2_2_4I1R4MassTerm : Ball := .exact 0
def CB2_2_4I1R4H : Ball := ⟨0, 0⟩
def CB2_2_4I1R5Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) 5 a
def CB2_2_4I1R5Entropy : Ball := ⟨0, 0⟩
def CB2_2_4I1R5Mass : Ball := ⟨0, 0⟩
def CB2_2_4I1R5MassTerm : Ball := .exact 0
def CB2_2_4I1R5H : Ball := ⟨0, 0⟩
def CB2_2_4I1R6Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) 6 a
def CB2_2_4I1R6Entropy : Ball := ⟨0, 0⟩
def CB2_2_4I1R6Mass : Ball := ⟨0, 0⟩
def CB2_2_4I1R6MassTerm : Ball := .exact 0
def CB2_2_4I1R6H : Ball := ⟨0, 0⟩
def CB2_2_4I1R7Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) 7 a
def CB2_2_4I1R7Entropy : Ball := ⟨0, 0⟩
def CB2_2_4I1R7Mass : Ball := ⟨0, 0⟩
def CB2_2_4I1R7MassTerm : Ball := .exact 0
def CB2_2_4I1R7H : Ball := ⟨0, 0⟩
def CB2_2_4I1R8Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) 8 a
def CB2_2_4I1R8Entropy : Ball := ⟨0, 0⟩
def CB2_2_4I1R8Mass : Ball := ⟨0, 0⟩
def CB2_2_4I1R8MassTerm : Ball := .exact 0
def CB2_2_4I1R8H : Ball := ⟨0, 0⟩
def CB2_2_4I1R9Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) 9 a
def CB2_2_4I1R9Entropy : Ball := ⟨0, 0⟩
def CB2_2_4I1R9Mass : Ball := ⟨0, 0⟩
def CB2_2_4I1R9MassTerm : Ball := .exact 0
def CB2_2_4I1R9H : Ball := ⟨0, 0⟩
def CB2_2_4I1R10Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) 10 a
def CB2_2_4I1R10Entropy : Ball := ⟨0, 0⟩
def CB2_2_4I1R10Mass : Ball := ⟨0, 0⟩
def CB2_2_4I1R10MassTerm : Ball := .exact 0
def CB2_2_4I1R10H : Ball := ⟨0, 0⟩
def CB2_2_4I1R11Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) 11 a
def CB2_2_4I1R11Entropy : Ball := ⟨0, 0⟩
def CB2_2_4I1R11Mass : Ball := ⟨0, 0⟩
def CB2_2_4I1R11MassTerm : Ball := .exact 0
def CB2_2_4I1R11H : Ball := ⟨0, 0⟩
def CB2_2_4I1R12Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) 12 a
def CB2_2_4I1R12Entropy : Ball := ⟨0, 0⟩
def CB2_2_4I1R12Mass : Ball := ⟨0, 0⟩
def CB2_2_4I1R12MassTerm : Ball := .exact 0
def CB2_2_4I1R12H : Ball := ⟨0, 0⟩
def CB2_2_4I1R13Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) 13 a
def CB2_2_4I1R13Entropy : Ball := ⟨0, 0⟩
def CB2_2_4I1R13Mass : Ball := ⟨0, 0⟩
def CB2_2_4I1R13MassTerm : Ball := .exact 0
def CB2_2_4I1R13H : Ball := ⟨0, 0⟩
def CB2_2_4I1R14Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) 14 a
def CB2_2_4I1R14Entropy : Ball := ⟨0, 0⟩
def CB2_2_4I1R14Mass : Ball := ⟨0, 0⟩
def CB2_2_4I1R14MassTerm : Ball := .exact 0
def CB2_2_4I1R14H : Ball := ⟨0, 0⟩
def CB2_2_4I1R15Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) 15 a
def CB2_2_4I1R15Entropy : Ball := ⟨0, 0⟩
def CB2_2_4I1R15Mass : Ball := ⟨0, 0⟩
def CB2_2_4I1R15MassTerm : Ball := .exact 0
def CB2_2_4I1R15H : Ball := ⟨0, 0⟩
def CB2_2_4I1R16Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) 16 a
def CB2_2_4I1R16Entropy : Ball := ⟨0, 0⟩
def CB2_2_4I1R16Mass : Ball := ⟨0, 0⟩
def CB2_2_4I1R16MassTerm : Ball := .exact 0
def CB2_2_4I1R16H : Ball := ⟨0, 0⟩
def CB2_2_4I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CB2_2_4I1R0H
  | 1 => CB2_2_4I1R1H
  | 2 => CB2_2_4I1R2H
  | 3 => CB2_2_4I1R3H
  | 4 => CB2_2_4I1R4H
  | 5 => CB2_2_4I1R5H
  | 6 => CB2_2_4I1R6H
  | 7 => CB2_2_4I1R7H
  | 8 => CB2_2_4I1R8H
  | 9 => CB2_2_4I1R9H
  | 10 => CB2_2_4I1R10H
  | 11 => CB2_2_4I1R11H
  | 12 => CB2_2_4I1R12H
  | 13 => CB2_2_4I1R13H
  | 14 => CB2_2_4I1R14H
  | 15 => CB2_2_4I1R15H
  | 16 => CB2_2_4I1R16H
  | _ => (.exact 0)
def CB2_2_4I1S2_2_0Value (a : Fin 6) : ℝ := (littleLaw (shape 2 2 4) (shape 2 2 0) ((stageBPriority (shape 2 2 4)) 1) a : ℝ)
def CB2_2_4I1S2_2_0E_2LogWitness : LogWitness := ⟨-1, 468209, 250000⟩
def CB2_2_4I1S2_2_0E_2Log : Ball := ⟨(-1642333024891709491091130987267 / 25000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def CB2_2_4I1S2_2_0E_2 : Ball := ⟨(3075820413006089636457149393669 / 50000000000000000000000000000000), (9914711231 / 25000000000000000000000000000000)⟩
def CB2_2_4I1S2_2_0E_3LogWitness : LogWitness := ⟨-4, 31791, 31250⟩
def CB2_2_4I1S2_2_0E_3Log : Ball := ⟨(-8610702711129322182939633075951 / 3125000000000000000000000000000), (52939559207 / 50000000000000000000000000000000)⟩
def CB2_2_4I1S2_2_0E_3 : Ball := ⟨(4379885598232196504285342001881 / 25000000000000000000000000000000), (1683001527 / 25000000000000000000000000000000)⟩
def CB2_2_4I1S2_2_0Terms (a : Fin 6) : Ball :=
  match a.val with
  | 2 => ⟨(3075820413006089636457149393669 / 50000000000000000000000000000000), (9914711231 / 25000000000000000000000000000000)⟩
  | 3 => ⟨(4379885598232196504285342001881 / 25000000000000000000000000000000), (1683001527 / 25000000000000000000000000000000)⟩
  | _ => (.exact 0)
def CB2_2_4I1S2_2_0Entropy : Ball := ⟨(11835591609470482645027833397431 / 50000000000000000000000000000000), (5798856379 / 12500000000000000000000000000000)⟩
def CB2_2_4I1S2_2_0Mass : Ball := ⟨1, 0⟩
def CB2_2_4I1S2_2_0MassTermLog : Ball := .exact 0
def CB2_2_4I1S2_2_0MassTerm : Ball := ⟨0, 0⟩
def CB2_2_4I1S2_2_0H : Ball := ⟨(11835591609470482645027833397431 / 50000000000000000000000000000000), (5798856379 / 12500000000000000000000000000000)⟩
def CB2_2_4I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 2, 2, 0 => CB2_2_4I1S2_2_0H
  | _, _, _ => (.exact 0)
def CB2_2_4I1Singleton : Ball := ⟨(5248073979006309136194565619 / 100000000000000000000000000000000), (10285191 / 100000000000000000000000000000000)⟩
def CB2_2_4I1Group : Ball := ⟨(5619238395446087896636001318713 / 100000000000000000000000000000000), (58483587453 / 50000000000000000000000000000000)⟩

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
def CB2_2_4I1H : Ball := ⟨(91377184222344073687557847874937 / 100000000000000000000000000000000), (315206326839 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB2_2_4I2
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
def CB2_2_4I2PairEntropy : Ball := ⟨(82463923851946036745093272664089 / 100000000000000000000000000000000), (2900045671 / 5000000000000000000000000000000)⟩
def CB2_2_4I2PairMass : Ball := ⟨(50000000000000000000000000000001 / 50000000000000000000000000000000), (227 / 100000000000000000000000000000000)⟩
def CB2_2_4I2PairMassTermLogWitness : LogWitness := ⟨0, 50000000000000000000000000000001, 50000000000000000000000000000000⟩
def CB2_2_4I2PairMassTermLog : Ball := ⟨(1 / 50000000000000000000000000000000), (21175823909 / 100000000000000000000000000000000)⟩
def CB2_2_4I2PairMassTerm : Ball := ⟨(-1 / 50000000000000000000000000000000), (2117582391 / 10000000000000000000000000000000)⟩
def CB2_2_4I2PairH : Ball := ⟨(82463923851946036745093272664091 / 100000000000000000000000000000000), (7917673733 / 10000000000000000000000000000000)⟩

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
def CB2_2_4I2R0Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) 0 a
def CB2_2_4I2R0Entropy : Ball := ⟨(186547899184436920742962037689 / 100000000000000000000000000000000), (32863847 / 50000000000000000000000000000000)⟩
def CB2_2_4I2R0Mass : Ball := ⟨(22170729407421252075742212347 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def CB2_2_4I2R0MassTermLogWitness : LogWitness := ⟨-13, 22170729407421252075742212347, 12207031250000000000000000000⟩
def CB2_2_4I2R0MassTermLog : Ball := ⟨(-841415254123273786972146125285279 / 100000000000000000000000000000000), (37057692009 / 12500000000000000000000000000000)⟩
def CB2_2_4I2R0MassTerm : Ball := ⟨(186547899184436920742962037689 / 100000000000000000000000000000000), (32863847 / 50000000000000000000000000000000)⟩
def CB2_2_4I2R0H : Ball := ⟨0, (32863847 / 25000000000000000000000000000000)⟩
def CB2_2_4I2R1Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) 1 a
def CB2_2_4I2R1Entropy : Ball := ⟨(4860812523784326097575945646473 / 25000000000000000000000000000000), (7951755343 / 100000000000000000000000000000000)⟩
def CB2_2_4I2R1Mass : Ball := ⟨(1877555123344146106224953559491 / 25000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
def CB2_2_4I2R1MassTermLogWitness : LogWitness := ⟨-4, 1877555123344146106224953559491, 1562500000000000000000000000000⟩
def CB2_2_4I2R1MassTermLog : Ball := ⟨(-64722634016819814007605771245177 / 25000000000000000000000000000000), (2646977969 / 2500000000000000000000000000000)⟩
def CB2_2_4I2R1MassTerm : Ball := ⟨(4860812523784326097575945646473 / 25000000000000000000000000000000), (7951755343 / 100000000000000000000000000000000)⟩
def CB2_2_4I2R1H : Ball := ⟨0, (7951755343 / 50000000000000000000000000000000)⟩
def CB2_2_4I2R2Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) 2 a
def CB2_2_4I2R2Entropy : Ball := ⟨(35493218695489216105630271416153 / 100000000000000000000000000000000), (24303033031 / 100000000000000000000000000000000)⟩
def CB2_2_4I2R2Mass : Ball := ⟨(6953020038287276387329040621707 / 12500000000000000000000000000000), (63 / 100000000000000000000000000000000)⟩
def CB2_2_4I2R2MassTermLogWitness : LogWitness := ⟨-1, 6953020038287276387329040621707, 6250000000000000000000000000000⟩
def CB2_2_4I2R2MassTermLog : Ball := ⟨(-14663813530818446743036588603247 / 25000000000000000000000000000000), (42351647479 / 100000000000000000000000000000000)⟩
def CB2_2_4I2R2MassTerm : Ball := ⟨(16313246290798201299195114300737 / 50000000000000000000000000000000), (5889437081 / 25000000000000000000000000000000)⟩
def CB2_2_4I2R2H : Ball := ⟨(2866726113892813507240042814679 / 100000000000000000000000000000000), (9572156271 / 20000000000000000000000000000000)⟩
def CB2_2_4I2R3Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) 3 a
def CB2_2_4I2R3Entropy : Ball := ⟨0, 0⟩
def CB2_2_4I2R3Mass : Ball := ⟨0, 0⟩
def CB2_2_4I2R3MassTerm : Ball := .exact 0
def CB2_2_4I2R3H : Ball := ⟨0, 0⟩
def CB2_2_4I2R4Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) 4 a
def CB2_2_4I2R4Entropy : Ball := ⟨0, 0⟩
def CB2_2_4I2R4Mass : Ball := ⟨0, 0⟩
def CB2_2_4I2R4MassTerm : Ball := .exact 0
def CB2_2_4I2R4H : Ball := ⟨0, 0⟩
def CB2_2_4I2R5Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) 5 a
def CB2_2_4I2R5Entropy : Ball := ⟨0, 0⟩
def CB2_2_4I2R5Mass : Ball := ⟨0, 0⟩
def CB2_2_4I2R5MassTerm : Ball := .exact 0
def CB2_2_4I2R5H : Ball := ⟨0, 0⟩
def CB2_2_4I2R6Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) 6 a
def CB2_2_4I2R6Entropy : Ball := ⟨0, 0⟩
def CB2_2_4I2R6Mass : Ball := ⟨0, 0⟩
def CB2_2_4I2R6MassTerm : Ball := .exact 0
def CB2_2_4I2R6H : Ball := ⟨0, 0⟩
def CB2_2_4I2R7Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) 7 a
def CB2_2_4I2R7Entropy : Ball := ⟨0, 0⟩
def CB2_2_4I2R7Mass : Ball := ⟨0, 0⟩
def CB2_2_4I2R7MassTerm : Ball := .exact 0
def CB2_2_4I2R7H : Ball := ⟨0, 0⟩
def CB2_2_4I2R8Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) 8 a
def CB2_2_4I2R8Entropy : Ball := ⟨0, 0⟩
def CB2_2_4I2R8Mass : Ball := ⟨0, 0⟩
def CB2_2_4I2R8MassTerm : Ball := .exact 0
def CB2_2_4I2R8H : Ball := ⟨0, 0⟩
def CB2_2_4I2R9Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) 9 a
def CB2_2_4I2R9Entropy : Ball := ⟨0, 0⟩
def CB2_2_4I2R9Mass : Ball := ⟨0, 0⟩
def CB2_2_4I2R9MassTerm : Ball := .exact 0
def CB2_2_4I2R9H : Ball := ⟨0, 0⟩
def CB2_2_4I2R10Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) 10 a
def CB2_2_4I2R10Entropy : Ball := ⟨0, 0⟩
def CB2_2_4I2R10Mass : Ball := ⟨0, 0⟩
def CB2_2_4I2R10MassTerm : Ball := .exact 0
def CB2_2_4I2R10H : Ball := ⟨0, 0⟩
def CB2_2_4I2R11Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) 11 a
def CB2_2_4I2R11Entropy : Ball := ⟨0, 0⟩
def CB2_2_4I2R11Mass : Ball := ⟨0, 0⟩
def CB2_2_4I2R11MassTerm : Ball := .exact 0
def CB2_2_4I2R11H : Ball := ⟨0, 0⟩
def CB2_2_4I2R12Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) 12 a
def CB2_2_4I2R12Entropy : Ball := ⟨0, 0⟩
def CB2_2_4I2R12Mass : Ball := ⟨0, 0⟩
def CB2_2_4I2R12MassTerm : Ball := .exact 0
def CB2_2_4I2R12H : Ball := ⟨0, 0⟩
def CB2_2_4I2R13Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) 13 a
def CB2_2_4I2R13Entropy : Ball := ⟨0, 0⟩
def CB2_2_4I2R13Mass : Ball := ⟨0, 0⟩
def CB2_2_4I2R13MassTerm : Ball := .exact 0
def CB2_2_4I2R13H : Ball := ⟨0, 0⟩
def CB2_2_4I2R14Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) 14 a
def CB2_2_4I2R14Entropy : Ball := ⟨0, 0⟩
def CB2_2_4I2R14Mass : Ball := ⟨0, 0⟩
def CB2_2_4I2R14MassTerm : Ball := .exact 0
def CB2_2_4I2R14H : Ball := ⟨0, 0⟩
def CB2_2_4I2R15Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) 15 a
def CB2_2_4I2R15Entropy : Ball := ⟨0, 0⟩
def CB2_2_4I2R15Mass : Ball := ⟨0, 0⟩
def CB2_2_4I2R15MassTerm : Ball := .exact 0
def CB2_2_4I2R15H : Ball := ⟨0, 0⟩
def CB2_2_4I2R16Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) 16 a
def CB2_2_4I2R16Entropy : Ball := ⟨0, 0⟩
def CB2_2_4I2R16Mass : Ball := ⟨0, 0⟩
def CB2_2_4I2R16MassTerm : Ball := .exact 0
def CB2_2_4I2R16H : Ball := ⟨0, 0⟩
def CB2_2_4I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CB2_2_4I2R0H
  | 1 => CB2_2_4I2R1H
  | 2 => CB2_2_4I2R2H
  | 3 => CB2_2_4I2R3H
  | 4 => CB2_2_4I2R4H
  | 5 => CB2_2_4I2R5H
  | 6 => CB2_2_4I2R6H
  | 7 => CB2_2_4I2R7H
  | 8 => CB2_2_4I2R8H
  | 9 => CB2_2_4I2R9H
  | 10 => CB2_2_4I2R10H
  | 11 => CB2_2_4I2R11H
  | 12 => CB2_2_4I2R12H
  | 13 => CB2_2_4I2R13H
  | 14 => CB2_2_4I2R14H
  | 15 => CB2_2_4I2R15H
  | 16 => CB2_2_4I2R16H
  | _ => (.exact 0)
def CB2_2_4I2S0_0_4Value (a : Fin 6) : ℝ := (littleLaw (shape 2 2 4) (shape 0 0 4) ((stageBPriority (shape 2 2 4)) 2) a : ℝ)
def CB2_2_4I2S0_0_4E_5Log : Ball := .exact 0
def CB2_2_4I2S0_0_4E_5 : Ball := ⟨0, 0⟩
def CB2_2_4I2S0_0_4Terms (a : Fin 6) : Ball :=
  match a.val with
  | 5 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB2_2_4I2S0_0_4Entropy : Ball := ⟨0, 0⟩
def CB2_2_4I2S0_0_4Mass : Ball := ⟨1, 0⟩
def CB2_2_4I2S0_0_4MassTermLog : Ball := .exact 0
def CB2_2_4I2S0_0_4MassTerm : Ball := ⟨0, 0⟩
def CB2_2_4I2S0_0_4H : Ball := ⟨0, 0⟩
def CB2_2_4I2S0_1_3Value (a : Fin 6) : ℝ := (littleLaw (shape 2 2 4) (shape 0 1 3) ((stageBPriority (shape 2 2 4)) 2) a : ℝ)
def CB2_2_4I2S0_1_3E_4Log : Ball := .exact 0
def CB2_2_4I2S0_1_3E_4 : Ball := ⟨0, 0⟩
def CB2_2_4I2S0_1_3Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB2_2_4I2S0_1_3Entropy : Ball := ⟨0, 0⟩
def CB2_2_4I2S0_1_3Mass : Ball := ⟨1, 0⟩
def CB2_2_4I2S0_1_3MassTermLog : Ball := .exact 0
def CB2_2_4I2S0_1_3MassTerm : Ball := ⟨0, 0⟩
def CB2_2_4I2S0_1_3H : Ball := ⟨0, 0⟩
def CB2_2_4I2S0_2_2Value (a : Fin 6) : ℝ := (littleLaw (shape 2 2 4) (shape 0 2 2) ((stageBPriority (shape 2 2 4)) 2) a : ℝ)
def CB2_2_4I2S0_2_2E_2LogWitness : LogWitness := ⟨-1, 448219, 250000⟩
def CB2_2_4I2S0_2_2E_2Log : Ball := ⟨(-2186522923289837780427151140763 / 20000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def CB2_2_4I2S0_2_2E_2 : Ball := ⟨(9800411181540478001052772571617 / 100000000000000000000000000000000), (18982813031 / 50000000000000000000000000000000)⟩
def CB2_2_4I2S0_2_2E_3LogWitness : LogWitness := ⟨-4, 51781, 31250⟩
def CB2_2_4I2S0_2_2E_3Log : Ball := ⟨(-226758481180942422019326103547823 / 100000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
def CB2_2_4I2S0_2_2E_3 : Ball := ⟨(1174178091403037955458272496781 / 5000000000000000000000000000000), (5482526631 / 50000000000000000000000000000000)⟩
def CB2_2_4I2S0_2_2Terms (a : Fin 6) : Ball :=
  match a.val with
  | 2 => ⟨(9800411181540478001052772571617 / 100000000000000000000000000000000), (18982813031 / 50000000000000000000000000000000)⟩
  | 3 => ⟨(1174178091403037955458272496781 / 5000000000000000000000000000000), (5482526631 / 50000000000000000000000000000000)⟩
  | _ => (.exact 0)
def CB2_2_4I2S0_2_2Entropy : Ball := ⟨(33283973009601237110218222507237 / 100000000000000000000000000000000), (12232669831 / 25000000000000000000000000000000)⟩
def CB2_2_4I2S0_2_2Mass : Ball := ⟨1, 0⟩
def CB2_2_4I2S0_2_2MassTermLog : Ball := .exact 0
def CB2_2_4I2S0_2_2MassTerm : Ball := ⟨0, 0⟩
def CB2_2_4I2S0_2_2H : Ball := ⟨(33283973009601237110218222507237 / 100000000000000000000000000000000), (12232669831 / 25000000000000000000000000000000)⟩
def CB2_2_4I2S1_0_3Value (a : Fin 6) : ℝ := (littleLaw (shape 2 2 4) (shape 1 0 3) ((stageBPriority (shape 2 2 4)) 2) a : ℝ)
def CB2_2_4I2S1_0_3E_4Log : Ball := .exact 0
def CB2_2_4I2S1_0_3E_4 : Ball := ⟨0, 0⟩
def CB2_2_4I2S1_0_3Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB2_2_4I2S1_0_3Entropy : Ball := ⟨0, 0⟩
def CB2_2_4I2S1_0_3Mass : Ball := ⟨1, 0⟩
def CB2_2_4I2S1_0_3MassTermLog : Ball := .exact 0
def CB2_2_4I2S1_0_3MassTerm : Ball := ⟨0, 0⟩
def CB2_2_4I2S1_0_3H : Ball := ⟨0, 0⟩
def CB2_2_4I2S2_0_2Value (a : Fin 6) : ℝ := (littleLaw (shape 2 2 4) (shape 2 0 2) ((stageBPriority (shape 2 2 4)) 2) a : ℝ)
def CB2_2_4I2S2_0_2E_2LogWitness : LogWitness := ⟨-1, 896423, 500000⟩
def CB2_2_4I2S2_0_2E_2Log : Ball := ⟨(-2733571979905550299613262420469 / 25000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
def CB2_2_4I2S2_0_2E_2 : Ball := ⟨(306304599367859139528777442343 / 3125000000000000000000000000000), (37964990787 / 100000000000000000000000000000000)⟩
def CB2_2_4I2S2_0_2E_3LogWitness : LogWitness := ⟨-4, 103577, 62500⟩
def CB2_2_4I2S2_0_2E_3Log : Ball := ⟨(-2834299976907655511632457381399 / 1250000000000000000000000000000), (52939559207 / 50000000000000000000000000000000)⟩
def CB2_2_4I2S2_0_2E_3 : Ball := ⟨(23485463096653138794268403055453 / 100000000000000000000000000000000), (10966641449 / 100000000000000000000000000000000)⟩
def CB2_2_4I2S2_0_2Terms (a : Fin 6) : Ball :=
  match a.val with
  | 2 => ⟨(306304599367859139528777442343 / 3125000000000000000000000000000), (37964990787 / 100000000000000000000000000000000)⟩
  | 3 => ⟨(23485463096653138794268403055453 / 100000000000000000000000000000000), (10966641449 / 100000000000000000000000000000000)⟩
  | _ => (.exact 0)
def CB2_2_4I2S2_0_2Entropy : Ball := ⟨(33287210276424631259189281210429 / 100000000000000000000000000000000), (12232908059 / 25000000000000000000000000000000)⟩
def CB2_2_4I2S2_0_2Mass : Ball := ⟨1, 0⟩
def CB2_2_4I2S2_0_2MassTermLog : Ball := .exact 0
def CB2_2_4I2S2_0_2MassTerm : Ball := ⟨0, 0⟩
def CB2_2_4I2S2_0_2H : Ball := ⟨(33287210276424631259189281210429 / 100000000000000000000000000000000), (12232908059 / 25000000000000000000000000000000)⟩
def CB2_2_4I2Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => CB2_2_4I2S0_0_4H
  | 0, 1, 3 => CB2_2_4I2S0_1_3H
  | 0, 2, 2 => CB2_2_4I2S0_2_2H
  | 1, 0, 3 => CB2_2_4I2S1_0_3H
  | 2, 0, 2 => CB2_2_4I2S2_0_2H
  | _, _, _ => (.exact 0)
def CB2_2_4I2Singleton : Ball := ⟨(9756358821863553579066193634899 / 100000000000000000000000000000000), (179277989 / 1250000000000000000000000000000)⟩
def CB2_2_4I2Group : Ball := ⟨(6311542467878183543153118224789 / 50000000000000000000000000000000), (78237986549 / 100000000000000000000000000000000)⟩

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
def CB2_2_4I2H : Ball := ⟨(11443550796086660514496159952987 / 20000000000000000000000000000000), (58913177607 / 25000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB2_3_3I0
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
def CB2_3_3I0Value (a : Fin 17) : ℝ := marginal (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) ((stageBPriority (shape 2 3 3)) 0) a
def CB2_3_3I0Entropy : Ball := ⟨(40764548588315651308630792965447 / 50000000000000000000000000000000), (1326540167 / 2000000000000000000000000000000)⟩
def CB2_3_3I0Mass : Ball := ⟨1, (21 / 25000000000000000000000000000000)⟩
def CB2_3_3I0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB2_3_3I0MassTermLog : Ball := ⟨0, (10587911883 / 50000000000000000000000000000000)⟩
def CB2_3_3I0MassTerm : Ball := ⟨0, (21175823767 / 100000000000000000000000000000000)⟩
def CB2_3_3I0H : Ball := ⟨(40764548588315651308630792965447 / 50000000000000000000000000000000), (87502832117 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB2_3_3I1
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
def CB2_3_3I1PairEntropy : Ball := ⟨(49258475697145552294495931906059 / 50000000000000000000000000000000), (29741143613 / 50000000000000000000000000000000)⟩
def CB2_3_3I1PairMass : Ball := ⟨1, (43 / 50000000000000000000000000000000)⟩
def CB2_3_3I1PairMassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB2_3_3I1PairMassTermLog : Ball := ⟨0, (2646977971 / 12500000000000000000000000000000)⟩
def CB2_3_3I1PairMassTerm : Ball := ⟨0, (21175823769 / 100000000000000000000000000000000)⟩
def CB2_3_3I1PairH : Ball := ⟨(49258475697145552294495931906059 / 50000000000000000000000000000000), (16131622199 / 20000000000000000000000000000000)⟩

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
def CB2_3_3I1R0Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 1 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 1) a : ℝ)) 0 a
def CB2_3_3I1R0Entropy : Ball := ⟨(31210104061251053825671556162407 / 100000000000000000000000000000000), (15661751147 / 100000000000000000000000000000000)⟩
def CB2_3_3I1R0Mass : Ball := ⟨(18490132078687878363345409025791 / 100000000000000000000000000000000), (7 / 25000000000000000000000000000000)⟩
def CB2_3_3I1R0MassTermLogWitness : LogWitness := ⟨-3, 18490132078687878363345409025791, 12500000000000000000000000000000⟩
def CB2_3_3I1R0MassTermLog : Ball := ⟨(-8439664986824103647164745978359 / 5000000000000000000000000000000), (84703294883 / 100000000000000000000000000000000)⟩
def CB2_3_3I1R0MassTerm : Ball := ⟨(31210104061251053825671556162407 / 100000000000000000000000000000000), (15661751147 / 100000000000000000000000000000000)⟩
def CB2_3_3I1R0H : Ball := ⟨0, (15661751147 / 50000000000000000000000000000000)⟩
def CB2_3_3I1R1Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 1 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 1) a : ℝ)) 1 a
def CB2_3_3I1R1Entropy : Ball := ⟨(5836729010460201172294134918613 / 20000000000000000000000000000000), (6655511643 / 25000000000000000000000000000000)⟩
def CB2_3_3I1R1Mass : Ball := ⟨(7857441264699229683296977815819 / 12500000000000000000000000000000), (27 / 100000000000000000000000000000000)⟩
def CB2_3_3I1R1MassTermLogWitness : LogWitness := ⟨-1, 7857441264699229683296977815819, 6250000000000000000000000000000⟩
def CB2_3_3I1R1MassTermLog : Ball := ⟨(-23213381485437445740208763534969 / 50000000000000000000000000000000), (42351647409 / 100000000000000000000000000000000)⟩
def CB2_3_3I1R1MassTerm : Ball := ⟨(5836729010460201172294134918613 / 20000000000000000000000000000000), (6655511643 / 25000000000000000000000000000000)⟩
def CB2_3_3I1R1H : Ball := ⟨0, (6655511643 / 12500000000000000000000000000000)⟩
def CB2_3_3I1R2Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 1 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 1) a : ℝ)) 2 a
def CB2_3_3I1R2Entropy : Ball := ⟨(16734134313523414453384739707907 / 50000000000000000000000000000000), (241875329 / 1562500000000000000000000000000)⟩
def CB2_3_3I1R2Mass : Ball := ⟨(17339048786962947875254487659649 / 100000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
def CB2_3_3I1R2MassTermLogWitness : LogWitness := ⟨-3, 17339048786962947875254487659649, 12500000000000000000000000000000⟩
def CB2_3_3I1R2MassTermLog : Ball := ⟨(-87610453635845193070010899116863 / 50000000000000000000000000000000), (84703294881 / 100000000000000000000000000000000)⟩
def CB2_3_3I1R2MassTerm : Ball := ⟨(15190819298398751811632270251413 / 50000000000000000000000000000000), (1468674567 / 10000000000000000000000000000000)⟩
def CB2_3_3I1R2H : Ball := ⟨(771657507562331320876234728247 / 25000000000000000000000000000000), (15083383363 / 50000000000000000000000000000000)⟩
def CB2_3_3I1R3Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 1 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 1) a : ℝ)) 3 a
def CB2_3_3I1R3Entropy : Ball := ⟨0, 0⟩
def CB2_3_3I1R3Mass : Ball := ⟨0, 0⟩
def CB2_3_3I1R3MassTerm : Ball := .exact 0
def CB2_3_3I1R3H : Ball := ⟨0, 0⟩
def CB2_3_3I1R4Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 1 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 1) a : ℝ)) 4 a
def CB2_3_3I1R4Entropy : Ball := ⟨0, 0⟩
def CB2_3_3I1R4Mass : Ball := ⟨0, 0⟩
def CB2_3_3I1R4MassTerm : Ball := .exact 0
def CB2_3_3I1R4H : Ball := ⟨0, 0⟩
def CB2_3_3I1R5Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 1 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 1) a : ℝ)) 5 a
def CB2_3_3I1R5Entropy : Ball := ⟨0, 0⟩
def CB2_3_3I1R5Mass : Ball := ⟨0, 0⟩
def CB2_3_3I1R5MassTerm : Ball := .exact 0
def CB2_3_3I1R5H : Ball := ⟨0, 0⟩
def CB2_3_3I1R6Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 1 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 1) a : ℝ)) 6 a
def CB2_3_3I1R6Entropy : Ball := ⟨0, 0⟩
def CB2_3_3I1R6Mass : Ball := ⟨0, 0⟩
def CB2_3_3I1R6MassTerm : Ball := .exact 0
def CB2_3_3I1R6H : Ball := ⟨0, 0⟩
def CB2_3_3I1R7Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 1 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 1) a : ℝ)) 7 a
def CB2_3_3I1R7Entropy : Ball := ⟨0, 0⟩
def CB2_3_3I1R7Mass : Ball := ⟨0, 0⟩
def CB2_3_3I1R7MassTerm : Ball := .exact 0
def CB2_3_3I1R7H : Ball := ⟨0, 0⟩
def CB2_3_3I1R8Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 1 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 1) a : ℝ)) 8 a
def CB2_3_3I1R8Entropy : Ball := ⟨0, 0⟩
def CB2_3_3I1R8Mass : Ball := ⟨0, 0⟩
def CB2_3_3I1R8MassTerm : Ball := .exact 0
def CB2_3_3I1R8H : Ball := ⟨0, 0⟩
def CB2_3_3I1R9Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 1 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 1) a : ℝ)) 9 a
def CB2_3_3I1R9Entropy : Ball := ⟨0, 0⟩
def CB2_3_3I1R9Mass : Ball := ⟨0, 0⟩
def CB2_3_3I1R9MassTerm : Ball := .exact 0
def CB2_3_3I1R9H : Ball := ⟨0, 0⟩
def CB2_3_3I1R10Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 1 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 1) a : ℝ)) 10 a
def CB2_3_3I1R10Entropy : Ball := ⟨0, 0⟩
def CB2_3_3I1R10Mass : Ball := ⟨0, 0⟩
def CB2_3_3I1R10MassTerm : Ball := .exact 0
def CB2_3_3I1R10H : Ball := ⟨0, 0⟩
def CB2_3_3I1R11Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 1 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 1) a : ℝ)) 11 a
def CB2_3_3I1R11Entropy : Ball := ⟨0, 0⟩
def CB2_3_3I1R11Mass : Ball := ⟨0, 0⟩
def CB2_3_3I1R11MassTerm : Ball := .exact 0
def CB2_3_3I1R11H : Ball := ⟨0, 0⟩
def CB2_3_3I1R12Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 1 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 1) a : ℝ)) 12 a
def CB2_3_3I1R12Entropy : Ball := ⟨0, 0⟩
def CB2_3_3I1R12Mass : Ball := ⟨0, 0⟩
def CB2_3_3I1R12MassTerm : Ball := .exact 0
def CB2_3_3I1R12H : Ball := ⟨0, 0⟩
def CB2_3_3I1R13Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 1 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 1) a : ℝ)) 13 a
def CB2_3_3I1R13Entropy : Ball := ⟨0, 0⟩
def CB2_3_3I1R13Mass : Ball := ⟨0, 0⟩
def CB2_3_3I1R13MassTerm : Ball := .exact 0
def CB2_3_3I1R13H : Ball := ⟨0, 0⟩
def CB2_3_3I1R14Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 1 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 1) a : ℝ)) 14 a
def CB2_3_3I1R14Entropy : Ball := ⟨0, 0⟩
def CB2_3_3I1R14Mass : Ball := ⟨0, 0⟩
def CB2_3_3I1R14MassTerm : Ball := .exact 0
def CB2_3_3I1R14H : Ball := ⟨0, 0⟩
def CB2_3_3I1R15Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 1 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 1) a : ℝ)) 15 a
def CB2_3_3I1R15Entropy : Ball := ⟨0, 0⟩
def CB2_3_3I1R15Mass : Ball := ⟨0, 0⟩
def CB2_3_3I1R15MassTerm : Ball := .exact 0
def CB2_3_3I1R15H : Ball := ⟨0, 0⟩
def CB2_3_3I1R16Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 1 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 1) a : ℝ)) 16 a
def CB2_3_3I1R16Entropy : Ball := ⟨0, 0⟩
def CB2_3_3I1R16Mass : Ball := ⟨0, 0⟩
def CB2_3_3I1R16MassTerm : Ball := .exact 0
def CB2_3_3I1R16H : Ball := ⟨0, 0⟩
def CB2_3_3I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CB2_3_3I1R0H
  | 1 => CB2_3_3I1R1H
  | 2 => CB2_3_3I1R2H
  | 3 => CB2_3_3I1R3H
  | 4 => CB2_3_3I1R4H
  | 5 => CB2_3_3I1R5H
  | 6 => CB2_3_3I1R6H
  | 7 => CB2_3_3I1R7H
  | 8 => CB2_3_3I1R8H
  | 9 => CB2_3_3I1R9H
  | 10 => CB2_3_3I1R10H
  | 11 => CB2_3_3I1R11H
  | 12 => CB2_3_3I1R12H
  | 13 => CB2_3_3I1R13H
  | 14 => CB2_3_3I1R14H
  | 15 => CB2_3_3I1R15H
  | 16 => CB2_3_3I1R16H
  | _ => (.exact 0)
def CB2_3_3I1S1_3_0Value (a : Fin 6) : ℝ := (littleLaw (shape 2 3 3) (shape 1 3 0) ((stageBPriority (shape 2 3 3)) 1) a : ℝ)
def CB2_3_3I1S1_3_0E_1Log : Ball := .exact 0
def CB2_3_3I1S1_3_0E_1 : Ball := ⟨0, 0⟩
def CB2_3_3I1S1_3_0Terms (a : Fin 6) : Ball :=
  match a.val with
  | 1 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB2_3_3I1S1_3_0Entropy : Ball := ⟨0, 0⟩
def CB2_3_3I1S1_3_0Mass : Ball := ⟨1, 0⟩
def CB2_3_3I1S1_3_0MassTermLog : Ball := .exact 0
def CB2_3_3I1S1_3_0MassTerm : Ball := ⟨0, 0⟩
def CB2_3_3I1S1_3_0H : Ball := ⟨0, 0⟩
def CB2_3_3I1S2_2_0Value (a : Fin 6) : ℝ := (littleLaw (shape 2 3 3) (shape 2 2 0) ((stageBPriority (shape 2 3 3)) 1) a : ℝ)
def CB2_3_3I1S2_2_0E_2LogWitness : LogWitness := ⟨-1, 897617, 500000⟩
def CB2_3_3I1S2_2_0E_2Log : Ball := ⟨(-2160236099982276913212034276979 / 20000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def CB2_3_3I1S2_2_0E_2 : Ball := ⟨(1939064647357791456006646571599 / 20000000000000000000000000000000), (7603111731 / 20000000000000000000000000000000)⟩
def CB2_3_3I1S2_2_0E_3LogWitness : LogWitness := ⟨-4, 102383, 62500⟩
def CB2_3_3I1S2_2_0E_3Log : Ball := ⟨(-56975864894596222495907774317173 / 25000000000000000000000000000000), (52939559207 / 50000000000000000000000000000000)⟩
def CB2_3_3I1S2_2_0E_3 : Ball := ⟨(1166671995100689009559705131583 / 5000000000000000000000000000000), (5420110891 / 50000000000000000000000000000000)⟩
def CB2_3_3I1S2_2_0Terms (a : Fin 6) : Ball :=
  match a.val with
  | 2 => ⟨(1939064647357791456006646571599 / 20000000000000000000000000000000), (7603111731 / 20000000000000000000000000000000)⟩
  | 3 => ⟨(1166671995100689009559705131583 / 5000000000000000000000000000000), (5420110891 / 50000000000000000000000000000000)⟩
  | _ => (.exact 0)
def CB2_3_3I1S2_2_0Entropy : Ball := ⟨(6605752627760547494245467097931 / 20000000000000000000000000000000), (48855780437 / 100000000000000000000000000000000)⟩
def CB2_3_3I1S2_2_0Mass : Ball := ⟨1, 0⟩
def CB2_3_3I1S2_2_0MassTermLog : Ball := .exact 0
def CB2_3_3I1S2_2_0MassTerm : Ball := ⟨0, 0⟩
def CB2_3_3I1S2_2_0H : Ball := ⟨(6605752627760547494245467097931 / 20000000000000000000000000000000), (48855780437 / 100000000000000000000000000000000)⟩
def CB2_3_3I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 1, 3, 0 => CB2_3_3I1S1_3_0H
  | 2, 2, 0 => CB2_3_3I1S2_2_0H
  | _, _, _ => (.exact 0)
def CB2_3_3I1Singleton : Ball := ⟨(380188573954161022314410796219 / 100000000000000000000000000000000), (70296341 / 12500000000000000000000000000000)⟩
def CB2_3_3I1Group : Ball := ⟨(3466818604203486305819349709207 / 100000000000000000000000000000000), (28824183223 / 25000000000000000000000000000000)⟩

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
def CB2_3_3I1H : Ball := ⟨(11447914273235516497169145549213 / 12500000000000000000000000000000), (311251576779 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB2_3_3I2
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
def CB2_3_3I2PairEntropy : Ball := ⟨(49211359927335064083719528823497 / 50000000000000000000000000000000), (8721172953 / 12500000000000000000000000000000)⟩
def CB2_3_3I2PairMass : Ball := ⟨1, (43 / 50000000000000000000000000000000)⟩
def CB2_3_3I2PairMassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB2_3_3I2PairMassTermLog : Ball := ⟨0, (2646977971 / 12500000000000000000000000000000)⟩
def CB2_3_3I2PairMassTerm : Ball := ⟨0, (21175823769 / 100000000000000000000000000000000)⟩
def CB2_3_3I2PairH : Ball := ⟨(49211359927335064083719528823497 / 50000000000000000000000000000000), (90945207393 / 100000000000000000000000000000000)⟩

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
def CB2_3_3I2R0Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) 0 a
def CB2_3_3I2R0Entropy : Ball := ⟨(710416976898713047679469856213 / 12500000000000000000000000000000), (2221410029 / 100000000000000000000000000000000)⟩
def CB2_3_3I2R0Mass : Ball := ⟨(163911127094417036878035098501 / 12500000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
def CB2_3_3I2R0MassTermLogWitness : LogWitness := ⟨-7, 163911127094417036878035098501, 97656250000000000000000000000⟩
def CB2_3_3I2R0MassTermLog : Ball := ⟨(-108353988757806318051603335024857 / 25000000000000000000000000000000), (33881317969 / 20000000000000000000000000000000)⟩
def CB2_3_3I2R0MassTerm : Ball := ⟨(710416976898713047679469856213 / 12500000000000000000000000000000), (2221410029 / 100000000000000000000000000000000)⟩
def CB2_3_3I2R0H : Ball := ⟨0, (2221410029 / 50000000000000000000000000000000)⟩
def CB2_3_3I2R1Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) 1 a
def CB2_3_3I2R1Entropy : Ball := ⟨(35354047389686535436129562195663 / 100000000000000000000000000000000), (30192620343 / 100000000000000000000000000000000)⟩
def CB2_3_3I2R1Mass : Ball := ⟨(23763436341818321284544175804257 / 50000000000000000000000000000000), (33 / 100000000000000000000000000000000)⟩
def CB2_3_3I2R1MassTermLogWitness : LogWitness := ⟨-2, 23763436341818321284544175804257, 12500000000000000000000000000000⟩
def CB2_3_3I2R1MassTermLog : Ball := ⟨(-74387489421029854998168788216519 / 100000000000000000000000000000000), (31763735559 / 50000000000000000000000000000000)⟩
def CB2_3_3I2R1MassTerm : Ball := ⟨(35354047389686535436129562195663 / 100000000000000000000000000000000), (30192620343 / 100000000000000000000000000000000)⟩
def CB2_3_3I2R1H : Ball := ⟨0, (30192620343 / 50000000000000000000000000000000)⟩
def CB2_3_3I2R2Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) 2 a
def CB2_3_3I2R2Entropy : Ball := ⟨(4660228591251511180712242027301 / 12500000000000000000000000000000), (20159096491 / 100000000000000000000000000000000)⟩
def CB2_3_3I2R2Mass : Ball := ⟨(31349662196281715829721231552343 / 100000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
def CB2_3_3I2R2MassTermLogWitness : LogWitness := ⟨-2, 31349662196281715829721231552343, 25000000000000000000000000000000⟩
def CB2_3_3I2R2MassTermLog : Ball := ⟨(-115996669420543774296075561313107 / 100000000000000000000000000000000), (7940933887 / 12500000000000000000000000000000)⟩
def CB2_3_3I2R2MassTerm : Ball := ⟨(9091141005569521211958861081541 / 25000000000000000000000000000000), (2489455951 / 12500000000000000000000000000000)⟩
def CB2_3_3I2R2H : Ball := ⟨(229316176933501149465622973061 / 25000000000000000000000000000000), (40074744099 / 100000000000000000000000000000000)⟩
def CB2_3_3I2R3Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) 3 a
def CB2_3_3I2R3Entropy : Ball := ⟨0, 0⟩
def CB2_3_3I2R3Mass : Ball := ⟨0, 0⟩
def CB2_3_3I2R3MassTerm : Ball := .exact 0
def CB2_3_3I2R3H : Ball := ⟨0, 0⟩
def CB2_3_3I2R4Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) 4 a
def CB2_3_3I2R4Entropy : Ball := ⟨0, 0⟩
def CB2_3_3I2R4Mass : Ball := ⟨0, 0⟩
def CB2_3_3I2R4MassTerm : Ball := .exact 0
def CB2_3_3I2R4H : Ball := ⟨0, 0⟩
def CB2_3_3I2R5Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) 5 a
def CB2_3_3I2R5Entropy : Ball := ⟨0, 0⟩
def CB2_3_3I2R5Mass : Ball := ⟨0, 0⟩
def CB2_3_3I2R5MassTerm : Ball := .exact 0
def CB2_3_3I2R5H : Ball := ⟨0, 0⟩
def CB2_3_3I2R6Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) 6 a
def CB2_3_3I2R6Entropy : Ball := ⟨0, 0⟩
def CB2_3_3I2R6Mass : Ball := ⟨0, 0⟩
def CB2_3_3I2R6MassTerm : Ball := .exact 0
def CB2_3_3I2R6H : Ball := ⟨0, 0⟩
def CB2_3_3I2R7Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) 7 a
def CB2_3_3I2R7Entropy : Ball := ⟨0, 0⟩
def CB2_3_3I2R7Mass : Ball := ⟨0, 0⟩
def CB2_3_3I2R7MassTerm : Ball := .exact 0
def CB2_3_3I2R7H : Ball := ⟨0, 0⟩
def CB2_3_3I2R8Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) 8 a
def CB2_3_3I2R8Entropy : Ball := ⟨0, 0⟩
def CB2_3_3I2R8Mass : Ball := ⟨0, 0⟩
def CB2_3_3I2R8MassTerm : Ball := .exact 0
def CB2_3_3I2R8H : Ball := ⟨0, 0⟩
def CB2_3_3I2R9Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) 9 a
def CB2_3_3I2R9Entropy : Ball := ⟨0, 0⟩
def CB2_3_3I2R9Mass : Ball := ⟨0, 0⟩
def CB2_3_3I2R9MassTerm : Ball := .exact 0
def CB2_3_3I2R9H : Ball := ⟨0, 0⟩
def CB2_3_3I2R10Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) 10 a
def CB2_3_3I2R10Entropy : Ball := ⟨0, 0⟩
def CB2_3_3I2R10Mass : Ball := ⟨0, 0⟩
def CB2_3_3I2R10MassTerm : Ball := .exact 0
def CB2_3_3I2R10H : Ball := ⟨0, 0⟩
def CB2_3_3I2R11Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) 11 a
def CB2_3_3I2R11Entropy : Ball := ⟨0, 0⟩
def CB2_3_3I2R11Mass : Ball := ⟨0, 0⟩
def CB2_3_3I2R11MassTerm : Ball := .exact 0
def CB2_3_3I2R11H : Ball := ⟨0, 0⟩
def CB2_3_3I2R12Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) 12 a
def CB2_3_3I2R12Entropy : Ball := ⟨0, 0⟩
def CB2_3_3I2R12Mass : Ball := ⟨0, 0⟩
def CB2_3_3I2R12MassTerm : Ball := .exact 0
def CB2_3_3I2R12H : Ball := ⟨0, 0⟩
def CB2_3_3I2R13Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) 13 a
def CB2_3_3I2R13Entropy : Ball := ⟨0, 0⟩
def CB2_3_3I2R13Mass : Ball := ⟨0, 0⟩
def CB2_3_3I2R13MassTerm : Ball := .exact 0
def CB2_3_3I2R13H : Ball := ⟨0, 0⟩
def CB2_3_3I2R14Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) 14 a
def CB2_3_3I2R14Entropy : Ball := ⟨0, 0⟩
def CB2_3_3I2R14Mass : Ball := ⟨0, 0⟩
def CB2_3_3I2R14MassTerm : Ball := .exact 0
def CB2_3_3I2R14H : Ball := ⟨0, 0⟩
def CB2_3_3I2R15Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) 15 a
def CB2_3_3I2R15Entropy : Ball := ⟨0, 0⟩
def CB2_3_3I2R15Mass : Ball := ⟨0, 0⟩
def CB2_3_3I2R15MassTerm : Ball := .exact 0
def CB2_3_3I2R15H : Ball := ⟨0, 0⟩
def CB2_3_3I2R16Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) 16 a
def CB2_3_3I2R16Entropy : Ball := ⟨0, 0⟩
def CB2_3_3I2R16Mass : Ball := ⟨0, 0⟩
def CB2_3_3I2R16MassTerm : Ball := .exact 0
def CB2_3_3I2R16H : Ball := ⟨0, 0⟩
def CB2_3_3I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CB2_3_3I2R0H
  | 1 => CB2_3_3I2R1H
  | 2 => CB2_3_3I2R2H
  | 3 => CB2_3_3I2R3H
  | 4 => CB2_3_3I2R4H
  | 5 => CB2_3_3I2R5H
  | 6 => CB2_3_3I2R6H
  | 7 => CB2_3_3I2R7H
  | 8 => CB2_3_3I2R8H
  | 9 => CB2_3_3I2R9H
  | 10 => CB2_3_3I2R10H
  | 11 => CB2_3_3I2R11H
  | 12 => CB2_3_3I2R12H
  | 13 => CB2_3_3I2R13H
  | 14 => CB2_3_3I2R14H
  | 15 => CB2_3_3I2R15H
  | 16 => CB2_3_3I2R16H
  | _ => (.exact 0)
def CB2_3_3I2S0_1_3Value (a : Fin 6) : ℝ := (littleLaw (shape 2 3 3) (shape 0 1 3) ((stageBPriority (shape 2 3 3)) 2) a : ℝ)
def CB2_3_3I2S0_1_3E_4Log : Ball := .exact 0
def CB2_3_3I2S0_1_3E_4 : Ball := ⟨0, 0⟩
def CB2_3_3I2S0_1_3Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB2_3_3I2S0_1_3Entropy : Ball := ⟨0, 0⟩
def CB2_3_3I2S0_1_3Mass : Ball := ⟨1, 0⟩
def CB2_3_3I2S0_1_3MassTermLog : Ball := .exact 0
def CB2_3_3I2S0_1_3MassTerm : Ball := ⟨0, 0⟩
def CB2_3_3I2S0_1_3H : Ball := ⟨0, 0⟩
def CB2_3_3I2S0_2_2Value (a : Fin 6) : ℝ := (littleLaw (shape 2 3 3) (shape 0 2 2) ((stageBPriority (shape 2 3 3)) 2) a : ℝ)
def CB2_3_3I2S0_2_2E_2LogWitness : LogWitness := ⟨-1, 444959, 250000⟩
def CB2_3_3I2S0_2_2E_2Log : Ball := ⟨(-5831297766604325579437218806789 / 50000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def CB2_3_3I2S0_2_2E_2 : Ball := ⟨(51893768458609882110016108861 / 500000000000000000000000000000), (37689493321 / 100000000000000000000000000000000)⟩
def CB2_3_3I2S0_2_2E_3LogWitness : LogWitness := ⟨-4, 55041, 31250⟩
def CB2_3_3I2S0_2_2E_3Log : Ball := ⟨(-55163243408937486421493177388873 / 25000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
def CB2_3_3I2S0_2_2E_3 : Ball := ⟨(3036240080471328190125405976661 / 12500000000000000000000000000000), (5827692557 / 50000000000000000000000000000000)⟩
def CB2_3_3I2S0_2_2Terms (a : Fin 6) : Ball :=
  match a.val with
  | 2 => ⟨(51893768458609882110016108861 / 500000000000000000000000000000), (37689493321 / 100000000000000000000000000000000)⟩
  | 3 => ⟨(3036240080471328190125405976661 / 12500000000000000000000000000000), (5827692557 / 50000000000000000000000000000000)⟩
  | _ => (.exact 0)
def CB2_3_3I2S0_2_2Entropy : Ball := ⟨(2166792145968287621437904349093 / 6250000000000000000000000000000), (9868975687 / 20000000000000000000000000000000)⟩
def CB2_3_3I2S0_2_2Mass : Ball := ⟨1, 0⟩
def CB2_3_3I2S0_2_2MassTermLog : Ball := .exact 0
def CB2_3_3I2S0_2_2MassTerm : Ball := ⟨0, 0⟩
def CB2_3_3I2S0_2_2H : Ball := ⟨(2166792145968287621437904349093 / 6250000000000000000000000000000), (9868975687 / 20000000000000000000000000000000)⟩
def CB2_3_3I2S0_3_1Value (a : Fin 6) : ℝ := (littleLaw (shape 2 3 3) (shape 0 3 1) ((stageBPriority (shape 2 3 3)) 2) a : ℝ)
def CB2_3_3I2S0_3_1E_1Log : Ball := .exact 0
def CB2_3_3I2S0_3_1E_1 : Ball := ⟨0, 0⟩
def CB2_3_3I2S0_3_1Terms (a : Fin 6) : Ball :=
  match a.val with
  | 1 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB2_3_3I2S0_3_1Entropy : Ball := ⟨0, 0⟩
def CB2_3_3I2S0_3_1Mass : Ball := ⟨1, 0⟩
def CB2_3_3I2S0_3_1MassTermLog : Ball := .exact 0
def CB2_3_3I2S0_3_1MassTerm : Ball := ⟨0, 0⟩
def CB2_3_3I2S0_3_1H : Ball := ⟨0, 0⟩
def CB2_3_3I2S1_0_3Value (a : Fin 6) : ℝ := (littleLaw (shape 2 3 3) (shape 1 0 3) ((stageBPriority (shape 2 3 3)) 2) a : ℝ)
def CB2_3_3I2S1_0_3E_4Log : Ball := .exact 0
def CB2_3_3I2S1_0_3E_4 : Ball := ⟨0, 0⟩
def CB2_3_3I2S1_0_3Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB2_3_3I2S1_0_3Entropy : Ball := ⟨0, 0⟩
def CB2_3_3I2S1_0_3Mass : Ball := ⟨1, 0⟩
def CB2_3_3I2S1_0_3MassTermLog : Ball := .exact 0
def CB2_3_3I2S1_0_3MassTerm : Ball := ⟨0, 0⟩
def CB2_3_3I2S1_0_3H : Ball := ⟨0, 0⟩
def CB2_3_3I2S2_0_2Value (a : Fin 6) : ℝ := (littleLaw (shape 2 3 3) (shape 2 0 2) ((stageBPriority (shape 2 3 3)) 2) a : ℝ)
def CB2_3_3I2S2_0_2E_2LogWitness : LogWitness := ⟨-1, 895909, 500000⟩
def CB2_3_3I2S2_0_2E_2Log : Ball := ⟨(-10991643366502651450018611428491 / 100000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def CB2_3_3I2S2_0_2E_2 : Ball := ⟨(615469513552501497370920259143 / 6250000000000000000000000000000), (37943222041 / 100000000000000000000000000000000)⟩
def CB2_3_3I2S2_0_2E_3LogWitness : LogWitness := ⟨-4, 104091, 62500⟩
def CB2_3_3I2S2_0_2E_3Log : Ball := ⟨(-56562244060752588474630885788059 / 25000000000000000000000000000000), (52939559207 / 50000000000000000000000000000000)⟩
def CB2_3_3I2S2_0_2E_3 : Ball := ⟨(23550482186111190747651214130259 / 100000000000000000000000000000000), (2755265829 / 25000000000000000000000000000000)⟩
def CB2_3_3I2S2_0_2Terms (a : Fin 6) : Ball :=
  match a.val with
  | 2 => ⟨(615469513552501497370920259143 / 6250000000000000000000000000000), (37943222041 / 100000000000000000000000000000000)⟩
  | 3 => ⟨(23550482186111190747651214130259 / 100000000000000000000000000000000), (2755265829 / 25000000000000000000000000000000)⟩
  | _ => (.exact 0)
def CB2_3_3I2S2_0_2Entropy : Ball := ⟨(33397994402951214705585938276547 / 100000000000000000000000000000000), (48964285357 / 100000000000000000000000000000000)⟩
def CB2_3_3I2S2_0_2Mass : Ball := ⟨1, 0⟩
def CB2_3_3I2S2_0_2MassTermLog : Ball := .exact 0
def CB2_3_3I2S2_0_2MassTerm : Ball := ⟨0, 0⟩
def CB2_3_3I2S2_0_2H : Ball := ⟨(33397994402951214705585938276547 / 100000000000000000000000000000000), (48964285357 / 100000000000000000000000000000000)⟩
def CB2_3_3I2Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 1, 3 => CB2_3_3I2S0_1_3H
  | 0, 2, 2 => CB2_3_3I2S0_2_2H
  | 0, 3, 1 => CB2_3_3I2S0_3_1H
  | 1, 0, 3 => CB2_3_3I2S1_0_3H
  | 2, 0, 2 => CB2_3_3I2S2_0_2H
  | _, _, _ => (.exact 0)
def CB2_3_3I2Singleton : Ball := ⟨(5996455110702665623701618784177 / 100000000000000000000000000000000), (8551510679 / 100000000000000000000000000000000)⟩
def CB2_3_3I2Group : Ball := ⟨(6913719818436670221564110676421 / 100000000000000000000000000000000), (56727157761 / 50000000000000000000000000000000)⟩

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
def CB2_3_3I2H : Ball := ⟨(10574410027224598465538854536769 / 12500000000000000000000000000000), (317853838437 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB2_4_2I0
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
def CB2_4_2I0Value (a : Fin 17) : ℝ := marginal (below (shape 2 4 2)) (fun u => (stageBLaw (shape 2 4 2) u : ℝ)) ((stageBPriority (shape 2 4 2)) 0) a
def CB2_4_2I0Entropy : Ball := ⟨(91406743097339094653419408019757 / 100000000000000000000000000000000), (5797509451 / 10000000000000000000000000000000)⟩
def CB2_4_2I0Mass : Ball := ⟨1, (231 / 100000000000000000000000000000000)⟩
def CB2_4_2I0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB2_4_2I0MassTermLog : Ball := ⟨0, (21175823913 / 100000000000000000000000000000000)⟩
def CB2_4_2I0MassTerm : Ball := ⟨0, (10587911957 / 50000000000000000000000000000000)⟩
def CB2_4_2I0H : Ball := ⟨(91406743097339094653419408019757 / 100000000000000000000000000000000), (9893864803 / 12500000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB2_4_2I1
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
def CB2_4_2I1PairEntropy : Ball := ⟨(10269267576713346525031730774743 / 10000000000000000000000000000000), (7514885453 / 12500000000000000000000000000000)⟩
def CB2_4_2I1PairMass : Ball := ⟨1, (47 / 20000000000000000000000000000000)⟩
def CB2_4_2I1PairMassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB2_4_2I1PairMassTermLog : Ball := ⟨0, (21175823917 / 100000000000000000000000000000000)⟩
def CB2_4_2I1PairMassTerm : Ball := ⟨0, (10587911959 / 50000000000000000000000000000000)⟩
def CB2_4_2I1PairH : Ball := ⟨(10269267576713346525031730774743 / 10000000000000000000000000000000), (40647453771 / 50000000000000000000000000000000)⟩

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
def CB2_4_2I1R0Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 4 2)) (fun u => (stageBLaw (shape 2 4 2) u : ℝ)) (stageBPriority (shape 2 4 2)) 1 (fun u a => (littleLaw (shape 2 4 2) u ((stageBPriority (shape 2 4 2)) 1) a : ℝ)) 0 a
def CB2_4_2I1R0Entropy : Ball := ⟨(31180563847682646222562347994213 / 100000000000000000000000000000000), (390636011 / 2500000000000000000000000000000)⟩
def CB2_4_2I1R0Mass : Ball := ⟨(18447263832039517395401339896779 / 100000000000000000000000000000000), (69 / 100000000000000000000000000000000)⟩
def CB2_4_2I1R0MassTermLogWitness : LogWitness := ⟨-3, 18447263832039517395401339896779, 12500000000000000000000000000000⟩
def CB2_4_2I1R0MassTermLog : Ball := ⟨(-42256353207145711870694366372109 / 25000000000000000000000000000000), (16940659021 / 20000000000000000000000000000000)⟩
def CB2_4_2I1R0MassTerm : Ball := ⟨(31180563847682646222562347994213 / 100000000000000000000000000000000), (390636011 / 2500000000000000000000000000000)⟩
def CB2_4_2I1R0H : Ball := ⟨0, (390636011 / 1250000000000000000000000000000)⟩
def CB2_4_2I1R1Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 4 2)) (fun u => (stageBLaw (shape 2 4 2) u : ℝ)) (stageBPriority (shape 2 4 2)) 1 (fun u a => (littleLaw (shape 2 4 2) u ((stageBPriority (shape 2 4 2)) 1) a : ℝ)) 1 a
def CB2_4_2I1R1Entropy : Ball := ⟨(14525702669047952430944640508619 / 50000000000000000000000000000000), (1670387953 / 6250000000000000000000000000000)⟩
def CB2_4_2I1R1Mass : Ball := ⟨(31552736167960482604598660103221 / 50000000000000000000000000000000), (93 / 100000000000000000000000000000000)⟩
def CB2_4_2I1R1MassTermLogWitness : LogWitness := ⟨-1, 31552736167960482604598660103221, 25000000000000000000000000000000⟩
def CB2_4_2I1R1MassTermLog : Ball := ⟨(-46036269538480631096329422118643 / 100000000000000000000000000000000), (42351647513 / 100000000000000000000000000000000)⟩
def CB2_4_2I1R1MassTerm : Ball := ⟨(14525702669047952430944640508619 / 50000000000000000000000000000000), (1670387953 / 6250000000000000000000000000000)⟩
def CB2_4_2I1R1H : Ball := ⟨0, (1670387953 / 3125000000000000000000000000000)⟩
def CB2_4_2I1R2Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 4 2)) (fun u => (stageBLaw (shape 2 4 2) u : ℝ)) (stageBPriority (shape 2 4 2)) 1 (fun u a => (littleLaw (shape 2 4 2) u ((stageBPriority (shape 2 4 2)) 1) a : ℝ)) 2 a
def CB2_4_2I1R2Entropy : Ball := ⟨(18394994260919096611303449609021 / 50000000000000000000000000000000), (4166819233 / 25000000000000000000000000000000)⟩
def CB2_4_2I1R2Mass : Ball := ⟨(9207198781517672306192161877829 / 50000000000000000000000000000000), (7 / 10000000000000000000000000000000)⟩
def CB2_4_2I1R2MassTermLogWitness : LogWitness := ⟨-3, 9207198781517672306192161877829, 6250000000000000000000000000000⟩
def CB2_4_2I1R2MassTermLog : Ball := ⟨(-84601867554808563020932609949299 / 50000000000000000000000000000000), (84703295111 / 100000000000000000000000000000000)⟩
def CB2_4_2I1R2MassTerm : Ball := ⟨(7789462118647528960199539877531 / 25000000000000000000000000000000), (1559760163 / 10000000000000000000000000000000)⟩
def CB2_4_2I1R2H : Ball := ⟨(2816070023624038690904369853959 / 50000000000000000000000000000000), (16132439281 / 50000000000000000000000000000000)⟩
def CB2_4_2I1R3Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 4 2)) (fun u => (stageBLaw (shape 2 4 2) u : ℝ)) (stageBPriority (shape 2 4 2)) 1 (fun u a => (littleLaw (shape 2 4 2) u ((stageBPriority (shape 2 4 2)) 1) a : ℝ)) 3 a
def CB2_4_2I1R3Entropy : Ball := ⟨0, 0⟩
def CB2_4_2I1R3Mass : Ball := ⟨0, 0⟩
def CB2_4_2I1R3MassTerm : Ball := .exact 0
def CB2_4_2I1R3H : Ball := ⟨0, 0⟩
def CB2_4_2I1R4Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 4 2)) (fun u => (stageBLaw (shape 2 4 2) u : ℝ)) (stageBPriority (shape 2 4 2)) 1 (fun u a => (littleLaw (shape 2 4 2) u ((stageBPriority (shape 2 4 2)) 1) a : ℝ)) 4 a
def CB2_4_2I1R4Entropy : Ball := ⟨0, 0⟩
def CB2_4_2I1R4Mass : Ball := ⟨0, 0⟩
def CB2_4_2I1R4MassTerm : Ball := .exact 0
def CB2_4_2I1R4H : Ball := ⟨0, 0⟩
def CB2_4_2I1R5Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 4 2)) (fun u => (stageBLaw (shape 2 4 2) u : ℝ)) (stageBPriority (shape 2 4 2)) 1 (fun u a => (littleLaw (shape 2 4 2) u ((stageBPriority (shape 2 4 2)) 1) a : ℝ)) 5 a
def CB2_4_2I1R5Entropy : Ball := ⟨0, 0⟩
def CB2_4_2I1R5Mass : Ball := ⟨0, 0⟩
def CB2_4_2I1R5MassTerm : Ball := .exact 0
def CB2_4_2I1R5H : Ball := ⟨0, 0⟩
def CB2_4_2I1R6Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 4 2)) (fun u => (stageBLaw (shape 2 4 2) u : ℝ)) (stageBPriority (shape 2 4 2)) 1 (fun u a => (littleLaw (shape 2 4 2) u ((stageBPriority (shape 2 4 2)) 1) a : ℝ)) 6 a
def CB2_4_2I1R6Entropy : Ball := ⟨0, 0⟩
def CB2_4_2I1R6Mass : Ball := ⟨0, 0⟩
def CB2_4_2I1R6MassTerm : Ball := .exact 0
def CB2_4_2I1R6H : Ball := ⟨0, 0⟩
def CB2_4_2I1R7Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 4 2)) (fun u => (stageBLaw (shape 2 4 2) u : ℝ)) (stageBPriority (shape 2 4 2)) 1 (fun u a => (littleLaw (shape 2 4 2) u ((stageBPriority (shape 2 4 2)) 1) a : ℝ)) 7 a
def CB2_4_2I1R7Entropy : Ball := ⟨0, 0⟩
def CB2_4_2I1R7Mass : Ball := ⟨0, 0⟩
def CB2_4_2I1R7MassTerm : Ball := .exact 0
def CB2_4_2I1R7H : Ball := ⟨0, 0⟩
def CB2_4_2I1R8Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 4 2)) (fun u => (stageBLaw (shape 2 4 2) u : ℝ)) (stageBPriority (shape 2 4 2)) 1 (fun u a => (littleLaw (shape 2 4 2) u ((stageBPriority (shape 2 4 2)) 1) a : ℝ)) 8 a
def CB2_4_2I1R8Entropy : Ball := ⟨0, 0⟩
def CB2_4_2I1R8Mass : Ball := ⟨0, 0⟩
def CB2_4_2I1R8MassTerm : Ball := .exact 0
def CB2_4_2I1R8H : Ball := ⟨0, 0⟩
def CB2_4_2I1R9Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 4 2)) (fun u => (stageBLaw (shape 2 4 2) u : ℝ)) (stageBPriority (shape 2 4 2)) 1 (fun u a => (littleLaw (shape 2 4 2) u ((stageBPriority (shape 2 4 2)) 1) a : ℝ)) 9 a
def CB2_4_2I1R9Entropy : Ball := ⟨0, 0⟩
def CB2_4_2I1R9Mass : Ball := ⟨0, 0⟩
def CB2_4_2I1R9MassTerm : Ball := .exact 0
def CB2_4_2I1R9H : Ball := ⟨0, 0⟩
def CB2_4_2I1R10Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 4 2)) (fun u => (stageBLaw (shape 2 4 2) u : ℝ)) (stageBPriority (shape 2 4 2)) 1 (fun u a => (littleLaw (shape 2 4 2) u ((stageBPriority (shape 2 4 2)) 1) a : ℝ)) 10 a
def CB2_4_2I1R10Entropy : Ball := ⟨0, 0⟩
def CB2_4_2I1R10Mass : Ball := ⟨0, 0⟩
def CB2_4_2I1R10MassTerm : Ball := .exact 0
def CB2_4_2I1R10H : Ball := ⟨0, 0⟩
def CB2_4_2I1R11Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 4 2)) (fun u => (stageBLaw (shape 2 4 2) u : ℝ)) (stageBPriority (shape 2 4 2)) 1 (fun u a => (littleLaw (shape 2 4 2) u ((stageBPriority (shape 2 4 2)) 1) a : ℝ)) 11 a
def CB2_4_2I1R11Entropy : Ball := ⟨0, 0⟩
def CB2_4_2I1R11Mass : Ball := ⟨0, 0⟩
def CB2_4_2I1R11MassTerm : Ball := .exact 0
def CB2_4_2I1R11H : Ball := ⟨0, 0⟩
def CB2_4_2I1R12Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 4 2)) (fun u => (stageBLaw (shape 2 4 2) u : ℝ)) (stageBPriority (shape 2 4 2)) 1 (fun u a => (littleLaw (shape 2 4 2) u ((stageBPriority (shape 2 4 2)) 1) a : ℝ)) 12 a
def CB2_4_2I1R12Entropy : Ball := ⟨0, 0⟩
def CB2_4_2I1R12Mass : Ball := ⟨0, 0⟩
def CB2_4_2I1R12MassTerm : Ball := .exact 0
def CB2_4_2I1R12H : Ball := ⟨0, 0⟩
def CB2_4_2I1R13Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 4 2)) (fun u => (stageBLaw (shape 2 4 2) u : ℝ)) (stageBPriority (shape 2 4 2)) 1 (fun u a => (littleLaw (shape 2 4 2) u ((stageBPriority (shape 2 4 2)) 1) a : ℝ)) 13 a
def CB2_4_2I1R13Entropy : Ball := ⟨0, 0⟩
def CB2_4_2I1R13Mass : Ball := ⟨0, 0⟩
def CB2_4_2I1R13MassTerm : Ball := .exact 0
def CB2_4_2I1R13H : Ball := ⟨0, 0⟩
def CB2_4_2I1R14Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 4 2)) (fun u => (stageBLaw (shape 2 4 2) u : ℝ)) (stageBPriority (shape 2 4 2)) 1 (fun u a => (littleLaw (shape 2 4 2) u ((stageBPriority (shape 2 4 2)) 1) a : ℝ)) 14 a
def CB2_4_2I1R14Entropy : Ball := ⟨0, 0⟩
def CB2_4_2I1R14Mass : Ball := ⟨0, 0⟩
def CB2_4_2I1R14MassTerm : Ball := .exact 0
def CB2_4_2I1R14H : Ball := ⟨0, 0⟩
def CB2_4_2I1R15Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 4 2)) (fun u => (stageBLaw (shape 2 4 2) u : ℝ)) (stageBPriority (shape 2 4 2)) 1 (fun u a => (littleLaw (shape 2 4 2) u ((stageBPriority (shape 2 4 2)) 1) a : ℝ)) 15 a
def CB2_4_2I1R15Entropy : Ball := ⟨0, 0⟩
def CB2_4_2I1R15Mass : Ball := ⟨0, 0⟩
def CB2_4_2I1R15MassTerm : Ball := .exact 0
def CB2_4_2I1R15H : Ball := ⟨0, 0⟩
def CB2_4_2I1R16Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 4 2)) (fun u => (stageBLaw (shape 2 4 2) u : ℝ)) (stageBPriority (shape 2 4 2)) 1 (fun u a => (littleLaw (shape 2 4 2) u ((stageBPriority (shape 2 4 2)) 1) a : ℝ)) 16 a
def CB2_4_2I1R16Entropy : Ball := ⟨0, 0⟩
def CB2_4_2I1R16Mass : Ball := ⟨0, 0⟩
def CB2_4_2I1R16MassTerm : Ball := .exact 0
def CB2_4_2I1R16H : Ball := ⟨0, 0⟩
def CB2_4_2I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CB2_4_2I1R0H
  | 1 => CB2_4_2I1R1H
  | 2 => CB2_4_2I1R2H
  | 3 => CB2_4_2I1R3H
  | 4 => CB2_4_2I1R4H
  | 5 => CB2_4_2I1R5H
  | 6 => CB2_4_2I1R6H
  | 7 => CB2_4_2I1R7H
  | 8 => CB2_4_2I1R8H
  | 9 => CB2_4_2I1R9H
  | 10 => CB2_4_2I1R10H
  | 11 => CB2_4_2I1R11H
  | 12 => CB2_4_2I1R12H
  | 13 => CB2_4_2I1R13H
  | 14 => CB2_4_2I1R14H
  | 15 => CB2_4_2I1R15H
  | 16 => CB2_4_2I1R16H
  | _ => (.exact 0)
def CB2_4_2I1S2_0_2Value (a : Fin 6) : ℝ := (littleLaw (shape 2 4 2) (shape 2 0 2) ((stageBPriority (shape 2 4 2)) 1) a : ℝ)
def CB2_4_2I1S2_0_2E_2LogWitness : LogWitness := ⟨-1, 468331, 250000⟩
def CB2_4_2I1S2_0_2E_2Log : Ball := ⟨(-817909844265902747909981412881 / 12500000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def CB2_4_2I1S2_0_2E_2 : Ball := ⟨(95763133818723624957857376269 / 1562500000000000000000000000000), (19834589363 / 50000000000000000000000000000000)⟩
def CB2_4_2I1S2_0_2E_3LogWitness : LogWitness := ⟨-4, 31669, 31250⟩
def CB2_4_2I1S2_0_2E_3Log : Ball := ⟨(-275926981399378237867248750022457 / 100000000000000000000000000000000), (52939559207 / 50000000000000000000000000000000)⟩
def CB2_4_2I1S2_0_2E_3 : Ball := ⟨(8738331573936909415017900664461 / 50000000000000000000000000000000), (6706171603 / 100000000000000000000000000000000)⟩
def CB2_4_2I1S2_0_2Terms (a : Fin 6) : Ball :=
  match a.val with
  | 2 => ⟨(95763133818723624957857376269 / 1562500000000000000000000000000), (19834589363 / 50000000000000000000000000000000)⟩
  | 3 => ⟨(8738331573936909415017900664461 / 50000000000000000000000000000000), (6706171603 / 100000000000000000000000000000000)⟩
  | _ => (.exact 0)
def CB2_4_2I1S2_0_2Entropy : Ball := ⟨(11802751856136065413669336705069 / 50000000000000000000000000000000), (46375350329 / 100000000000000000000000000000000)⟩
def CB2_4_2I1S2_0_2Mass : Ball := ⟨1, 0⟩
def CB2_4_2I1S2_0_2MassTermLog : Ball := .exact 0
def CB2_4_2I1S2_0_2MassTerm : Ball := ⟨0, 0⟩
def CB2_4_2I1S2_0_2H : Ball := ⟨(11802751856136065413669336705069 / 50000000000000000000000000000000), (46375350329 / 100000000000000000000000000000000)⟩
def CB2_4_2I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 2, 0, 2 => CB2_4_2I1S2_0_2H
  | _, _, _ => (.exact 0)
def CB2_4_2I1Singleton : Ball := ⟨(7758248349865350979731860157 / 100000000000000000000000000000000), (1905231 / 12500000000000000000000000000000)⟩
def CB2_4_2I1Group : Ball := ⟨(225595931823917709311538862723 / 4000000000000000000000000000000), (58491707893 / 50000000000000000000000000000000)⟩

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
def CB2_4_2I1H : Ball := ⟨(1142660989699219747309254557641 / 1250000000000000000000000000000), (157630869557 / 50000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB2_4_2I2
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
def CB2_4_2I2PairEntropy : Ball := ⟨(42571615482970303723282440519589 / 50000000000000000000000000000000), (58725469909 / 100000000000000000000000000000000)⟩
def CB2_4_2I2PairMass : Ball := ⟨1, (117 / 50000000000000000000000000000000)⟩
def CB2_4_2I2PairMassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB2_4_2I2PairMassTermLog : Ball := ⟨0, (5293955979 / 25000000000000000000000000000000)⟩
def CB2_4_2I2PairMassTerm : Ball := ⟨0, (21175823917 / 100000000000000000000000000000000)⟩
def CB2_4_2I2PairH : Ball := ⟨(42571615482970303723282440519589 / 50000000000000000000000000000000), (39950646913 / 50000000000000000000000000000000)⟩

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
def CB2_4_2I2R0Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 4 2)) (fun u => (stageBLaw (shape 2 4 2) u : ℝ)) (stageBPriority (shape 2 4 2)) 2 (fun u a => (littleLaw (shape 2 4 2) u ((stageBPriority (shape 2 4 2)) 2) a : ℝ)) 0 a
def CB2_4_2I2R0Entropy : Ball := ⟨(263603206926091894677212823061 / 100000000000000000000000000000000), (90476151 / 100000000000000000000000000000000)⟩
def CB2_4_2I2R0Mass : Ball := ⟨(32866269004172783017016141121 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def CB2_4_2I2R0MassTermLogWitness : LogWitness := ⟨-12, 32866269004172783017016141121, 24414062500000000000000000000⟩
def CB2_4_2I2R0MassTermLog : Ball := ⟨(-802047859136746485653157416152017 / 100000000000000000000000000000000), (275285710921 / 100000000000000000000000000000000)⟩
def CB2_4_2I2R0MassTerm : Ball := ⟨(263603206926091894677212823061 / 100000000000000000000000000000000), (90476151 / 100000000000000000000000000000000)⟩
def CB2_4_2I2R0H : Ball := ⟨0, (90476151 / 50000000000000000000000000000000)⟩
def CB2_4_2I2R1Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 4 2)) (fun u => (stageBLaw (shape 2 4 2) u : ℝ)) (stageBPriority (shape 2 4 2)) 2 (fun u a => (littleLaw (shape 2 4 2) u ((stageBPriority (shape 2 4 2)) 2) a : ℝ)) 1 a
def CB2_4_2I2R1Entropy : Ball := ⟨(19968586744498442177544038541237 / 100000000000000000000000000000000), (8306735557 / 100000000000000000000000000000000)⟩
def CB2_4_2I2R1Mass : Ball := ⟨(3922744904992762908135236404901 / 50000000000000000000000000000000), (31 / 100000000000000000000000000000000)⟩
def CB2_4_2I2R1MassTermLogWitness : LogWitness := ⟨-4, 3922744904992762908135236404901, 3125000000000000000000000000000⟩
def CB2_4_2I2R1MassTermLog : Ball := ⟨(-63630784145188005552858184192867 / 25000000000000000000000000000000), (10587911881 / 10000000000000000000000000000000)⟩
def CB2_4_2I2R1MassTerm : Ball := ⟨(19968586744498442177544038541237 / 100000000000000000000000000000000), (8306735557 / 100000000000000000000000000000000)⟩
def CB2_4_2I2R1H : Ball := ⟨0, (8306735557 / 50000000000000000000000000000000)⟩
def CB2_4_2I2R2Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 4 2)) (fun u => (stageBLaw (shape 2 4 2) u : ℝ)) (stageBPriority (shape 2 4 2)) 2 (fun u a => (littleLaw (shape 2 4 2) u ((stageBPriority (shape 2 4 2)) 2) a : ℝ)) 2 a
def CB2_4_2I2R2Entropy : Ball := ⟨(7264329299397631168292792115143 / 20000000000000000000000000000000), (24372262923 / 100000000000000000000000000000000)⟩
def CB2_4_2I2R2Mass : Ball := ⟨(6907792021600978205615474676497 / 12500000000000000000000000000000), (1 / 1562500000000000000000000000000)⟩
def CB2_4_2I2R2MassTermLogWitness : LogWitness := ⟨-1, 6907792021600978205615474676497, 6250000000000000000000000000000⟩
def CB2_4_2I2R2MassTermLog : Ball := ⟨(-59307859136746485653157626203699 / 100000000000000000000000000000000), (42351647481 / 100000000000000000000000000000000)⟩
def CB2_4_2I2R2MassTerm : Ball := ⟨(16387454246522082090302818465961 / 50000000000000000000000000000000), (5851127461 / 25000000000000000000000000000000)⟩
def CB2_4_2I2R2H : Ball := ⟨(3546738003943991660858323643793 / 100000000000000000000000000000000), (47776772767 / 100000000000000000000000000000000)⟩
def CB2_4_2I2R3Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 4 2)) (fun u => (stageBLaw (shape 2 4 2) u : ℝ)) (stageBPriority (shape 2 4 2)) 2 (fun u a => (littleLaw (shape 2 4 2) u ((stageBPriority (shape 2 4 2)) 2) a : ℝ)) 3 a
def CB2_4_2I2R3Entropy : Ball := ⟨0, 0⟩
def CB2_4_2I2R3Mass : Ball := ⟨0, 0⟩
def CB2_4_2I2R3MassTerm : Ball := .exact 0
def CB2_4_2I2R3H : Ball := ⟨0, 0⟩
def CB2_4_2I2R4Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 4 2)) (fun u => (stageBLaw (shape 2 4 2) u : ℝ)) (stageBPriority (shape 2 4 2)) 2 (fun u a => (littleLaw (shape 2 4 2) u ((stageBPriority (shape 2 4 2)) 2) a : ℝ)) 4 a
def CB2_4_2I2R4Entropy : Ball := ⟨0, 0⟩
def CB2_4_2I2R4Mass : Ball := ⟨0, 0⟩
def CB2_4_2I2R4MassTerm : Ball := .exact 0
def CB2_4_2I2R4H : Ball := ⟨0, 0⟩
def CB2_4_2I2R5Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 4 2)) (fun u => (stageBLaw (shape 2 4 2) u : ℝ)) (stageBPriority (shape 2 4 2)) 2 (fun u a => (littleLaw (shape 2 4 2) u ((stageBPriority (shape 2 4 2)) 2) a : ℝ)) 5 a
def CB2_4_2I2R5Entropy : Ball := ⟨0, 0⟩
def CB2_4_2I2R5Mass : Ball := ⟨0, 0⟩
def CB2_4_2I2R5MassTerm : Ball := .exact 0
def CB2_4_2I2R5H : Ball := ⟨0, 0⟩
def CB2_4_2I2R6Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 4 2)) (fun u => (stageBLaw (shape 2 4 2) u : ℝ)) (stageBPriority (shape 2 4 2)) 2 (fun u a => (littleLaw (shape 2 4 2) u ((stageBPriority (shape 2 4 2)) 2) a : ℝ)) 6 a
def CB2_4_2I2R6Entropy : Ball := ⟨0, 0⟩
def CB2_4_2I2R6Mass : Ball := ⟨0, 0⟩
def CB2_4_2I2R6MassTerm : Ball := .exact 0
def CB2_4_2I2R6H : Ball := ⟨0, 0⟩
def CB2_4_2I2R7Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 4 2)) (fun u => (stageBLaw (shape 2 4 2) u : ℝ)) (stageBPriority (shape 2 4 2)) 2 (fun u a => (littleLaw (shape 2 4 2) u ((stageBPriority (shape 2 4 2)) 2) a : ℝ)) 7 a
def CB2_4_2I2R7Entropy : Ball := ⟨0, 0⟩
def CB2_4_2I2R7Mass : Ball := ⟨0, 0⟩
def CB2_4_2I2R7MassTerm : Ball := .exact 0
def CB2_4_2I2R7H : Ball := ⟨0, 0⟩
def CB2_4_2I2R8Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 4 2)) (fun u => (stageBLaw (shape 2 4 2) u : ℝ)) (stageBPriority (shape 2 4 2)) 2 (fun u a => (littleLaw (shape 2 4 2) u ((stageBPriority (shape 2 4 2)) 2) a : ℝ)) 8 a
def CB2_4_2I2R8Entropy : Ball := ⟨0, 0⟩
def CB2_4_2I2R8Mass : Ball := ⟨0, 0⟩
def CB2_4_2I2R8MassTerm : Ball := .exact 0
def CB2_4_2I2R8H : Ball := ⟨0, 0⟩
def CB2_4_2I2R9Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 4 2)) (fun u => (stageBLaw (shape 2 4 2) u : ℝ)) (stageBPriority (shape 2 4 2)) 2 (fun u a => (littleLaw (shape 2 4 2) u ((stageBPriority (shape 2 4 2)) 2) a : ℝ)) 9 a
def CB2_4_2I2R9Entropy : Ball := ⟨0, 0⟩
def CB2_4_2I2R9Mass : Ball := ⟨0, 0⟩
def CB2_4_2I2R9MassTerm : Ball := .exact 0
def CB2_4_2I2R9H : Ball := ⟨0, 0⟩
def CB2_4_2I2R10Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 4 2)) (fun u => (stageBLaw (shape 2 4 2) u : ℝ)) (stageBPriority (shape 2 4 2)) 2 (fun u a => (littleLaw (shape 2 4 2) u ((stageBPriority (shape 2 4 2)) 2) a : ℝ)) 10 a
def CB2_4_2I2R10Entropy : Ball := ⟨0, 0⟩
def CB2_4_2I2R10Mass : Ball := ⟨0, 0⟩
def CB2_4_2I2R10MassTerm : Ball := .exact 0
def CB2_4_2I2R10H : Ball := ⟨0, 0⟩
def CB2_4_2I2R11Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 4 2)) (fun u => (stageBLaw (shape 2 4 2) u : ℝ)) (stageBPriority (shape 2 4 2)) 2 (fun u a => (littleLaw (shape 2 4 2) u ((stageBPriority (shape 2 4 2)) 2) a : ℝ)) 11 a
def CB2_4_2I2R11Entropy : Ball := ⟨0, 0⟩
def CB2_4_2I2R11Mass : Ball := ⟨0, 0⟩
def CB2_4_2I2R11MassTerm : Ball := .exact 0
def CB2_4_2I2R11H : Ball := ⟨0, 0⟩
def CB2_4_2I2R12Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 4 2)) (fun u => (stageBLaw (shape 2 4 2) u : ℝ)) (stageBPriority (shape 2 4 2)) 2 (fun u a => (littleLaw (shape 2 4 2) u ((stageBPriority (shape 2 4 2)) 2) a : ℝ)) 12 a
def CB2_4_2I2R12Entropy : Ball := ⟨0, 0⟩
def CB2_4_2I2R12Mass : Ball := ⟨0, 0⟩
def CB2_4_2I2R12MassTerm : Ball := .exact 0
def CB2_4_2I2R12H : Ball := ⟨0, 0⟩
def CB2_4_2I2R13Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 4 2)) (fun u => (stageBLaw (shape 2 4 2) u : ℝ)) (stageBPriority (shape 2 4 2)) 2 (fun u a => (littleLaw (shape 2 4 2) u ((stageBPriority (shape 2 4 2)) 2) a : ℝ)) 13 a
def CB2_4_2I2R13Entropy : Ball := ⟨0, 0⟩
def CB2_4_2I2R13Mass : Ball := ⟨0, 0⟩
def CB2_4_2I2R13MassTerm : Ball := .exact 0
def CB2_4_2I2R13H : Ball := ⟨0, 0⟩
def CB2_4_2I2R14Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 4 2)) (fun u => (stageBLaw (shape 2 4 2) u : ℝ)) (stageBPriority (shape 2 4 2)) 2 (fun u a => (littleLaw (shape 2 4 2) u ((stageBPriority (shape 2 4 2)) 2) a : ℝ)) 14 a
def CB2_4_2I2R14Entropy : Ball := ⟨0, 0⟩
def CB2_4_2I2R14Mass : Ball := ⟨0, 0⟩
def CB2_4_2I2R14MassTerm : Ball := .exact 0
def CB2_4_2I2R14H : Ball := ⟨0, 0⟩
def CB2_4_2I2R15Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 4 2)) (fun u => (stageBLaw (shape 2 4 2) u : ℝ)) (stageBPriority (shape 2 4 2)) 2 (fun u a => (littleLaw (shape 2 4 2) u ((stageBPriority (shape 2 4 2)) 2) a : ℝ)) 15 a
def CB2_4_2I2R15Entropy : Ball := ⟨0, 0⟩
def CB2_4_2I2R15Mass : Ball := ⟨0, 0⟩
def CB2_4_2I2R15MassTerm : Ball := .exact 0
def CB2_4_2I2R15H : Ball := ⟨0, 0⟩
def CB2_4_2I2R16Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 4 2)) (fun u => (stageBLaw (shape 2 4 2) u : ℝ)) (stageBPriority (shape 2 4 2)) 2 (fun u a => (littleLaw (shape 2 4 2) u ((stageBPriority (shape 2 4 2)) 2) a : ℝ)) 16 a
def CB2_4_2I2R16Entropy : Ball := ⟨0, 0⟩
def CB2_4_2I2R16Mass : Ball := ⟨0, 0⟩
def CB2_4_2I2R16MassTerm : Ball := .exact 0
def CB2_4_2I2R16H : Ball := ⟨0, 0⟩
def CB2_4_2I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CB2_4_2I2R0H
  | 1 => CB2_4_2I2R1H
  | 2 => CB2_4_2I2R2H
  | 3 => CB2_4_2I2R3H
  | 4 => CB2_4_2I2R4H
  | 5 => CB2_4_2I2R5H
  | 6 => CB2_4_2I2R6H
  | 7 => CB2_4_2I2R7H
  | 8 => CB2_4_2I2R8H
  | 9 => CB2_4_2I2R9H
  | 10 => CB2_4_2I2R10H
  | 11 => CB2_4_2I2R11H
  | 12 => CB2_4_2I2R12H
  | 13 => CB2_4_2I2R13H
  | 14 => CB2_4_2I2R14H
  | 15 => CB2_4_2I2R15H
  | 16 => CB2_4_2I2R16H
  | _ => (.exact 0)
def CB2_4_2I2S0_2_2Value (a : Fin 6) : ℝ := (littleLaw (shape 2 4 2) (shape 0 2 2) ((stageBPriority (shape 2 4 2)) 2) a : ℝ)
def CB2_4_2I2S0_2_2E_2LogWitness : LogWitness := ⟨-1, 895207, 500000⟩
def CB2_4_2I2S0_2_2E_2Log : Ball := ⟨(-22140060506662698219615744903 / 200000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def CB2_4_2I2S0_2_2E_2 : Ball := ⟨(990996857299399704254377607369 / 10000000000000000000000000000000), (2369593199 / 6250000000000000000000000000000)⟩
def CB2_4_2I2S0_2_2E_3LogWitness : LogWitness := ⟨-4, 104793, 62500⟩
def CB2_4_2I2S0_2_2E_3Log : Ball := ⟨(-22557683032191364513180248834139 / 10000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
def CB2_4_2I2S0_2_2E_3 : Ball := ⟨(23638872779924296614296978160759 / 100000000000000000000000000000000), (11095390457 / 100000000000000000000000000000000)⟩
def CB2_4_2I2S0_2_2Terms (a : Fin 6) : Ball :=
  match a.val with
  | 2 => ⟨(990996857299399704254377607369 / 10000000000000000000000000000000), (2369593199 / 6250000000000000000000000000000)⟩
  | 3 => ⟨(23638872779924296614296978160759 / 100000000000000000000000000000000), (11095390457 / 100000000000000000000000000000000)⟩
  | _ => (.exact 0)
def CB2_4_2I2S0_2_2Entropy : Ball := ⟨(33548841352918293656840754234449 / 100000000000000000000000000000000), (49008881641 / 100000000000000000000000000000000)⟩
def CB2_4_2I2S0_2_2Mass : Ball := ⟨1, 0⟩
def CB2_4_2I2S0_2_2MassTermLog : Ball := .exact 0
def CB2_4_2I2S0_2_2MassTerm : Ball := ⟨0, 0⟩
def CB2_4_2I2S0_2_2H : Ball := ⟨(33548841352918293656840754234449 / 100000000000000000000000000000000), (49008881641 / 100000000000000000000000000000000)⟩
def CB2_4_2I2S0_3_1Value (a : Fin 6) : ℝ := (littleLaw (shape 2 4 2) (shape 0 3 1) ((stageBPriority (shape 2 4 2)) 2) a : ℝ)
def CB2_4_2I2S0_3_1E_4Log : Ball := .exact 0
def CB2_4_2I2S0_3_1E_4 : Ball := ⟨0, 0⟩
def CB2_4_2I2S0_3_1Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB2_4_2I2S0_3_1Entropy : Ball := ⟨0, 0⟩
def CB2_4_2I2S0_3_1Mass : Ball := ⟨1, 0⟩
def CB2_4_2I2S0_3_1MassTermLog : Ball := .exact 0
def CB2_4_2I2S0_3_1MassTerm : Ball := ⟨0, 0⟩
def CB2_4_2I2S0_3_1H : Ball := ⟨0, 0⟩
def CB2_4_2I2S0_4_0Value (a : Fin 6) : ℝ := (littleLaw (shape 2 4 2) (shape 0 4 0) ((stageBPriority (shape 2 4 2)) 2) a : ℝ)
def CB2_4_2I2S0_4_0E_5Log : Ball := .exact 0
def CB2_4_2I2S0_4_0E_5 : Ball := ⟨0, 0⟩
def CB2_4_2I2S0_4_0Terms (a : Fin 6) : Ball :=
  match a.val with
  | 5 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB2_4_2I2S0_4_0Entropy : Ball := ⟨0, 0⟩
def CB2_4_2I2S0_4_0Mass : Ball := ⟨1, 0⟩
def CB2_4_2I2S0_4_0MassTermLog : Ball := .exact 0
def CB2_4_2I2S0_4_0MassTerm : Ball := ⟨0, 0⟩
def CB2_4_2I2S0_4_0H : Ball := ⟨0, 0⟩
def CB2_4_2I2S1_3_0Value (a : Fin 6) : ℝ := (littleLaw (shape 2 4 2) (shape 1 3 0) ((stageBPriority (shape 2 4 2)) 2) a : ℝ)
def CB2_4_2I2S1_3_0E_4Log : Ball := .exact 0
def CB2_4_2I2S1_3_0E_4 : Ball := ⟨0, 0⟩
def CB2_4_2I2S1_3_0Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB2_4_2I2S1_3_0Entropy : Ball := ⟨0, 0⟩
def CB2_4_2I2S1_3_0Mass : Ball := ⟨1, 0⟩
def CB2_4_2I2S1_3_0MassTermLog : Ball := .exact 0
def CB2_4_2I2S1_3_0MassTerm : Ball := ⟨0, 0⟩
def CB2_4_2I2S1_3_0H : Ball := ⟨0, 0⟩
def CB2_4_2I2S2_2_0Value (a : Fin 6) : ℝ := (littleLaw (shape 2 4 2) (shape 2 2 0) ((stageBPriority (shape 2 4 2)) 2) a : ℝ)
def CB2_4_2I2S2_2_0E_2LogWitness : LogWitness := ⟨-1, 27973, 15625⟩
def CB2_4_2I2S2_2_0E_2Log : Ball := ⟨(-2769490423601434424009732717579 / 25000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def CB2_4_2I2S2_2_0E_2 : Ball := ⟨(9916282319283574418281504423531 / 100000000000000000000000000000000), (37910484217 / 100000000000000000000000000000000)⟩
def CB2_4_2I2S2_2_0E_3LogWitness : LogWitness := ⟨-4, 26216, 15625⟩
def CB2_4_2I2S2_2_0E_3Log : Ball := ⟨(-56377275161643324031409595775453 / 25000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
def CB2_4_2I2S2_2_0E_3 : Ball := ⟨(5911946582550565531229735851397 / 25000000000000000000000000000000), (5551453937 / 50000000000000000000000000000000)⟩
def CB2_4_2I2S2_2_0Terms (a : Fin 6) : Ball :=
  match a.val with
  | 2 => ⟨(9916282319283574418281504423531 / 100000000000000000000000000000000), (37910484217 / 100000000000000000000000000000000)⟩
  | 3 => ⟨(5911946582550565531229735851397 / 25000000000000000000000000000000), (5551453937 / 50000000000000000000000000000000)⟩
  | _ => (.exact 0)
def CB2_4_2I2S2_2_0Entropy : Ball := ⟨(33564068649485836543200447829119 / 100000000000000000000000000000000), (49013392091 / 100000000000000000000000000000000)⟩
def CB2_4_2I2S2_2_0Mass : Ball := ⟨1, 0⟩
def CB2_4_2I2S2_2_0MassTermLog : Ball := .exact 0
def CB2_4_2I2S2_2_0MassTerm : Ball := ⟨0, 0⟩
def CB2_4_2I2S2_2_0H : Ball := ⟨(33564068649485836543200447829119 / 100000000000000000000000000000000), (49013392091 / 100000000000000000000000000000000)⟩
def CB2_4_2I2Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => CB2_4_2I2S0_2_2H
  | 0, 3, 1 => CB2_4_2I2S0_3_1H
  | 0, 4, 0 => CB2_4_2I2S0_4_0H
  | 1, 3, 0 => CB2_4_2I2S1_3_0H
  | 2, 2, 0 => CB2_4_2I2S2_2_0H
  | _, _, _ => (.exact 0)
def CB2_4_2I2Singleton : Ball := ⟨(972498000579950432644105765027 / 10000000000000000000000000000000), (14203893923 / 100000000000000000000000000000000)⟩
def CB2_4_2I2Group : Ball := ⟨(13271718009743495987299381294063 / 100000000000000000000000000000000), (39387545053 / 50000000000000000000000000000000)⟩

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
def CB2_4_2I2H : Ball := ⟨(14649948736613403867991529612763 / 25000000000000000000000000000000), (118725737019 / 50000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB2_5_1I0
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
def CB2_5_1I0Value (a : Fin 17) : ℝ := marginal (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) ((stageBPriority (shape 2 5 1)) 0) a
def CB2_5_1I0Entropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (21175823759 / 50000000000000000000000000000000)⟩
def CB2_5_1I0Mass : Ball := ⟨1, (9 / 10000000000000000000000000000000)⟩
def CB2_5_1I0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB2_5_1I0MassTermLog : Ball := ⟨0, (5293955943 / 25000000000000000000000000000000)⟩
def CB2_5_1I0MassTerm : Ball := ⟨0, (21175823773 / 100000000000000000000000000000000)⟩
def CB2_5_1I0H : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (63527471291 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB2_5_1I1
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
def CB2_5_1I1PairEntropy : Ball := ⟨(104127998046199018853850763540011 / 100000000000000000000000000000000), (60535873137 / 100000000000000000000000000000000)⟩
def CB2_5_1I1PairMass : Ball := ⟨1, (23 / 25000000000000000000000000000000)⟩
def CB2_5_1I1PairMassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB2_5_1I1PairMassTermLog : Ball := ⟨0, (10587911887 / 50000000000000000000000000000000)⟩
def CB2_5_1I1PairMassTerm : Ball := ⟨0, (847032951 / 4000000000000000000000000000000)⟩
def CB2_5_1I1PairH : Ball := ⟨(104127998046199018853850763540011 / 100000000000000000000000000000000), (5106981057 / 6250000000000000000000000000000)⟩

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
def CB2_5_1I1R0Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 1 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 1) a : ℝ)) 0 a
def CB2_5_1I1R0Entropy : Ball := ⟨(15604168792971093202814348314073 / 50000000000000000000000000000000), (7829788181 / 50000000000000000000000000000000)⟩
def CB2_5_1I1R0Mass : Ball := ⟨(18487564536437762690016551716173 / 100000000000000000000000000000000), (31 / 100000000000000000000000000000000)⟩
def CB2_5_1I1R0MassTermLogWitness : LogWitness := ⟨-3, 18487564536437762690016551716173, 12500000000000000000000000000000⟩
def CB2_5_1I1R0MassTermLog : Ball := ⟨(-21100898339281402038513976200687 / 12500000000000000000000000000000), (84703294899 / 100000000000000000000000000000000)⟩
def CB2_5_1I1R0MassTerm : Ball := ⟨(15604168792971093202814348314073 / 50000000000000000000000000000000), (7829788181 / 50000000000000000000000000000000)⟩
def CB2_5_1I1R0H : Ball := ⟨0, (7829788181 / 25000000000000000000000000000000)⟩
def CB2_5_1I1R1Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 1 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 1) a : ℝ)) 1 a
def CB2_5_1I1R1Entropy : Ball := ⟨(5818969873823774875978045709193 / 20000000000000000000000000000000), (26692071129 / 100000000000000000000000000000000)⟩
def CB2_5_1I1R1Mass : Ball := ⟨(31512435463562237309983448283827 / 50000000000000000000000000000000), (7 / 25000000000000000000000000000000)⟩
def CB2_5_1I1R1MassTermLogWitness : LogWitness := ⟨-1, 31512435463562237309983448283827, 25000000000000000000000000000000⟩
def CB2_5_1I1R1MassTermLog : Ball := ⟨(-23082038043966156920661634460399 / 50000000000000000000000000000000), (4235164741 / 10000000000000000000000000000000)⟩
def CB2_5_1I1R1MassTerm : Ball := ⟨(5818969873823774875978045709193 / 20000000000000000000000000000000), (26692071129 / 100000000000000000000000000000000)⟩
def CB2_5_1I1R1H : Ball := ⟨0, (26692071129 / 50000000000000000000000000000000)⟩
def CB2_5_1I1R2Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 1 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 1) a : ℝ)) 2 a
def CB2_5_1I1R2Entropy : Ball := ⟨(37516574338540072236980267497023 / 100000000000000000000000000000000), (4230475251 / 25000000000000000000000000000000)⟩
def CB2_5_1I1R2Mass : Ball := ⟨(18487564536437762690016551716173 / 100000000000000000000000000000000), (1 / 3125000000000000000000000000000)⟩
def CB2_5_1I1R2MassTermLogWitness : LogWitness := ⟨-3, 18487564536437762690016551716173, 12500000000000000000000000000000⟩
def CB2_5_1I1R2MassTermLog : Ball := ⟨(-21100898339281402038513976200687 / 12500000000000000000000000000000), (16940658981 / 20000000000000000000000000000000)⟩
def CB2_5_1I1R2MassTerm : Ball := ⟨(15604168792971093202814348314073 / 50000000000000000000000000000000), (3131915273 / 20000000000000000000000000000000)⟩
def CB2_5_1I1R2H : Ball := ⟨(6308236752597885831351570868877 / 100000000000000000000000000000000), (32581477369 / 100000000000000000000000000000000)⟩
def CB2_5_1I1R3Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 1 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 1) a : ℝ)) 3 a
def CB2_5_1I1R3Entropy : Ball := ⟨0, 0⟩
def CB2_5_1I1R3Mass : Ball := ⟨0, 0⟩
def CB2_5_1I1R3MassTerm : Ball := .exact 0
def CB2_5_1I1R3H : Ball := ⟨0, 0⟩
def CB2_5_1I1R4Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 1 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 1) a : ℝ)) 4 a
def CB2_5_1I1R4Entropy : Ball := ⟨0, 0⟩
def CB2_5_1I1R4Mass : Ball := ⟨0, 0⟩
def CB2_5_1I1R4MassTerm : Ball := .exact 0
def CB2_5_1I1R4H : Ball := ⟨0, 0⟩
def CB2_5_1I1R5Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 1 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 1) a : ℝ)) 5 a
def CB2_5_1I1R5Entropy : Ball := ⟨0, 0⟩
def CB2_5_1I1R5Mass : Ball := ⟨0, 0⟩
def CB2_5_1I1R5MassTerm : Ball := .exact 0
def CB2_5_1I1R5H : Ball := ⟨0, 0⟩
def CB2_5_1I1R6Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 1 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 1) a : ℝ)) 6 a
def CB2_5_1I1R6Entropy : Ball := ⟨0, 0⟩
def CB2_5_1I1R6Mass : Ball := ⟨0, 0⟩
def CB2_5_1I1R6MassTerm : Ball := .exact 0
def CB2_5_1I1R6H : Ball := ⟨0, 0⟩
def CB2_5_1I1R7Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 1 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 1) a : ℝ)) 7 a
def CB2_5_1I1R7Entropy : Ball := ⟨0, 0⟩
def CB2_5_1I1R7Mass : Ball := ⟨0, 0⟩
def CB2_5_1I1R7MassTerm : Ball := .exact 0
def CB2_5_1I1R7H : Ball := ⟨0, 0⟩
def CB2_5_1I1R8Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 1 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 1) a : ℝ)) 8 a
def CB2_5_1I1R8Entropy : Ball := ⟨0, 0⟩
def CB2_5_1I1R8Mass : Ball := ⟨0, 0⟩
def CB2_5_1I1R8MassTerm : Ball := .exact 0
def CB2_5_1I1R8H : Ball := ⟨0, 0⟩
def CB2_5_1I1R9Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 1 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 1) a : ℝ)) 9 a
def CB2_5_1I1R9Entropy : Ball := ⟨0, 0⟩
def CB2_5_1I1R9Mass : Ball := ⟨0, 0⟩
def CB2_5_1I1R9MassTerm : Ball := .exact 0
def CB2_5_1I1R9H : Ball := ⟨0, 0⟩
def CB2_5_1I1R10Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 1 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 1) a : ℝ)) 10 a
def CB2_5_1I1R10Entropy : Ball := ⟨0, 0⟩
def CB2_5_1I1R10Mass : Ball := ⟨0, 0⟩
def CB2_5_1I1R10MassTerm : Ball := .exact 0
def CB2_5_1I1R10H : Ball := ⟨0, 0⟩
def CB2_5_1I1R11Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 1 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 1) a : ℝ)) 11 a
def CB2_5_1I1R11Entropy : Ball := ⟨0, 0⟩
def CB2_5_1I1R11Mass : Ball := ⟨0, 0⟩
def CB2_5_1I1R11MassTerm : Ball := .exact 0
def CB2_5_1I1R11H : Ball := ⟨0, 0⟩
def CB2_5_1I1R12Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 1 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 1) a : ℝ)) 12 a
def CB2_5_1I1R12Entropy : Ball := ⟨0, 0⟩
def CB2_5_1I1R12Mass : Ball := ⟨0, 0⟩
def CB2_5_1I1R12MassTerm : Ball := .exact 0
def CB2_5_1I1R12H : Ball := ⟨0, 0⟩
def CB2_5_1I1R13Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 1 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 1) a : ℝ)) 13 a
def CB2_5_1I1R13Entropy : Ball := ⟨0, 0⟩
def CB2_5_1I1R13Mass : Ball := ⟨0, 0⟩
def CB2_5_1I1R13MassTerm : Ball := .exact 0
def CB2_5_1I1R13H : Ball := ⟨0, 0⟩
def CB2_5_1I1R14Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 1 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 1) a : ℝ)) 14 a
def CB2_5_1I1R14Entropy : Ball := ⟨0, 0⟩
def CB2_5_1I1R14Mass : Ball := ⟨0, 0⟩
def CB2_5_1I1R14MassTerm : Ball := .exact 0
def CB2_5_1I1R14H : Ball := ⟨0, 0⟩
def CB2_5_1I1R15Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 1 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 1) a : ℝ)) 15 a
def CB2_5_1I1R15Entropy : Ball := ⟨0, 0⟩
def CB2_5_1I1R15Mass : Ball := ⟨0, 0⟩
def CB2_5_1I1R15MassTerm : Ball := .exact 0
def CB2_5_1I1R15H : Ball := ⟨0, 0⟩
def CB2_5_1I1R16Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 1 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 1) a : ℝ)) 16 a
def CB2_5_1I1R16Entropy : Ball := ⟨0, 0⟩
def CB2_5_1I1R16Mass : Ball := ⟨0, 0⟩
def CB2_5_1I1R16MassTerm : Ball := .exact 0
def CB2_5_1I1R16H : Ball := ⟨0, 0⟩
def CB2_5_1I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CB2_5_1I1R0H
  | 1 => CB2_5_1I1R1H
  | 2 => CB2_5_1I1R2H
  | 3 => CB2_5_1I1R3H
  | 4 => CB2_5_1I1R4H
  | 5 => CB2_5_1I1R5H
  | 6 => CB2_5_1I1R6H
  | 7 => CB2_5_1I1R7H
  | 8 => CB2_5_1I1R8H
  | 9 => CB2_5_1I1R9H
  | 10 => CB2_5_1I1R10H
  | 11 => CB2_5_1I1R11H
  | 12 => CB2_5_1I1R12H
  | 13 => CB2_5_1I1R13H
  | 14 => CB2_5_1I1R14H
  | 15 => CB2_5_1I1R15H
  | 16 => CB2_5_1I1R16H
  | _ => (.exact 0)
def CB2_5_1I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | _, _, _ => (.exact 0)
def CB2_5_1I1Singleton : Ball := ⟨0, 0⟩
def CB2_5_1I1Group : Ball := ⟨(6308236752597885831351570868877 / 100000000000000000000000000000000), (117284772351 / 100000000000000000000000000000000)⟩

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
def CB2_5_1I1H : Ball := ⟨(91511524541003247191147621802257 / 100000000000000000000000000000000), (158140620807 / 50000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB2_5_1I2
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
def CB2_5_1I2PairEntropy : Ball := ⟨(293552408612091855129500575607 / 312500000000000000000000000000), (4302290427 / 6250000000000000000000000000000)⟩
def CB2_5_1I2PairMass : Ball := ⟨1, (23 / 25000000000000000000000000000000)⟩
def CB2_5_1I2PairMassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB2_5_1I2PairMassTermLog : Ball := ⟨0, (10587911887 / 50000000000000000000000000000000)⟩
def CB2_5_1I2PairMassTerm : Ball := ⟨0, (847032951 / 4000000000000000000000000000000)⟩
def CB2_5_1I2PairH : Ball := ⟨(293552408612091855129500575607 / 312500000000000000000000000000), (90012470607 / 100000000000000000000000000000000)⟩

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
def CB2_5_1I2R0Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) 0 a
def CB2_5_1I2R0Entropy : Ball := ⟨0, 0⟩
def CB2_5_1I2R0Mass : Ball := ⟨0, 0⟩
def CB2_5_1I2R0MassTerm : Ball := .exact 0
def CB2_5_1I2R0H : Ball := ⟨0, 0⟩
def CB2_5_1I2R1Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) 1 a
def CB2_5_1I2R1Entropy : Ball := ⟨(877420057559102802694039590203 / 25000000000000000000000000000000), (168951303 / 12500000000000000000000000000000)⟩
def CB2_5_1I2R1Mass : Ball := ⟨(354599982032740129828053827979 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def CB2_5_1I2R1MassTermLogWitness : LogWitness := ⟨-8, 354599982032740129828053827979, 195312500000000000000000000000⟩
def CB2_5_1I2R1MassTermLog : Ball := ⟨(-494878794143926844783046347417239 / 100000000000000000000000000000000), (19058241357 / 10000000000000000000000000000000)⟩
def CB2_5_1I2R1MassTerm : Ball := ⟨(877420057559102802694039590203 / 25000000000000000000000000000000), (168951303 / 12500000000000000000000000000000)⟩
def CB2_5_1I2R1H : Ball := ⟨0, (168951303 / 6250000000000000000000000000000)⟩
def CB2_5_1I2R2Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) 2 a
def CB2_5_1I2R2Entropy : Ball := ⟨(37139449891745745685566848755703 / 100000000000000000000000000000000), (808421691 / 4000000000000000000000000000000)⟩
def CB2_5_1I2R2Mass : Ball := ⟨(31512435463562237309983448283827 / 100000000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩
def CB2_5_1I2R2MassTermLogWitness : LogWitness := ⟨-2, 31512435463562237309983448283827, 25000000000000000000000000000000⟩
def CB2_5_1I2R2MassTermLog : Ball := ⟨(-14434849267990855597880807746391 / 12500000000000000000000000000000), (63527471099 / 100000000000000000000000000000000)⟩
def CB2_5_1I2R2MassTerm : Ball := ⟨(18195090239352417580992918396093 / 50000000000000000000000000000000), (20019053351 / 100000000000000000000000000000000)⟩
def CB2_5_1I2R2H : Ball := ⟨(749269413040910523581011963517 / 100000000000000000000000000000000), (20114797813 / 50000000000000000000000000000000)⟩
def CB2_5_1I2R3Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) 3 a
def CB2_5_1I2R3Entropy : Ball := ⟨0, 0⟩
def CB2_5_1I2R3Mass : Ball := ⟨0, 0⟩
def CB2_5_1I2R3MassTerm : Ball := .exact 0
def CB2_5_1I2R3H : Ball := ⟨0, 0⟩
def CB2_5_1I2R4Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) 4 a
def CB2_5_1I2R4Entropy : Ball := ⟨0, 0⟩
def CB2_5_1I2R4Mass : Ball := ⟨0, 0⟩
def CB2_5_1I2R4MassTerm : Ball := .exact 0
def CB2_5_1I2R4H : Ball := ⟨0, 0⟩
def CB2_5_1I2R5Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) 5 a
def CB2_5_1I2R5Entropy : Ball := ⟨0, 0⟩
def CB2_5_1I2R5Mass : Ball := ⟨0, 0⟩
def CB2_5_1I2R5MassTerm : Ball := .exact 0
def CB2_5_1I2R5H : Ball := ⟨0, 0⟩
def CB2_5_1I2R6Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) 6 a
def CB2_5_1I2R6Entropy : Ball := ⟨0, 0⟩
def CB2_5_1I2R6Mass : Ball := ⟨0, 0⟩
def CB2_5_1I2R6MassTerm : Ball := .exact 0
def CB2_5_1I2R6H : Ball := ⟨0, 0⟩
def CB2_5_1I2R7Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) 7 a
def CB2_5_1I2R7Entropy : Ball := ⟨0, 0⟩
def CB2_5_1I2R7Mass : Ball := ⟨0, 0⟩
def CB2_5_1I2R7MassTerm : Ball := .exact 0
def CB2_5_1I2R7H : Ball := ⟨0, 0⟩
def CB2_5_1I2R8Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) 8 a
def CB2_5_1I2R8Entropy : Ball := ⟨0, 0⟩
def CB2_5_1I2R8Mass : Ball := ⟨0, 0⟩
def CB2_5_1I2R8MassTerm : Ball := .exact 0
def CB2_5_1I2R8H : Ball := ⟨0, 0⟩
def CB2_5_1I2R9Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) 9 a
def CB2_5_1I2R9Entropy : Ball := ⟨0, 0⟩
def CB2_5_1I2R9Mass : Ball := ⟨0, 0⟩
def CB2_5_1I2R9MassTerm : Ball := .exact 0
def CB2_5_1I2R9H : Ball := ⟨0, 0⟩
def CB2_5_1I2R10Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) 10 a
def CB2_5_1I2R10Entropy : Ball := ⟨0, 0⟩
def CB2_5_1I2R10Mass : Ball := ⟨0, 0⟩
def CB2_5_1I2R10MassTerm : Ball := .exact 0
def CB2_5_1I2R10H : Ball := ⟨0, 0⟩
def CB2_5_1I2R11Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) 11 a
def CB2_5_1I2R11Entropy : Ball := ⟨0, 0⟩
def CB2_5_1I2R11Mass : Ball := ⟨0, 0⟩
def CB2_5_1I2R11MassTerm : Ball := .exact 0
def CB2_5_1I2R11H : Ball := ⟨0, 0⟩
def CB2_5_1I2R12Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) 12 a
def CB2_5_1I2R12Entropy : Ball := ⟨0, 0⟩
def CB2_5_1I2R12Mass : Ball := ⟨0, 0⟩
def CB2_5_1I2R12MassTerm : Ball := .exact 0
def CB2_5_1I2R12H : Ball := ⟨0, 0⟩
def CB2_5_1I2R13Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) 13 a
def CB2_5_1I2R13Entropy : Ball := ⟨0, 0⟩
def CB2_5_1I2R13Mass : Ball := ⟨0, 0⟩
def CB2_5_1I2R13MassTerm : Ball := .exact 0
def CB2_5_1I2R13H : Ball := ⟨0, 0⟩
def CB2_5_1I2R14Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) 14 a
def CB2_5_1I2R14Entropy : Ball := ⟨0, 0⟩
def CB2_5_1I2R14Mass : Ball := ⟨0, 0⟩
def CB2_5_1I2R14MassTerm : Ball := .exact 0
def CB2_5_1I2R14H : Ball := ⟨0, 0⟩
def CB2_5_1I2R15Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) 15 a
def CB2_5_1I2R15Entropy : Ball := ⟨0, 0⟩
def CB2_5_1I2R15Mass : Ball := ⟨0, 0⟩
def CB2_5_1I2R15MassTerm : Ball := .exact 0
def CB2_5_1I2R15H : Ball := ⟨0, 0⟩
def CB2_5_1I2R16Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) 16 a
def CB2_5_1I2R16Entropy : Ball := ⟨0, 0⟩
def CB2_5_1I2R16Mass : Ball := ⟨0, 0⟩
def CB2_5_1I2R16MassTerm : Ball := .exact 0
def CB2_5_1I2R16H : Ball := ⟨0, 0⟩
def CB2_5_1I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CB2_5_1I2R0H
  | 1 => CB2_5_1I2R1H
  | 2 => CB2_5_1I2R2H
  | 3 => CB2_5_1I2R3H
  | 4 => CB2_5_1I2R4H
  | 5 => CB2_5_1I2R5H
  | 6 => CB2_5_1I2R6H
  | 7 => CB2_5_1I2R7H
  | 8 => CB2_5_1I2R8H
  | 9 => CB2_5_1I2R9H
  | 10 => CB2_5_1I2R10H
  | 11 => CB2_5_1I2R11H
  | 12 => CB2_5_1I2R12H
  | 13 => CB2_5_1I2R13H
  | 14 => CB2_5_1I2R14H
  | 15 => CB2_5_1I2R15H
  | 16 => CB2_5_1I2R16H
  | _ => (.exact 0)
def CB2_5_1I2S0_3_1Value (a : Fin 6) : ℝ := (littleLaw (shape 2 5 1) (shape 0 3 1) ((stageBPriority (shape 2 5 1)) 2) a : ℝ)
def CB2_5_1I2S0_3_1E_4Log : Ball := .exact 0
def CB2_5_1I2S0_3_1E_4 : Ball := ⟨0, 0⟩
def CB2_5_1I2S0_3_1Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB2_5_1I2S0_3_1Entropy : Ball := ⟨0, 0⟩
def CB2_5_1I2S0_3_1Mass : Ball := ⟨1, 0⟩
def CB2_5_1I2S0_3_1MassTermLog : Ball := .exact 0
def CB2_5_1I2S0_3_1MassTerm : Ball := ⟨0, 0⟩
def CB2_5_1I2S0_3_1H : Ball := ⟨0, 0⟩
def CB2_5_1I2S0_4_0Value (a : Fin 6) : ℝ := (littleLaw (shape 2 5 1) (shape 0 4 0) ((stageBPriority (shape 2 5 1)) 2) a : ℝ)
def CB2_5_1I2S0_4_0E_5Log : Ball := .exact 0
def CB2_5_1I2S0_4_0E_5 : Ball := ⟨0, 0⟩
def CB2_5_1I2S0_4_0Terms (a : Fin 6) : Ball :=
  match a.val with
  | 5 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB2_5_1I2S0_4_0Entropy : Ball := ⟨0, 0⟩
def CB2_5_1I2S0_4_0Mass : Ball := ⟨1, 0⟩
def CB2_5_1I2S0_4_0MassTermLog : Ball := .exact 0
def CB2_5_1I2S0_4_0MassTerm : Ball := ⟨0, 0⟩
def CB2_5_1I2S0_4_0H : Ball := ⟨0, 0⟩
def CB2_5_1I2S1_3_0Value (a : Fin 6) : ℝ := (littleLaw (shape 2 5 1) (shape 1 3 0) ((stageBPriority (shape 2 5 1)) 2) a : ℝ)
def CB2_5_1I2S1_3_0E_4Log : Ball := .exact 0
def CB2_5_1I2S1_3_0E_4 : Ball := ⟨0, 0⟩
def CB2_5_1I2S1_3_0Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB2_5_1I2S1_3_0Entropy : Ball := ⟨0, 0⟩
def CB2_5_1I2S1_3_0Mass : Ball := ⟨1, 0⟩
def CB2_5_1I2S1_3_0MassTermLog : Ball := .exact 0
def CB2_5_1I2S1_3_0MassTerm : Ball := ⟨0, 0⟩
def CB2_5_1I2S1_3_0H : Ball := ⟨0, 0⟩
def CB2_5_1I2S2_2_0Value (a : Fin 6) : ℝ := (littleLaw (shape 2 5 1) (shape 2 2 0) ((stageBPriority (shape 2 5 1)) 2) a : ℝ)
def CB2_5_1I2S2_2_0E_2LogWitness : LogWitness := ⟨-1, 444957, 250000⟩
def CB2_5_1I2S2_2_0E_2Log : Ball := ⟨(-583152250691689478453229215219 / 5000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def CB2_5_1I2S2_2_0E_2 : Ball := ⟨(1297388380055110376320567559581 / 12500000000000000000000000000000), (7537864783 / 20000000000000000000000000000000)⟩
def CB2_5_1I2S2_2_0E_3LogWitness : LogWitness := ⟨-4, 55043, 31250⟩
def CB2_5_1I2S2_2_0E_3Log : Ball := ⟨(-22064934004685379356673449299827 / 10000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
def CB2_5_1I2S2_2_0E_3 : Ball := ⟨(1518150203024871669911720837263 / 6250000000000000000000000000000), (11655808631 / 100000000000000000000000000000000)⟩
def CB2_5_1I2S2_2_0Terms (a : Fin 6) : Ball :=
  match a.val with
  | 2 => ⟨(1297388380055110376320567559581 / 12500000000000000000000000000000), (7537864783 / 20000000000000000000000000000000)⟩
  | 3 => ⟨(1518150203024871669911720837263 / 6250000000000000000000000000000), (11655808631 / 100000000000000000000000000000000)⟩
  | _ => (.exact 0)
def CB2_5_1I2S2_2_0Entropy : Ball := ⟨(4333688786104853716144009234107 / 12500000000000000000000000000000), (24672566273 / 50000000000000000000000000000000)⟩
def CB2_5_1I2S2_2_0Mass : Ball := ⟨1, 0⟩
def CB2_5_1I2S2_2_0MassTermLog : Ball := .exact 0
def CB2_5_1I2S2_2_0MassTerm : Ball := ⟨0, 0⟩
def CB2_5_1I2S2_2_0H : Ball := ⟨(4333688786104853716144009234107 / 12500000000000000000000000000000), (24672566273 / 50000000000000000000000000000000)⟩
def CB2_5_1I2Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 3, 1 => CB2_5_1I2S0_3_1H
  | 0, 4, 0 => CB2_5_1I2S0_4_0H
  | 1, 3, 0 => CB2_5_1I2S1_3_0H
  | 2, 2, 0 => CB2_5_1I2S2_2_0H
  | _, _, _ => (.exact 0)
def CB2_5_1I2Singleton : Ball := ⟨(770458991825735733780541157757 / 12500000000000000000000000000000), (8772757573 / 100000000000000000000000000000000)⟩
def CB2_5_1I2Group : Ball := ⟨(6912941347646796393825341225573 / 100000000000000000000000000000000), (51705574047 / 100000000000000000000000000000000)⟩

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
def CB2_5_1I2H : Ball := ⟨(40055444030287900426894750871547 / 50000000000000000000000000000000), (193423618701 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB3_1_4I0
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
def CB3_1_4I0Value (a : Fin 17) : ℝ := marginal (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) ((stageBPriority (shape 3 1 4)) 0) a
def CB3_1_4I0Entropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (21175823729 / 50000000000000000000000000000000)⟩
def CB3_1_4I0Mass : Ball := ⟨1, (27 / 50000000000000000000000000000000)⟩
def CB3_1_4I0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB3_1_4I0MassTermLog : Ball := ⟨0, (2646977967 / 12500000000000000000000000000000)⟩
def CB3_1_4I0MassTerm : Ball := ⟨0, (21175823737 / 100000000000000000000000000000000)⟩
def CB3_1_4I0H : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (12705494239 / 20000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB3_1_4I1
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
def CB3_1_4I1PairEntropy : Ball := ⟨(55272475349477404898442189151021 / 50000000000000000000000000000000), (17943683107 / 25000000000000000000000000000000)⟩
def CB3_1_4I1PairMass : Ball := ⟨1, (7 / 12500000000000000000000000000000)⟩
def CB3_1_4I1PairMassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB3_1_4I1PairMassTermLog : Ball := ⟨0, (10587911869 / 50000000000000000000000000000000)⟩
def CB3_1_4I1PairMassTerm : Ball := ⟨0, (21175823739 / 100000000000000000000000000000000)⟩
def CB3_1_4I1PairH : Ball := ⟨(55272475349477404898442189151021 / 50000000000000000000000000000000), (92950556167 / 100000000000000000000000000000000)⟩

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
def CB3_1_4I1R0Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 1 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 1) a : ℝ)) 0 a
def CB3_1_4I1R0Entropy : Ball := ⟨(5736218497226440293141624761203 / 100000000000000000000000000000000), (2248328117 / 100000000000000000000000000000000)⟩
def CB3_1_4I1R0Mass : Ball := ⟨(331794662118768313410096879501 / 25000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def CB3_1_4I1R0MassTermLogWitness : LogWitness := ⟨-7, 331794662118768313410096879501, 195312500000000000000000000000⟩
def CB3_1_4I1R0MassTermLog : Ball := ⟨(-432211481387027192883904562168077 / 100000000000000000000000000000000), (42351647479 / 25000000000000000000000000000000)⟩
def CB3_1_4I1R0MassTerm : Ball := ⟨(5736218497226440293141624761203 / 100000000000000000000000000000000), (2248328117 / 100000000000000000000000000000000)⟩
def CB3_1_4I1R0H : Ball := ⟨0, (2248328117 / 50000000000000000000000000000000)⟩
def CB3_1_4I1R1Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 1 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 1) a : ℝ)) 1 a
def CB3_1_4I1R1Entropy : Ball := ⟨(17523417779096033358476442978537 / 50000000000000000000000000000000), (30920612529 / 100000000000000000000000000000000)⟩
def CB3_1_4I1R1Mass : Ball := ⟨(12168205337881231686589903120499 / 25000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
def CB3_1_4I1R1MassTermLogWitness : LogWitness := ⟨-2, 12168205337881231686589903120499, 6250000000000000000000000000000⟩
def CB3_1_4I1R1MassTermLog : Ball := ⟨(-14400987896336132212354969653389 / 20000000000000000000000000000000), (15881867773 / 25000000000000000000000000000000)⟩
def CB3_1_4I1R1MassTerm : Ball := ⟨(17523417779096033358476442978537 / 50000000000000000000000000000000), (30920612529 / 100000000000000000000000000000000)⟩
def CB3_1_4I1R1H : Ball := ⟨0, (30920612529 / 50000000000000000000000000000000)⟩
def CB3_1_4I1R2Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 1 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 1) a : ℝ)) 2 a
def CB3_1_4I1R2Entropy : Ball := ⟨(24768128426125482302650282194909 / 50000000000000000000000000000000), (33639038097 / 100000000000000000000000000000000)⟩
def CB3_1_4I1R2Mass : Ball := ⟨(12168205337881231686589903120499 / 25000000000000000000000000000000), (11 / 50000000000000000000000000000000)⟩
def CB3_1_4I1R2MassTermLogWitness : LogWitness := ⟨-2, 12168205337881231686589903120499, 6250000000000000000000000000000⟩
def CB3_1_4I1R2MassTermLog : Ball := ⟨(-14400987896336132212354969653389 / 20000000000000000000000000000000), (31763735547 / 50000000000000000000000000000000)⟩
def CB3_1_4I1R2MassTerm : Ball := ⟨(17523417779096033358476442978537 / 50000000000000000000000000000000), (30920612531 / 100000000000000000000000000000000)⟩
def CB3_1_4I1R2H : Ball := ⟨(1811177661757362236043459804093 / 12500000000000000000000000000000), (16139912657 / 25000000000000000000000000000000)⟩
def CB3_1_4I1R3Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 1 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 1) a : ℝ)) 3 a
def CB3_1_4I1R3Entropy : Ball := ⟨(5652606947245305451174414549533 / 100000000000000000000000000000000), (2205813341 / 100000000000000000000000000000000)⟩
def CB3_1_4I1R3Mass : Ball := ⟨(8138014732824595179881072909 / 625000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
def CB3_1_4I1R3MassTermLogWitness : LogWitness := ⟨-7, 8138014732824595179881072909, 4882812500000000000000000000⟩
def CB3_1_4I1R3MassTermLog : Ball := ⟨(-17364821559137684800421235168797 / 4000000000000000000000000000000), (21175823731 / 12500000000000000000000000000000)⟩
def CB3_1_4I1R3MassTerm : Ball := ⟨(5652606947245305451174414549533 / 100000000000000000000000000000000), (2205813341 / 100000000000000000000000000000000)⟩
def CB3_1_4I1R3H : Ball := ⟨0, (2205813341 / 50000000000000000000000000000000)⟩
def CB3_1_4I1R4Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 1 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 1) a : ℝ)) 4 a
def CB3_1_4I1R4Entropy : Ball := ⟨0, 0⟩
def CB3_1_4I1R4Mass : Ball := ⟨0, 0⟩
def CB3_1_4I1R4MassTerm : Ball := .exact 0
def CB3_1_4I1R4H : Ball := ⟨0, 0⟩
def CB3_1_4I1R5Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 1 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 1) a : ℝ)) 5 a
def CB3_1_4I1R5Entropy : Ball := ⟨0, 0⟩
def CB3_1_4I1R5Mass : Ball := ⟨0, 0⟩
def CB3_1_4I1R5MassTerm : Ball := .exact 0
def CB3_1_4I1R5H : Ball := ⟨0, 0⟩
def CB3_1_4I1R6Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 1 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 1) a : ℝ)) 6 a
def CB3_1_4I1R6Entropy : Ball := ⟨0, 0⟩
def CB3_1_4I1R6Mass : Ball := ⟨0, 0⟩
def CB3_1_4I1R6MassTerm : Ball := .exact 0
def CB3_1_4I1R6H : Ball := ⟨0, 0⟩
def CB3_1_4I1R7Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 1 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 1) a : ℝ)) 7 a
def CB3_1_4I1R7Entropy : Ball := ⟨0, 0⟩
def CB3_1_4I1R7Mass : Ball := ⟨0, 0⟩
def CB3_1_4I1R7MassTerm : Ball := .exact 0
def CB3_1_4I1R7H : Ball := ⟨0, 0⟩
def CB3_1_4I1R8Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 1 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 1) a : ℝ)) 8 a
def CB3_1_4I1R8Entropy : Ball := ⟨0, 0⟩
def CB3_1_4I1R8Mass : Ball := ⟨0, 0⟩
def CB3_1_4I1R8MassTerm : Ball := .exact 0
def CB3_1_4I1R8H : Ball := ⟨0, 0⟩
def CB3_1_4I1R9Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 1 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 1) a : ℝ)) 9 a
def CB3_1_4I1R9Entropy : Ball := ⟨0, 0⟩
def CB3_1_4I1R9Mass : Ball := ⟨0, 0⟩
def CB3_1_4I1R9MassTerm : Ball := .exact 0
def CB3_1_4I1R9H : Ball := ⟨0, 0⟩
def CB3_1_4I1R10Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 1 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 1) a : ℝ)) 10 a
def CB3_1_4I1R10Entropy : Ball := ⟨0, 0⟩
def CB3_1_4I1R10Mass : Ball := ⟨0, 0⟩
def CB3_1_4I1R10MassTerm : Ball := .exact 0
def CB3_1_4I1R10H : Ball := ⟨0, 0⟩
def CB3_1_4I1R11Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 1 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 1) a : ℝ)) 11 a
def CB3_1_4I1R11Entropy : Ball := ⟨0, 0⟩
def CB3_1_4I1R11Mass : Ball := ⟨0, 0⟩
def CB3_1_4I1R11MassTerm : Ball := .exact 0
def CB3_1_4I1R11H : Ball := ⟨0, 0⟩
def CB3_1_4I1R12Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 1 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 1) a : ℝ)) 12 a
def CB3_1_4I1R12Entropy : Ball := ⟨0, 0⟩
def CB3_1_4I1R12Mass : Ball := ⟨0, 0⟩
def CB3_1_4I1R12MassTerm : Ball := .exact 0
def CB3_1_4I1R12H : Ball := ⟨0, 0⟩
def CB3_1_4I1R13Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 1 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 1) a : ℝ)) 13 a
def CB3_1_4I1R13Entropy : Ball := ⟨0, 0⟩
def CB3_1_4I1R13Mass : Ball := ⟨0, 0⟩
def CB3_1_4I1R13MassTerm : Ball := .exact 0
def CB3_1_4I1R13H : Ball := ⟨0, 0⟩
def CB3_1_4I1R14Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 1 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 1) a : ℝ)) 14 a
def CB3_1_4I1R14Entropy : Ball := ⟨0, 0⟩
def CB3_1_4I1R14Mass : Ball := ⟨0, 0⟩
def CB3_1_4I1R14MassTerm : Ball := .exact 0
def CB3_1_4I1R14H : Ball := ⟨0, 0⟩
def CB3_1_4I1R15Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 1 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 1) a : ℝ)) 15 a
def CB3_1_4I1R15Entropy : Ball := ⟨0, 0⟩
def CB3_1_4I1R15Mass : Ball := ⟨0, 0⟩
def CB3_1_4I1R15MassTerm : Ball := .exact 0
def CB3_1_4I1R15H : Ball := ⟨0, 0⟩
def CB3_1_4I1R16Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 1 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 1) a : ℝ)) 16 a
def CB3_1_4I1R16Entropy : Ball := ⟨0, 0⟩
def CB3_1_4I1R16Mass : Ball := ⟨0, 0⟩
def CB3_1_4I1R16MassTerm : Ball := .exact 0
def CB3_1_4I1R16H : Ball := ⟨0, 0⟩
def CB3_1_4I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CB3_1_4I1R0H
  | 1 => CB3_1_4I1R1H
  | 2 => CB3_1_4I1R2H
  | 3 => CB3_1_4I1R3H
  | 4 => CB3_1_4I1R4H
  | 5 => CB3_1_4I1R5H
  | 6 => CB3_1_4I1R6H
  | 7 => CB3_1_4I1R7H
  | 8 => CB3_1_4I1R8H
  | 9 => CB3_1_4I1R9H
  | 10 => CB3_1_4I1R10H
  | 11 => CB3_1_4I1R11H
  | 12 => CB3_1_4I1R12H
  | 13 => CB3_1_4I1R13H
  | 14 => CB3_1_4I1R14H
  | 15 => CB3_1_4I1R15H
  | 16 => CB3_1_4I1R16H
  | _ => (.exact 0)
def CB3_1_4I1S3_1_0Value (a : Fin 6) : ℝ := (littleLaw (shape 3 1 4) (shape 3 1 0) ((stageBPriority (shape 3 1 4)) 1) a : ℝ)
def CB3_1_4I1S3_1_0E_4Log : Ball := .exact 0
def CB3_1_4I1S3_1_0E_4 : Ball := ⟨0, 0⟩
def CB3_1_4I1S3_1_0Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB3_1_4I1S3_1_0Entropy : Ball := ⟨0, 0⟩
def CB3_1_4I1S3_1_0Mass : Ball := ⟨1, 0⟩
def CB3_1_4I1S3_1_0MassTermLog : Ball := .exact 0
def CB3_1_4I1S3_1_0MassTerm : Ball := ⟨0, 0⟩
def CB3_1_4I1S3_1_0H : Ball := ⟨0, 0⟩
def CB3_1_4I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 3, 1, 0 => CB3_1_4I1S3_1_0H
  | _, _, _ => (.exact 0)
def CB3_1_4I1Singleton : Ball := ⟨0, 0⟩
def CB3_1_4I1Group : Ball := ⟨(1811177661757362236043459804093 / 12500000000000000000000000000000), (67654579301 / 50000000000000000000000000000000)⟩

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
def CB3_1_4I1H : Ball := ⟨(40783054055418507010094510718277 / 50000000000000000000000000000000), (363568873371 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB3_1_4I2
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
def CB3_1_4I2PairEntropy : Ball := ⟨(86522056707486857696995452485631 / 100000000000000000000000000000000), (59147630093 / 100000000000000000000000000000000)⟩
def CB3_1_4I2PairMass : Ball := ⟨1, (57 / 100000000000000000000000000000000)⟩
def CB3_1_4I2PairMassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB3_1_4I2PairMassTermLog : Ball := ⟨0, (21175823739 / 100000000000000000000000000000000)⟩
def CB3_1_4I2PairMassTerm : Ball := ⟨0, (1058791187 / 5000000000000000000000000000000)⟩
def CB3_1_4I2PairH : Ball := ⟨(86522056707486857696995452485631 / 100000000000000000000000000000000), (80323453833 / 100000000000000000000000000000000)⟩

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
def CB3_1_4I2R0Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) 0 a
def CB3_1_4I2R0Entropy : Ball := ⟨(2080534087616583180597915017 / 1000000000000000000000000000000), (69086513 / 100000000000000000000000000000000)⟩
def CB3_1_4I2R0Mass : Ball := ⟨(6274072805784506214853963141 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def CB3_1_4I2R0MassTermLogWitness : LogWitness := ⟨-12, 6274072805784506214853963141, 6103515625000000000000000000⟩
def CB3_1_4I2R0MassTermLog : Ball := ⟨(-414510269489221060005265391870793 / 50000000000000000000000000000000), (275285711863 / 100000000000000000000000000000000)⟩
def CB3_1_4I2R0MassTerm : Ball := ⟨(2080534087616583180597915017 / 1000000000000000000000000000000), (69086513 / 100000000000000000000000000000000)⟩
def CB3_1_4I2R0H : Ball := ⟨0, (69086513 / 50000000000000000000000000000000)⟩
def CB3_1_4I2R1Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) 1 a
def CB3_1_4I2R1Entropy : Ball := ⟨(4371852957778900787421083283603 / 25000000000000000000000000000000), (3356321177 / 50000000000000000000000000000000)⟩
def CB3_1_4I2R1Mass : Ball := ⟨(3169955708291305924669541513661 / 50000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
def CB3_1_4I2R1MassTermLogWitness : LogWitness := ⟨-4, 3169955708291305924669541513661, 3125000000000000000000000000000⟩
def CB3_1_4I2R1MassTermLog : Ball := ⟨(-275830538978442120010530936506341 / 100000000000000000000000000000000), (26469779643 / 25000000000000000000000000000000)⟩
def CB3_1_4I2R1MassTerm : Ball := ⟨(4371852957778900787421083283603 / 25000000000000000000000000000000), (3356321177 / 50000000000000000000000000000000)⟩
def CB3_1_4I2R1H : Ball := ⟨0, (3356321177 / 25000000000000000000000000000000)⟩
def CB3_1_4I2R2Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) 2 a
def CB3_1_4I2R2Entropy : Ball := ⟨(4631793068546561116750448563263 / 12500000000000000000000000000000), (27071085867 / 100000000000000000000000000000000)⟩
def CB3_1_4I2R2Mass : Ball := ⟨(21166454967471157448510264727337 / 50000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
def CB3_1_4I2R2MassTermLogWitness : LogWitness := ⟨-2, 21166454967471157448510264727337, 12500000000000000000000000000000⟩
def CB3_1_4I2R2MassTermLog : Ball := ⟨(-85960538978442120010530974697353 / 100000000000000000000000000000000), (63527471079 / 100000000000000000000000000000000)⟩
def CB3_1_4I2R2MassTerm : Ball := ⟨(71073432705732197860803257381 / 195312500000000000000000000000), (3361628391 / 12500000000000000000000000000000)⟩
def CB3_1_4I2R2H : Ball := ⟨(83093375379700453659040090879 / 12500000000000000000000000000000), (10792822599 / 20000000000000000000000000000000)⟩
def CB3_1_4I2R3Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) 3 a
def CB3_1_4I2R3Entropy : Ball := ⟨0, 0⟩
def CB3_1_4I2R3Mass : Ball := ⟨0, 0⟩
def CB3_1_4I2R3MassTerm : Ball := .exact 0
def CB3_1_4I2R3H : Ball := ⟨0, 0⟩
def CB3_1_4I2R4Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) 4 a
def CB3_1_4I2R4Entropy : Ball := ⟨0, 0⟩
def CB3_1_4I2R4Mass : Ball := ⟨0, 0⟩
def CB3_1_4I2R4MassTerm : Ball := .exact 0
def CB3_1_4I2R4H : Ball := ⟨0, 0⟩
def CB3_1_4I2R5Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) 5 a
def CB3_1_4I2R5Entropy : Ball := ⟨0, 0⟩
def CB3_1_4I2R5Mass : Ball := ⟨0, 0⟩
def CB3_1_4I2R5MassTerm : Ball := .exact 0
def CB3_1_4I2R5H : Ball := ⟨0, 0⟩
def CB3_1_4I2R6Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) 6 a
def CB3_1_4I2R6Entropy : Ball := ⟨0, 0⟩
def CB3_1_4I2R6Mass : Ball := ⟨0, 0⟩
def CB3_1_4I2R6MassTerm : Ball := .exact 0
def CB3_1_4I2R6H : Ball := ⟨0, 0⟩
def CB3_1_4I2R7Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) 7 a
def CB3_1_4I2R7Entropy : Ball := ⟨0, 0⟩
def CB3_1_4I2R7Mass : Ball := ⟨0, 0⟩
def CB3_1_4I2R7MassTerm : Ball := .exact 0
def CB3_1_4I2R7H : Ball := ⟨0, 0⟩
def CB3_1_4I2R8Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) 8 a
def CB3_1_4I2R8Entropy : Ball := ⟨0, 0⟩
def CB3_1_4I2R8Mass : Ball := ⟨0, 0⟩
def CB3_1_4I2R8MassTerm : Ball := .exact 0
def CB3_1_4I2R8H : Ball := ⟨0, 0⟩
def CB3_1_4I2R9Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) 9 a
def CB3_1_4I2R9Entropy : Ball := ⟨0, 0⟩
def CB3_1_4I2R9Mass : Ball := ⟨0, 0⟩
def CB3_1_4I2R9MassTerm : Ball := .exact 0
def CB3_1_4I2R9H : Ball := ⟨0, 0⟩
def CB3_1_4I2R10Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) 10 a
def CB3_1_4I2R10Entropy : Ball := ⟨0, 0⟩
def CB3_1_4I2R10Mass : Ball := ⟨0, 0⟩
def CB3_1_4I2R10MassTerm : Ball := .exact 0
def CB3_1_4I2R10H : Ball := ⟨0, 0⟩
def CB3_1_4I2R11Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) 11 a
def CB3_1_4I2R11Entropy : Ball := ⟨0, 0⟩
def CB3_1_4I2R11Mass : Ball := ⟨0, 0⟩
def CB3_1_4I2R11MassTerm : Ball := .exact 0
def CB3_1_4I2R11H : Ball := ⟨0, 0⟩
def CB3_1_4I2R12Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) 12 a
def CB3_1_4I2R12Entropy : Ball := ⟨0, 0⟩
def CB3_1_4I2R12Mass : Ball := ⟨0, 0⟩
def CB3_1_4I2R12MassTerm : Ball := .exact 0
def CB3_1_4I2R12H : Ball := ⟨0, 0⟩
def CB3_1_4I2R13Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) 13 a
def CB3_1_4I2R13Entropy : Ball := ⟨0, 0⟩
def CB3_1_4I2R13Mass : Ball := ⟨0, 0⟩
def CB3_1_4I2R13MassTerm : Ball := .exact 0
def CB3_1_4I2R13H : Ball := ⟨0, 0⟩
def CB3_1_4I2R14Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) 14 a
def CB3_1_4I2R14Entropy : Ball := ⟨0, 0⟩
def CB3_1_4I2R14Mass : Ball := ⟨0, 0⟩
def CB3_1_4I2R14MassTerm : Ball := .exact 0
def CB3_1_4I2R14H : Ball := ⟨0, 0⟩
def CB3_1_4I2R15Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) 15 a
def CB3_1_4I2R15Entropy : Ball := ⟨0, 0⟩
def CB3_1_4I2R15Mass : Ball := ⟨0, 0⟩
def CB3_1_4I2R15MassTerm : Ball := .exact 0
def CB3_1_4I2R15H : Ball := ⟨0, 0⟩
def CB3_1_4I2R16Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) 16 a
def CB3_1_4I2R16Entropy : Ball := ⟨0, 0⟩
def CB3_1_4I2R16Mass : Ball := ⟨0, 0⟩
def CB3_1_4I2R16MassTerm : Ball := .exact 0
def CB3_1_4I2R16H : Ball := ⟨0, 0⟩
def CB3_1_4I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CB3_1_4I2R0H
  | 1 => CB3_1_4I2R1H
  | 2 => CB3_1_4I2R2H
  | 3 => CB3_1_4I2R3H
  | 4 => CB3_1_4I2R4H
  | 5 => CB3_1_4I2R5H
  | 6 => CB3_1_4I2R6H
  | 7 => CB3_1_4I2R7H
  | 8 => CB3_1_4I2R8H
  | 9 => CB3_1_4I2R9H
  | 10 => CB3_1_4I2R10H
  | 11 => CB3_1_4I2R11H
  | 12 => CB3_1_4I2R12H
  | 13 => CB3_1_4I2R13H
  | 14 => CB3_1_4I2R14H
  | 15 => CB3_1_4I2R15H
  | 16 => CB3_1_4I2R16H
  | _ => (.exact 0)
def CB3_1_4I2S0_0_4Value (a : Fin 6) : ℝ := (littleLaw (shape 3 1 4) (shape 0 0 4) ((stageBPriority (shape 3 1 4)) 2) a : ℝ)
def CB3_1_4I2S0_0_4E_5Log : Ball := .exact 0
def CB3_1_4I2S0_0_4E_5 : Ball := ⟨0, 0⟩
def CB3_1_4I2S0_0_4Terms (a : Fin 6) : Ball :=
  match a.val with
  | 5 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB3_1_4I2S0_0_4Entropy : Ball := ⟨0, 0⟩
def CB3_1_4I2S0_0_4Mass : Ball := ⟨1, 0⟩
def CB3_1_4I2S0_0_4MassTermLog : Ball := .exact 0
def CB3_1_4I2S0_0_4MassTerm : Ball := ⟨0, 0⟩
def CB3_1_4I2S0_0_4H : Ball := ⟨0, 0⟩
def CB3_1_4I2S0_1_3Value (a : Fin 6) : ℝ := (littleLaw (shape 3 1 4) (shape 0 1 3) ((stageBPriority (shape 3 1 4)) 2) a : ℝ)
def CB3_1_4I2S0_1_3E_4Log : Ball := .exact 0
def CB3_1_4I2S0_1_3E_4 : Ball := ⟨0, 0⟩
def CB3_1_4I2S0_1_3Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB3_1_4I2S0_1_3Entropy : Ball := ⟨0, 0⟩
def CB3_1_4I2S0_1_3Mass : Ball := ⟨1, 0⟩
def CB3_1_4I2S0_1_3MassTermLog : Ball := .exact 0
def CB3_1_4I2S0_1_3MassTerm : Ball := ⟨0, 0⟩
def CB3_1_4I2S0_1_3H : Ball := ⟨0, 0⟩
def CB3_1_4I2S1_0_3Value (a : Fin 6) : ℝ := (littleLaw (shape 3 1 4) (shape 1 0 3) ((stageBPriority (shape 3 1 4)) 2) a : ℝ)
def CB3_1_4I2S1_0_3E_4Log : Ball := .exact 0
def CB3_1_4I2S1_0_3E_4 : Ball := ⟨0, 0⟩
def CB3_1_4I2S1_0_3Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB3_1_4I2S1_0_3Entropy : Ball := ⟨0, 0⟩
def CB3_1_4I2S1_0_3Mass : Ball := ⟨1, 0⟩
def CB3_1_4I2S1_0_3MassTermLog : Ball := .exact 0
def CB3_1_4I2S1_0_3MassTerm : Ball := ⟨0, 0⟩
def CB3_1_4I2S1_0_3H : Ball := ⟨0, 0⟩
def CB3_1_4I2S2_0_2Value (a : Fin 6) : ℝ := (littleLaw (shape 3 1 4) (shape 2 0 2) ((stageBPriority (shape 3 1 4)) 2) a : ℝ)
def CB3_1_4I2S2_0_2E_2LogWitness : LogWitness := ⟨-1, 56577, 31250⟩
def CB3_1_4I2S2_0_2E_2Log : Ball := ⟨(-9956401454401802915036069658881 / 100000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def CB3_1_4I2S2_0_2E_2 : Ball := ⟨(1126606650171381607047991426181 / 12500000000000000000000000000000), (38338066449 / 100000000000000000000000000000000)⟩
def CB3_1_4I2S2_0_2E_3LogWitness : LogWitness := ⟨-4, 23692, 15625⟩
def CB3_1_4I2S2_0_2E_3Log : Ball := ⟨(-235632347944752769756850307028051 / 100000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
def CB3_1_4I2S2_0_2E_3 : Ball := ⟨(11165203175014165242158594948217 / 50000000000000000000000000000000), (2006790459 / 20000000000000000000000000000000)⟩
def CB3_1_4I2S2_0_2Terms (a : Fin 6) : Ball :=
  match a.val with
  | 2 => ⟨(1126606650171381607047991426181 / 12500000000000000000000000000000), (38338066449 / 100000000000000000000000000000000)⟩
  | 3 => ⟨(11165203175014165242158594948217 / 50000000000000000000000000000000), (2006790459 / 20000000000000000000000000000000)⟩
  | _ => (.exact 0)
def CB3_1_4I2S2_0_2Entropy : Ball := ⟨(15671629775699691670350560652941 / 50000000000000000000000000000000), (6046502343 / 12500000000000000000000000000000)⟩
def CB3_1_4I2S2_0_2Mass : Ball := ⟨1, 0⟩
def CB3_1_4I2S2_0_2MassTermLog : Ball := .exact 0
def CB3_1_4I2S2_0_2MassTerm : Ball := ⟨0, 0⟩
def CB3_1_4I2S2_0_2H : Ball := ⟨(15671629775699691670350560652941 / 50000000000000000000000000000000), (6046502343 / 12500000000000000000000000000000)⟩
def CB3_1_4I2S3_0_1Value (a : Fin 6) : ℝ := (littleLaw (shape 3 1 4) (shape 3 0 1) ((stageBPriority (shape 3 1 4)) 2) a : ℝ)
def CB3_1_4I2S3_0_1E_1Log : Ball := .exact 0
def CB3_1_4I2S3_0_1E_1 : Ball := ⟨0, 0⟩
def CB3_1_4I2S3_0_1Terms (a : Fin 6) : Ball :=
  match a.val with
  | 1 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB3_1_4I2S3_0_1Entropy : Ball := ⟨0, 0⟩
def CB3_1_4I2S3_0_1Mass : Ball := ⟨1, 0⟩
def CB3_1_4I2S3_0_1MassTermLog : Ball := .exact 0
def CB3_1_4I2S3_0_1MassTerm : Ball := ⟨0, 0⟩
def CB3_1_4I2S3_0_1H : Ball := ⟨0, 0⟩
def CB3_1_4I2Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => CB3_1_4I2S0_0_4H
  | 0, 1, 3 => CB3_1_4I2S0_1_3H
  | 1, 0, 3 => CB3_1_4I2S1_0_3H
  | 2, 0, 2 => CB3_1_4I2S2_0_2H
  | 3, 0, 1 => CB3_1_4I2S3_0_1H
  | _, _, _ => (.exact 0)
def CB3_1_4I2Singleton : Ball := ⟨(3317128459142276397553763101999 / 25000000000000000000000000000000), (20477283133 / 100000000000000000000000000000000)⟩
def CB3_1_4I2Group : Ball := ⟨(3483315209901677304871843283757 / 25000000000000000000000000000000), (44002426931 / 50000000000000000000000000000000)⟩

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
def CB3_1_4I2H : Ball := ⟨(2346221401130937570320828248623 / 4000000000000000000000000000000), (256333161557 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB3_2_3I0
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
def CB3_2_3I0Value (a : Fin 17) : ℝ := marginal (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) ((stageBPriority (shape 3 2 3)) 0) a
def CB3_2_3I0Entropy : Ball := ⟨(40764060967000799747699145574527 / 50000000000000000000000000000000), (33163361031 / 50000000000000000000000000000000)⟩
def CB3_2_3I0Mass : Ball := ⟨1, (29 / 25000000000000000000000000000000)⟩
def CB3_2_3I0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB3_2_3I0MassTermLog : Ball := ⟨0, (10587911899 / 50000000000000000000000000000000)⟩
def CB3_2_3I0MassTerm : Ball := ⟨0, (21175823799 / 100000000000000000000000000000000)⟩
def CB3_2_3I0H : Ball := ⟨(40764060967000799747699145574527 / 50000000000000000000000000000000), (87502545861 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB3_2_3I1
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
def CB3_2_3I1PairEntropy : Ball := ⟨(98520099470480798521291707416279 / 100000000000000000000000000000000), (14870751089 / 25000000000000000000000000000000)⟩
def CB3_2_3I1PairMass : Ball := ⟨1, (3 / 2500000000000000000000000000000)⟩
def CB3_2_3I1PairMassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB3_2_3I1PairMassTermLog : Ball := ⟨0, (10587911901 / 50000000000000000000000000000000)⟩
def CB3_2_3I1PairMassTerm : Ball := ⟨0, (21175823803 / 100000000000000000000000000000000)⟩
def CB3_2_3I1PairH : Ball := ⟨(98520099470480798521291707416279 / 100000000000000000000000000000000), (80658828159 / 100000000000000000000000000000000)⟩

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
def CB3_2_3I1R0Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) 0 a
def CB3_2_3I1R0Entropy : Ball := ⟨(31209212985956947397911481005053 / 100000000000000000000000000000000), (3915163519 / 25000000000000000000000000000000)⟩
def CB3_2_3I1R0Mass : Ball := ⟨(4622209212727355593997713111989 / 25000000000000000000000000000000), (39 / 100000000000000000000000000000000)⟩
def CB3_2_3I1R0MassTermLogWitness : LogWitness := ⟨-3, 4622209212727355593997713111989, 3125000000000000000000000000000⟩
def CB3_2_3I1R0MassTermLog : Ball := ⟨(-84400152474767063710553601532469 / 50000000000000000000000000000000), (42351647471 / 50000000000000000000000000000000)⟩
def CB3_2_3I1R0MassTerm : Ball := ⟨(31209212985956947397911481005053 / 100000000000000000000000000000000), (3915163519 / 25000000000000000000000000000000)⟩
def CB3_2_3I1R0H : Ball := ⟨0, (3915163519 / 12500000000000000000000000000000)⟩
def CB3_2_3I1R1Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) 1 a
def CB3_2_3I1R1Entropy : Ball := ⟨(14591271509207952834805282866537 / 50000000000000000000000000000000), (13311458879 / 50000000000000000000000000000000)⟩
def CB3_2_3I1R1Mass : Ball := ⟨(62861587115248395273289176036939 / 100000000000000000000000000000000), (37 / 100000000000000000000000000000000)⟩
def CB3_2_3I1R1MassTermLogWitness : LogWitness := ⟨-1, 62861587115248395273289176036939, 50000000000000000000000000000000⟩
def CB3_2_3I1R1MassTermLog : Ball := ⟨(-46423490652429086244419251190089 / 100000000000000000000000000000000), (661744491 / 1562500000000000000000000000000)⟩
def CB3_2_3I1R1MassTerm : Ball := ⟨(14591271509207952834805282866537 / 50000000000000000000000000000000), (13311458879 / 50000000000000000000000000000000)⟩
def CB3_2_3I1R1H : Ball := ⟨0, (13311458879 / 25000000000000000000000000000000)⟩
def CB3_2_3I1R2Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) 2 a
def CB3_2_3I1R2Entropy : Ball := ⟨(267730593642770057803656087457 / 800000000000000000000000000000), (3869102293 / 25000000000000000000000000000000)⟩
def CB3_2_3I1R2Mass : Ball := ⟨(17333920646982871320201468360311 / 100000000000000000000000000000000), (7 / 20000000000000000000000000000000)⟩
def CB3_2_3I1R2MassTermLogWitness : LogWitness := ⟨-3, 17333920646982871320201468360311, 12500000000000000000000000000000⟩
def CB3_2_3I1R2MassTermLog : Ball := ⟨(-175250487316902480110780974093599 / 100000000000000000000000000000000), (84703294933 / 100000000000000000000000000000000)⟩
def CB3_2_3I1R2MassTerm : Ball := ⟨(15188890202481328612979926606431 / 50000000000000000000000000000000), (14682401991 / 100000000000000000000000000000000)⟩
def CB3_2_3I1R2H : Ball := ⟨(3088543800383599999497157719263 / 100000000000000000000000000000000), (30158811163 / 100000000000000000000000000000000)⟩
def CB3_2_3I1R3Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) 3 a
def CB3_2_3I1R3Entropy : Ball := ⟨0, 0⟩
def CB3_2_3I1R3Mass : Ball := ⟨0, 0⟩
def CB3_2_3I1R3MassTerm : Ball := .exact 0
def CB3_2_3I1R3H : Ball := ⟨0, 0⟩
def CB3_2_3I1R4Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) 4 a
def CB3_2_3I1R4Entropy : Ball := ⟨0, 0⟩
def CB3_2_3I1R4Mass : Ball := ⟨0, 0⟩
def CB3_2_3I1R4MassTerm : Ball := .exact 0
def CB3_2_3I1R4H : Ball := ⟨0, 0⟩
def CB3_2_3I1R5Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) 5 a
def CB3_2_3I1R5Entropy : Ball := ⟨0, 0⟩
def CB3_2_3I1R5Mass : Ball := ⟨0, 0⟩
def CB3_2_3I1R5MassTerm : Ball := .exact 0
def CB3_2_3I1R5H : Ball := ⟨0, 0⟩
def CB3_2_3I1R6Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) 6 a
def CB3_2_3I1R6Entropy : Ball := ⟨0, 0⟩
def CB3_2_3I1R6Mass : Ball := ⟨0, 0⟩
def CB3_2_3I1R6MassTerm : Ball := .exact 0
def CB3_2_3I1R6H : Ball := ⟨0, 0⟩
def CB3_2_3I1R7Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) 7 a
def CB3_2_3I1R7Entropy : Ball := ⟨0, 0⟩
def CB3_2_3I1R7Mass : Ball := ⟨0, 0⟩
def CB3_2_3I1R7MassTerm : Ball := .exact 0
def CB3_2_3I1R7H : Ball := ⟨0, 0⟩
def CB3_2_3I1R8Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) 8 a
def CB3_2_3I1R8Entropy : Ball := ⟨0, 0⟩
def CB3_2_3I1R8Mass : Ball := ⟨0, 0⟩
def CB3_2_3I1R8MassTerm : Ball := .exact 0
def CB3_2_3I1R8H : Ball := ⟨0, 0⟩
def CB3_2_3I1R9Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) 9 a
def CB3_2_3I1R9Entropy : Ball := ⟨0, 0⟩
def CB3_2_3I1R9Mass : Ball := ⟨0, 0⟩
def CB3_2_3I1R9MassTerm : Ball := .exact 0
def CB3_2_3I1R9H : Ball := ⟨0, 0⟩
def CB3_2_3I1R10Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) 10 a
def CB3_2_3I1R10Entropy : Ball := ⟨0, 0⟩
def CB3_2_3I1R10Mass : Ball := ⟨0, 0⟩
def CB3_2_3I1R10MassTerm : Ball := .exact 0
def CB3_2_3I1R10H : Ball := ⟨0, 0⟩
def CB3_2_3I1R11Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) 11 a
def CB3_2_3I1R11Entropy : Ball := ⟨0, 0⟩
def CB3_2_3I1R11Mass : Ball := ⟨0, 0⟩
def CB3_2_3I1R11MassTerm : Ball := .exact 0
def CB3_2_3I1R11H : Ball := ⟨0, 0⟩
def CB3_2_3I1R12Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) 12 a
def CB3_2_3I1R12Entropy : Ball := ⟨0, 0⟩
def CB3_2_3I1R12Mass : Ball := ⟨0, 0⟩
def CB3_2_3I1R12MassTerm : Ball := .exact 0
def CB3_2_3I1R12H : Ball := ⟨0, 0⟩
def CB3_2_3I1R13Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) 13 a
def CB3_2_3I1R13Entropy : Ball := ⟨0, 0⟩
def CB3_2_3I1R13Mass : Ball := ⟨0, 0⟩
def CB3_2_3I1R13MassTerm : Ball := .exact 0
def CB3_2_3I1R13H : Ball := ⟨0, 0⟩
def CB3_2_3I1R14Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) 14 a
def CB3_2_3I1R14Entropy : Ball := ⟨0, 0⟩
def CB3_2_3I1R14Mass : Ball := ⟨0, 0⟩
def CB3_2_3I1R14MassTerm : Ball := .exact 0
def CB3_2_3I1R14H : Ball := ⟨0, 0⟩
def CB3_2_3I1R15Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) 15 a
def CB3_2_3I1R15Entropy : Ball := ⟨0, 0⟩
def CB3_2_3I1R15Mass : Ball := ⟨0, 0⟩
def CB3_2_3I1R15MassTerm : Ball := .exact 0
def CB3_2_3I1R15H : Ball := ⟨0, 0⟩
def CB3_2_3I1R16Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) 16 a
def CB3_2_3I1R16Entropy : Ball := ⟨0, 0⟩
def CB3_2_3I1R16Mass : Ball := ⟨0, 0⟩
def CB3_2_3I1R16MassTerm : Ball := .exact 0
def CB3_2_3I1R16H : Ball := ⟨0, 0⟩
def CB3_2_3I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CB3_2_3I1R0H
  | 1 => CB3_2_3I1R1H
  | 2 => CB3_2_3I1R2H
  | 3 => CB3_2_3I1R3H
  | 4 => CB3_2_3I1R4H
  | 5 => CB3_2_3I1R5H
  | 6 => CB3_2_3I1R6H
  | 7 => CB3_2_3I1R7H
  | 8 => CB3_2_3I1R8H
  | 9 => CB3_2_3I1R9H
  | 10 => CB3_2_3I1R10H
  | 11 => CB3_2_3I1R11H
  | 12 => CB3_2_3I1R12H
  | 13 => CB3_2_3I1R13H
  | 14 => CB3_2_3I1R14H
  | 15 => CB3_2_3I1R15H
  | 16 => CB3_2_3I1R16H
  | _ => (.exact 0)
def CB3_2_3I1S2_2_0Value (a : Fin 6) : ℝ := (littleLaw (shape 3 2 3) (shape 2 2 0) ((stageBPriority (shape 3 2 3)) 1) a : ℝ)
def CB3_2_3I1S2_2_0E_2LogWitness : LogWitness := ⟨-1, 224407, 125000⟩
def CB3_2_3I1S2_2_0E_2Log : Ball := ⟨(-5399977520216846740471713413351 / 50000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
def CB3_2_3I1S2_2_0E_2 : Ball := ⟨(9694342043034415411912286335599 / 100000000000000000000000000000000), (19008012261 / 50000000000000000000000000000000)⟩
def CB3_2_3I1S2_2_0E_3LogWitness : LogWitness := ⟨-4, 25593, 15625⟩
def CB3_2_3I1S2_2_0E_3Log : Ball := ⟨(-113957102063378952030784463086693 / 50000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
def CB3_2_3I1S2_2_0E_3 : Ball := ⟨(11666016452432230077295467055111 / 50000000000000000000000000000000), (10839057111 / 100000000000000000000000000000000)⟩
def CB3_2_3I1S2_2_0Terms (a : Fin 6) : Ball :=
  match a.val with
  | 2 => ⟨(9694342043034415411912286335599 / 100000000000000000000000000000000), (19008012261 / 50000000000000000000000000000000)⟩
  | 3 => ⟨(11666016452432230077295467055111 / 50000000000000000000000000000000), (10839057111 / 100000000000000000000000000000000)⟩
  | _ => (.exact 0)
def CB3_2_3I1S2_2_0Entropy : Ball := ⟨(33026374947898875566503220445821 / 100000000000000000000000000000000), (48855081633 / 100000000000000000000000000000000)⟩
def CB3_2_3I1S2_2_0Mass : Ball := ⟨1, 0⟩
def CB3_2_3I1S2_2_0MassTermLog : Ball := .exact 0
def CB3_2_3I1S2_2_0MassTerm : Ball := ⟨0, 0⟩
def CB3_2_3I1S2_2_0H : Ball := ⟨(33026374947898875566503220445821 / 100000000000000000000000000000000), (48855081633 / 100000000000000000000000000000000)⟩
def CB3_2_3I1S3_1_0Value (a : Fin 6) : ℝ := (littleLaw (shape 3 2 3) (shape 3 1 0) ((stageBPriority (shape 3 2 3)) 1) a : ℝ)
def CB3_2_3I1S3_1_0E_1Log : Ball := .exact 0
def CB3_2_3I1S3_1_0E_1 : Ball := ⟨0, 0⟩
def CB3_2_3I1S3_1_0Terms (a : Fin 6) : Ball :=
  match a.val with
  | 1 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB3_2_3I1S3_1_0Entropy : Ball := ⟨0, 0⟩
def CB3_2_3I1S3_1_0Mass : Ball := ⟨1, 0⟩
def CB3_2_3I1S3_1_0MassTermLog : Ball := .exact 0
def CB3_2_3I1S3_1_0MassTerm : Ball := ⟨0, 0⟩
def CB3_2_3I1S3_1_0H : Ball := ⟨0, 0⟩
def CB3_2_3I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 2, 2, 0 => CB3_2_3I1S2_2_0H
  | 3, 1, 0 => CB3_2_3I1S3_1_0H
  | _, _, _ => (.exact 0)
def CB3_2_3I1Singleton : Ball := ⟨(76285391168564629548214282781 / 20000000000000000000000000000000), (564235257 / 100000000000000000000000000000000)⟩
def CB3_2_3I1Group : Ball := ⟨(216873172264151446702389320823 / 6250000000000000000000000000000), (14411273761 / 12500000000000000000000000000000)⟩

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
def CB3_2_3I1H : Ball := ⟨(91580157958027952226815249149943 / 100000000000000000000000000000000), (62247841667 / 20000000000000000000000000000000)⟩

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
def CB3_2_3I2PairEntropy : Ball := ⟨(49239484903323286625046781782817 / 50000000000000000000000000000000), (34892712469 / 50000000000000000000000000000000)⟩
def CB3_2_3I2PairMass : Ball := ⟨1, (3 / 2500000000000000000000000000000)⟩
def CB3_2_3I2PairMassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB3_2_3I2PairMassTermLog : Ball := ⟨0, (10587911901 / 50000000000000000000000000000000)⟩
def CB3_2_3I2PairMassTerm : Ball := ⟨0, (21175823803 / 100000000000000000000000000000000)⟩
def CB3_2_3I2PairH : Ball := ⟨(49239484903323286625046781782817 / 50000000000000000000000000000000), (90961248741 / 100000000000000000000000000000000)⟩

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
def CB3_2_3I2R0Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 2 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 2) a : ℝ)) 0 a
def CB3_2_3I2R0Entropy : Ball := ⟨(45583093825531771912031644789 / 800000000000000000000000000000), (2228806953 / 100000000000000000000000000000000)⟩
def CB3_2_3I2R0Mass : Ball := ⟨(657827693429655515259251577397 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def CB3_2_3I2R0MassTermLogWitness : LogWitness := ⟨-7, 657827693429655515259251577397, 390625000000000000000000000000⟩
def CB3_2_3I2R0MassTermLog : Ball := ⟨(-86616705029320451336803587500113 / 20000000000000000000000000000000), (1058791187 / 625000000000000000000000000000)⟩
def CB3_2_3I2R0MassTerm : Ball := ⟨(45583093825531771912031644789 / 800000000000000000000000000000), (2228806953 / 100000000000000000000000000000000)⟩
def CB3_2_3I2R0H : Ball := ⟨0, (2228806953 / 50000000000000000000000000000000)⟩
def CB3_2_3I2R1Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 2 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 2) a : ℝ)) 1 a
def CB3_2_3I2R1Entropy : Ball := ⟨(35354994317325124691906992926299 / 100000000000000000000000000000000), (30190271319 / 100000000000000000000000000000000)⟩
def CB3_2_3I2R1Mass : Ball := ⟨(47523174992684098213642460905101 / 100000000000000000000000000000000), (3 / 6250000000000000000000000000000)⟩
def CB3_2_3I2R1MassTermLogWitness : LogWitness := ⟨-2, 47523174992684098213642460905101, 25000000000000000000000000000000⟩
def CB3_2_3I2R1MassTermLog : Ball := ⟨(-74395269934653586537561574687477 / 100000000000000000000000000000000), (1270549423 / 2000000000000000000000000000000)⟩
def CB3_2_3I2R1MassTerm : Ball := ⟨(35354994317325124691906992926299 / 100000000000000000000000000000000), (30190271319 / 100000000000000000000000000000000)⟩
def CB3_2_3I2R1H : Ball := ⟨0, (30190271319 / 50000000000000000000000000000000)⟩
def CB3_2_3I2R2Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 2 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 2) a : ℝ)) 2 a
def CB3_2_3I2R2Entropy : Ball := ⟨(3730736662595773181213535634083 / 10000000000000000000000000000000), (20167605911 / 100000000000000000000000000000000)⟩
def CB3_2_3I2R2Mass : Ball := ⟨(6270084793231563529856005696979 / 20000000000000000000000000000000), (19 / 100000000000000000000000000000000)⟩
def CB3_2_3I2R2MassTermLogWitness : LogWitness := ⟨-2, 6270084793231563529856005696979, 5000000000000000000000000000000⟩
def CB3_2_3I2R2MassTermLog : Ball := ⟨(-28998559883980189693420039678553 / 25000000000000000000000000000000), (63527471109 / 100000000000000000000000000000000)⟩
def CB3_2_3I2R2MassTerm : Ball := ⟨(7272937174166361623897741548253 / 20000000000000000000000000000000), (19916131551 / 100000000000000000000000000000000)⟩
def CB3_2_3I2R2H : Ball := ⟨(188536151025184738529329719913 / 20000000000000000000000000000000), (20041868731 / 50000000000000000000000000000000)⟩
def CB3_2_3I2R3Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 2 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 2) a : ℝ)) 3 a
def CB3_2_3I2R3Entropy : Ball := ⟨0, 0⟩
def CB3_2_3I2R3Mass : Ball := ⟨0, 0⟩
def CB3_2_3I2R3MassTerm : Ball := .exact 0
def CB3_2_3I2R3H : Ball := ⟨0, 0⟩
def CB3_2_3I2R4Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 2 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 2) a : ℝ)) 4 a
def CB3_2_3I2R4Entropy : Ball := ⟨0, 0⟩
def CB3_2_3I2R4Mass : Ball := ⟨0, 0⟩
def CB3_2_3I2R4MassTerm : Ball := .exact 0
def CB3_2_3I2R4H : Ball := ⟨0, 0⟩
def CB3_2_3I2R5Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 2 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 2) a : ℝ)) 5 a
def CB3_2_3I2R5Entropy : Ball := ⟨0, 0⟩
def CB3_2_3I2R5Mass : Ball := ⟨0, 0⟩
def CB3_2_3I2R5MassTerm : Ball := .exact 0
def CB3_2_3I2R5H : Ball := ⟨0, 0⟩
def CB3_2_3I2R6Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 2 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 2) a : ℝ)) 6 a
def CB3_2_3I2R6Entropy : Ball := ⟨0, 0⟩
def CB3_2_3I2R6Mass : Ball := ⟨0, 0⟩
def CB3_2_3I2R6MassTerm : Ball := .exact 0
def CB3_2_3I2R6H : Ball := ⟨0, 0⟩
def CB3_2_3I2R7Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 2 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 2) a : ℝ)) 7 a
def CB3_2_3I2R7Entropy : Ball := ⟨0, 0⟩
def CB3_2_3I2R7Mass : Ball := ⟨0, 0⟩
def CB3_2_3I2R7MassTerm : Ball := .exact 0
def CB3_2_3I2R7H : Ball := ⟨0, 0⟩
def CB3_2_3I2R8Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 2 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 2) a : ℝ)) 8 a
def CB3_2_3I2R8Entropy : Ball := ⟨0, 0⟩
def CB3_2_3I2R8Mass : Ball := ⟨0, 0⟩
def CB3_2_3I2R8MassTerm : Ball := .exact 0
def CB3_2_3I2R8H : Ball := ⟨0, 0⟩
def CB3_2_3I2R9Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 2 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 2) a : ℝ)) 9 a
def CB3_2_3I2R9Entropy : Ball := ⟨0, 0⟩
def CB3_2_3I2R9Mass : Ball := ⟨0, 0⟩
def CB3_2_3I2R9MassTerm : Ball := .exact 0
def CB3_2_3I2R9H : Ball := ⟨0, 0⟩
def CB3_2_3I2R10Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 2 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 2) a : ℝ)) 10 a
def CB3_2_3I2R10Entropy : Ball := ⟨0, 0⟩
def CB3_2_3I2R10Mass : Ball := ⟨0, 0⟩
def CB3_2_3I2R10MassTerm : Ball := .exact 0
def CB3_2_3I2R10H : Ball := ⟨0, 0⟩
def CB3_2_3I2R11Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 2 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 2) a : ℝ)) 11 a
def CB3_2_3I2R11Entropy : Ball := ⟨0, 0⟩
def CB3_2_3I2R11Mass : Ball := ⟨0, 0⟩
def CB3_2_3I2R11MassTerm : Ball := .exact 0
def CB3_2_3I2R11H : Ball := ⟨0, 0⟩
def CB3_2_3I2R12Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 2 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 2) a : ℝ)) 12 a
def CB3_2_3I2R12Entropy : Ball := ⟨0, 0⟩
def CB3_2_3I2R12Mass : Ball := ⟨0, 0⟩
def CB3_2_3I2R12MassTerm : Ball := .exact 0
def CB3_2_3I2R12H : Ball := ⟨0, 0⟩
def CB3_2_3I2R13Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 2 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 2) a : ℝ)) 13 a
def CB3_2_3I2R13Entropy : Ball := ⟨0, 0⟩
def CB3_2_3I2R13Mass : Ball := ⟨0, 0⟩
def CB3_2_3I2R13MassTerm : Ball := .exact 0
def CB3_2_3I2R13H : Ball := ⟨0, 0⟩
def CB3_2_3I2R14Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 2 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 2) a : ℝ)) 14 a
def CB3_2_3I2R14Entropy : Ball := ⟨0, 0⟩
def CB3_2_3I2R14Mass : Ball := ⟨0, 0⟩
def CB3_2_3I2R14MassTerm : Ball := .exact 0
def CB3_2_3I2R14H : Ball := ⟨0, 0⟩
def CB3_2_3I2R15Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 2 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 2) a : ℝ)) 15 a
def CB3_2_3I2R15Entropy : Ball := ⟨0, 0⟩
def CB3_2_3I2R15Mass : Ball := ⟨0, 0⟩
def CB3_2_3I2R15MassTerm : Ball := .exact 0
def CB3_2_3I2R15H : Ball := ⟨0, 0⟩
def CB3_2_3I2R16Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 2 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 2) a : ℝ)) 16 a
def CB3_2_3I2R16Entropy : Ball := ⟨0, 0⟩
def CB3_2_3I2R16Mass : Ball := ⟨0, 0⟩
def CB3_2_3I2R16MassTerm : Ball := .exact 0
def CB3_2_3I2R16H : Ball := ⟨0, 0⟩
def CB3_2_3I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CB3_2_3I2R0H
  | 1 => CB3_2_3I2R1H
  | 2 => CB3_2_3I2R2H
  | 3 => CB3_2_3I2R3H
  | 4 => CB3_2_3I2R4H
  | 5 => CB3_2_3I2R5H
  | 6 => CB3_2_3I2R6H
  | 7 => CB3_2_3I2R7H
  | 8 => CB3_2_3I2R8H
  | 9 => CB3_2_3I2R9H
  | 10 => CB3_2_3I2R10H
  | 11 => CB3_2_3I2R11H
  | 12 => CB3_2_3I2R12H
  | 13 => CB3_2_3I2R13H
  | 14 => CB3_2_3I2R14H
  | 15 => CB3_2_3I2R15H
  | 16 => CB3_2_3I2R16H
  | _ => (.exact 0)
def CB3_2_3I2S0_1_3Value (a : Fin 6) : ℝ := (littleLaw (shape 3 2 3) (shape 0 1 3) ((stageBPriority (shape 3 2 3)) 2) a : ℝ)
def CB3_2_3I2S0_1_3E_4Log : Ball := .exact 0
def CB3_2_3I2S0_1_3E_4 : Ball := ⟨0, 0⟩
def CB3_2_3I2S0_1_3Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB3_2_3I2S0_1_3Entropy : Ball := ⟨0, 0⟩
def CB3_2_3I2S0_1_3Mass : Ball := ⟨1, 0⟩
def CB3_2_3I2S0_1_3MassTermLog : Ball := .exact 0
def CB3_2_3I2S0_1_3MassTerm : Ball := ⟨0, 0⟩
def CB3_2_3I2S0_1_3H : Ball := ⟨0, 0⟩
def CB3_2_3I2S0_2_2Value (a : Fin 6) : ℝ := (littleLaw (shape 3 2 3) (shape 0 2 2) ((stageBPriority (shape 3 2 3)) 2) a : ℝ)
def CB3_2_3I2S0_2_2E_2LogWitness : LogWitness := ⟨-1, 179163, 100000⟩
def CB3_2_3I2S0_2_2E_2Log : Ball := ⟨(-11002136054002092463393093233409 / 100000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def CB3_2_3I2S0_2_2E_2 : Ball := ⟨(4927939254607942230047241907443 / 50000000000000000000000000000000), (18969620493 / 50000000000000000000000000000000)⟩
def CB3_2_3I2S0_2_2E_3LogWitness : LogWitness := ⟨-4, 20837, 12500⟩
def CB3_2_3I2S0_2_2E_3Log : Ball := ⟨(-226158711395997353564112106926423 / 100000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
def CB3_2_3I2S0_2_2E_3 : Ball := ⟨(23562345346791984281077019860129 / 100000000000000000000000000000000), (11031015953 / 100000000000000000000000000000000)⟩
def CB3_2_3I2S0_2_2Terms (a : Fin 6) : Ball :=
  match a.val with
  | 2 => ⟨(4927939254607942230047241907443 / 50000000000000000000000000000000), (18969620493 / 50000000000000000000000000000000)⟩
  | 3 => ⟨(23562345346791984281077019860129 / 100000000000000000000000000000000), (11031015953 / 100000000000000000000000000000000)⟩
  | _ => (.exact 0)
def CB3_2_3I2S0_2_2Entropy : Ball := ⟨(6683644771201573748234300735003 / 20000000000000000000000000000000), (48970256939 / 100000000000000000000000000000000)⟩
def CB3_2_3I2S0_2_2Mass : Ball := ⟨1, 0⟩
def CB3_2_3I2S0_2_2MassTermLog : Ball := .exact 0
def CB3_2_3I2S0_2_2MassTerm : Ball := ⟨0, 0⟩
def CB3_2_3I2S0_2_2H : Ball := ⟨(6683644771201573748234300735003 / 20000000000000000000000000000000), (48970256939 / 100000000000000000000000000000000)⟩
def CB3_2_3I2S1_0_3Value (a : Fin 6) : ℝ := (littleLaw (shape 3 2 3) (shape 1 0 3) ((stageBPriority (shape 3 2 3)) 2) a : ℝ)
def CB3_2_3I2S1_0_3E_4Log : Ball := .exact 0
def CB3_2_3I2S1_0_3E_4 : Ball := ⟨0, 0⟩
def CB3_2_3I2S1_0_3Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
def CB3_2_3I2S1_0_3Entropy : Ball := ⟨0, 0⟩
def CB3_2_3I2S1_0_3Mass : Ball := ⟨1, 0⟩
def CB3_2_3I2S1_0_3MassTermLog : Ball := .exact 0
def CB3_2_3I2S1_0_3MassTerm : Ball := ⟨0, 0⟩
def CB3_2_3I2S1_0_3H : Ball := ⟨0, 0⟩
def CB3_2_3I2S2_0_2E_2LogWitness : LogWitness := ⟨-1, 177987, 100000⟩
def CB3_2_3I2S2_0_2E_2Log : Ball := ⟨(-11660685263090779968348502269377 / 100000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def CB3_2_3I2S2_0_2E_2 : Ball := ⟨(5188625969804346635566112183549 / 50000000000000000000000000000000), (37690213299 / 100000000000000000000000000000000)⟩
def CB3_2_3I2S2_0_2E_3LogWitness : LogWitness := ⟨-4, 22013, 12500⟩
def CB3_2_3I2S2_0_2E_3Log : Ball := ⟨(-27583552232710530620549709460953 / 12500000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
def CB3_2_3I2S2_0_2E_3 : Ball := ⟨(12143934705973138211003215087279 / 50000000000000000000000000000000), (11653585169 / 100000000000000000000000000000000)⟩
def CB3_2_3I2S2_0_2Mass : Ball := ⟨1, 0⟩
def CB3_2_3I2S2_0_2MassTerm : Ball := ⟨0, 0⟩
def CB3_2_3I2Group : Ball := ⟨(6937026787468251354457692241319 / 100000000000000000000000000000000), (56735385719 / 50000000000000000000000000000000)⟩

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
def CB3_2_3I2H : Ball := ⟨(21151229057927517635294544770749 / 25000000000000000000000000000000), (317902791617 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end


